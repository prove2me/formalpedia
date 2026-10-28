-- Prove2me | solution 1 for MusicStreaming.CoreSelection.equal_totals
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T17:04:11.833153+00:00
-- url     : https://prove2.me/submissions/43d1bbca-6ba6-4df9-815e-4371b94e0d71

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MusicStreaming_CoreSelection_Setting
import Theorems.Thm_MusicStreaming_CoreSelection_claim

set_option autoImplicit false

open MusicStreaming.CoreSelection

namespace MS3E

open MusicStreaming.Axioms in
lemma listened_single (j : ℕ) {n : ℕ} (x : Fin n → ℕ) :
    listened (Finsupp.single j x) j = Finset.univ.filter (fun i => 0 < x i) := by
  simp [listened]

lemma pstar_single {n : ℕ} (j : ℕ) (x : Fin n → ℕ)
    (h : Finset.univ.filter (fun i => 0 < x i) ≠ Finset.univ) :
    InPStar (Finsupp.single j x) := by
  intro j' hj'
  have : j' = j := by
    by_contra hne
    exact (Finsupp.mem_support_iff.mp hj') (by simp [Finsupp.single_apply, Ne.symm hne])
  subst this
  rw [listened_single]; exact h

lemma pstar_single_iff {n : ℕ} (j : ℕ) (x : Fin n → ℕ) (hx : x ≠ 0)
    (h : InPStar (Finsupp.single j x)) :
    Finset.univ.filter (fun i => 0 < x i) ≠ Finset.univ := by
  have hj : j ∈ (Finsupp.single j x).support := by simp [hx]
  have := h j hj
  rwa [listened_single] at this

/-- the unit profile `e_k`. -/
def e {n : ℕ} (k : Fin n) : Fin n → ℕ := Pi.single k 1

lemma e_ne_zero {n : ℕ} (k : Fin n) : e k ≠ 0 := by
  intro h
  have := congrFun h k
  simp [e] at this

lemma e_filter {n : ℕ} (k : Fin n) : Finset.univ.filter (fun i => 0 < e k i) = {k} := by
  ext i
  by_cases h : i = k
  · subst h; simp [e, Pi.single_apply]
  · simp [e, Pi.single_apply, h]

lemma pstar_e {n : ℕ} (u : ℕ) (k k' : Fin n) (hk : k' ≠ k) : InPStar (Finsupp.single u (e k)) := by
  apply pstar_single
  rw [e_filter]
  intro h
  have : k' ∈ ({k} : Finset (Fin n)) := by rw [h]; exact Finset.mem_univ _
  exact hk (Finset.mem_singleton.mp this)

lemma e_disj {n : ℕ} (k k' : Fin n) (hk : k ≠ k') :
    Disjoint (Finset.univ.filter (fun i => 0 < e k i)) (Finset.univ.filter (fun i => 0 < e k' i)) := by
  rw [e_filter, e_filter]; simpa using hk

lemma x_e_disj {n : ℕ} (x : Fin n → ℕ) (k : Fin n) (hk : x k = 0) :
    Disjoint (Finset.univ.filter (fun i => 0 < x i)) (Finset.univ.filter (fun i => 0 < e k i)) := by
  rw [e_filter]
  simp [hk]

end MS3E

open MS3E in
theorem solution (n : ℕ) (I : MusicStreaming.Axioms.Index n) (hI : IsIndexOn I) (hH : HomogeneityOn I)
    (hA : AdditivityOn I) (hC : CoreSelectionOn I) (j₁ j₂ : ℕ) (x y : Fin n → ℕ)
    (hj : j₁ ≠ j₂) (hx : x ≠ 0) (hy : y ≠ 0)
    (hPx : InPStar (Finsupp.single j₁ x)) (hPy : InPStar (Finsupp.single j₂ y)) :
    ∑ i, I (Finsupp.single j₁ x) i = ∑ i, I (Finsupp.single j₂ y) i := by
  set f : ℕ → (Fin n → ℕ) → ℝ := fun u z => ∑ i, I (Finsupp.single u z) i with hf
  have cl := claim n I hI hH hA hC
  -- an artist outside a nonuniversal list
  have outside : ∀ z : Fin n → ℕ, Finset.univ.filter (fun i => 0 < z i) ≠ Finset.univ →
      ∃ k, z k = 0 := by
    intro z hz
    by_contra h
    push_neg at h
    exact hz (Finset.eq_univ_of_forall fun i => by simp; exact Nat.pos_of_ne_zero (h i))
  obtain ⟨k₀, hk₀⟩ := outside x (pstar_single_iff j₁ x hx hPx)
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, x i₀ ≠ 0 := by
    by_contra h; push_neg at h; exact hx (funext h)
  have other : ∀ k : Fin n, ∃ k', k' ≠ k := by
    intro k
    by_cases h : k = k₀
    · exact ⟨i₀, by rintro rfl; exact hi₀ (h ▸ hk₀)⟩
    · exact ⟨k₀, Ne.symm h⟩
  have pe : ∀ (u : ℕ) (k : Fin n), InPStar (Finsupp.single u (e k)) := by
    intro u k; obtain ⟨k', hk'⟩ := other k; exact pstar_e u k k' hk'
  -- singleton profiles
  have clE : ∀ (u u' : ℕ) (k k' : Fin n), u ≠ u' → k ≠ k' → f u (e k) = f u' (e k') := by
    intro u u' k k' hu hk
    exact cl u u' (e k) (e k') hu (e_ne_zero k) (e_ne_zero k') (pe u k) (pe u' k') (e_disj k k' hk)
  have stepA : ∀ (u u' : ℕ) (k : Fin n), f u (e k) = f u' (e k) := by
    intro u u' k
    obtain ⟨k', hk'⟩ := other k
    have hwu : u + u' + 1 ≠ u := by omega
    have hwu' : u + u' + 1 ≠ u' := by omega
    rw [clE u (u + u' + 1) k k' (Ne.symm hwu) (Ne.symm hk'),
      clE (u + u' + 1) u' k' k hwu' hk']
  have stepB : ∀ (u u' : ℕ) (k k' : Fin n), f u (e k) = f u' (e k') := by
    intro u u' k k'
    by_cases hk : k = k'
    · subst hk; exact stepA u u' k
    · have hwu : u + u' + 1 ≠ u := by omega
      rw [clE u (u + u' + 1) k k' (Ne.symm hwu) hk, stepA]
  have stepC : ∀ (u : ℕ) (z : Fin n → ℕ), z ≠ 0 → InPStar (Finsupp.single u z) →
      ∃ k, f u z = f (u + 1) (e k) := by
    intro u z hz hPz
    obtain ⟨k, hk⟩ := outside z (pstar_single_iff u z hz hPz)
    exact ⟨k, cl u (u + 1) z (e k) (by omega) hz (e_ne_zero k) hPz (pe _ k) (x_e_disj z k hk)⟩
  obtain ⟨k₁, h₁⟩ := stepC j₁ x hx hPx
  obtain ⟨k₂, h₂⟩ := stepC j₂ y hy hPy
  change f j₁ x = f j₂ y
  rw [h₁, h₂, stepB]

