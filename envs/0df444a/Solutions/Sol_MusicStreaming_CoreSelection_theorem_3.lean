-- Prove2me | solution 1 for MusicStreaming.CoreSelection.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T17:04:09.407835+00:00
-- url     : https://prove2.me/submissions/bfcefab9-f4a0-4613-91c3-12ce7f956ecd

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MusicStreaming_CoreSelection_Setting
import Theorems.Thm_MusicStreaming_CoreSelection_userCentric_axioms
import Theorems.Thm_MusicStreaming_CoreSelection_one_user_form
import Theorems.Thm_MusicStreaming_CoreSelection_equal_totals

set_option autoImplicit false

open MusicStreaming.CoreSelection

namespace MS3T3

lemma pstar_add {n : ℕ} (t₁ t₂ : MusicStreaming.Axioms.Problem n)
    (h₁ : InPStar t₁) (h₂ : InPStar t₂) (hd : Disjoint t₁.support t₂.support) :
    InPStar (t₁ + t₂) := by
  intro j hj
  rcases Finset.mem_union.mp (Finsupp.support_add hj) with h | h
  · have h2 : t₂ j = 0 := Finsupp.notMem_support_iff.mp (Finset.disjoint_left.mp hd h)
    have := h₁ j h
    simpa [MusicStreaming.Axioms.listened, h2] using this
  · have h1 : t₁ j = 0 := Finsupp.notMem_support_iff.mp (Finset.disjoint_right.mp hd h)
    have := h₂ j h
    simpa [MusicStreaming.Axioms.listened, h1] using this

lemma pstar_of_add {n : ℕ} (t₁ t₂ : MusicStreaming.Axioms.Problem n)
    (h : InPStar (t₁ + t₂)) (hd : Disjoint t₁.support t₂.support) :
    InPStar t₁ ∧ InPStar t₂ := by
  constructor
  · intro j hj
    have h2 : t₂ j = 0 := Finsupp.notMem_support_iff.mp (Finset.disjoint_left.mp hd hj)
    have hj' : j ∈ (t₁ + t₂).support := by
      rw [Finsupp.mem_support_iff] at hj ⊢; simpa [h2] using hj
    have := h j hj'
    simpa [MusicStreaming.Axioms.listened, h2] using this
  · intro j hj
    have h1 : t₁ j = 0 := Finsupp.notMem_support_iff.mp (Finset.disjoint_right.mp hd hj)
    have hj' : j ∈ (t₁ + t₂).support := by
      rw [Finsupp.mem_support_iff] at hj ⊢; simpa [h1] using hj
    have := h j hj'
    simpa [MusicStreaming.Axioms.listened, h1] using this

lemma listened_single (j : ℕ) {n : ℕ} (x : Fin n → ℕ) :
    MusicStreaming.Axioms.listened (Finsupp.single j x) j =
      Finset.univ.filter (fun i => 0 < x i) := by
  simp [MusicStreaming.Axioms.listened]

/-- `InPStar` of a one-user problem depends only on the profile, not on the user's name. -/
lemma pstar_single_move {n : ℕ} (j j' : ℕ) (x : Fin n → ℕ) (hx : x ≠ 0)
    (h : InPStar (Finsupp.single j x)) : InPStar (Finsupp.single j' x) := by
  have hj : j ∈ (Finsupp.single j x).support := by simp [hx]
  have hL := h j hj
  rw [listened_single] at hL
  intro u hu
  have : u = j' := by
    by_contra hne
    exact (Finsupp.mem_support_iff.mp hu) (by simp [Ne.symm hne])
  subst this
  rw [listened_single]; exact hL

lemma I_zero {n : ℕ} (I : MusicStreaming.Axioms.Index n) (hA : AdditivityOn I) : I 0 = 0 := by
  have h0 : InPStar (0 : MusicStreaming.Axioms.Problem n) := by intro j hj; simp at hj
  funext i
  have h2 : I 0 i = I 0 i + I 0 i := by simpa using congrFun (hA 0 0 h0 h0 (by simp)) i
  show I 0 i = 0
  linarith

lemma userCentric_zero {n : ℕ} : userCentric (0 : MusicStreaming.Axioms.Problem n) = 0 := by
  funext i; simp [userCentric]

/-- Additive extension: if `I = c • U` on every nonempty one-user problem in `𝒫*`, then on all of
`𝒫*`. -/
lemma extend {n : ℕ} (I : MusicStreaming.Axioms.Index n) (hA : AdditivityOn I) (c : ℝ)
    (h1 : ∀ (j : ℕ) (x : Fin n → ℕ), x ≠ 0 → InPStar (Finsupp.single j x) →
      I (Finsupp.single j x) = c • userCentric (Finsupp.single j x)) :
    ∀ t : MusicStreaming.Axioms.Problem n, InPStar t → I t = c • userCentric t := by
  obtain ⟨-, hUA, -⟩ := userCentric_axioms n
  intro t
  induction t using Finsupp.induction with
  | zero => intro _; rw [I_zero I hA, userCentric_zero, smul_zero]
  | single_add a b f ha hb ih =>
    intro hP
    have hd : Disjoint (Finsupp.single a b).support f.support := by
      rw [Finsupp.support_single_ne_zero a hb]; simpa using ha
    obtain ⟨hPa, hPf⟩ := pstar_of_add _ _ hP hd
    rw [hA _ _ hPa hPf hd, hUA _ _ hPa hPf hd, h1 a b hb hPa, ih hPf, smul_add]

end MS3T3

open MS3T3 in
theorem solution (n : ℕ) (I : MusicStreaming.Axioms.Index n) (hI : IsIndexOn I) :
    (HomogeneityOn I ∧ AdditivityOn I ∧ CoreSelectionOn I) ↔
      ∃ c : ℝ, 0 < c ∧ ∀ t : MusicStreaming.Axioms.Problem n, InPStar t → I t = c • userCentric t := by
  obtain ⟨hUH, hUA, hUC⟩ := userCentric_axioms n
  constructor
  · rintro ⟨hH, hA, hC⟩
    by_cases hex : ∃ (j : ℕ) (x : Fin n → ℕ), x ≠ 0 ∧ InPStar (Finsupp.single j x)
    · obtain ⟨j₀, x₀, hx₀, hP₀⟩ := hex
      set c := ∑ i, I (Finsupp.single j₀ x₀) i with hc
      have hcpos : 0 < c := (hI _ hP₀ (by simp [hx₀])).2
      -- the total of every nonempty one-user problem in `𝒫*` is `c`
      have htot : ∀ (j : ℕ) (x : Fin n → ℕ), x ≠ 0 → InPStar (Finsupp.single j x) →
          ∑ i, I (Finsupp.single j x) i = c := by
        intro j x hx hP
        by_cases hj : j = j₀
        · subst hj
          have hw : j + 1 ≠ j := by omega
          rw [equal_totals n I hI hH hA hC j (j + 1) x x₀ hw.symm hx hx₀ hP
            (pstar_single_move j (j + 1) x₀ hx₀ hP₀),
            equal_totals n I hI hH hA hC (j + 1) j x₀ x₀ hw hx₀ hx₀
            (pstar_single_move j (j + 1) x₀ hx₀ hP₀) hP₀]
        · exact equal_totals n I hI hH hA hC j j₀ x x₀ hj hx hx₀ hP hP₀
      refine ⟨c, hcpos, extend I hA c ?_⟩
      intro j x hx hP
      funext i
      rw [one_user_form n I hI hH hC j x hx hP i, htot j x hx hP]
      rfl
    · push_neg at hex
      refine ⟨1, one_pos, extend I hA 1 ?_⟩
      intro j x hx hP
      exact absurd hP (hex j x hx)
  · rintro ⟨c, hc, hIc⟩
    refine ⟨?_, ?_, ?_⟩
    · intro t i i' l hP hl h
      rw [hIc t hP]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hUH t i i' l hP hl h]; ring
    · intro t₁ t₂ h₁ h₂ hd
      rw [hIc _ (pstar_add t₁ t₂ h₁ h₂ hd), hIc _ h₁, hIc _ h₂, hUA t₁ t₂ h₁ h₂ hd, smul_add]
    · intro t hP
      have hrew : MusicStreaming.Axioms.reward I t = MusicStreaming.Axioms.reward userCentric t := by
        funext i
        simp only [MusicStreaming.Axioms.reward, hIc t hP, Pi.smul_apply, smul_eq_mul]
        rw [← Finset.mul_sum, mul_div_mul_left _ _ hc.ne']
      rw [hrew]
      exact hUC t hP
