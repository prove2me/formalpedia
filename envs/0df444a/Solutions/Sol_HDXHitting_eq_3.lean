-- Prove2me | solution 1 for HDXHitting.eq_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:07:54.125971+00:00
-- url     : https://prove2.me/submissions/157d67a0-b75a-4fd6-8c67-02b8fcfcf1b9

import Mathlib
import Definitions.Def_HDXHitting_IsTopDist
import Definitions.Def_HDXHitting_vertexMeasure
import Definitions.Def_HDXHitting_hit
import Definitions.Def_HDXHitting_linkWeight
import Definitions.Def_HDXHitting_BipSingLE
import Definitions.Def_HDXHitting_IsPartiteHDX
import Definitions.Def_HDXHitting_linkDist
import Definitions.Def_HDXHitting_IsRainbow
import Definitions.Def_HDXHitting_colourMean
import Definitions.Def_HDXHitting_cPoly
import Theorems.Thm_HDXHitting_partite_vertex_decomposition
import Theorems.Thm_HDXHitting_affine_identity
import Theorems.Thm_HDXHitting_partite_good_vertex
import Theorems.Thm_HDXHitting_link_heredity

section
set_option autoImplicit false
namespace HDXHitting.Dev.Eq3
open HDXHitting

noncomputable def Pm {V : Type*} [Fintype V] [DecidableEq V] (p : Finset V → ℝ) (v : V) : ℝ :=
  ∑ σ ∈ Finset.univ.filter (fun σ : Finset V => v ∈ σ), p σ

theorem colour_swap {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (p : Finset V → ℝ) (c : V → ι) (k : ι) (a : V → ℝ) :
    ∑ u ∈ Finset.univ.filter (fun u => c u = k), Pm p u * a u =
      ∑ σ : Finset V, p σ * ∑ u ∈ Finset.univ.filter (fun u => u ∈ σ ∧ c u = k), a u := by
  have h1 : ∑ u ∈ Finset.univ.filter (fun u => c u = k), Pm p u * a u =
      ∑ u : V, ∑ σ : Finset V, if (c u = k ∧ u ∈ σ) then p σ * a u else 0 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl; intro u _
    unfold Pm
    rw [Finset.sum_filter, Finset.sum_mul]
    by_cases hu : c u = k
    · simp [hu, ite_mul]
    · simp [hu]
  rw [h1, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro σ _
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl; intro u _
  by_cases h : u ∈ σ <;> by_cases h' : c u = k <;> simp [h, h']

theorem cm_def {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (p : Finset V → ℝ) (c : V → ι) (f : V → ℝ) (i : ι) :
    colourMean p c f i = ∑ u ∈ Finset.univ.filter (fun u => c u = i), Pm p u * f u := rfl

theorem cm_nonneg {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (p : Finset V → ℝ) (h0 : ∀ σ, 0 ≤ p σ) (c : V → ι) (f : V → ℝ) (hf : ∀ v, 0 ≤ f v)
    (i : ι) : 0 ≤ colourMean p c f i :=
  Finset.sum_nonneg (fun w _ => mul_nonneg (Finset.sum_nonneg (fun σ _ => h0 σ)) (hf w))

theorem cPoly_nonneg' {ι : Type*} [DecidableEq ι] (S : Finset ι) (lam : ℝ) (hlam : 0 ≤ lam)
    (x : ι → ℝ) (hx : ∀ j ∈ S, 0 ≤ x j) : 0 ≤ cPoly S lam x := by
  unfold cPoly
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg; intro k hk
  apply mul_nonneg (hx k hk)
  apply Finset.prod_nonneg; intro j hj
  have := hx j (Finset.mem_of_mem_erase hj)
  have : (0 : ℝ) ≤ S.card * lam := by positivity
  linarith

theorem base_case {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (p : Finset V → ℝ) (hp : IsTopDist 1 p) (c : V → ι) (S : Finset ι) (hS : S.card = 1)
    (hc : IsRainbow p c S) (lam : ℝ) (f : V → ℝ) :
    hit p f ≤ cPoly S lam (colourMean p c f) := by
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hS
  have hcp : cPoly {i} lam (colourMean p c f) = colourMean p c f i := by
    simp [cPoly]
  rw [hcp, cm_def, colour_swap]
  apply le_of_eq
  apply Finset.sum_congr rfl; intro σ _
  by_cases h0 : p σ = 0
  · simp [h0]
  · obtain ⟨u, rfl⟩ := Finset.card_eq_one.1 (hp.2.1 σ h0)
    have hu : c u = i := by
      have := (hc {u} h0).1 u (Finset.mem_singleton_self u)
      simpa using this
    have e : Finset.univ.filter (fun w => w ∈ ({u} : Finset V) ∧ c w = i) = {u} := by
      ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · exact fun h => h.1
      · intro h; subst h; exact ⟨rfl, hu⟩
    rw [e]; simp

theorem step_case {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι] (d : ℕ)
    (hd : 2 ≤ d)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (IH : ∀ (p : Finset V → ℝ), IsTopDist (d - 1) p → ∀ (c : V → ι) (S : Finset ι),
      S.card = d - 1 → IsRainbow p c S → IsPartiteHDX p c S lam →
        ∀ f : V → ℝ, (∀ v, 0 ≤ f v ∧ f v ≤ 1) → hit p f ≤ cPoly S lam (colourMean p c f))
    (p : Finset V → ℝ) (hp : IsTopDist d p) (c : V → ι) (S : Finset ι) (hS : S.card = d)
    (hc : IsRainbow p c S) (hX : IsPartiteHDX p c S lam) :
    ∀ N : ℕ, ∀ f : V → ℝ, (∀ v, 0 ≤ f v ∧ f v ≤ 1) →
      (Finset.univ.filter (fun v => f v ≠ 0)).card = N →
        hit p f ≤ cPoly S lam (colourMean p c f) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
  intro f hf hN
  have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨i, hiS, hmax⟩ := Finset.exists_max_image S (colourMean p c f) hSne
  have hcm0 : ∀ j, 0 ≤ colourMean p c f j := fun j => cm_nonneg p hp.1 c f (fun v => (hf v).1) j
  by_cases hpos : 0 < colourMean p c f i
  · -- main case
    obtain ⟨-, v, hcv, hfv, hvm, hcp⟩ :=
      partite_good_vertex d p hp c S hS hd hc lam hlam hX f hf i hiS hmax hpos
    have hPv : 0 < ∑ σ ∈ Finset.univ.filter (fun σ : Finset V => {v} ⊆ σ), p σ := by
      have : (0 : ℝ) < (1 / (d : ℝ)) * ∑ σ ∈ Finset.univ.filter (fun σ : Finset V => v ∈ σ), p σ := hvm
      simp only [Finset.singleton_subset_iff]
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      by_contra hcon
      push Not at hcon
      have : (1 / (d : ℝ)) * ∑ σ ∈ Finset.univ.filter (fun σ : Finset V => v ∈ σ), p σ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hcon
      linarith
    obtain ⟨h1, -, h3, h4⟩ := link_heredity d p hp {v} hPv lam c S
    rw [Finset.card_singleton] at h1
    have hSeq : S \ ({v} : Finset V).image c = S.erase i := by
      simp [Finset.image_singleton, hcv, Finset.sdiff_singleton_eq_erase]
    have hlink := IH (linkDist p {v}) h1 c (S.erase i)
      (by rw [Finset.card_erase_of_mem hiS, hS]) (hSeq ▸ h3 hc) (hSeq ▸ h4 hc hX) f hf
    set g : V → ℝ := Function.update f v 0 with hg
    have hgb : ∀ w, 0 ≤ g w ∧ g w ≤ 1 := by
      intro w
      by_cases hw : w = v
      · subst hw; simp [hg]
      · simp only [hg, Function.update_of_ne hw]; exact hf w
    have hlt : (Finset.univ.filter (fun w => g w ≠ 0)).card < N := by
      rw [← hN]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨v, ?_, ?_⟩
        · simp [hfv.ne']
        · simp [hg]
      · intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hg] at hw ⊢
        by_cases hwv : w = v
        · subst hwv; simp at hw
        · rwa [Function.update_of_ne hwv] at hw
    have hgle := ihN _ hlt g hgb rfl
    have hh0 : 0 ≤ (d : ℝ) * vertexMeasure d p v * f v :=
      mul_nonneg (mul_nonneg (by positivity) hvm.le) hfv.le
    obtain ⟨-, -, h3'⟩ := partite_vertex_decomposition d p hp c S lam v hvm f _ rfl
    have key := h3' hfv.le hgle (by rw [hcv]; exact hlink)
    rw [hcv] at key
    have aff := (affine_identity S (by omega) i hiS lam (colourMean p c f)
      ((d : ℝ) * vertexMeasure d p v * f v)).2
    calc hit p f ≤ _ := key
      _ ≤ cPoly S lam (colourMean p c f - ((d : ℝ) * vertexMeasure d p v * f v) • Pi.single i 1) +
          ((d : ℝ) * vertexMeasure d p v * f v) *
            cPoly (S.erase i) lam (fun j => colourMean p c f j + lam) := by
          have := mul_le_mul_of_nonneg_left hcp hh0
          linarith
      _ = _ := aff
  · -- all colour means vanish
    have hz : ∀ j ∈ S, colourMean p c f j = 0 := fun j hj =>
      le_antisymm (le_trans (hmax j hj) (not_lt.1 hpos)) (hcm0 j)
    have hhit : hit p f = 0 := by
      unfold hit
      apply Finset.sum_eq_zero; intro σ _
      by_cases h0 : p σ = 0
      · simp [h0]
      · have hne : σ.Nonempty := Finset.card_pos.1 (by rw [hp.2.1 σ h0]; omega)
        obtain ⟨u, hu⟩ := hne
        have hcu : c u ∈ S := (hc σ h0).1 u hu
        have hz' := hz (c u) hcu
        rw [cm_def] at hz'
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ =>
          mul_nonneg (Finset.sum_nonneg (fun σ _ => hp.1 σ)) (hf w).1)).1 hz' u
            (by simp)
        have hPu : 0 < Pm p u := by
          have : p σ ≤ Pm p u :=
            Finset.single_le_sum (f := p) (fun σ _ => hp.1 σ) (by simpa using hu)
          exact lt_of_lt_of_le (lt_of_le_of_ne (hp.1 σ) (Ne.symm h0)) this
        have hfu : f u = 0 := by
          rcases mul_eq_zero.1 this with h | h
          · exact absurd h hPu.ne'
          · exact h
        rw [Finset.prod_eq_zero hu hfu, mul_zero]
    rw [hhit]
    exact cPoly_nonneg' S lam hlam _ (fun j _ => hcm0 j)

end HDXHitting.Dev.Eq3
namespace HDXHitting
open HDXHitting.Dev.Eq3 in
theorem chk_eq_3 {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι] (d : ℕ) (hd : 1 ≤ d)
    (p : Finset V → ℝ) (hp : IsTopDist d p) (c : V → ι) (S : Finset ι) (hS : S.card = d)
    (hc : IsRainbow p c S) (lam : ℝ) (hlam : 0 ≤ lam) (hX : IsPartiteHDX p c S lam)
    (f : V → ℝ) (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1) :
    hit p f ≤ cPoly S lam (colourMean p c f) := by
  induction d, hd using Nat.le_induction generalizing p c S f with
  | base =>
    exact base_case p hp c S hS hc lam f
  | succ n hn ih =>
    exact step_case (n + 1) (by omega) lam hlam
      (fun p' hp' c' S' hS' hc' hX' f' hf' => by
        simpa using ih p' (by simpa using hp') c' S' (by simpa using hS') hc' hX' f' hf')
      p hp c S hS hc hX _ f hf rfl

end HDXHitting
end

theorem solution : type_of% @HDXHitting.chk_eq_3 := @HDXHitting.chk_eq_3
