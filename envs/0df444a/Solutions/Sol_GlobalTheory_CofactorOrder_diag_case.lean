-- Prove2me | solution 1 for GlobalTheory.CofactorOrder.diag_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:47:16.848917+00:00
-- url     : https://prove2.me/submissions/58eb9f36-55a2-4ed2-9124-49761a02bc92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNotXPowDvdAdjugateOfFirstOrderKernel
import Theorems.Thm_GlobalTheory_CofactorOrder_exists_coeff_adjugate_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory
open GlobalTheory.CofactorOrder
variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.CofactorOrder
theorem _root_.solution [Nonempty n] (Θ : Matrix n n K[X]) (D : n → K)
    [DecidablePred fun i => D i = 0] (hD : (Θ.map fun p => p.coeff 0) = diagonal D)
    (H : ∀ x0 x1 : Fin (1 + 1) → n → K, (∀ j, (Θ.map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧
      (Θ.map fun p => p.coeff 1).mulVec (x0 j) + (Θ.map fun p => p.coeff 0).mulVec (x1 j) = 0) →
      ¬ LinearIndependent K x0) :
    ∃ b c, ¬ (X : K[X]) ^ (Fintype.card {i // D i = 0} + 1) ∣ Θ.adjugate b c := by
  obtain ⟨s, hs⟩ : ∃ s : n → K[X], s = fun i => if D i = 0 then X else 1 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Matrix n n K[X],
      T = Matrix.of fun i j => if D i = 0 then divX (Θ i j) else Θ i j := ⟨_, rfl⟩
  have h0 : ∀ i j, (Θ i j).coeff 0 = diagonal D i j := fun i j => by
    simpa using congrFun (congrFun hD i) j
  have hfac : Θ = diagonal s * T := by
    refine Matrix.ext fun i j => ?_
    rw [diagonal_mul, hs, hT, of_apply]
    by_cases hi : D i = 0
    · have hc : (Θ i j).coeff 0 = 0 := by
        rw [h0]
        by_cases hij : i = j
        · subst hij; simp [hi]
        · simp [diagonal_apply_ne _ hij]
      have hX := X_mul_divX_add (Θ i j)
      rw [hc, C_0, add_zero] at hX
      simp only [hi, if_true]
      exact hX.symm
    · simp [hi]
  have hadj : ∀ b c, Θ.adjugate b c = T.adjugate b c * ∏ j ∈ Finset.univ.erase c, s j := by
    intro b c
    rw [hfac, adjugate_mul_distrib, adjugate_diagonal, mul_diagonal]
  have hprod : ∀ c, (∏ j ∈ Finset.univ.erase c, s j) ∣ X ^ Fintype.card {i // D i = 0} := by
    intro c
    have hall : ∏ j, s j = X ^ Fintype.card {i // D i = 0} := by
      simp [hs, Finset.prod_ite, Fintype.card_subtype]
    rw [← hall]
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.erase_subset _ _)
  have hrow : ∀ (v : n → K) (i : n), ((T.map fun p => p.coeff 0) *ᵥ v) i =
      if D i = 0 then ((Θ.map fun p => p.coeff 1) *ᵥ v) i else D i * v i := by
    intro v i
    by_cases hi : D i = 0
    · simp [Matrix.mulVec, dotProduct, hT, hi, coeff_divX]
    · simp [Matrix.mulVec, dotProduct, hT, hi, h0, diagonal_apply]
  have hker : Module.finrank K (LinearMap.ker (T.map fun p => p.coeff 0).mulVecLin) ≤ 1 := by
    by_contra hlt
    push Not at hlt
    set V := LinearMap.ker (T.map fun p => p.coeff 0).mulVecLin
    have h2 : 1 + 1 ≤ Module.finrank K V := hlt
    have hinj : Function.Injective (Fin.castLE h2) := fun a b hab =>
      Fin.ext (by simpa using congrArg Fin.val hab)
    have hf := (Module.finBasis K V).linearIndependent.comp _ hinj
    have hli := hf.map' V.subtype (Submodule.ker_subtype V)
    refine H (fun j => (V.subtype ∘ (Module.finBasis K V ∘ Fin.castLE h2)) j)
      (fun j i => if D i = 0 then 0 else
        -((Θ.map fun p => p.coeff 1) *ᵥ (V.subtype ∘ (Module.finBasis K V ∘ Fin.castLE h2)) j) i / D i)
      ?_ hli
    intro j
    set v := (V.subtype ∘ (Module.finBasis K V ∘ Fin.castLE h2)) j with hv
    have hvk : (T.map fun p => p.coeff 0) *ᵥ v = 0 := by
      have := (Module.finBasis K V (Fin.castLE h2 j)).2
      rw [LinearMap.mem_ker, mulVecLin_apply] at this
      exact this
    have hvi : ∀ i, (if D i = 0 then ((Θ.map fun p => p.coeff 1) *ᵥ v) i else D i * v i) = 0 := by
      intro i
      rw [← hrow, hvk]
      rfl
    constructor
    · rw [hD]
      funext i
      rw [mulVec_diagonal]
      by_cases hi : D i = 0
      · simp [hi]
      · have := hvi i
        simp only [hi, if_false] at this
        simpa using this
    · rw [hD]
      funext i
      rw [Pi.add_apply, mulVec_diagonal]
      by_cases hi : D i = 0
      · have := hvi i
        simp only [hi, if_true] at this
        simp [hi, this]
      · simp only [hi, if_false]
        rw [Pi.zero_apply, ← mul_div_assoc, mul_div_cancel_left₀ _ hi, add_neg_cancel]
  obtain ⟨b, c, hbc⟩ := exists_coeff_adjugate_ne_zero T hker
  refine ⟨b, c, fun hdvd => hbc ?_⟩
  rw [hadj] at hdvd
  obtain ⟨r, hr⟩ := hprod c
  have h3 := Dvd.dvd.mul_right hdvd r
  rw [mul_assoc, ← hr, pow_succ, mul_comm (X ^ _) X] at h3
  exact (mul_dvd_mul_iff_right (pow_ne_zero _ X_ne_zero)).mp h3
end GlobalTheory.CofactorOrder
