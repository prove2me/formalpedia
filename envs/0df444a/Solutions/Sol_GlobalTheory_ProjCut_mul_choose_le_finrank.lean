-- Prove2me | solution 1 for GlobalTheory.ProjCut.mul_choose_le_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:58:36.549877+00:00
-- url     : https://prove2.me/submissions/9e710902-b247-46b4-8ac9-fc4850457d93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IntegralStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Theorems.Thm_GlobalTheory_ProjCut_finrank_homogeneousSubmodule
import Theorems.Thm_GlobalTheory_quotPiece_natCast


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module
open GlobalTheory
open GlobalTheory.ProjCut
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {ι k : Type*} [Field k]
namespace GlobalTheory.ProjCut
theorem _root_.solution [Finite ι] (I : Ideal (MvPolynomial ι k)) {e d : ℕ}
    (z : Fin (e + 1) → MvPolynomial ι k) (hz : ∀ j, (z j).IsHomogeneous 1)
    {l : MvPolynomial ι k} (hl : l.IsHomogeneous 1)
    (hind : ∀ a : Fin d → MvPolynomial (Fin (e + 1)) k,
      ∑ j, aeval z (a j) * l ^ (j : ℕ) ∈ I → a = 0) (m : ℕ) :
    d * (m + e).choose e ≤ finrank k (quotPiece I ((m + d : ℕ) : ℤ)) := by
  rw [quotPiece_natCast]
  let L : (Fin d → homogeneousSubmodule (Fin (e + 1)) k m) →ₗ[k] MvPolynomial ι k :=
    ∑ j : Fin d, LinearMap.mulRight k (l ^ (j : ℕ)) ∘ₗ (aeval z).toLinearMap ∘ₗ
      LinearMap.mulRight k (X 0 ^ (d - j)) ∘ₗ (Submodule.subtype _) ∘ₗ LinearMap.proj j
  have hL : ∀ a, L a = ∑ j : Fin d, aeval z ((a j).1 * X 0 ^ (d - j)) * l ^ (j : ℕ) := by
    intro a
    simp only [L, LinearMap.sum_apply]
    rfl
  have hmem : ∀ a, ((Ideal.Quotient.mkₐ k I).toLinearMap ∘ₗ L) a ∈
      (homogeneousSubmodule ι k (m + d)).map (Ideal.Quotient.mkₐ k I).toLinearMap := by
    intro a
    refine ⟨L a, ?_, rfl⟩
    rw [hL]
    refine Submodule.sum_mem _ fun j _ => ?_
    have h1 : (a j).1.IsHomogeneous m := (a j).2
    have := ((h1.mul (isHomogeneous_X_pow 0 (d - j))).aeval z hz).mul (hl.pow j)
    have hj := j.2
    rwa [show 1 * (m + (d - j)) + 1 * (j : ℕ) = m + d by omega] at this
  have hinj : Function.Injective (LinearMap.codRestrict _ _ hmem) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : L a ∈ I := Ideal.Quotient.eq_zero_iff_mem.1 (congrArg Subtype.val ha)
    rw [hL] at h1
    have h2 := hind _ h1
    funext j
    exact Subtype.ext ((mul_eq_zero.1 (congrFun h2 j)).resolve_right (pow_ne_zero _ (X_ne_zero _)))
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rw [finrank_pi_fintype, finrank_homogeneousSubmodule] at this
  simpa [← add_assoc, Nat.choose_symm_add] using this
end GlobalTheory.ProjCut
