-- Prove2me | solution 1 for GlobalTheory.ProjCut.isInternal_quotPiece
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:10.63817+00:00
-- url     : https://prove2.me/submissions/b25fd198-8d1f-4fd8-9617-a58b27d0efef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IntegralStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Theorems.Thm_GlobalTheory_weightedHomogeneousComponent_one_mem


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
theorem _root_.solution {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) : DirectSum.IsInternal (quotPiece I) := by
  classical
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    rintro y ⟨a, ha, rfl⟩ hy
    have hmap : (⨆ (j) (_ : j ≠ i), quotPiece I j) =
        (⨆ (j) (_ : j ≠ i), weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ)) j).map
          (Ideal.Quotient.mkₐ k I).toLinearMap := by
      simp only [quotPiece, Submodule.map_iSup]
    rw [hmap] at hy
    obtain ⟨b, hb, hab⟩ := hy
    have hb0 : weightedHomogeneousComponent (fun _ : ι => (1 : ℤ)) i b = 0 := by
      have : (⨆ (j) (_ : j ≠ i), weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ)) j) ≤
          LinearMap.ker (weightedHomogeneousComponent (fun _ : ι => (1 : ℤ)) i) := by
        refine iSup₂_le fun j hj z hz => ?_
        rw [LinearMap.mem_ker, weightedHomogeneousComponent_of_mem hz, if_neg (Ne.symm hj)]
      exact this hb
    have hab' : a - b ∈ I := Ideal.Quotient.eq.mp hab.symm
    have h2 := weightedHomogeneousComponent_one_mem hI i hab'
    rw [map_sub, hb0, sub_zero, weightedHomogeneousComponent_of_mem ha, if_pos rfl] at h2
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h2
  · letI := weightedDecomposition k (fun _ : ι => (1 : ℤ))
    have htop := (DirectSum.Decomposition.isInternal
      (weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ)))).submodule_iSup_eq_top
    unfold quotPiece
    rw [← Submodule.map_iSup, htop, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (Ideal.Quotient.mkₐ_surjective k I)
end GlobalTheory.ProjCut
