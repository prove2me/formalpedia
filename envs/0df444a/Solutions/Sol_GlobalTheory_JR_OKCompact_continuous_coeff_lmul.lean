-- Prove2me | solution 1 for GlobalTheory.JR.OKCompact.continuous_coeff_lmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:28:28.057914+00:00
-- url     : https://prove2.me/submissions/14a81c25-9766-4d82-b2d2-06bedc4be77d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCompactFiniteEtaleHermitianPairOK
import Theorems.Thm_GlobalTheory_JR_OKCompact_continuous_coeff_charpoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OKCompact
variable {F : Type} [NontriviallyNormedField F] {K : Type} [CommRing K] [Algebra F K] [Module.Finite F K]
namespace GlobalTheory.JR.OKCompact
theorem _root_.solution [TopologicalSpace K] [IsModuleTopology F K] (k : ℕ) :
    Continuous fun z : K => (LinearMap.charpoly (Algebra.lmul F K z)).coeff k := by
  let b := Module.finBasis F K
  have h : (fun z : K => (LinearMap.charpoly (Algebra.lmul F K z)).coeff k) =
      (fun M : Matrix _ _ F => M.charpoly.coeff k) ∘ (fun z => Algebra.leftMulMatrix b z) := by
    funext z
    simp only [Function.comp, Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]
  rw [h]
  refine (continuous_coeff_charpoly k).comp ?_
  refine continuous_matrix fun i j => ?_
  let l : K →ₗ[F] F :=
    { toFun := fun z => Algebra.leftMulMatrix b z i j
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
  exact IsModuleTopology.continuous_of_linearMap l
end GlobalTheory.JR.OKCompact
