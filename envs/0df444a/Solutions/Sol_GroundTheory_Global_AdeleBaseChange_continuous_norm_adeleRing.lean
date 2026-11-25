-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.continuous_norm_adeleRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:39:57.506806+00:00
-- url     : https://prove2.me/submissions/1c0cdaa5-677a-48d9-8878-2b8cd6f49c7d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_adeleBasis_repr
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_continuous_coord


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
open GroundTheory.Global.AdeleBaseChange
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution :
    Continuous (Algebra.norm 𝔸[K] : 𝔸[L] → 𝔸[K]) := by
  let b := Module.finBasis K L
  have h : (Algebra.norm 𝔸[K] : 𝔸[L] → 𝔸[K]) =
      fun y ↦ (Algebra.leftMulMatrix (adeleBasis b) y).det :=
    funext fun y ↦ Algebra.norm_eq_matrix_det (adeleBasis b) y
  rw [h]
  refine Continuous.matrix_det (continuous_matrix fun i j ↦ ?_)
  simp_rw [Algebra.leftMulMatrix_eq_repr_mul, adeleBasis_repr]
  exact (continuous_coord b i).comp (continuous_id.mul continuous_const)
end GroundTheory.Global.AdeleBaseChange
