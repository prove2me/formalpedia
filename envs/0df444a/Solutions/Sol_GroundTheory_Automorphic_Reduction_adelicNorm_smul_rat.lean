-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.adelicNorm_smul_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:44:02.436373+00:00
-- url     : https://prove2.me/submissions/f64eb28b-cc6a-4d1a-abf9-f1238a3fc6ec

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Theorems.Thm_GroundTheory_Automorphic_Reduction_adelicNorm_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution {y : Fin n → 𝔸[K]} (hy : HasFiniteContent y) {c : K} (hc : c ≠ 0) :
    adelicNorm (algebraMap K 𝔸[K] c • y) = adelicNorm y := by
  have h := adelicNorm_smul hy (GroundTheory.Global.IdeleGroup.diagonal K (Units.mk0 c hc))
  rwa [GroundTheory.Global.IdeleGroup.ideleModule_diagonal, GroundTheory.Global.IdeleGroup.coe_diagonal,
    Units.val_mk0, Positive.val_one, one_mul] at h
end GroundTheory.Automorphic.Reduction
