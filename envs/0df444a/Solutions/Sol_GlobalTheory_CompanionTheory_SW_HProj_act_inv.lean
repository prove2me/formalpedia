-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HProj.act_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:22:39.66081+00:00
-- url     : https://prove2.me/submissions/9aa46d4b-6ab5-4822-8d93-ce54200afabf

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjectionsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_mat_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_mat_one
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HProj
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
namespace GlobalTheory.CompanionTheory.SW.HProj
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (g : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E) :
    actW R σ J g⁻¹ (actW R σ J g X) = X := by
  funext a
  simp only [actW, actTup, Matrix.mulVec_mulVec]
  rw [← Units.val_mul, ← mat_mul, inv_mul_cancel, mat_one, Units.val_one, Matrix.one_mulVec]
end GlobalTheory.CompanionTheory.SW.HProj
