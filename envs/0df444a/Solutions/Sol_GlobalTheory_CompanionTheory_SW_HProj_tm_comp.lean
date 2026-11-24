-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HProj.tm_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:22:40.44958+00:00
-- url     : https://prove2.me/submissions/bf97abcd-2165-4028-876b-74762dc987ba

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjectionsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections
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
variable {F : Type} (E : Type) [Field F] [Field E] [Algebra F E]
  {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] [CommRing R''] [Algebra F R'']
namespace GlobalTheory.CompanionTheory.SW.HProj
theorem _root_.solution (φ : R →ₐ[F] R') (ψ : R' →ₐ[F] R'') (x : R ⊗[F] E) :
    tm E (ψ.comp φ) x = tm E ψ (tm E φ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [tm]
  | add x y hx hy => simp [hx, hy]
end GlobalTheory.CompanionTheory.SW.HProj
