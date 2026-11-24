-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StabFirst.act_iota
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:56:08.525828+00:00
-- url     : https://prove2.me/submissions/2c4c0a3a-55f3-4d98-b234-0bab1fc99654

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_mulVec_first
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_blockOne_mulVec_cons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StabFirst
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : E)
namespace GlobalTheory.CompanionTheory.SW.StabFirst
theorem _root_.solution {n : ℕ} (u : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E) :
    actW R σ _ (iotaHom R σ J s u) (consTup X) = consTup (actW R σ J u X) := by
  funext a
  refine Fin.cases ?_ (fun c => ?_) a
  · funext i
    change (blockOne 1 (HA.mat R σ J u : Matrix (Fin M) (Fin M) (R ⊗[F] E))).mulVec
      (Fin.cons 1 (fun _ => 0)) i = (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E) i
    rw [mulVec_first]
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  · exact blockOne_mulVec_cons _ _
end GlobalTheory.CompanionTheory.SW.StabFirst
