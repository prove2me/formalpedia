-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GramLocal.bcE_sigR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:21:22.209567+00:00
-- url     : https://prove2.me/submissions/efd5f6da-3895-438d-b802-0fd5cf4367e1

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramMatrixLocalGlobal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramLocal
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
namespace GlobalTheory.CompanionTheory.SW.GramLocal
theorem _root_.solution (f : R →ₐ[F] S) (σ : E →ₐ[F] E) (z : R ⊗[F] E) :
    bcE E f (sigR R σ z) = sigR S σ (bcE E f z) := by
  induction z with
  | zero => simp
  | tmul r e => simp [sigR, bcE]
  | add x y hx hy => simp only [map_add, hx, hy]
end GlobalTheory.CompanionTheory.SW.GramLocal
