-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.compLeft_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:29:04.264118+00:00
-- url     : https://prove2.me/submissions/c1b527a2-0db4-469d-984f-be2852b65bda

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatementStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
open _root_.CompanionTheory.RgExh _root_.CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet qminor Tm)
open Formalism.QuantumDeterminants (capP)
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] {I : Type*} (T : Module.End ℂ V)
    (c : ℂ) (k : ℕ) (f : I → V) (i : I) :
    ((T.compLeft I - algebraMap ℂ (Module.End ℂ (I → V)) c) ^ k) f i =
      ((T - algebraMap ℂ (Module.End ℂ V) c) ^ k) (f i) := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
    simp [Module.algebraMap_end_apply]
end GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
