-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwContraction.continuous_map_gl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:43:00.905234+00:00
-- url     : https://prove2.me/submissions/3730b0a1-f1de-4c56-8851-f1fc85903a1d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistedIwahoriContractionHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Tf.Loc Matrix ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TwContraction
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
namespace GlobalTheory.CompanionTheory.TwContraction
theorem _root_.solution (φ : F →+* F) (hφ : Continuous φ) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) φ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.matrix_map hφ :
      Continuous fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F).map φ)
  · have : (fun g : GL (Fin n) F =>
        (((Matrix.GeneralLinearGroup.map φ g)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
        fun g => ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map φ := by
      funext g; rw [← map_inv]; rfl
    exact this ▸ (Units.continuous_coe_inv.matrix_map hφ)
end GlobalTheory.CompanionTheory.TwContraction
