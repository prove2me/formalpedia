-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QLTop.isOpen_intSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:57:44.384396+00:00
-- url     : https://prove2.me/submissions/1b92b390-a655-40b3-8a62-d13b5aa4b6c6

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearIntegralCompactOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLTop
open ValuativeRel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
omit [ValuativeRel F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.CompanionTheory.QLTop
theorem _root_.solution {O : Subring F} (hO : IsOpen (O : Set F)) (n : ℕ) : IsOpen (intSet O n) := by
  have : intSet O n = ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) F => M i j) ⁻¹' (O : Set F) := by
    ext M; simp [intSet, IsInt]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    hO.preimage ((continuous_apply j).comp (continuous_apply i))
end GlobalTheory.CompanionTheory.QLTop
