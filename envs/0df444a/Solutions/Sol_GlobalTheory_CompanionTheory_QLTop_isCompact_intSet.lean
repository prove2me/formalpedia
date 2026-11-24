-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QLTop.isCompact_intSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:57:43.631879+00:00
-- url     : https://prove2.me/submissions/38b445bd-a357-456f-8c3a-bb695ec498be

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
theorem _root_.solution {O : Subring F} (hO : IsCompact (O : Set F)) (n : ℕ) : IsCompact (intSet O n) := by
  have : intSet O n = Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => (O : Set F) := by
    ext M
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hO
end GlobalTheory.CompanionTheory.QLTop
