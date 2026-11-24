-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.AbsUniq.orbitQuot_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:09:32.496846+00:00
-- url     : https://prove2.me/submissions/2a823995-310e-45df-b702-76a6d1e400ea

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QuotMeasUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ProperActionOrbitMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.AbsUniq
namespace GlobalTheory.CompanionTheory.SW.AbsUniq
theorem _root_.solution {G V : Type} [Group G] (act : G → V → V) (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) (g : G)
    (y : G ⧸ stabilizerOf act h1 hm x₀) :
    orbitQuot act h1 hm x₀ (g • y) = act g (orbitQuot act h1 hm x₀ y) := by
  induction y using QuotientGroup.induction_on with | _ a => ?_
  show act (g * a) x₀ = act g (act a x₀)
  rw [hm]
end GlobalTheory.CompanionTheory.SW.AbsUniq
