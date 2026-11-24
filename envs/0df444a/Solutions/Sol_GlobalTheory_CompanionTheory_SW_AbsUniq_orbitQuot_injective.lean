-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.AbsUniq.orbitQuot_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:26:44.254048+00:00
-- url     : https://prove2.me/submissions/f08430e4-4e20-455d-9e6b-34000a0ecf70

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QuotMeasUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ProperActionOrbitMeasure
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsUniq_orbitQuot_mk

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
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) :
    Function.Injective (orbitQuot act h1 hm x₀) := by
  intro a b
  induction a using QuotientGroup.induction_on with | _ a => ?_
  induction b using QuotientGroup.induction_on with | _ b => ?_
  intro hab
  rw [orbitQuot_mk, orbitQuot_mk] at hab
  refine QuotientGroup.eq.2 ?_
  show act (a⁻¹ * b) x₀ = x₀
  rw [hm, ← hab, ← hm, inv_mul_cancel, h1]
end GlobalTheory.CompanionTheory.SW.AbsUniq
