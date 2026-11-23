-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.AbsUniq.range_orbitQuot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:41.795799+00:00
-- url     : https://prove2.me/submissions/d44cc3d0-d460-4e42-b827-6022ce2468b3

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
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) (Z : Set V) (hx : x₀ ∈ Z)
    (hinv : ∀ g, ∀ x ∈ Z, act g x ∈ Z) (htr : ∀ x ∈ Z, ∀ y ∈ Z, ∃ g, act g x = y) :
    Set.range (orbitQuot act h1 hm x₀) = Z := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    induction a using QuotientGroup.induction_on with | _ a => ?_
    exact hinv a x₀ hx
  · intro hy
    obtain ⟨g, rfl⟩ := htr x₀ hx y hy
    exact ⟨(g : G ⧸ stabilizerOf act h1 hm x₀), rfl⟩
end GlobalTheory.CompanionTheory.SW.AbsUniq
