-- Prove2me | solution 1 for GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:05:58.05348+00:00
-- url     : https://prove2.me/submissions/9062c133-44b7-4e22-a7bd-9b4cae4c6c64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianGenusMassEqOrbitStabilizerMass
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianGenusMassEqOrbitStabilizerMassStatement
import Theorems.Thm_GlobalTheory_Mass_GenusOrb_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ L : Submodule (𝓞 K) V, Submodule.IsLattice K L → ENNReal.ofReal (mass h L) = orbMass (isom h) (genus h L) ∧ 0 < mass h L ∧ Stable (isom h) (genus h L) ∧ (∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M → Finite (MulAction.stabilizer (isom h) M)) ∧ ∀ (s : Finset (Submodule (𝓞 K) V)) (N : Submodule (𝓞 K) V → ℝ≥0∞), Formalism.ThetaLiftIndependence.IsClassReps h L s → (∀ (g : isom h) M, N (g • M) = N M) → ∑ M ∈ s, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ))⁻¹ * N M = orbSum (isom h) (genus h L) N := by
  first | exact @GlobalTheory.Mass.GenusOrb.main | exact GlobalTheory.Mass.GenusOrb.main | (intros; apply GlobalTheory.Mass.GenusOrb.main <;> assumption)
end _root_.GlobalTheory.T
