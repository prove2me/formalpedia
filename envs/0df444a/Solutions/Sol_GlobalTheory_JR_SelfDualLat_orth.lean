-- Prove2me | solution 1 for GlobalTheory.JR.SelfDualLat.orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:09:41.606259+00:00
-- url     : https://prove2.me/submissions/012da57c-c1ab-45c9-987e-8ce1edec31a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.SelfDualLat
namespace GlobalTheory.JR.SelfDualLat
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] [IsTopologicalAddGroup V] (β : LinearMap.BilinForm F V) (μ : Measure V), μ.IsAddHaarMeasure → ∀ M : AddSubgroup V, IsOpen (M : Set V) → IsCompact (M : Set V) → ∀ y, ∫ x in (M : Set V), ψ (β x y) ∂μ = Set.indicator {y | ∀ x ∈ M, ψ (β x y) = 1} (fun _ => ((μ M).toReal : ℂ)) y := by
  intro F E _ _ _ _ _ ψ hψ V _ _ _ _ _ _ _ _ β μ hμ M hMo hMc y
  classical
  by_cases hy : y ∈ {y | ∀ x ∈ M, ψ (β x y) = 1}
  · rw [Set.indicator_of_mem hy, setIntegral_congr_fun hMo.measurableSet (fun x hx => hy x hx)]
    simp [Measure.real]
  · rw [Set.indicator_of_notMem hy]
    simp only [Set.mem_setOf_eq, not_forall] at hy
    obtain ⟨x0, hx0, hne⟩ := hy
    have ht := integral_add_left_eq_self (μ := μ) (fun x => (M : Set V).indicator (fun x => ψ (β x y)) x) x0
    have hpt : ∀ x, (M : Set V).indicator (fun x => ψ (β x y)) (x0 + x) =
        ψ (β x0 y) * (M : Set V).indicator (fun x => ψ (β x y)) x := by
      intro x
      by_cases hx : x ∈ M
      · have : x0 + x ∈ M := M.add_mem hx0 hx
        simp [Set.indicator_of_mem (show x0 + x ∈ (M : Set V) from this),
          Set.indicator_of_mem (show x ∈ (M : Set V) from hx), map_add, AddChar.map_add_eq_mul]
      · have : x0 + x ∉ M := fun h => hx (by simpa using M.sub_mem h hx0)
        simp [Set.indicator_of_notMem (show x0 + x ∉ (M : Set V) from this),
          Set.indicator_of_notMem (show x ∉ (M : Set V) from hx)]
    simp_rw [hpt] at ht
    rw [integral_const_mul, integral_indicator hMo.measurableSet] at ht
    have h0 : (ψ (β x0 y) - 1) * ∫ x in (M : Set V), ψ (β x y) ∂μ = 0 := by rw [sub_mul, one_mul, ht, sub_self]
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
end GlobalTheory.JR.SelfDualLat
