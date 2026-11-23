-- Prove2me | solution 1 for GlobalTheory.integral_cube_succ_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:05.372193+00:00
-- url     : https://prove2.me/submissions/f8fb2b6f-2e8c-46fa-b0af-6318f1093a7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqIntervalIntegralLeMulIntervalIntegralSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SobolevIteratedOneParameterSubgroups

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (N : ℕ) (s : ℝ) (f : (Fin (N + 1) → ℝ) → ℝ) (hf : Continuous f) :
    IntegrableOn (fun t : Fin N → ℝ => ∫ r in Set.Icc (0 : ℝ) s, f (Fin.snoc (α := fun _ => ℝ) t r))
      (Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s)) ∧
    ∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s), f t =
      ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s),
        ∫ r in Set.Icc (0 : ℝ) s, f (Fin.snoc (α := fun _ => ℝ) t r) := by
  set T : Set (Fin N → ℝ) := Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s) with hT
  have hTc : IsCompact T := isCompact_univ_pi fun _ => isCompact_Icc
  have hG : Continuous fun z : (Fin N → ℝ) × ℝ => f (Fin.snoc (α := fun _ => ℝ) z.1 z.2) :=
    hf.comp (Continuous.finSnoc (n := N) (A := fun _ => ℝ) continuous_fst continuous_snd)
  refine ⟨?_, ?_⟩
  · exact (continuous_parametric_integral_of_continuous
      (f := fun t r => f (Fin.snoc (α := fun _ => ℝ) t r)) hG isCompact_Icc).continuousOn.integrableOn_compact hTc
  · let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) (Fin.last N)
    have hp : MeasurePreserving e (volume : Measure (Fin (N + 1) → ℝ))
        ((volume : Measure ℝ).prod (volume : Measure (Fin N → ℝ))) :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) (Fin.last N)
    have hsymm : ∀ z : ℝ × (Fin N → ℝ), e.symm z = Fin.snoc (α := fun _ => ℝ) z.2 z.1 := by
      intro z
      simp [e, MeasurableEquiv.piFinSuccAbove]
      rfl
    have hS : Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s) =
        e ⁻¹' (Set.Icc (0 : ℝ) s ×ˢ T) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_prod, hT, Set.mem_pi, Set.mem_univ, true_implies]
      rw [Fin.forall_fin_succ', and_comm]
      simp [e, Fin.init]
    have hsw : (fun z : (Fin N → ℝ) × ℝ => f (e.symm z.swap)) =
        fun z => f (Fin.snoc (α := fun _ => ℝ) z.1 z.2) := by
      funext z
      rw [hsymm]
      rfl
    calc ∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s), f t
        = ∫ t in e ⁻¹' (Set.Icc (0 : ℝ) s ×ˢ T), f (e.symm (e t)) := by
          rw [hS]
          simp only [MeasurableEquiv.symm_apply_apply]
      _ = ∫ z in Set.Icc (0 : ℝ) s ×ˢ T, f (e.symm z) ∂((volume : Measure ℝ).prod volume) :=
          hp.setIntegral_preimage_emb e.measurableEmbedding (fun z => f (e.symm z)) _
      _ = ∫ z in T ×ˢ Set.Icc (0 : ℝ) s, f (e.symm z.swap)
            ∂((volume : Measure (Fin N → ℝ)).prod volume) :=
          (setIntegral_prod_swap _ _ _).symm
      _ = ∫ t in T, ∫ r in Set.Icc (0 : ℝ) s, f (Fin.snoc (α := fun _ => ℝ) t r) := by
          rw [setIntegral_prod]
          · simp only [hsymm, Prod.swap_prod_mk]
          · rw [hsw]
            exact hG.continuousOn.integrableOn_compact (hTc.prod isCompact_Icc)
end GlobalTheory
