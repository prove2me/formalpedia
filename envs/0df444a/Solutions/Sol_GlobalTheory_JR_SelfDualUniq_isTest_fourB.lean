-- Prove2me | solution 1 for GlobalTheory.JR.SelfDualUniq.isTest_fourB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:12:06.155298+00:00
-- url     : https://prove2.me/submissions/66141783-e128-4661-871d-a7214bf4284c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualOfDualSubgroups
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion
import Theorems.Thm_GlobalTheory_JR_AbsInv_exists_nhds_invariant
import Theorems.Thm_GlobalTheory_JR_AbsInv_integral_eq_zero_of_translate
import Theorems.Thm_GlobalTheory_JR_EtMeas_top_facts
import Theorems.Thm_GlobalTheory_JR_exists_small_dual_lattices


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.SelfDualUniq
namespace GlobalTheory.JR.SelfDualUniq
theorem _root_.solution {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F]
    (ψ : AddChar F ℂ) (hψ : IsStdChar ψ)
    (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V]
    [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V) (hs : β.IsSymm) (hn : β.Nondegenerate)
    (μ : Measure V) [μ.IsAddHaarMeasure] (f : V → ℂ) (hf : IsTest f) :
    IsTest (fourB μ (fun x y => ψ (β x y)) f) := by
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F V
  obtain ⟨-, hl⟩ := GlobalTheory.JR.exists_small_dual_lattices F ψ hψ V β hs hn
  obtain ⟨U, hU, hUinv⟩ := AbsInv.exists_nhds_invariant hf
  obtain ⟨M, N, hMU, -, -, -, hNc, hN, -⟩ := hl U hU
  have hβ : Continuous (fun p : V × V => β p.1 p.2) :=
    IsModuleTopology.continuous_bilinear_of_finite_left β
  have hev : ∀ᶠ w in 𝓝 (0 : V), ∀ x ∈ tsupport f, ψ (β x w) = 1 := by
    refine hf.2.isCompact.eventually_forall_of_forall_eventually fun x _ => ?_
    have hc : Continuous (fun z : V × V => β z.2 z.1) := hβ.comp continuous_swap
    have ho : IsOpen {z : V × V | ‖β z.2 z.1‖ < 1} := isOpen_lt (continuous_norm.comp hc) continuous_const
    have hmem : ((0 : V), x) ∈ {z : V × V | ‖β z.2 z.1‖ < 1} := by simp
    filter_upwards [ho.mem_nhds hmem] with z hz
    exact hψ.1 _ hz.le
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro y
    have hev' : ∀ᶠ y' in 𝓝 y, ∀ x ∈ tsupport f, ψ (β x (y' - y)) = 1 := by
      have ht : Tendsto (fun y' : V => y' - y) (𝓝 y) (𝓝 0) := by
        have h := (continuous_sub_right y).tendsto y
        rwa [sub_self] at h
      exact ht.eventually hev
    filter_upwards [hev'] with y' hy'
    simp only [fourB]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport f
    · have : β x y' = β x y + β x (y' - y) := by simp
      simp only [this, AddChar.map_add_eq_mul, hy' x hx, mul_one]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · refine HasCompactSupport.intro hNc fun y hy => ?_
    have : ¬ ∀ x ∈ M, ψ (β x y) = 1 := fun h => hy ((hN y).2 h)
    push_neg at this
    obtain ⟨m, hm, hne⟩ := this
    refine AbsInv.integral_eq_zero_of_translate μ _ m _ hne fun x => ?_
    simp only [map_add, LinearMap.add_apply, AddChar.map_add_eq_mul, hUinv M hMU x m hm]
    ring
end GlobalTheory.JR.SelfDualUniq
