-- Prove2me | solution 1 for GlobalTheory.PartRed.IntEntry.integrable_red
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:37:00.803174+00:00
-- url     : https://prove2.me/submissions/72bff3ab-a51d-4603-8e6c-b30aa75bf1e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionIntegrateEntryOfTranslation
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_StepData_IntM_neg
import Theorems.Thm_GlobalTheory_StepData_MaxM_neg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.PartRed GlobalTheory.PartRed.IntEntry
namespace GlobalTheory.PartRed.IntEntry
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → ∀ x : Matrix R Q k, Integrable (fun y : I → k => Φ (fillAt β E I x y) * (ψ (-w (fillAt β E I x y)) : ℂ)) (Measure.pi fun _ => ν) := by
  intro k _ _ _ _ _ _ ψ ν hψ hν R Q _ _ _ _ w β E I Φ hΦ x
  haveI := secondCountable k
  haveI := t2Space k
  haveI : LocallyCompactSpace k := inferInstance
  haveI : SigmaFinite ν := inferInstance
  haveI : (Measure.pi fun _ : I => ν).IsAddHaarMeasure := inferInstance
  have hf : Continuous (fillAt β E I x) := by
    refine continuous_matrix fun r q => ?_
    simp only [fillAt, Matrix.of_apply]
    by_cases h : (r, q) ∈ I
    · simp only [dif_pos h]; fun_prop
    · simp only [dif_neg h]; fun_prop
  have hw : Continuous w := by
    have : (w : Matrix R Q k → k) = fun t => ∑ r, ∑ q, t r q * w (Matrix.single r q 1) := by
      funext t
      conv_lhs => rw [Matrix.matrix_eq_sum_single t]
      simp only [map_sum]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun q _ => ?_
      rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this]
    fun_prop
  have hc : Continuous fun y : I → k => Φ (fillAt β E I x y) * (ψ (-w (fillAt β E I x y)) : ℂ) :=
    (hΦ.1.continuous.comp hf).mul (continuous_subtype_val.comp (hψ.comp (hw.comp hf).neg))
  refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro
    (K := Set.univ.pi fun i : I => (fun t : Matrix R Q k => t i.1.1 i.1.2) '' tsupport Φ)
    (isCompact_univ_pi fun i => hΦ.2.image (by fun_prop)) fun y hy => ?_)
  rw [image_eq_zero_of_notMem_tsupport (f := Φ) fun h => hy fun i _ => ⟨_, h, ?_⟩, zero_mul]
  simp [fillAt, i.2]
end GlobalTheory.PartRed.IntEntry
