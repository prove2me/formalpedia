-- Prove2me | solution 1 for GlobalTheory.SchwartzFstOp.remainder_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:36:17.953384+00:00
-- url     : https://prove2.me/submissions/3b5656f2-8a90-44cd-9749-1de220622817

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslateTaylorSecondOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasFderivAtSchwartzOperatorFirst
import Theorems.Thm_GlobalTheory_T_schwartz_translate_taylor_second_order


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp
noncomputable section
open Filter Topology Asymptotics
open GlobalTheory GlobalTheory.SchwartzFstOp
variable {V W V' E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.SchwartzFstOp
theorem _root_.solution (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (x' : V') :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : V', ‖v‖ ≤ 1 → ∀ z : W,
      ‖T (sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f - f - lineSnd v f)) z‖
        ≤ K * ‖v‖ ^ 2 := by
  let q : Seminorm ℂ 𝓢(V × V', ℂ) :=
    (SchwartzMap.seminorm ℂ 0 0).comp (T.comp (sliceCLM x')).toLinearMap
  have hq : Continuous q :=
    ((schwartz_withSeminorms ℂ W E).continuous_seminorm (0, 0)).comp (T.comp (sliceCLM x')).continuous
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (V × V') ℂ) q hq
  choose D hD using fun i : ℕ × ℕ => GlobalTheory.T.schwartz_translate_taylor_second_order f i.1 i.2
  refine ⟨(C : ℝ) * ∑ i ∈ s, |D i|, by positivity, fun v hv z => ?_⟩
  set g := SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f - f - lineSnd v f with hg
  have ha : ‖((0 : V), v)‖ = ‖v‖ := by simp [Prod.norm_def]
  have h1 : ‖T (sliceCLM x' g) z‖ ≤ q g := SchwartzMap.norm_le_seminorm ℂ _ _
  have h2 : q g ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ (V × V') ℂ)) g := by
    have := hC g
    simpa [Seminorm.smul_apply, NNReal.smul_def] using this
  have h3 : (s.sup (schwartzSeminormFamily ℂ (V × V') ℂ)) g ≤ (∑ i ∈ s, |D i|) * ‖v‖ ^ 2 := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro i hi
    have hDi := hD i ((0 : V), v) (by rw [ha]; exact hv)
    rw [ha] at hDi
    calc schwartzSeminormFamily ℂ (V × V') ℂ i g ≤ D i * ‖v‖ ^ 2 := hDi
      _ ≤ |D i| * ‖v‖ ^ 2 := by gcongr; exact le_abs_self _
      _ ≤ (∑ j ∈ s, |D j|) * ‖v‖ ^ 2 := by
          gcongr; exact Finset.single_le_sum (fun j _ => abs_nonneg (D j)) hi
  calc ‖T (sliceCLM x' g) z‖ ≤ q g := h1
    _ ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ (V × V') ℂ)) g := h2
    _ ≤ (C : ℝ) * ((∑ i ∈ s, |D i|) * ‖v‖ ^ 2) := by gcongr
    _ = (C : ℝ) * (∑ i ∈ s, |D i|) * ‖v‖ ^ 2 := by ring
end GlobalTheory.SchwartzFstOp
