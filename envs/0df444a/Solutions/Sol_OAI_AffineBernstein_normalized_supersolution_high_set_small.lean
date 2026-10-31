-- Prove2me | solution 1 for OAI.AffineBernstein.normalized_supersolution_high_set_small
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:22:24.133028+00:00
-- url     : https://prove2.me/submissions/518470ab-1bea-470f-a53e-baed15833e52

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_normalized_critical_density
import Theorems.Thm_OAI_AffineBernstein_normalized_log_variance

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricAffineArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- The augmented tangent frame, with its transverse column last. -/

lemma hessian_add_constant {n : ℕ} (f : Space n → ℝ) (r : ℝ) (x : Space n) :
    hessian (fun y => f y + r) x = hessian f x := by
  ext i j
  simp only [hessian, fderiv_add_const]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_EllipticComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section EllipticComparison
open Filter
open scoped Topology

lemma inverseHessianTrace_add_constant {n : ℕ} {f u : Space n → ℝ} (c : ℝ) (x : Space n) :
    inverseHessianTrace u (fun y => f y+c) x = inverseHessianTrace u f x := by
  simp only [inverseHessianTrace,hessian_add_constant]

end EllipticComparison


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_WeightedPoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section WeightedPoincare

lemma compact_integrable_pair {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    [T2Space X] [T2Space Y] [SecondCountableTopology X] [SecondCountableTopology Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν] [IsFiniteMeasureOnCompacts (μ.prod ν)]
    {K : Set X} {S : Set Y} (hK : IsCompact K) (hS : IsCompact S)
    {F : X × Y → ℝ} (hF : Continuous F) :
    Integrable F ((μ.restrict K).prod (ν.restrict S)) := by
  rw [Measure.prod_restrict K S]
  exact ContinuousOn.integrableOn_compact (hK.prod hS) hF.continuousOn

end WeightedPoincare



end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_VarianceSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section VarianceSeparation

lemma variance_lower_of_separated_sets {n : ℕ} {K A B : Set (Space n)}
    (hK : IsCompact K) (hA : IsCompact A) (hB : IsCompact B)
    (hAK : A ⊆ K) (hBK : B ⊆ K) {f : Space n → ℝ} (hf : Continuous f)
    {L : ℝ} (hL : 0 ≤ L) (hsep : ∀ x ∈ A, ∀ y ∈ B, L ≤ f y-f x) :
    (volume A).toReal*(volume B).toReal*L^2 ≤
      ∫ x in K, ∫ y in K, (f y-f x)^2 := by
  let : IsFiniteMeasure (volume.restrict A) := ⟨by simpa using hA.measure_lt_top (μ := volume)⟩
  let : IsFiniteMeasure (volume.restrict B) := ⟨by simpa using hB.measure_lt_top (μ := volume)⟩
  let F := fun p : Space n × Space n => (f p.2-f p.1)^2
  have hF : Continuous F := by fun_prop
  have hFK := compact_integrable_pair (μ := volume) (ν := volume) hK hK hF
  have hFB := compact_integrable_pair (μ := volume) (ν := volume) hA hB hF
  have hFAK := compact_integrable_pair (μ := volume) (ν := volume) hA hK hF
  have hlo : (∫ x in A, ∫ y in B, L^2) ≤ ∫ x in A, ∫ y in B, F (x,y) := by
    apply setIntegral_mono_on (integrable_const _) hFB.integral_prod_left hA.measurableSet
    intro x hx
    apply setIntegral_mono_on (integrable_const _)
      (ContinuousOn.integrableOn_compact hB (hF.comp (continuous_const.prodMk continuous_id)).continuousOn)
      hB.measurableSet
    intro y hy
    exact (sq_le_sq₀ hL (hL.trans (hsep x hx y hy))).mpr (hsep x hx y hy)
  have hmid : (∫ x in A, ∫ y in B, F (x,y)) ≤ ∫ x in A, ∫ y in K, F (x,y) := by
    apply setIntegral_mono_on hFB.integral_prod_left hFAK.integral_prod_left hA.measurableSet
    intro point _
    apply setIntegral_mono_set
      (ContinuousOn.integrableOn_compact hK (hF.comp (continuous_const.prodMk continuous_id)).continuousOn)
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      (Filter.Eventually.of_forall hBK)
  have hhi : (∫ x in A, ∫ y in K, F (x,y)) ≤ ∫ x in K, ∫ y in K, F (x,y) :=
    setIntegral_mono_set hFK.integral_prod_left
      (Filter.Eventually.of_forall (fun _ => MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)))
      (Filter.Eventually.of_forall hAK)
  have hh := hlo.trans (hmid.trans hhi)
  simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_assoc] using hh

lemma compact_sublevel_in_compact {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    {f : Space n → ℝ} (hf : Continuous f) (t : ℝ) :
    IsCompact {x | x ∈ K ∧ f x ≤ t} :=
  hK.inter_right (isClosed_le hf continuous_const)

end VarianceSeparation


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SupersolutionHighSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section SupersolutionHighSet

/-- A small value of a nonnegative supersolution forces almost all of the
fixed inner ball below any prescribed positive threshold. The small value
is quantitative and uniform in the generated normalized graph. -/
theorem normalized_supersolution_high_set_small_oai {n : ℕ} (hn : 1 ≤ n) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R) {η β : ℝ} (hη : 0 < η) (hβ : 0 < β) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v : Space n → ℝ, BalancedNormalized ρ R v →
      ∀ s : Space n → ℝ, ContDiff ℝ ∞ s → (∀ x, 0 ≤ s x) →
      (∀ x, inverseHessianTrace v s x ≤ 0) → ∀ a ∈ Metric.ball (0:Space n) (1/64:ℝ),
      s a ≤ ε → (volume {x | x ∈ Metric.closedBall (0:Space n) (1/16:ℝ) ∧ η ≤ s x}).toReal < β := by
  obtain ⟨δ,hδ,Hδ⟩ := normalized_critical_density hn hρ hρ1 hR
  obtain ⟨V,hV,HV⟩ := normalized_log_variance hρ hρ1 hR (n := n)
  let T := V/(δ*β)+2
  have hdb : 0 < δ*β := mul_pos hδ hβ
  have hT : 2 ≤ T := by have H := div_nonneg hV hdb.le; dsimp [T]; linarith
  have hDT : δ*β*T=V+2*δ*β := by dsimp [T]; field_simp
  have hbig : V < δ*β*T^2 := by
    have hsq : T ≤ T^2 := by nlinarith
    have H := mul_le_mul_of_nonneg_left hsq hdb.le
    nlinarith
  let ε := η/(4*Real.exp T)
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε,hε,?_⟩
  intro v hv s hs hspos hLs a ha hsa
  let r := fun x => s x+ε
  have hr : ContDiff ℝ ∞ r := hs.add contDiff_const
  have hrpos (x : Space n) : 0 < r x := by dsimp [r]; linarith [hspos x]
  have hLr (x : Space n) : inverseHessianTrace v r x ≤ 0 := by
    simpa only [r,inverseHessianTrace_add_constant] using hLs x
  let K := Metric.closedBall (0:Space n) (1/16:ℝ)
  let A := {x | x ∈ K ∧ r x ≤ 4*ε}
  let B := {x | x ∈ K ∧ η ≤ s x}
  have hK : IsCompact K := isCompact_closedBall _ _
  have hA : IsCompact A := compact_sublevel_in_compact hK hr.continuous (4*ε)
  have hB : IsCompact B := hK.inter_right (isClosed_le continuous_const hs.continuous)
  have hAl : δ ≤ (volume A).toReal := by
    have H := Hδ v hv r hr (fun x => (hrpos x).le) hLr a ha (2*ε) (by positivity)
      (by dsimp [r]; linarith)
    simpa only [show 2*(2*ε)=4*ε by ring] using H
  have hlogeq : Real.log η-Real.log (4*ε)=T := by
    rw [← Real.log_div hη.ne' (by positivity : 4*ε≠0)]
    have he : η/(4*ε)=Real.exp T := by dsimp [ε]; field_simp
    rw [he,Real.log_exp]
  have hsep : ∀ x ∈ A, ∀ y ∈ B, T ≤ Real.log (r y)-Real.log (r x) := by
    intro x hx y hy
    have hylo : η ≤ r y := by dsimp [r]; linarith [hy.2]
    have hxl := Real.log_le_log (hrpos x) hx.2
    have hyl := Real.log_le_log hη hylo
    linarith
  have hlow := variance_lower_of_separated_sets hK hA hB
    (fun x hx => hx.1) (fun x hx => hx.1) (hr.log (fun x => (hrpos x).ne')).continuous
    (by linarith : 0 ≤ T) hsep
  have hupper := HV v hv r hr hrpos hLr
  change (volume B).toReal < β
  by_contra h
  have hBl : β ≤ (volume B).toReal := le_of_not_gt h
  have hprod : δ*β ≤ (volume A).toReal*(volume B).toReal :=
    mul_le_mul hAl hBl hβ.le ENNReal.toReal_nonneg
  have H := mul_le_mul_of_nonneg_right hprod (sq_nonneg T)
  exact (not_lt_of_ge (H.trans (hlow.trans hupper))) hbig

end SupersolutionHighSet


end
end AffineBernstein
end

end OAI
end

theorem solution : type_of% @OAI.AffineBernstein.normalized_supersolution_high_set_small_oai := @OAI.AffineBernstein.normalized_supersolution_high_set_small_oai
