-- Prove2me | solution 1 for OAI.AffineBernstein.normalized_harmonic_no_two_extremes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:19:27.967965+00:00
-- url     : https://prove2.me/submissions/5e958293-25b4-4fcf-b251-1ab9a0d35259

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_normalized_critical_density
import Theorems.Thm_OAI_AffineBernstein_normalized_log_variance

section
-- module Solutions.OAIQ22_AB.AffineBernstein_WeightedDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section WeightedDivergence

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem contDiffAt_dirDeriv {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (v : E) :
    ContDiffAt ℝ ∞ (dirDeriv v f) x :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

end WeightedDivergence

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_MatrixConcavity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

/-- On an open set the Hessian is additive; no extension outside that set is used. -/
theorem hessian_add_on {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u v : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    {x : Space n} (hx : x ∈ Ω) :
    hessian (fun y => u y + v y) x = hessian u x + hessian v x := by
  ext i j
  have he : (fun y => fderiv ℝ (fun z => u z + v z) y (coordinateVector n j)) =ᶠ[nhds x]
      (fun y => fderiv ℝ u y (coordinateVector n j) + fderiv ℝ v y (coordinateVector n j)) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    rw [fderiv_fun_add ((hu.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      ((hv.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))]
    rfl
  change fderiv ℝ (fun y => fderiv ℝ (fun z => u z + v z) y (coordinateVector n j)) x (coordinateVector n i) =
    fderiv ℝ (fun y => fderiv ℝ u y (coordinateVector n j)) x (coordinateVector n i) +
    fderiv ℝ (fun y => fderiv ℝ v y (coordinateVector n j)) x (coordinateVector n i)
  rw [he.fderiv_eq]
  change fderiv ℝ (fun y => dirDeriv (coordinateVector n j) u y + dirDeriv (coordinateVector n j) v y) x (coordinateVector n i) =
    fderiv ℝ (dirDeriv (coordinateVector n j) u) x (coordinateVector n i) +
    fderiv ℝ (dirDeriv (coordinateVector n j) v) x (coordinateVector n i)
  rw [fderiv_fun_add
    ((contDiffAt_dirDeriv (hu.contDiffAt (hΩ.mem_nhds hx)) (coordinateVector n j)).differentiableAt (by simp))
    ((contDiffAt_dirDeriv (hv.contDiffAt (hΩ.mem_nhds hx)) (coordinateVector n j)).differentiableAt (by simp))]
  rfl

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ConvexSmoothMax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology

lemma hessian_sub_on {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u v : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    {x : Space n} (hx : x ∈ Ω) :
    hessian (fun y => u y-v y) x = hessian u x-hessian v x := by
  have h := hessian_add_on hΩ (hu.sub hv) hv hx
  have he : (fun y => (u y-v y)+v y) = u := by funext y; ring
  rw [he] at h
  exact eq_sub_iff_add_eq.mpr h.symm

end AffineBernstein
end

end OAI
end

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

lemma inverseHessianTrace_sub {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {u f g : Space n → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    {x : Space n} (hx : x ∈ O) :
    inverseHessianTrace u (fun y => f y-g y) x = inverseHessianTrace u f x - inverseHessianTrace u g x := by
  simp only [inverseHessianTrace,hessian_sub_on hO hf hg hx,Matrix.sub_apply,mul_sub,Finset.sum_sub_distrib]

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
-- module Solutions.OAIQ22_AB.AffineBernstein_BoundedHarmonic
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

section BoundedHarmonic

lemma inverseHessianTrace_constant {n : ℕ} (u : Space n → ℝ) (c : ℝ) (x : Space n) :
    inverseHessianTrace u (fun _ => c) x = 0 := by
  simp [inverseHessianTrace,hessian]

/-- A quantitative oscillation reduction on an actual normalized section.
This is proved from the ABP low-set and logarithmic energy estimates above. -/
theorem normalized_harmonic_no_two_extremes_oai {n : ℕ} (hn : 1 ≤ n) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R) {d : ℝ} (hd : 0 < d) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v : Space n → ℝ, BalancedNormalized ρ R v →
      ∀ F : Space n → ℝ, ContDiff ℝ ∞ F → (∀ x, 0 ≤ F x ∧ F x ≤ d) →
      (∀ x, inverseHessianTrace v F x = 0) →
      ∀ a ∈ Metric.ball (0:Space n) (1/64:ℝ), ∀ b ∈ Metric.ball (0:Space n) (1/64:ℝ),
        ¬(F a ≤ ε ∧ d-F b ≤ ε) := by
  obtain ⟨δ,hδ,Hδ⟩ := normalized_critical_density hn hρ hρ1 hR
  obtain ⟨V,hV,HV⟩ := normalized_log_variance hρ hρ1 hR (n := n)
  let T : ℝ := V/δ^2+2
  have hδs : 0 < δ^2 := sq_pos_of_pos hδ
  have hT : 2 ≤ T := by
    have H : 0 ≤ V/δ^2 := div_nonneg hV hδs.le
    dsimp [T]; linarith
  have hDT : δ^2*T=V+2*δ^2 := by dsimp [T]; field_simp [ne_of_gt hδ]
  have hbig : V < δ^2*T^2 := by
    have hsq : T ≤ T^2 := by nlinarith
    have H := mul_le_mul_of_nonneg_left hsq hδs.le
    nlinarith
  let ε := d/(8*Real.exp T)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hE : 1 ≤ Real.exp T := Real.one_le_exp (by linarith)
  have hεeq : 8*ε*Real.exp T=d := by dsimp [ε]; field_simp
  have hεsmall : 8*ε ≤ d := by nlinarith
  refine ⟨ε,hε,?_⟩
  intro v hv F hF hFrange hLF a ha b hb hab
  let s := fun x => F x+ε
  let r := fun x => d-F x+ε
  have hs : ContDiff ℝ ∞ s := hF.add contDiff_const
  have hr : ContDiff ℝ ∞ r := (contDiff_const.sub hF).add contDiff_const
  have hspos (x : Space n) : 0 < s x := by dsimp [s]; linarith [(hFrange x).1]
  have hrpos (x : Space n) : 0 < r x := by dsimp [r]; linarith [(hFrange x).2]
  have hLs (x : Space n) : inverseHessianTrace v s x ≤ 0 := by
    rw [show s=(fun y => F y+ε) from rfl,inverseHessianTrace_add_constant,hLF]
  have hLr (x : Space n) : inverseHessianTrace v r x ≤ 0 := by
    rw [show r=(fun y => (d-F y)+ε) from rfl,inverseHessianTrace_add_constant,
      inverseHessianTrace_sub isOpen_univ contDiffOn_const hF.contDiffOn (mem_univ x),
      inverseHessianTrace_constant,hLF,sub_zero]
  let K := Metric.closedBall (0:Space n) (1/16:ℝ)
  let A := {x | x ∈ K ∧ s x ≤ 4*ε}
  let B := {x | x ∈ K ∧ r x ≤ 4*ε}
  have hA := compact_sublevel_in_compact (isCompact_closedBall (0:Space n) (1/16:ℝ)) hs.continuous (4*ε)
  have hB := compact_sublevel_in_compact (isCompact_closedBall (0:Space n) (1/16:ℝ)) hr.continuous (4*ε)
  have hAl : δ ≤ (volume A).toReal := by
    have H := Hδ v hv s hs (fun x => (hspos x).le) hLs a ha (2*ε) (by positivity)
      (by dsimp [s]; linarith [hab.1])
    simpa only [show 2*(2*ε)=4*ε by ring] using H
  have hBl : δ ≤ (volume B).toReal := by
    have H := Hδ v hv r hr (fun x => (hrpos x).le) hLr b hb (2*ε) (by positivity)
      (by dsimp [r]; linarith [hab.2])
    simpa only [show 2*(2*ε)=4*ε by ring] using H
  have hlogeq : Real.log (d/2)-Real.log (4*ε)=T := by
    rw [← Real.log_div (by positivity : d/2≠0) (by positivity : 4*ε≠0)]
    have he : (d/2)/(4*ε)=Real.exp T := by dsimp [ε]; field_simp; ring
    rw [he,Real.log_exp]
  have hsep : ∀ x ∈ A, ∀ y ∈ B, T ≤ Real.log (s y)-Real.log (s x) := by
    intro x hx y hy
    have hylo : d/2 ≤ s y := by
      have HY : r y ≤ 4*ε := hy.2
      dsimp [r] at HY
      dsimp [s]
      linarith
    have hxl := Real.log_le_log (hspos x) hx.2
    have hyl := Real.log_le_log (by positivity : (0:ℝ)<d/2) hylo
    linarith
  have hlow := variance_lower_of_separated_sets (isCompact_closedBall (0:Space n) (1/16:ℝ)) hA hB
    (fun _ hx => hx.1) (fun _ hx => hx.1) (hs.log (fun x => (hspos x).ne')).continuous
    (by linarith : 0 ≤ T) hsep
  have hupper := HV v hv s hs hspos hLs
  have hprod : δ^2 ≤ (volume A).toReal*(volume B).toReal := by
    simpa only [pow_two] using mul_le_mul hAl hBl hδ.le (ENNReal.toReal_nonneg)
  have H := mul_le_mul_of_nonneg_right hprod (sq_nonneg T)
  exact (not_lt_of_ge (H.trans (hlow.trans hupper))) hbig

end BoundedHarmonic


end
end AffineBernstein
end

end OAI
end

theorem solution : type_of% @OAI.AffineBernstein.normalized_harmonic_no_two_extremes_oai := @OAI.AffineBernstein.normalized_harmonic_no_two_extremes_oai
