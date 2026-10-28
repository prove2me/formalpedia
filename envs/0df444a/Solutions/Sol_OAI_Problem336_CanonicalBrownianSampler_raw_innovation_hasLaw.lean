-- Prove2me | solution 1 for OAI.Problem336.CanonicalBrownianSampler.raw_innovation_hasLaw
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:39:32.235291+00:00
-- url     : https://prove2.me/submissions/ec08e13c-eead-44f3-a9cb-cf4b096ec21c

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.List.Nodup
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Definitions.Def_OAIS336000

section
-- module Solutions.OAIS_P336.SpanningForest_FinitePosterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators ProbabilityTheory

namespace Problem336.FinitePosterior

variable {Θ Y : Type*} [Fintype Θ] [MeasurableSpace Θ]
    [MeasurableSingletonClass Θ] [MeasurableSpace Y]

omit [MeasurableSingletonClass Θ] in
lemma measurable_mixtureDensity (π : Measure Θ) (f : Θ → Y → ℝ≥0∞)
    (hf : ∀ θ, Measurable (f θ)) : Measurable (mixtureDensity π f) := by
  unfold mixtureDensity
  fun_prop

theorem marginal_eq_withDensity (π : Measure Θ) (κ : Kernel Θ Y) (ν : Measure Y)
    (f : Θ → Y → ℝ≥0∞) (hf : ∀ θ, Measurable (f θ))
    (hκ : ∀ θ, κ θ = ν.withDensity (f θ)) :
    κ ∘ₘ π = ν.withDensity (mixtureDensity π f) := by
  calc
    κ ∘ₘ π = Measure.sum (fun θ => π {θ} • ν.withDensity (f θ)) := by
      rw [Measure.comp_eq_sum_of_countable]
      simp_rw [hκ]
    _ = Measure.sum (fun θ => ν.withDensity (fun y => π {θ} * f θ y)) := by
      congr 1
      funext θ
      exact (withDensity_smul (π {θ}) (hf θ)).symm
    _ = ν.withDensity (∑' θ, fun y => π {θ} * f θ y) := by
      exact (withDensity_tsum (fun θ => measurable_const.mul (hf θ))).symm
    _ = ν.withDensity (mixtureDensity π f) := by
      congr 1
      ext y
      simp [mixtureDensity]

omit [MeasurableSingletonClass Θ] [MeasurableSpace Y] in
lemma mixtureDensity_ne_top (π : Measure Θ) [IsFiniteMeasure π]
    (f : Θ → Y → ℝ≥0∞) (hf : ∀ θ y, f θ y ≠ ∞) (y : Y) :
    mixtureDensity π f y ≠ ∞ := by
  unfold mixtureDensity
  exact ENNReal.sum_ne_top.mpr (fun θ _ => ENNReal.mul_ne_top (measure_ne_top π _) (hf θ y))

omit [MeasurableSpace Y] in

lemma mixtureDensity_ne_zero_of_positive (π : Measure Θ) [IsProbabilityMeasure π]
    (f : Θ → Y → ℝ≥0∞) (hf : ∀ θ y, f θ y ≠ 0) (y : Y) :
    mixtureDensity π f y ≠ 0 := by
  have hsum : (∑ θ, π {θ}) = 1 := by simp
  have hpos : 0 < ∑ θ, π {θ} := by rw [hsum]; exact zero_lt_one
  obtain ⟨θ, hθ, hpθ⟩ := Finset.sum_pos_iff.mp hpos
  apply ne_of_gt
  exact Finset.sum_pos_iff.mpr ⟨θ, hθ, ENNReal.mul_pos hpθ.ne' (hf θ y)⟩

omit [MeasurableSingletonClass Θ] [MeasurableSpace Y] in

lemma mixtureDensity_toReal (π : Measure Θ) [IsFiniteMeasure π]
    (f : Θ → Y → ℝ≥0∞) (hf : ∀ θ y, f θ y ≠ ∞) (y : Y) :
    (mixtureDensity π f y).toReal = ∑ θ, (π {θ}).toReal * (f θ y).toReal := by
  rw [mixtureDensity, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro θ _
    exact ENNReal.mul_ne_top (measure_ne_top π _) (hf θ y)

theorem likelihood_rnDeriv_marginal (π : Measure Θ) [IsFiniteMeasure π]
    (κ : Kernel Θ Y) [IsFiniteKernel κ] (ν : Measure Y) [SigmaFinite ν]
    (f : Θ → Y → ℝ≥0∞) (hf : ∀ θ, Measurable (f θ))
    (hfinite : ∀ θ y, f θ y ≠ ∞)
    (hpositive : ∀ y, mixtureDensity π f y ≠ 0)
    (hκ : ∀ θ, κ θ = ν.withDensity (f θ)) (θ : Θ) :
    (κ θ).rnDeriv (κ ∘ₘ π) =ᵐ[ν]
      fun y => f θ y / mixtureDensity π f y := by
  have hright := Measure.rnDeriv_withDensity_right (κ θ) ν
    (measurable_mixtureDensity π f hf).aemeasurable
    (Filter.Eventually.of_forall hpositive)
    (Filter.Eventually.of_forall (mixtureDensity_ne_top π f hfinite))
  have hleft : (κ θ).rnDeriv ν =ᵐ[ν] f θ := by
    rw [hκ θ]
    exact Measure.rnDeriv_withDensity ν (hf θ)
  rw [marginal_eq_withDensity π κ ν f hf hκ]
  filter_upwards [hright, hleft] with y hy hy'
  rw [hy, hy', div_eq_mul_inv, mul_comm]

theorem posterior_singleton_formula [StandardBorelSpace Θ] [Nonempty Θ]
    (π : Measure Θ) [IsFiniteMeasure π]
    (κ : Kernel Θ Y) [IsFiniteKernel κ] (ν : Measure Y) [SigmaFinite ν]
    (f : Θ → Y → ℝ≥0∞) (hf : ∀ θ, Measurable (f θ))
    (hfinite : ∀ θ y, f θ y ≠ ∞)
    (hpositive : ∀ y, mixtureDensity π f y ≠ 0)
    (hκ : ∀ θ, κ θ = ν.withDensity (f θ)) :
    ∀ᵐ y ∂(κ ∘ₘ π), ∀ θ,
      (κ†π) y {θ} = π {θ} * f θ y / mixtureDensity π f y := by
  have hac : κ ∘ₘ π ≪ ν := by
    rw [marginal_eq_withDensity π κ ν f hf hκ]
    exact withDensity_absolutelyContinuous ν _
  have hrn : ∀ᵐ y ∂(κ ∘ₘ π), ∀ θ,
      (κ θ).rnDeriv (κ ∘ₘ π) y = f θ y / mixtureDensity π f y := by
    exact hac.ae_le (ae_all_iff.mpr (fun θ =>
      likelihood_rnDeriv_marginal π κ ν f hf hfinite hpositive hκ θ))
  filter_upwards [posterior_eq_withDensity_of_countable κ π, hrn] with y hy hrny
  intro θ
  rw [hy]
  simp only [withDensity_apply _ (measurableSet_singleton θ), lintegral_singleton, hrny θ]
  rw [mul_comm, mul_div_assoc]

theorem posterior_mean_formula [StandardBorelSpace Θ] [Nonempty Θ]
    (π : Measure Θ) [IsFiniteMeasure π]
    (κ : Kernel Θ Y) [IsFiniteKernel κ] (ν : Measure Y) [SigmaFinite ν]
    (f : Θ → Y → ℝ≥0∞) (hf : ∀ θ, Measurable (f θ))
    (hfinite : ∀ θ y, f θ y ≠ ∞)
    (hpositive : ∀ y, mixtureDensity π f y ≠ 0)
    (hκ : ∀ θ, κ θ = ν.withDensity (f θ)) (g : Θ → ℝ) :
    ∀ᵐ y ∂(κ ∘ₘ π),
      (∫ θ, g θ ∂(κ†π) y) =
        (∑ θ, (π {θ}).toReal * (f θ y).toReal * g θ) /
          (mixtureDensity π f y).toReal := by
  filter_upwards [posterior_singleton_formula π κ ν f hf hfinite hpositive hκ]
    with y hy
  rw [integral_fintype (Integrable.of_finite)]
  simp only [Measure.real, hy, ENNReal.toReal_div, ENNReal.toReal_mul, smul_eq_mul]
  simp_rw [div_mul_eq_mul_div]
  exact (Finset.sum_div _ _ _).symm

theorem condExp_eq_posterior_mean_of_jointLaw
    [StandardBorelSpace Θ] [Nonempty Θ]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → Θ) (Yobs : Ω → Y) (hX : Measurable X) (hY : Measurable Yobs)
    (π : Measure Θ) [IsFiniteMeasure π]
    (κ : Kernel Θ Y) [IsFiniteKernel κ]
    (hjoint : P.map (fun ω => (X ω, Yobs ω)) = π ⊗ₘ κ) (g : Θ → ℝ) :
    P[fun ω => g (X ω) | (inferInstance : MeasurableSpace Y).comap Yobs] =ᵐ[P]
      fun ω => ∫ θ, g θ ∂(κ†π) (Yobs ω) := by
  have hmapY : P.map Yobs = κ ∘ₘ π := by
    calc
      P.map Yobs = (P.map (fun ω => (X ω, Yobs ω))).map Prod.snd := by
        rw [Measure.map_map measurable_snd (hX.prodMk hY)]
        rfl
      _ = (π ⊗ₘ κ).snd := by rw [hjoint]; rfl
      _ = κ ∘ₘ π := Measure.snd_compProd π κ
  have hswap : P.map (fun ω => (Yobs ω, X ω)) = (π ⊗ₘ κ).map Prod.swap := by
    rw [← hjoint, Measure.map_map measurable_swap (hX.prodMk hY)]
    rfl
  have hkernel : condDistrib X Yobs P =ᵐ[P.map Yobs] κ†π := by
    apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hY hX
    rw [hmapY, compProd_posterior_eq_map_swap]
    exact hswap
  have hgint : Integrable (fun ω => g (X ω)) P :=
    (show Integrable g (P.map X) from Integrable.of_finite).comp_measurable hX
  have hcond := condExp_ae_eq_integral_condDistrib hY hX.aemeasurable
    (measurable_of_countable g).stronglyMeasurable hgint
  have hkernel' := ae_of_ae_map hY.aemeasurable hkernel
  filter_upwards [hcond, hkernel'] with ω hω hkω
  rwa [hkω] at hω

theorem condExp_eq_likelihood_ratio_of_jointLaw
    [StandardBorelSpace Θ] [Nonempty Θ]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → Θ) (Yobs : Ω → Y) (hX : Measurable X) (hY : Measurable Yobs)
    (π : Measure Θ) [IsFiniteMeasure π]
    (κ : Kernel Θ Y) [IsFiniteKernel κ]
    (hjoint : P.map (fun ω => (X ω, Yobs ω)) = π ⊗ₘ κ)
    (ν : Measure Y) [SigmaFinite ν]
    (f : Θ → Y → ℝ≥0∞) (hf : ∀ θ, Measurable (f θ))
    (hfinite : ∀ θ y, f θ y ≠ ∞)
    (hpositive : ∀ y, mixtureDensity π f y ≠ 0)
    (hκ : ∀ θ, κ θ = ν.withDensity (f θ)) (g : Θ → ℝ) :
    P[fun ω => g (X ω) | (inferInstance : MeasurableSpace Y).comap Yobs] =ᵐ[P]
      fun ω => (∑ θ, (π {θ}).toReal * (f θ (Yobs ω)).toReal * g θ) /
        (mixtureDensity π f (Yobs ω)).toReal := by
  apply (condExp_eq_posterior_mean_of_jointLaw P X Yobs hX hY π κ hjoint g).trans
  have hmapY : P.map Yobs = κ ∘ₘ π := by
    calc
      P.map Yobs = (P.map (fun ω => (X ω, Yobs ω))).map Prod.snd := by
        rw [Measure.map_map measurable_snd (hX.prodMk hY)]
        rfl
      _ = (π ⊗ₘ κ).snd := by rw [hjoint]; rfl
      _ = κ ∘ₘ π := Measure.snd_compProd π κ
  have hpost := posterior_mean_formula π κ ν f hf hfinite hpositive hκ g
  rw [← hmapY] at hpost
  exact ae_of_ae_map hY.aemeasurable hpost

end Problem336.FinitePosterior

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_GaussianLikelihood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace Problem336.GaussianObservation

theorem pdf_binary_shift (v : ℝ≥0) (hv : v ≠ 0) (x y : ℝ)
    (hx : x = 0 ∨ x = 1) :
    gaussianPDFReal ((v : ℝ) * x) v y =
      gaussianPDFReal 0 v y * Real.exp ((y - (v : ℝ) / 2) * x) := by
  rcases hx with rfl | rfl
  · simp
  · have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    have hexp : -(y - (v : ℝ)) ^ 2 / (2 * (v : ℝ)) =
        -y ^ 2 / (2 * (v : ℝ)) + (y - (v : ℝ) / 2) := by
      field_simp
      ring
    simp only [mul_one, gaussianPDFReal, sub_zero]
    rw [hexp, Real.exp_add]
    ring

theorem pdf_binary_shift_ennreal (v : ℝ≥0) (hv : v ≠ 0) (x y : ℝ)
    (hx : x = 0 ∨ x = 1) :
    gaussianPDF ((v : ℝ) * x) v y =
      gaussianPDF 0 v y * ENNReal.ofReal (Real.exp ((y - (v : ℝ) / 2) * x)) := by
  simp only [gaussianPDF, pdf_binary_shift v hv x y hx,
    ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 v y)]

theorem gaussian_binary_shift_withDensity (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ)
    (hx : x = 0 ∨ x = 1) :
    gaussianReal ((v : ℝ) * x) v =
      (gaussianReal 0 v).withDensity
        (fun y => ENNReal.ofReal (Real.exp ((y - (v : ℝ) / 2) * x))) := by
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ hv,
    ← withDensity_mul volume (measurable_gaussianPDF 0 v) (by fun_prop)]
  congr 1
  funext y
  exact pdf_binary_shift_ennreal v hv x y hx

end Problem336.GaussianObservation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FiniteProductDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Problem336.GaussianObservation

theorem pi_withDensity_of_probability {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ ν : (i : ι) → Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, SigmaFinite (ν i)] (f : (i : ι) → α i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (hν : ∀ i, ν i = (μ i).withDensity (f i)) :
    Measure.pi ν = (Measure.pi μ).withDensity (fun y => ∏ i, f i (y i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  have hrect := MeasurableSet.univ_pi hs
  have hind : (Set.univ.pi s).indicator (fun y => ∏ i, f i (y i)) =
      (fun y => ∏ i, (s i).indicator (f i) (y i)) := by
    funext y
    by_cases hy : ∀ i, y i ∈ s i
    · rw [Set.indicator_of_mem (by simpa only [Set.mem_univ_pi] using hy)]
      apply Finset.prod_congr rfl
      intro i hi
      exact (Set.indicator_of_mem (hy i) (f i)).symm
    · rw [Set.indicator_of_notMem (by simpa only [Set.mem_univ_pi] using hy)]
      obtain ⟨i, hi⟩ := not_forall.mp hy
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi (f i))
  rw [withDensity_apply _ hrect, ← lintegral_indicator hrect, hind]
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun i (y : ∀ j, α j) => (s i).indicator (f i) (y i))
    (iIndepFun_pi (fun i => ((hf i).indicator (hs i)).aemeasurable))
    (fun i => ((hf i).indicator (hs i)).comp (measurable_pi_apply i))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [(measurePreserving_eval μ i).lintegral_comp ((hf i).indicator (hs i)),
    lintegral_indicator (hs i), hν i, withDensity_apply _ (hs i)]

theorem gaussian_pi_binary_shift_withDensity {ι : Type*} [Fintype ι]
    (v : ℝ≥0) (hv : v ≠ 0) (x : ι → ℝ) (hx : ∀ i, x i = 0 ∨ x i = 1) :
    Measure.pi (fun i => gaussianReal ((v : ℝ) * x i) v) =
      (Measure.pi (fun _ : ι => gaussianReal 0 v)).withDensity
        (fun y => ENNReal.ofReal (Real.exp (∑ i, (y i - (v : ℝ) / 2) * x i))) := by
  have h := pi_withDensity_of_probability
    (fun _ : ι => gaussianReal 0 v) (fun i => gaussianReal ((v : ℝ) * x i) v)
    (fun i y => ENNReal.ofReal (Real.exp ((y - (v : ℝ) / 2) * x i)))
    (fun _ => by fun_prop) (fun i => gaussian_binary_shift_withDensity v hv (x i) (hx i))
  simpa only [Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)] using h

end Problem336.GaussianObservation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_GaussianObservationKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Problem336.GaussianObservation

variable {ι α : Type*} [Fintype ι] [MeasurableSpace α]

theorem measurable_endpoint_likelihood (v : ℝ≥0) (ξ : α → ι → ℝ)
    (hξ : ∀ i, Measurable (fun a => ξ a i)) :
    Measurable (Function.uncurry
      (fun (a : α) (y : ι → ℝ) =>
        ENNReal.ofReal (Real.exp (∑ i, (y i - (v : ℝ) / 2) * ξ a i)))) := by
  change Measurable (fun q : α × (ι → ℝ) =>
    ENNReal.ofReal (Real.exp (∑ i, (q.2 i - (v : ℝ) / 2) * ξ q.1 i)))
  fun_prop

theorem endpointKernel_apply (v : ℝ≥0) (hv : v ≠ 0) (ξ : α → ι → ℝ)
    (hξ : ∀ i, Measurable (fun a => ξ a i))
    (hbinary : ∀ a i, ξ a i = 0 ∨ ξ a i = 1) (a : α) :
    endpointKernel v ξ a = Measure.pi (fun i => gaussianReal ((v : ℝ) * ξ a i) v) := by
  rw [endpointKernel, Kernel.withDensity_apply _ (measurable_endpoint_likelihood v ξ hξ),
    Kernel.const_apply]
  exact (gaussian_pi_binary_shift_withDensity v hv (ξ a) (hbinary a)).symm

theorem endpointKernel_markov (v : ℝ≥0) (hv : v ≠ 0) (ξ : α → ι → ℝ)
    (hξ : ∀ i, Measurable (fun a => ξ a i))
    (hbinary : ∀ a i, ξ a i = 0 ∨ ξ a i = 1) : IsMarkovKernel (endpointKernel v ξ) := by
  constructor
  intro a
  rw [endpointKernel_apply v hv ξ hξ hbinary a]
  infer_instance

theorem centered_gaussian_pi_map_shift (v : ℝ≥0) (z : ι → ℝ) :
    (Measure.pi (fun _ : ι => gaussianReal 0 v)).map (fun y i => z i + y i) =
      Measure.pi (fun i => gaussianReal (z i) v) := by
  rw [Measure.pi_map_pi (fun _ => by fun_prop)]
  congr 1
  funext i
  simpa only [zero_add] using (gaussianReal_map_const_add (μ := 0) (v := v) (z i))

theorem map_prod_endpoint_eq_compProd (v : ℝ≥0) (hv : v ≠ 0)
    (ξ : α → ι → ℝ) (hξ : ∀ i, Measurable (fun a => ξ a i))
    (hbinary : ∀ a i, ξ a i = 0 ∨ ξ a i = 1)
    (π : Measure α) [SFinite π] :
    (π.prod (Measure.pi (fun _ : ι => gaussianReal 0 v))).map
      (fun q => (q.1, fun i => (v : ℝ) * ξ q.1 i + q.2 i)) =
        π ⊗ₘ endpointKernel v ξ := by
  let := endpointKernel_markov v hv ξ hξ hbinary
  have hmap : Measurable (fun q : α × (ι → ℝ) =>
      (q.1, fun i => (v : ℝ) * ξ q.1 i + q.2 i)) := by fun_prop
  ext s hs
  rw [Measure.map_apply hmap hs, Measure.prod_apply (hs.preimage hmap),
    Measure.compProd_apply hs]
  apply lintegral_congr
  intro a
  rw [endpointKernel_apply v hv ξ hξ hbinary a,
    ← centered_gaussian_pi_map_shift v (fun i => (v : ℝ) * ξ a i),
    Measure.map_apply (by fun_prop) (hs.preimage measurable_prodMk_left)]
  rfl

theorem hasLaw_independent_gaussian_observation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (π : Measure α) [IsProbabilityMeasure π]
    (v : ℝ≥0) (hv : v ≠ 0) (ξ : α → ι → ℝ)
    (hξ : ∀ i, Measurable (fun a => ξ a i))
    (hbinary : ∀ a i, ξ a i = 0 ∨ ξ a i = 1)
    (X : Ω → α) (B : Ω → ι → ℝ) (hX : HasLaw X π P)
    (hB : HasLaw B (Measure.pi (fun _ : ι => gaussianReal 0 v)) P)
    (hIndep : IndepFun X B P) :
    HasLaw (fun ω => (X ω, fun i => (v : ℝ) * ξ (X ω) i + B ω i))
      (π ⊗ₘ endpointKernel v ξ) P := by
  have hpair := hIndep.hasLaw_prod hX hB
  have hmap : HasLaw
      (fun q : α × (ι → ℝ) => (q.1, fun i => (v : ℝ) * ξ q.1 i + q.2 i))
      (π ⊗ₘ endpointKernel v ξ)
      (π.prod (Measure.pi (fun _ : ι => gaussianReal 0 v))) :=
    ⟨by fun_prop, map_prod_endpoint_eq_compProd v hv ξ hξ hbinary π⟩
  exact hmap.fun_comp hpair

end Problem336.GaussianObservation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FiniteGaussianPosterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators ProbabilityTheory

namespace Problem336.FinitePosterior

variable {Θ ι : Type*} [Fintype Θ] [MeasurableSpace Θ]
    [MeasurableSingletonClass Θ] [Fintype ι]

omit [Fintype Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ] in
lemma measurable_gaussianLikelihood (t : ℝ≥0) (signal : Θ → ι → ℝ) (θ : Θ) :
    Measurable (gaussianLikelihood t signal θ) := by
  unfold gaussianLikelihood
  fun_prop

lemma gaussianObservationKernel_eq_withDensity (t : ℝ≥0) (ht : t ≠ 0)
    (signal : Θ → ι → ℝ) (hbinary : ∀ θ i, signal θ i = 0 ∨ signal θ i = 1)
    (θ : Θ) :
    GaussianObservation.endpointKernel t signal θ =
      (Measure.pi (fun _ : ι => gaussianReal 0 t)).withDensity
        (gaussianLikelihood t signal θ) := by
  rw [GaussianObservation.endpointKernel_apply t ht signal
    (fun i => measurable_of_countable (fun θ => signal θ i)) hbinary θ]
  exact GaussianObservation.gaussian_pi_binary_shift_withDensity t ht (signal θ) (hbinary θ)

theorem gaussian_condExp_eq_exponential_ratio_of_jointLaw
    [StandardBorelSpace Θ] [Nonempty Θ]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → Θ) (Yobs : Ω → (ι → ℝ)) (hX : Measurable X) (hY : Measurable Yobs)
    (π : Measure Θ) [IsProbabilityMeasure π]
    (t : ℝ≥0) (ht : t ≠ 0) (signal : Θ → ι → ℝ)
    (hbinary : ∀ θ i, signal θ i = 0 ∨ signal θ i = 1)
    (hjoint : P.map (fun ω => (X ω, Yobs ω)) =
      π ⊗ₘ GaussianObservation.endpointKernel t signal) (g : Θ → ℝ) :
    P[fun ω => g (X ω) | (inferInstance : MeasurableSpace (ι → ℝ)).comap Yobs] =ᵐ[P]
      fun ω =>
        (∑ θ, (π {θ}).toReal *
          Real.exp (∑ i, (Yobs ω i - (t : ℝ) / 2) * signal θ i) * g θ) /
        (∑ θ, (π {θ}).toReal *
          Real.exp (∑ i, (Yobs ω i - (t : ℝ) / 2) * signal θ i)) := by
  let := GaussianObservation.endpointKernel_markov t ht signal
    (fun i => measurable_of_countable (fun θ => signal θ i)) hbinary
  have hfinite : ∀ θ y, gaussianLikelihood t signal θ y ≠ ∞ := by
    intro θ y
    exact ENNReal.ofReal_ne_top
  have hpositive : ∀ θ y, gaussianLikelihood t signal θ y ≠ 0 := by
    intro θ y
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have h := condExp_eq_likelihood_ratio_of_jointLaw P X Yobs hX hY π
    (GaussianObservation.endpointKernel t signal) hjoint
    (Measure.pi (fun _ : ι => gaussianReal 0 t)) (gaussianLikelihood t signal)
    (measurable_gaussianLikelihood t signal) hfinite
    (mixtureDensity_ne_zero_of_positive π _ hpositive)
    (gaussianObservationKernel_eq_withDensity t ht signal hbinary) g
  simpa only [mixtureDensity_toReal π _ hfinite, gaussianLikelihood,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] using h

theorem gaussian_condExp_eq_exponential_ratio_of_independent
    [StandardBorelSpace Θ] [Nonempty Θ]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Θ) (noise : Ω → (ι → ℝ)) (hX : Measurable X) (hnoise : Measurable noise)
    (π : Measure Θ) [IsProbabilityMeasure π]
    (t : ℝ≥0) (ht : t ≠ 0) (signal : Θ → ι → ℝ)
    (hbinary : ∀ θ i, signal θ i = 0 ∨ signal θ i = 1)
    (hprior : P.map X = π)
    (hnoiseLaw : P.map noise = Measure.pi (fun _ : ι => gaussianReal 0 t))
    (hindep : X ⟂ᵢ[P] noise) (g : Θ → ℝ) :
    let Yobs := fun ω i => (t : ℝ) * signal (X ω) i + noise ω i
    P[fun ω => g (X ω) | (inferInstance : MeasurableSpace (ι → ℝ)).comap Yobs] =ᵐ[P]
      fun ω =>
        (∑ θ, (π {θ}).toReal *
          Real.exp (∑ i, (Yobs ω i - (t : ℝ) / 2) * signal θ i) * g θ) /
        (∑ θ, (π {θ}).toReal *
          Real.exp (∑ i, (Yobs ω i - (t : ℝ) / 2) * signal θ i)) := by
  let Yobs := fun ω i => (t : ℝ) * signal (X ω) i + noise ω i
  have hs : Measurable signal := measurable_of_countable signal
  have hY : Measurable Yobs := by
    unfold Yobs
    fun_prop
  have hjoint := GaussianObservation.hasLaw_independent_gaussian_observation P π t ht signal
    (fun i => measurable_of_countable (fun θ => signal θ i)) hbinary X noise
    ⟨hX.aemeasurable, hprior⟩ ⟨hnoise.aemeasurable, hnoiseLaw⟩ hindep
  exact gaussian_condExp_eq_exponential_ratio_of_jointLaw P X Yobs hX hY π t ht signal
    hbinary hjoint.map_eq g

end Problem336.FinitePosterior

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_BinaryGaussianPosterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators ProbabilityTheory

namespace Problem336.FinitePosterior

lemma binaryValue_binary (b : Bool) : binaryValue b = 0 ∨ binaryValue b = 1 := by
  cases b <;> simp [binaryValue]

lemma measurable_binarySummary {I ι : Type*} (observed : ι → I) (target : I) :
    Measurable (binarySummary observed target) := by
  unfold binarySummary
  fun_prop

lemma finiteMarginal_ratio_eq_integral {A Θ : Type*} [MeasurableSpace A]
    [Fintype Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
    (ν : Measure A) [IsFiniteMeasure ν] (R : A → Θ) (hR : Measurable R)
    (w g : Θ → ℝ) :
    (∑ θ, ((ν.map R) {θ}).toReal * w θ * g θ) /
      (∑ θ, ((ν.map R) {θ}).toReal * w θ) =
    (∫ x, w (R x) * g (R x) ∂ν) / (∫ x, w (R x) ∂ν) := by
  rw [← integral_map_of_stronglyMeasurable hR
      (measurable_of_countable (fun θ => w θ * g θ)).stronglyMeasurable,
    ← integral_map_of_stronglyMeasurable hR (measurable_of_countable w).stronglyMeasurable]
  simp only [integral_fintype (Integrable.of_finite), Measure.real, smul_eq_mul, mul_assoc]

theorem binaryField_gaussian_condExp
    {Ω I ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure (I → Bool)) [IsProbabilityMeasure ν]
    (X : Ω → (I → Bool)) (noise : Ω → (ι → ℝ))
    (hX : Measurable X) (hnoise : Measurable noise)
    (observed : ι → I) (target : I) (t : ℝ≥0) (ht : t ≠ 0)
    (hprior : P.map X = ν)
    (hnoiseLaw : P.map noise = Measure.pi (fun _ : ι => gaussianReal 0 t))
    (hindep : X ⟂ᵢ[P] noise) :
    let Yobs := fun ω j => (t : ℝ) * binaryValue (X ω (observed j)) + noise ω j
    P[fun ω => binaryValue (X ω target) |
      (inferInstance : MeasurableSpace (ι → ℝ)).comap Yobs] =ᵐ[P]
      fun ω => gaussianFiniteTilt ν observed target t (Yobs ω) := by
  classical
  let R : (I → Bool) → Bool × (ι → Bool) := binarySummary observed target
  have hR : Measurable R := measurable_binarySummary observed target
  let π := ν.map R
  let : IsProbabilityMeasure π := Measure.isProbabilityMeasure_map hR.aemeasurable
  let signal : (Bool × (ι → Bool)) → ι → ℝ := fun θ j => binaryValue (θ.2 j)
  let g : (Bool × (ι → Bool)) → ℝ := fun θ => binaryValue θ.1
  have hsignal : ∀ θ j, signal θ j = 0 ∨ signal θ j = 1 := by
    intro θ j
    exact binaryValue_binary _
  have hprior' : P.map (fun ω => R (X ω)) = π := by
    change P.map (R ∘ X) = ν.map R
    rw [← Measure.map_map hR hX, hprior]
  have hindep' : (fun ω => R (X ω)) ⟂ᵢ[P] noise := by
    simpa only [Function.comp_def, id_eq] using hindep.comp hR measurable_id
  have h := gaussian_condExp_eq_exponential_ratio_of_independent P
    (fun ω => R (X ω)) noise (hR.comp hX) hnoise π t ht signal hsignal
    hprior' hnoiseLaw hindep' g
  have hratio (y : ι → ℝ) :
      (∑ θ, (π {θ}).toReal * Real.exp (∑ j, (y j - (t : ℝ) / 2) * signal θ j) * g θ) /
        (∑ θ, (π {θ}).toReal * Real.exp (∑ j, (y j - (t : ℝ) / 2) * signal θ j)) =
      gaussianFiniteTilt ν observed target t y := by
    simpa only [π, R, signal, g, binarySummary, gaussianFiniteTilt] using
      finiteMarginal_ratio_eq_integral ν R hR
        (fun θ => Real.exp (∑ j, (y j - (t : ℝ) / 2) * signal θ j)) g
  filter_upwards [h] with ω hω
  exact hω.trans (hratio _)

end Problem336.FinitePosterior

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_BrownianBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336.BrownianBridge

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

theorem indepFun_regroup {A C D : Type*} [MeasurableSpace A]
    [MeasurableSpace C] [MeasurableSpace D] [IsFiniteMeasure P]
    {X : Ω → A} {Y : Ω → C} {Z : Ω → D}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXYZ : IndepFun X (fun ω => (Y ω, Z ω)) P)
    (hYZ : IndepFun Y Z P) :
    IndepFun Y (fun ω => (X ω, Z ω)) P := by
  let μX := P.map X
  let μY := P.map Y
  let μZ := P.map Z
  let swapFirst : A × (C × D) → C × (A × D) := fun q => (q.2.1, q.1, q.2.2)
  have hm : Measurable swapFirst := by fun_prop
  have hp : MeasurePreserving swapFirst (μX.prod (μY.prod μZ))
      (μY.prod (μX.prod μZ)) := by
    exact (measurePreserving_prodAssoc μY μX μZ).comp
      (((Measure.measurePreserving_swap (μ := μX) (ν := μY)).prod
        (MeasurePreserving.id μZ)).comp
          ((measurePreserving_prodAssoc μX μY μZ).symm MeasurableEquiv.prodAssoc))
  have hpair : P.map (fun ω => (Y ω, Z ω)) = μY.prod μZ :=
    hYZ.map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable
  have hall : P.map (fun ω => (X ω, (Y ω, Z ω))) = μX.prod (μY.prod μZ) := by
    rw [hXYZ.map_prod_eq_prod_map_map hX.aemeasurable
      (hY.prodMk hZ).aemeasurable, hpair]
  have hxz : IndepFun X Z P := hXYZ.comp measurable_id measurable_snd
  apply (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable
    (hX.prodMk hZ).aemeasurable).2
  rw [hxz.map_prod_eq_prod_map_map hX.aemeasurable hZ.aemeasurable]
  change P.map (swapFirst ∘ (fun ω => (X ω, (Y ω, Z ω)))) = _
  rw [← Measure.map_map hm (hX.prodMk (hY.prodMk hZ)), hall]
  exact hp.map_eq

theorem isGaussianProcess_independent_family {I T : Type*}
    {C : I → T → Ω → ℝ} (hC : ∀ i, IsGaussianProcess (C i) P)
    (hind : iIndepFun (fun i ω t => C i t ω) P) :
    IsGaussianProcess (fun p : I × T => C p.1 p.2) P := by
  classical
  constructor
  intro S
  let J := S.image Prod.fst
  let K := S.image Prod.snd
  have hG : ∀ i : J, HasGaussianLaw (fun ω (t : K) => C i t ω) P :=
    fun i => (hC i).hasGaussianLaw K
  have hI : iIndepFun (fun (i : J) ω (t : K) => C i t ω) P := by
    exact (hind.precomp Subtype.val_injective).comp
      (fun _ f (t : K) => f t) (fun _ => by fun_prop)
  let L : (J → K → ℝ) →L[ℝ] (S → ℝ) :=
    { toFun x := fun p => x ⟨p.1.1, Finset.mem_image_of_mem _ p.2⟩
        ⟨p.1.2, Finset.mem_image_of_mem _ p.2⟩
      map_add' x y := by rfl
      map_smul' c x := by rfl }
  exact (hI.hasGaussianLaw hG).map L

theorem indepFun_residual_family_endpoint {I : Type*}
    {C : I → ℝ≥0 → Ω → ℝ} (hC : ∀ i, IsPreBrownianReal (C i) P)
    (hind : iIndepFun (fun i ω s => C i s ω) P) (t : ℝ≥0) (ht : t ≠ 0) :
    IndepFun (fun ω (p : I × Set.Iic t) => residual (C p.1) t p.2 ω)
      (fun ω i => C i t ω) P := by
  classical
  have hp := hind.isProbabilityMeasure
  have hg := isGaussianProcess_independent_family (fun i => (hC i).isGaussianProcess) hind
  have hLp i s := ((hC i).isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hm i s := (hC i).aemeasurable s
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero
  · apply hg.of_isGaussianProcess
    rintro (⟨i, s, hs⟩ | i)
    · exact ⟨{(i, s), (i, t)},
        { toFun x := x ⟨(i, s), by simp⟩ - (s : ℝ) / (t : ℝ) * x ⟨(i, t), by simp⟩
          map_add' x y := by simp; ring
          map_smul' c x := by simp; ring }, by simp [residual]⟩
    · exact ⟨{(i, t)},
        { toFun x := x ⟨(i, t), by simp⟩
          map_add' x y := by simp
          map_smul' c x := by simp }, by simp⟩
  · intro p
    exact (hm p.1 p.2).sub ((hm p.1 t).const_mul _)
  · intro i
    exact hm i t
  · rintro ⟨i, s, hs⟩ j
    unfold residual
    rw [covariance_fun_sub_left (hLp i s) ((hLp i t).const_mul _) (hLp j t),
      covariance_const_mul_left]
    by_cases hij : i = j
    · subst j
      rw [(hC i).covariance_eval, (hC i).covariance_eval, min_self, min_eq_left hs]
      have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
      field_simp
      ring
    · have hc (r : ℝ≥0) : cov[C i r, C j t; P] = 0 :=
        ((hind.indepFun hij).comp (measurable_pi_apply r)
          (measurable_pi_apply t)).covariance_eq_zero (hLp i r) (hLp j t)
      rw [hc s, hc t]
      ring

theorem indepFun_residual_family_hidden_endpoint {I A : Type*} [MeasurableSpace A]
    {C : I → ℝ≥0 → Ω → ℝ} (hC : ∀ i, IsPreBrownianReal (C i) P)
    (hind : iIndepFun (fun i ω s => C i s ω) P)
    (hCm : ∀ i s, Measurable (C i s)) {X : Ω → A} (hXm : Measurable X)
    (D : A → I → ℝ) (hD : Measurable D)
    (hXC : IndepFun X (fun ω (p : I × ℝ≥0) => C p.1 p.2 ω) P)
    (t : ℝ≥0) (ht : t ≠ 0) :
    IndepFun (fun ω (p : I × Set.Iic t) => residual (C p.1) t p.2 ω)
      (fun ω => (X ω, fun i => (t : ℝ) * D (X ω) i + C i t ω)) P := by
  have := hind.isProbabilityMeasure
  have hpair : IndepFun X
      (fun ω => ((fun p : I × Set.Iic t => residual (C p.1) t p.2 ω),
        fun i => C i t ω)) P := by
    exact hXC.comp measurable_id
      (show Measurable (fun f : I × ℝ≥0 → ℝ =>
        ((fun p : I × Set.Iic t => f (p.1, p.2) -
          (p.2 : ℝ) / (t : ℝ) * f (p.1, t)), fun i => f (i, t))) by fun_prop)
  have hm : Measurable (fun ω (p : I × Set.Iic t) => residual (C p.1) t p.2 ω) := by
    apply Measurable.of_eval
    intro p
    exact (hCm p.1 p.2).sub ((hCm p.1 t).const_mul _)
  have hE : Measurable (fun ω i => C i t ω) := Measurable.of_eval (fun i => hCm i t)
  have h := indepFun_regroup hXm hm hE hpair (indepFun_residual_family_endpoint hC hind t ht)
  exact h.comp measurable_id
    (show Measurable (fun q : A × (I → ℝ) =>
      (q.1, fun i => (t : ℝ) * D q.1 i + q.2 i)) by fun_prop)

omit [MeasurableSpace Ω] in

theorem observation_family_history_comap {I A : Type*} (C : I → ℝ≥0 → Ω → ℝ)
    (X : Ω → A) (D : A → I → ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    MeasurableSpace.comap
      (fun ω (p : I × Set.Iic t) => (p.2 : ℝ) * D (X ω) p.1 + C p.1 p.2 ω) inferInstance =
      MeasurableSpace.comap (fun ω i => (t : ℝ) * D (X ω) i + C i t ω) inferInstance ⊔
        MeasurableSpace.comap
          (fun ω (p : I × Set.Iic t) => residual (C p.1) t p.2 ω) inferInstance := by
  let H := fun ω (p : I × Set.Iic t) => (p.2 : ℝ) * D (X ω) p.1 + C p.1 p.2 ω
  let F := fun ω => ((fun i => (t : ℝ) * D (X ω) i + C i t ω),
    fun p : I × Set.Iic t => residual (C p.1) t p.2 ω)
  let decompose : (I × Set.Iic t → ℝ) → (I → ℝ) × (I × Set.Iic t → ℝ) :=
    fun f => (fun i => f (i, ⟨t, by simp⟩),
      fun p => f p - (p.2 : ℝ) / (t : ℝ) * f (p.1, ⟨t, by simp⟩))
  let assemble : (I → ℝ) × (I × Set.Iic t → ℝ) → (I × Set.Iic t → ℝ) :=
    fun q p => q.2 p + (p.2 : ℝ) / (t : ℝ) * q.1 p.1
  have hd : Measurable decompose := by fun_prop
  have ha : Measurable assemble := by fun_prop
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  have hF : F = decompose ∘ H := by
    funext ω
    apply Prod.ext
    · rfl
    · funext p
      dsimp [F, decompose, H, residual]
      field_simp
      ring
  have hH : H = assemble ∘ F := by
    funext ω p
    dsimp [H, F, assemble, residual]
    field_simp
    ring
  rw [← MeasurableSpace.comap_prodMk]
  change MeasurableSpace.comap H _ = MeasurableSpace.comap F _
  apply le_antisymm
  · rw [hH, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono ha.comap_le
  · rw [hF, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hd.comap_le

end Problem336.BrownianBridge

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_PosteriorIndependentExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory

namespace Problem336.Observation

private theorem fieldRectangles_pi {Ω : Type*} (m n : MeasurableSpace Ω) :
    IsPiSystem (fieldRectangles m n) := by
  rintro s ⟨a, b, ha, hb, rfl⟩ t ⟨c, d, hc, hd, rfl⟩ _
  refine ⟨a ∩ c, b ∩ d, ha.inter hc, hb.inter hd, ?_⟩
  ext x
  simp only [Set.mem_inter_iff]
  tauto

private theorem generateFrom_fieldRectangles {Ω : Type*} (m n : MeasurableSpace Ω) :
    m ⊔ n = MeasurableSpace.generateFrom (fieldRectangles m n) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · intro s hs
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨s, Set.univ, hs, MeasurableSet.univ, Set.inter_univ s⟩
    · intro s hs
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨Set.univ, s, MeasurableSet.univ, hs, Set.univ_inter s⟩
  · apply MeasurableSpace.generateFrom_le
    rintro s ⟨a, b, ha, hb, rfl⟩
    exact (show MeasurableSet[m ⊔ n] a from (show m ≤ m ⊔ n from le_sup_left) a ha).inter
      (show MeasurableSet[m ⊔ n] b from (show n ≤ m ⊔ n from le_sup_right) b hb)

theorem setIntegral_eq_on_sup_of_rectangles
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    {m n : MeasurableSpace Ω} (hm : m ≤ mΩ) (hn : n ≤ mΩ)
    {f g : Ω → ℝ} (hf : Integrable f P) (hg : Integrable g P)
    (heq : ∀ a b, MeasurableSet[m] a → MeasurableSet[n] b →
      ∫ ω in a ∩ b, f ω ∂P = ∫ ω in a ∩ b, g ω ∂P) :
    ∀ s, MeasurableSet[m ⊔ n] s →
      ∫ ω in s, f ω ∂P = ∫ ω in s, g ω ∂P := by
  have hmn : m ⊔ n ≤ mΩ := sup_le hm hn
  have huniv : ∫ ω, f ω ∂P = ∫ ω, g ω ∂P := by
    simpa using heq Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
  refine MeasurableSpace.induction_on_inter
    (generateFrom_fieldRectangles m n) (fieldRectangles_pi m n) (by simp) ?_ ?_ ?_
  · rintro s ⟨a, b, ha, hb, rfl⟩
    exact heq a b ha hb
  · intro s hs ih
    rw [setIntegral_compl (hmn s hs) hf, setIntegral_compl (hmn s hs) hg, huniv, ih]
  · intro s hd hs ih
    rw [integral_iUnion (fun i => hmn _ (hs i)) hd hf.integrableOn,
      integral_iUnion (fun i => hmn _ (hs i)) hd hg.integrableOn]
    exact tsum_congr ih

theorem setIntegral_of_independent_field
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsFiniteMeasure P]
    {m n : MeasurableSpace Ω} (hm : m ≤ mΩ) (hn : n ≤ mΩ)
    {f : Ω → ℝ} (hf : StronglyMeasurable[m] f) (hfi : Integrable f P)
    (hindep : Indep m n P) {s : Set Ω} (hs : MeasurableSet[n] s) :
    ∫ ω in s, f ω ∂P = P.real s * ∫ ω, f ω ∂P := by
  calc
    _ = ∫ ω in s, (P[f | n]) ω ∂P := (setIntegral_condExp hn hfi hs).symm
    _ = ∫ _ in s, (∫ ω, f ω ∂P) ∂P :=
      integral_congr_ae (ae_restrict_of_ae (condExp_indep_eq hm hn hf hindep))
    _ = _ := by simp [smul_eq_mul]

theorem condExp_sup_independent
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsFiniteMeasure P]
    {hidden observed auxiliary : MeasurableSpace Ω}
    (hhidden : hidden ≤ mΩ) (hauxiliary : auxiliary ≤ mΩ)
    (hobserved : observed ≤ hidden) {X : Ω → ℝ}
    (hX : StronglyMeasurable[hidden] X) (hXi : Integrable X P)
    (hindep : Indep hidden auxiliary P) :
    P[X | observed ⊔ auxiliary] =ᵐ[P] P[X | observed] := by
  have ho : observed ≤ mΩ := hobserved.trans hhidden
  have hoa : observed ⊔ auxiliary ≤ mΩ := sup_le ho hauxiliary
  have hC : StronglyMeasurable[hidden] (P[X | observed]) :=
    stronglyMeasurable_condExp.mono hobserved
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hoa hXi
    (fun _ _ _ => integrable_condExp.integrableOn)
  · intro s hs _
    apply setIntegral_eq_on_sup_of_rectangles P ho hauxiliary
      integrable_condExp hXi _ s hs
    intro a b ha hb
    have hca := setIntegral_of_independent_field P hhidden hauxiliary
      (hC.indicator (hobserved a ha))
      (integrable_condExp.indicator (ho a ha)) hindep hb
    have hxa := setIntegral_of_independent_field P hhidden hauxiliary
      (hX.indicator (hobserved a ha)) (hXi.indicator (ho a ha)) hindep hb
    rw [setIntegral_indicator (ho a ha), integral_indicator (ho a ha),
      Set.inter_comm b a] at hca hxa
    rw [hca, hxa, setIntegral_condExp ho hXi ha]
  · exact (stronglyMeasurable_condExp.mono le_sup_left).aestronglyMeasurable

end Problem336.Observation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_BrownianPosteriorReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace Problem336.BrownianBridge

theorem condExp_observation_history_eq_endpoint
    {Ω I A : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace A] {P : Measure Ω}
    {C : I → ℝ≥0 → Ω → ℝ} (hC : ∀ i, IsPreBrownianReal (C i) P)
    (hind : iIndepFun (fun i ω s => C i s ω) P)
    (hCm : ∀ i s, Measurable (C i s)) {X : Ω → A} (hXm : Measurable X)
    (D : A → I → ℝ) (hD : Measurable D)
    (hXC : IndepFun X (fun ω (p : I × ℝ≥0) => C p.1 p.2 ω) P)
    (t : ℝ≥0) (ht : t ≠ 0) (f : A → ℝ) (hf : Measurable f)
    (hfi : Integrable (f ∘ X) P) :
    P[f ∘ X | MeasurableSpace.comap
      (fun ω (p : I × Set.Iic t) => (p.2 : ℝ) * D (X ω) p.1 + C p.1 p.2 ω) inferInstance]
      =ᵐ[P]
    P[f ∘ X | MeasurableSpace.comap
      (fun ω i => (t : ℝ) * D (X ω) i + C i t ω) inferInstance] := by
  have := hind.isProbabilityMeasure
  let E := fun ω i => (t : ℝ) * D (X ω) i + C i t ω
  let R := fun ω (p : I × Set.Iic t) => residual (C p.1) t p.2 ω
  let hidden := MeasurableSpace.comap (fun ω => (X ω, E ω)) inferInstance
  let : MeasurableSpace Ω := mΩ
  have hE : Measurable[mΩ] E := by
    apply Measurable.of_eval
    intro i
    exact (((measurable_pi_apply i).comp (hD.comp hXm)).const_mul _).add (hCm i t)
  have hR : Measurable[mΩ] R := by
    apply Measurable.of_eval
    intro p
    exact (hCm p.1 p.2).sub ((hCm p.1 t).const_mul _)
  have hhidden : hidden ≤ mΩ := (hXm.prodMk hE).comap_le
  have hobs : MeasurableSpace.comap E inferInstance ≤ hidden :=
    (comap_measurable (fun ω => (X ω, E ω))).snd.comap_le
  have hXhidden : @Measurable Ω A hidden _ X :=
    (comap_measurable (fun ω => (X ω, E ω))).fst
  have hfh : StronglyMeasurable[hidden] (f ∘ X) := (hf.comp hXhidden).stronglyMeasurable
  have hbridge : Indep hidden (MeasurableSpace.comap R inferInstance) P :=
    (indepFun_residual_family_hidden_endpoint hC hind hCm hXm D hD hXC t ht).symm
  rw [observation_family_history_comap C X D t ht]
  exact Observation.condExp_sup_independent P hhidden hR.comap_le hobs hfh hfi hbridge

end Problem336.BrownianBridge

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_ObservationPosterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace Problem336.Observation

theorem iSup_finiteObservationFiltration {Ω I : Type*} {mΩ : MeasurableSpace Ω}
    (coordinate : I → MeasurableSpace Ω) (hcoordinate : ∀ i, coordinate i ≤ mΩ)
    (S : ℕ → Finset I) (hS : Monotone S) (hcover : ∀ i, ∃ n, i ∈ S n) :
    (⨆ n, finiteObservationFiltration coordinate hcoordinate S hS n) =
      ⨆ i, coordinate i := by
  apply le_antisymm
  · exact iSup_le fun _ => iSup_le fun i => iSup_le fun _ => le_iSup coordinate i
  · refine iSup_le fun i => ?_
    obtain ⟨n, hi⟩ := hcover i
    exact le_iSup_of_le n (le_iSup_of_le i (le_iSup_of_le hi le_rfl))

theorem tendsto_posterior_of_finite_stage
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsFiniteMeasure P] (F : Filtration ℕ mΩ) (X : Ω → ℝ)
    (posterior : ℕ → Ω → ℝ)
    (hposterior : ∀ n, posterior n =ᵐ[P] P[X | F n]) :
    ∀ᵐ ω ∂P, Tendsto (fun n => posterior n ω) atTop
      (nhds ((P[X | ⨆ n, F n]) ω)) := by
  have hall : ∀ᵐ ω ∂P, ∀ n, posterior n ω = (P[X | F n]) ω :=
    ae_all_iff.mpr hposterior
  filter_upwards [hall, MeasureTheory.tendsto_ae_condExp (μ := P) (ℱ := F) X]
    with ω hω hlim
  exact hlim.congr (fun n => (hω n).symm)

theorem limsup_posterior_of_finite_stage
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsFiniteMeasure P] (F : Filtration ℕ mΩ) (X : Ω → ℝ)
    (posterior : ℕ → Ω → ℝ)
    (hposterior : ∀ n, posterior n =ᵐ[P] P[X | F n]) :
    (fun ω => limsup (fun n => posterior n ω) atTop) =ᵐ[P]
      P[X | ⨆ n, F n] := by
  filter_upwards [tendsto_posterior_of_finite_stage P F X posterior hposterior]
    with ω hω
  exact hω.limsup_eq

theorem limsup_posterior_all_coordinates
    {Ω I : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsFiniteMeasure P] (coordinate : I → MeasurableSpace Ω)
    (hcoordinate : ∀ i, coordinate i ≤ mΩ)
    (S : ℕ → Finset I) (hS : Monotone S) (hcover : ∀ i, ∃ n, i ∈ S n)
    (X : Ω → ℝ) (posterior : ℕ → Ω → ℝ)
    (hposterior : ∀ n, posterior n =ᵐ[P] P[X | ⨆ i ∈ S n, coordinate i]) :
    (fun ω => limsup (fun n => posterior n ω) atTop) =ᵐ[P]
      P[X | ⨆ i, coordinate i] := by
  have h := limsup_posterior_of_finite_stage P
    (finiteObservationFiltration coordinate hcoordinate S hS) X posterior hposterior
  simpa only [iSup_finiteObservationFiltration coordinate hcoordinate S hS hcover] using h

end Problem336.Observation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CanonicalDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace Problem336
namespace CanonicalDrift

theorem measurable_outerLimit {X : Type*} [MeasurableSpace X]
    {b : ℕ → X → ℝ} (hb : ∀ n, Measurable (b n)) :
    Measurable (outerLimit b) :=
  Measurable.limsup hb

theorem outerLimit_mem_Icc {X : Type*} {b : ℕ → X → ℝ}
    {a c : ℝ} (hb : ∀ n x, b n x ∈ Set.Icc a c) (x : X) :
    outerLimit b x ∈ Set.Icc a c := by
  have hu : atTop.IsBoundedUnder (· ≤ ·) (fun n => b n x) :=
    isBoundedUnder_of ⟨c, fun n => (hb n x).2⟩
  have hl : atTop.IsCoboundedUnder (· ≤ ·) (fun n => b n x) :=
    isCoboundedUnder_le_of_le atTop fun n => (hb n x).1
  constructor
  · exact le_limsup_of_frequently_le
      (Eventually.of_forall fun n => (hb n x).1).frequently hu
  · exact limsup_le_of_le hl (Eventually.of_forall fun n => (hb n x).2)

end CanonicalDrift
end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_PosteriorTiltLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace Problem336.TiltLimit

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω]

theorem integral_exp_pos [CompactSpace Ω] (μ : ProbabilityMeasure Ω)
    {h : Ω → ℝ} (hh : Continuous h) :
    0 < ∫ x, Real.exp (h x) ∂(μ : Measure Ω) := by
  apply MeasureTheory.integral_exp_pos
  exact (BoundedContinuousFunction.mkOfCompact ⟨_, (Real.continuous_exp.comp hh)⟩).integrable _

omit [TopologicalSpace Ω] [OpensMeasurableSpace Ω] in

theorem measurable_tiltedMean {A : Type*} [MeasurableSpace A]
    (μ : ProbabilityMeasure Ω) (h X : A → Ω → ℝ)
    (hh : Measurable (Function.uncurry h))
    (hX : Measurable (Function.uncurry X)) :
    Measurable (fun a => tiltedMean μ (h a) (X a)) := by
  exact ((hX.mul hh.exp).stronglyMeasurable.integral_prod_right).measurable.div
    (hh.exp.stronglyMeasurable.integral_prod_right).measurable

theorem tiltedMean_mem_Icc [CompactSpace Ω] (μ : ProbabilityMeasure Ω)
    {h X : Ω → ℝ} (hh : Continuous h) (hX : Continuous X)
    (hb : ∀ x, X x ∈ Set.Icc (0 : ℝ) 1) :
    tiltedMean μ h X ∈ Set.Icc (0 : ℝ) 1 := by
  have hd := integral_exp_pos μ hh
  have hi : Integrable (fun x => Real.exp (h x)) (μ : Measure Ω) :=
    (BoundedContinuousFunction.mkOfCompact ⟨_, Real.continuous_exp.comp hh⟩).integrable _
  have hn : Integrable (fun x => X x * Real.exp (h x)) (μ : Measure Ω) :=
    (BoundedContinuousFunction.mkOfCompact ⟨_, hX.mul (Real.continuous_exp.comp hh)⟩).integrable _
  constructor
  · exact div_nonneg (integral_nonneg (fun x => mul_nonneg (hb x).1 (Real.exp_pos _).le)) hd.le
  · apply (div_le_one₀ hd).2
    exact integral_mono hn hi (fun x => mul_le_of_le_one_left (Real.exp_pos _).le (hb x).2)

variable {I : Type*}

theorem continuous_finiteEnergy (S : Finset I) (h : I → ℝ) :
    Continuous (finiteEnergy S h) := by
  apply continuous_finsetSum
  intro i hi
  exact continuous_const.mul (continuous_bit.comp (continuous_apply i))

variable [Countable I]

theorem finiteTiltMean_mem_Icc (μ : ProbabilityMeasure (I → Bool))
    (S : Finset I) (h : I → ℝ) (e : I) :
    finiteTiltMean μ S h e ∈ Set.Icc (0 : ℝ) 1 := by
  apply tiltedMean_mem_Icc μ (continuous_finiteEnergy S h)
    (continuous_bit.comp (continuous_apply e))
  intro x
  cases hx : x e <;> simp [bit, hx]

omit [Countable I] in

theorem measurable_finitePosterior (μ : ProbabilityMeasure (I → Bool))
    (S : Finset I) (e : I) :
    Measurable (fun p : ℝ × (I → ℝ) =>
      finiteTiltMean μ S (fun i => p.2 i - p.1 / 2) e) := by
  apply measurable_tiltedMean
  · change Measurable (fun q : (ℝ × (I → ℝ)) × (I → Bool) =>
      ∑ i ∈ S, (q.1.2 i - q.1.1 / 2) * bit (q.2 i))
    apply Finset.measurable_sum
    intro i hi
    have hfield : Measurable (fun q : (ℝ × (I → ℝ)) × (I → Bool) =>
        q.1.2 i - q.1.1 / 2) :=
      (((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)).sub
        ((measurable_fst.comp measurable_fst).div_const 2))
    have hbit : Measurable (fun q : (ℝ × (I → ℝ)) × (I → Bool) => bit (q.2 i)) :=
      continuous_bit.measurable.comp ((measurable_pi_apply i).comp measurable_snd)
    exact hfield.mul hbit
  · change Measurable (fun q : (ℝ × (I → ℝ)) × (I → Bool) => bit (q.2 e))
    exact continuous_bit.measurable.comp ((measurable_pi_apply e).comp measurable_snd)

end Problem336.TiltLimit

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_PosteriorDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Problem336.PosteriorDrift
open TiltLimit

variable {I : Type*} [Countable I]

omit [Countable I] in
theorem measurable_drift_coordinate (μ : ProbabilityMeasure (I → Bool))
    (S : I → ℕ → Finset I) (e : I) :
    Measurable (fun p : ℝ × (I → ℝ) => drift μ S p.1 p.2 e) :=
  CanonicalDrift.measurable_outerLimit (fun n => measurable_finitePosterior μ (S e n) e)

theorem drift_mem_Icc (μ : ProbabilityMeasure (I → Bool)) (S : I → ℕ → Finset I)
    (t : ℝ) (y : I → ℝ) (e : I) : drift μ S t y e ∈ Set.Icc (0 : ℝ) 1 :=
  CanonicalDrift.outerLimit_mem_Icc (b := finiteStage μ S e)
    (fun n (p : ℝ × (I → ℝ)) =>
      finiteTiltMean_mem_Icc μ (S e n) (fun i => p.2 i - p.1 / 2) e) (t, y)

omit [Countable I] in

theorem drift_eq_of_tendsto (μ : ProbabilityMeasure (I → Bool))
    (S : I → ℕ → Finset I) (t : ℝ) (y : I → ℝ) (e : I) {a : ℝ}
    (h : Tendsto (fun n => finiteTiltMean μ (S e n) (fun i => y i - t / 2) e)
      atTop (𝓝 a)) : drift μ S t y e = a :=
  h.limsup_eq

end Problem336.PosteriorDrift

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CanonicalPosteriorIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem336.Observation

theorem historySigma_eq_iSup {Ω I T : Type*} (Y : I → T → Ω → ℝ) :
    historySigma Y =
      ⨆ i, MeasurableSpace.comap (fun ω s => Y i s ω) inferInstance := by
  simp only [historySigma, MeasurableSpace.comap_process_pi, iSup_prod]

theorem historySigma_finset_eq {Ω I T : Type*} (Y : I → T → Ω → ℝ)
    (S : Finset I) :
    historySigma (fun (i : S) s ω => Y i s ω) =
      ⨆ i ∈ S, MeasurableSpace.comap (fun ω s => Y i s ω) inferInstance := by
  rw [historySigma_eq_iSup]
  simp only [iSup_subtype]

theorem drift_eq_condExp_of_finite_history
    {Ω I : Type*} [mΩ : MeasurableSpace Ω] [Countable I]
    (P : Measure Ω) [IsFiniteMeasure P] (μ : ProbabilityMeasure (I → Bool))
    (S : I → ℕ → Finset I) (e : I)
    (hS : Monotone (S e)) (hcover : ∀ i, ∃ n, i ∈ S e n)
    (Y : I → ℝ≥0 → Ω → ℝ) (hY : ∀ i s, Measurable (Y i s))
    (X : Ω → ℝ) (t : ℝ≥0)
    (hfinite : ∀ n,
      (fun ω => TiltLimit.finiteTiltMean μ (S e n)
        (fun i => Y i t ω - (t : ℝ) / 2) e) =ᵐ[P]
        P[X | historySigma (fun (i : S e n) (s : Set.Iic t) ω => Y i s ω)]) :
    (fun ω => PosteriorDrift.drift μ S (t : ℝ) (fun i => Y i t ω) e) =ᵐ[P]
      P[X | historySigma (fun i (s : Set.Iic t) ω => Y i s ω)] := by
  let coordinate : I → MeasurableSpace Ω := fun i =>
    MeasurableSpace.comap (fun ω (s : Set.Iic t) => Y i s ω) inferInstance
  have hcoordinate : ∀ i, coordinate i ≤ mΩ := fun i =>
    (Measurable.of_eval (f := fun ω (s : Set.Iic t) => Y i s ω)
      (fun s => hY i s)).comap_le
  have hfinite' : ∀ n,
      (fun ω => TiltLimit.finiteTiltMean μ (S e n)
        (fun i => Y i t ω - (t : ℝ) / 2) e) =ᵐ[P]
        P[X | ⨆ i ∈ S e n, coordinate i] := by
    intro n
    have hn := hfinite n
    rw [historySigma_finset_eq (fun i (s : Set.Iic t) ω => Y i s ω) (S e n)] at hn
    exact hn
  have h := limsup_posterior_all_coordinates P coordinate hcoordinate (S e)
    hS hcover X _ hfinite'
  simpa only [PosteriorDrift.drift, CanonicalDrift.outerLimit,
    PosteriorDrift.finiteStage, historySigma_eq_iSup] using h

end Problem336.Observation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_BrownianCanonicalPosterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal BigOperators ProbabilityTheory Topology

namespace Problem336.Observation

theorem gaussianFiniteTilt_finset_eq {I : Type*}
    (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (e : I)
    (t : ℝ) (y : I → ℝ) :
    FinitePosterior.gaussianFiniteTilt (μ : Measure (I → Bool))
      (fun i : S => (i : I)) e t (fun i => y i) =
      TiltLimit.finiteTiltMean μ S (fun i => y i - t / 2) e := by
  unfold FinitePosterior.gaussianFiniteTilt TiltLimit.finiteTiltMean
    TiltLimit.tiltedMean TiltLimit.finiteEnergy
  have hsum (x : I → Bool) :
      (∑ i : S, (y i - t / 2) * FinitePosterior.binaryValue (x i)) =
        ∑ i ∈ S, (y i - t / 2) * FinitePosterior.binaryValue (x i) :=
    Finset.sum_coe_sort S (fun i : I => (y i - t / 2) * FinitePosterior.binaryValue (x i))
  simp_rw [hsum]
  simp only [FinitePosterior.binaryValue, TiltLimit.bit]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => mul_comm _ _)

theorem finiteTiltMean_eq_condExp_brownian_history
    {Ω I : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ProbabilityMeasure (I → Bool)) (X : Ω → I → Bool) (hX : Measurable X)
    (hprior : P.map X = (μ : Measure (I → Bool)))
    (B : I → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω s => B i s ω) P)
    (hBm : ∀ i s, Measurable (B i s))
    (hXB : IndepFun X (fun ω (p : I × ℝ≥0) => B p.1 p.2 ω) P)
    (S : Finset I) (e : I) (t : ℝ≥0) (ht : t ≠ 0) :
    (fun ω => TiltLimit.finiteTiltMean μ S
      (fun i => (t : ℝ) * TiltLimit.bit (X ω i) + B i t ω - (t : ℝ) / 2) e) =ᵐ[P]
      P[fun ω => TiltLimit.bit (X ω e) |
        historySigma (fun (i : S) (s : Set.Iic t) ω =>
          (s : ℝ) * TiltLimit.bit (X ω i) + B i s ω)] := by
  classical
  let noise : Ω → S → ℝ := fun ω i => B i t ω
  have hnoise : Measurable noise := Measurable.of_eval (fun i => hBm i t)
  have hbind : iIndepFun (fun (i : S) ω s => B i s ω) P :=
    hind.precomp Subtype.val_injective
  have heind : iIndepFun (fun (i : S) ω => B i t ω) P :=
    hbind.comp (fun _ f => f t) (fun _ => measurable_pi_apply t)
  have hnoiseLaw : P.map noise = Measure.pi (fun _ : S => gaussianReal 0 t) := by
    rw [iIndepFun.map_fun_eq_pi_map (fun (i : S) => (hBm i t).aemeasurable) heind]
    congr 1
    funext i
    exact (hB i).hasLaw_eval t |>.map_eq
  have hXnoise : IndepFun X noise P := hXB.comp measurable_id
    (show Measurable (fun f : I × ℝ≥0 → ℝ => fun i : S => f (i, t)) by fun_prop)
  have hXsub : IndepFun X (fun ω (p : S × ℝ≥0) => B p.1 p.2 ω) P :=
    hXB.comp measurable_id
      (show Measurable (fun f : I × ℝ≥0 → ℝ => fun p : S × ℝ≥0 => f (p.1, p.2)) by
        fun_prop)
  let D : (I → Bool) → S → ℝ := fun x i => TiltLimit.bit (x i)
  have hD : Measurable D := Measurable.of_eval (fun i =>
    TiltLimit.continuous_bit.measurable.comp (measurable_pi_apply (i : I)))
  let f : (I → Bool) → ℝ := fun x => TiltLimit.bit (x e)
  have hf : Measurable f :=
    TiltLimit.continuous_bit.measurable.comp (measurable_pi_apply e)
  have hfi : Integrable (f ∘ X) P := by
    exact (show Integrable TiltLimit.bit (P.map (fun ω => X ω e)) from
      Integrable.of_finite).comp_measurable ((measurable_pi_apply e).comp hX)
  have hh := BrownianBridge.condExp_observation_history_eq_endpoint
    (fun (i : S) => hB i) hbind (fun i s => hBm i s) hX D hD hXsub t ht f hf hfi
  have he := FinitePosterior.binaryField_gaussian_condExp P
    (μ : Measure (I → Bool)) X noise hX hnoise (fun i : S => (i : I)) e t ht
    hprior hnoiseLaw hXnoise
  have he' : P[f ∘ X | MeasurableSpace.comap
      (fun ω (i : S) => (t : ℝ) * TiltLimit.bit (X ω i) + B i t ω) inferInstance] =ᵐ[P]
      fun ω => TiltLimit.finiteTiltMean μ S
        (fun i => (t : ℝ) * TiltLimit.bit (X ω i) + B i t ω - (t : ℝ) / 2) e := by
    filter_upwards [he] with ω hω
    exact hω.trans (gaussianFiniteTilt_finset_eq μ S e t
      (fun i => (t : ℝ) * TiltLimit.bit (X ω i) + B i t ω))
  exact (hh.trans he').symm

theorem drift_eq_condExp_brownian_history
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ProbabilityMeasure (I → Bool)) (X : Ω → I → Bool) (hX : Measurable X)
    (hprior : P.map X = (μ : Measure (I → Bool)))
    (B : I → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω s => B i s ω) P)
    (hBm : ∀ i s, Measurable (B i s))
    (hXB : IndepFun X (fun ω (p : I × ℝ≥0) => B p.1 p.2 ω) P)
    (S : I → ℕ → Finset I) (e : I)
    (hS : Monotone (S e)) (hcover : ∀ i, ∃ n, i ∈ S e n)
    (t : ℝ≥0) (ht : t ≠ 0) :
    (fun ω => PosteriorDrift.drift μ S t
      (fun i => (t : ℝ) * TiltLimit.bit (X ω i) + B i t ω) e) =ᵐ[P]
      P[fun ω => TiltLimit.bit (X ω e) |
        historySigma (fun i (s : Set.Iic t) ω =>
          (s : ℝ) * TiltLimit.bit (X ω i) + B i s ω)] := by
  apply drift_eq_condExp_of_finite_history P μ S e hS hcover
    (fun i s ω => (s : ℝ) * TiltLimit.bit (X ω i) + B i s ω)
  · intro i s
    exact ((TiltLimit.continuous_bit.measurable.comp
      ((measurable_pi_apply i).comp hX)).const_mul _).add (hBm i s)
  · intro n
    exact finiteTiltMean_eq_condExp_brownian_history P μ X hX hprior B hB hind hBm hXB
      (S e n) e t ht

theorem drift_zero_zero {I : Type*} [Countable I]
    (μ : ProbabilityMeasure (I → Bool)) (S : I → ℕ → Finset I) (e : I) :
    PosteriorDrift.drift μ S 0 (fun _ => 0) e =
      ∫ x, TiltLimit.bit (x e) ∂(μ : Measure (I → Bool)) := by
  apply PosteriorDrift.drift_eq_of_tendsto
  simp [TiltLimit.finiteTiltMean, TiltLimit.tiltedMean, TiltLimit.finiteEnergy]

theorem drift_eq_condExp_brownian_history_zero
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ProbabilityMeasure (I → Bool)) (X : Ω → I → Bool) (hX : Measurable X)
    (hprior : P.map X = (μ : Measure (I → Bool)))
    (B : I → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hBm : ∀ i s, Measurable (B i s))
    (S : I → ℕ → Finset I) (e : I) :
    (fun ω => PosteriorDrift.drift μ S 0
      (fun i => (0 : ℝ) * TiltLimit.bit (X ω i) + B i 0 ω) e) =ᵐ[P]
      P[fun ω => TiltLimit.bit (X ω e) |
        historySigma (fun i (s : Set.Iic (0 : ℝ≥0)) ω =>
          (s : ℝ) * TiltLimit.bit (X ω i) + B i s ω)] := by
  let H := fun ω (p : I × Set.Iic (0 : ℝ≥0)) =>
    (p.2 : ℝ) * TiltLimit.bit (X ω p.1) + B p.1 p.2 ω
  have hH : Measurable H := by
    apply Measurable.of_eval
    intro p
    exact ((TiltLimit.continuous_bit.measurable.comp
      ((measurable_pi_apply p.1).comp hX)).const_mul _).add (hBm p.1 p.2)
  have hzero : ∀ᵐ ω ∂P, ∀ i, B i 0 ω = 0 :=
    ae_all_iff.mpr (fun i => (hB i).eval_zero_ae_eq_zero)
  have hHzero : H =ᵐ[P] fun _ => (0 : I × Set.Iic (0 : ℝ≥0) → ℝ) := by
    filter_upwards [hzero] with ω hω
    funext p
    have hs : (p.2 : ℝ≥0) = 0 := le_antisymm p.2.2 (by positivity)
    simp [H, hs, hω p.1]
  have hind0 : IndepFun X H P :=
    (indepFun_const_right X (0 : I × Set.Iic (0 : ℝ≥0) → ℝ)).congr
      Filter.EventuallyEq.rfl hHzero.symm
  have hs : StronglyMeasurable[(inferInstance : MeasurableSpace (I → Bool)).comap X]
      (fun ω => TiltLimit.bit (X ω e)) :=
    (TiltLimit.continuous_bit.measurable.comp
      ((measurable_pi_apply e).comp (comap_measurable X))).stronglyMeasurable
  have hc := condExp_indep_eq hX.comap_le hH.comap_le hs hind0
  have hmean : (∫ ω, TiltLimit.bit (X ω e) ∂P) =
      ∫ x, TiltLimit.bit (x e) ∂(μ : Measure (I → Bool)) := by
    rw [← hprior]
    exact (integral_map_of_stronglyMeasurable hX
      (TiltLimit.continuous_bit.measurable.comp (measurable_pi_apply e)).stronglyMeasurable).symm
  filter_upwards [hzero, hc] with ω hω hcω
  have hy : (fun i => (0 : ℝ) * TiltLimit.bit (X ω i) + B i 0 ω) =
      (fun _ => 0) := by
    funext i
    simp [hω i]
  rw [hy, drift_zero_zero]
  exact hmean.symm.trans hcω.symm

theorem drift_eq_condExp_brownian_history_all_times
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ProbabilityMeasure (I → Bool)) (X : Ω → I → Bool) (hX : Measurable X)
    (hprior : P.map X = (μ : Measure (I → Bool)))
    (B : I → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω s => B i s ω) P)
    (hBm : ∀ i s, Measurable (B i s))
    (hXB : IndepFun X (fun ω (p : I × ℝ≥0) => B p.1 p.2 ω) P)
    (S : I → ℕ → Finset I) (e : I)
    (hS : Monotone (S e)) (hcover : ∀ i, ∃ n, i ∈ S e n)
    (t : ℝ≥0) :
    (fun ω => PosteriorDrift.drift μ S t
      (fun i => (t : ℝ) * TiltLimit.bit (X ω i) + B i t ω) e) =ᵐ[P]
      P[fun ω => TiltLimit.bit (X ω e) |
        historySigma (fun i (s : Set.Iic t) ω =>
          (s : ℝ) * TiltLimit.bit (X ω i) + B i s ω)] := by
  by_cases ht : t = 0
  · subst t
    exact drift_eq_condExp_brownian_history_zero P μ X hX hprior B hB hBm S e
  · exact drift_eq_condExp_brownian_history P μ X hX hprior B hB hind hBm hXB
      S e hS hcover t ht

end Problem336.Observation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_IndependentProcessVectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Measure ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem336.IndependentProcessVectors

variable {Ω I J T E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P]

theorem iIndepFun_curry {X : I → J → Ω → E}
    (hX : ∀ i j, Measurable (X i j))
    (h : iIndepFun (fun p : I × J => X p.1 p.2) P) :
    iIndepFun (fun i ω j => X i j ω) P := by
  have : ∀ i j, IsProbabilityMeasure (P.map (X i j)) :=
    fun i j => Measure.isProbabilityMeasure_map (hX i j).aemeasurable
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  have hflat : Measurable (fun ω (p : I × J) => X p.1 p.2 ω) := by fun_prop
  have hc : (fun ω i j => X i j ω) =
      (MeasurableEquiv.curry I J E) ∘ (fun ω (p : I × J) => X p.1 p.2 ω) := rfl
  rw [hc, ← Measure.map_map (MeasurableEquiv.curry I J E).measurable hflat,
    (iIndepFun.map_fun_eq_infinitePi_map (X := fun p : I × J => X p.1 p.2) (fun p => hX p.1 p.2) h), Measure.infinitePi_map_curry (fun i j => P.map (X i j))]
  congr 1
  funext i
  exact (iIndepFun.map_fun_eq_infinitePi_map (X := X i) (hX i)
    (h.precomp (g := fun j : J => (i, j)) (fun a b hab => (Prod.mk.inj hab).2))).symm

theorem hasIndepIncrements_vector [Preorder T]
    {B : I → T → Ω → ℝ}
    (hm : ∀ i t, Measurable (B i t))
    (hi : iIndepFun (fun i ω t => B i t ω) P)
    (hB : ∀ i, HasIndepIncrements (B i) P) (S : Finset I) :
    HasIndepIncrements
      (fun t ω => (WithLp.toLp 2 (fun i : S => B i t ω) : EuclideanSpace ℝ S)) P := by
  intro n times htimes
  let D (i : S) (j : Fin n) (ω : Ω) :=
    B i (times j.succ) ω - B i (times j.castSucc) ω
  have hD (i : S) (j : Fin n) : Measurable (D i j) := (hm _ _).sub (hm _ _)
  have hrows : iIndepFun (fun i : S => fun ω (j : Fin n) => D i j ω) P := by
    exact (hi.precomp Subtype.val_injective).comp
      (fun _ (z : T → ℝ) (j : Fin n) => z (times j.succ) - z (times j.castSucc))
      (by intro i; fun_prop)
  have hflat : iIndepFun (fun p : S × Fin n => D p.1 p.2) P :=
    iIndepFun_uncurry' hD hrows (fun i => hB i n times htimes)
  have hswap : iIndepFun (fun p : Fin n × S => D p.2 p.1) P :=
    hflat.precomp (Equiv.prodComm (Fin n) S).injective
  have hcols := iIndepFun_curry (fun j i => hD i j) hswap
  exact hcols.comp (fun _ => (MeasurableEquiv.toLp 2 (S → ℝ)))
    (fun _ => (MeasurableEquiv.toLp 2 (S → ℝ)).measurable)

omit [IsProbabilityMeasure P] in

theorem brownian_vector_increment_hasLaw
    {B : I → ℝ≥0 → Ω → ℝ}
    (hm : ∀ i t, Measurable (B i t))
    (hi : iIndepFun (fun i ω t => B i t ω) P)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (S : Finset I) (s t : ℝ≥0) :
    HasLaw (fun ω => (WithLp.toLp 2
      (fun i : S => B i t ω - B i s ω) : EuclideanSpace ℝ S))
      ((Measure.infinitePi (fun _ : S => gaussianReal 0 (nndist t.1 s.1))).map
        (MeasurableEquiv.toLp 2 (S → ℝ))) P := by
  have hd : iIndepFun (fun i : S => fun ω => B i t ω - B i s ω) P :=
    (hi.precomp Subtype.val_injective).comp (fun _ (z : ℝ≥0 → ℝ) => z t - z s)
      (by intro i; fun_prop)
  have hl := hd.hasLaw_infinitePi (fun i : S => (hB i).hasLaw_sub t s)
    (Measurable.aemeasurable (by fun_prop))
  have he : HasLaw (MeasurableEquiv.toLp 2 (S → ℝ))
      ((Measure.infinitePi (fun _ : S => gaussianReal 0 (nndist t.1 s.1))).map
        (MeasurableEquiv.toLp 2 (S → ℝ)))
      (Measure.infinitePi (fun _ : S => gaussianReal 0 (nndist t.1 s.1))) :=
    ⟨(MeasurableEquiv.toLp 2 (S → ℝ)).measurable.aemeasurable, rfl⟩
  exact he.comp hl

end Problem336.IndependentProcessVectors

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_InnovationIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal NNReal

namespace Problem336.InnovationIdentification

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem restrict_map_eq_smul_of_characteristic
    {P : Measure Ω} [IsFiniteMeasure P] {ν : Measure E} [IsFiniteMeasure ν]
    {D : Ω → E} (hD : Measurable D) (A : Set Ω)
    (hchar : ∀ θ : E,
      (∫ ω in A, Complex.exp ((inner ℝ (D ω) θ : ℂ) * Complex.I) ∂P) =
        (P A).toReal • charFun ν θ) :
    (P.restrict A).map D = P A • ν := by
  have : IsFiniteMeasure (P A • ν) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (measure_lt_top P A) (measure_lt_top ν Set.univ)⟩
  apply Measure.ext_of_charFun
  funext θ
  rw [charFun_apply, integral_map hD.aemeasurable (by fun_prop), hchar θ]
  simp only [charFun_apply, integral_smul_measure]

theorem iIndepFun_of_past_characteristic
    {ι : Type*} [LinearOrder ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : ι → Measure E} [∀ i, IsProbabilityMeasure (ν i)]
    {D : ι → Ω → E} (hD : ∀ i, Measurable (D i))
    (hchar : ∀ (i : ι) (s : Finset ι) (sets : ι → Set E),
      (∀ j ∈ s, j < i) → (∀ j ∈ s, MeasurableSet (sets j)) → ∀ θ : E,
      (∫ ω in ⋂ j ∈ s, D j ⁻¹' sets j,
        Complex.exp ((inner ℝ (D i ω) θ : ℂ) * Complex.I) ∂P) =
        (P (⋂ j ∈ s, D j ⁻¹' sets j)).toReal • charFun (ν i) θ) :
    iIndepFun D P := by
  classical
  have hLaw (i : ι) : P.map (D i) = ν i := by
    have h := restrict_map_eq_smul_of_characteristic (hD i)
      (⋂ j ∈ (∅ : Finset ι), D j ⁻¹' (Set.univ : Set E))
      (hchar i ∅ (fun _ => Set.univ) (by simp) (by simp))
    simpa using h
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.2
  intro s sets hs
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert i s his ih =>
    have hi : i ∉ s := fun hi => lt_irrefl i (his i hi)
    have hsi : ∀ j ∈ s, MeasurableSet (sets j) :=
      fun j hj => hs j (Finset.mem_insert_of_mem hj)
    have hmi : MeasurableSet (sets i) := hs i (Finset.mem_insert_self i s)
    have heq := congrArg (fun ρ : Measure E => ρ (sets i))
      (restrict_map_eq_smul_of_characteristic (hD i)
        (⋂ j ∈ s, D j ⁻¹' sets j) (hchar i s sets his hsi))
    rw [Measure.map_apply (hD i) hmi, Measure.restrict_apply ((hD i) hmi),
      Measure.smul_apply, smul_eq_mul] at heq
    have hLi : ν i (sets i) = P (D i ⁻¹' sets i) := by
      rw [← hLaw i, Measure.map_apply (hD i) hmi]
    rw [hLi, ih hsi, mul_comm] at heq
    simpa only [Finset.set_biInter_insert, Finset.prod_insert hi] using heq

theorem hasIndepIncrements_of_past_characteristic
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : ℝ≥0 → ℝ≥0 → Measure E} [∀ s t, IsProbabilityMeasure (ν s t)]
    {W : ℝ≥0 → Ω → E} {ℱ : Filtration ℝ≥0 mΩ} (hW : Adapted ℱ W)
    (hchar : ∀ (s t : ℝ≥0), s ≤ t → ∀ A : Set Ω, MeasurableSet[ℱ s] A →
      ∀ θ : E,
      (∫ ω in A, Complex.exp ((inner ℝ (W t ω - W s ω) θ : ℂ) * Complex.I) ∂P) =
        (P A).toReal • charFun (ν s t) θ) :
    HasIndepIncrements W P := by
  intro n times htimes
  apply iIndepFun_of_past_characteristic
    (ν := fun i : Fin n => ν (times i.castSucc) (times i.succ))
    (fun i => hW.measurable.sub hW.measurable)
  intro i s sets hprior hsets θ
  apply hchar (times i.castSucc) (times i.succ) (htimes (Fin.castSucc_le_succ i))
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro hj
  have hjs : j.succ ≤ i.castSucc := by
    exact_mod_cast hprior j hj
  have hjc : j.castSucc ≤ i.castSucc := (Fin.castSucc_le_succ j).trans hjs
  exact ((hW.measurable_le (htimes hjs)).sub
    (hW.measurable_le (htimes hjc))) (hsets j hj)

end Problem336.InnovationIdentification

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_JointProcessLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

section PrivateCopy
open MeasureTheory Finset

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [LinearOrder T]

namespace Finset

variable (I : Finset T)

section Bot

variable [Bot T]

lemma orderEmbOfFinWithBot_of_ne_zero (i : Fin (#I + 1)) (hi : i ≠ 0) :
    I.orderEmbOfFinWithBot i = I.orderEmbOfFin rfl (i.pred hi) := by
  rw [orderEmbOfFinWithBot, dif_neg hi]

@[simp]
lemma orderEmbOfFinWithBot_succ (i : Fin #I) :
    I.orderEmbOfFinWithBot i.succ = I.orderEmbOfFin rfl i := by
  rw [orderEmbOfFinWithBot_of_ne_zero, Fin.pred_succ]
  simp

end Bot

lemma monotone_orderEmbOfFinWithBot [OrderBot T] : Monotone (I.orderEmbOfFinWithBot) := by
  intro i j hij
  obtain rfl | hi := eq_or_ne i 0
  · simp
  rw [orderEmbOfFinWithBot_of_ne_zero I i hi, orderEmbOfFinWithBot_of_ne_zero I j (by grind)]
  exact OrderEmbedding.monotone _ (by simpa)

end Finset

namespace ProbabilityTheory

lemma incrementsToRestrict_increments_orderEmbOfFinWithBot_ae_eq_restrict [Bot T] (R : Type*)
    [Semiring R] [AddCommGroup E] [Module R E] [TopologicalSpace E] [ContinuousAdd E]
    {X : T → Ω → E} (h : ∀ᵐ ω ∂P, X ⊥ ω = 0) (I : Finset T) :
    (fun ω ↦ I.restrict (X · ω)) =ᵐ[P]
      (incrementsToRestrict R I) ∘
        (fun ω i ↦ X (I.orderEmbOfFinWithBot i.succ) ω -
          X (I.orderEmbOfFinWithBot i.castSucc) ω) := by
  filter_upwards [h] with ω hω
  ext t
  simp only [restrict, incrementsToRestrict, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, Function.comp_apply]
  rw [Fin.sum_Iic_sub _ (fun j ↦ X (I.orderEmbOfFinWithBot j) ω)]
  simp [hω, orderEmbOfFin]
end ProbabilityTheory
end PrivateCopy

namespace OAI

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem336.JointProcessLaw

variable {Ω Ω' T E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [LinearOrder T] [OrderBot T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {Q : Measure Ω'} [IsProbabilityMeasure Q]
  {X : T → Ω → E} {Y : T → Ω' → E}

omit [IsProbabilityMeasure Q] in

theorem identDistrib_process_of_increments
    (hX : ∀ t, Measurable (X t)) (hY : ∀ t, Measurable (Y t))
    (hX0 : ∀ᵐ ω ∂P, X ⊥ ω = 0) (hY0 : ∀ᵐ ω ∂Q, Y ⊥ ω = 0)
    (hXi : HasIndepIncrements X P) (hYi : HasIndepIncrements Y Q)
    (hinc : ∀ s t, s ≤ t →
      IdentDistrib (fun ω => X t ω - X s ω) (fun ω => Y t ω - Y s ω) P Q) :
    IdentDistrib (fun ω t => X t ω) (fun ω t => Y t ω) P Q := by
  classical
  have hXm : Measurable (fun ω t => X t ω) := Measurable.of_eval hX
  have hYm : Measurable (fun ω t => Y t ω) := Measurable.of_eval hY
  have hrestrict (S : Finset T) :
      IdentDistrib (fun ω => S.restrict (X · ω))
        (fun ω => S.restrict (Y · ω)) P Q := by
    let DX : Fin S.card → Ω → E := fun i ω =>
      X (S.orderEmbOfFinWithBot i.succ) ω - X (S.orderEmbOfFinWithBot i.castSucc) ω
    let DY : Fin S.card → Ω' → E := fun i ω =>
      Y (S.orderEmbOfFinWithBot i.succ) ω - Y (S.orderEmbOfFinWithBot i.castSucc) ω
    have hDX : ∀ i, Measurable (DX i) := fun _ => (hX _).sub (hX _)
    have hDY : ∀ i, Measurable (DY i) := fun _ => (hY _).sub (hY _)
    have hdmap : P.map (fun ω i => DX i ω) = Q.map (fun ω i => DY i ω) := by
      rw [(hXi _ _ (S.monotone_orderEmbOfFinWithBot)).map_fun_eq_infinitePi_map hDX,
        (hYi _ _ (S.monotone_orderEmbOfFinWithBot)).map_fun_eq_infinitePi_map hDY]
      congr 1
      funext i
      exact (hinc _ _ (S.monotone_orderEmbOfFinWithBot (Fin.castSucc_le_succ i))).map_eq
    have hd : IdentDistrib (fun ω i => DX i ω) (fun ω i => DY i ω) P Q :=
      ⟨(Measurable.of_eval hDX).aemeasurable,
        (Measurable.of_eval hDY).aemeasurable, hdmap⟩
    have hc := hd.comp (incrementsToRestrict ℝ S).measurable
    have hx := incrementsToRestrict_increments_orderEmbOfFinWithBot_ae_eq_restrict ℝ hX0 S
    have hy := incrementsToRestrict_increments_orderEmbOfFinWithBot_ae_eq_restrict ℝ hY0 S
    exact ((IdentDistrib.of_ae_eq
      (Measurable.of_eval (fun i => hX i.1)).aemeasurable hx).trans hc).trans
      (IdentDistrib.of_ae_eq
        (Measurable.of_eval (fun i => hY i.1)).aemeasurable hy).symm
  refine ⟨hXm.aemeasurable, hYm.aemeasurable, ?_⟩
  let F (S : Finset T) : Measure (S → E) :=
    (P.map (fun ω t => X t ω)).map S.restrict
  have hp : IsProjectiveLimit (P.map (fun ω t => X t ω)) F := fun _ => rfl
  have hq : IsProjectiveLimit (Q.map (fun ω t => Y t ω)) F := by
    intro S
    have hm : Measurable (fun z : T → E => S.restrict z) :=
      Measurable.of_eval (fun i => measurable_pi_apply i.1)
    change (Q.map (fun ω t => Y t ω)).map S.restrict =
      (P.map (fun ω t => X t ω)).map S.restrict
    rw [Measure.map_map hm hYm, Measure.map_map hm hXm]
    exact (hrestrict S).map_eq.symm
  exact hp.unique hq

omit [IsProbabilityMeasure Q] in

theorem identDistrib_family_of_finite_increments {I : Type*}
    {W : I → T → Ω → ℝ} {B : I → T → Ω' → ℝ}
    (hW : ∀ i t, Measurable (W i t)) (hB : ∀ i t, Measurable (B i t))
    (hW0 : ∀ i, ∀ᵐ ω ∂P, W i ⊥ ω = 0)
    (hB0 : ∀ i, ∀ᵐ ω ∂Q, B i ⊥ ω = 0)
    (hWi : ∀ S : Finset I, HasIndepIncrements
      (fun t ω => (WithLp.toLp 2 (fun i : S => W i t ω) : EuclideanSpace ℝ S)) P)
    (hBi : ∀ S : Finset I, HasIndepIncrements
      (fun t ω => (WithLp.toLp 2 (fun i : S => B i t ω) : EuclideanSpace ℝ S)) Q)
    (hinc : ∀ (S : Finset I) (s t : T), s ≤ t →
      IdentDistrib
        (fun ω => (WithLp.toLp 2 (fun i : S => W i t ω - W i s ω) : EuclideanSpace ℝ S))
        (fun ω => (WithLp.toLp 2 (fun i : S => B i t ω - B i s ω) : EuclideanSpace ℝ S)) P Q) :
    IdentDistrib (fun ω i t => W i t ω) (fun ω i t => B i t ω) P Q := by
  classical
  have hWm : Measurable (fun ω i t => W i t ω) :=
    Measurable.of_eval (fun i => Measurable.of_eval (hW i))
  have hBm : Measurable (fun ω i t => B i t ω) :=
    Measurable.of_eval (fun i => Measurable.of_eval (hB i))
  have hrestrict (S : Finset I) :
      IdentDistrib (fun ω => S.restrict (fun i t => W i t ω))
        (fun ω => S.restrict (fun i t => B i t ω)) P Q := by
    have hWS (t : T) : Measurable
        (fun ω => (WithLp.toLp 2 (fun i : S => W i t ω) : EuclideanSpace ℝ S)) :=
      (MeasurableEquiv.toLp 2 (S → ℝ)).measurable.comp
        (Measurable.of_eval (fun i => hW i t))
    have hBS (t : T) : Measurable
        (fun ω => (WithLp.toLp 2 (fun i : S => B i t ω) : EuclideanSpace ℝ S)) :=
      (MeasurableEquiv.toLp 2 (S → ℝ)).measurable.comp
        (Measurable.of_eval (fun i => hB i t))
    have hWS0 : ∀ᵐ ω ∂P,
        (WithLp.toLp 2 (fun i : S => W i ⊥ ω) : EuclideanSpace ℝ S) = 0 := by
      filter_upwards [ae_all_iff.mpr (fun i : S => hW0 i)] with ω hω
      ext i
      exact hω i
    have hBS0 : ∀ᵐ ω ∂Q,
        (WithLp.toLp 2 (fun i : S => B i ⊥ ω) : EuclideanSpace ℝ S) = 0 := by
      filter_upwards [ae_all_iff.mpr (fun i : S => hB0 i)] with ω hω
      ext i
      exact hω i
    have hproc := identDistrib_process_of_increments hWS hBS hWS0 hBS0 (hWi S) (hBi S)
      (fun s t hst => hinc S s t hst)
    have hswap : Measurable (fun z : T → EuclideanSpace ℝ S => fun i : S => fun t => z t i) := by
      fun_prop
    exact hproc.comp hswap
  refine ⟨hWm.aemeasurable, hBm.aemeasurable, ?_⟩
  let F (S : Finset I) : Measure (S → T → ℝ) :=
    (P.map (fun ω i t => W i t ω)).map S.restrict
  have hp : IsProjectiveLimit (P.map (fun ω i t => W i t ω)) F := fun _ => rfl
  have hq : IsProjectiveLimit (Q.map (fun ω i t => B i t ω)) F := by
    intro S
    have hm : Measurable (fun z : I → T → ℝ => S.restrict z) :=
      Measurable.of_eval (fun i => measurable_pi_apply i.1)
    change (Q.map (fun ω i t => B i t ω)).map S.restrict =
      (P.map (fun ω i t => W i t ω)).map S.restrict
    rw [Measure.map_map hm hBm, Measure.map_map hm hWm]
    exact (hrestrict S).map_eq.symm
  exact hp.unique hq

end Problem336.JointProcessLaw

end
end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_JointInnovationLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem336.JointInnovationLaw

variable {Ω Ω' I : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} [IsProbabilityMeasure P]
  {Q : Measure Ω'} [IsProbabilityMeasure Q]

omit [IsProbabilityMeasure Q] in

theorem identDistrib_of_past_characteristic
    (F : Filtration ℝ≥0 mΩ)
    (W : I → ℝ≥0 → Ω → ℝ) (B : I → ℝ≥0 → Ω' → ℝ)
    (hW : ∀ i, Adapted F (W i)) (hB : ∀ i t, Measurable (B i t))
    (hW0 : ∀ i, ∀ᵐ ω ∂P, W i 0 ω = 0)
    (hB0 : ∀ i, ∀ᵐ ω ∂Q, B i 0 ω = 0)
    (ν : (S : Finset I) → ℝ≥0 → ℝ≥0 → Measure (EuclideanSpace ℝ S))
    [∀ S s t, IsProbabilityMeasure (ν S s t)]
    (hchar : ∀ (S : Finset I) (s t : ℝ≥0), s ≤ t →
      ∀ A : Set Ω, MeasurableSet[F s] A → ∀ θ : EuclideanSpace ℝ S,
      (∫ ω in A, Complex.exp ((inner ℝ
        (WithLp.toLp 2 (fun i : S => W i t ω - W i s ω) : EuclideanSpace ℝ S) θ : ℂ)
          * Complex.I) ∂P) = (P A).toReal • charFun (ν S s t) θ)
    (hBi : ∀ S : Finset I, HasIndepIncrements
      (fun t ω => (WithLp.toLp 2 (fun i : S => B i t ω) : EuclideanSpace ℝ S)) Q)
    (hBLaw : ∀ (S : Finset I) (s t : ℝ≥0), s ≤ t →
      HasLaw (fun ω => (WithLp.toLp 2 (fun i : S => B i t ω - B i s ω) :
        EuclideanSpace ℝ S)) (ν S s t) Q) :
    IdentDistrib (fun ω i t => W i t ω) (fun ω i t => B i t ω) P Q := by
  have hWS (S : Finset I) : Adapted F
      (fun t ω => (WithLp.toLp 2 (fun i : S => W i t ω) : EuclideanSpace ℝ S)) := by
    intro t
    let : MeasurableSpace Ω := F t
    exact (MeasurableEquiv.toLp 2 (S → ℝ)).measurable.comp
      (Measurable.of_eval (fun i => hW i t))
  refine JointProcessLaw.identDistrib_family_of_finite_increments
    (fun i t => (hW i).measurable (i := t)) hB hW0 hB0 ?_ hBi ?_
  · intro S
    exact InnovationIdentification.hasIndepIncrements_of_past_characteristic
      (hWS S) (hchar S)
  · intro S s t hst
    have hD : Measurable (fun ω => (WithLp.toLp 2
        (fun i : S => W i t ω - W i s ω) : EuclideanSpace ℝ S)) :=
      ((hWS S).measurable (i := t)).sub ((hWS S).measurable (i := s))
    have hlaw : HasLaw (fun ω => (WithLp.toLp 2
        (fun i : S => W i t ω - W i s ω) : EuclideanSpace ℝ S)) (ν S s t) P := by
      refine ⟨hD.aemeasurable, ?_⟩
      have h := InnovationIdentification.restrict_map_eq_smul_of_characteristic
        hD Set.univ (hchar S s t hst Set.univ MeasurableSet.univ)
      simpa using h
    exact hlaw.identDistrib (hBLaw S s t hst)

end Problem336.JointInnovationLaw

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_BrownianFamilyIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem336.BrownianFamilyIdentification

variable {I : Type*}

theorem charFun_vectorGaussian (S : Finset I) (h : ℝ≥0) (θ : EuclideanSpace ℝ S) :
    charFun (vectorGaussian S h) θ =
      Complex.exp (-((h : ℝ) : ℂ) * (‖θ‖ : ℂ) ^ 2 / 2) := by
  classical
  rw [vectorGaussian, Measure.infinitePi_eq_pi]
  change charFun ((Measure.pi (fun _ : S => gaussianReal 0 h)).map
    (WithLp.toLp 2)) θ = _
  rw [charFun_pi]
  simp only [charFun_gaussianReal, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  rw [← Complex.exp_sum]
  congr 1
  rw [← Complex.ofReal_pow, EuclideanSpace.real_norm_sq_eq]
  simp [Complex.ofReal_sum, Finset.sum_div, Finset.mul_sum, neg_div, neg_mul]

variable {Ω Ω' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} [IsProbabilityMeasure P]
  {Q : Measure Ω'} [IsProbabilityMeasure Q]

theorem identDistrib_brownian_family
    (F : Filtration ℝ≥0 mΩ)
    (W : I → ℝ≥0 → Ω → ℝ) (B : I → ℝ≥0 → Ω' → ℝ)
    (hW : ∀ i, Adapted F (W i)) (hBm : ∀ i t, Measurable (B i t))
    (hW0 : ∀ i, ∀ᵐ ω ∂P, W i 0 ω = 0)
    (hB : ∀ i, IsPreBrownianReal (B i) Q)
    (hi : iIndepFun (fun i ω t => B i t ω) Q)
    (hchar : ∀ (S : Finset I) (s t : ℝ≥0), s ≤ t →
      ∀ A : Set Ω, MeasurableSet[F s] A → ∀ θ : EuclideanSpace ℝ S,
      (∫ ω in A, Complex.exp ((inner ℝ
        (WithLp.toLp 2 (fun i : S => W i t ω - W i s ω) : EuclideanSpace ℝ S) θ : ℂ)
          * Complex.I) ∂P) = (P A).toReal • charFun (vectorGaussian S (t - s)) θ) :
    IdentDistrib (fun ω i t => W i t ω) (fun ω i t => B i t ω) P Q := by
  refine JointInnovationLaw.identDistrib_of_past_characteristic F W B hW hBm
    hW0 (fun i => (hB i).eval_zero_ae_eq_zero)
    (fun S s t => vectorGaussian S (t - s)) hchar ?_ ?_
  · intro S
    exact IndependentProcessVectors.hasIndepIncrements_vector hBm hi
      (fun i => (hB i).hasIndepIncrements) S
  · intro S s t hst
    have hstR : (s : ℝ) ≤ (t : ℝ) := hst
    have hd : nndist t.1 s.1 = t - s := by
      apply NNReal.coe_injective
      change dist (t : ℝ) (s : ℝ) = ((t - s : ℝ≥0) : ℝ)
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hstR), NNReal.coe_sub hst]
    simpa only [vectorGaussian, hd] using
      IndependentProcessVectors.brownian_vector_increment_hasLaw hBm hi hB S s t

end Problem336.BrownianFamilyIdentification

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_BrownianFamilyPast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Problem336.BrownianFamilyPast

variable {Ω I : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : I → ℝ≥0 → Ω → ℝ}

theorem indepFun_shift_past
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hI : iIndepFun (fun i ω t => B i t ω) P) (u : ℝ≥0) :
    IndepFun
      (fun ω (p : I × ℝ≥0) => B p.1 (u + p.2) ω - B p.1 u ω)
      (fun ω (p : I × Set.Iic u) => B p.1 p.2 ω) P := by
  classical
  have hG := BrownianBridge.isGaussianProcess_independent_family
    (fun i => (hB i).isGaussianProcess) hI
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero
  · apply hG.of_isGaussianProcess
    rintro (⟨i, t⟩ | ⟨i, ⟨t, ht⟩⟩)
    · exact ⟨{(i, u), (i, u + t)},
        { toFun x := x ⟨(i, u + t), by simp⟩ - x ⟨(i, u), by simp⟩
          map_add' x y := by simp; abel
          map_smul' c x := by simp; ring }, by simp⟩
    · exact ⟨{(i, t)},
        { toFun x := x ⟨(i, t), by simp⟩
          map_add' x y := by simp
          map_smul' c x := by simp }, by simp⟩
  · intro p
    exact ((hB p.1).aemeasurable _).sub ((hB p.1).aemeasurable _)
  · intro p
    exact (hB p.1).aemeasurable _
  · rintro ⟨i, t⟩ ⟨j, s⟩
    have hf := (hB i).isGaussianProcess.hasGaussianLaw_sub
      (s := u + t) (t := u)
    have hg := (hB j).isGaussianProcess.hasGaussianLaw_eval (s : ℝ≥0)
    apply IndepFun.covariance_eq_zero _ hf.memLp_two hg.memLp_two
    by_cases hij : i = j
    · subst j
      exact ((hB i).indepFun_shift u).comp
        (measurable_pi_apply t) (measurable_pi_apply s)
    · exact (hI.indepFun hij).comp
        (show Measurable (fun f : ℝ≥0 → ℝ => f (u + t) - f u) by fun_prop)
        (measurable_pi_apply (s : ℝ≥0))

theorem indepFun_shift_hidden_past {A : Type*} [MeasurableSpace A]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hBm : ∀ i t, Measurable (B i t))
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    {X : Ω → A} (hX : Measurable X)
    (hXB : IndepFun X (fun ω i t => B i t ω) P) (u : ℝ≥0) :
    IndepFun
      (fun ω (p : I × ℝ≥0) => B p.1 (u + p.2) ω - B p.1 u ω)
      (fun ω => (X ω, fun p : I × Set.Iic u => B p.1 p.2 ω)) P := by
  have : IsProbabilityMeasure P := hI.isProbabilityMeasure
  have hpair : IndepFun X
      (fun ω =>
        ((fun p : I × ℝ≥0 => B p.1 (u + p.2) ω - B p.1 u ω),
          fun p : I × Set.Iic u => B p.1 p.2 ω)) P := by
    exact hXB.comp measurable_id
      (show Measurable (fun f : I → ℝ≥0 → ℝ =>
        ((fun p : I × ℝ≥0 => f p.1 (u + p.2) - f p.1 u),
          fun p : I × Set.Iic u => f p.1 p.2)) by fun_prop)
  exact BrownianBridge.indepFun_regroup hX (by fun_prop) (by fun_prop)
    hpair (indepFun_shift_past hB hI u)

theorem indepFun_shift_hidden_observation
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hBm : ∀ i t, Measurable (B i t))
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    {X : Ω → I → ℝ} (hX : Measurable X)
    (hXB : IndepFun X (fun ω i t => B i t ω) P) (u : ℝ≥0) :
    IndepFun
      (fun ω (p : I × ℝ≥0) => B p.1 (u + p.2) ω - B p.1 u ω)
      (fun ω => (X ω, fun p : I × Set.Iic u =>
        (p.2 : ℝ≥0) * X ω p.1 + B p.1 p.2 ω)) P := by
  exact (indepFun_shift_hidden_past hB hBm hI hX hXB u).comp measurable_id
    (show Measurable (fun q : (I → ℝ) × (I × Set.Iic u → ℝ) =>
      (q.1, fun p : I × Set.Iic u => (p.2 : ℝ≥0) * q.1 p.1 + q.2 p)) by fun_prop)

theorem indepFun_weighted_increment_observation
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hBm : ∀ i t, Measurable (B i t))
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    {X : Ω → I → ℝ} (hX : Measurable X)
    (hXB : IndepFun X (fun ω i t => B i t ω) P)
    (S : Finset I) (θ : I → ℝ) (u h : ℝ≥0) :
    IndepFun (fun ω => ∑ i ∈ S, θ i * (B i (u + h) ω - B i u ω))
      (fun ω (p : I × Set.Iic u) =>
        (p.2 : ℝ≥0) * X ω p.1 + B p.1 p.2 ω) P := by
  exact (indepFun_shift_hidden_observation hB hBm hI hX hXB u).comp
    (show Measurable (fun f : I × ℝ≥0 → ℝ => ∑ i ∈ S, θ i * f (i, h)) by fun_prop)
    measurable_snd

theorem integral_weighted_increment_eq_zero
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (S : Finset I) (θ : I → ℝ) (u h : ℝ≥0) :
    (∫ ω, ∑ i ∈ S, θ i * (B i (u + h) ω - B i u ω) ∂P) = 0 := by
  have hi (i : I) : Integrable (fun ω => θ i * (B i (u + h) ω - B i u ω)) P :=
    (((hB i).integrable_eval (u + h)).sub ((hB i).integrable_eval u)).const_mul (θ i)
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_eq_zero
  intro i hi
  rw [integral_const_mul, integral_sub ((hB i).integrable_eval _)
    ((hB i).integrable_eval _), (hB i).integral_eval, (hB i).integral_eval]
  simp

theorem condExp_weighted_increment_observation_eq_zero
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hBm : ∀ i t, Measurable (B i t))
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    {X : Ω → I → ℝ} (hX : Measurable X)
    (hXB : IndepFun X (fun ω i t => B i t ω) P)
    (S : Finset I) (θ : I → ℝ) (u h : ℝ≥0) :
    P[(fun ω => ∑ i ∈ S, θ i * (B i (u + h) ω - B i u ω)) |
      MeasurableSpace.comap (fun ω (p : I × Set.Iic u) =>
        (p.2 : ℝ≥0) * X ω p.1 + B p.1 p.2 ω) inferInstance]
      =ᵐ[P] (fun _ => (0 : ℝ)) := by
  have : IsProbabilityMeasure P := hI.isProbabilityMeasure
  have hQ : Measurable (fun ω => ∑ i ∈ S, θ i * (B i (u + h) ω - B i u ω)) := by
    fun_prop
  have hH : Measurable (fun ω (p : I × Set.Iic u) =>
      (p.2 : ℝ≥0) * X ω p.1 + B p.1 p.2 ω) := by fun_prop
  have hc := condExp_indep_eq hQ.comap_le hH.comap_le
    (comap_measurable _).stronglyMeasurable
    (indepFun_weighted_increment_observation hB hBm hI hX hXB S θ u h)
  simpa only [integral_weighted_increment_eq_zero hB S θ u h] using hc

theorem setIntegral_weighted_increment_observation_eq_zero
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hBm : ∀ i t, Measurable (B i t))
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    {X : Ω → I → ℝ} (hX : Measurable X)
    (hXB : IndepFun X (fun ω i t => B i t ω) P)
    (S : Finset I) (θ : I → ℝ) (u h : ℝ≥0) {A : Set Ω}
    (hA : MeasurableSet[MeasurableSpace.comap (fun ω (p : I × Set.Iic u) =>
      (p.2 : ℝ≥0) * X ω p.1 + B p.1 p.2 ω) inferInstance] A) :
    (∫ ω in A, ∑ i ∈ S, θ i * (B i (u + h) ω - B i u ω) ∂P) = 0 := by
  have : IsProbabilityMeasure P := hI.isProbabilityMeasure
  have hH : Measurable (fun ω (p : I × Set.Iic u) =>
      (p.2 : ℝ≥0) * X ω p.1 + B p.1 p.2 ω) := by fun_prop
  have hQ : Integrable (fun ω => ∑ i ∈ S, θ i * (B i (u + h) ω - B i u ω)) P := by
    apply integrable_finsetSum
    intro i hi
    exact (((hB i).integrable_eval (u + h)).sub ((hB i).integrable_eval u)).const_mul _
  rw [← setIntegral_condExp hH.comap_le hQ hA]
  exact integral_eq_zero_of_ae (ae_restrict_of_ae
    (condExp_weighted_increment_observation_eq_zero hB hBm hI hX hXB S θ u h))

end Problem336.BrownianFamilyPast

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_BrownianReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336.BrownianReference

variable {A W I : Type*} [MeasurableSpace A] [MeasurableSpace W]
  (ν : Measure A) (ρ : Measure W) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]

omit [IsProbabilityMeasure ν] in
theorem hidden_hasLaw : HasLaw (fun q : A × (I → W) => q.1) ν (coupling ν ρ) :=
  measurePreserving_fst.hasLaw

theorem noise_coordinate_preserving (i : I) :
    MeasurePreserving (fun q : A × (I → W) => q.2 i) (coupling ν ρ) ρ :=
  (measurePreserving_eval_infinitePi (fun _ : I => ρ) i).comp measurePreserving_snd

theorem independent_samples :
    iIndepFun (fun (i : I) (q : A × (I → W)) => q.2 i) (coupling ν ρ) := by
  have hm : ∀ i : I, Measurable (fun q : A × (I → W) => q.2 i) :=
    fun i => (measurable_pi_apply i).comp measurable_snd
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map hm).2
  simp_rw [(noise_coordinate_preserving ν ρ _).map_eq]
  exact measurePreserving_snd.map_eq

theorem independent_processes (b : ℝ≥0 → W → ℝ) (hb : ∀ t, Measurable (b t)) :
    iIndepFun (fun (i : I) (q : A × (I → W)) t => b t (q.2 i)) (coupling ν ρ) :=
  (independent_samples ν ρ).comp (fun _ w t => b t w)
    (fun _ => Measurable.of_eval hb)

theorem hidden_independent_field (b : ℝ≥0 → W → ℝ) (hb : ∀ t, Measurable (b t)) :
    IndepFun (fun q : A × (I → W) => q.1)
      (fun q (p : I × ℝ≥0) => b p.2 (q.2 p.1)) (coupling ν ρ) := by
  have h : IndepFun (fun q : A × (I → W) => q.1) (fun q => q.2) (coupling ν ρ) :=
    indepFun_prod measurable_id measurable_id
  exact h.comp measurable_id
    (Measurable.of_eval (fun p : I × ℝ≥0 => (hb p.2).comp (measurable_pi_apply p.1)))

theorem preBrownian_process {b : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal b ρ) (i : I) :
    IsPreBrownianReal (fun t (q : A × (I → W)) => b t (q.2 i)) (coupling ν ρ) := by
  constructor
  intro S
  exact (hB.hasLaw S).comp (noise_coordinate_preserving ν ρ i).hasLaw

theorem brownian_process {b : ℝ≥0 → W → ℝ} (hB : IsBrownianReal b ρ) (i : I) :
    IsBrownianReal (fun t (q : A × (I → W)) => b t (q.2 i)) (coupling ν ρ) where
  toIsPreBrownianReal := preBrownian_process ν ρ hB.toIsPreBrownianReal i
  cont := (noise_coordinate_preserving ν ρ i).quasiMeasurePreserving.ae hB.cont

end Problem336.BrownianReference

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_GlobalWiener
attribute [-instance] _root_.OAI.Problem336.CanonicalBrownianReference.law_probability _root_.OAI.Problem336.CanonicalBrownianReference.noiseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace Problem336.GlobalWiener

attribute [local instance] OAI.Problem336.GlobalWiener.instMeasurableSpacePath
theorem isBrownian_wienerMeasure :
    IsBrownianReal (fun t (w : Path) => w t) wienerMeasure :=
  (Classical.choose_spec exists_wiener).2

end Problem336.GlobalWiener

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CanonicalBrownianReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace Problem336.CanonicalBrownianReference

variable {I : Type*} (μ : ProbabilityMeasure (I → Bool))

attribute [local instance] OAI.Problem336.CanonicalBrownianReference.instMeasurableSpacePath
theorem hidden_measurable : Measurable (hidden (I := I)) := measurable_fst

theorem hidden_hasLaw : HasLaw hidden (μ : Measure (I → Bool)) (law μ) :=
  BrownianReference.hidden_hasLaw (μ : Measure (I → Bool)) GlobalWiener.wienerMeasure

theorem paths_hasLaw :
    HasLaw (fun q : Space I => q.2) (noiseLaw I) (law μ) :=
  measurePreserving_snd.hasLaw

attribute [local instance] OAI.Problem336.CanonicalBrownianReference.instBorelSpacePath
theorem raw_noise_hasLaw :
    HasLaw (fun (q : Space I) i t => noise i t q)
      ((noiseLaw I).map (fun (w : I → GlobalWiener.Path) i t => w i t)) (law μ) := by
  have hm : Measurable (fun (w : I → GlobalWiener.Path) i t => w i t) :=
    Measurable.of_eval (fun i => Measurable.of_eval (fun t =>
      (continuous_eval_const t).measurable.comp (measurable_pi_apply i)))
  exact (show HasLaw (fun (w : I → GlobalWiener.Path) i t => w i t)
    ((noiseLaw I).map (fun (w : I → GlobalWiener.Path) i t => w i t))
    (noiseLaw I) from ⟨hm.aemeasurable, rfl⟩).comp (paths_hasLaw μ)

theorem noise_measurable (i : I) (t : ℝ≥0) : Measurable (noise i t) :=
  (continuous_eval_const t).measurable.comp ((measurable_pi_apply i).comp measurable_snd)

theorem noise_continuous (q : Space I) (i : I) :
    Continuous (fun t => noise i t q) := (q.2 i).continuous

theorem noise_brownian (i : I) : IsBrownianReal (noise i) (law μ) :=
  BrownianReference.brownian_process (μ : Measure (I → Bool))
    GlobalWiener.wienerMeasure GlobalWiener.isBrownian_wienerMeasure i

theorem noise_independent :
    iIndepFun (fun i (q : Space I) t => noise i t q) (law μ) :=
  BrownianReference.independent_processes (μ : Measure (I → Bool))
    GlobalWiener.wienerMeasure (fun t w => w t)
    (fun t => (continuous_eval_const t).measurable)

theorem hidden_independent_flat_noise :
    IndepFun hidden (fun (q : Space I) (p : I × ℝ≥0) => noise p.1 p.2 q) (law μ) :=
  BrownianReference.hidden_independent_field (μ : Measure (I → Bool))
    GlobalWiener.wienerMeasure (fun t w => w t)
    (fun t => (continuous_eval_const t).measurable)

theorem hidden_independent_noise :
    IndepFun hidden (fun (q : Space I) i t => noise i t q) (law μ) := by
  exact (hidden_independent_flat_noise μ).comp measurable_id
    (show Measurable (fun f : I × ℝ≥0 → ℝ => fun i t => f (i, t)) by fun_prop)

theorem bit_hidden_measurable :
    Measurable (fun q : Space I => fun i => TiltLimit.bit (hidden q i)) := by
  apply Measurable.of_eval
  intro i
  exact TiltLimit.continuous_bit.measurable.comp
    ((measurable_pi_apply i).comp measurable_fst)

theorem bit_hidden_independent_noise :
    IndepFun (fun q : Space I => fun i => TiltLimit.bit (hidden q i))
      (fun (q : Space I) i t => noise i t q) (law μ) := by
  exact (hidden_independent_noise μ).comp
    (Measurable.of_eval (fun i => TiltLimit.continuous_bit.measurable.comp
      (measurable_pi_apply i))) measurable_id

theorem bit_hidden_mem_Icc (q : Space I) (i : I) :
    TiltLimit.bit (hidden q i) ∈ Set.Icc (0 : ℝ) 1 := by
  cases hidden q i <;> norm_num [TiltLimit.bit]

end Problem336.CanonicalBrownianReference

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_InnovationMartingale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace Problem336.Innovation

theorem integrable_bounded_field {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {b : ℝ → Ω → ℝ}
    (hb : Measurable (Function.uncurry b)) {C : ℝ}
    (hbound : ∀ t ω, ‖b t ω‖ ≤ C) (u v : ℝ) (A : Set Ω) :
    Integrable (Function.uncurry b)
      ((volume.restrict (uIoc u v)).prod (P.restrict A)) := by
  let : IsFiniteMeasure (volume.restrict (uIoc u v)) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min u v) (max u v)))
    infer_instance
  exact Integrable.of_bound hb.aestronglyMeasurable C
    (Eventually.of_forall (fun q => hbound q.1 q.2))

theorem integral_integrated_drift {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {b : ℝ → Ω → ℝ}
    (hb : Measurable (Function.uncurry b)) {C : ℝ}
    (hbound : ∀ t ω, ‖b t ω‖ ≤ C) (u v : ℝ) (A : Set Ω) (m : ℝ)
    (hmean : ∀ t ∈ uIoc u v, ∫ ω in A, b t ω ∂P = m) :
    (∫ ω in A, (∫ t in u..v, b t ω) ∂P) = (v - u) * m := by
  rw [← intervalIntegral_integral_swap
    (integrable_bounded_field P hb hbound u v A)]
  calc
    (∫ t in u..v, ∫ ω in A, b t ω ∂P) = ∫ _t in u..v, m := by
      apply intervalIntegral.integral_congr_ae
      exact Eventually.of_forall hmean
    _ = (v - u) * m := by simp

theorem integrable_integrated_field {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {b : ℝ → Ω → ℝ}
    (hb : Measurable (Function.uncurry b)) {C : ℝ}
    (hbound : ∀ t ω, ‖b t ω‖ ≤ C) (u v : ℝ) :
    Integrable (fun ω => ∫ t in u..v, b t ω) P := by
  have hprod := integrable_bounded_field P hb hbound u v univ
  simp only [Measure.restrict_univ] at hprod
  have hint := hprod.integral_prod_right
  simpa only [intervalIntegral.intervalIntegral_eq_integral_uIoc,
    Function.uncurry_apply_pair, Pi.smul_def] using
    hint.smul (if u ≤ v then (1 : ℝ) else -1)

theorem intervalIntegrable_field {Ω : Type*} [MeasurableSpace Ω]
    {b : ℝ → Ω → ℝ} (hb : Measurable (Function.uncurry b)) {C : ℝ}
    (hbound : ∀ t ω, ‖b t ω‖ ≤ C) (u v : ℝ) (ω : Ω) :
    IntervalIntegrable (fun t => b t ω) volume u v := by
  rw [intervalIntegrable_iff]
  let : IsFiniteMeasure (volume.restrict (uIoc u v)) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min u v) (max u v)))
    infer_instance
  exact Integrable.of_bound
    (hb.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable C
    (Eventually.of_forall (fun t => hbound t ω))

theorem innovation_sub {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (B : ℝ → Ω → ℝ) {b : ℝ → Ω → ℝ}
    (hb : Measurable (Function.uncurry b)) {C : ℝ}
    (hbound : ∀ t ω, ‖b t ω‖ ≤ C) (u v : ℝ) (ω : Ω) :
    innovation X B b v ω - innovation X B b u ω =
      (v - u) * X ω + (B v ω - B u ω) - ∫ t in u..v, b t ω := by
  have hi := intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_field hb hbound 0 v ω)
    (intervalIntegrable_field hb hbound 0 u ω)
  simp only [innovation]
  rw [← hi]
  ring

theorem integrable_innovation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {X : Ω → ℝ} (hX : Integrable X P)
    {B b : ℝ → Ω → ℝ} (hB : ∀ t, Integrable (B t) P)
    (hb : Measurable (Function.uncurry b)) {C : ℝ}
    (hbound : ∀ t ω, ‖b t ω‖ ≤ C) (t : ℝ) :
    Integrable (innovation X B b t) P :=
  ((hX.const_mul t).add (hB t)).sub (integrable_integrated_field P hb hbound 0 t)

theorem integral_weighted_eq_zero_of_condExp {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {D : Ω → ℝ} (hD : Integrable D P)
    (hzero : P[D | m] =ᵐ[P] (fun _ => (0 : ℝ)))
    {K : Ω → ℂ} (hK : StronglyMeasurable[m] K) {C : ℝ}
    (hKbound : ∀ᵐ ω ∂P, ‖K ω‖ ≤ C) :
    (∫ ω, K ω * (D ω : ℂ) ∂P) = 0 := by
  let M : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := (ContinuousLinearMap.lsmul ℝ ℝ).flip
  have hprod : Integrable (fun ω => M (K ω) (D ω)) P :=
    M.integrable_of_bilin_of_bdd_left C (hK.mono hm).aestronglyMeasurable hKbound hD
  have hpull := condExp_bilin_of_stronglyMeasurable_left M hK hprod hD
  have hz : P[(fun ω => M (K ω) (D ω)) | m] =ᵐ[P] (fun _ => (0 : ℂ)) := by
    filter_upwards [hpull, hzero] with ω hω hzω
    simpa only [hzω, map_zero] using hω
  have hi : (∫ ω, M (K ω) (D ω) ∂P) = 0 := by
    rw [← integral_condExp hm]
    simpa only [integral_zero] using integral_congr_ae hz
  simpa only [M, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
    Complex.real_smul, mul_comm] using hi

theorem integral_integrated_posterior_nnreal {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] (ℱ : Filtration ℝ≥0 mΩ)
    {X : Ω → ℝ} (hX : Integrable X P) {b : ℝ → Ω → ℝ}
    (hb : Measurable (Function.uncurry b)) {C : ℝ}
    (hbound : ∀ t ω, ‖b t ω‖ ≤ C)
    (hposterior : ∀ t : ℝ≥0, b t =ᵐ[P] P[X | ℱ t])
    {u v : ℝ≥0} (huv : u ≤ v) {A : Set Ω} (hA : MeasurableSet[ℱ u] A) :
    (∫ ω in A, (∫ t in (u : ℝ)..v, b t ω) ∂P) =
      ((v : ℝ) - u) * ∫ ω in A, X ω ∂P := by
  apply integral_integrated_drift P hb hbound u v A
  intro t ht
  rw [uIoc_of_le (show (u : ℝ) ≤ v from huv)] at ht
  let t' : ℝ≥0 := ⟨t, u.2.trans ht.1.le⟩
  have hut : u ≤ t' := ht.1.le
  calc
    (∫ ω in A, b t ω ∂P) = ∫ ω in A, P[X | ℱ t'] ω ∂P :=
      integral_congr_ae (ae_restrict_of_ae (hposterior t'))
    _ = ∫ ω in A, X ω ∂P :=
      setIntegral_condExp (ℱ.le t') hX ((ℱ.mono hut) A hA)

theorem martingale_nnInnovation {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] (ℱ : Filtration ℝ≥0 mΩ)
    {X : Ω → ℝ} (hX : Integrable X P)
    {B : ℝ≥0 → Ω → ℝ} {b : ℝ → Ω → ℝ}
    (hB : ∀ t, Integrable (B t) P)
    (hb : Measurable (Function.uncurry b)) {C : ℝ}
    (hbound : ∀ t ω, ‖b t ω‖ ≤ C)
    (hposterior : ∀ t : ℝ≥0, b t =ᵐ[P] P[X | ℱ t])
    (hadapted : StronglyAdapted ℱ (nnInnovation X B b))
    (hnoise : ∀ u v, u ≤ v → ∀ A : Set Ω, MeasurableSet[ℱ u] A →
      (∫ ω in A, (B v ω - B u ω) ∂P) = 0) :
    Martingale (nnInnovation X B b) ℱ P := by
  have hint (t : ℝ≥0) : Integrable (nnInnovation X B b t) P :=
    integrable_innovation P hX (fun s => hB s.toNNReal) hb hbound t
  refine ⟨hadapted, fun u v huv => ?_⟩
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le u) (hint v)
  · intro A _ _
    exact (hint u).integrableOn
  · intro A hA _
    have hid (ω : Ω) :
        nnInnovation X B b v ω - nnInnovation X B b u ω =
          ((v : ℝ) - u) * X ω + (B v ω - B u ω) -
            ∫ t in (u : ℝ)..v, b t ω := by
      simpa only [nnInnovation, Real.toNNReal_coe] using
        innovation_sub X (fun s => B s.toNNReal) hb hbound u v ω
    have hs : Integrable (fun ω => ((v : ℝ) - u) * X ω) (P.restrict A) :=
      (hX.const_mul ((v : ℝ) - u)).integrableOn
    have hn : Integrable (fun ω => B v ω - B u ω) (P.restrict A) := by
      simpa only [IntegrableOn, Pi.sub_def] using
        ((hB v).sub (hB u)).integrableOn (s := A)
    have hsum : Integrable
        (fun ω => ((v : ℝ) - u) * X ω + (B v ω - B u ω)) (P.restrict A) := by
      simpa only [Pi.add_def] using hs.add hn
    have hzero : (∫ ω in A,
        (nnInnovation X B b v ω - nnInnovation X B b u ω) ∂P) = 0 := by
      simp_rw [hid]
      rw [integral_sub hsum
        (integrable_integrated_field P hb hbound u v).integrableOn]
      rw [integral_add hs hn, integral_const_mul, hnoise u v huv A hA,
        integral_integrated_posterior_nnreal P ℱ hX hb hbound hposterior huv hA]
      ring
    rw [integral_sub (hint v).integrableOn (hint u).integrableOn] at hzero
    linarith
  · exact (hadapted u).aestronglyMeasurable

theorem integral_weighted_martingale_sub_eq_zero
    {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] (ℱ : Filtration ι mΩ)
    {M : ι → Ω → ℝ} (hM : Martingale M ℱ P)
    {u v : ι} (huv : u ≤ v) {K : Ω → ℂ}
    (hK : StronglyMeasurable[ℱ u] K) {C : ℝ}
    (hKbound : ∀ᵐ ω ∂P, ‖K ω‖ ≤ C) :
    (∫ ω, K ω * ((M v ω - M u ω : ℝ) : ℂ) ∂P) = 0 := by
  have hD : Integrable (fun ω => M v ω - M u ω) P := by
    simpa only [Pi.sub_def] using (hM.integrable v).sub (hM.integrable u)
  apply integral_weighted_eq_zero_of_condExp P (ℱ.le u) hD _ hK hKbound
  have hsub := condExp_sub (hM.integrable v) (hM.integrable u) (ℱ u)
  filter_upwards [hsub, hM.condExp_ae_eq huv, hM.condExp_ae_eq (le_refl u)]
    with ω hω hvω huω
  simpa only [Pi.sub_def, hvω, huω, sub_self] using hω

theorem innovation_sub_noise_bound {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (B : ℝ → Ω → ℝ) {b : ℝ → Ω → ℝ}
    (hb : Measurable (Function.uncurry b))
    (hXbound : ∀ ω, X ω ∈ Icc (0 : ℝ) 1)
    (hbbound : ∀ t ω, b t ω ∈ Icc (0 : ℝ) 1)
    (u v : ℝ) (ω : Ω) :
    ‖innovation X B b v ω - innovation X B b u ω - (B v ω - B u ω)‖ ≤
      |v - u| := by
  have hbound : ∀ t ω, ‖b t ω‖ ≤ 1 := by
    intro t ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hbbound t ω).1]
    exact (hbbound t ω).2
  rw [innovation_sub X B hb hbound u v]
  have hid : (v - u) * X ω + (B v ω - B u ω) -
      (∫ t in u..v, b t ω) - (B v ω - B u ω) =
        ∫ t in u..v, (X ω - b t ω) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegrable_field hb hbound u v ω)]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hid]
  have hdiff : ∀ t ∈ uIoc u v, ‖X ω - b t ω‖ ≤ 1 := by
    intro t _
    rw [Real.norm_eq_abs, abs_le]
    have hx := hXbound ω
    have ht := hbbound t ω
    constructor <;> linarith [hx.1, hx.2, ht.1, ht.2]
  simpa only [one_mul] using intervalIntegral.norm_integral_le_of_norm_le_const hdiff

end Problem336.Innovation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_InnovationAdapted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped NNReal Topology

namespace Problem336.Innovation

theorem measurable_stopped_observation {ι Ω : Type*} {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℝ≥0 mΩ) (Y : ℝ≥0 → Ω → ι → ℝ)
    (hcont : ∀ ω i, Continuous (fun t => Y t ω i))
    (hadapted : ∀ t i, Measurable[ℱ t] (fun ω => Y t ω i)) (T : ℝ≥0) :
    Measurable[(borel ℝ).prod (ℱ T)]
      (fun q : ℝ × Ω => Y (min q.1.toNNReal T) q.2) := by
  let : MeasurableSpace Ω := ℱ T
  apply Measurable.of_eval
  intro i
  apply measurable_uncurry_of_continuous_of_measurable (m := ℱ T)
    (u := fun s : ℝ => fun ω : Ω => Y (min s.toNNReal T) ω i)
  · intro ω
    exact (hcont ω i).comp (by fun_prop)
  · intro s
    exact (hadapted (min s.toNNReal T) i).mono
      (ℱ.mono (min_le_right _ _)) le_rfl

theorem stronglyMeasurable_integrated_observation_drift
    {ι Ω : Type*} {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℝ≥0 mΩ) (Y : ℝ≥0 → Ω → ι → ℝ)
    (hcont : ∀ ω i, Continuous (fun t => Y t ω i))
    (hadapted : ∀ t i, Measurable[ℱ t] (fun ω => Y t ω i))
    (b : ℝ≥0 → (ι → ℝ) → ℝ) (hb : Measurable (Function.uncurry b))
    (T : ℝ≥0) :
    StronglyMeasurable[ℱ T]
      (fun ω => ∫ s in (0 : ℝ)..T, b s.toNNReal (Y s.toNNReal ω)) := by
  let : MeasurableSpace Ω := ℱ T
  have htime : Measurable[(borel ℝ).prod (ℱ T)]
      (fun q : ℝ × Ω => min q.1.toNNReal T) := by
    exact (show Continuous (fun s : ℝ => min s.toNNReal T) by fun_prop).measurable.comp
      measurable_fst
  have hfield := measurable_stopped_observation ℱ Y hcont hadapted T
  have hstop : Measurable[(borel ℝ).prod (ℱ T)]
      (fun q : ℝ × Ω => b (min q.1.toNNReal T) (Y (min q.1.toNNReal T) q.2)) :=
    hb.comp (htime.prodMk hfield)
  have hint : StronglyMeasurable[ℱ T]
      (fun ω => ∫ s in Ioc (0 : ℝ) (T : ℝ),
        b (min s.toNNReal T) (Y (min s.toNNReal T) ω)) :=
    hstop.stronglyMeasurable.integral_prod_left'
  convert hint using 1
  funext ω
  calc
    (∫ s in (0 : ℝ)..T, b s.toNNReal (Y s.toNNReal ω)) =
        ∫ s in Ioc (0 : ℝ) (T : ℝ), b s.toNNReal (Y s.toNNReal ω) :=
      intervalIntegral.integral_of_le T.2
    _ = ∫ s in Ioc (0 : ℝ) (T : ℝ),
        b (min s.toNNReal T) (Y (min s.toNNReal T) ω) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      dsimp only
      rw [min_eq_left (Real.toNNReal_le_iff_le_coe.mpr hs.2)]

theorem stronglyAdapted_observation_innovation
    {ι Ω : Type*} {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℝ≥0 mΩ) (Y : ℝ≥0 → Ω → ι → ℝ)
    (hcont : ∀ ω i, Continuous (fun t => Y t ω i))
    (hadapted : ∀ t i, Measurable[ℱ t] (fun ω => Y t ω i))
    (b : ℝ≥0 → (ι → ℝ) → ℝ) (hb : Measurable (Function.uncurry b))
    (i : ι) :
    StronglyAdapted ℱ (fun t ω => Y t ω i -
      ∫ s in (0 : ℝ)..t, b s.toNNReal (Y s.toNNReal ω)) := by
  intro t
  exact (hadapted t i).stronglyMeasurable.sub
    (stronglyMeasurable_integrated_observation_drift ℱ Y hcont hadapted b hb t)

theorem measurable_observation_field {ι Ω : Type*} {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℝ≥0 mΩ) (Y : ℝ≥0 → Ω → ι → ℝ)
    (hcont : ∀ ω i, Continuous (fun t => Y t ω i))
    (hadapted : ∀ t i, Measurable[ℱ t] (fun ω => Y t ω i)) :
    Measurable (fun q : ℝ × Ω => Y q.1.toNNReal q.2) := by
  apply Measurable.of_eval
  intro i
  apply measurable_uncurry_of_continuous_of_measurable
    (u := fun s : ℝ => fun ω : Ω => Y s.toNNReal ω i)
  · intro ω
    exact (hcont ω i).comp (by fun_prop)
  · intro s
    exact (hadapted s.toNNReal i).mono (ℱ.le _) le_rfl

theorem martingale_borel_observation
    {ι Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] (ℱ : Filtration ℝ≥0 mΩ)
    (Y : ℝ≥0 → Ω → ι → ℝ)
    (hcont : ∀ ω i, Continuous (fun t => Y t ω i))
    (hadapted : ∀ t i, Measurable[ℱ t] (fun ω => Y t ω i))
    (i : ι) (X : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hobs : ∀ t ω, Y t ω i = (t : ℝ) * X ω + B t ω)
    (hX : Integrable X P) (hB : ∀ t, Integrable (B t) P)
    (b : ℝ≥0 → (ι → ℝ) → ℝ) (hb : Measurable (Function.uncurry b))
    {C : ℝ} (hbound : ∀ t y, ‖b t y‖ ≤ C)
    (hposterior : ∀ t : ℝ≥0, (fun ω => b t (Y t ω)) =ᵐ[P] P[X | ℱ t])
    (hnoise : ∀ u v, u ≤ v → ∀ A : Set Ω, MeasurableSet[ℱ u] A →
      (∫ ω in A, (B v ω - B u ω) ∂P) = 0) :
    Martingale (fun t ω => Y t ω i -
      ∫ s in (0 : ℝ)..t, b s.toNNReal (Y s.toNNReal ω)) ℱ P := by
  let bt : ℝ → Ω → ℝ := fun s ω => b s.toNNReal (Y s.toNNReal ω)
  have hbt : Measurable (Function.uncurry bt) :=
    hb.comp ((show Measurable (fun q : ℝ × Ω => q.1.toNNReal) by fun_prop).prodMk
      (measurable_observation_field ℱ Y hcont hadapted))
  have hbnd : ∀ t ω, ‖bt t ω‖ ≤ C := fun t ω => hbound _ _
  have hpost : ∀ t : ℝ≥0, bt t =ᵐ[P] P[X | ℱ t] := by
    intro t
    simpa only [bt, Real.toNNReal_coe] using hposterior t
  have heq : nnInnovation X B bt = (fun t ω => Y t ω i -
      ∫ s in (0 : ℝ)..t, b s.toNNReal (Y s.toNNReal ω)) := by
    funext t ω
    rw [nnInnovation_apply, hobs]
  have hstrong : StronglyAdapted ℱ (nnInnovation X B bt) := by
    rw [heq]
    exact stronglyAdapted_observation_innovation ℱ Y hcont hadapted b hb i
  rw [← heq]
  exact martingale_nnInnovation P ℱ hX hB hbt hbnd hpost hstrong hnoise

end Problem336.Innovation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_ObservedBrownianMartingale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace Problem336.Innovation

theorem measurable_observationHistoryFiltration {I Ω : Type*}
    {mΩ : MeasurableSpace Ω} (Y : ℝ≥0 → Ω → I → ℝ)
    (hY : ∀ t i, Measurable (fun ω => Y t ω i)) (t : ℝ≥0) (i : I) :
    Measurable[observationHistoryFiltration (mΩ := mΩ) Y hY t] (fun ω => Y t ω i) := by
  exact (measurable_pi_apply ((i, ⟨t, by simp⟩) : I × Iic t)).comp
    (comap_measurable (fun ω (p : I × Iic t) => Y p.2 ω p.1))

theorem martingale_nnInnovation_of_brownian_family
    {I Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (Y : ℝ≥0 → Ω → I → ℝ)
    (hYmeas : ∀ t i, Measurable (fun ω => Y t ω i))
    (hYcont : ∀ ω i, Continuous (fun t => Y t ω i))
    (B : I → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hBm : ∀ i t, Measurable (B i t))
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    (X : Ω → I → ℝ) (hX : Measurable X)
    (hXB : IndepFun X (fun ω i t => B i t ω) P)
    (hobs : ∀ t ω i, Y t ω i = (t : ℝ) * X ω i + B i t ω)
    (i : I) (hXbound : ∀ ω, X ω i ∈ Icc (0 : ℝ) 1)
    (b : ℝ≥0 → (I → ℝ) → ℝ) (hb : Measurable (Function.uncurry b))
    {C : ℝ} (hbound : ∀ t y, ‖b t y‖ ≤ C)
    (hposterior : ∀ t : ℝ≥0, (fun ω => b t (Y t ω)) =ᵐ[P]
      P[(fun ω => X ω i) | observationHistoryFiltration Y hYmeas t]) :
    Martingale (nnInnovation (fun ω => X ω i) (B i)
      (fun s ω => b s.toNNReal (Y s.toNNReal ω)))
      (observationHistoryFiltration Y hYmeas) P := by
  classical
  let : IsProbabilityMeasure P := hI.isProbabilityMeasure
  have hXi : Integrable (fun ω => X ω i) P :=
    Integrable.of_bound ((measurable_pi_apply i).comp hX).aestronglyMeasurable 1 (by
      apply Filter.Eventually.of_forall
      intro ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hXbound ω).1]
      exact (hXbound ω).2)
  have hnoise : ∀ u v : ℝ≥0, u ≤ v → ∀ A : Set Ω,
      MeasurableSet[observationHistoryFiltration Y hYmeas u] A →
      (∫ ω in A, (B i v ω - B i u ω) ∂P) = 0 := by
    intro u v huv A hA
    have hA' : MeasurableSet[MeasurableSpace.comap
        (fun ω (p : I × Iic u) => (p.2 : ℝ≥0) * X ω p.1 + B p.1 p.2 ω)
        inferInstance] A := by
      change MeasurableSet[MeasurableSpace.comap
        (fun ω (p : I × Iic u) => Y p.2 ω p.1) inferInstance] A at hA
      have hhist : (fun ω (p : I × Iic u) => Y p.2 ω p.1) =
          (fun ω (p : I × Iic u) => (p.2 : ℝ≥0) * X ω p.1 + B p.1 p.2 ω) := by
        funext ω p
        exact hobs p.2 ω p.1
      rw [hhist] at hA
      exact hA
    have hz := BrownianFamilyPast.setIntegral_weighted_increment_observation_eq_zero
      hB hBm hI hX hXB {i} (fun _ => (1 : ℝ)) u (v - u) hA'
    simpa only [Finset.sum_singleton, one_mul, add_tsub_cancel_of_le huv] using hz
  have heq : nnInnovation (fun ω => X ω i) (B i)
      (fun s ω => b s.toNNReal (Y s.toNNReal ω)) =
      (fun t ω => Y t ω i -
        ∫ s in (0 : ℝ)..t, b s.toNNReal (Y s.toNNReal ω)) := by
    funext t ω
    rw [nnInnovation_apply, hobs]
  rw [heq]
  exact martingale_borel_observation P (observationHistoryFiltration Y hYmeas)
    Y hYcont (measurable_observationHistoryFiltration Y hYmeas) i
    (fun ω => X ω i) (B i) (fun t ω => hobs t ω i) hXi
    (fun t => (hB i).integrable_eval t) b hb hbound hposterior hnoise

end Problem336.Innovation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CanonicalPosteriorMartingale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336.CanonicalPosteriorMartingale

theorem martingale_nnInnovation
    {I Ω : Type*} [Countable I] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ProbabilityMeasure (I → Bool))
    (X : Ω → I → Bool) (hX : Measurable X)
    (hprior : P.map X = (μ : Measure (I → Bool)))
    (B : I → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hBm : ∀ i t, Measurable (B i t))
    (hBcont : ∀ ω i, Continuous (fun t => B i t ω))
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    (hXB : IndepFun X (fun ω (p : I × ℝ≥0) => B p.1 p.2 ω) P)
    (S : I → ℕ → Finset I) (e : I)
    (hS : Monotone (S e)) (hcover : ∀ i, ∃ n, i ∈ S e n) :
    Martingale (Innovation.nnInnovation (fun ω => TiltLimit.bit (X ω e)) (B e)
      (fun s ω => PosteriorDrift.drift μ S s
        (observation X B s.toNNReal ω) e))
      (Innovation.observationHistoryFiltration (observation X B)
        (measurable_observation X hX B hBm)) P := by
  let R : (I → Bool) → I → ℝ := fun x i => TiltLimit.bit (x i)
  have hR : Measurable R := Measurable.of_eval (fun i =>
    TiltLimit.continuous_bit.measurable.comp (measurable_pi_apply i))
  have hXI : IndepFun (R ∘ X) (fun ω i t => B i t ω) P :=
    hXB.comp hR (Measurable.of_eval (fun i =>
      Measurable.of_eval (fun t => measurable_pi_apply (i, t))))
  have hYcont : ∀ ω i, Continuous (fun t => observation X B t ω i) := by
    intro ω i
    exact (continuous_subtype_val.mul continuous_const).add (hBcont ω i)
  have hbound : ∀ t y,
      ‖PosteriorDrift.drift μ S (t : ℝ≥0) y e‖ ≤ (1 : ℝ) := by
    intro t y
    have h := PosteriorDrift.drift_mem_Icc μ S t y e
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2
  have hb : Measurable (Function.uncurry
      (fun (t : ℝ≥0) y => PosteriorDrift.drift μ S t y e)) := by
    let f : ℝ≥0 × (I → ℝ) → ℝ × (I → ℝ) :=
      fun p => ((p.1 : ℝ), p.2)
    have hf : Measurable f :=
      (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
    exact (PosteriorDrift.measurable_drift_coordinate μ S e).comp (f := f) hf
  have hM := Innovation.martingale_nnInnovation_of_brownian_family P
    (observation X B) (measurable_observation X hX B hBm) hYcont
    B hB hBm hI (R ∘ X) (hR.comp hX) hXI (fun _ _ _ => rfl) e
    (fun ω => by cases h : X ω e <;> simp [R, TiltLimit.bit, h])
    (fun t y => PosteriorDrift.drift μ S t y e) hb hbound
    (fun t => Observation.drift_eq_condExp_brownian_history_all_times
      P μ X hX hprior B hB hI hBm hXB S e hS hcover t)
  have heq : Innovation.nnInnovation (fun ω => TiltLimit.bit (X ω e)) (B e)
      (fun s ω => PosteriorDrift.drift μ S (s.toNNReal : ℝ)
        (observation X B s.toNNReal ω) e) =
      Innovation.nnInnovation (fun ω => TiltLimit.bit (X ω e)) (B e)
      (fun s ω => PosteriorDrift.drift μ S s
        (observation X B s.toNNReal ω) e) := by
    funext t ω
    simp only [Innovation.nnInnovation_apply]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have ht : (0 : ℝ) ≤ (t : ℝ) := t.2
    have hs0 : 0 ≤ s := by
      simpa only [min_eq_left ht] using hs.1
    dsimp only
    rw [Real.coe_toNNReal s hs0]
  change Martingale (Innovation.nnInnovation (fun ω => TiltLimit.bit (X ω e)) (B e)
      (fun s ω => PosteriorDrift.drift μ S (s.toNNReal : ℝ)
        (observation X B s.toNNReal ω) e)) _ P at hM
  rw [heq] at hM
  exact hM

end Problem336.CanonicalPosteriorMartingale

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_GaussianMomentScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem336

theorem standardGaussian_sqrt_hasLaw (v : ℝ≥0) :
    HasLaw (fun z : ℝ => Real.sqrt v * z) (gaussianReal 0 v) (gaussianReal 0 1) := by
  have h := gaussianReal_const_mul
    (HasLaw.id (μ := gaussianReal 0 1)) (Real.sqrt v)
  have hv : (⟨(Real.sqrt (v : ℝ)) ^ 2, sq_nonneg _⟩ : ℝ≥0) = v := by
    apply NNReal.coe_injective
    exact Real.sq_sqrt v.coe_nonneg
  simp only [mul_zero, mul_one, id_eq] at h
  convert h using 1
  congr 1
  exact hv.symm

theorem gaussian_absolute_moment_scaling (v : ℝ≥0) (k : ℕ) :
    (∫ z : ℝ, |z| ^ k ∂gaussianReal 0 v) =
      (Real.sqrt (v : ℝ)) ^ k * (∫ z : ℝ, |z| ^ k ∂gaussianReal 0 1) := by
  rw [← (standardGaussian_sqrt_hasLaw v).integral_comp (f := fun z : ℝ => |z| ^ k)
    (by fun_prop)]
  simp only [Function.comp_apply, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  exact integral_const_mul _ _

theorem standardGaussian_absolute_first_moment_le_one :
    (∫ z : ℝ, |z| ∂gaussianReal 0 1) ≤ 1 := by
  have hint : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num) |>.abs
  have hsint : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 1) := by
    simpa only [id_eq, Real.norm_eq_abs, sq_abs] using
      (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_norm_pow' (p := 2)
  have hsq : (∫ z : ℝ, z ^ 2 ∂gaussianReal 0 1) = 1 := by
    have h := variance_id_gaussianReal (μ := 0) (v := 1)
    simp only [variance_eq_integral aemeasurable_id, id_eq, integral_id_gaussianReal, sub_zero] at h
    simpa only [id_eq, sub_zero, NNReal.coe_one] using h
  have hle := integral_mono (hint.const_mul 2) (hsint.add (integrable_const 1))
    (fun z : ℝ => show 2 * |z| ≤ z ^ 2 + 1 by nlinarith [sq_nonneg (|z| - 1), sq_abs z])
  simp only [Pi.add_apply] at hle
  rw [integral_const_mul, integral_add hsint (integrable_const 1), hsq, integral_const] at hle
  norm_num at hle
  linarith

theorem gaussian_absolute_first_moment_le_sqrt (v : ℝ≥0) :
    (∫ z : ℝ, |z| ∂gaussianReal 0 v) ≤ Real.sqrt v := by
  have h := gaussian_absolute_moment_scaling v 1
  simp only [pow_one] at h
  rw [h]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left standardGaussian_absolute_first_moment_le_one (Real.sqrt_nonneg _)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {Q : Ω → ℝ} {v : ℝ≥0}

theorem gaussian_hasLaw_integrable_abs_pow (hQ : HasLaw Q (gaussianReal 0 v) P) (k : ℕ) :
    Integrable (fun ω => |Q ω| ^ k) P := by
  let := hQ.isProbabilityMeasure
  simpa only [Real.norm_eq_abs] using
    (hQ.hasGaussianLaw.memLp (p := (k : ℝ≥0∞)) (by simp)).integrable_norm_pow' (p := k)

theorem gaussian_hasLaw_absolute_moment (hQ : HasLaw Q (gaussianReal 0 v) P) (k : ℕ) :
    (∫ ω, |Q ω| ^ k ∂P) =
      (Real.sqrt (v : ℝ)) ^ k * (∫ z : ℝ, |z| ^ k ∂gaussianReal 0 1) := by
  calc
    (∫ ω, |Q ω| ^ k ∂P) = (∫ z : ℝ, |z| ^ k ∂gaussianReal 0 v) :=
      hQ.integral_comp (f := fun z : ℝ => |z| ^ k) (by fun_prop)
    _ = _ := gaussian_absolute_moment_scaling v k

theorem gaussian_hasLaw_second_moment (hQ : HasLaw Q (gaussianReal 0 v) P) :
    (∫ ω, (Q ω) ^ 2 ∂P) = (v : ℝ) := by
  have h := variance_id_gaussianReal (μ := 0) (v := v)
  simp only [variance_eq_integral aemeasurable_id, id_eq, integral_id_gaussianReal, sub_zero] at h
  calc
    (∫ ω, (Q ω) ^ 2 ∂P) = (∫ z : ℝ, z ^ 2 ∂gaussianReal 0 v) :=
      hQ.integral_comp (f := fun z : ℝ => z ^ 2) (by fun_prop)
    _ = _ := h

theorem gaussian_hasLaw_absolute_first_moment_le (hQ : HasLaw Q (gaussianReal 0 v) P) :
    (∫ ω, |Q ω| ∂P) ≤ Real.sqrt v := by
  calc
    (∫ ω, |Q ω| ∂P) = (∫ z : ℝ, |z| ∂gaussianReal 0 v) :=
      hQ.integral_comp (f := fun z : ℝ => |z|) (by fun_prop)
    _ ≤ _ := gaussian_absolute_first_moment_le_sqrt v

theorem gaussian_independent_weighted_second_moment
    (hQ : HasLaw Q (gaussianReal 0 v) P) {K : Ω → ℂ}
    (hK : AEMeasurable K P) (hind : IndepFun K Q P) :
    (∫ ω, K ω * (Q ω : ℂ) ^ 2 ∂P) =
      (∫ ω, K ω ∂P) * (v : ℂ) := by
  have hi := hind.integral_fun_comp_mul_comp hK hQ.aemeasurable
    (f := id) (g := fun z : ℝ => (z : ℂ) ^ 2) (by fun_prop) (by fun_prop)
  have hmoment : (∫ ω, (Q ω : ℂ) ^ 2 ∂P) = (v : ℂ) := by
    simp only [← Complex.ofReal_pow, integral_complex_ofReal,
      gaussian_hasLaw_second_moment hQ]
  simpa only [id_eq, hmoment] using hi

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_GaussianSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace Problem336

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  {P : Measure Ω} {Q : ι → Ω → ℝ} {v : ι → ℝ≥0}

theorem independent_centered_gaussian_sum_hasLaw
    (hQ : ∀ i, HasLaw (Q i) (gaussianReal 0 (v i)) P) (hind : iIndepFun Q P) :
    HasLaw (fun ω => ∑ i, Q i ω) (gaussianReal 0 (∑ i, v i)) P := by
  have hG : HasGaussianLaw (fun ω => ∑ i, Q i ω) P :=
    iIndepFun.hasGaussianLaw_fun_sum (fun i => (hQ i).hasGaussianLaw) hind
  have hmean : (∫ ω, ∑ i, Q i ω ∂P) = 0 := by
    rw [integral_finsetSum _ (fun i _ => (hQ i).hasGaussianLaw.integrable)]
    simp only [fun i => (hQ i).integral_eq, integral_id_gaussianReal, Finset.sum_const_zero]
  have hvar : Var[fun ω => ∑ i, Q i ω; P] = ∑ i, (v i : ℝ) := by
    have h := IndepFun.variance_sum (s := Finset.univ)
      (fun i _ => (hQ i).hasGaussianLaw.memLp_two)
      (fun i _ j _ hij => hind.indepFun hij)
    have heq : (fun ω => ∑ i, Q i ω) = ∑ i, Q i := by
      funext ω
      simp only [Finset.sum_apply]
    rw [heq]
    simpa only [fun i => (hQ i).variance_eq, variance_id_gaussianReal] using h
  refine ⟨hG.aemeasurable, ?_⟩
  rw [hG.map_eq_gaussianReal, hmean, hvar]
  congr 1
  simp only [← NNReal.coe_sum, Real.toNNReal_coe]

theorem independent_weighted_gaussian_sum_hasLaw
    (hQ : ∀ i, HasLaw (Q i) (gaussianReal 0 (v i)) P)
    (hind : iIndepFun Q P) (θ : ι → ℝ) :
    HasLaw (fun ω => ∑ i, θ i * Q i ω)
      (gaussianReal 0 (∑ i, NNReal.mk ((θ i) ^ 2) (sq_nonneg _) * v i)) P := by
  apply independent_centered_gaussian_sum_hasLaw
  · intro i
    simpa only [mul_zero] using gaussianReal_const_mul (hQ i) (θ i)
  · exact hind.comp (fun i z => θ i * z) (by fun_prop)

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_InnovationMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem336.InnovationMoments

theorem abs_square_perturbation_le (q r a : ℝ) (ha : 0 ≤ a) (hr : |r| ≤ a) :
    |(q + r) ^ 2 - q ^ 2| ≤ 2 * a * |q| + a ^ 2 := by
  have hqr : |q * r| ≤ |q| * a := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hr (abs_nonneg q)
  have hqr' := abs_le.mp hqr
  have hr2 : r ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_abs r, mul_nonneg (sub_nonneg.mpr hr) (add_nonneg (abs_nonneg r) ha)]
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg r]

theorem abs_cube_perturbation_le (q r a : ℝ) (ha : 0 ≤ a) (hr : |r| ≤ a) :
    |q + r| ^ 3 ≤ 4 * (|q| ^ 3 + a ^ 3) := by
  have hsum : |q + r| ≤ |q| + a := (abs_add_le q r).trans (add_le_add le_rfl hr)
  have hcube := pow_le_pow_left₀ (abs_nonneg (q + r)) hsum 3
  have hexpand := mul_nonneg (add_nonneg (abs_nonneg q) ha) (sq_nonneg (|q| - a))
  nlinarith

theorem square_perturbation_le (q r a : ℝ) (ha : 0 ≤ a) (hr : |r| ≤ a) :
    (q + r) ^ 2 ≤ 2 * (q ^ 2 + a ^ 2) := by
  have hr2 : r ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_abs r, mul_nonneg (sub_nonneg.mpr hr) (add_nonneg (abs_nonneg r) ha)]
  nlinarith [sq_nonneg (q - r)]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {Q R : Ω → ℝ} {a : ℝ}

theorem integrable_square_add_of_bounded
    (hQ : AEStronglyMeasurable Q μ) (hR : AEStronglyMeasurable R μ)
    (hQ2 : Integrable (fun ω => Q ω ^ 2) μ)
    (ha : 0 ≤ a) (hRbound : ∀ᵐ ω ∂μ, |R ω| ≤ a) :
    Integrable (fun ω => (Q ω + R ω) ^ 2) μ := by
  apply ((hQ2.add (integrable_const (a ^ 2))).const_mul 2).mono'
    ((hQ.add hR).pow 2)
  filter_upwards [hRbound] with ω hω
  change |(Q ω + R ω) ^ 2| ≤ 2 * (Q ω ^ 2 + a ^ 2)
  rw [abs_of_nonneg (sq_nonneg _)]
  exact square_perturbation_le (Q ω) (R ω) a ha hω

theorem integrable_abs_cube_add_of_bounded
    (hQ : AEStronglyMeasurable Q μ) (hR : AEStronglyMeasurable R μ)
    (hQ3 : Integrable (fun ω => |Q ω| ^ 3) μ)
    (ha : 0 ≤ a) (hRbound : ∀ᵐ ω ∂μ, |R ω| ≤ a) :
    Integrable (fun ω => |Q ω + R ω| ^ 3) μ := by
  apply ((hQ3.add (integrable_const (a ^ 3))).const_mul 4).mono'
    (by
      apply ((hQ.add hR).norm.pow 3).congr
      filter_upwards [] with ω
      simp only [Pi.pow_apply, Pi.add_apply, Real.norm_eq_abs])
  filter_upwards [hRbound] with ω hω
  change |(|Q ω + R ω| ^ 3)| ≤ 4 * (|Q ω| ^ 3 + a ^ 3)
  rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
  exact abs_cube_perturbation_le (Q ω) (R ω) a ha hω

theorem integral_abs_cube_perturbation_le
    (hQ : AEStronglyMeasurable Q μ) (hR : AEStronglyMeasurable R μ)
    (hQ3 : Integrable (fun ω => |Q ω| ^ 3) μ)
    (ha : 0 ≤ a) (hRbound : ∀ᵐ ω ∂μ, |R ω| ≤ a) :
    (∫ ω, |Q ω + R ω| ^ 3 ∂μ) ≤
      4 * ((∫ ω, |Q ω| ^ 3 ∂μ) + a ^ 3 * μ.real Set.univ) := by
  have hD3 := integrable_abs_cube_add_of_bounded hQ hR hQ3 ha hRbound
  have hbound : Integrable (fun ω => 4 * (|Q ω| ^ 3 + a ^ 3)) μ :=
    (hQ3.add (integrable_const _)).const_mul _
  calc
    _ ≤ ∫ ω, 4 * (|Q ω| ^ 3 + a ^ 3) ∂μ := by
      apply integral_mono_ae hD3 hbound
      filter_upwards [hRbound] with ω hω
      exact abs_cube_perturbation_le (Q ω) (R ω) a ha hω
    _ = _ := by
      rw [integral_const_mul, integral_add hQ3 (integrable_const _), integral_const]
      simp only [smul_eq_mul]
      ring

end Problem336.InnovationMoments

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_InnovationTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Problem336
namespace Innovation

theorem norm_exp_I_taylor_two (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I +
      (x : ℂ) ^ 2 / 2‖ ≤ 4 * |x| ^ 3 := by
  have hnorm : ‖(x : ℂ) * Complex.I‖ = |x| := by simp
  by_cases hx : |x| ≤ 1
  · have hb := Complex.exp_bound (x := (x : ℂ) * Complex.I)
      (by simpa only [hnorm] using hx) (n := 3) (by decide)
    have hpoly : (∑ m ∈ Finset.range 3,
        ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)) =
        1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2 := by
      norm_num [Finset.sum_range_succ, mul_pow, Complex.I_sq]
      ring
    rw [hpoly, hnorm] at hb
    norm_num at hb
    have heq : Complex.exp ((x : ℂ) * Complex.I) -
        (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2) =
        Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I +
          (x : ℂ) ^ 2 / 2 := by ring
    rw [heq] at hb
    nlinarith [pow_nonneg (abs_nonneg x) 3]
  · have hx1 : 1 ≤ |x| := (lt_of_not_ge hx).le
    have hsq : |x| ≤ |x| ^ 2 := by nlinarith [mul_nonneg (abs_nonneg x) (sub_nonneg.mpr hx1)]
    have hcube : |x| ^ 2 ≤ |x| ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg |x|) (sub_nonneg.mpr hx1)]
    calc
      ‖Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I +
          (x : ℂ) ^ 2 / 2‖
          ≤ ‖Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I‖ +
              ‖(x : ℂ) ^ 2 / 2‖ := norm_add_le _ _
      _ ≤ (‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ +
              ‖(x : ℂ) * Complex.I‖) + ‖(x : ℂ) ^ 2 / 2‖ := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ ((‖Complex.exp ((x : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖) +
              ‖(x : ℂ) * Complex.I‖) + ‖(x : ℂ) ^ 2 / 2‖ := by
        gcongr
        exact norm_sub_le _ _
      _ = 2 + |x| + |x| ^ 2 / 2 := by simp [norm_pow]; ring
      _ ≤ 4 * |x| ^ 3 := by nlinarith

theorem norm_integral_weighted_taylor {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (D : Ω → ℝ) (K : Ω → ℂ)
    (hK : ∀ᵐ ω ∂P, ‖K ω‖ ≤ 1)
    (hthird : Integrable (fun ω => |D ω| ^ 3) P) :
    ‖∫ ω, K ω * (Complex.exp ((D ω : ℂ) * Complex.I) - 1 -
        (D ω : ℂ) * Complex.I + (D ω : ℂ) ^ 2 / 2) ∂P‖ ≤
      4 * ∫ ω, |D ω| ^ 3 ∂P := by
  calc
    _ ≤ ∫ ω, 4 * |D ω| ^ 3 ∂P := by
      apply norm_integral_le_of_norm_le (hthird.const_mul 4)
      filter_upwards [hK] with ω hω
      rw [norm_mul]
      calc
        _ ≤ 1 * ‖Complex.exp ((D ω : ℂ) * Complex.I) - 1 -
            (D ω : ℂ) * Complex.I + (D ω : ℂ) ^ 2 / 2‖ :=
          mul_le_mul_of_nonneg_right hω (norm_nonneg _)
        _ ≤ 4 * |D ω| ^ 3 := by simpa using norm_exp_I_taylor_two (D ω)
    _ = _ := integral_const_mul 4 _

theorem characteristic_second_order {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (D : Ω → ℝ) (K : Ω → ℂ)
    (hK : ∀ᵐ ω ∂P, ‖K ω‖ ≤ 1)
    (hthird : Integrable (fun ω => |D ω| ^ 3) P)
    (hconst : Integrable K P)
    (hlinear : Integrable (fun ω => K ω * (D ω : ℂ)) P)
    (hquad : Integrable (fun ω => K ω * (D ω : ℂ) ^ 2) P)
    (hchar : Integrable (fun ω => K ω * Complex.exp ((D ω : ℂ) * Complex.I)) P)
    (hmean : (∫ ω, K ω * (D ω : ℂ) ∂P) = 0) :
    ‖(∫ ω, K ω * Complex.exp ((D ω : ℂ) * Complex.I) ∂P) -
        (∫ ω, K ω ∂P) + (∫ ω, K ω * (D ω : ℂ) ^ 2 ∂P) / 2‖ ≤
      4 * ∫ ω, |D ω| ^ 3 ∂P := by
  have hbound := norm_integral_weighted_taylor P D K hK hthird
  have hfun : (fun ω => K ω * (Complex.exp ((D ω : ℂ) * Complex.I) - 1 -
        (D ω : ℂ) * Complex.I + (D ω : ℂ) ^ 2 / 2)) =
      (fun ω => (K ω * Complex.exp ((D ω : ℂ) * Complex.I) - K ω) -
        (K ω * (D ω : ℂ)) * Complex.I + (K ω * (D ω : ℂ) ^ 2) / 2) := by
    funext ω
    ring
  rw [hfun] at hbound
  have hadd := integral_add ((hchar.sub hconst).sub (hlinear.mul_const Complex.I))
      (hquad.div_const 2)
  have hsub := integral_sub (hchar.sub hconst) (hlinear.mul_const Complex.I)
  have hsub' := integral_sub hchar hconst
  simp only [Pi.sub_apply] at hadd hsub hsub'
  rw [hadd, hsub, hsub', integral_mul_const, integral_div, hmean] at hbound
  simpa using hbound

theorem gaussian_approximation_of_moments {A B M : ℂ} {r d q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hB : ‖B‖ ≤ 1)
    (hTaylor : ‖A - B + M / 2‖ ≤ r)
    (hMoment : ‖M - (2 * q : ℝ) * B‖ ≤ d) :
    ‖A - (Real.exp (-q) : ℂ) * B‖ ≤ r + d / 2 + q ^ 2 := by
  have hexp : |Real.exp (-q) - 1 + q| ≤ q ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le (x := -q)
      (by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1)
    simpa [Real.norm_eq_abs, sub_neg_eq_add] using h
  have hdecomp : A - (Real.exp (-q) : ℂ) * B =
      (A - B + M / 2) - (M - (2 * q : ℝ) * B) / 2 -
        ((Real.exp (-q) - 1 + q : ℝ) : ℂ) * B := by
    push_cast
    ring
  rw [hdecomp]
  calc
    _ ≤ ‖A - B + M / 2‖ + ‖(M - (2 * q : ℝ) * B) / 2‖ +
        ‖((Real.exp (-q) - 1 + q : ℝ) : ℂ) * B‖ := by
      apply (norm_sub_le _ _).trans
      gcongr
      exact norm_sub_le _ _
    _ ≤ r + d / 2 + q ^ 2 := by
      have hdiv : ‖(M - (2 * q : ℝ) * B) / 2‖ ≤ d / 2 := by
        simpa [norm_div] using div_le_div_of_nonneg_right hMoment (by norm_num : (0 : ℝ) ≤ 2)
      have hmul : ‖((Real.exp (-q) - 1 + q : ℝ) : ℂ) * B‖ ≤ q ^ 2 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc
          _ ≤ q ^ 2 * 1 := mul_le_mul hexp hB (norm_nonneg _) (sq_nonneg _)
          _ = q ^ 2 := mul_one _
      exact add_le_add (add_le_add hTaylor hdiv) hmul

theorem weighted_characteristic_gaussian_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Ω → ℝ) (K : Ω → ℂ)
    (hKmeas : AEStronglyMeasurable K P) (hK : ∀ᵐ ω ∂P, ‖K ω‖ ≤ 1)
    (hfirst : Integrable D P) (hsecond : Integrable (fun ω => D ω ^ 2) P)
    (hthird : Integrable (fun ω => |D ω| ^ 3) P)
    (hmean : (∫ ω, K ω * (D ω : ℂ) ∂P) = 0)
    {q δ : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hsecond_est : ‖(∫ ω, K ω * (D ω : ℂ) ^ 2 ∂P) -
      (2 * q : ℝ) * (∫ ω, K ω ∂P)‖ ≤ δ) :
    ‖(∫ ω, K ω * Complex.exp ((D ω : ℂ) * Complex.I) ∂P) -
      (Real.exp (-q) : ℂ) * (∫ ω, K ω ∂P)‖ ≤
      4 * (∫ ω, |D ω| ^ 3 ∂P) + δ / 2 + q ^ 2 := by
  have hconst : Integrable K P := Integrable.of_bound hKmeas 1 hK
  have hlinear : Integrable (fun ω => K ω * (D ω : ℂ)) P :=
    hfirst.ofReal.bdd_mul hKmeas hK
  have hsq : Integrable (fun ω => (D ω : ℂ) ^ 2) P := by
    have h : Integrable (fun ω => ((D ω ^ 2 : ℝ) : ℂ)) P := hsecond.ofReal
    simpa only [Complex.ofReal_pow] using h
  have hquad : Integrable (fun ω => K ω * (D ω : ℂ) ^ 2) P :=
    hsq.bdd_mul hKmeas hK
  have hphase : AEStronglyMeasurable
      (fun ω => Complex.exp ((D ω : ℂ) * Complex.I)) P :=
    Complex.continuous_exp.comp_aestronglyMeasurable
      ((hfirst.ofReal : Integrable (fun ω => (D ω : ℂ)) P).aestronglyMeasurable.mul_const _)
  have hphase_int : Integrable (fun ω => Complex.exp ((D ω : ℂ) * Complex.I)) P :=
    Integrable.of_bound hphase 1 (Filter.Eventually.of_forall (fun ω => by simp))
  have hchar : Integrable (fun ω => K ω * Complex.exp ((D ω : ℂ) * Complex.I)) P :=
    hphase_int.bdd_mul hKmeas hK
  have hB : ‖∫ ω, K ω ∂P‖ ≤ 1 := by
    simpa using norm_integral_le_of_norm_le (integrable_const (1 : ℝ)) hK
  exact gaussian_approximation_of_moments hq0 hq1 hB
    (characteristic_second_order P D K hK hthird hconst hlinear hquad hchar hmean)
    hsecond_est

end Innovation
end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_WeightedInnovation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal

namespace Problem336.Innovation

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem weighted_square_perturbation [IsFiniteMeasure P]
    {Q R : Ω → ℝ} {K : Ω → ℂ} {a : ℝ}
    (hQ : Integrable Q P) (hQ2 : Integrable (fun ω => Q ω ^ 2) P)
    (hR : AEStronglyMeasurable R P) (ha : 0 ≤ a)
    (hRbound : ∀ᵐ ω ∂P, |R ω| ≤ a)
    (hKmeas : AEStronglyMeasurable K P) (hK : ∀ᵐ ω ∂P, ‖K ω‖ ≤ 1) :
    ‖(∫ ω, K ω * ((Q ω + R ω : ℝ) : ℂ) ^ 2 ∂P) -
        ∫ ω, K ω * (Q ω : ℂ) ^ 2 ∂P‖ ≤
      2 * a * (∫ ω, |Q ω| ∂P) + a ^ 2 * P.real Set.univ := by
  have hD2 := InnovationMoments.integrable_square_add_of_bounded
    hQ.aestronglyMeasurable hR hQ2 ha hRbound
  have hCD2 : Integrable (fun ω => ((Q ω + R ω : ℝ) : ℂ) ^ 2) P := by
    convert Complex.ofRealCLM.integrable_comp hD2 using 1
    ext ω
    simp
  have hCQ2 : Integrable (fun ω => (Q ω : ℂ) ^ 2) P := by
    convert Complex.ofRealCLM.integrable_comp hQ2 using 1
    ext ω
    simp
  have hKD2 := hCD2.bdd_mul hKmeas hK
  have hKQ2 := hCQ2.bdd_mul hKmeas hK
  have hbound : Integrable (fun ω => 2 * a * |Q ω| + a ^ 2) P :=
    (hQ.abs.const_mul (2 * a)).add (integrable_const _)
  rw [← integral_sub hKD2 hKQ2]
  calc
    _ ≤ ∫ ω, 2 * a * |Q ω| + a ^ 2 ∂P := by
      apply norm_integral_le_of_norm_le hbound
      filter_upwards [hRbound, hK] with ω hRω hKω
      have heq : K ω * ((Q ω + R ω : ℝ) : ℂ) ^ 2 - K ω * (Q ω : ℂ) ^ 2 =
          K ω * ((((Q ω + R ω) ^ 2 - Q ω ^ 2 : ℝ)) : ℂ) := by
        push_cast
        ring
      rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ 1 * |(Q ω + R ω) ^ 2 - Q ω ^ 2| :=
          mul_le_mul_of_nonneg_right hKω (abs_nonneg _)
        _ ≤ 2 * a * |Q ω| + a ^ 2 := by
          simpa only [one_mul] using
            InnovationMoments.abs_square_perturbation_le (Q ω) (R ω) a ha hRω
    _ = _ := by
      rw [integral_add (hQ.abs.const_mul _) (integrable_const _),
        integral_const_mul, integral_const]
      simp only [smul_eq_mul]
      ring

theorem weighted_bounded_perturbation_characteristic [IsProbabilityMeasure P]
    {Q R : Ω → ℝ} {K : Ω → ℂ} {a q : ℝ}
    (hQ : Integrable Q P) (hQ2 : Integrable (fun ω => Q ω ^ 2) P)
    (hQ3 : Integrable (fun ω => |Q ω| ^ 3) P)
    (hR : AEStronglyMeasurable R P) (ha : 0 ≤ a)
    (hRbound : ∀ᵐ ω ∂P, |R ω| ≤ a)
    (hKmeas : AEStronglyMeasurable K P) (hK : ∀ᵐ ω ∂P, ‖K ω‖ ≤ 1)
    (hmean : (∫ ω, K ω * ((Q ω + R ω : ℝ) : ℂ) ∂P) = 0)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hQmoment : (∫ ω, K ω * (Q ω : ℂ) ^ 2 ∂P) =
      (2 * q : ℝ) * (∫ ω, K ω ∂P)) :
    ‖(∫ ω, K ω * Complex.exp (((Q ω + R ω : ℝ) : ℂ) * Complex.I) ∂P) -
        (Real.exp (-q) : ℂ) * (∫ ω, K ω ∂P)‖ ≤
      16 * ((∫ ω, |Q ω| ^ 3 ∂P) + a ^ 3) +
        (2 * a * (∫ ω, |Q ω| ∂P) + a ^ 2) / 2 + q ^ 2 := by
  have hRint : Integrable R P := Integrable.of_bound hR a (by simpa using hRbound)
  have hD2 := InnovationMoments.integrable_square_add_of_bounded
    hQ.aestronglyMeasurable hR hQ2 ha hRbound
  have hD3 := InnovationMoments.integrable_abs_cube_add_of_bounded
    hQ.aestronglyMeasurable hR hQ3 ha hRbound
  have hM : ‖(∫ ω, K ω * ((Q ω + R ω : ℝ) : ℂ) ^ 2 ∂P) -
      (2 * q : ℝ) * (∫ ω, K ω ∂P)‖ ≤
      2 * a * (∫ ω, |Q ω| ∂P) + a ^ 2 := by
    rw [← hQmoment]
    simpa using weighted_square_perturbation hQ hQ2 hR ha hRbound hKmeas hK
  have hstep := weighted_characteristic_gaussian_bound P (fun ω => Q ω + R ω) K
    hKmeas hK (hQ.add hRint) hD2 hD3 hmean hq0 hq1 hM
  have hthird : (∫ ω, |Q ω + R ω| ^ 3 ∂P) ≤
      4 * ((∫ ω, |Q ω| ^ 3 ∂P) + a ^ 3) := by
    simpa using InnovationMoments.integral_abs_cube_perturbation_le
      hQ.aestronglyMeasurable hR hQ3 ha hRbound
  linarith

theorem gaussian_bounded_perturbation_characteristic
    {Q R : Ω → ℝ} {K : Ω → ℂ} {a : ℝ} {v : ℝ≥0}
    (hLaw : ProbabilityTheory.HasLaw Q (ProbabilityTheory.gaussianReal 0 v) P)
    (hIndep : ProbabilityTheory.IndepFun K Q P)
    (hR : AEStronglyMeasurable R P) (ha : 0 ≤ a)
    (hRbound : ∀ᵐ ω ∂P, |R ω| ≤ a)
    (hKmeas : AEStronglyMeasurable K P) (hK : ∀ᵐ ω ∂P, ‖K ω‖ ≤ 1)
    (hmean : (∫ ω, K ω * ((Q ω + R ω : ℝ) : ℂ) ∂P) = 0)
    (hv : (v : ℝ) ≤ 2) :
    ‖(∫ ω, K ω * Complex.exp (((Q ω + R ω : ℝ) : ℂ) * Complex.I) ∂P) -
        (Real.exp (-((v : ℝ) / 2)) : ℂ) * (∫ ω, K ω ∂P)‖ ≤
      16 * ((Real.sqrt (v : ℝ)) ^ 3 *
        (∫ z : ℝ, |z| ^ 3 ∂ProbabilityTheory.gaussianReal 0 1) + a ^ 3) +
        (2 * a * Real.sqrt (v : ℝ) + a ^ 2) / 2 + ((v : ℝ) / 2) ^ 2 := by
  let : IsProbabilityMeasure P := hLaw.isProbabilityMeasure
  have hQ : Integrable Q P := hLaw.hasGaussianLaw.integrable
  have hQ2 : Integrable (fun ω => Q ω ^ 2) P := by
    simpa only [sq_abs] using gaussian_hasLaw_integrable_abs_pow hLaw 2
  have hQ3 := gaussian_hasLaw_integrable_abs_pow hLaw 3
  have hQmoment : (∫ ω, K ω * (Q ω : ℂ) ^ 2 ∂P) =
      (2 * ((v : ℝ) / 2) : ℝ) * (∫ ω, K ω ∂P) := by
    rw [gaussian_independent_weighted_second_moment hLaw hKmeas.aemeasurable hIndep]
    push_cast
    ring
  have hq0 : 0 ≤ (v : ℝ) / 2 := by positivity
  have hq1 : (v : ℝ) / 2 ≤ 1 := by linarith
  have hstep := weighted_bounded_perturbation_characteristic hQ hQ2 hQ3 hR ha
    hRbound hKmeas hK hmean hq0 hq1 hQmoment
  apply hstep.trans
  rw [gaussian_hasLaw_absolute_moment hLaw 3]
  gcongr
  exact gaussian_hasLaw_absolute_first_moment_le hLaw

end Problem336.Innovation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_InnovationErrorRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem336.Innovation

theorem gaussian_error_le_smallStep {h L c m : ℝ}
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hL : 0 ≤ L) :
    16 * ((Real.sqrt (h * c)) ^ 3 * m + (h * L) ^ 3) +
        (2 * (h * L) * Real.sqrt (h * c) + (h * L) ^ 2) / 2 +
        (h * c / 2) ^ 2 ≤
      (16 * ((Real.sqrt c) ^ 3 * m + L ^ 3) + L * Real.sqrt c +
        L ^ 2 / 2 + c ^ 2 / 4) * h * Real.sqrt h := by
  have hs0 := Real.sqrt_nonneg h
  have hs1 : Real.sqrt h ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hh1
  have hs2 := Real.sq_sqrt hh0
  have hh_s : h ≤ Real.sqrt h := by
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  have hh2 : h ^ 2 ≤ h * Real.sqrt h := by
    nlinarith [mul_le_mul_of_nonneg_left hh_s hh0]
  have hh3 : h ^ 3 ≤ h * Real.sqrt h := by
    nlinarith [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hh1)]
  have hs3 : (Real.sqrt h) ^ 3 = h * Real.sqrt h := by nlinarith
  rw [Real.sqrt_mul hh0, mul_pow, hs3]
  have hL3 := mul_le_mul_of_nonneg_right hh3 (pow_nonneg hL 3)
  have hL2 := mul_le_mul_of_nonneg_right hh2 (sq_nonneg L)
  have hc2 := mul_le_mul_of_nonneg_right hh2 (sq_nonneg c)
  nlinarith [hL3, hL2, hc2]

theorem gaussian_smallStep_characteristic {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Q R : Ω → ℝ} {K : Ω → ℂ} {h L c : ℝ} {v : ℝ≥0}
    (hLaw : HasLaw Q (gaussianReal 0 v) P) (hIndep : IndepFun K Q P)
    (hR : AEStronglyMeasurable R P)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hL : 0 ≤ L)
    (hvariance : (v : ℝ) = h * c) (hsmall : h * c ≤ 2)
    (hRbound : ∀ᵐ ω ∂P, |R ω| ≤ h * L)
    (hKmeas : AEStronglyMeasurable K P) (hK : ∀ᵐ ω ∂P, ‖K ω‖ ≤ 1)
    (hmean : (∫ ω, K ω * ((Q ω + R ω : ℝ) : ℂ) ∂P) = 0) :
    ‖(∫ ω, K ω * Complex.exp (((Q ω + R ω : ℝ) : ℂ) * Complex.I) ∂P) -
        (Real.exp (-(h * c / 2)) : ℂ) * (∫ ω, K ω ∂P)‖ ≤
      gaussianErrorConstant L c * h * Real.sqrt h := by
  have hv : (v : ℝ) ≤ 2 := by simpa only [hvariance] using hsmall
  have hbase := gaussian_bounded_perturbation_characteristic hLaw hIndep hR
    (mul_nonneg hh0 hL) hRbound hKmeas hK hmean hv
  rw [hvariance] at hbase
  exact hbase.trans (gaussian_error_le_smallStep hh0 hh1 hL)

end Problem336.Innovation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_InnovationSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace Problem336.InnovationSubdivision

theorem norm_sub_geometric_le {A : Type*} [NormedRing A]
    (a : A) (μ : ℕ → A) (ε : ℝ) (ha : ‖a‖ ≤ 1) :
    ∀ n, (∀ k < n, ‖μ (k + 1) - a * μ k‖ ≤ ε) →
      ‖μ n - a ^ n * μ 0‖ ≤ (n : ℝ) * ε := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro hstep
    have ih' := ih (fun k hk => hstep k (Nat.lt_trans hk (Nat.lt_succ_self n)))
    have hid : μ (n + 1) - a ^ (n + 1) * μ 0 =
        (μ (n + 1) - a * μ n) + a * (μ n - a ^ n * μ 0) := by
      rw [pow_succ']
      noncomm_ring
    rw [hid]
    calc
      ‖(μ (n + 1) - a * μ n) + a * (μ n - a ^ n * μ 0)‖
          ≤ ‖μ (n + 1) - a * μ n‖ + ‖a * (μ n - a ^ n * μ 0)‖ :=
        norm_add_le _ _
      _ ≤ ε + ‖a‖ * ‖μ n - a ^ n * μ 0‖ :=
        add_le_add (hstep n (Nat.lt_succ_self n)) (norm_mul_le _ _)
      _ ≤ ε + 1 * ((n : ℝ) * ε) := by gcongr
      _ = ((n + 1 : ℕ) : ℝ) * ε := by push_cast; ring

theorem tendsto_subdivision_error (C T : ℝ) :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * C *
      (T / ((n + 1 : ℕ) : ℝ)) * Real.sqrt (T / ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 0) := by
  have hquot : Tendsto (fun n : ℕ => T / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat T).comp (tendsto_add_atTop_nat 1)
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hquot
  have hlim : Tendsto (fun n : ℕ => C * T *
      Real.sqrt (T / ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := C * T)).mul hroot
  convert hlim using 1
  funext n
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

theorem eq_of_eventual_subdivision_recurrences {A : Type*} [NormedRing A]
    (z w : A) (a : ℕ → A) (μ : ℕ → ℕ → A) (C T : ℝ)
    (ha : ∀ n, ‖a n‖ ≤ 1)
    (hfinal : ∀ n, μ n (n + 1) = z)
    (hfree : ∀ n, a n ^ (n + 1) * μ n 0 = w)
    (hstep : ∀ᶠ n : ℕ in atTop, ∀ k < n + 1,
      ‖μ n (k + 1) - a n * μ n k‖ ≤
        C * (T / ((n + 1 : ℕ) : ℝ)) * Real.sqrt (T / ((n + 1 : ℕ) : ℝ))) :
    z = w := by
  have hb : ∀ᶠ n : ℕ in atTop, ‖z - w‖ ≤ ((n + 1 : ℕ) : ℝ) * C *
      (T / ((n + 1 : ℕ) : ℝ)) * Real.sqrt (T / ((n + 1 : ℕ) : ℝ)) := by
    filter_upwards [hstep] with n hn
    have hbound := norm_sub_geometric_le (a n) (μ n)
      (C * (T / ((n + 1 : ℕ) : ℝ)) * Real.sqrt (T / ((n + 1 : ℕ) : ℝ)))
      (ha n) (n + 1) hn
    rw [hfinal n, hfree n] at hbound
    simpa only [mul_assoc] using hbound
  have hz : ‖z - w‖ ≤ 0 := ge_of_tendsto (tendsto_subdivision_error C T) hb
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

theorem gaussian_identity_of_subdivision_recurrences
    (z m : ℂ) (μ : ℕ → ℕ → ℂ) (C T v : ℝ) (hT : 0 ≤ T) (hv : 0 ≤ v)
    (hinit : ∀ n, μ n 0 = m) (hfinal : ∀ n, μ n (n + 1) = z)
    (hstep : ∀ᶠ n : ℕ in atTop, ∀ k < n + 1,
      ‖μ n (k + 1) - (Real.exp (-(T / ((n + 1 : ℕ) : ℝ)) * v) : ℂ) * μ n k‖ ≤
        C * (T / ((n + 1 : ℕ) : ℝ)) * Real.sqrt (T / ((n + 1 : ℕ) : ℝ))) :
    z = (Real.exp (-T * v) : ℂ) * m := by
  apply eq_of_eventual_subdivision_recurrences z ((Real.exp (-T * v) : ℂ) * m)
    (fun n => (Real.exp (-(T / ((n + 1 : ℕ) : ℝ)) * v) : ℂ)) μ C T
    ?_ hfinal ?_ hstep
  · intro n
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg hT (by positivity))) hv
  · intro n
    rw [hinit n]
    congr 1
    have he : Real.exp (-(T / ((n + 1 : ℕ) : ℝ)) * v) ^ (n + 1) =
        Real.exp (-T * v) := by
      rw [← Real.exp_nat_mul]
      congr 1
      have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp
    exact_mod_cast he

end Problem336.InnovationSubdivision

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_InnovationPhaseRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal

namespace Problem336.InnovationPhaseRecurrence

lemma norm_phaseOn_le_one {Ω : Type*} (A : Set Ω) (X Y : Ω → ℝ) (ω : Ω) :
    ‖phaseOn A X Y ω‖ ≤ 1 := by
  classical
  by_cases hω : ω ∈ A
  · simp only [phaseOn, Set.indicator_of_mem hω, Complex.norm_exp_ofReal_mul_I]
    exact le_rfl
  · simp [phaseOn, hω]

lemma measurable_phaseOn {Ω : Type*} [MeasurableSpace Ω] {A : Set Ω} {X Y : Ω → ℝ}
    (hA : MeasurableSet A) (hX : Measurable X) (hY : Measurable Y) :
    Measurable (phaseOn A X Y) := by
  apply Measurable.indicator _ hA
  fun_prop

lemma phaseOn_mul_increment {Ω : Type*} (A : Set Ω) (X Y Z : Ω → ℝ) (ω : Ω) :
    phaseOn A X Y ω * Complex.exp (((Z ω - Y ω : ℝ) : ℂ) * Complex.I) =
      phaseOn A X Z ω := by
  classical
  by_cases hω : ω ∈ A
  · simp only [phaseOn, Set.indicator_of_mem hω]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp [phaseOn, hω]

lemma integral_phaseOn_self {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A : Set Ω} (hA : MeasurableSet A) (X : Ω → ℝ) :
    (∫ ω, phaseOn A X X ω ∂P) = (P.real A : ℂ) := by
  simp [phaseOn, integral_indicator hA]

lemma integral_phaseOn_eq_setIntegral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {A : Set Ω} (hA : MeasurableSet A) (X Y : Ω → ℝ) :
    (∫ ω, phaseOn A X Y ω ∂P) =
      ∫ ω in A, Complex.exp (((Y ω - X ω : ℝ) : ℂ) * Complex.I) ∂P := by
  exact integral_indicator hA

lemma phase_recurrence_of_weighted_step {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (A : Set Ω) (X Y Z : Ω → ℝ) (a : ℂ) (ε : ℝ)
    (hstep : ‖(∫ ω, phaseOn A X Y ω *
        Complex.exp (((Z ω - Y ω : ℝ) : ℂ) * Complex.I) ∂P) -
        (∫ ω, phaseOn A X Y ω ∂P) * a‖ ≤ ε) :
    ‖(∫ ω, phaseOn A X Z ω ∂P) - a * (∫ ω, phaseOn A X Y ω ∂P)‖ ≤ ε := by
  simp only [phaseOn_mul_increment] at hstep
  simpa only [mul_comm] using hstep

theorem restricted_characteristic_of_phase_steps
    {Ω T : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : T → Ω → ℝ) (s t : T) (τ : ℕ → ℕ → T)
    {A : Set Ω} (hA : MeasurableSet A)
    (hstart : ∀ n, τ n 0 = s) (hfinish : ∀ n, τ n (n + 1) = t)
    (C duration v : ℝ) (hduration : 0 ≤ duration) (hv : 0 ≤ v)
    (hstep : ∀ᶠ n : ℕ in atTop, ∀ k < n + 1,
      ‖(∫ ω, phaseOn A (X s) (X (τ n k)) ω *
          Complex.exp (((X (τ n (k + 1)) ω - X (τ n k) ω : ℝ) : ℂ) * Complex.I) ∂P) -
          (∫ ω, phaseOn A (X s) (X (τ n k)) ω ∂P) *
            (Real.exp (-(duration / ((n + 1 : ℕ) : ℝ)) * v) : ℂ)‖ ≤
        C * (duration / ((n + 1 : ℕ) : ℝ)) *
          Real.sqrt (duration / ((n + 1 : ℕ) : ℝ))) :
    (∫ ω in A, Complex.exp (((X t ω - X s ω : ℝ) : ℂ) * Complex.I) ∂P) =
      (Real.exp (-duration * v) : ℂ) * (P.real A : ℂ) := by
  let μ : ℕ → ℕ → ℂ := fun n k => ∫ ω, phaseOn A (X s) (X (τ n k)) ω ∂P
  apply InnovationSubdivision.gaussian_identity_of_subdivision_recurrences
    _ _ μ C duration v hduration hv
  · intro n
    dsimp [μ]
    rw [hstart n]
    exact integral_phaseOn_self hA (X s)
  · intro n
    dsimp [μ]
    rw [hfinish n]
    exact integral_phaseOn_eq_setIntegral hA (X s) (X t)
  · filter_upwards [hstep] with n hn
    intro k hk
    exact phase_recurrence_of_weighted_step A (X s) (X (τ n k))
      (X (τ n (k + 1))) _ _ (hn k hk)

theorem restricted_characteristic_of_bounded_test_steps
    {Ω T : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (X : T → Ω → ℝ) (s t : T) (τ : ℕ → ℕ → T)
    (past : ℕ → ℕ → MeasurableSpace Ω)
    {A : Set Ω} (hA : MeasurableSet A)
    (hApast : ∀ n k, MeasurableSet[past n k] A)
    (hXstart : ∀ n k, Measurable[past n k] (X s))
    (hXpast : ∀ n k, Measurable[past n k] (X (τ n k)))
    (hstart : ∀ n, τ n 0 = s) (hfinish : ∀ n, τ n (n + 1) = t)
    (C duration v : ℝ) (hduration : 0 ≤ duration) (hv : 0 ≤ v)
    (hlocal : ∀ᶠ n : ℕ in atTop, ∀ k < n + 1, ∀ K : Ω → ℂ,
      Measurable[past n k] K → (∀ ω, ‖K ω‖ ≤ 1) →
      ‖(∫ ω, K ω *
          Complex.exp (((X (τ n (k + 1)) ω - X (τ n k) ω : ℝ) : ℂ) * Complex.I) ∂P) -
          (∫ ω, K ω ∂P) * (Real.exp (-(duration / ((n + 1 : ℕ) : ℝ)) * v) : ℂ)‖ ≤
        C * (duration / ((n + 1 : ℕ) : ℝ)) *
          Real.sqrt (duration / ((n + 1 : ℕ) : ℝ))) :
    (∫ ω in A, Complex.exp (((X t ω - X s ω : ℝ) : ℂ) * Complex.I) ∂P) =
      (Real.exp (-duration * v) : ℂ) * (P.real A : ℂ) := by
  apply restricted_characteristic_of_phase_steps X s t τ hA hstart hfinish
    C duration v hduration hv
  filter_upwards [hlocal] with n hn
  intro k hk
  exact hn k hk (phaseOn A (X s) (X (τ n k)))
    (@measurable_phaseOn Ω (past n k) A (X s) (X (τ n k))
      (hApast n k) (hXstart n k) (hXpast n k))
    (norm_phaseOn_le_one A (X s) (X (τ n k)))

lemma timeGrid_mono (s d : ℝ≥0) (n : ℕ) : Monotone (timeGrid s d n) := by
  intro k l hkl
  dsimp [timeGrid]
  gcongr

lemma timeGrid_succ_sub (s d : ℝ≥0) (n k : ℕ) :
    (timeGrid s d n (k + 1) : ℝ) - (timeGrid s d n k : ℝ) =
      (d : ℝ) / ((n + 1 : ℕ) : ℝ) := by
  simp only [timeGrid, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div,
    NNReal.coe_natCast, NNReal.coe_one, Nat.cast_add, Nat.cast_one]
  ring

end Problem336.InnovationPhaseRecurrence

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_InnovationGaussianProcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem336.InnovationGaussianProcess

theorem restricted_characteristic_of_gaussian_perturbations
    {Ω T : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (X : T → Ω → ℝ) (s t : T) (τ : ℕ → ℕ → T)
    (past : ℕ → ℕ → MeasurableSpace Ω)
    (hpast : ∀ n k, past n k ≤ mΩ)
    {A : Set Ω} (hA : MeasurableSet A)
    (hApast : ∀ n k, MeasurableSet[past n k] A)
    (hXstart : ∀ n k, Measurable[past n k] (X s))
    (hXpast : ∀ n k, Measurable[past n k] (X (τ n k)))
    (hstart : ∀ n, τ n 0 = s) (hfinish : ∀ n, τ n (n + 1) = t)
    (duration c L : ℝ) (hduration : 0 ≤ duration) (hc : 0 ≤ c) (hL : 0 ≤ L)
    (Q R : ℕ → ℕ → Ω → ℝ) (variance : ℕ → ℕ → ℝ≥0)
    (hLaw : ∀ n k, k < n + 1 → HasLaw (Q n k) (gaussianReal 0 (variance n k)) P)
    (hvariance : ∀ n k, k < n + 1 →
      (variance n k : ℝ) = (duration / ((n + 1 : ℕ) : ℝ)) * c)
    (hR : ∀ n k, k < n + 1 → AEStronglyMeasurable (R n k) P)
    (hRbound : ∀ n k, k < n + 1 → ∀ᵐ ω ∂P,
      |R n k ω| ≤ (duration / ((n + 1 : ℕ) : ℝ)) * L)
    (hdecomp : ∀ n k, k < n + 1 → ∀ᵐ ω ∂P,
      X (τ n (k + 1)) ω - X (τ n k) ω = Q n k ω + R n k ω)
    (hIndep : ∀ n k, k < n + 1 → ∀ K : Ω → ℂ,
      Measurable[past n k] K → IndepFun K (Q n k) P)
    (hmean : ∀ n k, k < n + 1 → ∀ K : Ω → ℂ,
      Measurable[past n k] K → (∀ ω, ‖K ω‖ ≤ 1) →
      (∫ ω, K ω * ((X (τ n (k + 1)) ω - X (τ n k) ω : ℝ) : ℂ) ∂P) = 0) :
    (∫ ω in A, Complex.exp (((X t ω - X s ω : ℝ) : ℂ) * Complex.I) ∂P) =
      (Real.exp (-duration * (c / 2)) : ℂ) * (P.real A : ℂ) := by
  apply InnovationPhaseRecurrence.restricted_characteristic_of_bounded_test_steps
    X s t τ past hA hApast hXstart hXpast hstart hfinish
    (Innovation.gaussianErrorConstant L c) duration (c / 2) hduration (by positivity)
  have hquot : Tendsto (fun n : ℕ => duration / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat duration).comp (tendsto_add_atTop_nat 1)
  have htimes : Tendsto (fun n : ℕ => (duration / ((n + 1 : ℕ) : ℝ)) * c)
      atTop (𝓝 0) := by simpa using hquot.mul_const c
  have hsmall1 : ∀ᶠ n : ℕ in atTop, duration / ((n + 1 : ℕ) : ℝ) < 1 :=
    hquot.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hsmall2 : ∀ᶠ n : ℕ in atTop,
      (duration / ((n + 1 : ℕ) : ℝ)) * c < 2 :=
    htimes.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 2))
  filter_upwards [hsmall1, hsmall2] with n hn1 hn2
  intro k hk K hKmeas hKbound
  have hKΩ : Measurable K := hKmeas.mono (hpast n k) le_rfl
  have hmean' : (∫ ω, K ω * ((Q n k ω + R n k ω : ℝ) : ℂ) ∂P) = 0 := by
    rw [← hmean n k hk K hKmeas hKbound]
    apply integral_congr_ae
    filter_upwards [hdecomp n k hk] with ω hω
    rw [hω]
  have hstep := Innovation.gaussian_smallStep_characteristic
    (hLaw n k hk) (hIndep n k hk K hKmeas) (hR n k hk)
    (div_nonneg hduration (by positivity)) hn1.le hL
    (hvariance n k hk) hn2.le (hRbound n k hk) hKΩ.aestronglyMeasurable
    (Filter.Eventually.of_forall hKbound) hmean'
  have hphase : (∫ ω, K ω * Complex.exp (((Q n k ω + R n k ω : ℝ) : ℂ) * Complex.I) ∂P) =
      ∫ ω, K ω * Complex.exp (((X (τ n (k + 1)) ω - X (τ n k) ω : ℝ) : ℂ) * Complex.I) ∂P := by
    apply integral_congr_ae
    filter_upwards [hdecomp n k hk] with ω hω
    rw [hω]
  rw [hphase] at hstep
  have hexponent : -(duration / ((n + 1 : ℕ) : ℝ) * c / 2) =
      -(duration / ((n + 1 : ℕ) : ℝ)) * (c / 2) := by ring
  rw [hexponent] at hstep
  simpa only [mul_comm] using hstep

end Problem336.InnovationGaussianProcess

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_InnovationFiniteGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Problem336.InnovationFiniteGaussian

theorem martingale_projection {I T Ω : Type*} [Preorder T]
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) (F : Filtration T mΩ)
    (M : I → T → Ω → ℝ) (hM : ∀ i, Martingale (M i) F P)
    (S : Finset I) (θ : I → ℝ) :
    Martingale (fun t ω => ∑ i ∈ S, θ i * M i t ω) F P := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    convert (martingale_zero ℝ F P : Martingale (0 : T → Ω → ℝ) F P) using 1
    funext t ω
    simp
  | @insert i S hi ih =>
    simpa only [Finset.sum_insert hi, Pi.add_def, Pi.smul_def, smul_eq_mul] using
      ((hM i).smul (θ i)).add ih

theorem brownian_projection_law {I Ω : Type*} [Fintype I] [MeasurableSpace Ω]
    {P : Measure Ω} {B : I → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    (θ : I → ℝ) (u v : ℝ≥0) :
    HasLaw (fun ω => ∑ i, θ i * (B i v ω - B i u ω))
      (gaussianReal 0 (∑ i, NNReal.mk (θ i ^ 2) (sq_nonneg _) *
        nndist (v : ℝ) (u : ℝ))) P := by
  apply independent_weighted_gaussian_sum_hasLaw
  · intro i
    exact (hB i).hasLaw_sub v u
  · exact hI.comp (fun _ f => f v - f u) (by fun_prop)

theorem brownian_finset_projection_law {I Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : I → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    (S : Finset I) (θ : I → ℝ) (u v : ℝ≥0) :
    HasLaw (fun ω => ∑ i ∈ S, θ i * (B i v ω - B i u ω))
      (gaussianReal 0 (∑ i ∈ S, NNReal.mk (θ i ^ 2) (sq_nonneg _) *
        nndist (v : ℝ) (u : ℝ))) P := by
  classical
  have hi := brownian_projection_law (fun i : S => hB i)
    (hI.precomp (g := fun i : S => (i : I)) Subtype.val_injective)
    (fun i : S => θ i) u v
  have heq : (fun ω => ∑ i : S, θ i * (B i v ω - B i u ω)) =
      (fun ω => ∑ i ∈ S, θ i * (B i v ω - B i u ω)) := by
    funext ω
    exact Finset.sum_coe_sort S (fun i => θ i * (B i v ω - B i u ω))
  have hv := Finset.sum_coe_sort S (fun i => NNReal.mk (θ i ^ 2) (sq_nonneg _) *
    nndist (v : ℝ) (u : ℝ))
  rw [heq, hv] at hi
  exact hi

theorem brownian_projection_indep {I Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {B : I → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hBm : ∀ i t, Measurable (B i t))
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    {X : Ω → I → ℝ} (hX : Measurable X)
    (hXB : IndepFun X (fun ω i t => B i t ω) P)
    (S : Finset I) (θ : I → ℝ) {u v : ℝ≥0} (huv : u ≤ v)
    {m : MeasurableSpace Ω}
    (hm : m ≤ MeasurableSpace.comap (fun ω (p : I × Set.Iic u) =>
      (p.2 : ℝ≥0) * X ω p.1 + B p.1 p.2 ω) inferInstance)
    {K : Ω → ℂ} (hK : Measurable[m] K) :
    IndepFun K (fun ω => ∑ i ∈ S, θ i * (B i v ω - B i u ω)) P := by
  let : MeasurableSpace Ω := mΩ
  have hi := BrownianFamilyPast.indepFun_weighted_increment_observation
    hB hBm hI hX hXB S θ u (v - u)
  rw [add_tsub_cancel_of_le huv] at hi
  exact (indep_of_indep_of_le_right hi (hK.comap_le.trans hm)).symm

theorem restricted_characteristic_nnInnovation
    {I Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (X : Ω → I → ℝ) (B : I → ℝ≥0 → Ω → ℝ) (b : I → ℝ → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hBm : ∀ i t, Measurable (B i t))
    (hI : iIndepFun (fun i ω t => B i t ω) P) (hX : Measurable X)
    (hXB : IndepFun X (fun ω i t => B i t ω) P)
    (hb : ∀ i, Measurable (Function.uncurry (b i)))
    (hXrange : ∀ ω i, X ω i ∈ Set.Icc (0 : ℝ) 1)
    (hbrange : ∀ i t ω, b i t ω ∈ Set.Icc (0 : ℝ) 1)
    (hM : ∀ i, Martingale (Innovation.nnInnovation (fun ω => X ω i) (B i) (b i)) F P)
    (hF : ∀ u, F u ≤ MeasurableSpace.comap (fun ω (p : I × Set.Iic u) =>
      (p.2 : ℝ≥0) * X ω p.1 + B p.1 p.2 ω) inferInstance)
    (S : Finset I) (θ : I → ℝ) (s t : ℝ≥0) (τ : ℕ → ℕ → ℝ≥0)
    (hτ : ∀ n, Monotone (τ n))
    (hstart : ∀ n, τ n 0 = s) (hfinish : ∀ n, τ n (n + 1) = t)
    (duration : ℝ) (hduration : 0 ≤ duration)
    (hstep : ∀ n k, k < n + 1 →
      (τ n (k + 1) : ℝ) - (τ n k : ℝ) = duration / ((n + 1 : ℕ) : ℝ))
    {A : Set Ω} (hA : MeasurableSet[F s] A) :
    (∫ ω in A, Complex.exp (((∑ i ∈ S, θ i *
      (Innovation.nnInnovation (fun ω => X ω i) (B i) (b i) t ω -
       Innovation.nnInnovation (fun ω => X ω i) (B i) (b i) s ω) : ℝ) : ℂ) * Complex.I) ∂P) =
      (Real.exp (-duration * ((∑ i ∈ S, θ i ^ 2) / 2)) : ℂ) * (P.real A : ℂ) := by
  let W := fun i => Innovation.nnInnovation (fun ω => X ω i) (B i) (b i)
  let Z := fun r ω => ∑ i ∈ S, θ i * W i r ω
  have hZ : Martingale Z F P := martingale_projection P F W hM S θ
  let Q := fun n k ω => ∑ i ∈ S, θ i * (B i (τ n (k + 1)) ω - B i (τ n k) ω)
  let R := fun n k ω => Z (τ n (k + 1)) ω - Z (τ n k) ω - Q n k ω
  let v := fun n k => ∑ i ∈ S, NNReal.mk (θ i ^ 2) (sq_nonneg _) *
    nndist (τ n (k + 1) : ℝ) (τ n k : ℝ)
  have hZsub (u v : ℝ≥0) (ω : Ω) :
      Z v ω - Z u ω = ∑ i ∈ S, θ i * (W i v ω - W i u ω) := by
    simp only [Z, mul_sub, Finset.sum_sub_distrib]
  have hmono (n k : ℕ) : τ n k ≤ τ n (k + 1) := hτ n (Nat.le_succ k)
  have hres := InnovationGaussianProcess.restricted_characteristic_of_gaussian_perturbations
    Z s t τ (fun n k => F (τ n k)) (fun n k => F.le _) (F.le s A hA)
    (fun n k => F.mono (by simpa only [hstart n] using hτ n (Nat.zero_le k)) A hA)
    (fun n k => (hZ.stronglyMeasurable s).measurable.mono
      (F.mono (by simpa only [hstart n] using hτ n (Nat.zero_le k))) le_rfl)
    (fun n k => (hZ.stronglyMeasurable _).measurable)
    hstart hfinish duration (∑ i ∈ S, θ i ^ 2) (∑ i ∈ S, |θ i|) hduration
    (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    (Finset.sum_nonneg (fun i _ => abs_nonneg _)) Q R v
    (fun n k _ => brownian_finset_projection_law hB hI S θ _ _) ?_ ?_ ?_ ?_ ?_ ?_
  · simpa only [hZsub] using hres
  · intro n k hk
    simp only [v, NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_mk,
      coe_nndist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (show (τ n k : ℝ) ≤ (τ n (k + 1) : ℝ) from hmono n k))]
    rw [hstep n k hk, ← Finset.sum_mul, mul_comm]
  · intro n k hk
    have hq : Measurable (Q n k) := by dsimp [Q]; fun_prop
    exact (((hZ.integrable _).sub (hZ.integrable _)).aestronglyMeasurable).sub
      hq.aestronglyMeasurable
  · intro n k hk
    apply Filter.Eventually.of_forall
    intro ω
    have hid : R n k ω = ∑ i ∈ S, θ i *
        (W i (τ n (k + 1)) ω - W i (τ n k) ω -
          (B i (τ n (k + 1)) ω - B i (τ n k) ω)) := by
      simp only [R, hZsub, Q, mul_sub, Finset.sum_sub_distrib]
    rw [hid, ← hstep n k hk]
    calc
      _ ≤ ∑ i ∈ S, |θ i * (W i (τ n (k + 1)) ω - W i (τ n k) ω -
          (B i (τ n (k + 1)) ω - B i (τ n k) ω))| := by
        simpa only [Real.norm_eq_abs] using norm_sum_le S (fun i => θ i *
          (W i (τ n (k + 1)) ω - W i (τ n k) ω -
            (B i (τ n (k + 1)) ω - B i (τ n k) ω)))
      _ ≤ ∑ i ∈ S, |θ i| * ((τ n (k + 1) : ℝ) - (τ n k : ℝ)) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have hi := Innovation.innovation_sub_noise_bound
          (fun ω => X ω i) (fun r => B i r.toNNReal) (hb i)
          (fun ω => hXrange ω i) (hbrange i) (τ n k) (τ n (k + 1)) ω
        simpa only [W, Innovation.nnInnovation, Real.toNNReal_coe,
          Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (show (τ n k : ℝ) ≤ (τ n (k + 1) : ℝ) from hmono n k))] using hi
      _ = _ := by rw [← Finset.sum_mul, mul_comm]
  · intro n k hk
    exact Filter.Eventually.of_forall (fun ω => by dsimp [R]; ring)
  · intro n k hk K hK
    exact brownian_projection_indep hB hBm hI hX hXB S θ (hmono n k) (hF _) hK
  · intro n k hk K hK hKbound
    exact Innovation.integral_weighted_martingale_sub_eq_zero P F hZ (hmono n k)
      hK.stronglyMeasurable (Filter.Eventually.of_forall hKbound)

end Problem336.InnovationFiniteGaussian

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_InnovationProcessLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Problem336.InnovationProcessLaw

theorem identDistrib_nnInnovation
    {I Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (X : Ω → I → ℝ) (B : I → ℝ≥0 → Ω → ℝ) (b : I → ℝ → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hBm : ∀ i t, Measurable (B i t))
    (hI : iIndepFun (fun i ω t => B i t ω) P) (hX : Measurable X)
    (hXB : IndepFun X (fun ω i t => B i t ω) P)
    (hb : ∀ i, Measurable (Function.uncurry (b i)))
    (hXrange : ∀ ω i, X ω i ∈ Set.Icc (0 : ℝ) 1)
    (hbrange : ∀ i t ω, b i t ω ∈ Set.Icc (0 : ℝ) 1)
    (hM : ∀ i, Martingale (Innovation.nnInnovation (fun ω => X ω i) (B i) (b i)) F P)
    (hF : ∀ u, F u ≤ MeasurableSpace.comap (fun ω (p : I × Set.Iic u) =>
      (p.2 : ℝ≥0) * X ω p.1 + B p.1 p.2 ω) inferInstance) :
    IdentDistrib
      (fun ω i t => Innovation.nnInnovation (fun ω => X ω i) (B i) (b i) t ω)
      (fun ω i t => B i t ω) P P := by
  classical
  let W := fun i => Innovation.nnInnovation (fun ω => X ω i) (B i) (b i)
  apply BrownianFamilyIdentification.identDistrib_brownian_family F W B
    (fun i t => (hM i).stronglyMeasurable t |>.measurable) hBm
  · intro i
    filter_upwards [(hB i).eval_zero_ae_eq_zero] with ω hω
    simpa [W, Innovation.nnInnovation_apply] using hω
  · exact hB
  · exact hI
  · intro S s t hst A hA θ
    let θ' : I → ℝ := fun i => if hi : i ∈ S then θ ⟨i, hi⟩ else 0
    have heval (i : S) : θ' i = θ i := by simp [θ', i.property]
    have hscalar := InnovationFiniteGaussian.restricted_characteristic_nnInnovation
      P F X B b hB hBm hI hX hXB hb hXrange hbrange hM hF S θ' s (s + (t - s))
      (InnovationPhaseRecurrence.timeGrid s (t - s))
      (InnovationPhaseRecurrence.timeGrid_mono s (t - s))
      (InnovationPhaseRecurrence.timeGrid_zero s (t - s))
      (InnovationPhaseRecurrence.timeGrid_finish s (t - s))
      ((t - s : ℝ≥0) : ℝ) (NNReal.coe_nonneg _)
      (fun n k _ => InnovationPhaseRecurrence.timeGrid_succ_sub s (t - s) n k) hA
    rw [add_tsub_cancel_of_le hst] at hscalar
    have hsum (ω : Ω) : (∑ i ∈ S, θ' i * (W i t ω - W i s ω)) =
        ∑ i : S, θ i * (W i t ω - W i s ω) := by
      rw [← Finset.sum_coe_sort S (fun i => θ' i * (W i t ω - W i s ω))]
      simp only [heval]
    have hsq : (∑ i ∈ S, θ' i ^ 2) = ‖θ‖ ^ 2 := by
      rw [← Finset.sum_coe_sort S (fun i => θ' i ^ 2), EuclideanSpace.real_norm_sq_eq]
      simp only [heval]
    change (∫ ω in A, Complex.exp (((∑ i ∈ S, θ' i *
      (W i t ω - W i s ω) : ℝ) : ℂ) * Complex.I) ∂P) = _ at hscalar
    simp_rw [hsum] at hscalar
    rw [hsq] at hscalar
    convert hscalar using 1
    · first | rfl | congr 1
    simp only [BrownianFamilyIdentification.charFun_vectorGaussian,
      RCLike.real_smul_eq_coe_mul, Measure.real, mul_comm]
    rw [Complex.ofReal_exp]
    congr 2
    push_cast
    ring

end Problem336.InnovationProcessLaw

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CanonicalBrownianSampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace Problem336.CanonicalBrownianSampler

open CanonicalBrownianReference

variable {I : Type*} [countableIndices : Countable I]

attribute [local instance] OAI.Problem336.CanonicalBrownianSampler.instMeasurableSpacePath
omit countableIndices in
theorem measurable_driftField [Countable I] (μ : ProbabilityMeasure (I → Bool))
    (S : I → ℕ → Finset I) (i : I) :
    Measurable (Function.uncurry (driftField μ S i)) := by
  have hf : Measurable (fun p : ℝ × Space I => CanonicalBrownianReference.observation p.1.toNNReal p.2) :=
    observation_jointlyMeasurable.comp
      ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  change Measurable (fun p : ℝ × Space I =>
    PosteriorDrift.drift μ S p.1 (CanonicalBrownianReference.observation p.1.toNNReal p.2) i)
  let f : ℝ × Space I → ℝ × (I → ℝ) := fun p =>
    (p.1, CanonicalBrownianReference.observation p.1.toNNReal p.2)
  have hm : Measurable f := measurable_fst.prodMk hf
  exact (PosteriorDrift.measurable_drift_coordinate μ S i).comp (f := f) hm

theorem martingale_innovation (μ : ProbabilityMeasure (I → Bool))
    (S : I → ℕ → Finset I) (i : I)
    (hS : Monotone (S i)) (hcover : ∀ j, ∃ n, j ∈ S i n) :
    Martingale (Innovation.nnInnovation (fun q : Space I => signal q i)
      (CanonicalBrownianReference.noise i) (driftField μ S i)) filtration (law μ) := by
  exact CanonicalPosteriorMartingale.martingale_nnInnovation (law μ) μ CanonicalBrownianReference.hidden
    hidden_measurable (hidden_hasLaw μ).map_eq CanonicalBrownianReference.noise
    (fun i => (noise_brownian μ i).toIsPreBrownianReal) noise_measurable
    noise_continuous (noise_independent μ) (hidden_independent_flat_noise μ)
    S i hS hcover

theorem raw_innovation_identDistrib (μ : ProbabilityMeasure (I → Bool))
    (S : I → ℕ → Finset I)
    (hS : ∀ i, Monotone (S i)) (hcover : ∀ i j, ∃ n, j ∈ S i n) :
    IdentDistrib
      (fun q i t => Innovation.nnInnovation (fun q : Space I => signal q i)
        (CanonicalBrownianReference.noise i) (driftField μ S i) t q)
      (fun (q : Space I) i t => CanonicalBrownianReference.noise i t q) (law μ) (law μ) := by
  apply InnovationProcessLaw.identDistrib_nnInnovation (law μ) filtration signal CanonicalBrownianReference.noise
    (driftField μ S)
  · exact fun i => (noise_brownian μ i).toIsPreBrownianReal
  · exact noise_measurable
  · exact noise_independent μ
  · exact bit_hidden_measurable
  · exact bit_hidden_independent_noise μ
  · exact measurable_driftField μ S
  · exact bit_hidden_mem_Icc
  · exact fun i s q => PosteriorDrift.drift_mem_Icc μ S s _ i
  · exact fun i => martingale_innovation μ S i (hS i) (hcover i)
  · intro u
    exact le_rfl

theorem raw_innovation_hasLaw_oai (μ : ProbabilityMeasure (I → Bool))
    (S : I → ℕ → Finset I)
    (hS : ∀ i, Monotone (S i)) (hcover : ∀ i j, ∃ n, j ∈ S i n) :
    HasLaw (RawInnovationSampler.rawInnovation CanonicalBrownianReference.hidden CanonicalBrownianReference.noise (PosteriorDrift.drift μ S))
      ((noiseLaw I).map ContinuousPathLaw.raw) (law μ) := by
  have hd := raw_innovation_identDistrib μ S hS hcover
  exact ⟨hd.aemeasurable_fst, hd.map_eq.trans (raw_noise_hasLaw μ).map_eq⟩

end Problem336.CanonicalBrownianSampler

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Problem336.CanonicalBrownianSampler.raw_innovation_hasLaw_oai.{u_1} := @OAI.Problem336.CanonicalBrownianSampler.raw_innovation_hasLaw_oai.{u_1}
