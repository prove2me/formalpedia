-- Prove2me | solution 1 for OAI.Problem358.one_third_stability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T09:22:33.704442+00:00
-- url     : https://prove2.me/submissions/17b66193-db79-45b7-94f7-d4d532a7bab5

import Mathlib
import Definitions.Def_Brenier
import Definitions.Def_OAIQ5T2000
import Theorems.Thm_OAI_Problem358_FixedMassIntercepts_exists_actual_atomic_intercept_path

section
-- module Solutions.OAIQ5_T2.Brenier_AffineCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace Problem358.FiniteAffine

variable {ι F : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma affine_le_potential (y : ι → F) (c : ι → ℝ) (x : F) (i : ι) :
    ⟪x, y i⟫ + c i ≤ potential y c x := by
  unfold potential
  exact Finset.le_sup' (fun j => ⟪x, y j⟫ + c j) (Finset.mem_univ i)

lemma potential_eq_iff_maximizes (y : ι → F) (c : ι → ℝ) (x : F) (i : ι) :
    potential y c x = ⟪x, y i⟫ + c i ↔ Maximizes y c x i := by
  constructor
  · intro h j
    simpa only [h] using affine_le_potential y c x j
  · intro h
    exact le_antisymm (Finset.sup'_le _ _ fun j _ => h j)
      (affine_le_potential y c x i)

lemma continuous_potential (y : ι → F) (c : ι → ℝ) :
    Continuous (potential y c) := by
  unfold potential
  exact Continuous.finset_sup'_apply _ fun i _ =>
    (continuous_id.inner continuous_const).add continuous_const

lemma potential_le_of_affine_le (y : ι → F) (c : ι → ℝ) (x : F) (r : ℝ)
    (h : ∀ i, ⟪x, y i⟫ + c i ≤ r) : potential y c x ≤ r := by
  exact Finset.sup'_le _ _ fun i _ => h i

lemma dual_gap (y : ι → F) (c : ι → ℝ) (x : F) (i : ι) :
    ‖x - y i‖ ^ 2 - (sourceDual y c x + targetDualAt y c i) =
      2 * (potential y c x - (⟪x, y i⟫ + c i)) := by
  rw [norm_sub_sq_real]
  unfold sourceDual targetDualAt
  ring

lemma dual_le_cost (y : ι → F) (c : ι → ℝ) (x : F) (i : ι) :
    sourceDual y c x + targetDualAt y c i ≤ ‖x - y i‖ ^ 2 := by
  have h := affine_le_potential y c x i
  have hg := dual_gap y c x i
  linarith

lemma dual_eq_cost_iff (y : ι → F) (c : ι → ℝ) (x : F) (i : ι) :
    sourceDual y c x + targetDualAt y c i = ‖x - y i‖ ^ 2 ↔
      Maximizes y c x i := by
  rw [← potential_eq_iff_maximizes]
  have hg := dual_gap y c x i
  constructor <;> intro h <;> linarith

lemma dual_eq_cost_of_maximizes (y : ι → F) (c : ι → ℝ) (x : F) (i : ι)
    (hi : Maximizes y c x i) :
    sourceDual y c x + targetDualAt y c i = ‖x - y i‖ ^ 2 :=
  (dual_eq_cost_iff y c x i).mpr hi

lemma continuous_sourceDual (y : ι → F) (c : ι → ℝ) :
    Continuous (sourceDual y c) := by
  exact (continuous_norm.pow 2).sub (continuous_const.mul (continuous_potential y c))

omit [Nonempty ι] [InnerProductSpace ℝ F] in
lemma targetDual_site (y : ι → F) (c : ι → ℝ) (hy : Function.Injective y)
    (i : ι) : targetDual y c (y i) = targetDualAt y c i := by
  classical
  simp [targetDual, Set.indicator, hy.eq_iff]

variable [MeasurableSpace F] [BorelSpace F]

omit [Nonempty ι] [InnerProductSpace ℝ F] in
lemma integrable_targetDual (y : ι → F) (c : ι → ℝ)
    (μ : Measure F) [IsFiniteMeasure μ] : Integrable (targetDual y c) μ := by
  unfold targetDual
  exact integrable_finsetSum _ fun i _ =>
    (integrable_const _).indicator (measurableSet_singleton (y i))

omit [MeasurableSpace F] [BorelSpace F] in
lemma dual_le_cost_on_range (y : ι → F) (c : ι → ℝ) (hy : Function.Injective y)
    (x z : F) (hz : z ∈ Set.range y) :
    sourceDual y c x + targetDual y c z ≤ ‖x - z‖ ^ 2 := by
  obtain ⟨i, rfl⟩ := hz
  rw [targetDual_site y c hy i]
  exact dual_le_cost y c x i

omit [MeasurableSpace F] [BorelSpace F] in
lemma dual_eq_cost_on_range_iff (y : ι → F) (c : ι → ℝ)
    (hy : Function.Injective y) (x : F) (i : ι) :
    sourceDual y c x + targetDual y c (y i) = ‖x - y i‖ ^ 2 ↔
      Maximizes y c x i := by
  rw [targetDual_site y c hy i]
  exact dual_eq_cost_iff y c x i

end Problem358.FiniteAffine

end

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_CompactMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358

section General

variable {X F : Type*} [TopologicalSpace X] [T2Space X]
  [MeasurableSpace X] [OpensMeasurableSpace X] [NormedAddCommGroup F]
  {μ : Measure X} [IsFiniteMeasure μ] {K : Set X} {f : X → F}

/-- Continuity only on a compact set of full measure suffices for integrability. -/
theorem integrable_of_continuousOn_of_ae_mem_compact
    (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K) (hf : ContinuousOn f K) :
    Integrable f μ := by
  have h := hf.integrableOn_compact hK (μ := μ)
  rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] at h
  exact h

end General

/-- Continuous-on-support functions are integrable for compactly supported finite measures. -/
theorem IsSupported.integrable_continuousOn
    {d : ℕ} {μ : Measure (E d)} [IsFiniteMeasure μ] {K : Set (E d)}
    (hμ : IsSupported μ K) (hK : IsCompact K)
    {F : Type*} [NormedAddCommGroup F] {f : E d → F} (hf : ContinuousOn f K) :
    Integrable f μ := by
  exact integrable_of_continuousOn_of_ae_mem_compact hK (ae_iff.mpr hμ) hf

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem358
namespace CompactIntegrability

variable {d : ℕ} {ρ : Measure (E d)} {T S : E d → E d}
  {Y Z : Set (E d)}

/-- An almost-everywhere limit of maps into a fixed compact set stays in that set. -/
theorem ae_mem_of_ae_tendsto {F : ℕ → E d → E d}
    (hY : IsCompact Y) (hFY : ∀ n, ∀ᵐ x ∂ρ, F n x ∈ Y)
    (hlim : ∀ᵐ x ∂ρ, Filter.Tendsto (fun n => F n x) Filter.atTop (𝓝 (T x))) :
    ∀ᵐ x ∂ρ, T x ∈ Y := by
  have hmem : ∀ᵐ x ∂ρ, ∀ n, F n x ∈ Y := ae_all_iff.mpr hFY
  filter_upwards [hmem, hlim] with x hx hlimx
  exact hY.isClosed.mem_of_tendsto hlimx (Filter.Eventually.of_forall hx)

/-- Compact range supplies the domination needed to pass to continuous test integrals. -/
theorem tendsto_integral_comp_of_ae_tendsto [IsFiniteMeasure ρ]
    {F : ℕ → E d → E d} (hF : ∀ n, Measurable (F n))
    (hY : IsCompact Y) (hFY : ∀ n, ∀ᵐ x ∂ρ, F n x ∈ Y)
    (hlim : ∀ᵐ x ∂ρ, Filter.Tendsto (fun n => F n x) Filter.atTop (𝓝 (T x)))
    {φ : E d → ℝ} (hφ : Continuous φ) :
    Filter.Tendsto (fun n => ∫ x, φ (F n x) ∂ρ) Filter.atTop
      (𝓝 (∫ x, φ (T x) ∂ρ)) := by
  obtain ⟨R, _, hR⟩ := (hY.image hφ).isBounded.exists_pos_norm_le
  apply tendsto_integral_of_dominated_convergence (fun _ => R)
  · intro n
    exact (hφ.measurable.comp (hF n)).aestronglyMeasurable
  · exact integrable_const R
  · intro n
    filter_upwards [hFY n] with x hx
    exact hR _ ⟨F n x, hx, rfl⟩
  · filter_upwards [hlim] with x hx
    exact hφ.continuousAt.tendsto.comp hx

/-- Almost-everywhere convergence within a common compact range implies convergence of
squared map distances. This is the bounded-convergence step in finite-target approximation. -/
theorem tendsto_integral_sub_norm_sq_of_ae_tendsto [IsFiniteMeasure ρ]
    {F : ℕ → E d → E d} (hF : ∀ n, Measurable (F n)) (hT : Measurable T)
    (hY : IsCompact Y) (hFY : ∀ n, ∀ᵐ x ∂ρ, F n x ∈ Y)
    (hlim : ∀ᵐ x ∂ρ, Filter.Tendsto (fun n => F n x) Filter.atTop (𝓝 (T x))) :
    Filter.Tendsto (fun n => ∫ x, ‖F n x - T x‖ ^ 2 ∂ρ) Filter.atTop (𝓝 0) := by
  have hTY := ae_mem_of_ae_tendsto hY hFY hlim
  obtain ⟨R, hRpos, hR⟩ := hY.isBounded.exists_pos_norm_le
  have hdom := tendsto_integral_of_dominated_convergence (μ := ρ)
    (F := fun n x => ‖F n x - T x‖ ^ 2) (f := fun _ => (0 : ℝ))
    (fun _ => (2 * R) ^ 2)
  apply (by simpa using hdom : _)
  · intro n
    exact ((hF n).sub hT).norm.pow_const 2 |>.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [hFY n, hTY] with x hx hxT
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
    calc
      ‖F n x - T x‖ ≤ ‖F n x‖ + ‖T x‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add (hR _ hx) (hR _ hxT)
      _ = 2 * R := by ring
  · filter_upwards [hlim] with x hx
    have hc : Tendsto (fun _ : ℕ => T x) atTop (𝓝 (T x)) := tendsto_const_nhds
    simpa using (hx.sub hc).norm.pow 2

/-- Compact-range bounded convergence stated using the problem's exact map distance. -/
theorem tendsto_mapL2Dist_of_ae_tendsto [IsFiniteMeasure ρ]
    {F : ℕ → E d → E d} (hF : ∀ n, Measurable (F n)) (hT : Measurable T)
    (hY : IsCompact Y) (hFY : ∀ n, ∀ᵐ x ∂ρ, F n x ∈ Y)
    (hlim : ∀ᵐ x ∂ρ, Filter.Tendsto (fun n => F n x) Filter.atTop (𝓝 (T x))) :
    Filter.Tendsto (fun n => mapL2Dist ρ (F n) T) Filter.atTop (𝓝 0) := by
  have h := tendsto_integral_sub_norm_sq_of_ae_tendsto hF hT hY hFY hlim
  simpa [mapL2Dist, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp h

end CompactIntegrability

namespace CompactIntegrability

variable {d : ℕ} {ρ μ : Measure (E d)} {Y : Set (E d)}
  {F Q : ℕ → E d → E d} {T : E d → E d}

/-- Identify a compact-range pointwise limit's law by continuous test integrals. -/
theorem map_eq_of_ae_tendsto_of_test_tendsto [IsFiniteMeasure ρ] [IsFiniteMeasure μ]
    (hF : ∀ n, Measurable (F n)) (hT : Measurable T)
    (hY : IsCompact Y) (hFY : ∀ n, ∀ᵐ x ∂ρ, F n x ∈ Y)
    (hlim : ∀ᵐ x ∂ρ, Tendsto (fun n => F n x) atTop (𝓝 (T x)))
    (htest : ∀ φ : E d → ℝ, Continuous φ →
      Tendsto (fun n => ∫ x, φ (F n x) ∂ρ) atTop (𝓝 (∫ y, φ y ∂μ))) :
    Measure.map T ρ = μ := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  have hφ : Continuous (φ : E d → ℝ) := map_continuous φ
  rw [integral_map hT.aemeasurable hφ.measurable.aestronglyMeasurable]
  exact tendsto_nhds_unique
    (tendsto_integral_comp_of_ae_tendsto hF hY hFY hlim hφ) (htest φ hφ)

/-- If the approximating maps have the laws of quantizers converging to the identity,
the almost-everywhere limit has the original target law. -/
theorem map_eq_of_ae_tendsto_of_map_eq_quantizers [IsFiniteMeasure ρ] [IsFiniteMeasure μ]
    (hF : ∀ n, Measurable (F n)) (hT : Measurable T)
    (hQ : ∀ n, Measurable (Q n)) (hY : IsCompact Y)
    (hFY : ∀ n, ∀ᵐ x ∂ρ, F n x ∈ Y)
    (hQY : ∀ n, ∀ᵐ y ∂μ, Q n y ∈ Y)
    (hlim : ∀ᵐ x ∂ρ, Tendsto (fun n => F n x) atTop (𝓝 (T x)))
    (hQlim : ∀ᵐ y ∂μ, Tendsto (fun n => Q n y) atTop (𝓝 y))
    (hpush : ∀ n, Measure.map (F n) ρ = Measure.map (Q n) μ) :
    Measure.map T ρ = μ := by
  apply map_eq_of_ae_tendsto_of_test_tendsto hF hT hY hFY hlim
  intro φ hφ
  have htest := tendsto_integral_comp_of_ae_tendsto hQ hY hQY hQlim hφ
  have heq : (fun n => ∫ x, φ (F n x) ∂ρ) = (fun n => ∫ y, φ (Q n y) ∂μ) := by
    funext n
    rw [← integral_map (hF n).aemeasurable hφ.measurable.aestronglyMeasurable,
      hpush n, integral_map (hQ n).aemeasurable hφ.measurable.aestronglyMeasurable]
  rw [heq]
  exact htest

end CompactIntegrability
end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Optimality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory

namespace Problem358

/-- A measure concentrated on the graph of a measurable function is determined
by its first marginal. This is the last step in uniqueness of a transport plan. -/
theorem eq_graph_map_of_ae_on_graph
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (π : Measure (X × Y)) {T : X → Y} (hT : Measurable T)
    (hgraph : ∀ᵐ p ∂π, p.2 = T p.1) :
    π = Measure.map (fun x => (x, T x)) (Measure.map Prod.fst π) := by
  have hm : Measurable (fun x : X => (x, T x)) := measurable_id.prodMk hT
  rw [Measure.map_map hm measurable_fst]
  calc
    π = Measure.map id π := (Measure.map_id).symm
    _ = Measure.map ((fun x => (x, T x)) ∘ Prod.fst) π := by
      apply Measure.map_congr
      filter_upwards [hgraph] with p hp
      exact Prod.ext rfl hp

/-- The same reconstruction statement with an explicitly prescribed marginal. -/
theorem eq_graph_map_of_fst_eq_and_ae_on_graph
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {π : Measure (X × Y)} {ρ : Measure X} {T : X → Y}
    (hT : Measurable T) (hfst : Measure.map Prod.fst π = ρ)
    (hgraph : ∀ᵐ p ∂π, p.2 = T p.1) :
    π = Measure.map (fun x => (x, T x)) ρ := by
  rw [← hfst]
  exact eq_graph_map_of_ae_on_graph π hT hgraph

end Problem358

end

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem358

variable {d : ℕ} {ρ μ : Measure (E d)} {π : Measure (E d × E d)}

/-- A finite quadratic plan cost is an ordinary integrable squared distance. -/
theorem integrable_sqdist_of_cost_ne_top
    (h : quadraticPlanCost π ≠ ∞) :
    Integrable (fun p : E d × E d => ‖p.1 - p.2‖ ^ 2) π := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (by fun_prop) (Filter.Eventually.of_forall fun p => sq_nonneg _)).mp
  exact h

/-- Conversion between the extended and real quadratic costs. -/
theorem quadraticPlanCost_eq_ofReal_integral
    (h : Integrable (fun p : E d × E d => ‖p.1 - p.2‖ ^ 2) π) :
    quadraticPlanCost π = ENNReal.ofReal (∫ p, ‖p.1 - p.2‖ ^ 2 ∂π) := by
  exact (ofReal_integral_eq_lintegral_ofReal h
    (Filter.Eventually.of_forall fun p => sq_nonneg _)).symm

/-- Integrability of a separable dual potential under any coupling. -/
theorem dual_integrable_sum (hπ : IsCoupling ρ μ π)
    {f g : E d → ℝ} (hf : Integrable f ρ) (hg : Integrable g μ) :
    Integrable (fun p : E d × E d => f p.1 + g p.2) π := by
  have hf' : Integrable f (Measure.map Prod.fst π) := hπ.2.1.symm ▸ hf
  have hg' : Integrable g (Measure.map Prod.snd π) := hπ.2.2.symm ▸ hg
  exact (hf'.comp_measurable measurable_fst).add
    (hg'.comp_measurable measurable_snd)

/-- The integral of a separable dual potential depends only on the marginals. -/
theorem dual_integral_sum (hπ : IsCoupling ρ μ π)
    {f g : E d → ℝ} (hf : Integrable f ρ) (hg : Integrable g μ) :
    (∫ p, f p.1 + g p.2 ∂π) = (∫ x, f x ∂ρ) + ∫ y, g y ∂μ := by
  have hf' : Integrable f (Measure.map Prod.fst π) := hπ.2.1.symm ▸ hf
  have hg' : Integrable g (Measure.map Prod.snd π) := hπ.2.2.symm ▸ hg
  have hfi : Integrable (fun p : E d × E d => f p.1) π := hf'.comp_measurable measurable_fst
  have hgi : Integrable (fun p : E d × E d => g p.2) π := hg'.comp_measurable measurable_snd
  rw [integral_add hfi hgi]
  rw [← integral_map measurable_fst.aemeasurable hf'.aestronglyMeasurable,
    ← integral_map measurable_snd.aemeasurable hg'.aestronglyMeasurable,
    hπ.2.1, hπ.2.2]

/-- Weak Kantorovich duality for the problem's quadratic cost definition. -/
theorem dual_cost_lower_bound (hπ : IsCoupling ρ μ π)
    {f g : E d → ℝ} (hf : Integrable f ρ) (hg : Integrable g μ)
    (hbound : ∀ᵐ p ∂π, f p.1 + g p.2 ≤ ‖p.1 - p.2‖ ^ 2) :
    ENNReal.ofReal ((∫ x, f x ∂ρ) + ∫ y, g y ∂μ) ≤ quadraticPlanCost π := by
  by_cases htop : quadraticPlanCost π = ∞
  · simp [htop]
  have hc := integrable_sqdist_of_cost_ne_top htop
  rw [quadraticPlanCost_eq_ofReal_integral hc,
    ← dual_integral_sum hπ hf hg]
  exact ENNReal.ofReal_le_ofReal (integral_mono_ae (dual_integrable_sum hπ hf hg) hc hbound)

/-- A graph saturating a separable dual bound has exactly the dual cost. -/
theorem quadraticPlanCost_graph_eq_dual
    {T : E d → E d} (hT : Measurable T) (hpush : Measure.map T ρ = μ)
    {f g : E d → ℝ} (hf : Integrable f ρ) (hg : Integrable g μ)
    (heq : ∀ᵐ x ∂ρ, ‖x - T x‖ ^ 2 = f x + g (T x)) :
    quadraticPlanCost (graphPlan ρ T) =
      ENNReal.ofReal ((∫ x, f x ∂ρ) + ∫ y, g y ∂μ) := by
  have hg' : Integrable g (Measure.map T ρ) := hpush.symm ▸ hg
  have hgT : Integrable (fun x => g (T x)) ρ := hg'.comp_measurable hT
  have hc : Integrable (fun x => ‖x - T x‖ ^ 2) ρ := (hf.add hgT).congr (heq.mono fun x hx => hx.symm)
  unfold quadraticPlanCost graphPlan
  have hm : Measurable (fun x : E d => (x, T x)) := by fun_prop
  rw [lintegral_map (by fun_prop) hm]
  change (∫⁻ x, ENNReal.ofReal (‖x - T x‖ ^ 2) ∂ρ) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hc
    (Filter.Eventually.of_forall fun x => sq_nonneg _), integral_congr_ae heq,
    integral_add hf hgT, ← integral_map hT.aemeasurable hg'.aestronglyMeasurable,
    hpush]

/-- Dual attainment certifies optimality against every probability coupling. -/
theorem isQuadraticOptimalMap_of_dual
    {T : E d → E d} (hT : Measurable T) (hpush : Measure.map T ρ = μ)
    {f g : E d → ℝ} (hf : Integrable f ρ) (hg : Integrable g μ)
    (hbound : ∀ π : Measure (E d × E d), IsCoupling ρ μ π →
      ∀ᵐ p ∂π, f p.1 + g p.2 ≤ ‖p.1 - p.2‖ ^ 2)
    (heq : ∀ᵐ x ∂ρ, ‖x - T x‖ ^ 2 = f x + g (T x)) :
    IsQuadraticOptimalMap ρ μ T := by
  refine ⟨hT, hpush, fun π hπ => ?_⟩
  rw [quadraticPlanCost_graph_eq_dual hT hpush hf hg heq]
  exact dual_cost_lower_bound hπ hf hg (hbound π hπ)

end Problem358

end

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358

variable {d : ℕ} {ρ μ : Measure (E d)} {π : Measure (E d × E d)}

/-- Equality in the integral dual bound forces saturation almost everywhere. -/
theorem dual_saturation_of_integral_eq
    (hπ : IsCoupling ρ μ π) {f g : E d → ℝ}
    (hf : Integrable f ρ) (hg : Integrable g μ)
    (hc : Integrable (fun p : E d × E d => ‖p.1 - p.2‖ ^ 2) π)
    (hbound : ∀ᵐ p ∂π, f p.1 + g p.2 ≤ ‖p.1 - p.2‖ ^ 2)
    (heq : (∫ p, ‖p.1 - p.2‖ ^ 2 ∂π) =
      (∫ x, f x ∂ρ) + ∫ y, g y ∂μ) :
    ∀ᵐ p ∂π, f p.1 + g p.2 = ‖p.1 - p.2‖ ^ 2 := by
  apply (integral_eq_iff_of_ae_le (dual_integrable_sum hπ hf hg) hc hbound).mp
  rw [dual_integral_sum hπ hf hg]
  exact heq.symm

/-- A saturated dual bound whose equality locus is a graph identifies the full plan. -/
theorem eq_graphPlan_of_dual_saturation
    {T : E d → E d} (hT : Measurable T)
    (hπ : IsCoupling ρ μ π) {f g : E d → ℝ}
    (hf : Integrable f ρ) (hg : Integrable g μ)
    (hc : Integrable (fun p : E d × E d => ‖p.1 - p.2‖ ^ 2) π)
    (hbound : ∀ᵐ p ∂π, f p.1 + g p.2 ≤ ‖p.1 - p.2‖ ^ 2)
    (heq : (∫ p, ‖p.1 - p.2‖ ^ 2 ∂π) =
      (∫ x, f x ∂ρ) + ∫ y, g y ∂μ)
    (hstrict : ∀ᵐ p ∂π,
      f p.1 + g p.2 = ‖p.1 - p.2‖ ^ 2 → p.2 = T p.1) :
    π = graphPlan ρ T := by
  apply eq_graph_map_of_fst_eq_and_ae_on_graph hT hπ.2.1
  filter_upwards [dual_saturation_of_integral_eq hπ hf hg hc hbound heq,
    hstrict] with p hp hs
  exact hs hp

/-- A dual value attained by a graph is nonnegative. -/
theorem dual_value_nonneg_of_graph
    {T : E d → E d} (hT : Measurable T) (hpush : Measure.map T ρ = μ)
    {f g : E d → ℝ} (hf : Integrable f ρ) (hg : Integrable g μ)
    (heq : ∀ᵐ x ∂ρ, ‖x - T x‖ ^ 2 = f x + g (T x)) :
    0 ≤ (∫ x, f x ∂ρ) + ∫ y, g y ∂μ := by
  have hg' : Integrable g (Measure.map T ρ) := hpush.symm ▸ hg
  have hgT : Integrable (fun x => g (T x)) ρ := hg'.comp_measurable hT
  rw [← hpush, integral_map hT.aemeasurable hg'.aestronglyMeasurable,
    ← integral_add hf hgT]
  apply integral_nonneg_of_ae
  filter_upwards [heq] with x hx
  rw [← hx]
  exact sq_nonneg _

/-- Strictness of a dual certificate identifies every optimal plan with its graph.
The strictness premise is only required almost everywhere for each coupling, so
null tie sets and support restrictions can be used directly. -/
theorem isUniqueQuadraticOptimalMap_of_dual
    {T : E d → E d} (hT : Measurable T) (hpush : Measure.map T ρ = μ)
    {f g : E d → ℝ} (hf : Integrable f ρ) (hg : Integrable g μ)
    (hbound : ∀ π : Measure (E d × E d), IsCoupling ρ μ π →
      ∀ᵐ p ∂π, f p.1 + g p.2 ≤ ‖p.1 - p.2‖ ^ 2)
    (heq : ∀ᵐ x ∂ρ, ‖x - T x‖ ^ 2 = f x + g (T x))
    (hstrict : ∀ π : Measure (E d × E d), IsCoupling ρ μ π →
      ∀ᵐ p ∂π, f p.1 + g p.2 = ‖p.1 - p.2‖ ^ 2 → p.2 = T p.1) :
    IsUniqueQuadraticOptimalMap ρ μ T := by
  have hopt := isQuadraticOptimalMap_of_dual hT hpush hf hg hbound heq
  refine ⟨hopt, fun π hπ hle => ?_⟩
  have hgraph := quadraticPlanCost_graph_eq_dual hT hpush hf hg heq
  have hfinite : quadraticPlanCost π ≠ ∞ := by
    apply ne_top_of_le_ne_top _ hle
    rw [hgraph]
    exact ENNReal.ofReal_ne_top
  have hc := integrable_sqdist_of_cost_ne_top hfinite
  have hcosteq : quadraticPlanCost π = quadraticPlanCost (graphPlan ρ T) :=
    le_antisymm hle (hopt.2.2 π hπ)
  have hvalue := dual_value_nonneg_of_graph hT hpush hf hg heq
  have hint : (∫ p, ‖p.1 - p.2‖ ^ 2 ∂π) =
      (∫ x, f x ∂ρ) + ∫ y, g y ∂μ := by
    have hh := (quadraticPlanCost_eq_ofReal_integral hc).symm.trans
      (hcosteq.trans hgraph)
    have hn : 0 ≤ ∫ p : E d × E d, ‖p.1 - p.2‖ ^ 2 ∂π :=
      integral_nonneg (fun p => sq_nonneg _)
    simpa only [ENNReal.toReal_ofReal hn, ENNReal.toReal_ofReal hvalue] using
      congrArg ENNReal.toReal hh
  exact eq_graphPlan_of_dual_saturation hT hπ hf hg hc (hbound π hπ)
    hint (hstrict π hπ)

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_AffineOptimality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace

namespace Problem358

variable {d : ℕ} {ι : Type*} [Fintype ι]
  {ρ : Measure (E d)} {T : E d → E d}

/-- An active finite-affine selection takes values in the finite site set almost everywhere. -/
theorem finiteAffine_map_ae_mem_range [Nonempty ι] (y : ι → E d) (c : ι → ℝ)
    (hT : Measurable T)
    (hactive : ∀ᵐ x ∂ρ, ∃ i, T x = y i ∧ FiniteAffine.Maximizes y c x i) :
    ∀ᵐ z ∂Measure.map T ρ, z ∈ Set.range y := by
  apply (ae_map_iff hT.aemeasurable (Set.finite_range y).measurableSet).mpr
  filter_upwards [hactive] with x hx
  obtain ⟨i, hi, _⟩ := hx
  exact ⟨i, hi.symm⟩

variable [Nonempty ι]

/-- The pointwise finite-affine dual estimate holds under every competing coupling. -/
theorem finiteAffine_coupling_dual_bound (y : ι → E d) (c : ι → ℝ)
    (hy : Function.Injective y) (hT : Measurable T)
    (hactive : ∀ᵐ x ∂ρ, ∃ i, T x = y i ∧ FiniteAffine.Maximizes y c x i)
    {π : Measure (E d × E d)} (hπ : IsCoupling ρ (Measure.map T ρ) π) :
    ∀ᵐ p ∂π, FiniteAffine.sourceDual y c p.1 +
      FiniteAffine.targetDual y c p.2 ≤ ‖p.1 - p.2‖ ^ 2 := by
  have hrange : ∀ᵐ p ∂π, p.2 ∈ Set.range y := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    rw [hπ.2.2]
    exact finiteAffine_map_ae_mem_range y c hT hactive
  exact hrange.mono fun p hp => FiniteAffine.dual_le_cost_on_range y c hy p.1 p.2 hp

/-- Under an absolutely continuous source, saturation of the finite-affine certificate
    forces every competing plan onto the selected graph. -/
theorem finiteAffine_dual_eq_implies_graph_ae
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hρ : ρ ≪ (volume : Measure (E d))) (hT : Measurable T)
    (hactive : ∀ᵐ x ∂ρ, ∃ i, T x = y i ∧ FiniteAffine.Maximizes y c x i)
    {π : Measure (E d × E d)} (hπ : IsCoupling ρ (Measure.map T ρ) π) :
    ∀ᵐ p ∂π, FiniteAffine.sourceDual y c p.1 +
      FiniteAffine.targetDual y c p.2 = ‖p.1 - p.2‖ ^ 2 → p.2 = T p.1 := by
  have htie : ∀ᵐ x ∂ρ, ∀ i j,
      ⟪x, y i⟫ + c i = ⟪x, y j⟫ + c j → y i = y j :=
    hρ.ae_le (ae_affine_tie_implies_slopes_eq volume y c)
  have hfst : ∀ᵐ p ∂π, (∃ i, T p.1 = y i ∧ FiniteAffine.Maximizes y c p.1 i) ∧
      (∀ i j, ⟪p.1, y i⟫ + c i = ⟪p.1, y j⟫ + c j → y i = y j) := by
    have h := hactive.and htie
    rw [← hπ.2.1] at h
    exact ae_of_ae_map measurable_fst.aemeasurable h
  have hsnd : ∀ᵐ p ∂π, p.2 ∈ Set.range y := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    rw [hπ.2.2]
    exact finiteAffine_map_ae_mem_range y c hT hactive
  filter_upwards [hfst, hsnd] with p hp hpy
  intro heq
  obtain ⟨i, hi, hmax⟩ := hp.1
  obtain ⟨j, hj⟩ := hpy
  have hjmax : FiniteAffine.Maximizes y c p.1 j := by
    apply (FiniteAffine.dual_eq_cost_on_range_iff y c hy p.1 j).mp
    simpa only [hj] using heq
  have hsites : y j = y i := hp.2 j i (le_antisymm (hmax j) (hjmax i))
  exact hj.symm.trans (hsites.trans hi.symm)

/-- Compact support makes the continuous source potential integrable. -/
theorem integrable_finiteAffine_sourceDual_of_compact
    [IsFiniteMeasure ρ] (y : ι → E d) (c : ι → ℝ)
    {K : Set (E d)} (hK : IsCompact K) (hρK : IsSupported ρ K) :
    Integrable (FiniteAffine.sourceDual y c) ρ := by
  have hae : ∀ᵐ x ∂ρ, x ∈ K := by
    rw [ae_iff]
    exact hρK
  have hi := ContinuousOn.integrableOn_compact hK
    (FiniteAffine.continuous_sourceDual y c).continuousOn (μ := ρ)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at hi

/-- The finite-affine construction gives uniqueness among all transport plans, not
    merely among maps, whenever the source is absolutely continuous. -/
theorem isUniqueQuadraticOptimalMap_of_finite_affine
    [IsProbabilityMeasure ρ] (y : ι → E d) (c : ι → ℝ)
    (hy : Function.Injective y) (hρ : ρ ≪ (volume : Measure (E d)))
    (hT : Measurable T) (hsource : Integrable (FiniteAffine.sourceDual y c) ρ)
    (hactive : ∀ᵐ x ∂ρ, ∃ i, T x = y i ∧ FiniteAffine.Maximizes y c x i) :
    IsUniqueQuadraticOptimalMap ρ (Measure.map T ρ) T := by
  let : IsProbabilityMeasure (Measure.map T ρ) := Measure.isProbabilityMeasure_map hT.aemeasurable
  apply isUniqueQuadraticOptimalMap_of_dual hT rfl hsource
    (FiniteAffine.integrable_targetDual y c (Measure.map T ρ))
  · intro π hπ
    exact finiteAffine_coupling_dual_bound y c hy hT hactive hπ
  · filter_upwards [hactive] with x hx
    obtain ⟨i, hi, hmax⟩ := hx
    rw [hi, FiniteAffine.targetDual_site y c hy i]
    exact (FiniteAffine.dual_eq_cost_of_maximizes y c x i hmax).symm
  · intro π hπ
    exact finiteAffine_dual_eq_implies_graph_ae y c hy hρ hT hactive hπ

/-- Compactly supported absolutely continuous probabilities admit the finite-affine
    optimality certificate without auxiliary integrability assumptions. -/
theorem isUniqueQuadraticOptimalMap_of_finite_affine_of_compact
    [IsProbabilityMeasure ρ] (y : ι → E d) (c : ι → ℝ)
    (hy : Function.Injective y) (hρ : ρ ≪ (volume : Measure (E d)))
    {K : Set (E d)} (hK : IsCompact K) (hρK : IsSupported ρ K)
    (hT : Measurable T)
    (hactive : ∀ᵐ x ∂ρ, ∃ i, T x = y i ∧ FiniteAffine.Maximizes y c x i) :
    IsUniqueQuadraticOptimalMap ρ (Measure.map T ρ) T :=
  isUniqueQuadraticOptimalMap_of_finite_affine y c hy hρ hT
    (integrable_finiteAffine_sourceDual_of_compact y c hK hρK) hactive

/-- Uniform compact-source specialization for the finite-affine maps used in sharpness. -/
theorem isUniqueQuadraticOptimalMap_uniform_of_finite_affine
    (K : Set (E d)) [IsProbabilityMeasure (uniformMeasure K)]
    (hK : IsCompact K) (y : ι → E d) (c : ι → ℝ)
    (hy : Function.Injective y) (hT : Measurable T)
    (hactive : ∀ᵐ x ∂uniformMeasure K,
      ∃ i, T x = y i ∧ FiniteAffine.Maximizes y c x i) :
    IsUniqueQuadraticOptimalMap (uniformMeasure K)
      (Measure.map T (uniformMeasure K)) T := by
  have hac : uniformMeasure K ≪ (volume : Measure (E d)) :=
    Measure.absolutelyContinuous_restrict.smul_left _
  have hs : IsSupported (uniformMeasure K) K := by
    simp [IsSupported, uniformMeasure, Measure.restrict_apply hK.measurableSet.compl]
  exact isUniqueQuadraticOptimalMap_of_finite_affine_of_compact y c hy hac hK hs hT hactive

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Argmax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Problem358

/-- Finite affine maxima have a globally measurable maximizing-slope map,
including on their tie sets. -/
theorem exists_measurable_affine_maximizer {V ι : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [Fintype ι] [Nonempty ι] (y : ι → V) (c : ι → ℝ) :
    ∃ T : V → V, Measurable T ∧ ∀ x, ∃ i,
      T x = y i ∧ ∀ j, ⟪y j, x⟫_ℝ + c j ≤ ⟪y i, x⟫_ℝ + c i := by
  classical
  let : MeasurableSpace ι := ⊤
  have hf (i : ι) : Measurable (fun x : V => ⟪y i, x⟫_ℝ + c i) := by
    fun_prop
  obtain ⟨g, hg, _, hmax⟩ := exists_measurable_argmax
    (fun i x => ⟪y i, x⟫_ℝ + c i) hf
  have hy : Measurable y := Measurable.of_discrete
  exact ⟨fun x => y (g x), hy.comp hg, fun x => ⟨g x, rfl, hmax x⟩⟩

end Problem358

end

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem358

/-- The law of a finite choice of prescribed values is determined by the choice-cell masses. -/
lemma map_finite_selector {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype ι]
    [MeasurableSingletonClass β] (ρ : Measure α) (s : α → ι)
    (hs : Measurable s) (y : ι → β) :
    Measure.map (fun x => y (s x)) ρ = ∑ i, ρ (s ⁻¹' {i}) • Measure.dirac (y i) := by
  have hy : Measurable y := measurable_of_countable y
  change Measure.map (y ∘ s) ρ = _
  rw [← Measure.map_map hy hs, Measure.map_eq_sum ρ s hs, Measure.sum_fintype,
    Measure.map_finset_sum hy.aemeasurable]
  simp only [Measure.map_smul, Measure.map_dirac]

/-- A version of `map_finite_selector` using supplied cell masses. -/
lemma map_finite_selector_of_masses {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype ι]
    [MeasurableSingletonClass β] (ρ : Measure α) (s : α → ι)
    (hs : Measurable s) (y : ι → β) (w : ι → ℝ≥0∞)
    (hw : ∀ i, ρ (s ⁻¹' {i}) = w i) :
    Measure.map (fun x => y (s x)) ρ = ∑ i, w i • Measure.dirac (y i) := by
  rw [map_finite_selector ρ s hs y]
  simp_rw [hw]

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_MaxCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology NNReal

namespace Problem358.FiniteMaxDerivative

variable {ι X : Type*} [Fintype ι] [Nonempty ι]

theorem le_maxValue (f : ι → X → ℝ) (i : ι) (x : X) :
    f i x ≤ maxValue f x :=
  Finset.le_sup' (fun j => f j x) (Finset.mem_univ i)

theorem maxValue_le {f : ι → X → ℝ} {x : X} {a : ℝ}
    (h : ∀ i, f i x ≤ a) : maxValue f x ≤ a :=
  Finset.sup'_le _ _ (fun i _ => h i)

/-- A strict active branch remains the maximum in a neighborhood. -/
theorem eventuallyEq_of_strict_max [TopologicalSpace X]
    {f : ι → X → ℝ} {x : X} {i : ι}
    (hc : ∀ j, ContinuousAt (f j) x)
    (hi : ∀ j, j ≠ i → f j x < f i x) :
    maxValue f =ᶠ[𝓝 x] f i := by
  have hnear : ∀ j, ∀ᶠ y in 𝓝 x, f j y ≤ f i y := by
    intro j
    by_cases hji : j = i
    · subst j
      exact Filter.Eventually.of_forall fun _ => le_rfl
    · exact ((hc j).eventually_lt (hc i) (hi j hji)).mono fun _ h => h.le
  filter_upwards [Filter.eventually_all.mpr hnear] with y hy
  exact le_antisymm (maxValue_le hy) (le_maxValue f i y)

/-- Differentiation of a finite maximum at a strict active branch. -/
theorem hasDerivAt_of_strict_max {f : ι → ℝ → ℝ} {x f' : ℝ} {i : ι}
    (hc : ∀ j, ContinuousAt (f j) x)
    (hi : ∀ j, j ≠ i → f j x < f i x)
    (hd : HasDerivAt (f i) f' x) : HasDerivAt (maxValue f) f' x := by
  exact hd.congr_of_eventuallyEq (eventuallyEq_of_strict_max hc hi)

/-- The same bound holds on any common time domain. -/
theorem lipschitzOnWith_maxValue [PseudoMetricSpace X]
    {f : ι → X → ℝ} {K : ℝ≥0} {s : Set X}
    (hf : ∀ i, LipschitzOnWith K (f i) s) :
    LipschitzOnWith K (maxValue f) s := by
  apply LipschitzOnWith.of_le_add_mul K
  intro x hx y hy
  apply maxValue_le
  intro i
  exact (hf i |>.le_add_mul hx hy).trans
    (add_le_add (le_maxValue f i y) le_rfl)

end Problem358.FiniteMaxDerivative

end

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Problem358

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- Injective moving affine slopes have jointly almost-everywhere distinct scores.
The joint conclusion is what is needed to integrate derivatives along time paths. -/
theorem ae_prod_injective_affine_scores (K : Set (E d))
    {τ : Measure ℝ} [SFinite (uniformMeasure K)]
    {y : ι → ℝ → E d} {c : ι → ℝ → ℝ}
    (hy : ∀ i, Measurable (y i)) (hc : ∀ i, Measurable (c i))
    (hinj : ∀ᵐ t ∂τ, Function.Injective (fun i => y i t)) :
    ∀ᵐ p ∂τ.prod (uniformMeasure K),
      Function.Injective (fun i => ⟪p.2, y i p.1⟫_ℝ + c i p.1) := by
  have hscore (i : ι) :
      Measurable (fun p : ℝ × E d => ⟪p.2, y i p.1⟫_ℝ + c i p.1) :=
    (measurable_snd.inner (hy i |>.comp measurable_fst)).add
      (hc i |>.comp measurable_fst)
  have hm : MeasurableSet {p : ℝ × E d |
      Function.Injective (fun i => ⟪p.2, y i p.1⟫_ℝ + c i p.1)} := by
    change MeasurableSet {p : ℝ × E d | ∀ i j,
      ⟪p.2, y i p.1⟫_ℝ + c i p.1 = ⟪p.2, y j p.1⟫_ℝ + c j p.1 → i = j}
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    by_cases hij : i = j
    · simp [hij]
    · simpa only [hij, imp_false, Set.compl_ofPred] using
        (measurableSet_eq_fun (hscore i) (hscore j)).compl
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  filter_upwards [hinj] with t ht
  filter_upwards [uniform_ae_affine_tie_implies_slopes_eq K
    (fun i => y i t) (fun i => c i t)] with x hx
  intro i j hij
  exact ht (hx i j hij)

/-- Any maximizing selector of moving affine scores is strictly active jointly a.e.
when the moving slopes are a.e. injective. -/
theorem ae_prod_strict_active_affine (K : Set (E d))
    {τ : Measure ℝ} [SFinite (uniformMeasure K)]
    {y : ι → ℝ → E d} {c : ι → ℝ → ℝ}
    (active : ℝ → E d → ι)
    (hy : ∀ i, Measurable (y i)) (hc : ∀ i, Measurable (c i))
    (hinj : ∀ᵐ t ∂τ, Function.Injective (fun i => y i t))
    (hactive : ∀ᵐ p ∂τ.prod (uniformMeasure K), ∀ j,
      ⟪p.2, y j p.1⟫_ℝ + c j p.1 ≤
        ⟪p.2, y (active p.1 p.2) p.1⟫_ℝ + c (active p.1 p.2) p.1) :
    ∀ᵐ p ∂τ.prod (uniformMeasure K), ∀ j, j ≠ active p.1 p.2 →
      ⟪p.2, y j p.1⟫_ℝ + c j p.1 <
        ⟪p.2, y (active p.1 p.2) p.1⟫_ℝ + c (active p.1 p.2) p.1 := by
  filter_upwards [ae_prod_injective_affine_scores K hy hc hinj, hactive] with p hp ha
  intro j hj
  exact lt_of_le_of_ne (ha j) (fun heq => hj (hp heq))

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_PotentialTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace Problem358.PotentialTimeIntegral

/-- Cauchy--Schwarz against the constant function, without real powers. -/
theorem sq_integral_le_mass_mul_integral_sq
    {T : Type*} [MeasurableSpace T] {ν : Measure T} [IsFiniteMeasure ν]
    {f : T → ℝ} (hmass : 0 < ν.real univ) (hf : Integrable f ν)
    (hf2 : Integrable (fun t => f t ^ 2) ν) :
    (∫ t, f t ∂ν) ^ 2 ≤ ν.real univ * ∫ t, f t ^ 2 ∂ν := by
  let m := ν.real univ
  let z := ∫ t, f t ∂ν
  have hnonneg : 0 ≤ ∫ t, (m * f t - z) ^ 2 ∂ν :=
    integral_nonneg (fun t => sq_nonneg _)
  have heq : (∫ t, (m * f t - z) ^ 2 ∂ν) =
      m ^ 2 * (∫ t, f t ^ 2 ∂ν) - (2 * m * z) * z + m * z ^ 2 := by
    calc
      _ = ∫ t, m ^ 2 * f t ^ 2 - (2 * m * z) * f t + z ^ 2 ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun t => by ring)
      _ = _ := by
        rw [integral_add (f := fun t => m ^ 2 * f t ^ 2 - (2 * m * z) * f t)
          (g := fun _ => z ^ 2) ((hf2.const_mul _).sub (hf.const_mul _)) (integrable_const _),
          integral_sub (f := fun t => m ^ 2 * f t ^ 2)
          (g := fun t => (2 * m * z) * f t) (hf2.const_mul _) (hf.const_mul _), integral_const_mul,
          integral_const_mul, integral_const]
        rfl
  rw [heq] at hnonneg
  have hm : 0 < m := hmass
  change z ^ 2 ≤ m * ∫ t, f t ^ 2 ∂ν
  nlinarith

/-- Spatial squared `L²` control for a pointwise time-integral representation. -/
theorem integral_sq_of_time_integral_le
    {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    {ν : Measure T} {μ : Measure X} [IsFiniteMeasure ν] [SFinite μ]
    {v : T → X → ℝ} {F : X → ℝ}
    (hmass : 0 < ν.real univ)
    (hv : Integrable (Function.uncurry v) (ν.prod μ))
    (hv2 : Integrable (fun p : T × X => v p.1 p.2 ^ 2) (ν.prod μ))
    (hF2 : Integrable (fun x => F x ^ 2) μ)
    (hF : ∀ᵐ x ∂μ, F x = ∫ t, v t x ∂ν) :
    (∫ x, F x ^ 2 ∂μ) ≤
      ν.real univ * ∫ t, ∫ x, v t x ^ 2 ∂μ ∂ν := by
  calc
    (∫ x, F x ^ 2 ∂μ) ≤
        ∫ x, ν.real univ * (∫ t, v t x ^ 2 ∂ν) ∂μ := by
      apply integral_mono_ae hF2 (hv2.integral_prod_right.const_mul _)
      filter_upwards [hF, hv.prod_left_ae, hv2.prod_left_ae] with x hx hvx hv2x
      rw [hx]
      exact sq_integral_le_mass_mul_integral_sq hmass hvx hv2x
    _ = ν.real univ * ∫ t, ∫ x, v t x ^ 2 ∂μ ∂ν := by
      rw [integral_const_mul, ← integral_integral_swap hv2]

/-- A uniform spatial `L²` speed bound integrates to a spatial `L²` displacement bound. -/
theorem sqrt_integral_sq_of_time_integral_le
    {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    {ν : Measure T} {μ : Measure X} [IsFiniteMeasure ν] [SFinite μ]
    {v : T → X → ℝ} {F : X → ℝ} {B : ℝ}
    (hmass : 0 < ν.real univ) (hB : 0 ≤ B)
    (hv : Integrable (Function.uncurry v) (ν.prod μ))
    (hv2 : Integrable (fun p : T × X => v p.1 p.2 ^ 2) (ν.prod μ))
    (hF2 : Integrable (fun x => F x ^ 2) μ)
    (hF : ∀ᵐ x ∂μ, F x = ∫ t, v t x ∂ν)
    (hspeed : ∀ᵐ t ∂ν, (∫ x, v t x ^ 2 ∂μ) ≤ B ^ 2) :
    Real.sqrt (∫ x, F x ^ 2 ∂μ) ≤ ν.real univ * B := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg hmass.le hB, ?_⟩
  calc
    (∫ x, F x ^ 2 ∂μ) ≤ ν.real univ * ∫ t, ∫ x, v t x ^ 2 ∂μ ∂ν :=
      integral_sq_of_time_integral_le hmass hv hv2 hF2 hF
    _ ≤ ν.real univ * ∫ _ : T, B ^ 2 ∂ν :=
      mul_le_mul_of_nonneg_left
        (integral_mono_ae hv2.integral_prod_left (integrable_const _) hspeed) hmass.le
    _ = (ν.real univ * B) ^ 2 := by
      rw [integral_const]
      simp only [smul_eq_mul]
      ring

/-- The time-interval form of the potential-path estimate, with an a.e. FTC identity. -/
theorem potential_path_L2_bound
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {u v : ℝ → X → ℝ} {s t B : ℝ} (hst : s < t) (hB : 0 ≤ B)
    (hv : Integrable (Function.uncurry v) ((volume.restrict (Ioc s t)).prod μ))
    (hv2 : Integrable (fun p : ℝ × X => v p.1 p.2 ^ 2)
      ((volume.restrict (Ioc s t)).prod μ))
    (hu2 : Integrable (fun x => (u t x - u s x) ^ 2) μ)
    (hFTC : ∀ᵐ x ∂μ, u t x - u s x = ∫ r in s..t, v r x)
    (hspeed : ∀ᵐ r ∂volume.restrict (Ioc s t), (∫ x, v r x ^ 2 ∂μ) ≤ B ^ 2) :
    Real.sqrt (∫ x, (u t x - u s x) ^ 2 ∂μ) ≤ B * (t - s) := by
  have hmass : (volume.restrict (Ioc s t)).real univ = t - s := by
    simp [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hst.le)]
  have hFTC' : ∀ᵐ x ∂μ, u t x - u s x = ∫ r, v r x ∂volume.restrict (Ioc s t) := by
    simpa only [intervalIntegral.integral_of_le hst.le] using hFTC
  have h := sqrt_integral_sq_of_time_integral_le
    (by rw [hmass]; exact sub_pos.mpr hst) hB hv hv2 hu2 hFTC' hspeed
  simpa only [hmass, mul_comm] using h

/-- The path estimate with FTC supplied by absolute continuity and an a.e. derivative.
The derivative hypothesis is joint in time and space, as in the finite-max construction. -/
theorem potential_path_L2_bound_of_absolutelyContinuous
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {u v : ℝ → X → ℝ} {s t B : ℝ} (hst : s < t) (hB : 0 ≤ B)
    (hv : Integrable (Function.uncurry v) ((volume.restrict (Ioc s t)).prod μ))
    (hv2 : Integrable (fun p : ℝ × X => v p.1 p.2 ^ 2)
      ((volume.restrict (Ioc s t)).prod μ))
    (hu2 : Integrable (fun x => (u t x - u s x) ^ 2) μ)
    (hu : ∀ᵐ x ∂μ, AbsolutelyContinuousOnInterval (fun r => u r x) s t)
    (hderiv : ∀ᵐ p ∂(volume.restrict (Ioc s t)).prod μ,
      HasDerivAt (fun r => u r p.2) (v p.1 p.2) p.1)
    (hspeed : ∀ᵐ r ∂volume.restrict (Ioc s t), (∫ x, v r x ^ 2 ∂μ) ≤ B ^ 2) :
    Real.sqrt (∫ x, (u t x - u s x) ^ 2 ∂μ) ≤ B * (t - s) := by
  apply potential_path_L2_bound hst hB hv hv2 hu2 ?_ hspeed
  have hswap : ∀ᵐ p ∂μ.prod (volume.restrict (Ioc s t)),
      HasDerivAt (fun r => u r p.1) (v p.2 p.1) p.2 :=
    (Measure.measurePreserving_swap (μ := μ)
      (ν := volume.restrict (Ioc s t))).quasiMeasurePreserving.ae hderiv
  filter_upwards [hu, Measure.ae_ae_of_ae_prod hswap] with x hx hdx
  calc
    u t x - u s x = ∫ r in s..t, deriv (fun r => u r x) r :=
      hx.integral_deriv_eq_sub.symm
    _ = ∫ r in s..t, v r x := by
      rw [intervalIntegral.integral_of_le hst.le, intervalIntegral.integral_of_le hst.le]
      apply integral_congr_ae
      exact hdx.mono (fun r hr => hr.deriv)

/-- A locally uniform Lipschitz bound in time is enough for the preceding theorem. -/
theorem potential_path_L2_bound_of_lipschitz
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {u v : ℝ → X → ℝ} {s t B : ℝ} (hst : s < t) (hB : 0 ≤ B)
    (hv : Integrable (Function.uncurry v) ((volume.restrict (Ioc s t)).prod μ))
    (hv2 : Integrable (fun p : ℝ × X => v p.1 p.2 ^ 2)
      ((volume.restrict (Ioc s t)).prod μ))
    (hu2 : Integrable (fun x => (u t x - u s x) ^ 2) μ)
    (hu : ∀ᵐ x ∂μ, ∃ L : ℝ≥0, LipschitzOnWith L (fun r => u r x) (Icc s t))
    (hderiv : ∀ᵐ p ∂(volume.restrict (Ioc s t)).prod μ,
      HasDerivAt (fun r => u r p.2) (v p.1 p.2) p.1)
    (hspeed : ∀ᵐ r ∂volume.restrict (Ioc s t), (∫ x, v r x ^ 2 ∂μ) ≤ B ^ 2) :
    Real.sqrt (∫ x, (u t x - u s x) ^ 2 ∂μ) ≤ B * (t - s) := by
  apply potential_path_L2_bound_of_absolutelyContinuous hst hB hv hv2 hu2 ?_ hderiv hspeed
  filter_upwards [hu] with x hx
  obtain ⟨L, hL⟩ := hx
  apply LipschitzOnWith.absolutelyContinuousOnInterval (K := L)
  simpa only [uIcc_of_le hst.le] using hL

end Problem358.PotentialTimeIntegral

end

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace Problem358.PotentialSpeed

/-- Integration over a finite measurable selector is the weighted sum over its fibers. -/
theorem integral_selector {X I : Type*} [MeasurableSpace X]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {μ : Measure X} [IsFiniteMeasure μ] {sel : X → I} (hsel : Measurable sel)
    (f : I → ℝ) :
    (∫ x, f (sel x) ∂μ) = ∑ i, μ.real {x | sel x = i} * f i := by
  have hf : Integrable f (Measure.map sel μ) := Integrable.of_finite
  rw [← integral_map hsel.aemeasurable hf.aestronglyMeasurable, integral_fintype hf]
  apply Finset.sum_congr rfl
  intro i hi
  have hset : sel ⁻¹' {i} = {x | sel x = i} := by ext x; simp
  simp only [measureReal_def, Measure.map_apply hsel (measurableSet_singleton i),
    hset, smul_eq_mul]

/-- Every real-valued finite-selector function is integrable on a finite measure. -/
theorem integrable_selector {X I : Type*} [MeasurableSpace X]
    [Finite I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {μ : Measure X} [IsFiniteMeasure μ] {sel : X → I} (hsel : Measurable sel)
    (f : I → ℝ) : Integrable (fun x => f (sel x)) μ := by
  exact (Integrable.of_finite (f := f) (μ := Measure.map sel μ)).comp_measurable hsel

/-- A pointwise speed bound with a harmless factor of two. -/
theorem affine_sq_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {x v : H} {r R : ℝ} (hx : ‖x‖ ≤ R) :
    (inner ℝ x v + r) ^ 2 ≤ 2 * R ^ 2 * ‖v‖ ^ 2 + 2 * r ^ 2 := by
  have hR : 0 ≤ R := (norm_nonneg x).trans hx
  have hab : |inner ℝ x v| ≤ R * ‖v‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) x v).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg v))
  have hs := (sq_le_sq₀ (abs_nonneg (inner ℝ x v))
    (mul_nonneg hR (norm_nonneg v))).mpr hab
  rw [sq_abs, mul_pow] at hs
  nlinarith [sq_nonneg (inner ℝ x v - r)]

/-- Weighted cellwise integration of the time derivative of a finite affine maximum. -/
theorem integral_affine_speed_sq_le
    {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {μ : Measure H} [IsFiniteMeasure μ] {sel : H → I} (hsel : Measurable sel)
    (v : I → H) (r : I → ℝ) {R : ℝ}
    (hR : ∀ᵐ x ∂μ, ‖x‖ ≤ R)
    (hint : Integrable (fun x => (inner ℝ x (v (sel x)) + r (sel x)) ^ 2) μ) :
    (∫ x, (inner ℝ x (v (sel x)) + r (sel x)) ^ 2 ∂μ) ≤
      2 * R ^ 2 * (∑ i, μ.real {x | sel x = i} * ‖v i‖ ^ 2) +
        2 * (∑ i, μ.real {x | sel x = i} * r i ^ 2) := by
  calc
    (∫ x, (inner ℝ x (v (sel x)) + r (sel x)) ^ 2 ∂μ) ≤
        ∫ x, 2 * R ^ 2 * ‖v (sel x)‖ ^ 2 + 2 * r (sel x) ^ 2 ∂μ := by
      apply integral_mono_ae hint (integrable_selector hsel
        (fun i => 2 * R ^ 2 * ‖v i‖ ^ 2 + 2 * r i ^ 2))
      exact hR.mono (fun x hx => affine_sq_le hx)
    _ = _ := by
      rw [integral_selector hsel (fun i => 2 * R ^ 2 * ‖v i‖ ^ 2 + 2 * r i ^ 2)]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro i hi
        ring
      · apply Finset.sum_congr rfl
        intro i hi
        ring

/-- A bounded source and a measurable finite selector give the required square integrability. -/
theorem integrable_affine_speed_sq
    {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [OpensMeasurableSpace H] [SecondCountableTopology H]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {μ : Measure H} [IsFiniteMeasure μ] {sel : H → I} (hsel : Measurable sel)
    (v : I → H) (r : I → ℝ) {R : ℝ} (hR : ∀ᵐ x ∂μ, ‖x‖ ≤ R) :
    Integrable (fun x => (inner ℝ x (v (sel x)) + r (sel x)) ^ 2) μ := by
  have hmeas : Measurable (fun x => (inner ℝ x (v (sel x)) + r (sel x)) ^ 2) :=
    ((measurable_id.inner ((measurable_of_finite v).comp hsel)).add
      ((measurable_of_finite r).comp hsel)).pow_const 2
  apply (integrable_selector hsel
    (fun i => 2 * R ^ 2 * ‖v i‖ ^ 2 + 2 * r i ^ 2)).mono' hmeas.aestronglyMeasurable
  filter_upwards [hR] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (inner ℝ x (v (sel x)) + r (sel x)))] using
    (affine_sq_le (v := v (sel x)) (r := r (sel x)) hx)

/-- From the coupling and intercept energy bounds to the spatial potential speed bound.
The constant is non-sharp, which is sufficient for one-third stability. -/
theorem integral_affine_speed_sq_le_of_energy
    {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [OpensMeasurableSpace H] [SecondCountableTopology H]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {μ : Measure H} [IsFiniteMeasure μ] {sel : H → I} (hsel : Measurable sel)
    (v : I → H) (r m : I → ℝ) {R w k : ℝ}
    (hR : ∀ᵐ x ∂μ, ‖x‖ ≤ R)
    (hm : ∀ i, μ.real {x | sel x = i} = m i)
    (hv : (∑ i, m i * ‖v i‖ ^ 2) ≤ w ^ 2)
    (hr : (∑ i, m i * r i ^ 2) ≤ k * R ^ 2 * w ^ 2) :
    (∫ x, (inner ℝ x (v (sel x)) + r (sel x)) ^ 2 ∂μ) ≤
      2 * (1 + k) * R ^ 2 * w ^ 2 := by
  have h := integral_affine_speed_sq_le hsel v r hR
    (integrable_affine_speed_sq hsel v r hR)
  simp_rw [hm] at h
  calc
    (∫ x, (inner ℝ x (v (sel x)) + r (sel x)) ^ 2 ∂μ) ≤
        2 * R ^ 2 * (∑ i, m i * ‖v i‖ ^ 2) + 2 * (∑ i, m i * r i ^ 2) := h
    _ ≤ 2 * R ^ 2 * w ^ 2 + 2 * (k * R ^ 2 * w ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hv (by positivity))
        (mul_le_mul_of_nonneg_left hr (by positivity))
    _ = _ := by ring

end Problem358.PotentialSpeed

end

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace Problem358.FiniteMaxDerivative

variable {ι X : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace X]

omit [Nonempty ι] in
/-- Selecting a measurable member of a finite measurable family stays measurable. -/
theorem measurable_selected (g : ι → X → ℝ) (k : X → ι)
    (hg : ∀ i, Measurable (g i)) (hk : ∀ i, MeasurableSet {x | k x = i}) :
    Measurable (fun x => g (k x) x) := by
  classical
  have h : Measurable (fun x => ∑ i, {x | k x = i}.indicator (g i) x) := by
    exact Finset.measurable_sum _ (fun i _ => (hg i).indicator (hk i))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp [Set.indicator_apply]

/-- Endpoint values of the finite maximum are measurable. -/
theorem measurable_maxValue (f : ι → X → ℝ) (hf : ∀ i, Measurable (f i)) :
    Measurable (maxValue f) := by
  have h : Measurable (Finset.univ.sup' Finset.univ_nonempty f) := by
    exact Finset.sup'_induction Finset.univ_nonempty f
      (p := fun g : X → ℝ => Measurable g)
      (fun g hg h hh => hg.sup hh) (fun i _ => hf i)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  exact (Finset.sup'_apply Finset.univ_nonempty f x).symm

/-- A finite maximum inherits the spatial `L²` time bound from its active-branch speed.
All integrability and pointwise FTC obligations are discharged by measurability and uniform bounds. -/
theorem finite_max_path_L2_bound
    {μ : Measure X} [IsFiniteMeasure μ] {a b B D : ℝ} {L : ℝ≥0}
    (f g : ι → ℝ × X → ℝ) (k : ℝ × X → ι)
    (hab : a < b) (hB : 0 ≤ B)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hk : ∀ i, MeasurableSet {p | k p = i})
    (hLip : ∀ᵐ x ∂μ, ∀ i, LipschitzOnWith L (fun r => f i (r, x)) (Icc a b))
    (hderiv : ∀ᵐ p ∂(volume.restrict (Ioc a b)).prod μ, ∀ i,
      HasDerivAt (fun r => f i (r, p.2)) (g i p) p.1)
    (hstrict : ∀ᵐ p ∂(volume.restrict (Ioc a b)).prod μ, ∀ j, j ≠ k p →
      f j p < f (k p) p)
    (hbound : ∀ᵐ p ∂(volume.restrict (Ioc a b)).prod μ, ‖g (k p) p‖ ≤ D)
    (hspeed : ∀ᵐ r ∂volume.restrict (Ioc a b),
      (∫ x, g (k (r, x)) (r, x) ^ 2 ∂μ) ≤ B ^ 2) :
    Real.sqrt (∫ x, (finiteMax (fun i => f i (b, x)) -
      finiteMax (fun i => f i (a, x))) ^ 2 ∂μ) ≤ B * (b - a) := by
  let u : ℝ → X → ℝ := fun r x => finiteMax (fun i => f i (r, x))
  let w : ℝ → X → ℝ := fun r x => g (k (r, x)) (r, x)
  have hwmeas : Measurable (Function.uncurry w) := measurable_selected g k hg hk
  have hw : Integrable (Function.uncurry w) ((volume.restrict (Ioc a b)).prod μ) :=
    Integrable.of_bound hwmeas.aestronglyMeasurable D hbound
  have hw2 : Integrable (fun p : ℝ × X => w p.1 p.2 ^ 2)
      ((volume.restrict (Ioc a b)).prod μ) := by
    apply Integrable.of_bound (hwmeas.pow_const 2).aestronglyMeasurable (D ^ 2)
    filter_upwards [hbound] with p hp
    change ‖g (k p) p ^ 2‖ ≤ D ^ 2
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hp 2
  have humeas (r : ℝ) : Measurable (u r) := by
    exact measurable_maxValue (fun i x => f i (r, x))
      (fun i => (hf i).comp (measurable_const.prodMk measurable_id))
  have huLip : ∀ᵐ x ∂μ, LipschitzOnWith L (fun r => u r x) (Icc a b) := by
    filter_upwards [hLip] with x hx
    exact lipschitzOnWith_maxValue hx
  have hu2 : Integrable (fun x => (u b x - u a x) ^ 2) μ := by
    apply Integrable.of_bound ((humeas b).sub (humeas a) |>.pow_const 2).aestronglyMeasurable
      (((L : ℝ) * (b - a)) ^ 2)
    filter_upwards [huLip] with x hx
    have hh := hx.dist_le_mul b (right_mem_Icc.mpr hab.le) a (left_mem_Icc.mpr hab.le)
    have hh' : ‖u b x - u a x‖ ≤ (L : ℝ) * (b - a) := by
      simpa only [Real.dist_eq, abs_of_pos (sub_pos.mpr hab), Real.norm_eq_abs] using hh
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hh' 2
  apply PotentialTimeIntegral.potential_path_L2_bound_of_lipschitz
    hab hB hw hw2 hu2
  · exact huLip.mono fun x hx => ⟨L, hx⟩
  · filter_upwards [hderiv, hstrict] with p hp hs
    exact hasDerivAt_of_strict_max (fun i => (hp i).continuousAt) hs (hp (k p))
  · exact hspeed

end Problem358.FiniteMaxDerivative

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_AffinePaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace NNReal BigOperators

namespace Problem358

/-- Quantitative time stability for a genuine finite affine maximum with fixed cell
masses.  Null ties, time regularity, square integrability, and the fundamental theorem
are derived from the stated coefficient data rather than assumed for the potential. -/
theorem finite_affine_path_L2_bound
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (K : Set (E d)) [IsFiniteMeasure (uniformMeasure K)]
    (y v : ι → ℝ → E d) (c r : ι → ℝ → ℝ)
    (active : ℝ × E d → ι) (m : ι → ℝ)
    {a b w κ : ℝ} {R A B : ℝ≥0}
    (hab : a < b) (hw : 0 ≤ w) (hκ : 0 ≤ κ)
    (hxR : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hy : ∀ i, Measurable (y i)) (hc : ∀ i, Measurable (c i))
    (hv : ∀ i, Measurable (v i)) (hr : ∀ i, Measurable (r i))
    (hactiveMeas : Measurable active)
    (hdy : ∀ i q, q ∈ Icc a b → HasDerivAt (y i) (v i q) q)
    (hdc : ∀ i q, q ∈ Icc a b → HasDerivAt (c i) (r i q) q)
    (hvBound : ∀ i q, q ∈ Icc a b → ‖v i q‖ ≤ A)
    (hrBound : ∀ i q, q ∈ Icc a b → ‖r i q‖ ≤ B)
    (hinj : ∀ᵐ q ∂volume.restrict (Ioc a b), Function.Injective (fun i => y i q))
    (hactive : ∀ᵐ p ∂(volume.restrict (Ioc a b)).prod (uniformMeasure K), ∀ j,
      ⟪p.2, y j p.1⟫_ℝ + c j p.1 ≤
        ⟪p.2, y (active p) p.1⟫_ℝ + c (active p) p.1)
    (hm : ∀ q ∈ Ioc a b, ∀ i,
      (uniformMeasure K).real {x | active (q, x) = i} = m i)
    (hvEnergy : ∀ q ∈ Ioc a b, (∑ i, m i * ‖v i q‖ ^ 2) ≤ w ^ 2)
    (hrEnergy : ∀ q ∈ Ioc a b, (∑ i, m i * r i q ^ 2) ≤ κ * (R : ℝ) ^ 2 * w ^ 2) :
    Real.sqrt (∫ x,
      (FiniteMaxDerivative.maxValue (fun i q => ⟪x, y i q⟫_ℝ + c i q) b -
        FiniteMaxDerivative.maxValue (fun i q => ⟪x, y i q⟫_ℝ + c i q) a) ^ 2
      ∂uniformMeasure K) ≤ (Real.sqrt (2 * (1 + κ)) * R * w) * (b - a) := by
  let f : ι → ℝ × E d → ℝ := fun i p => ⟪p.2, y i p.1⟫_ℝ + c i p.1
  let g : ι → ℝ × E d → ℝ := fun i p => ⟪p.2, v i p.1⟫_ℝ + r i p.1
  have hf (i : ι) : Measurable (f i) :=
    (measurable_snd.inner (hy i |>.comp measurable_fst)).add
      (hc i |>.comp measurable_fst)
  have hg (i : ι) : Measurable (g i) :=
    (measurable_snd.inner (hv i |>.comp measurable_fst)).add
      (hr i |>.comp measurable_fst)
  have hd (i : ι) (q : ℝ) (hq : q ∈ Icc a b) (x : E d) :
      HasDerivAt (fun t => f i (t, x)) (g i (q, x)) q := by
    convert ((hasDerivAt_const q x).inner ℝ (hdy i q hq)).add (hdc i q hq) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [inner_zero_left, add_zero]
    rfl
  have hbound (i : ι) (q : ℝ) (hq : q ∈ Icc a b) (x : E d) (hx : ‖x‖ ≤ R) :
      ‖g i (q, x)‖ ≤ (R : ℝ) * A + B := by
    calc
      ‖g i (q, x)‖ ≤ ‖⟪x, v i q⟫_ℝ‖ + ‖r i q‖ := norm_add_le _ _
      _ ≤ ‖x‖ * ‖v i q‖ + ‖r i q‖ := add_le_add (norm_inner_le_norm _ _) le_rfl
      _ ≤ (R : ℝ) * A + B := by
        gcongr
        · exact hvBound i q hq
        · exact hrBound i q hq
  have hLip : ∀ᵐ x ∂uniformMeasure K, ∀ i,
      LipschitzOnWith (R * A + B) (fun q => f i (q, x)) (Icc a b) := by
    filter_upwards [hxR] with x hx
    intro i
    apply (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun q hq => (hd i q hq x).hasDerivWithinAt)
    intro q hq
    change ‖g i (q, x)‖ ≤ (↑(R * A + B) : ℝ)
    simpa only [NNReal.coe_add, NNReal.coe_mul] using hbound i q hq x hx
  have htime : ∀ᵐ p : ℝ × E d ∂(volume.restrict (Ioc a b)).prod (uniformMeasure K),
      p.1 ∈ Ioc a b :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  have hspace : ∀ᵐ p : ℝ × E d ∂(volume.restrict (Ioc a b)).prod (uniformMeasure K),
      ‖p.2‖ ≤ R := Measure.quasiMeasurePreserving_snd.ae hxR
  have hderiv : ∀ᵐ p ∂(volume.restrict (Ioc a b)).prod (uniformMeasure K), ∀ i,
      HasDerivAt (fun q => f i (q, p.2)) (g i p) p.1 := by
    filter_upwards [htime] with p hp
    exact fun i => hd i p.1 (Ioc_subset_Icc_self hp) p.2
  have hstrict : ∀ᵐ p ∂(volume.restrict (Ioc a b)).prod (uniformMeasure K), ∀ j,
      j ≠ active p → f j p < f (active p) p :=
    ae_prod_strict_active_affine K (fun q x => active (q, x)) hy hc hinj hactive
  have hfullbound : ∀ᵐ p ∂(volume.restrict (Ioc a b)).prod (uniformMeasure K),
      ‖g (active p) p‖ ≤ (R : ℝ) * A + B := by
    filter_upwards [htime, hspace] with p hp hx
    exact hbound (active p) p.1 (Ioc_subset_Icc_self hp) p.2 hx
  have hspeed : ∀ᵐ q ∂volume.restrict (Ioc a b),
      (∫ x, g (active (q, x)) (q, x) ^ 2 ∂uniformMeasure K) ≤
        (Real.sqrt (2 * (1 + κ)) * R * w) ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
    have hsel : Measurable (fun x => active (q, x)) :=
      hactiveMeas.comp (measurable_const.prodMk measurable_id)
    have hh := PotentialSpeed.integral_affine_speed_sq_le_of_energy
      hsel (fun i => v i q) (fun i => r i q) m hxR (hm q hq)
      (hvEnergy q hq) (hrEnergy q hq)
    have hsquare : (Real.sqrt (2 * (1 + κ)) * R * w) ^ 2 =
        2 * (1 + κ) * (R : ℝ) ^ 2 * w ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    rw [hsquare]
    exact hh
  exact FiniteMaxDerivative.finite_max_path_L2_bound f g active hab (by positivity)
    hf hg (fun i => hactiveMeas (measurableSet_singleton i)) hLip hderiv hstrict
    hfullbound hspeed

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators RealInnerProductSpace

namespace Problem358.FiniteAffine

variable {I F : Type*} [Fintype I] [Nonempty I]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Uniform comparison of finite affine maxima, without any uniqueness of
active indices or separation of the sites. -/
theorem abs_potential_sub_le_coefficients (y z : I → F) (c b : I → ℝ)
    {R : ℝ} (hR : 0 ≤ R) {x : F} (hx : ‖x‖ ≤ R) :
    |potential y c x - potential z b x| ≤
      R * ∑ i, ‖y i - z i‖ + ∑ i, |c i - b i| := by
  classical
  let e := R * ∑ i, ‖y i - z i‖ + ∑ i, |c i - b i|
  have hscore (i : I) :
      |(⟪x, y i⟫ + c i) - (⟪x, z i⟫ + b i)| ≤ e := by
    have hy : ‖y i - z i‖ ≤ ∑ j, ‖y j - z j‖ :=
      Finset.single_le_sum (fun j _ => norm_nonneg (y j - z j)) (Finset.mem_univ i)
    have hc : |c i - b i| ≤ ∑ j, |c j - b j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (c j - b j)) (Finset.mem_univ i)
    calc
      _ = |⟪x, y i - z i⟫ + (c i - b i)| := by
        congr 1
        rw [inner_sub_right]
        ring
      _ ≤ |⟪x, y i - z i⟫| + |c i - b i| := abs_add_le _ _
      _ ≤ R * (∑ j, ‖y j - z j‖) + ∑ j, |c j - b j| := by
        apply add_le_add _ hc
        exact (abs_real_inner_le_norm _ _).trans
          ((mul_le_mul_of_nonneg_right hx (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_left hy hR))
  have hr : potential y c x ≤ potential z b x + e := by
    apply potential_le_of_affine_le
    intro i
    have hi := affine_le_potential z b x i
    have hs := (abs_le.mp (hscore i)).2
    linarith
  have hl : potential z b x ≤ potential y c x + e := by
    apply potential_le_of_affine_le
    intro i
    have hi := affine_le_potential y c x i
    have hs := (abs_le.mp (hscore i)).1
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

variable [MeasurableSpace F] (μ : Measure F) [IsFiniteMeasure μ]

/-- Coefficient convergence gives scalar L² convergence on every finite
bounded source.  Arbitrary filters are allowed, including both endpoint
filters; repeated limiting sites cause no issue. -/
theorem tendsto_integral_potential_sub_sq
    {A : Type*} {l : Filter A} {y : A → I → F} {c : A → I → ℝ}
    {z : I → F} {b : I → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hx : ∀ᵐ x ∂μ, ‖x‖ ≤ R)
    (hy : ∀ i, Tendsto (fun t => y t i) l (𝓝 (z i)))
    (hc : ∀ i, Tendsto (fun t => c t i) l (𝓝 (b i))) :
    Tendsto (fun t => ∫ x, (potential (y t) (c t) x - potential z b x) ^ 2 ∂μ)
      l (𝓝 0) := by
  classical
  let e : A → ℝ := fun t => R * ∑ i, ‖y t i - z i‖ + ∑ i, |c t i - b i|
  have hyl (i : I) : Tendsto (fun t => ‖y t i - z i‖) l (𝓝 0) := by
    simpa only [sub_self, norm_zero] using ((hy i).sub (tendsto_const_nhds (x := z i))).norm
  have hcl (i : I) : Tendsto (fun t => |c t i - b i|) l (𝓝 0) := by
    simpa only [sub_self, abs_zero] using ((hc i).sub (tendsto_const_nhds (x := b i))).abs
  have hel : Tendsto e l (𝓝 0) := by
    simpa [e] using ((tendsto_finsetSum Finset.univ (fun i _ => hyl i)).const_mul R).add
      (tendsto_finsetSum Finset.univ (fun i _ => hcl i))
  have hbound (t : A) :
      (∫ x, (potential (y t) (c t) x - potential z b x) ^ 2 ∂μ) ≤
        μ.real Set.univ * e t ^ 2 := by
    have hb : ∀ᵐ x ∂μ,
        (potential (y t) (c t) x - potential z b x) ^ 2 ≤ e t ^ 2 := by
      filter_upwards [hx] with x hx
      have he := abs_potential_sub_le_coefficients (y t) z (c t) b hR hx
      have he0 : 0 ≤ e t := by dsimp [e]; positivity
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) he0).mpr he
    have hi := integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x => sq_nonneg
        (potential (y t) (c t) x - potential z b x)) (integrable_const (e t ^ 2)) hb
    simpa only [integral_const, smul_eq_mul] using hi
  apply squeeze_zero (fun t => integral_nonneg fun x => sq_nonneg _) hbound
  simpa using (hel.pow 2).const_mul (μ.real Set.univ)

/-- Norm-form endpoint convergence of the finite affine potentials. -/
theorem tendsto_sqrt_integral_potential_sub_sq
    {A : Type*} {l : Filter A} {y : A → I → F} {c : A → I → ℝ}
    {z : I → F} {b : I → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hx : ∀ᵐ x ∂μ, ‖x‖ ≤ R)
    (hy : ∀ i, Tendsto (fun t => y t i) l (𝓝 (z i)))
    (hc : ∀ i, Tendsto (fun t => c t i) l (𝓝 (b i))) :
    Tendsto (fun t => Real.sqrt
      (∫ x, (potential (y t) (c t) x - potential z b x) ^ 2 ∂μ)) l (𝓝 0) := by
  simpa only [Real.sqrt_zero] using
    (tendsto_integral_potential_sub_sq μ hR hx hy hc).sqrt

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [IsFiniteMeasure μ] in
/-- The scalar square-root energy is the genuine L² metric. -/
theorem sqrt_integral_sub_sq_eq_dist {f g : F → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Real.sqrt (∫ x, (f x - g x) ^ 2 ∂μ) =
      dist (hf.toLp f) (hg.toLp g) := by
  rw [Lp.dist_edist, Lp.edist_toLp_toLp, toReal_eLpNorm (hf.sub hg).aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      (hf.sub hg).aestronglyMeasurable]
  simp [Real.sqrt_eq_rpow, Real.norm_eq_abs]

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [IsFiniteMeasure μ] in
/-- L² convergence of both endpoints preserves their scalar L² distance. -/
theorem tendsto_sqrt_integral_pair_sub_sq
    {A : Type*} {l : Filter A} {u v : A → F → ℝ} {u₀ v₀ : F → ℝ}
    (hu : ∀ t, MemLp (u t) 2 μ) (hv : ∀ t, MemLp (v t) 2 μ)
    (hu₀ : MemLp u₀ 2 μ) (hv₀ : MemLp v₀ 2 μ)
    (hul : Tendsto (fun t => Real.sqrt (∫ x, (u t x - u₀ x) ^ 2 ∂μ)) l (𝓝 0))
    (hvl : Tendsto (fun t => Real.sqrt (∫ x, (v t x - v₀ x) ^ 2 ∂μ)) l (𝓝 0)) :
    Tendsto (fun t => Real.sqrt (∫ x, (u t x - v t x) ^ 2 ∂μ))
      l (𝓝 (Real.sqrt (∫ x, (u₀ x - v₀ x) ^ 2 ∂μ))) := by
  have huLp : Tendsto (fun t => (hu t).toLp (u t)) l (𝓝 (hu₀.toLp u₀)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [← sqrt_integral_sub_sq_eq_dist] using hul
  have hvLp : Tendsto (fun t => (hv t).toLp (v t)) l (𝓝 (hv₀.toLp v₀)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [← sqrt_integral_sub_sq_eq_dist] using hvl
  simpa only [← sqrt_integral_sub_sq_eq_dist] using huLp.dist hvLp

variable [BorelSpace F]

/-- Finite affine potentials are in L² on every finite bounded source. -/
theorem memLp_potential_of_ae_norm_le (y : I → F) (c : I → ℝ)
    {R : ℝ} (hR : 0 ≤ R) (hx : ∀ᵐ x ∂μ, ‖x‖ ≤ R) :
    MemLp (potential y c) 2 μ := by
  apply MemLp.of_bound (continuous_potential y c).aestronglyMeasurable
    (R * ∑ i, ‖y i‖ + ∑ i, |c i|)
  filter_upwards [hx] with x hx
  have h := abs_potential_sub_le_coefficients y (fun _ => 0) c (fun _ => 0) hR hx
  simpa [Real.norm_eq_abs, potential] using h

/-- Endpoint coefficients alone suffice for continuity of the distance
between two finite affine potentials. -/
theorem tendsto_sqrt_integral_potential_pair_sub_sq
    {A : Type*} {l : Filter A}
    {y z : A → I → F} {c b : A → I → ℝ}
    {y₀ z₀ : I → F} {c₀ b₀ : I → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hx : ∀ᵐ x ∂μ, ‖x‖ ≤ R)
    (hy : ∀ i, Tendsto (fun t => y t i) l (𝓝 (y₀ i)))
    (hc : ∀ i, Tendsto (fun t => c t i) l (𝓝 (c₀ i)))
    (hz : ∀ i, Tendsto (fun t => z t i) l (𝓝 (z₀ i)))
    (hb : ∀ i, Tendsto (fun t => b t i) l (𝓝 (b₀ i))) :
    Tendsto (fun t => Real.sqrt
      (∫ x, (potential (y t) (c t) x - potential (z t) (b t) x) ^ 2 ∂μ))
      l (𝓝 (Real.sqrt (∫ x, (potential y₀ c₀ x - potential z₀ b₀ x) ^ 2 ∂μ))) := by
  exact tendsto_sqrt_integral_pair_sub_sq μ
    (fun t => memLp_potential_of_ae_norm_le μ (y t) (c t) hR hx)
    (fun t => memLp_potential_of_ae_norm_le μ (z t) (b t) hR hx)
    (memLp_potential_of_ae_norm_le μ y₀ c₀ hR hx)
    (memLp_potential_of_ae_norm_le μ z₀ b₀ hR hx)
    (tendsto_sqrt_integral_potential_sub_sq μ hR hx hy hc)
    (tendsto_sqrt_integral_potential_sub_sq μ hR hx hz hb)

end Problem358.FiniteAffine

end

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal BigOperators RealInnerProductSpace

namespace Problem358

/-- An interior time estimate for finite affine potentials passes to both
endpoints using only continuity of the coefficients.  Sites may collide at
 either endpoint. -/
theorem finite_affine_path_endpoint_bound
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (K : Set (E d)) [IsFiniteMeasure (uniformMeasure K)]
    (y : ι → ℝ → E d) (c : ι → ℝ → ℝ) {R L : ℝ}
    (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hxR : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hy : ∀ i, Continuous (y i)) (hc : ∀ i, Continuous (c i))
    (hinterior : ∀ a b : ℝ, 0 < a → a < b → b < 1 →
      Real.sqrt (∫ x,
        (FiniteAffine.potential (fun i => y i b) (fun i => c i b) x -
         FiniteAffine.potential (fun i => y i a) (fun i => c i a) x) ^ 2
        ∂uniformMeasure K) ≤ L * (b - a)) :
    Real.sqrt (∫ x,
      (FiniteAffine.potential (fun i => y i 1) (fun i => c i 1) x -
       FiniteAffine.potential (fun i => y i 0) (fun i => c i 0) x) ^ 2
      ∂uniformMeasure K) ≤ L := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hot : Tendsto (fun t : ℝ => 1 - t) (𝓝[>] 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub ht
  have hlim := FiniteAffine.tendsto_sqrt_integral_potential_pair_sub_sq
    (uniformMeasure K) hR hxR
    (fun i => (hy i).continuousAt.tendsto.comp hot)
    (fun i => (hc i).continuousAt.tendsto.comp hot)
    (fun i => (hy i).continuousAt.tendsto.comp ht)
    (fun i => (hc i).continuousAt.tendsto.comp ht)
  apply le_of_tendsto hlim
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 / 2 :=
    ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht0 ht1
  have htpos : 0 < t := ht0
  exact (hinterior t (1 - t) htpos (by linarith) (by linarith)).trans
    (mul_le_of_le_one_right hL (by linarith))

/-- A finite C¹ fixed-mass path on the open time interval has the full
endpoint estimate. Derivatives need neither exist nor stay bounded near
endpoints; continuity of the endpoint coefficients is sufficient. -/
theorem finite_affine_C1_path_endpoint_L2_bound
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (K : Set (E d)) [IsFiniteMeasure (uniformMeasure K)]
    (y v : ι → ℝ → E d) (c r : ι → ℝ → ℝ)
    (active : ℝ × E d → ι) (m : ι → ℝ)
    {w κ : ℝ} {R : ℝ≥0} (hw : 0 ≤ w) (hκ : 0 ≤ κ)
    (hxR : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hy : ∀ i, Continuous (y i)) (hc : ∀ i, Continuous (c i))
    (hv : ∀ i, ContinuousOn (v i) (Ioo 0 1))
    (hr : ∀ i, ContinuousOn (r i) (Ioo 0 1))
    (hactiveMeas : Measurable active)
    (hdy : ∀ i q, q ∈ Ioo 0 1 → HasDerivAt (y i) (v i q) q)
    (hdc : ∀ i q, q ∈ Ioo 0 1 → HasDerivAt (c i) (r i q) q)
    (hinj : ∀ q ∈ Ioo 0 1, Function.Injective (fun i => y i q))
    (hactive : ∀ q ∈ Ioo 0 1, ∀ x j,
      ⟪x, y j q⟫ + c j q ≤
        ⟪x, y (active (q, x)) q⟫ + c (active (q, x)) q)
    (hm : ∀ q ∈ Ioo 0 1, ∀ i,
      (uniformMeasure K).real {x | active (q, x) = i} = m i)
    (hvEnergy : ∀ q ∈ Ioo 0 1, (∑ i, m i * ‖v i q‖ ^ 2) ≤ w ^ 2)
    (hrEnergy : ∀ q ∈ Ioo 0 1, (∑ i, m i * r i q ^ 2) ≤ κ * (R : ℝ) ^ 2 * w ^ 2) :
    Real.sqrt (∫ x,
      (FiniteAffine.potential (fun i => y i 1) (fun i => c i 1) x -
       FiniteAffine.potential (fun i => y i 0) (fun i => c i 0) x) ^ 2
      ∂uniformMeasure K) ≤ Real.sqrt (2 * (1 + κ)) * R * w := by
  classical
  let v' : ι → ℝ → E d := fun i => (Ioo 0 1).piecewise (v i) (fun _ => 0)
  let r' : ι → ℝ → ℝ := fun i => (Ioo 0 1).piecewise (r i) (fun _ => 0)
  have hv'Meas (i : ι) : Measurable (v' i) :=
    (hv i).measurable_piecewise continuousOn_const measurableSet_Ioo
  have hr'Meas (i : ι) : Measurable (r' i) :=
    (hr i).measurable_piecewise continuousOn_const measurableSet_Ioo
  have hv'eq (i : ι) {q : ℝ} (hq : q ∈ Ioo 0 1) : v' i q = v i q := by
    simp [v', hq]
  have hr'eq (i : ι) {q : ℝ} (hq : q ∈ Ioo 0 1) : r' i q = r i q := by
    simp [r', hq]
  apply finite_affine_path_endpoint_bound K y c (by positivity) (by positivity)
    hxR hy hc
  intro a b ha hab hb
  have hsub : Icc a b ⊆ Ioo (0 : ℝ) 1 := by
    intro q hq
    exact ⟨ha.trans_le hq.1, hq.2.trans_lt hb⟩
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_pi.mpr fun i => (hv i).mono hsub)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_pi.mpr fun i => (hr i).mono hsub)
  let An : ℝ≥0 := ⟨max A 0, le_max_right _ _⟩
  let Bn : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hvBound (i : ι) (q : ℝ) (hq : q ∈ Icc a b) : ‖v' i q‖ ≤ An := by
    rw [hv'eq i (hsub hq)]
    exact (norm_le_pi_norm (fun j => v j q) i).trans ((hA q hq).trans (le_max_left _ _))
  have hrBound (i : ι) (q : ℝ) (hq : q ∈ Icc a b) : ‖r' i q‖ ≤ Bn := by
    rw [hr'eq i (hsub hq)]
    exact (norm_le_pi_norm (fun j => r j q) i).trans ((hB q hq).trans (le_max_left _ _))
  have htime : ∀ᵐ q : ℝ ∂volume.restrict (Ioc a b), q ∈ Ioo 0 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
    exact hsub (Ioc_subset_Icc_self hq)
  have hpair : ∀ᵐ p : ℝ × E d ∂(volume.restrict (Ioc a b)).prod (uniformMeasure K),
      p.1 ∈ Ioo 0 1 := Measure.quasiMeasurePreserving_fst.ae htime
  have hbound := finite_affine_path_L2_bound K y v' c r' active m
    hab hw hκ hxR (fun i => (hy i).measurable) (fun i => (hc i).measurable)
    hv'Meas hr'Meas hactiveMeas
    (fun i q hq => by rw [hv'eq i (hsub hq)]; exact hdy i q (hsub hq))
    (fun i q hq => by rw [hr'eq i (hsub hq)]; exact hdc i q (hsub hq))
    hvBound hrBound
    (htime.mono fun q hq => hinj q hq)
    (hpair.mono fun p hp => hactive p.1 hp p.2)
    (fun q hq => hm q (hsub (Ioc_subset_Icc_self hq)))
    (fun q hq => by
      simp only [hv'eq _ (hsub (Ioc_subset_Icc_self hq))]
      exact hvEnergy q (hsub (Ioc_subset_Icc_self hq)))
    (fun q hq => by
      simp only [hr'eq _ (hsub (Ioc_subset_Icc_self hq))]
      exact hrEnergy q (hsub (Ioc_subset_Icc_self hq)))
  exact hbound

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Wasserstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358

variable {d : ℕ}

/-- The real-valued transport distance is nonnegative. -/
theorem wasserstein2_nonneg (μ ν : Measure (E d)) :
    0 ≤ wasserstein2 μ ν :=
  Real.sqrt_nonneg _

/-- Any finite-cost coupling supplies an upper bound for the transport distance. -/
theorem wasserstein2_le_of_coupling {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} (hπ : IsCoupling μ ν π)
    (hfin : quadraticPlanCost π ≠ ∞) :
    wasserstein2 μ ν ≤ Real.sqrt (quadraticPlanCost π).toReal := by
  apply Real.sqrt_le_sqrt
  apply ENNReal.toReal_mono hfin
  exact sInf_le ⟨π, hπ, rfl⟩

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_CompactTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358

/-- A coupling inherits almost-everywhere support from each marginal. -/
theorem IsCoupling.ae_mem {d : ℕ} {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} {K Y : Set (E d)}
    (hπ : IsCoupling μ ν π) (hμ : IsSupported μ K) (hν : IsSupported ν Y) :
    ∀ᵐ p ∂π, p.1 ∈ K ∧ p.2 ∈ Y := by
  have hμae : ∀ᵐ x ∂μ, x ∈ K := by
    rw [ae_iff]
    exact hμ
  have hνae : ∀ᵐ y ∂ν, y ∈ Y := by
    rw [ae_iff]
    exact hν
  have hfst : ∀ᵐ p ∂π, p.1 ∈ K := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    simpa only [hπ.2.1] using hμae
  have hsnd : ∀ᵐ p ∂π, p.2 ∈ Y := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    simpa only [hπ.2.2] using hνae
  exact hfst.and hsnd

/-- Finite second cost for a coupling whose two marginals have compact support. -/
theorem IsCoupling.integrable_sqDist_of_compact {d : ℕ} {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} {K Y : Set (E d)}
    (hπ : IsCoupling μ ν π) (hK : IsCompact K) (hY : IsCompact Y)
    (hμ : IsSupported μ K) (hν : IsSupported ν Y) :
    Integrable (fun p : E d × E d => ‖p.1 - p.2‖ ^ 2) π := by
  let : IsProbabilityMeasure π := hπ.1
  obtain ⟨R, hR, hRK⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨S, hS, hSY⟩ := hY.isBounded.exists_pos_norm_le
  have hmeas : AEStronglyMeasurable (fun p : E d × E d => ‖p.1 - p.2‖ ^ 2) π :=
    ((continuous_fst.sub continuous_snd).norm.pow 2).aestronglyMeasurable
  apply (integrable_const ((R + S) ^ 2)).mono' hmeas
  filter_upwards [hπ.ae_mem hμ hν] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add (hRK _ hp.1) (hSY _ hp.2))) 2

/-- On compact marginal supports every coupling has finite ENNReal quadratic cost. -/
theorem IsCoupling.quadraticPlanCost_ne_top_of_compact {d : ℕ} {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} {K Y : Set (E d)}
    (hπ : IsCoupling μ ν π) (hK : IsCompact K) (hY : IsCompact Y)
    (hμ : IsSupported μ K) (hν : IsSupported ν Y) :
    quadraticPlanCost π ≠ ∞ := by
  have hi := hπ.integrable_sqDist_of_compact hK hY hμ hν
  exact (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => sq_nonneg ‖p.1 - p.2‖))).2 hi

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Coupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358

/-- Mapping both coordinates of a coupling gives a coupling of the mapped marginals. -/
theorem IsCoupling.map {d : ℕ} {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} (hπ : IsCoupling μ ν π)
    {Q R : E d → E d} (hQ : Measurable Q) (hR : Measurable R) :
    IsCoupling (Measure.map Q μ) (Measure.map R ν)
      (Measure.map (Prod.map Q R) π) := by
  have hQR : Measurable (Prod.map Q R) :=
    (hQ.comp measurable_fst).prodMk (hR.comp measurable_snd)
  let : IsProbabilityMeasure π := hπ.1
  refine ⟨Measure.isProbabilityMeasure_map hQR.aemeasurable, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hQR, ← hπ.2.1,
      Measure.map_map hQ measurable_fst]
    rfl
  · rw [Measure.map_map measurable_snd hQR, ← hπ.2.2,
      Measure.map_map hR measurable_snd]
    rfl

/-- Change of variables for the quadratic cost of a mapped coupling. -/
theorem quadraticPlanCost_map {d : ℕ} (π : Measure (E d × E d))
    {Q R : E d → E d} (hQ : Measurable Q) (hR : Measurable R) :
    quadraticPlanCost (Measure.map (Prod.map Q R) π) =
      ∫⁻ p, ENNReal.ofReal (‖Q p.1 - R p.2‖ ^ 2) ∂π := by
  unfold quadraticPlanCost
  rw [lintegral_map]
  · rfl
  · fun_prop
  · exact (hQ.comp measurable_fst).prodMk (hR.comp measurable_snd)

/-- Almost-everywhere statements about either marginal pull back along a coupling. -/
theorem IsCoupling.ae_pair {d : ℕ} {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} (hπ : IsCoupling μ ν π)
    {P Q : E d → Prop} (hP : ∀ᵐ x ∂μ, P x) (hQ : ∀ᵐ y ∂ν, Q y) :
    ∀ᵐ p ∂π, P p.1 ∧ Q p.2 := by
  have hP' : ∀ᵐ p ∂π, P p.1 :=
    ae_of_ae_map measurable_fst.aemeasurable (hπ.2.1.symm ▸ hP)
  have hQ' : ∀ᵐ p ∂π, Q p.2 :=
    ae_of_ae_map measurable_snd.aemeasurable (hπ.2.2.symm ▸ hQ)
  exact hP'.and hQ'

private theorem sqrt_lintegral_norm_sq_eq_lpNorm
    {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    {σ : Measure α} {f : α → F} (hf : AEStronglyMeasurable f σ) :
    Real.sqrt ((∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂σ).toReal) =
      lpNorm f 2 σ := by
  rw [← integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => sq_nonneg (‖f x‖))) (hf.norm.pow 2)]
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf]
  simp [Real.sqrt_eq_rpow]

private theorem lpNorm_two_le_of_ae_bound
    {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    {σ : Measure α} [IsProbabilityMeasure σ] {f : α → F}
    (hf : AEStronglyMeasurable f σ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ᵐ x ∂σ, ‖f x‖ ≤ δ) : lpNorm f 2 σ ≤ δ := by
  have hc : MemLp (fun _ : α => δ) 2 σ := memLp_const δ
  calc
    lpNorm f 2 σ ≤ lpNorm (fun _ : α => δ) 2 σ := by
      rw [← toReal_eLpNorm hf, ← toReal_eLpNorm hc.aestronglyMeasurable]
      exact ENNReal.toReal_mono hc.eLpNorm_ne_top (eLpNorm_mono_ae_real hb)
    _ = δ := by simp [lpNorm_const', Real.norm_eq_abs, abs_of_nonneg hδ]

/-- The square root of a quadratic plan cost is the real-valued L² norm. -/
theorem sqrt_quadraticPlanCost_eq_lpNorm {d : ℕ} (π : Measure (E d × E d)) :
    Real.sqrt (quadraticPlanCost π).toReal =
      lpNorm (fun p : E d × E d => p.1 - p.2) 2 π := by
  exact sqrt_lintegral_norm_sq_eq_lpNorm (by fun_prop)

/-- A plan has finite quadratic cost exactly when its displacement belongs to L². -/
theorem quadraticPlanCost_ne_top_iff_memLp {d : ℕ}
    (π : Measure (E d × E d)) :
    quadraticPlanCost π ≠ ∞ ↔
      MemLp (fun p : E d × E d => p.1 - p.2) 2 π := by
  rw [memLp_two_iff_integrable_sq_norm (by fun_prop)]
  exact lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (Filter.Eventually.of_forall (fun p => sq_nonneg (‖p.1 - p.2‖)))

/-- Perturbing the two coordinates by uniformly bounded errors changes root cost
by at most the sum of those errors. Only the original displacement needs an L² bound. -/
theorem sqrt_quadraticPlanCost_map_le_of_memLp {d : ℕ} {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} (hπ : IsCoupling μ ν π)
    {Q R : E d → E d} (hQ : Measurable Q) (hR : Measurable R)
    {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hQerr : ∀ᵐ x ∂μ, ‖Q x - x‖ ≤ ε)
    (hRerr : ∀ᵐ y ∂ν, ‖R y - y‖ ≤ η)
    (hfinite : MemLp (fun p : E d × E d => p.1 - p.2) 2 π) :
    Real.sqrt (quadraticPlanCost (Measure.map (Prod.map Q R) π)).toReal ≤
      Real.sqrt (quadraticPlanCost π).toReal + ε + η := by
  let : IsProbabilityMeasure π := hπ.1
  let f : E d × E d → E d := fun p => p.1 - p.2
  let e : E d × E d → E d := fun p => (Q p.1 - p.1) - (R p.2 - p.2)
  have he : AEStronglyMeasurable e π := by dsimp [e]; fun_prop
  have heb : ∀ᵐ p ∂π, ‖e p‖ ≤ ε + η := by
    filter_upwards [hπ.ae_pair hQerr hRerr] with p hp
    exact (norm_sub_le _ _).trans (add_le_add hp.1 hp.2)
  have hel : lpNorm e 2 π ≤ ε + η :=
    lpNorm_two_le_of_ae_bound he (add_nonneg hε hη) heb
  rw [quadraticPlanCost_map π hQ hR,
    sqrt_lintegral_norm_sq_eq_lpNorm (by fun_prop),
    sqrt_quadraticPlanCost_eq_lpNorm]
  have hdecomp : (fun p : E d × E d => Q p.1 - R p.2) = f + e := by
    funext p
    dsimp [f, e]
    abel
  rw [hdecomp]
  exact (lpNorm_add_le hfinite (by norm_num)).trans (by linarith)

/-- Uniformly bounded changes of coordinates preserve finite quadratic cost. -/
theorem quadraticPlanCost_map_ne_top {d : ℕ} {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} (hπ : IsCoupling μ ν π)
    {Q R : E d → E d} (hQ : Measurable Q) (hR : Measurable R)
    {ε η : ℝ}
    (hQerr : ∀ᵐ x ∂μ, ‖Q x - x‖ ≤ ε)
    (hRerr : ∀ᵐ y ∂ν, ‖R y - y‖ ≤ η)
    (hfinite : quadraticPlanCost π ≠ ∞) :
    quadraticPlanCost (Measure.map (Prod.map Q R) π) ≠ ∞ := by
  let : IsProbabilityMeasure π := hπ.1
  let f : E d × E d → E d := fun p => p.1 - p.2
  let e : E d × E d → E d := fun p => (Q p.1 - p.1) - (R p.2 - p.2)
  have hf : MemLp f 2 π := (quadraticPlanCost_ne_top_iff_memLp π).1 hfinite
  have he : MemLp e 2 π := by
    apply MemLp.of_bound (by dsimp [e]; fun_prop) (ε + η)
    filter_upwards [hπ.ae_pair hQerr hRerr] with p hp
    exact (norm_sub_le _ _).trans (add_le_add hp.1 hp.2)
  have hdecomp : (fun p : E d × E d => Q p.1 - R p.2) = f + e := by
    funext p
    dsimp [f, e]
    abel
  have hmem : MemLp (fun p : E d × E d => Q p.1 - R p.2) 2 π := by
    rw [hdecomp]
    exact hf.add he
  rw [quadraticPlanCost_map π hQ hR]
  apply (lintegral_ofReal_ne_top_iff_integrable (hmem.aestronglyMeasurable.norm.pow 2)
    (Filter.Eventually.of_forall (fun p => sq_nonneg (‖Q p.1 - R p.2‖)))).2
  exact (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem

/-- Finite-cost version of `sqrt_quadraticPlanCost_map_le_of_memLp`. -/
theorem sqrt_quadraticPlanCost_map_le {d : ℕ} {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} (hπ : IsCoupling μ ν π)
    {Q R : E d → E d} (hQ : Measurable Q) (hR : Measurable R)
    {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hQerr : ∀ᵐ x ∂μ, ‖Q x - x‖ ≤ ε)
    (hRerr : ∀ᵐ y ∂ν, ‖R y - y‖ ≤ η)
    (hfinite : quadraticPlanCost π ≠ ∞) :
    Real.sqrt (quadraticPlanCost (Measure.map (Prod.map Q R) π)).toReal ≤
      Real.sqrt (quadraticPlanCost π).toReal + ε + η :=
  sqrt_quadraticPlanCost_map_le_of_memLp hπ hQ hR hε hη hQerr hRerr
    ((quadraticPlanCost_ne_top_iff_memLp π).1 hfinite)

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_MapDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358

variable {d : ℕ} {ρ : Measure (E d)} {T S U : E d → E d}

@[simp] theorem mapL2Dist_self (ρ : Measure (E d)) (T : E d → E d) :
    mapL2Dist ρ T T = 0 := by
  simp [mapL2Dist]

theorem mapL2Dist_congr_ae {T' S' : E d → E d}
    (hT : T =ᵐ[ρ] T') (hS : S =ᵐ[ρ] S') :
    mapL2Dist ρ T S = mapL2Dist ρ T' S' := by
  unfold mapL2Dist
  congr 1
  apply integral_congr_ae
  filter_upwards [hT, hS] with x hx hy
  rw [hx, hy]

theorem mapL2Dist_eq_lpNorm (hT : AEStronglyMeasurable T ρ)
    (hS : AEStronglyMeasurable S ρ) :
    mapL2Dist ρ T S = lpNorm (T - S) 2 ρ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) (hT.sub hS)]
  simp [mapL2Dist, Real.sqrt_eq_rpow]

theorem mapL2Dist_eq_dist_toLp (hT : MemLp T 2 ρ) (hS : MemLp S 2 ρ) :
    mapL2Dist ρ T S = dist (hT.toLp T) (hS.toLp S) := by
  rw [Lp.dist_edist, Lp.edist_toLp_toLp, toReal_eLpNorm (hT.sub hS).aestronglyMeasurable]
  exact mapL2Dist_eq_lpNorm hT.aestronglyMeasurable hS.aestronglyMeasurable

end Problem358

end

noncomputable section
open MeasureTheory

namespace Problem358

/-- The graph plan of a measurable map remembers its almost-everywhere class. -/
theorem graphPlan_eq_iff_ae_eq {d : ℕ} {ρ : Measure (E d)}
    {T S : E d → E d} (hT : Measurable T) (hS : Measurable S) :
    graphPlan ρ T = graphPlan ρ S ↔ T =ᵐ[ρ] S := by
  constructor
  · intro heq
    have hgraph : ∀ᵐ p ∂graphPlan ρ T, p.2 = T p.1 := by
      apply (ae_map_iff (measurable_id.prodMk hT).aemeasurable
        (measurableSet_eq_fun measurable_snd (hT.comp measurable_fst))).2
      exact Filter.Eventually.of_forall fun _ => rfl
    rw [heq] at hgraph
    have hae := ae_of_ae_map (measurable_id.prodMk hS).aemeasurable hgraph
    filter_upwards [hae] with x hx
    exact hx.symm
  · intro hae
    apply Measure.map_congr
    filter_upwards [hae] with x hx
    exact Prod.ext rfl hx

/-- A measurable transport of a probability source defines a coupling with its law. -/
theorem graphPlan_isCoupling {d : ℕ} {ρ μ : Measure (E d)}
    [IsProbabilityMeasure ρ] {T : E d → E d}
    (hT : Measurable T) (hlaw : Measure.map T ρ = μ) :
    IsCoupling ρ μ (graphPlan ρ T) := by
  have hm : Measurable (fun x => (x, T x)) := measurable_id.prodMk hT
  refine ⟨?_, ?_, ?_⟩
  · unfold graphPlan
    exact Measure.isProbabilityMeasure_map hm.aemeasurable
  · rw [graphPlan, Measure.map_map measurable_fst hm]
    exact Measure.map_id
  · rw [graphPlan, Measure.map_map measurable_snd hm]
    exact hlaw

/-- Uniqueness among transport plans implies uniqueness of the map almost everywhere. -/
theorem IsUniqueQuadraticOptimalMap.ae_eq_of_optimal {d : ℕ}
    {ρ μ : Measure (E d)} [IsProbabilityMeasure ρ] {T S : E d → E d}
    (hT : IsUniqueQuadraticOptimalMap ρ μ T)
    (hS : IsQuadraticOptimalMap ρ μ S) : T =ᵐ[ρ] S := by
  apply (graphPlan_eq_iff_ae_eq hT.1.1 hS.1).mp
  exact (hT.2 _ (graphPlan_isCoupling hS.1 hS.2.1)
    (hS.2.2 _ (graphPlan_isCoupling hT.1.1 hT.1.2.1))).symm

/-- Distances between unique optimal maps do not depend on selected representatives. -/
theorem mapL2Dist_eq_of_optimal_maps {d : ℕ} {ρ μ ν : Measure (E d)}
    [IsProbabilityMeasure ρ] {T S T' S' : E d → E d}
    (hT : IsUniqueQuadraticOptimalMap ρ μ T)
    (hS : IsUniqueQuadraticOptimalMap ρ ν S)
    (hT' : IsQuadraticOptimalMap ρ μ T') (hS' : IsQuadraticOptimalMap ρ ν S') :
    mapL2Dist ρ T S = mapL2Dist ρ T' S' :=
  mapL2Dist_congr_ae (hT.ae_eq_of_optimal hT') (hS.ae_eq_of_optimal hS')

end Problem358

end

noncomputable section
open Filter
open scoped Topology

namespace Problem358.StabilityLimit

/-- A uniform power bound survives convergence when the input distances have only
an asymptotic upper bound. This is enough for finite-target quantization. -/
theorem real_bound_of_approximation
    {D W C α : ℝ} {Dₙ Wₙ ε : ℕ → ℝ}
    (hC : 0 ≤ C) (hα : 0 ≤ α) (hWₙ : ∀ n, 0 ≤ Wₙ n)
    (hD : Tendsto Dₙ atTop (𝓝 D)) (hε : Tendsto ε atTop (𝓝 0))
    (hupper : ∀ n, Wₙ n ≤ W + ε n)
    (hbound : ∀ n, Dₙ n ≤ C * Real.rpow (Wₙ n) α) :
    D ≤ C * Real.rpow W α := by
  have hinput : Tendsto (fun n => W + ε n) atTop (𝓝 W) := by
    simpa using tendsto_const_nhds.add hε
  have hpower : Tendsto (fun n => C * Real.rpow (W + ε n) α)
      atTop (𝓝 (C * Real.rpow W α)) :=
    tendsto_const_nhds.mul ((Real.continuous_rpow_const hα).tendsto W |>.comp hinput)
  apply le_of_tendsto_of_tendsto hD hpower
  exact Filter.Eventually.of_forall fun n => (hbound n).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hWₙ n) (hupper n) hα) hC)

open MeasureTheory
variable {d : ℕ} {ρ : Measure (E d)}

/-- Strong L² convergence in both arguments gives convergence of the map distance. -/
theorem tendsto_mapL2Dist {T S : E d → E d} {Tₙ Sₙ : ℕ → E d → E d}
    (hT : MemLp T 2 ρ) (hS : MemLp S 2 ρ)
    (hTₙ : ∀ n, MemLp (Tₙ n) 2 ρ) (hSₙ : ∀ n, MemLp (Sₙ n) 2 ρ)
    (hlimT : Tendsto (fun n => mapL2Dist ρ (Tₙ n) T) atTop (𝓝 0))
    (hlimS : Tendsto (fun n => mapL2Dist ρ (Sₙ n) S) atTop (𝓝 0)) :
    Tendsto (fun n => mapL2Dist ρ (Tₙ n) (Sₙ n)) atTop (𝓝 (mapL2Dist ρ T S)) := by
  have hTLp : Tendsto (fun n => (hTₙ n).toLp (Tₙ n)) atTop (𝓝 (hT.toLp T)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [← mapL2Dist_eq_dist_toLp] using hlimT
  have hSLp : Tendsto (fun n => (hSₙ n).toLp (Sₙ n)) atTop (𝓝 (hS.toLp S)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [← mapL2Dist_eq_dist_toLp] using hlimS
  simpa only [← mapL2Dist_eq_dist_toLp] using hTLp.dist hSLp

/-- Passage from finite-target map bounds to a strong-L² limiting pair. -/
theorem mapL2Dist_bound_of_approximation
    {T S : E d → E d} {Tₙ Sₙ : ℕ → E d → E d}
    {W C α : ℝ} {Wₙ ε : ℕ → ℝ}
    (hT : MemLp T 2 ρ) (hS : MemLp S 2 ρ)
    (hTₙ : ∀ n, MemLp (Tₙ n) 2 ρ) (hSₙ : ∀ n, MemLp (Sₙ n) 2 ρ)
    (hlimT : Tendsto (fun n => mapL2Dist ρ (Tₙ n) T) atTop (𝓝 0))
    (hlimS : Tendsto (fun n => mapL2Dist ρ (Sₙ n) S) atTop (𝓝 0))
    (hC : 0 ≤ C) (hα : 0 ≤ α) (hWₙ : ∀ n, 0 ≤ Wₙ n)
    (hε : Tendsto ε atTop (𝓝 0)) (hupper : ∀ n, Wₙ n ≤ W + ε n)
    (hbound : ∀ n, mapL2Dist ρ (Tₙ n) (Sₙ n) ≤ C * Real.rpow (Wₙ n) α) :
    mapL2Dist ρ T S ≤ C * Real.rpow W α := by
  exact real_bound_of_approximation hC hα hWₙ
    (tendsto_mapL2Dist hT hS hTₙ hSₙ hlimT hlimS) hε hupper hbound

/-- Final one-third estimate under explicit finite approximation hypotheses. -/
theorem one_third_bound_of_target_approximation
    {T S : E d → E d} {Tₙ Sₙ : ℕ → E d → E d}
    {μ ν : Measure (E d)} {μₙ νₙ : ℕ → Measure (E d)} {C : ℝ} {ε : ℕ → ℝ}
    (hT : MemLp T 2 ρ) (hS : MemLp S 2 ρ)
    (hTₙ : ∀ n, MemLp (Tₙ n) 2 ρ) (hSₙ : ∀ n, MemLp (Sₙ n) 2 ρ)
    (hlimT : Tendsto (fun n => mapL2Dist ρ (Tₙ n) T) atTop (𝓝 0))
    (hlimS : Tendsto (fun n => mapL2Dist ρ (Sₙ n) S) atTop (𝓝 0))
    (hC : 0 ≤ C) (hε : Tendsto ε atTop (𝓝 0))
    (hupper : ∀ n, wasserstein2 (μₙ n) (νₙ n) ≤ wasserstein2 μ ν + ε n)
    (hbound : ∀ n, mapL2Dist ρ (Tₙ n) (Sₙ n) ≤
      C * Real.rpow (wasserstein2 (μₙ n) (νₙ n)) (1 / 3 : ℝ)) :
    mapL2Dist ρ T S ≤ C * Real.rpow (wasserstein2 μ ν) (1 / 3 : ℝ) := by
  exact mapL2Dist_bound_of_approximation hT hS hTₙ hSₙ hlimT hlimS hC
    (by norm_num) (fun n => Real.sqrt_nonneg _) hε hupper hbound

end Problem358.StabilityLimit

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_MapLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Problem358

/-- Bounded continuous tests commute with almost-everywhere limits of measurable
maps on a finite measure space. No uniform bound on the maps themselves is needed. -/
theorem tendsto_integral_boundedContinuous_comp_ae
    {X Y : Type*} [MeasurableSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {ρ : Measure X} [IsFiniteMeasure ρ]
    {Tn : ℕ → X → Y} {T : X → Y}
    (hTn : ∀ n, Measurable (Tn n))
    (hlim : ∀ᵐ x ∂ρ, Tendsto (fun n => Tn n x) atTop (𝓝 (T x)))
    (f : Y →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, f (Tn n x) ∂ρ) atTop
      (𝓝 (∫ x, f (T x) ∂ρ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
  · intro n
    exact (f.continuous.measurable.comp (hTn n)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Filter.Eventually.of_forall fun x => f.norm_coe_le_norm (Tn n x)
  · filter_upwards [hlim] with x hx
    exact f.continuous.continuousAt.tendsto.comp hx

/-- A candidate almost-everywhere limit has the prescribed target law whenever
the approximating laws converge against bounded continuous functions. -/
theorem map_eq_of_ae_tendsto_and_test_tendsto
    {X Y : Type*} [MeasurableSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [HasOuterApproxClosed Y]
    {ρ : Measure X} [IsFiniteMeasure ρ]
    {ν : Measure Y} [IsFiniteMeasure ν]
    {Tn : ℕ → X → Y} {T : X → Y}
    (hTn : ∀ n, Measurable (Tn n)) (hT : Measurable T)
    (hlim : ∀ᵐ x ∂ρ, Tendsto (fun n => Tn n x) atTop (𝓝 (T x)))
    (htest : ∀ f : Y →ᵇ ℝ,
      Tendsto (fun n => ∫ x, f (Tn n x) ∂ρ) atTop (𝓝 (∫ y, f y ∂ν))) :
    Measure.map T ρ = ν := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hT.aemeasurable f.continuous.measurable.aestronglyMeasurable]
  exact tendsto_nhds_unique (tendsto_integral_boundedContinuous_comp_ae hTn hlim f) (htest f)

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Conjugacy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter
open scoped NNReal Topology

namespace Problem358

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma restrictedConjugate_eq_of_isMaxOn
    {K : Set V} {u : V → ℝ} {x y : V} (hx : x ∈ K)
    (hmax : IsMaxOn (fun z => inner ℝ z y - u z) K x) :
    restrictedConjugate K u y = inner ℝ x y - u x := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨x, hx, rfl⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hmax hz

lemma restrictedConjugate_attained
    {K : Set V} {u : V → ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    (hu : ContinuousOn u K) (y : V) :
    ∃ x ∈ K, restrictedConjugate K u y = inner ℝ x y - u x := by
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne
    ((continuous_id.inner continuous_const).continuousOn.sub hu :
      ContinuousOn (fun x => inner ℝ x y - u x) K)
  exact ⟨x, hx, restrictedConjugate_eq_of_isMaxOn hx hmax⟩

lemma restrictedConjugate_fenchel
    {K : Set V} {u : V → ℝ} (hK : IsCompact K)
    (hu : ContinuousOn u K) {x : V} (hx : x ∈ K) (y : V) :
    inner ℝ x y ≤ u x + restrictedConjugate K u y := by
  have hbound := hK.bddAbove_image
    ((continuous_id.inner continuous_const).continuousOn.sub hu :
      ContinuousOn (fun x => inner ℝ x y - u x) K)
  have hle : inner ℝ x y - u x ≤ restrictedConjugate K u y :=
    le_csSup hbound ⟨x, hx, rfl⟩
  linarith

/-- Fenchel equality is exactly the supporting-slope inequality on the source set. -/
lemma restrictedConjugate_eq_iff_support
    {K : Set V} {u : V → ℝ} (hK : IsCompact K)
    (hu : ContinuousOn u K) {x y : V} (hx : x ∈ K) :
    inner ℝ x y = u x + restrictedConjugate K u y ↔
      ∀ z ∈ K, u x + inner ℝ (z - x) y ≤ u z := by
  constructor
  · intro heq z hz
    have hle := restrictedConjugate_fenchel hK hu hz y
    rw [inner_sub_left] at *
    linarith
  · intro hs
    have hmax : IsMaxOn (fun z => inner ℝ z y - u z) K x := by
      intro z hz
      change inner ℝ z y - u z ≤ inner ℝ x y - u x
      have h := hs z hz
      rw [inner_sub_left] at h
      linarith
    rw [restrictedConjugate_eq_of_isMaxOn hx hmax]
    ring

lemma restrictedConjugate_sub_le
    {K : Set V} {u : V → ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    (hu : ContinuousOn u K) {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R)
    (y z : V) :
    restrictedConjugate K u y - restrictedConjugate K u z ≤ R * ‖y - z‖ := by
  obtain ⟨x, hx, heq⟩ := restrictedConjugate_attained hK hne hu y
  have hfen := restrictedConjugate_fenchel hK hu hx z
  have hinner := real_inner_le_norm x (y - z)
  have hmul := mul_le_mul_of_nonneg_right (hR x hx) (norm_nonneg (y - z))
  rw [inner_sub_right] at hinner
  rw [heq]
  linarith

lemma restrictedConjugate_lipschitz
    {K : Set V} {u : V → ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    (hu : ContinuousOn u K) {R : ℝ≥0} (hR : ∀ x ∈ K, ‖x‖ ≤ R) :
    LipschitzWith R (restrictedConjugate K u) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [Real.dist_eq, dist_eq_norm]
  apply abs_le.mpr
  constructor
  · have h := restrictedConjugate_sub_le hK hne hu hR z y
    rw [norm_sub_rev] at h
    linarith
  · exact restrictedConjugate_sub_le hK hne hu hR y z

lemma restrictedConjugate_continuous
    {K : Set V} {u : V → ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    (hu : ContinuousOn u K) : Continuous (restrictedConjugate K u) := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨x, hx⟩ := hne
  have hR0 : 0 ≤ R := (norm_nonneg x).trans (hR x hx)
  exact (restrictedConjugate_lipschitz hK ⟨x, hx⟩ hu (R := ⟨R, hR0⟩) hR).continuous

/-- A supporting slope at an interior differentiability point is the derivative. -/
lemma restrictedConjugate_supporting_slope_eq_fderiv
    {K : Set V} {u : V → ℝ} {x y : V} {u' : V →L[ℝ] ℝ}
    (hx : x ∈ interior K) (hu : HasFDerivAt u u' x)
    (hs : ∀ z ∈ K, u x + inner ℝ (z - x) y ≤ u z) :
    u' = innerSL ℝ y := by
  have hmin : IsMinOn (fun z => u z - inner ℝ y z) K x := by
    intro z hz
    change u x - inner ℝ y x ≤ u z - inner ℝ y z
    have h := hs z hz
    rw [inner_sub_left] at h
    have hxy := real_inner_comm x y
    have hzy := real_inner_comm z y
    linarith
  have hzero := (hmin.isLocalMin (mem_interior_iff_mem_nhds.mp hx)).hasFDerivAt_eq_zero
    (hu.sub (innerSL ℝ y).hasFDerivAt)
  exact sub_eq_zero.mp hzero

lemma restrictedConjugate_supporting_slope_unique
    {K : Set V} {u : V → ℝ} {x y z : V}
    (hx : x ∈ interior K) (hu : DifferentiableAt ℝ u x)
    (hy : ∀ w ∈ K, u x + inner ℝ (w - x) y ≤ u w)
    (hz : ∀ w ∈ K, u x + inner ℝ (w - x) z ≤ u w) : y = z := by
  apply (innerSL_inj (𝕜 := ℝ)).mp
  exact (restrictedConjugate_supporting_slope_eq_fderiv hx hu.hasFDerivAt hy).symm.trans
    (restrictedConjugate_supporting_slope_eq_fderiv hx hu.hasFDerivAt hz)

/-- Continuous quadratic-cost dual potentials obtained from the restricted conjugate. -/
lemma restrictedConjugate_quadratic_dual_le
    {K : Set V} {u : V → ℝ} (hK : IsCompact K) (hu : ContinuousOn u K)
    {x : V} (hx : x ∈ K) (y : V) :
    (‖x‖ ^ 2 - 2 * u x) + (‖y‖ ^ 2 - 2 * restrictedConjugate K u y) ≤
      ‖x - y‖ ^ 2 := by
  rw [norm_sub_sq_real]
  have h := restrictedConjugate_fenchel hK hu hx y
  linarith

lemma restrictedConjugate_quadratic_dual_eq_iff
    {K : Set V} {u : V → ℝ} (hK : IsCompact K) (hu : ContinuousOn u K)
    {x y : V} (hx : x ∈ K) :
    (‖x‖ ^ 2 - 2 * u x) + (‖y‖ ^ 2 - 2 * restrictedConjugate K u y) =
      ‖x - y‖ ^ 2 ↔ ∀ z ∈ K, u x + inner ℝ (z - x) y ≤ u z := by
  rw [← restrictedConjugate_eq_iff_support hK hu hx, norm_sub_sq_real]
  constructor <;> intro h <;> linarith

end Problem358

end

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Problem358

/-- A convex source gives full measure to its interior. -/
theorem ae_mem_interior_uniformMeasure {d : ℕ} {K : Set (E d)}
    (hK : Convex ℝ K) (hKm : MeasurableSet K) :
    ∀ᵐ x ∂uniformMeasure K, x ∈ interior K := by
  apply Measure.ae_smul_measure
  have hEq : interior K =ᵐ[volume] K :=
    interior_ae_eq_of_null_frontier (hK.addHaar_frontier volume)
  filter_upwards [ae_restrict_of_ae hEq, ae_restrict_mem hKm] with x hx hmem
  exact hx.mpr hmem

/-- Rademacher's theorem on a convex source, upgraded from within-derivatives
using the nullity of the boundary of a convex set. No regular boundary is needed. -/
theorem ae_differentiableAt_uniformMeasure {d : ℕ} {K : Set (E d)}
    {u : E d → ℝ} {L : ℝ≥0}
    (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hu : LipschitzOnWith L u K) :
    ∀ᵐ x ∂uniformMeasure K, x ∈ interior K ∧ DifferentiableAt ℝ u x := by
  have hd : ∀ᵐ x ∂volume.restrict K, DifferentiableWithinAt ℝ u K x :=
    hu.ae_differentiableWithinAt hKm
  have hd' : ∀ᵐ x ∂uniformMeasure K, DifferentiableWithinAt ℝ u K x :=
    Measure.ae_smul_measure hd _
  filter_upwards [ae_mem_interior_uniformMeasure hK hKm, hd'] with x hx hdx
  exact ⟨hx, hdx.differentiableAt (mem_interior_iff_mem_nhds.mp hx)⟩

end Problem358

end

/-! # Supporting slopes at differentiability points

The elementary local step used to identify the equality locus of a
Fenchel certificate.  No convexity assumption is needed once a supporting
inequality is supplied.
-/

noncomputable section

open Set Filter
open scoped Topology RealInnerProductSpace

namespace Problem358

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A supporting slope on a neighborhood is the derivative. -/
theorem hasFDerivAt_eq_innerSL_of_supporting
    {u : H → ℝ} {D : H →L[ℝ] ℝ} {K : Set H} {x p : H}
    (hu : HasFDerivAt u D x) (hx : x ∈ interior K)
    (hp : ∀ z ∈ K, u x + ⟪p, z - x⟫ ≤ u z) :
    D = innerSL ℝ p := by
  have hmin : IsLocalMin (fun z => u z - ⟪p, z⟫) x := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hx] with z hz
    have h := hp z hz
    simp only [inner_sub_right] at h
    linarith
  have hderiv : HasFDerivAt (fun z => u z - ⟪p, z⟫)
      (D - innerSL ℝ p) x := hu.sub (innerSL ℝ p).hasFDerivAt
  exact sub_eq_zero.mp (hmin.hasFDerivAt_eq_zero hderiv)

/-- Evaluated form of the supporting-slope identification. -/
theorem hasFDerivAt_apply_eq_inner_of_supporting
    {u : H → ℝ} {D : H →L[ℝ] ℝ} {K : Set H} {x p : H}
    (hu : HasFDerivAt u D x) (hx : x ∈ interior K)
    (hp : ∀ z ∈ K, u x + ⟪p, z - x⟫ ≤ u z) (v : H) :
    D v = ⟪p, v⟫ := by
  rw [hasFDerivAt_eq_innerSL_of_supporting hu hx hp]
  rfl

/-- Supporting slopes are unique at an interior differentiability point. -/
theorem supporting_slope_unique
    {u : H → ℝ} {K : Set H} {x p q : H}
    (hu : DifferentiableAt ℝ u x) (hx : x ∈ interior K)
    (hp : ∀ z ∈ K, u x + ⟪p, z - x⟫ ≤ u z)
    (hq : ∀ z ∈ K, u x + ⟪q, z - x⟫ ≤ u z) : p = q := by
  apply ext_inner_right ℝ
  intro v
  exact (hasFDerivAt_apply_eq_inner_of_supporting hu.hasFDerivAt hx hp v).symm.trans
    (hasFDerivAt_apply_eq_inner_of_supporting hu.hasFDerivAt hx hq v)

/-- Equality in a Fenchel inequality produces a supporting slope. -/
theorem supporting_of_fenchel_eq
    {u : H → ℝ} {v : H → ℝ} {K : Set H} {x y : H}
    (hdual : ∀ z ∈ K, ⟪z, y⟫ ≤ u z + v y)
    (heq : ⟪x, y⟫ = u x + v y) :
    ∀ z ∈ K, u x + ⟪y, z - x⟫ ≤ u z := by
  intro z hz
  have h := hdual z hz
  rw [inner_sub_right, real_inner_comm z y, real_inner_comm x y]
  linarith

/-- At an interior differentiability point, equality in a Fenchel
certificate forces the target coordinate to equal any known supporting slope. -/
theorem eq_supporting_slope_of_fenchel_eq
    {u : H → ℝ} {v : H → ℝ} {K : Set H} {x p y : H}
    (hu : DifferentiableAt ℝ u x) (hx : x ∈ interior K)
    (hp : ∀ z ∈ K, u x + ⟪p, z - x⟫ ≤ u z)
    (hdual : ∀ z ∈ K, ⟪z, y⟫ ≤ u z + v y)
    (heq : ⟪x, y⟫ = u x + v y) : y = p :=
  supporting_slope_unique hu hx (supporting_of_fenchel_eq hdual heq) hp

end Problem358

end

/-! # Almost-everywhere uniqueness of supporting slopes

Rademacher's theorem and the null boundary of a convex set provide the
regularity needed by the local supporting-slope lemmas.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology RealInnerProductSpace NNReal ENNReal

namespace Problem358

/-- A Fenchel equality locus is the graph of a known supporting map,
source-almost everywhere.  This is the pointwise input for uniqueness of plans. -/
theorem uniform_ae_eq_supporting_map_of_fenchel_eq
    {d : ℕ} {K Y : Set (E d)} {u v : E d → ℝ} {T : E d → E d} {L : ℝ≥0}
    (hK : Convex ℝ K) (hKm : MeasurableSet K) (hu : LipschitzOnWith L u K)
    (hT : ∀ᵐ x ∂uniformMeasure K, ∀ z ∈ K, u x + ⟪T x, z - x⟫ ≤ u z)
    (hdual : ∀ y ∈ Y, ∀ z ∈ K, ⟪z, y⟫ ≤ u z + v y) :
    ∀ᵐ x ∂uniformMeasure K, ∀ y ∈ Y,
      ⟪x, y⟫ = u x + v y → y = T x := by
  filter_upwards [ae_differentiableAt_uniformMeasure hK hKm hu, hT]
    with x hx hsupport
  intro y hy heq
  exact eq_supporting_slope_of_fenchel_eq hx.2 hx.1 hsupport (hdual y hy) heq

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_ConvexOptimality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Problem358

/-- A continuous source potential, supporting the map almost everywhere and
having almost everywhere unique differentiable interior slopes, certifies
uniqueness among all transport plans. -/
theorem isUniqueQuadraticOptimalMap_of_ae_differentiable_supporting_potential
    {d : ℕ} {ρ μ : Measure (E d)} [IsFiniteMeasure ρ] [IsFiniteMeasure μ]
    {K Y : Set (E d)} {u : E d → ℝ} {T : E d → E d}
    (hK : IsCompact K) (hne : K.Nonempty) (hY : IsCompact Y)
    (hρ : IsSupported ρ K) (hμ : IsSupported μ Y)
    (hu : ContinuousOn u K) (hT : Measurable T) (hpush : Measure.map T ρ = μ)
    (hdiff : ∀ᵐ x ∂ρ, x ∈ interior K ∧ DifferentiableAt ℝ u x)
    (hs : ∀ᵐ x ∂ρ, ∀ z ∈ K, u x + inner ℝ (z - x) (T x) ≤ u z) :
    IsUniqueQuadraticOptimalMap ρ μ T := by
  let f : E d → ℝ := fun x => ‖x‖ ^ 2 - 2 * u x
  let g : E d → ℝ := fun y => ‖y‖ ^ 2 - 2 * restrictedConjugate K u y
  have hf : Integrable f ρ := hρ.integrable_continuousOn hK
    ((continuous_norm.pow 2).continuousOn.sub (hu.const_mul 2))
  have hg : Integrable g μ := hμ.integrable_continuousOn hY
    (((continuous_norm.pow 2).sub
      ((restrictedConjugate_continuous hK hne hu).const_mul 2)).continuousOn)
  apply isUniqueQuadraticOptimalMap_of_dual hT hpush hf hg
  · intro π hπ
    have hfst : ∀ᵐ p ∂π, p.1 ∈ K := by
      apply ae_of_ae_map measurable_fst.aemeasurable
      rw [hπ.2.1]
      exact ae_iff.mpr hρ
    filter_upwards [hfst] with p hp
    exact restrictedConjugate_quadratic_dual_le hK hu hp p.2
  · have hsource : ∀ᵐ x ∂ρ, x ∈ K := ae_iff.mpr hρ
    filter_upwards [hsource, hs] with x hx hsx
    exact ((restrictedConjugate_quadratic_dual_eq_iff hK hu hx).mpr hsx).symm
  · intro π hπ
    have hfst : ∀ᵐ p ∂π, (p.1 ∈ interior K ∧ DifferentiableAt ℝ u p.1) ∧
        ∀ z ∈ K, u p.1 + inner ℝ (z - p.1) (T p.1) ≤ u z := by
      have he : ∀ᵐ x ∂Measure.map Prod.fst π,
          (x ∈ interior K ∧ DifferentiableAt ℝ u x) ∧
          ∀ z ∈ K, u x + inner ℝ (z - x) (T x) ≤ u z := by
        rw [hπ.2.1]
        exact hdiff.and hs
      exact ae_of_ae_map measurable_fst.aemeasurable he
    filter_upwards [hfst] with p hp
    intro heq
    have hx : p.1 ∈ K := interior_subset hp.1.1
    have hsupport := (restrictedConjugate_quadratic_dual_eq_iff hK hu hx).mp heq
    exact restrictedConjugate_supporting_slope_unique hp.1.1 hp.1.2 hsupport hp.2

/-- For uniform convex sources, Rademacher and the null convex boundary discharge
all differentiability assumptions of the preceding certificate. -/
theorem isUniqueQuadraticOptimalMap_uniform_of_supporting_potential
    {d : ℕ} {K Y : Set (E d)} {μ : Measure (E d)}
    [IsFiniteMeasure (uniformMeasure K)] [IsFiniteMeasure μ]
    {u : E d → ℝ} {T : E d → E d} {L : ℝ≥0}
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (hY : IsCompact Y) (hμ : IsSupported μ Y)
    (hu : LipschitzOnWith L u K) (hT : Measurable T)
    (hpush : Measure.map T (uniformMeasure K) = μ)
    (hs : ∀ᵐ x ∂uniformMeasure K, ∀ z ∈ K,
      u x + inner ℝ (z - x) (T x) ≤ u z) :
    IsUniqueQuadraticOptimalMap (uniformMeasure K) μ T := by
  have hρ : IsSupported (uniformMeasure K) K := by
    apply ae_iff.mp
    exact Measure.ae_smul_measure (ae_restrict_mem hK.measurableSet) _
  exact isUniqueQuadraticOptimalMap_of_ae_differentiable_supporting_potential hK hne hY hρ hμ
    hu.continuousOn hT hpush
    (ae_differentiableAt_uniformMeasure hconv hK.measurableSet hu) hs

end Problem358

end

/-! # Optimality and uniqueness from a supporting potential

This packages the limiting-potential step of the arbitrary-target argument.
The potential need only be Lipschitz on the source body and support the
candidate map almost everywhere.  Its restricted conjugate supplies the
dual certificate, and Rademacher regularity makes its equality locus a graph.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace Problem358

/-- A measurable map supported by a Lipschitz potential on a compact convex
source is the unique quadratic optimal plan to its compactly supported law. -/
theorem isUniqueQuadraticOptimalMap_of_supporting_potential
    {d : ℕ} {K Y : Set (E d)} {μ : Measure (E d)} [IsProbabilityMeasure μ]
    {u : E d → ℝ} {T : E d → E d} {L : ℝ≥0}
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (hY : IsCompact Y) (hμ : IsSupported μ Y)
    (hu : LipschitzOnWith L u K) (hT : Measurable T)
    (hpush : Measure.map T (uniformMeasure K) = μ)
    (hsupport : ∀ᵐ x ∂uniformMeasure K,
      ∀ z ∈ K, u x + ⟪T x, z - x⟫ ≤ u z) :
    IsUniqueQuadraticOptimalMap (uniformMeasure K) μ T := by
  let : IsProbabilityMeasure (Measure.map T (uniformMeasure K)) :=
    hpush.symm ▸ inferInstance
  let : IsProbabilityMeasure (uniformMeasure K) :=
    Measure.isProbabilityMeasure_of_map T
  let v : E d → ℝ := restrictedConjugate K u
  have hv : Continuous v := restrictedConjugate_continuous hK hKne hu.continuousOn
  have hsource : ∀ᵐ x ∂uniformMeasure K, x ∈ K :=
    Measure.ae_smul_measure (ae_restrict_mem hK.measurableSet) _
  have hf : Integrable (fun x : E d => ‖x‖ ^ 2 - 2 * u x) (uniformMeasure K) := by
    apply integrable_of_continuousOn_of_ae_mem_compact hK hsource
    exact (continuous_norm.pow 2).continuousOn.sub (continuousOn_const.mul hu.continuousOn)
  have hg : Integrable (fun y : E d => ‖y‖ ^ 2 - 2 * v y) μ := by
    apply hμ.integrable_continuousOn hY
    exact ((continuous_norm.pow 2).sub (continuous_const.mul hv)).continuousOn
  have hfenchel : ∀ y : E d, ∀ z ∈ K, ⟪z, y⟫ ≤ u z + v y := by
    intro y z hz
    exact restrictedConjugate_fenchel hK hu.continuousOn hz y
  have hstrictSource : ∀ᵐ x ∂uniformMeasure K, ∀ y : E d,
      ⟪x, y⟫ = u x + v y → y = T x := by
    have h := uniform_ae_eq_supporting_map_of_fenchel_eq
      (Y := Set.univ) hKconv hK.measurableSet hu hsupport
      (fun y _ => hfenchel y)
    filter_upwards [h] with x hx
    intro y heq
    exact hx y (Set.mem_univ y) heq
  apply isUniqueQuadraticOptimalMap_of_dual hT hpush hf hg
  · intro π hπ
    have hfst : ∀ᵐ p ∂π, p.1 ∈ K := by
      apply ae_of_ae_map measurable_fst.aemeasurable
      rw [hπ.2.1]
      exact hsource
    filter_upwards [hfst] with p hp
    have h := hfenchel p.2 p.1 hp
    rw [norm_sub_sq_real]
    linarith
  · filter_upwards [hsource, hsupport] with x hx hs
    have heq : ⟪x, T x⟫ = u x + v (T x) := by
      apply (restrictedConjugate_eq_iff_support hK hu.continuousOn hx).mpr
      intro z hz
      simpa only [real_inner_comm (z - x) (T x)] using hs z hz
    rw [norm_sub_sq_real]
    linarith
  · intro π hπ
    have hfst : ∀ᵐ p ∂π, ∀ y : E d,
        ⟪p.1, y⟫ = u p.1 + v y → y = T p.1 := by
      have hm : ∀ᵐ x ∂Measure.map Prod.fst π, ∀ y : E d,
          ⟪x, y⟫ = u x + v y → y = T x := by
        rw [hπ.2.1]
        exact hstrictSource
      exact ae_of_ae_map measurable_fst.aemeasurable hm
    filter_upwards [hfst] with p hp
    intro heq
    apply hp p.2
    rw [norm_sub_sq_real] at heq
    linarith

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_PotentialLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter
open scoped Topology NNReal BoundedContinuousFunction

namespace Problem358

/-- Arzelà--Ascoli in the form needed for a sequence of transport potentials. -/
theorem exists_uniformly_convergent_subseq_of_lipschitz
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (u : ℕ → X → ℝ) (L : ℝ≥0) (M : ℝ)
    (hLip : ∀ n, LipschitzWith L (u n))
    (hbound : ∀ n x, |u n x| ≤ M) :
    ∃ (v : X → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      TendstoUniformly (fun n => u (φ n)) v atTop ∧ LipschitzWith L v := by
  let F : ℕ → X →ᵇ ℝ := fun n =>
    BoundedContinuousFunction.mkOfCompact ⟨u n, (hLip n).continuous⟩
  have hEqui : Equicontinuous (fun g : Set.range F => (g.1 : X → ℝ)) := by
    apply (LipschitzWith.uniformEquicontinuous _ L ?_).equicontinuous
    rintro ⟨g, n, rfl⟩
    exact hLip n
  have hcompact : IsCompact (closure (Set.range F)) := by
    apply BoundedContinuousFunction.arzela_ascoli (Set.Icc (-M) M) isCompact_Icc
    · intro g x hg
      obtain ⟨n, rfl⟩ := hg
      exact abs_le.mp (hbound n x)
    · exact hEqui
  obtain ⟨v, hv, φ, hφ, hlim⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (Set.mem_range_self n))
  have hunif : TendstoUniformly (fun n => u (φ n)) (fun x => v x) atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim
  refine ⟨v, φ, hφ, hunif, ?_⟩
  apply (isClosed_setOfPred_lipschitzWith L).mem_of_tendsto
    (tendsto_pi_nhds.mpr hunif.tendsto_at)
  exact Filter.Eventually.of_forall (fun n => hLip (φ n))

/-- Convexity on a fixed set is preserved by pointwise limits on that set. -/
theorem convexOn_of_pointwise_limit
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    {K : Set V} {u : ℕ → V → ℝ} {v : V → ℝ}
    (hconv : ∀ n, ConvexOn ℝ K (u n))
    (hlim : ∀ x ∈ K, Tendsto (fun n => u n x) atTop (𝓝 (v x))) :
    ConvexOn ℝ K v := by
  refine ⟨(hconv 0).1, ?_⟩
  intro x hx y hy a b ha hb hab
  apply le_of_tendsto_of_tendsto
    (hlim (a • x + b • y) ((hconv 0).1 hx hy ha hb hab))
    (((hlim x hx).const_mul a).add ((hlim y hy).const_mul b))
  exact Filter.Eventually.of_forall (fun n => (hconv n).2 hx hy ha hb hab)

/-- Normalized convex potentials with a uniform Lipschitz constant on a compact convex
body admit a uniformly convergent subsequence, and the limit has the same properties. -/
theorem exists_normalized_convex_potential_subseq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {K : Set V} (hK : IsCompact K)
    (x₀ : V) (hx₀ : x₀ ∈ K) (u : ℕ → V → ℝ) (L : ℝ≥0)
    (hLip : ∀ n, LipschitzOnWith L (u n) K)
    (hconv : ∀ n, ConvexOn ℝ K (u n))
    (hnormal : ∀ n, u n x₀ = 0) :
    ∃ (v : V → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      TendstoUniformlyOn (fun n => u (φ n)) v atTop K ∧
      LipschitzOnWith L v K ∧ ConvexOn ℝ K v ∧ v x₀ = 0 := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hbound : ∀ n (x : K), |u n x| ≤ (L : ℝ) * (R + ‖x₀‖) := by
    intro n x
    calc
      |u n x| = dist (u n x) (u n x₀) := by rw [hnormal n, dist_zero_right, Real.norm_eq_abs]
      _ ≤ (L : ℝ) * dist (x : V) x₀ := (hLip n).dist_le_mul x x.property x₀ hx₀
      _ ≤ (L : ℝ) * (R + ‖x₀‖) := by
        apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
        rw [dist_eq_norm]
        exact (norm_sub_le _ _).trans (add_le_add (hR x x.property) le_rfl)
  obtain ⟨w, φ, hφ, hwlim, hwLip⟩ := exists_uniformly_convergent_subseq_of_lipschitz
    (fun n (x : K) => u n x) L ((L : ℝ) * (R + ‖x₀‖))
    (fun n => (hLip n).to_restrict) hbound
  let v : V → ℝ := fun x => if hx : x ∈ K then w ⟨x, hx⟩ else 0
  have hv : ∀ x : K, v x = w x := by intro x; simp [v, x.property]
  have hvlim : TendstoUniformlyOn (fun n => u (φ n)) v atTop K := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    simpa only [Function.comp_def, hv] using hwlim
  have hvLip : LipschitzOnWith L v K := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [← hv, Subtype.dist_eq] using hwLip.dist_le_mul ⟨x, hx⟩ ⟨y, hy⟩
  refine ⟨v, φ, hφ, hvlim, hvLip, ?_, ?_⟩
  · exact convexOn_of_pointwise_limit (fun n => hconv (φ n))
      (fun x hx => hvlim.tendsto_at hx)
  · have hzero : Tendsto (fun n => u (φ n) x₀) atTop (𝓝 (0 : ℝ)) := by
      simpa only [hnormal] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    exact tendsto_nhds_unique (hvlim.tendsto_at hx₀) hzero

end Problem358

end

section

open Filter MeasureTheory
open scoped Topology

namespace Problem358

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {u : V → ℝ} {x p : V} {u' : V →L[ℝ] ℝ} {K : Set V}

/-- Supporting inequalities are closed under pointwise convergence of potentials
and convergence of the supporting slope. -/
theorem supporting_inequality_of_tendsto
    {ι : Type*} {l : Filter ι} [NeBot l]
    {uₙ : ι → V → ℝ} {pₙ : ι → V}
    (hx : x ∈ K)
    (hu : ∀ z ∈ K, Tendsto (fun n => uₙ n z) l (𝓝 (u z)))
    (hp : Tendsto pₙ l (𝓝 p))
    (hs : ∀ᶠ n in l, ∀ z ∈ K,
      uₙ n x + inner ℝ (pₙ n) (z - x) ≤ uₙ n z) :
    ∀ z ∈ K, u x + inner ℝ p (z - x) ≤ u z := by
  intro z hz
  exact le_of_tendsto_of_tendsto
    ((hu x hx).add (hp.inner tendsto_const_nhds))
    (hu z hz) (hs.mono fun n hn => hn z hz)

/-- Countably many almost-everywhere supporting inequalities pass to an
almost-everywhere converging sequence of slopes.  The potential convergence
is assumed on the whole body, so the resulting inequality is simultaneous
for every comparison point, not merely almost every comparison point. -/
theorem supporting_maps_of_ae_tendsto [MeasurableSpace V]
    (ρ : Measure V) {uₙ : ℕ → V → ℝ} {Tₙ : ℕ → V → V} {T : V → V}
    (hK : ∀ᵐ x ∂ρ, x ∈ K)
    (hu : ∀ z ∈ K, Tendsto (fun n => uₙ n z) atTop (𝓝 (u z)))
    (hT : ∀ᵐ x ∂ρ, Tendsto (fun n => Tₙ n x) atTop (𝓝 (T x)))
    (hs : ∀ n, ∀ᵐ x ∂ρ, ∀ z ∈ K,
      uₙ n x + inner ℝ (Tₙ n x) (z - x) ≤ uₙ n z) :
    ∀ᵐ x ∂ρ, ∀ z ∈ K, u x + inner ℝ (T x) (z - x) ≤ u z := by
  filter_upwards [hK, hT, ae_all_iff.mpr hs] with x hx hTx hsx
  exact supporting_inequality_of_tendsto hx hu hTx
    (Filter.Eventually.of_forall hsx)

/-- Compactly constrained supporting slopes converge wherever the limiting
potential is differentiable.  This is valid for arbitrary filters and requires
only pointwise convergence of potentials, not convergence of their derivatives. -/
theorem supporting_slopes_tendsto_of_isCompact
    {ι : Type*} {l : Filter ι} {uₙ : ι → V → ℝ} {pₙ : ι → V} {Y : Set V}
    (hY : IsCompact Y) (hx : x ∈ interior K)
    (hderiv : HasFDerivAt u (innerSL ℝ p) x)
    (hu : ∀ z ∈ K, Tendsto (fun n => uₙ n z) l (𝓝 (u z)))
    (hmem : ∀ᶠ n in l, pₙ n ∈ Y)
    (hs : ∀ᶠ n in l, ∀ z ∈ K,
      uₙ n x + inner ℝ (pₙ n) (z - x) ≤ uₙ n z) :
    Tendsto pₙ l (𝓝 p) := by
  apply hY.tendsto_nhds_of_unique_mapClusterPt hmem
  intro q _ hq
  obtain ⟨U, hUl, hUq⟩ := mapClusterPt_iff_ultrafilter.mp hq
  have hsupport : ∀ z ∈ K, u x + inner ℝ q (z - x) ≤ u z :=
    supporting_inequality_of_tendsto (interior_subset hx)
      (fun z hz => (hu z hz).mono_left hUl) hUq (hUl hs)
  exact ((innerSL_inj (𝕜 := ℝ)).mp
    (hasFDerivAt_eq_innerSL_of_supporting hderiv hx hsupport)).symm

/-- A differentiable pointwise limit of potentials admits a supporting slope
in the same compact target set, and the full slope family converges to it. -/
theorem exists_supporting_slope_limit_of_isCompact
    {ι : Type*} {l : Filter ι} [NeBot l]
    {uₙ : ι → V → ℝ} {pₙ : ι → V} {Y : Set V}
    (hY : IsCompact Y) (hx : x ∈ interior K)
    (hderiv : DifferentiableAt ℝ u x)
    (hu : ∀ z ∈ K, Tendsto (fun n => uₙ n z) l (𝓝 (u z)))
    (hmem : ∀ᶠ n in l, pₙ n ∈ Y)
    (hs : ∀ᶠ n in l, ∀ z ∈ K,
      uₙ n x + inner ℝ (pₙ n) (z - x) ≤ uₙ n z) :
    ∃ p ∈ Y, Tendsto pₙ l (𝓝 p) ∧
      ∀ z ∈ K, u x + inner ℝ p (z - x) ≤ u z := by
  obtain ⟨p, hpY, hp⟩ := hY.exists_mapClusterPt_of_frequently hmem.frequently
  obtain ⟨U, hUl, hUp⟩ := mapClusterPt_iff_ultrafilter.mp hp
  have hsupport : ∀ z ∈ K, u x + inner ℝ p (z - x) ≤ u z :=
    supporting_inequality_of_tendsto (interior_subset hx)
      (fun z hz => (hu z hz).mono_left hUl) hUp (hUl hs)
  have hdiff : HasFDerivAt u (innerSL ℝ p) x := by
    rw [← hasFDerivAt_eq_innerSL_of_supporting hderiv.hasFDerivAt hx hsupport]
    exact hderiv.hasFDerivAt
  exact ⟨p, hpY, supporting_slopes_tendsto_of_isCompact hY hx hdiff hu hmem hs,
    hsupport⟩

/-- The compact-slope limit construction holds almost everywhere simultaneously
for an entire sequence of supporting maps. -/
theorem ae_exists_supporting_map_limit [MeasurableSpace V]
    (ρ : Measure V) {uₙ : ℕ → V → ℝ} {Tₙ : ℕ → V → V} {Y : Set V}
    (hY : IsCompact Y)
    (hK : ∀ᵐ x ∂ρ, x ∈ interior K)
    (hderiv : ∀ᵐ x ∂ρ, DifferentiableAt ℝ u x)
    (hu : ∀ z ∈ K, Tendsto (fun n => uₙ n z) atTop (𝓝 (u z)))
    (hmem : ∀ n, ∀ᵐ x ∂ρ, Tₙ n x ∈ Y)
    (hs : ∀ n, ∀ᵐ x ∂ρ, ∀ z ∈ K,
      uₙ n x + inner ℝ (Tₙ n x) (z - x) ≤ uₙ n z) :
    ∀ᵐ x ∂ρ, ∃ p ∈ Y, Tendsto (fun n => Tₙ n x) atTop (𝓝 p) ∧
      ∀ z ∈ K, u x + inner ℝ p (z - x) ≤ u z := by
  filter_upwards [hK, hderiv, ae_all_iff.mpr hmem, ae_all_iff.mpr hs]
    with x hx hdx hmx hsx
  exact exists_supporting_slope_limit_of_isCompact hY hx hdx hu
    (Filter.Eventually.of_forall hmx) (Filter.Eventually.of_forall hsx)

end Problem358

end

noncomputable section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Problem358

/-- Compactly constrained supporting maps have a measurable limiting representative
when their potentials converge to an almost-everywhere differentiable potential. -/
theorem exists_measurable_supporting_map_limit
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (ρ : Measure V) {K Y : Set V} {uₙ : ℕ → V → ℝ} {u : V → ℝ}
    {Tₙ : ℕ → V → V}
    (hY : IsCompact Y)
    (hK : ∀ᵐ x ∂ρ, x ∈ interior K)
    (hderiv : ∀ᵐ x ∂ρ, DifferentiableAt ℝ u x)
    (hu : ∀ z ∈ K, Tendsto (fun n => uₙ n z) atTop (𝓝 (u z)))
    (hmeas : ∀ n, Measurable (Tₙ n))
    (hmem : ∀ n, ∀ᵐ x ∂ρ, Tₙ n x ∈ Y)
    (hs : ∀ n, ∀ᵐ x ∂ρ, ∀ z ∈ K,
      uₙ n x + inner ℝ (Tₙ n x) (z - x) ≤ uₙ n z) :
    ∃ T : V → V, Measurable T ∧
      (∀ᵐ x ∂ρ, Tendsto (fun n => Tₙ n x) atTop (𝓝 (T x))) ∧
      (∀ᵐ x ∂ρ, T x ∈ Y) ∧
      (∀ᵐ x ∂ρ, ∀ z ∈ K, u x + inner ℝ (T x) (z - x) ≤ u z) := by
  have hlim := ae_exists_supporting_map_limit ρ hY hK hderiv hu hmem hs
  obtain ⟨T, hT, hTlim⟩ := measurable_limit_of_tendsto_metrizable_ae
    (fun n => (hmeas n).aemeasurable) (hlim.mono (fun x hx => by
      obtain ⟨p, hpY, hplim, hps⟩ := hx
      exact ⟨p, hplim⟩))
  refine ⟨T, hT, hTlim, ?_, ?_⟩
  · filter_upwards [hlim, hTlim] with x hx hTx
    obtain ⟨p, hpY, hplim, hps⟩ := hx
    exact tendsto_nhds_unique hTx hplim ▸ hpY
  · exact supporting_maps_of_ae_tendsto ρ (hK.mono (fun x hx => interior_subset hx))
      hu hTlim hs

/-- Joint subsequential compactness of normalized convex potentials and their
compactly constrained supporting maps on a uniform convex source. -/
theorem exists_potential_and_map_limit
    {d : ℕ} {K Y : Set (E d)}
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hY : IsCompact Y)
    (x₀ : E d) (hx₀ : x₀ ∈ K)
    (uₙ : ℕ → E d → ℝ) (Tₙ : ℕ → E d → E d) (L : ℝ≥0)
    (hLip : ∀ n, LipschitzOnWith L (uₙ n) K)
    (hconv : ∀ n, ConvexOn ℝ K (uₙ n))
    (hnormal : ∀ n, uₙ n x₀ = 0)
    (hmeas : ∀ n, Measurable (Tₙ n))
    (hmem : ∀ n, ∀ᵐ x ∂uniformMeasure K, Tₙ n x ∈ Y)
    (hs : ∀ n, ∀ᵐ x ∂uniformMeasure K, ∀ z ∈ K,
      uₙ n x + inner ℝ (Tₙ n x) (z - x) ≤ uₙ n z) :
    ∃ (u : E d → ℝ) (T : E d → E d) (φ : ℕ → ℕ),
      StrictMono φ ∧ TendstoUniformlyOn (fun n => uₙ (φ n)) u atTop K ∧
      LipschitzOnWith L u K ∧ ConvexOn ℝ K u ∧ u x₀ = 0 ∧
      Measurable T ∧
      (∀ᵐ x ∂uniformMeasure K, Tendsto (fun n => Tₙ (φ n) x) atTop (𝓝 (T x))) ∧
      (∀ᵐ x ∂uniformMeasure K, T x ∈ Y) ∧
      (∀ᵐ x ∂uniformMeasure K, ∀ z ∈ K,
        u x + inner ℝ (T x) (z - x) ≤ u z) := by
  obtain ⟨u, φ, hφ, hulim, huLip, huconv, hunormal⟩ :=
    exists_normalized_convex_potential_subseq hK x₀ hx₀ uₙ L hLip hconv hnormal
  have hudiff := ae_differentiableAt_uniformMeasure hKconv hK.measurableSet huLip
  obtain ⟨T, hTmeas, hTlim, hTmem, hTs⟩ := exists_measurable_supporting_map_limit
    (uniformMeasure K) hY (hudiff.mono (fun x hx => hx.1))
    (hudiff.mono (fun x hx => hx.2)) (fun z hz => hulim.tendsto_at hz)
    (fun n => hmeas (φ n)) (fun n => hmem (φ n)) (fun n => hs (φ n))
  exact ⟨u, T, φ, hφ, hulim, huLip, huconv, hunormal, hTmeas, hTlim, hTmem, hTs⟩

end Problem358

namespace Problem358

/-- The approximation step for Brenier-map existence. Finite supporting potentials
and quantized target laws suffice; quantitative stability is not an assumption. -/
theorem exists_uniqueOptimalMap_of_quantized_supporting_potentials
    {d : ℕ} {K Y : Set (E d)} {μ : Measure (E d)}
    [IsFiniteMeasure (uniformMeasure K)] [IsFiniteMeasure μ]
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hY : IsCompact Y)
    (hμ : IsSupported μ Y) (x₀ : E d) (hx₀ : x₀ ∈ K)
    (uₙ : ℕ → E d → ℝ) (Tₙ Qₙ : ℕ → E d → E d) (L : ℝ≥0)
    (hLip : ∀ n, LipschitzOnWith L (uₙ n) K)
    (hconv : ∀ n, ConvexOn ℝ K (uₙ n))
    (hnormal : ∀ n, uₙ n x₀ = 0)
    (hTmeas : ∀ n, Measurable (Tₙ n))
    (hQmeas : ∀ n, Measurable (Qₙ n))
    (hQmem : ∀ n, ∀ᵐ y ∂μ, Qₙ n y ∈ Y)
    (hQlim : ∀ᵐ y ∂μ, Tendsto (fun n => Qₙ n y) atTop (𝓝 y))
    (hpush : ∀ n, Measure.map (Tₙ n) (uniformMeasure K) = Measure.map (Qₙ n) μ)
    (hs : ∀ n, ∀ᵐ x ∂uniformMeasure K, ∀ z ∈ K,
      uₙ n x + inner ℝ (Tₙ n x) (z - x) ≤ uₙ n z) :
    ∃ (T : E d → E d) (φ : ℕ → ℕ), StrictMono φ ∧
      IsUniqueQuadraticOptimalMap (uniformMeasure K) μ T ∧
      (∀ᵐ x ∂uniformMeasure K, T x ∈ Y) ∧
      (∀ᵐ x ∂uniformMeasure K, Tendsto (fun n => Tₙ (φ n) x) atTop (𝓝 (T x))) ∧
      Tendsto (fun n => mapL2Dist (uniformMeasure K) (Tₙ (φ n)) T) atTop (𝓝 0) := by
  have hTmem : ∀ n, ∀ᵐ x ∂uniformMeasure K, Tₙ n x ∈ Y := by
    intro n
    apply ae_of_ae_map (hTmeas n).aemeasurable
    rw [hpush n]
    exact (ae_map_iff (hQmeas n).aemeasurable hY.measurableSet).mpr (hQmem n)
  obtain ⟨u, T, φ, hφ, hulim, huLip, huconv, hunormal, hT, hTlim, hTY, hTs⟩ :=
    exists_potential_and_map_limit hK hKconv hY x₀ hx₀ uₙ Tₙ L
      hLip hconv hnormal hTmeas hTmem hs
  have hlimitlaw : Measure.map T (uniformMeasure K) = μ :=
    CompactIntegrability.map_eq_of_ae_tendsto_of_map_eq_quantizers
      (fun n => hTmeas (φ n)) hT (fun n => hQmeas (φ n)) hY
      (fun n => hTmem (φ n)) (fun n => hQmem (φ n)) hTlim
      (hQlim.mono (fun y hy => hy.comp hφ.tendsto_atTop)) (fun n => hpush (φ n))
  have hopt : IsUniqueQuadraticOptimalMap (uniformMeasure K) μ T := by
    apply isUniqueQuadraticOptimalMap_uniform_of_supporting_potential
      hK ⟨x₀, hx₀⟩ hKconv hY hμ huLip hT hlimitlaw
    filter_upwards [hTs] with x hx
    intro z hz
    simpa only [real_inner_comm (z - x) (T x)] using hx z hz
  exact ⟨T, φ, hφ, hopt, hTY, hTlim,
    CompactIntegrability.tendsto_mapL2Dist_of_ae_tendsto
      (fun n => hTmeas (φ n)) hT hY (fun n => hTmem (φ n)) hTlim⟩

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_CellGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*}

/-- With distinct slopes, any maximizing index selects the closed affine cell
almost everywhere. No measurability of the supplied selector is required. -/
theorem ae_fiber_eq_closedCell [Countable ι]
    {K : Set (E d)} (hK : MeasurableSet K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (k : E d → ι)
    (hk : ∀ᵐ x ∂uniformMeasure K, ∀ j,
      ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x)) (i : ι) :
    {x | k x = i} =ᵐ[uniformMeasure K] closedCell K y c i := by
  filter_upwards [UniformSource.ae_mem hK,
    uniform_ae_affine_tie_implies_slopes_eq K y c, hk] with x hx ht hk
  apply propext
  constructor
  · intro hi
    exact ⟨hx, fun j => hi ▸ hk j⟩
  · intro hi
    apply hy
    exact ht (k x) i (le_antisymm (hi.2 (k x)) (hk i))

/-- Closed-cell masses are exactly the masses of any maximizing selector. -/
theorem measure_fiber_eq_closedCell [Countable ι]
    {K : Set (E d)} (hK : MeasurableSet K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (k : E d → ι)
    (hk : ∀ᵐ x ∂uniformMeasure K, ∀ j,
      ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x)) (i : ι) :
    uniformMeasure K {x | k x = i} =
      uniformMeasure K (closedCell K y c i) :=
  measure_congr (ae_fiber_eq_closedCell hK y c hy k hk i)

/-- The real-valued mass form used in the moving-potential energy estimate. -/
theorem real_fiber_eq_closedCell [Countable ι]
    {K : Set (E d)} (hK : MeasurableSet K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (k : E d → ι)
    (hk : ∀ᵐ x ∂uniformMeasure K, ∀ j,
      ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x)) (i : ι) :
    (uniformMeasure K).real {x | k x = i} =
      (uniformMeasure K).real (closedCell K y c i) :=
  congrArg ENNReal.toReal (measure_fiber_eq_closedCell hK y c hy k hk i)

/-- A single globally measurable selector works for all parameters. Its masses
agree with closed-cell masses at every parameter with distinct slopes, so no
injectivity at endpoint parameters or outside the time interval is imposed. -/
theorem exists_joint_measurable_selector_closedCell_masses
    {P : Type*} [MeasurableSpace P] [MeasurableSpace ι]
    [Fintype ι] [Nonempty ι]
    {K : Set (E d)} (hK : MeasurableSet K)
    (y : P → ι → E d) (c : P → ι → ℝ)
    (hy : ∀ i, Measurable (fun p => y p i))
    (hc : ∀ i, Measurable (fun p => c p i)) :
    ∃ k : P × E d → ι, Measurable k ∧
      (∀ p x j, ⟪x, y p j⟫ + c p j ≤
        ⟪x, y p (k (p, x))⟫ + c p (k (p, x))) ∧
      ∀ p, Function.Injective (y p) → ∀ i,
        (uniformMeasure K).real {x | k (p, x) = i} =
          (uniformMeasure K).real (closedCell K (y p) (c p) i) := by
  have hf (i : ι) : Measurable
      (fun p : P × E d => ⟪p.2, y p.1 i⟫ + c p.1 i) :=
    (measurable_snd.inner ((hy i).comp measurable_fst)).add
      ((hc i).comp measurable_fst)
  obtain ⟨k, hk, _, hmax⟩ := exists_measurable_argmax
    (fun i (p : P × E d) => ⟪p.2, y p.1 i⟫ + c p.1 i) hf
  refine ⟨k, hk, fun p x j => hmax (p, x) j, ?_⟩
  intro p hp i
  exact real_fiber_eq_closedCell hK (y p) (c p) hp (fun x => k (p, x))
    (Filter.Eventually.of_forall fun x => hmax (p, x)) i

/-- Prescribed closed-cell masses on a chosen set of parameters are realized by
one jointly measurable selector, even when sites collide elsewhere. -/
theorem exists_joint_measurable_selector_prescribed_masses
    {P : Type*} [MeasurableSpace P] [MeasurableSpace ι]
    [Fintype ι] [Nonempty ι]
    {K : Set (E d)} (hK : MeasurableSet K)
    (y : P → ι → E d) (c m : P → ι → ℝ) (s : Set P)
    (hy : ∀ i, Measurable (fun p => y p i))
    (hc : ∀ i, Measurable (fun p => c p i))
    (hinj : ∀ p ∈ s, Function.Injective (y p))
    (hm : ∀ p ∈ s, ∀ i,
      (uniformMeasure K).real (closedCell K (y p) (c p) i) = m p i) :
    ∃ k : P × E d → ι, Measurable k ∧
      (∀ p x j, ⟪x, y p j⟫ + c p j ≤
        ⟪x, y p (k (p, x))⟫ + c p (k (p, x))) ∧
      ∀ p ∈ s, ∀ i, (uniformMeasure K).real {x | k (p, x) = i} = m p i := by
  obtain ⟨k, hk, hmax, hmass⟩ :=
    exists_joint_measurable_selector_closedCell_masses hK y c hy hc
  exact ⟨k, hk, hmax, fun p hp i => (hmass p (hinj p hp) i).trans (hm p hp i)⟩

end Problem358.CellGeometry

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Potential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped RealInnerProductSpace Topology

namespace Problem358
namespace MaxPotential

variable {ι V : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem supporting_inequality (y : ι → V) (c : ι → ℝ) (x z : V) (i : ι)
    (h : ∀ j, ⟪x, y j⟫ + c j ≤ ⟪x, y i⟫ + c i) :
    potential y c x + ⟪z - x, y i⟫ ≤ potential y c z := by
  rw [affine_eq_potential y c x i h, inner_sub_left]
  linarith [affine_le_potential y c z i]

theorem convexOn_potential (y : ι → V) (c : ι → ℝ) :
    ConvexOn ℝ Set.univ (potential y c) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx z hz a b ha hb hab
  apply potential_le
  intro i
  simp only [inner_add_left, real_inner_smul_left, smul_eq_mul]
  have hx' := affine_le_potential y c x i
  have hz' := affine_le_potential y c z i
  have hc : a * c i + b * c i = c i := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx' ha, mul_le_mul_of_nonneg_left hz' hb]

theorem potential_sub_le (y : ι → V) (c : ι → ℝ) (L : NNReal)
    (hy : ∀ i, ‖y i‖ ≤ L) (x z : V) :
    potential y c x - potential y c z ≤ (L : ℝ) * ‖x - z‖ := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i => ⟪x, y i⟫ + c i)
  change potential y c x = _ at hmax
  have hz := affine_le_potential y c z i
  have hinner : ⟪x - z, y i⟫ ≤ ‖x - z‖ * (L : ℝ) := by
    calc
      ⟪x - z, y i⟫ ≤ |⟪x - z, y i⟫| := le_abs_self _
      _ = ‖⟪x - z, y i⟫‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x - z‖ * ‖y i‖ := norm_inner_le_norm _ _
      _ ≤ ‖x - z‖ * (L : ℝ) := mul_le_mul_of_nonneg_left (hy i) (norm_nonneg _)
  rw [inner_sub_left] at hinner
  rw [hmax]
  nlinarith

theorem lipschitzWith_potential (y : ι → V) (c : ι → ℝ) (L : NNReal)
    (hy : ∀ i, ‖y i‖ ≤ L) : LipschitzWith L (potential y c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  rw [Real.dist_eq, dist_eq_norm]
  apply abs_le.mpr
  constructor
  · have h := potential_sub_le y c L hy z x
    rw [norm_sub_rev] at h
    linarith
  · exact potential_sub_le y c L hy x z

end MaxPotential
end Problem358

end

/-! Uniqueness of finite affine intercepts from connected full-support sources.
This route uses finite-range continuity, not differentiability of moving cells. -/

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Quantization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set

namespace Problem358

/-- A Borel nearest-point selection on a finite set, with a default point. -/
theorem exists_finite_nearest_selection
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (y₀ : X) (s : Finset X) :
    ∃ q : SimpleFunc X X, (∀ x, q x = y₀ ∨ q x ∈ s) ∧
      ∀ x y, y ∈ s → dist (q x) x ≤ dist y x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨SimpleFunc.const X y₀, ?_, ?_⟩
      · intro x
        exact Or.inl rfl
      · simp
  | @insert a s ha ih =>
      obtain ⟨q, hqmem, hqdist⟩ := ih
      let A : Set X := {x | dist a x ≤ dist (q x) x}
      have hA : MeasurableSet A :=
        measurableSet_le (measurable_const.dist measurable_id)
          (q.measurable.dist measurable_id)
      let r : SimpleFunc X X := SimpleFunc.piecewise A hA (SimpleFunc.const X a) q
      refine ⟨r, ?_, ?_⟩
      · intro x
        by_cases hx : x ∈ A
        · right
          simp [r, SimpleFunc.coe_piecewise, Set.piecewise, hx]
        · rcases hqmem x with h | h
          · left
            simpa [r, SimpleFunc.coe_piecewise, Set.piecewise, hx] using h
          · right
            simpa [r, SimpleFunc.coe_piecewise, Set.piecewise, hx] using
              (Finset.mem_insert_of_mem h : q x ∈ insert a s)
      · intro x y hy
        by_cases hx : x ∈ A
        · have hax : dist a x ≤ dist (q x) x := hx
          simp only [r, SimpleFunc.coe_piecewise, Set.piecewise, hx, ite_true,
            SimpleFunc.const_apply]
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact le_rfl
          · exact hax.trans (hqdist x y hy)
        · have hax : dist (q x) x ≤ dist a x := (lt_of_not_ge hx).le
          simp only [r, SimpleFunc.coe_piecewise, Set.piecewise, hx, ite_false]
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact hax
          · exact hqdist x y hy

/-- Compact sets admit finite-range Borel quantizers valued in the same set. -/
theorem exists_compact_quantizer
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {Y : Set X} (hY : IsCompact Y) (hne : Y.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : SimpleFunc X X, (∀ x, q x ∈ Y) ∧ ∀ x ∈ Y, dist (q x) x < ε := by
  classical
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨s, hsY, hs, hcover⟩ := hY.finite_cover_balls hε
  obtain ⟨q, hqmem, hqdist⟩ := exists_finite_nearest_selection y₀ hs.toFinset
  refine ⟨q, ?_, ?_⟩
  · intro x
    rcases hqmem x with h | h
    · simpa [h] using hy₀
    · exact hsY (by simpa using h)
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover hx)
    exact (hqdist x y (by simpa using hy)).trans_lt
      (by simpa [Metric.mem_ball, dist_comm] using hxy)

/-- Pushing a measure through a simple function gives a finitely supported measure. -/
theorem simpleFunc_map_finite_support {d : ℕ} (μ : Measure (E d))
    (q : SimpleFunc (E d) (E d)) :
    (Set.range q).Finite ∧ IsSupported (Measure.map q μ) (Set.range q) := by
  refine ⟨q.finite_range, ?_⟩
  unfold IsSupported
  rw [Measure.map_apply q.measurable q.finite_range.measurableSet.compl]
  have hempty : q ⁻¹' (Set.range q)ᶜ = ∅ := by
    ext x
    simp
  rw [hempty, measure_empty]

end Problem358

end

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Problem358

/-- Zero-mass sites can be discarded from any finite support without changing the measure. -/
theorem exists_positive_atomic_support {d : ℕ} {μ : Measure (E d)}
    [IsProbabilityMeasure μ] {F : Set (E d)} (hF : F.Finite)
    (hμ : IsSupported μ F) :
    ∃ S : Finset (E d), S.Nonempty ∧ (S : Set (E d)) ⊆ F ∧
      (∀ x ∈ S, 0 < μ {x}) ∧ (∑ x ∈ S, μ {x}) = 1 ∧
      μ = ∑ x ∈ S, μ {x} • Measure.dirac x := by
  classical
  have hae : ∀ᵐ x ∂μ, x ∈ hF.toFinset := by
    simpa only [hF.mem_toFinset] using (ae_iff.mpr hμ : ∀ᵐ x ∂μ, x ∈ F)
  have hrepr := Measure.ae_mem_finset_iff.mp hae
  let S := hF.toFinset.filter (fun x => μ {x} ≠ 0)
  have hreprS : μ = ∑ x ∈ S, μ {x} • Measure.dirac x := by
    calc
      μ = ∑ x ∈ hF.toFinset, μ {x} • Measure.dirac x := hrepr
      _ = ∑ x ∈ S, μ {x} • Measure.dirac x := by
        dsimp [S]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro x hx
        by_cases h : μ {x} = 0 <;> simp [h]
  have hsum : (∑ x ∈ S, μ {x}) = 1 := by
    have h := congrArg (fun ν : Measure (E d) => ν Set.univ) hreprS
    simpa using h.symm
  refine ⟨S, ?_, ?_, ?_, hsum, hreprS⟩
  · by_contra h
    have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [hempty] at hsum
  · intro x hx
    exact hF.mem_toFinset.mp (Finset.mem_filter.mp hx).1
  · intro x hx
    exact pos_iff_ne_zero.mpr (Finset.mem_filter.mp hx).2

/-- The finite-support representation can use positive ordinary real weights. -/
theorem exists_positive_real_atomic_support {d : ℕ} {μ : Measure (E d)}
    [IsProbabilityMeasure μ] {F : Set (E d)} (hF : F.Finite)
    (hμ : IsSupported μ F) :
    ∃ S : Finset (E d), S.Nonempty ∧ (S : Set (E d)) ⊆ F ∧
      (∀ x ∈ S, 0 < (μ {x}).toReal) ∧ (∑ x ∈ S, (μ {x}).toReal) = 1 ∧
      μ = ∑ x ∈ S, ENNReal.ofReal ((μ {x}).toReal) • Measure.dirac x := by
  obtain ⟨S, hS, hsub, hpos, hsum, hrepr⟩ := exists_positive_atomic_support hF hμ
  refine ⟨S, hS, hsub, ?_, ?_, ?_⟩
  · intro x hx
    exact ENNReal.toReal_pos (ne_of_gt (hpos x hx)) (measure_singleton_lt_top.ne)
  · rw [← ENNReal.toReal_sum (fun x hx => measure_singleton_lt_top.ne), hsum]
    simp
  · simpa only [ENNReal.ofReal_toReal measure_singleton_lt_top.ne] using hrepr

/-- A finite supported probability has a presentation by distinct sites and strictly
positive real weights, indexed by a nonempty finite ordinal. -/
theorem exists_positive_finite_atomic_presentation {d : ℕ} {μ : Measure (E d)}
    [IsProbabilityMeasure μ] {F : Set (E d)} (hF : F.Finite)
    (hμ : IsSupported μ F) :
    ∃ n : ℕ, 0 < n ∧ ∃ (y : Fin n → E d) (w : Fin n → ℝ),
      Function.Injective y ∧ (∀ i, y i ∈ F) ∧ (∀ i, 0 < w i) ∧
      (∑ i, w i) = 1 ∧ μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (y i) := by
  classical
  obtain ⟨S, hS, hsub, hpos, hsum, hrepr⟩ := exists_positive_real_atomic_support hF hμ
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  have hn : 0 < Fintype.card S := by
    apply Fintype.card_pos_iff.mpr
    obtain ⟨x, hx⟩ := hS
    exact ⟨⟨x, hx⟩⟩
  refine ⟨Fintype.card S, hn, (fun i => (e i).val),
    (fun i => (μ {(e i).val}).toReal), Subtype.val_injective.comp e.injective,
    (fun i => hsub (e i).property), (fun i => hpos _ (e i).property), ?_, ?_⟩
  · calc
      _ = ∑ x : S, (μ {x.val}).toReal := e.sum_comp _
      _ = ∑ x ∈ S, (μ {x}).toReal := Finset.sum_coe_sort S (fun x : E d => (μ {x}).toReal)
      _ = 1 := hsum
  · calc
      μ = ∑ x ∈ S, ENNReal.ofReal ((μ {x}).toReal) • Measure.dirac x := hrepr
      _ = ∑ x : S, ENNReal.ofReal ((μ {x.val}).toReal) • Measure.dirac x.val :=
        (Finset.sum_coe_sort S (fun x : E d => ENNReal.ofReal ((μ {x}).toReal) • Measure.dirac x)).symm
      _ = _ := (e.sum_comp _).symm

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Existence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal RealInnerProductSpace

namespace Problem358

variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Finite-target existence together with a globally convex normalized Lipschitz
potential and its pointwise supporting-slope inequality. -/
theorem exists_uniform_atomic_map_and_potential
    (K : Set (E d)) [IsProbabilityMeasure (uniformMeasure K)]
    (hK : IsCompact K) (y : ι → E d) (hinj : Function.Injective y)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (L : NNReal) (hL : ∀ i, ‖y i‖ ≤ L) (x₀ : E d) :
    ∃ (u : E d → ℝ) (T : E d → E d),
      IsUniqueQuadraticOptimalMap (uniformMeasure K)
        (∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i)) T ∧
      ConvexOn ℝ Set.univ u ∧ LipschitzWith L u ∧ u x₀ = 0 ∧
      (∀ x, T x ∈ Set.range y) ∧
      ∀ x z, u x + ⟪T x, z - x⟫ ≤ u z := by
  obtain ⟨c, k, hc, hk, hmax, hmass⟩ :=
    MaxPotential.exists_prescribed_cell_masses_uniform K hK y hinj m hm hsum
  let T : E d → E d := fun x => y (k x)
  let u : E d → ℝ := fun x => MaxPotential.potential y c x - MaxPotential.potential y c x₀
  have hy : Measurable y := measurable_of_countable y
  have hT : Measurable T := hy.comp hk
  have hweights : ∀ i, uniformMeasure K (k ⁻¹' {i}) = ENNReal.ofReal (m i) := by
    intro i
    have hi : (uniformMeasure K).real (k ⁻¹' {i}) = m i := hmass i
    rw [← hi]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hpush := map_finite_selector_of_masses (uniformMeasure K) k hk y
    (fun i => ENNReal.ofReal (m i)) hweights
  have hopt := isUniqueQuadraticOptimalMap_uniform_of_finite_affine K hK y c hinj hT
    (Filter.Eventually.of_forall (fun x => ⟨k x, rfl, hmax x⟩))
  refine ⟨u, T, hpush ▸ hopt, ?_, ?_, ?_, ?_, ?_⟩
  · exact (MaxPotential.convexOn_potential y c).sub
      (concaveOn_const _ convex_univ)
  · apply LipschitzWith.of_dist_le_mul
    intro x z
    simpa only [u, Real.dist_eq, sub_sub_sub_cancel_right] using
      (MaxPotential.lipschitzWith_potential y c L hL).dist_le_mul x z
  · simp [u]
  · intro x
    exact ⟨k x, rfl⟩
  · intro x z
    have h := MaxPotential.supporting_inequality y c x z (k x) (hmax x)
    dsimp [u, T]
    rw [real_inner_comm] at h
    linarith

/-- Presentation-free finite-source data for compactness/approximation arguments. -/
theorem exists_uniform_finite_map_and_potential
    (K : Set (E d)) (hK : IsCompact K) (hinterior : (interior K).Nonempty)
    (μ : Measure (E d)) [IsProbabilityMeasure μ]
    {F Y : Set (E d)} (hF : F.Finite) (hFY : F ⊆ Y) (hμ : IsSupported μ F)
    (L : NNReal) (hL : ∀ z ∈ Y, ‖z‖ ≤ L) (x₀ : E d) :
    ∃ (u : E d → ℝ) (T : E d → E d),
      IsUniqueQuadraticOptimalMap (uniformMeasure K) μ T ∧
      ConvexOn ℝ Set.univ u ∧ LipschitzWith L u ∧ u x₀ = 0 ∧
      (∀ x, T x ∈ Y) ∧ ∀ x z, u x + ⟪T x, z - x⟫ ≤ u z := by
  let : IsProbabilityMeasure (uniformMeasure K) := UniformSource.probability hK hinterior
  obtain ⟨n, hn, y, m, hy, hyF, hm, hsum, hrepr⟩ :=
    exists_positive_finite_atomic_presentation hF hμ
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨u, T, hT, hu, hLip, hnorm, hrange, hsupport⟩ :=
    exists_uniform_atomic_map_and_potential K hK y hy m hm hsum L
      (fun i => hL (y i) (hFY (hyF i))) x₀
  refine ⟨u, T, hrepr.symm ▸ hT, hu, hLip, hnorm, ?_, hsupport⟩
  intro x
  obtain ⟨i, hi⟩ := hrange x
  rw [← hi]
  exact hFY (hyF i)

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Approximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358

/-- An estimate against every finite-cost coupling descends to the transport infimum.
The finite-cost witness is essential because the definition sends infinite cost to zero. -/
theorem le_wasserstein2_add_of_le_rootCost {d : ℕ} {μ ν : Measure (E d)}
    {a δ : ℝ}
    (hfinite : ∃ π : Measure (E d × E d),
      IsCoupling μ ν π ∧ quadraticPlanCost π ≠ ∞)
    (hbound : ∀ π : Measure (E d × E d), IsCoupling μ ν π →
      quadraticPlanCost π ≠ ∞ →
        a ≤ Real.sqrt (quadraticPlanCost π).toReal + δ) :
    a ≤ wasserstein2 μ ν + δ := by
  by_cases ha : a ≤ δ
  · linarith [wasserstein2_nonneg μ ν]
  have ht : 0 < a - δ := by linarith
  let S : Set ℝ≥0∞ := {r | ∃ π : Measure (E d × E d),
    IsCoupling μ ν π ∧ quadraticPlanCost π = r}
  have hinf : sInf S ≠ ∞ := by
    obtain ⟨π, hπ, hcost⟩ := hfinite
    exact ne_top_of_le_ne_top hcost (sInf_le ⟨π, hπ, rfl⟩)
  have hlower : ENNReal.ofReal ((a - δ) ^ 2) ≤ sInf S := by
    apply le_sInf
    rintro r ⟨π, hπ, rfl⟩
    by_cases hcost : quadraticPlanCost π = ∞
    · simp [hcost]
    apply (ENNReal.ofReal_le_iff_le_toReal hcost).2
    have hr : a - δ ≤ Real.sqrt (quadraticPlanCost π).toReal := by
      linarith [hbound π hπ hcost]
    have hs := (sq_le_sq₀ ht.le (Real.sqrt_nonneg _)).2 hr
    simpa only [Real.sq_sqrt ENNReal.toReal_nonneg] using hs
  have hs : (a - δ) ^ 2 ≤ (sInf S).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hinf).1 hlower
  have hr : a - δ ≤ wasserstein2 μ ν := Real.le_sqrt_of_sq_le hs
  linarith

/-- Quantizing the two marginals changes their Wasserstein distance by at most
 the two uniform approximation errors. This does not require an optimal coupling. -/
theorem wasserstein2_map_le {d : ℕ} {μ ν : Measure (E d)}
    {Q R : E d → E d} (hQ : Measurable Q) (hR : Measurable R)
    {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hQerr : ∀ᵐ x ∂μ, ‖Q x - x‖ ≤ ε)
    (hRerr : ∀ᵐ y ∂ν, ‖R y - y‖ ≤ η)
    (hfinite : ∃ π : Measure (E d × E d),
      IsCoupling μ ν π ∧ quadraticPlanCost π ≠ ∞) :
    wasserstein2 (Measure.map Q μ) (Measure.map R ν) ≤
      wasserstein2 μ ν + ε + η := by
  have h := le_wasserstein2_add_of_le_rootCost (δ := ε + η) hfinite
    (fun π hπ hcost =>
      (wasserstein2_le_of_coupling (hπ.map hQ hR)
        (quadraticPlanCost_map_ne_top hπ hQ hR hQerr hRerr hcost)).trans
        (by simpa only [add_assoc] using
          sqrt_quadraticPlanCost_map_le hπ hQ hR hε hη hQerr hRerr hcost))
  simpa only [add_assoc] using h

/-- Compactly supported probability marginals admit a finite-cost coupling. -/
theorem exists_finiteCost_coupling_of_compact {d : ℕ} {μ ν : Measure (E d)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K Y : Set (E d)} (hK : IsCompact K) (hY : IsCompact Y)
    (hμ : IsSupported μ K) (hν : IsSupported ν Y) :
    ∃ π : Measure (E d × E d), IsCoupling μ ν π ∧ quadraticPlanCost π ≠ ∞ := by
  have hπ : IsCoupling μ ν (μ.prod ν) := by
    refine ⟨inferInstance, ?_, ?_⟩ <;> simp
  exact ⟨μ.prod ν, hπ, hπ.quadraticPlanCost_ne_top_of_compact hK hY hμ hν⟩

/-- The approximation inequality with the compact-support hypotheses of the challenge. -/
theorem wasserstein2_map_le_of_compact {d : ℕ} {μ ν : Measure (E d)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K Y : Set (E d)} (hK : IsCompact K) (hY : IsCompact Y)
    (hμ : IsSupported μ K) (hν : IsSupported ν Y)
    {Q R : E d → E d} (hQ : Measurable Q) (hR : Measurable R)
    {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hQerr : ∀ᵐ x ∂μ, ‖Q x - x‖ ≤ ε)
    (hRerr : ∀ᵐ y ∂ν, ‖R y - y‖ ≤ η) :
    wasserstein2 (Measure.map Q μ) (Measure.map R ν) ≤
      wasserstein2 μ ν + ε + η :=
  wasserstein2_map_le hQ hR hε hη hQerr hRerr
    (exists_finiteCost_coupling_of_compact hK hY hμ hν)

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace Problem358

/-- Uniformly vanishing almost-everywhere quantization errors give pointwise convergence. -/
theorem ae_tendsto_of_quantization_error {d : ℕ} {μ : Measure (E d)}
    {Q : ℕ → E d → E d} {ε : ℕ → ℝ}
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hQerr : ∀ n, ∀ᵐ x ∂μ, ‖Q n x - x‖ ≤ ε n) :
    ∀ᵐ x ∂μ, Tendsto (fun n => Q n x) atTop (𝓝 x) := by
  have hall : ∀ᵐ x ∂μ, ∀ n, ‖Q n x - x‖ ≤ ε n := ae_all_iff.mpr hQerr
  filter_upwards [hall] with x hx
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun n => norm_nonneg _) hx hεlim)

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal RealInnerProductSpace

namespace Problem358

/-- A paired finite-target estimate passes to arbitrary target laws. The only
quantitative assumption is the bound for the supplied approximating maps; all
limit maps and their all-plan uniqueness certificates are constructed here. -/
theorem exists_uniqueOptimal_pair_of_quantized_stability
    {d : ℕ} {K Y : Set (E d)}
    [IsFiniteMeasure (uniformMeasure K)]
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hY : IsCompact Y)
    (x₀ : E d) (hx₀ : x₀ ∈ K)
    {μ ν : Measure (E d)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsSupported μ Y) (hν : IsSupported ν Y)
    (u v : ℕ → E d → ℝ) (T S Q R : ℕ → E d → E d) (L : ℝ≥0)
    (huLip : ∀ n, LipschitzOnWith L (u n) K)
    (hvLip : ∀ n, LipschitzOnWith L (v n) K)
    (huconv : ∀ n, ConvexOn ℝ K (u n))
    (hvconv : ∀ n, ConvexOn ℝ K (v n))
    (hunormal : ∀ n, u n x₀ = 0) (hvnormal : ∀ n, v n x₀ = 0)
    (hT : ∀ n, Measurable (T n)) (hS : ∀ n, Measurable (S n))
    (hQ : ∀ n, Measurable (Q n)) (hR : ∀ n, Measurable (R n))
    (hQmem : ∀ n, ∀ᵐ y ∂μ, Q n y ∈ Y)
    (hRmem : ∀ n, ∀ᵐ y ∂ν, R n y ∈ Y)
    (hTpush : ∀ n, Measure.map (T n) (uniformMeasure K) = Measure.map (Q n) μ)
    (hSpush : ∀ n, Measure.map (S n) (uniformMeasure K) = Measure.map (R n) ν)
    (hTs : ∀ n, ∀ᵐ x ∂uniformMeasure K,
      ∀ z ∈ K, u n x + ⟪T n x, z - x⟫ ≤ u n z)
    (hSs : ∀ n, ∀ᵐ x ∂uniformMeasure K,
      ∀ z ∈ K, v n x + ⟪S n x, z - x⟫ ≤ v n z)
    {ε η : ℕ → ℝ} (hε : ∀ n, 0 ≤ ε n) (hη : ∀ n, 0 ≤ η n)
    (hεlim : Tendsto ε atTop (𝓝 0)) (hηlim : Tendsto η atTop (𝓝 0))
    (hQerr : ∀ n, ∀ᵐ y ∂μ, ‖Q n y - y‖ ≤ ε n)
    (hRerr : ∀ n, ∀ᵐ y ∂ν, ‖R n y - y‖ ≤ η n)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n, mapL2Dist (uniformMeasure K) (T n) (S n) ≤
      C * Real.rpow (wasserstein2 (Measure.map (Q n) μ) (Measure.map (R n) ν))
        (1 / 3 : ℝ)) :
    ∃ Tμ Tν : E d → E d,
      IsUniqueQuadraticOptimalMap (uniformMeasure K) μ Tμ ∧
      IsUniqueQuadraticOptimalMap (uniformMeasure K) ν Tν ∧
      mapL2Dist (uniformMeasure K) Tμ Tν ≤
        C * Real.rpow (wasserstein2 μ ν) (1 / 3 : ℝ) := by
  have hQlim := ae_tendsto_of_quantization_error hεlim hQerr
  have hRlim := ae_tendsto_of_quantization_error hηlim hRerr
  obtain ⟨Tμ, φ, hφ, hTμ, hTμmem, _, hTμlim⟩ :=
    exists_uniqueOptimalMap_of_quantized_supporting_potentials
      hK hKconv hY hμ x₀ hx₀ u T Q L huLip huconv hunormal
      hT hQ hQmem hQlim hTpush hTs
  have hRφlim : ∀ᵐ y ∂ν,
      Tendsto (fun n => R (φ n) y) atTop (𝓝 y) := by
    filter_upwards [hRlim] with y hy
    exact hy.comp hφ.tendsto_atTop
  obtain ⟨Tν, ψ, hψ, hTν, hTνmem, _, hTνlim⟩ :=
    exists_uniqueOptimalMap_of_quantized_supporting_potentials
      hK hKconv hY hν x₀ hx₀ (fun n => v (φ n))
      (fun n => S (φ n)) (fun n => R (φ n)) L
      (fun n => hvLip (φ n)) (fun n => hvconv (φ n))
      (fun n => hvnormal (φ n)) (fun n => hS (φ n))
      (fun n => hR (φ n)) (fun n => hRmem (φ n)) hRφlim
      (fun n => hSpush (φ n)) (fun n => hSs (φ n))
  have hTmem : ∀ n, ∀ᵐ x ∂uniformMeasure K, T n x ∈ Y := by
    intro n
    apply ae_of_ae_map (hT n).aemeasurable
    rw [hTpush n]
    exact (ae_map_iff (hQ n).aemeasurable hY.measurableSet).mpr (hQmem n)
  have hSmem : ∀ n, ∀ᵐ x ∂uniformMeasure K, S n x ∈ Y := by
    intro n
    apply ae_of_ae_map (hS n).aemeasurable
    rw [hSpush n]
    exact (ae_map_iff (hR n).aemeasurable hY.measurableSet).mpr (hRmem n)
  obtain ⟨B, hB⟩ := hY.isBounded.exists_norm_le
  have hLp : ∀ F : E d → E d, Measurable F →
      (∀ᵐ x ∂uniformMeasure K, F x ∈ Y) → MemLp F 2 (uniformMeasure K) := by
    intro F hF hFY
    exact MemLp.of_bound hF.aestronglyMeasurable B (hFY.mono fun x hx => hB _ hx)
  have herrlim : Tendsto (fun n => ε (φ (ψ n)) + η (φ (ψ n)))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using (hεlim.add hηlim).comp (hφ.comp hψ).tendsto_atTop
  refine ⟨Tμ, Tν, hTμ, hTν, ?_⟩
  apply StabilityLimit.one_third_bound_of_target_approximation
    (hLp Tμ hTμ.1.1 hTμmem) (hLp Tν hTν.1.1 hTνmem)
    (fun n => hLp (T (φ (ψ n))) (hT _) (hTmem _))
    (fun n => hLp (S (φ (ψ n))) (hS _) (hSmem _))
    (hTμlim.comp hψ.tendsto_atTop) hTνlim hC herrlim
    (μₙ := fun n => Measure.map (Q (φ (ψ n))) μ)
    (νₙ := fun n => Measure.map (R (φ (ψ n))) ν)
  · intro n
    simpa only [add_assoc] using wasserstein2_map_le_of_compact hY hY hμ hν
      (hQ (φ (ψ n))) (hR (φ (ψ n))) (hε _) (hη _) (hQerr _) (hRerr _)
  · exact fun n => hbound (φ (ψ n))

end Problem358

namespace Problem358

/-- Finite-target stability is the sole quantitative input needed for the full
compact-target conclusion. The finite hypothesis only asks for some pair of
optimal maps; uniqueness transfers its estimate to the constructed potentials. -/
theorem one_third_stability_of_finite_targets
    {d : ℕ} {K Y : Set (E d)}
    (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hY : IsCompact Y) (hYne : Y.Nonempty)
    {C : ℝ} (hC : 0 ≤ C)
    (hfinite : ∀ (μ ν : Measure (E d)),
      IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      (∃ F : Set (E d), F.Finite ∧ F ⊆ Y ∧ IsSupported μ F) →
      (∃ G : Set (E d), G.Finite ∧ G ⊆ Y ∧ IsSupported ν G) →
      ∃ Tμ Tν : E d → E d,
        IsUniqueQuadraticOptimalMap (uniformMeasure K) μ Tμ ∧
        IsUniqueQuadraticOptimalMap (uniformMeasure K) ν Tν ∧
        mapL2Dist (uniformMeasure K) Tμ Tν ≤
          C * Real.rpow (wasserstein2 μ ν) (1 / 3 : ℝ)) :
    ∀ (μ ν : Measure (E d)),
      IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      IsSupported μ Y → IsSupported ν Y →
      ∃ Tμ Tν : E d → E d,
        IsUniqueQuadraticOptimalMap (uniformMeasure K) μ Tμ ∧
        IsUniqueQuadraticOptimalMap (uniformMeasure K) ν Tν ∧
        mapL2Dist (uniformMeasure K) Tμ Tν ≤
          C * Real.rpow (wasserstein2 μ ν) (1 / 3 : ℝ) := by
  classical
  intro μ ν hμprob hνprob hμ hν
  let : IsProbabilityMeasure μ := hμprob
  let : IsProbabilityMeasure ν := hνprob
  let : IsProbabilityMeasure (uniformMeasure K) := UniformSource.probability hK hKint
  let x₀ : E d := hKint.choose
  have hx₀ : x₀ ∈ interior K := hKint.choose_spec
  have hx₀K : x₀ ∈ K := interior_subset hx₀
  obtain ⟨B, hBpos, hB⟩ := hY.isBounded.exists_pos_norm_le
  let L : ℝ≥0 := ⟨B, hBpos.le⟩
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose Q hQY hQerr using fun n => exists_compact_quantizer hY hYne (hεpos n)
  have hQrange : ∀ n, Set.range (Q n) ⊆ Y := by
    intro n y hy
    obtain ⟨x, rfl⟩ := hy
    exact hQY n x
  have hμn : ∀ n, IsProbabilityMeasure (Measure.map (Q n) μ) :=
    fun n => (Measure.isProbabilityMeasure_map_iff (Q n).measurable.aemeasurable).mpr
      inferInstance
  have hνn : ∀ n, IsProbabilityMeasure (Measure.map (Q n) ν) :=
    fun n => (Measure.isProbabilityMeasure_map_iff (Q n).measurable.aemeasurable).mpr
      inferInstance
  have hpotμ : ∀ n, ∃ (u : E d → ℝ) (T : E d → E d),
      IsUniqueQuadraticOptimalMap (uniformMeasure K) (Measure.map (Q n) μ) T ∧
      ConvexOn ℝ Set.univ u ∧ LipschitzWith L u ∧ u x₀ = 0 ∧
      (∀ x, T x ∈ Y) ∧ ∀ x z, u x + ⟪T x, z - x⟫ ≤ u z := by
    intro n
    let := hμn n
    exact exists_uniform_finite_map_and_potential K hK hKint
      (Measure.map (Q n) μ) (Q n).finite_range (hQrange n)
      (simpleFunc_map_finite_support μ (Q n)).2 L hB x₀
  have hpotν : ∀ n, ∃ (v : E d → ℝ) (S : E d → E d),
      IsUniqueQuadraticOptimalMap (uniformMeasure K) (Measure.map (Q n) ν) S ∧
      ConvexOn ℝ Set.univ v ∧ LipschitzWith L v ∧ v x₀ = 0 ∧
      (∀ x, S x ∈ Y) ∧ ∀ x z, v x + ⟪S x, z - x⟫ ≤ v z := by
    intro n
    let := hνn n
    exact exists_uniform_finite_map_and_potential K hK hKint
      (Measure.map (Q n) ν) (Q n).finite_range (hQrange n)
      (simpleFunc_map_finite_support ν (Q n)).2 L hB x₀
  choose u T hTu huconv huLip hunormal hTY hTs using hpotμ
  choose v S hSu hvconv hvLip hvnormal hSY hSs using hpotν
  have hbound : ∀ n, mapL2Dist (uniformMeasure K) (T n) (S n) ≤
      C * Real.rpow (wasserstein2 (Measure.map (Q n) μ) (Measure.map (Q n) ν))
        (1 / 3 : ℝ) := by
    intro n
    obtain ⟨T', S', hT', hS', hb⟩ := hfinite (Measure.map (Q n) μ)
      (Measure.map (Q n) ν) (hμn n) (hνn n)
      ⟨Set.range (Q n), (Q n).finite_range, hQrange n,
        (simpleFunc_map_finite_support μ (Q n)).2⟩
      ⟨Set.range (Q n), (Q n).finite_range, hQrange n,
        (simpleFunc_map_finite_support ν (Q n)).2⟩
    rw [mapL2Dist_eq_of_optimal_maps (hTu n) (hSu n) hT'.1 hS'.1]
    exact hb
  have hQμerr : ∀ n, ∀ᵐ y ∂μ, ‖Q n y - y‖ ≤ ε n := by
    intro n
    filter_upwards [show ∀ᵐ y ∂μ, y ∈ Y from ae_iff.mpr hμ] with y hy
    simpa only [dist_eq_norm] using (hQerr n y hy).le
  have hQνerr : ∀ n, ∀ᵐ y ∂ν, ‖Q n y - y‖ ≤ ε n := by
    intro n
    filter_upwards [show ∀ᵐ y ∂ν, y ∈ Y from ae_iff.mpr hν] with y hy
    simpa only [dist_eq_norm] using (hQerr n y hy).le
  exact exists_uniqueOptimal_pair_of_quantized_stability hK hKconv hY x₀ hx₀K hμ hν
    u v T S (fun n => Q n) (fun n => Q n) L
    (fun n => (huLip n).lipschitzOnWith) (fun n => (hvLip n).lipschitzOnWith)
    (fun n => (huconv n).subset (Set.subset_univ K) hKconv)
    (fun n => (hvconv n).subset (Set.subset_univ K) hKconv)
    hunormal hvnormal (fun n => (hTu n).1.1) (fun n => (hSu n).1.1)
    (fun n => (Q n).measurable) (fun n => (Q n).measurable)
    (fun n => ae_of_all _ (hQY n)) (fun n => ae_of_all _ (hQY n))
    (fun n => (hTu n).1.2.1) (fun n => (hSu n).1.2.1)
    (fun n => ae_of_all _ fun x z _ => hTs n x z)
    (fun n => ae_of_all _ fun x z _ => hSs n x z)
    (fun n => (hεpos n).le) (fun n => (hεpos n).le)
    hεlim hεlim hQμerr hQνerr hC hbound

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Atomic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem358

theorem atomicMatchingPlan_isProbability {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0∞) (y z : ι → E d) (hw : ∑ i, w i = 1) :
    IsProbabilityMeasure (atomicMatchingPlan w y z) := by
  constructor
  simpa [atomicMatchingPlan, Measure.finsetSum_apply, Measure.smul_apply] using hw

theorem atomicMatchingPlan_fst {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0∞) (y z : ι → E d) :
    Measure.map Prod.fst (atomicMatchingPlan w y z) =
      ∑ i, w i • Measure.dirac (y i) := by
  unfold atomicMatchingPlan
  rw [Measure.map_finset_sum measurable_fst.aemeasurable]
  simp only [Measure.map_smul, Measure.map_dirac]

theorem atomicMatchingPlan_snd {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0∞) (y z : ι → E d) :
    Measure.map Prod.snd (atomicMatchingPlan w y z) =
      ∑ i, w i • Measure.dirac (z i) := by
  unfold atomicMatchingPlan
  rw [Measure.map_finset_sum measurable_snd.aemeasurable]
  simp only [Measure.map_smul, Measure.map_dirac]

theorem quadraticPlanCost_atomicMatchingPlan {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0∞) (y z : ι → E d) :
    quadraticPlanCost (atomicMatchingPlan w y z) =
      ∑ i, w i * ENNReal.ofReal (‖y i - z i‖ ^ 2) := by
  simp [quadraticPlanCost, atomicMatchingPlan,
    lintegral_smul_measure, lintegral_dirac]

end Problem358

namespace Problem358

/-- A measure concentrated on an injectively indexed finite set is the sum of
its point masses. -/
theorem eq_sum_dirac_of_ae_mem_range {X ι : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [Fintype ι] (μ : Measure X) (y : ι → X)
    (hy : Function.Injective y) (hμ : ∀ᵐ x ∂μ, x ∈ Set.range y) :
    μ = ∑ i, μ {y i} • Measure.dirac (y i) := by
  classical
  have hm : ∀ᵐ x ∂μ, x ∈ Finset.univ.image y := by
    simpa only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using hμ
  have heq := Measure.ae_mem_finset_iff.mp hm
  rw [Finset.sum_image] at heq
  · exact heq
  · intro a _ b _ hab
    exact hy hab

/-- Every weighted finite atomic measure is concentrated on its listed atoms. -/
theorem ae_mem_range_sum_dirac {X ι : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [Fintype ι] (w : ι → ℝ≥0∞) (y : ι → X) :
    ∀ᵐ x ∂(∑ i, w i • Measure.dirac (y i)), x ∈ Set.range y := by
  rw [ae_finsetSum_measure_iff]
  intro i _
  exact Measure.ae_smul_measure (by simp) _

/-- All mass of a coupling of finite atomic measures is carried by pairs of
listed atoms. -/
theorem IsCoupling.ae_mem_atomic_pairs {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π) :
    ∀ᵐ p ∂π, p ∈ Set.range (fun q : ι × κ => (y q.1, z q.2)) := by
  have hfst : ∀ᵐ p ∂π, p.1 ∈ Set.range y := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [hπ.2.1]
    exact ae_mem_range_sum_dirac w y
  have hsnd : ∀ᵐ p ∂π, p.2 ∈ Set.range z := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    rw [hπ.2.2]
    exact ae_mem_range_sum_dirac v z
  filter_upwards [hfst, hsnd] with p hp hq
  obtain ⟨i, hi⟩ := hp
  obtain ⟨j, hj⟩ := hq
  exact ⟨(i,j), Prod.ext hi hj⟩

/-- A coupling of injectively indexed atomic measures has the usual finite
matrix representation. -/
theorem IsCoupling.atomic_decomposition {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) :
    π = ∑ q : ι × κ, π {(y q.1, z q.2)} • Measure.dirac (y q.1, z q.2) := by
  apply eq_sum_dirac_of_ae_mem_range
  · intro a b hab
    exact Prod.ext (hy (congrArg Prod.fst hab)) (hz (congrArg Prod.snd hab))
  · exact hπ.ae_mem_atomic_pairs

theorem IsCoupling.atomic_row_sum {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) (i : ι) :
    ∑ j, π {(y i, z j)} = w i := by
  classical
  have he := congrArg (fun μ : Measure (E d) => μ {y i}) hπ.2.1
  have hd : π = atomicMatchingPlan (fun q : ι × κ => π {(y q.1, z q.2)})
      (fun q => y q.1) (fun q => z q.2) := hπ.atomic_decomposition hy hz
  rw [hd, atomicMatchingPlan_fst] at he
  simpa [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply,
    Pi.single_apply, hy.eq_iff, Fintype.sum_prod_type] using he

theorem IsCoupling.atomic_col_sum {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) (j : κ) :
    ∑ i, π {(y i, z j)} = v j := by
  classical
  have he := congrArg (fun μ : Measure (E d) => μ {z j}) hπ.2.2
  have hd : π = atomicMatchingPlan (fun q : ι × κ => π {(y q.1, z q.2)})
      (fun q => y q.1) (fun q => z q.2) := hπ.atomic_decomposition hy hz
  rw [hd, atomicMatchingPlan_snd] at he
  simpa [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply,
    Pi.single_apply, hz.eq_iff, Fintype.sum_prod_type] using he

theorem IsCoupling.atomic_cost {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) :
    quadraticPlanCost π =
      ∑ q : ι × κ, π {(y q.1, z q.2)} * ENNReal.ofReal (‖y q.1 - z q.2‖ ^ 2) := by
  have hd : π = atomicMatchingPlan (fun q : ι × κ => π {(y q.1, z q.2)})
      (fun q => y q.1) (fun q => z q.2) := hπ.atomic_decomposition hy hz
  conv_lhs => rw [hd, quadraticPlanCost_atomicMatchingPlan]

theorem atomicMatchingPlan_isCoupling_of_marginal_sums
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ≥0∞) (v : κ → ℝ≥0∞) (p : ι × κ → ℝ≥0∞)
    (y : ι → E d) (z : κ → E d) (hw : ∑ i, w i = 1)
    (hrow : ∀ i, ∑ j, p (i,j) = w i) (hcol : ∀ j, ∑ i, p (i,j) = v j) :
    IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j))
      (atomicMatchingPlan p (fun q => y q.1) (fun q => z q.2)) := by
  have hp : ∑ q, p q = 1 := by
    rw [Fintype.sum_prod_type]
    simpa only [hrow] using hw
  refine ⟨atomicMatchingPlan_isProbability _ _ _ hp, ?_, ?_⟩
  · rw [atomicMatchingPlan_fst, Fintype.sum_prod_type]
    simp_rw [← Finset.sum_smul, hrow]
  · rw [atomicMatchingPlan_snd, Fintype.sum_prod_type_right]
    simp_rw [← Finset.sum_smul, hcol]

theorem IsCoupling.atomic_row_sum_toReal {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) (i : ι) :
    ∑ j, (π {(y i, z j)}).toReal = (w i).toReal := by
  let : IsProbabilityMeasure π := hπ.1
  rw [← ENNReal.toReal_sum (fun j _ => measure_ne_top π _)]
  exact congrArg ENNReal.toReal (hπ.atomic_row_sum hy hz i)

theorem IsCoupling.atomic_col_sum_toReal {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) (j : κ) :
    ∑ i, (π {(y i, z j)}).toReal = (v j).toReal := by
  let : IsProbabilityMeasure π := hπ.1
  rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top π _)]
  exact congrArg ENNReal.toReal (hπ.atomic_col_sum hy hz j)

theorem IsCoupling.atomic_cost_ne_top {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) :
    quadraticPlanCost π ≠ ∞ := by
  let : IsProbabilityMeasure π := hπ.1
  rw [hπ.atomic_cost hy hz]
  exact ENNReal.sum_ne_top.mpr fun q _ =>
    ENNReal.mul_ne_top (measure_ne_top π _) ENNReal.ofReal_ne_top

theorem IsCoupling.atomic_cost_toReal {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) :
    (quadraticPlanCost π).toReal =
      ∑ q : ι × κ, (π {(y q.1, z q.2)}).toReal * ‖y q.1 - z q.2‖ ^ 2 := by
  let : IsProbabilityMeasure π := hπ.1
  rw [hπ.atomic_cost hy hz, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
  · intro q _
    exact ENNReal.mul_ne_top (measure_ne_top π _) ENNReal.ofReal_ne_top

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_FiniteCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
open Set

namespace Problem358

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The transportation polytope of two finite real-valued probability vectors is compact. -/
theorem isCompact_finite_coupling_set
    (a : I → ℝ) (b : J → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hasum : ∑ i, a i = 1) :
    IsCompact {p : I → J → ℝ |
      (∀ i j, 0 ≤ p i j) ∧
      (∀ i, ∑ j, p i j = a i) ∧
      (∀ j, ∑ i, p i j = b j)} := by
  classical
  have hnonneg : IsClosed {p : I → J → ℝ | ∀ i j, 0 ≤ p i j} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le continuous_const ((continuous_apply j).comp (continuous_apply i))
  have hrows : IsClosed {p : I → J → ℝ | ∀ i, ∑ j, p i j = a i} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const
  have hcols : IsClosed {p : I → J → ℝ | ∀ j, ∑ i, p i j = b j} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun j => isClosed_eq (by fun_prop) continuous_const
  have hclosed : IsClosed {p : I → J → ℝ |
      (∀ i j, 0 ≤ p i j) ∧
      (∀ i, ∑ j, p i j = a i) ∧
      (∀ j, ∑ i, p i j = b j)} := hnonneg.inter (hrows.inter hcols)
  apply (isCompact_Icc : IsCompact (Icc (0 : I → J → ℝ) 1)).of_isClosed_subset hclosed
  intro p hp
  refine ⟨hp.1, ?_⟩
  intro i j
  have hpij : p i j ≤ ∑ k, p i k :=
    Finset.single_le_sum (fun k _ => hp.1 i k) (Finset.mem_univ j)
  have hai : a i ≤ ∑ k, a k :=
    Finset.single_le_sum (fun k _ => ha k) (Finset.mem_univ i)
  rw [hp.2.1 i] at hpij
  rw [hasum] at hai
  exact hpij.trans hai

/-- Every finite transportation problem with probability margins has a cost minimizer.
No nonnegativity or metric assumptions on the finite cost matrix are needed. -/
theorem exists_minimal_finite_coupling
    (a : I → ℝ) (b : J → ℝ) (c : I → J → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hasum : ∑ i, a i = 1) (hbsum : ∑ j, b j = 1) :
    ∃ p : I → J → ℝ,
      (∀ i j, 0 ≤ p i j) ∧
      (∀ i, ∑ j, p i j = a i) ∧
      (∀ j, ∑ i, p i j = b j) ∧
      ∀ q : I → J → ℝ,
        (∀ i j, 0 ≤ q i j) →
        (∀ i, ∑ j, q i j = a i) →
        (∀ j, ∑ i, q i j = b j) →
        (∑ i, ∑ j, p i j * c i j) ≤ ∑ i, ∑ j, q i j * c i j := by
  classical
  let S := {p : I → J → ℝ |
      (∀ i j, 0 ≤ p i j) ∧
      (∀ i, ∑ j, p i j = a i) ∧
      (∀ j, ∑ i, p i j = b j)}
  have hS : IsCompact S := isCompact_finite_coupling_set a b ha hasum
  have hne : S.Nonempty := by
    refine ⟨fun i j => a i * b j, ?_, ?_, ?_⟩
    · exact fun i j => mul_nonneg (ha i) (hb j)
    · intro i
      rw [← Finset.mul_sum, hbsum, mul_one]
    · intro j
      rw [← Finset.sum_mul, hasum, one_mul]
  let cost : (I → J → ℝ) → ℝ := fun p => ∑ i, ∑ j, p i j * c i j
  have hcost : Continuous cost := by fun_prop
  obtain ⟨p, hp, hmin⟩ := hS.exists_isMinOn hne hcost.continuousOn
  refine ⟨p, hp.1, hp.2.1, hp.2.2, ?_⟩
  intro q hq hqr hqc
  exact hmin ⟨hq, hqr, hqc⟩

end Problem358

end

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Problem358
namespace FiniteCoupling

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] in
lemma rectangleSwap_row (w : ι → κ → ℝ) (ε : ℝ) (i k : ι) (j l : κ) (u : ι) :
    ∑ v, rectangleSwap w ε i k j l u v = ∑ v, w u v := by
  simp [rectangleSwap, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]

omit [Fintype κ] in
lemma rectangleSwap_col (w : ι → κ → ℝ) (ε : ℝ) (i k : ι) (j l : κ) (v : κ) :
    ∑ u, rectangleSwap w ε i k j l u v = ∑ u, w u v := by
  simp [rectangleSwap, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_sub_distrib]

omit [Fintype ι] [Fintype κ] in
lemma rectangleSwap_nonneg {w : ι → κ → ℝ} {ε : ℝ} {i k : ι} {j l : κ}
    (hw : ∀ u v, 0 ≤ w u v) (hε : 0 ≤ ε) (hij : ε ≤ w i j) (hkl : ε ≤ w k l)
    (hik : i ≠ k) (hjl : j ≠ l) : ∀ u v, 0 ≤ rectangleSwap w ε i k j l u v := by
  intro u v
  have huv := hw u v
  by_cases hui : u = i <;> by_cases huk : u = k <;>
    by_cases hvj : v = j <;> by_cases hvl : v = l <;>
    simp_all [rectangleSwap] <;> linarith [hw i l, hw k j]

lemma rectangleSwap_cost (c w : ι → κ → ℝ) (ε : ℝ) (i k : ι) (j l : κ) :
    cost c (rectangleSwap w ε i k j l) =
      cost c w + ε * (c i l + c k j - c i j - c k l) := by
  simp [cost, rectangleSwap, add_mul, sub_mul, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- The two-point exchange inequality on the positive support of an optimal matrix. -/
lemma IsOptimal.cross_cost_le {c w : ι → κ → ℝ} (hopt : IsOptimal c w)
    {i k : ι} {j l : κ} (hij : 0 < w i j) (hkl : 0 < w k l) :
    c i j + c k l ≤ c i l + c k j := by
  by_cases hik : i = k
  · subst k
    linarith
  by_cases hjl : j = l
  · subst l
    linarith
  let ε : ℝ := min (w i j) (w k l)
  have hε : 0 < ε := lt_min hij hkl
  have hswap := hopt.2 (rectangleSwap w ε i k j l)
    (rectangleSwap_nonneg hopt.1 hε.le (min_le_left _ _) (min_le_right _ _) hik hjl)
    (rectangleSwap_row w ε i k j l) (rectangleSwap_col w ε i k j l)
  rw [rectangleSwap_cost] at hswap
  nlinarith

end FiniteCoupling

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The quadratic exchange inequality is exactly two-point monotonicity. -/
lemma inner_sub_nonneg_of_quadratic_cross {x x' y y' : F}
    (h : ‖x - y‖ ^ 2 + ‖x' - y'‖ ^ 2 ≤
      ‖x - y'‖ ^ 2 + ‖x' - y‖ ^ 2) :
    0 ≤ ⟪x - x', y - y'⟫ := by
  simp only [norm_sub_sq_real] at h
  simp only [inner_sub_left, inner_sub_right]
  linarith

/-- Positive entries of a finite quadratic optimal coupling are monotone. -/
lemma FiniteCoupling.IsOptimal.inner_nonneg
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {x : ι → F} {y : κ → F} {w : ι → κ → ℝ}
    (hopt : FiniteCoupling.IsOptimal (fun i j => ‖x i - y j‖ ^ 2) w)
    {i k : ι} {j l : κ} (hij : 0 < w i j) (hkl : 0 < w k l) :
    0 ≤ ⟪x i - x k, y j - y l⟫ :=
  inner_sub_nonneg_of_quadratic_cross (hopt.cross_cost_le hij hkl)

/-- A positive linear combination of two vectors with nonnegative inner product
can vanish only when both vectors vanish. -/
lemma eq_zero_of_pos_smul_add_smul_eq_zero {x y : F} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hxy : 0 ≤ ⟪x, y⟫)
    (h : a • x + b • y = 0) : x = 0 ∧ y = 0 := by
  have hx := congrArg (fun z : F => ⟪z, x⟫) h
  have hy := congrArg (fun z : F => ⟪z, y⟫) h
  simp only [inner_add_left, real_inner_smul_left, inner_zero_left] at hx hy
  rw [real_inner_comm x y] at hx
  have hxx := real_inner_self_nonneg (x := x)
  have hyy := real_inner_self_nonneg (x := y)
  constructor
  · apply real_inner_self_nonpos.mp
    nlinarith [mul_nonneg hb.le hxy]
  · apply real_inner_self_nonpos.mp
    nlinarith [mul_nonneg ha.le hxy]

/-- Distinct endpoint pairs on a monotone relation cannot collide at interior time. -/
lemma interpolate_ne_of_inner_nonneg {x x' y y' : F} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1)
    (hxy : 0 ≤ ⟪x - x', y - y'⟫) (hne : (x, y) ≠ (x', y')) :
    (1 - t) • x + t • y ≠ (1 - t) • x' + t • y' := by
  intro heq
  have hzero : (1 - t) • (x - x') + t • (y - y') = 0 := by
    calc
      (1 - t) • (x - x') + t • (y - y') =
          ((1 - t) • x + t • y) - ((1 - t) • x' + t • y') := by
        simp only [smul_sub]
        abel
      _ = 0 := sub_eq_zero.mpr heq
  obtain ⟨hx, hy⟩ := eq_zero_of_pos_smul_add_smul_eq_zero
    (sub_pos.mpr ht1) ht0 hxy hzero
  exact hne (Prod.ext (sub_eq_zero.mp hx) (sub_eq_zero.mp hy))

end Problem358

end

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Problem358
namespace PositiveFiniteCoupling

variable {ι : Type*} [Fintype ι]

/-- Removing zero weights preserves every weighted real sum. -/
theorem sum_support_mul (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i : Support w, w i * f i) = ∑ i, w i * f i := by
  classical
  have hzero : (∑ i : {i : ι // ¬ 0 < w i}, w i * f i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : w i = 0 := le_antisymm (le_of_not_gt i.property) (hw i)
    simp [hi]
  have h := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < w i)
    (fun i => w i * f i)
  simpa only [hzero, add_zero] using h

theorem sum_support (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i : Support w, w i) = ∑ i, w i := by
  simpa using sum_support_mul w (fun _ => 1) hw

variable {κ : Type*} [Fintype κ]

theorem sum_pairs_mul (w c : ι → κ → ℝ) (hw : ∀ i j, 0 ≤ w i j) :
    (∑ p : Pairs w, w p.1.1 p.1.2 * c p.1.1 p.1.2) =
      ∑ i, ∑ j, w i j * c i j := by
  rw [sum_support_mul (fun p : ι × κ => w p.1 p.2)
    (fun p : ι × κ => c p.1 p.2) (fun p => hw p.1 p.2), Fintype.sum_prod_type]

theorem sum_pairs_eq_one (w : ι → κ → ℝ) (a : ι → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j = a i)
    (ha : ∑ i, a i = 1) :
    (∑ p : Pairs w, w p.1.1 p.1.2) = 1 := by
  rw [sum_support (fun p : ι × κ => w p.1 p.2)
    (fun p => hw p.1 p.2), Fintype.sum_prod_type]
  simpa only [hrow] using ha

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

omit [Fintype ι] [Fintype κ] [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
/-- Injective endpoint site families give distinct positive coupling pairs. -/
theorem endpoint_pairs_injective {x : ι → F} {y : κ → F}
    (hx : Function.Injective x) (hy : Function.Injective y) (w : ι → κ → ℝ) :
    Function.Injective (fun p : Pairs w => (x p.1.1, y p.1.2)) := by
  intro p q hpq
  apply Subtype.ext
  exact Prod.ext (hx (congrArg Prod.fst hpq)) (hy (congrArg Prod.snd hpq))

/-- The positive pairs of an optimal quadratic matrix remain distinct at interior times. -/
theorem interpolated_sites_injective [DecidableEq ι] [DecidableEq κ]
    {x : ι → F} {y : κ → F} {w : ι → κ → ℝ}
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hopt : FiniteCoupling.IsOptimal (fun i j => ‖x i - y j‖ ^ 2) w)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Function.Injective
      (fun p : Pairs w => (1-t) • x p.1.1 + t • y p.1.2) := by
  intro p q hpq
  by_contra hne
  apply interpolate_ne_of_inner_nonneg ht0 ht1
    (hopt.inner_nonneg p.property q.property) _ hpq
  exact fun heq => hne (endpoint_pairs_injective hx hy w heq)

/-- A finite quadratic optimal coupling, with zero entries removed, has positive
normalized weights and pairwise distinct interpolated sites for every interior time. -/
theorem exists_optimal_positive_pairs [DecidableEq ι] [DecidableEq κ]
    (a : ι → ℝ) (b : κ → ℝ) (x : ι → F) (y : κ → F)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hasum : ∑ i, a i = 1) (hbsum : ∑ j, b j = 1)
    (hx : Function.Injective x) (hy : Function.Injective y) :
    ∃ w : ι → κ → ℝ,
      (∀ i, ∑ j, w i j = a i) ∧
      (∀ j, ∑ i, w i j = b j) ∧
      FiniteCoupling.IsOptimal (fun i j => ‖x i - y j‖ ^ 2) w ∧
      (∑ p : Pairs w, w p.1.1 p.1.2) = 1 ∧
      ∀ t : ℝ, 0 < t → t < 1 → Function.Injective
        (fun p : Pairs w => (1-t) • x p.1.1 + t • y p.1.2) := by
  obtain ⟨w, hw, hrow, hcol, hmin⟩ :=
    exists_minimal_finite_coupling a b (fun i j => ‖x i - y j‖ ^ 2)
      ha hb hasum hbsum
  have hopt : FiniteCoupling.IsOptimal (fun i j => ‖x i - y j‖ ^ 2) w := by
    refine ⟨hw, ?_⟩
    intro q hq hqr hqc
    exact hmin q hq (fun i => (hqr i).trans (hrow i))
      (fun j => (hqc j).trans (hcol j))
  exact ⟨w, hrow, hcol, hopt, sum_pairs_eq_one w a hw hrow hasum,
    fun _ ht0 ht1 => interpolated_sites_injective hx hy hopt ht0 ht1⟩

end PositiveFiniteCoupling
end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_AtomicTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem358

/-- Real-valued finite matrix weights have the expected real quadratic cost. -/
theorem quadraticPlanCost_atomicMatchingPlan_ofReal_toReal
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → κ → ℝ) (hp : ∀ i j, 0 ≤ p i j) (y : ι → E d) (z : κ → E d) :
    (quadraticPlanCost (atomicMatchingPlan
      (fun q : ι × κ => ENNReal.ofReal (p q.1 q.2))
      (fun q => y q.1) (fun q => z q.2))).toReal =
      ∑ i, ∑ j, p i j * ‖y i - z j‖ ^ 2 := by
  rw [quadraticPlanCost_atomicMatchingPlan, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
      ENNReal.toReal_ofReal (hp _ _), Fintype.sum_prod_type]
  · intro q _
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- Criterion turning any real matrix minimizer into a minimum among arbitrary
couplings, without changing the chosen matrix. -/
theorem atomicMatchingPlan_minimal_of_matrix_minimal
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ≥0∞) (v : κ → ℝ≥0∞) (y : ι → E d) (z : κ → E d)
    (hy : Function.Injective y) (hz : Function.Injective z)
    (p : ι → κ → ℝ) (hp : ∀ i j, 0 ≤ p i j)
    (hcoupling : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j))
      (atomicMatchingPlan (fun q : ι × κ => ENNReal.ofReal (p q.1 q.2))
        (fun q => y q.1) (fun q => z q.2)))
    (hmin : ∀ q : ι → κ → ℝ, (∀ i j, 0 ≤ q i j) →
      (∀ i, ∑ j, q i j = (w i).toReal) →
      (∀ j, ∑ i, q i j = (v j).toReal) →
      (∑ i, ∑ j, p i j * ‖y i - z j‖ ^ 2) ≤ ∑ i, ∑ j, q i j * ‖y i - z j‖ ^ 2) :
    ∀ π, IsCoupling (∑ i, w i • Measure.dirac (y i))
        (∑ j, v j • Measure.dirac (z j)) π →
      quadraticPlanCost (atomicMatchingPlan
        (fun q : ι × κ => ENNReal.ofReal (p q.1 q.2))
        (fun q => y q.1) (fun q => z q.2)) ≤ quadraticPlanCost π := by
  intro π hπ
  apply (ENNReal.toReal_le_toReal (hcoupling.atomic_cost_ne_top hy hz)
    (hπ.atomic_cost_ne_top hy hz)).mp
  rw [quadraticPlanCost_atomicMatchingPlan_ofReal_toReal p hp,
    hπ.atomic_cost_toReal hy hz, Fintype.sum_prod_type]
  exact hmin (fun i j => (π {(y i, z j)}).toReal)
    (fun _ _ => ENNReal.toReal_nonneg)
    (hπ.atomic_row_sum_toReal hy hz) (hπ.atomic_col_sum_toReal hy hz)

/-- Any actual minimum realizes the infimum in the challenge's Wasserstein definition. -/
theorem wasserstein2_sq_eq_planCost_of_minimal {d : ℕ}
    {μ ν : Measure (E d)} {π : Measure (E d × E d)}
    (hπ : IsCoupling μ ν π)
    (hmin : ∀ σ, IsCoupling μ ν σ → quadraticPlanCost π ≤ quadraticPlanCost σ) :
    wasserstein2 μ ν ^ 2 = (quadraticPlanCost π).toReal := by
  have hInf : sInf {r : ℝ≥0∞ | ∃ σ : Measure (E d × E d),
      IsCoupling μ ν σ ∧ quadraticPlanCost σ = r} = quadraticPlanCost π := by
    apply le_antisymm
    · exact sInf_le ⟨π, hπ, rfl⟩
    · apply le_sInf
      rintro r ⟨σ, hσ, rfl⟩
      exact hmin σ hσ
  simp only [wasserstein2, hInf, Real.sq_sqrt ENNReal.toReal_nonneg]

end Problem358

namespace Problem358

/-- Removing the zero weights also preserves finite sums of weighted measures. -/
theorem sum_ofReal_smul_positive_support {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (w : ι → ℝ) (μ : ι → Measure X) (hw : ∀ i, 0 ≤ w i) :
    (∑ i : PositiveFiniteCoupling.Support w, ENNReal.ofReal (w i) • μ i) =
      ∑ i, ENNReal.ofReal (w i) • μ i := by
  classical
  have hzero : (∑ i : {i : ι // ¬ 0 < w i}, ENNReal.ofReal (w i) • μ i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : w i = 0 := le_antisymm (le_of_not_gt i.property) (hw i)
    simp [hi]
  have h := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < w i)
    (fun i => ENNReal.ofReal (w i) • μ i)
  simpa only [hzero, add_zero] using h

/-- A nonnegative real matrix with probability margins induces a coupling of
those atomic probability laws. -/
theorem real_atomic_matrix_isCoupling
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (m : ι → ℝ) (n : κ → ℝ) (y : ι → E d) (z : κ → E d)
    (hm : ∀ i, 0 ≤ m i) (hm1 : ∑ i, m i = 1)
    (p : ι → κ → ℝ) (hp : ∀ i j, 0 ≤ p i j)
    (hrow : ∀ i, ∑ j, p i j = m i) (hcol : ∀ j, ∑ i, p i j = n j) :
    IsCoupling (∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i))
      (∑ j, ENNReal.ofReal (n j) • Measure.dirac (z j))
      (atomicMatchingPlan (fun q : ι × κ => ENNReal.ofReal (p q.1 q.2))
        (fun q => y q.1) (fun q => z q.2)) := by
  apply atomicMatchingPlan_isCoupling_of_marginal_sums
  · rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hm i), hm1]
    exact ENNReal.ofReal_one
  · intro i
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hp i j), hrow i]
  · intro j
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i j), hcol j]

/-- The cost of any chosen optimal real matrix is exactly the squared Wasserstein
quantity of its two atomic laws. -/
theorem FiniteCoupling.IsOptimal.wasserstein_cost
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {m : ι → ℝ} {n : κ → ℝ} {y : ι → E d} {z : κ → E d}
    (hm : ∀ i, 0 ≤ m i) (hn : ∀ j, 0 ≤ n j) (hm1 : ∑ i, m i = 1)
    (hy : Function.Injective y) (hz : Function.Injective z)
    {p : ι → κ → ℝ} (hopt : FiniteCoupling.IsOptimal (fun i j => ‖y i - z j‖ ^ 2) p)
    (hrow : ∀ i, ∑ j, p i j = m i) (hcol : ∀ j, ∑ i, p i j = n j) :
    (∑ i, ∑ j, p i j * ‖y i - z j‖ ^ 2) =
      wasserstein2 (∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i))
        (∑ j, ENNReal.ofReal (n j) • Measure.dirac (z j)) ^ 2 := by
  have hc := real_atomic_matrix_isCoupling m n y z hm hm1 p hopt.1 hrow hcol
  have hmin := atomicMatchingPlan_minimal_of_matrix_minimal
    (fun i => ENNReal.ofReal (m i)) (fun j => ENNReal.ofReal (n j))
    y z hy hz p hopt.1 hc (by
      intro q hq hqr hqc
      apply hopt.2 q hq
      · intro i
        rw [hrow i]
        simpa only [ENNReal.toReal_ofReal (hm i)] using hqr i
      · intro j
        rw [hcol j]
        simpa only [ENNReal.toReal_ofReal (hn j)] using hqc j)
  rw [wasserstein2_sq_eq_planCost_of_minimal hc hmin]
  exact (quadraticPlanCost_atomicMatchingPlan_ofReal_toReal p hopt.1 y z).symm

/-- The positive-pair family has the same explicit joint law as the whole matrix. -/
theorem positive_atomic_plan_eq_full
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → κ → ℝ) (hp : ∀ i j, 0 ≤ p i j) (y : ι → E d) (z : κ → E d) :
    atomicMatchingPlan
      (fun q : PositiveFiniteCoupling.Pairs p => ENNReal.ofReal (p q.1.1 q.1.2))
      (fun q => y q.1.1) (fun q => z q.1.2) =
    atomicMatchingPlan (fun q : ι × κ => ENNReal.ofReal (p q.1 q.2))
      (fun q => y q.1) (fun q => z q.2) := by
  exact sum_ofReal_smul_positive_support (fun q : ι × κ => p q.1 q.2)
    (fun q => Measure.dirac (y q.1, z q.2)) (fun q => hp q.1 q.2)

/-- Endpoint atomic laws survive removal of the zero matrix entries. -/
theorem positive_atomic_marginal_laws
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (m : ι → ℝ) (n : κ → ℝ) (y : ι → E d) (z : κ → E d)
    (hm : ∀ i, 0 ≤ m i) (hm1 : ∑ i, m i = 1)
    (p : ι → κ → ℝ) (hp : ∀ i j, 0 ≤ p i j)
    (hrow : ∀ i, ∑ j, p i j = m i) (hcol : ∀ j, ∑ i, p i j = n j) :
    (∑ q : PositiveFiniteCoupling.Pairs p,
      ENNReal.ofReal (p q.1.1 q.1.2) • Measure.dirac (y q.1.1)) =
        ∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i) ∧
    (∑ q : PositiveFiniteCoupling.Pairs p,
      ENNReal.ofReal (p q.1.1 q.1.2) • Measure.dirac (z q.1.2)) =
        ∑ j, ENNReal.ofReal (n j) • Measure.dirac (z j) := by
  have hc := real_atomic_matrix_isCoupling m n y z hm hm1 p hp hrow hcol
  rw [← positive_atomic_plan_eq_full p hp y z] at hc
  exact ⟨(atomicMatchingPlan_fst _ _ _).symm.trans hc.2.1,
    (atomicMatchingPlan_snd _ _ _).symm.trans hc.2.2⟩

/-- Fully semantic positive-pair input for the moving-site stability argument:
positive normalized weights, the original endpoint laws, exact W₂ speed, and
no site collisions at interior interpolation times. -/
theorem exists_positive_atomic_coupling_data
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (m : ι → ℝ) (n : κ → ℝ) (y : ι → E d) (z : κ → E d)
    (hm : ∀ i, 0 ≤ m i) (hn : ∀ j, 0 ≤ n j)
    (hm1 : ∑ i, m i = 1) (hn1 : ∑ j, n j = 1)
    (hy : Function.Injective y) (hz : Function.Injective z) :
    ∃ p : ι → κ → ℝ,
      (∀ q : PositiveFiniteCoupling.Pairs p, 0 < p q.1.1 q.1.2) ∧
      (∑ q : PositiveFiniteCoupling.Pairs p, p q.1.1 q.1.2) = 1 ∧
      (∑ q : PositiveFiniteCoupling.Pairs p,
        ENNReal.ofReal (p q.1.1 q.1.2) • Measure.dirac (y q.1.1)) =
          (∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i)) ∧
      (∑ q : PositiveFiniteCoupling.Pairs p,
        ENNReal.ofReal (p q.1.1 q.1.2) • Measure.dirac (z q.1.2)) =
          (∑ j, ENNReal.ofReal (n j) • Measure.dirac (z j)) ∧
      Function.Injective (fun q : PositiveFiniteCoupling.Pairs p => (y q.1.1, z q.1.2)) ∧
      (∑ q : PositiveFiniteCoupling.Pairs p,
        p q.1.1 q.1.2 * ‖y q.1.1 - z q.1.2‖ ^ 2) =
          wasserstein2 (∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i))
            (∑ j, ENNReal.ofReal (n j) • Measure.dirac (z j)) ^ 2 ∧
      ∀ t : ℝ, 0 < t → t < 1 → Function.Injective
        (fun q : PositiveFiniteCoupling.Pairs p => (1-t) • y q.1.1 + t • z q.1.2) := by
  classical
  obtain ⟨p, hrow, hcol, hopt, hsum, hinj⟩ :=
    PositiveFiniteCoupling.exists_optimal_positive_pairs m n y z hm hn hm1 hn1 hy hz
  have hlaws := positive_atomic_marginal_laws m n y z hm hm1 p hopt.1 hrow hcol
  refine ⟨p, fun q => q.property, hsum, hlaws.1, hlaws.2,
    PositiveFiniteCoupling.endpoint_pairs_injective hy hz p, ?_, hinj⟩
  rw [PositiveFiniteCoupling.sum_pairs_mul p (fun i j => ‖y i - z j‖ ^ 2) hopt.1]
  exact hopt.wasserstein_cost hm hn hm1 hy hz hrow hcol

end Problem358

namespace Problem358

/-- Two finitely supported probabilities admit a common strictly positive finite
weight family. Its paired sites give the original laws, exact Wasserstein energy,
and an injective moving family at every interior interpolation time. -/
theorem exists_finite_atomic_motion
    {d : ℕ} {μ ν : Measure (E d)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F G : Set (E d)} (hF : F.Finite) (hG : G.Finite)
    (hμ : IsSupported μ F) (hν : IsSupported ν G) :
    ∃ N : ℕ, 0 < N ∧ ∃ (w : Fin N → ℝ) (y z : Fin N → E d),
      (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
      (∀ i, y i ∈ F) ∧ (∀ i, z i ∈ G) ∧
      μ = (∑ i, ENNReal.ofReal (w i) • Measure.dirac (y i)) ∧
      ν = (∑ i, ENNReal.ofReal (w i) • Measure.dirac (z i)) ∧
      Function.Injective (fun i => (y i, z i)) ∧
      (∑ i, w i * ‖y i - z i‖ ^ 2) = wasserstein2 μ ν ^ 2 ∧
      ∀ t : ℝ, 0 < t → t < 1 →
        Function.Injective (fun i => (1-t) • y i + t • z i) := by
  classical
  obtain ⟨m, _, y, a, hy, hyF, ha, ha1, hμeq⟩ :=
    exists_positive_finite_atomic_presentation hF hμ
  obtain ⟨n, _, z, b, hz, hzG, hb, hb1, hνeq⟩ :=
    exists_positive_finite_atomic_presentation hG hν
  obtain ⟨p, hp, hp1, hpμ, hpν, hpair, hcost, hinj⟩ :=
    exists_positive_atomic_coupling_data a b y z (fun i => (ha i).le)
      (fun i => (hb i).le) ha1 hb1 hy hz
  let P := PositiveFiniteCoupling.Pairs p
  let e : Fin (Fintype.card P) ≃ P := (Fintype.equivFin P).symm
  have hN : 0 < Fintype.card P := by
    by_contra h
    have hzcard : Fintype.card P = 0 := by omega
    have : IsEmpty P := Fintype.card_eq_zero_iff.mp hzcard
    have hzero : (∑ q : P, p q.1.1 q.1.2) = 0 := by simp
    have : (0 : ℝ) = 1 := hzero.symm.trans hp1
    norm_num at this
  refine ⟨Fintype.card P, hN, (fun i => p (e i).1.1 (e i).1.2),
    (fun i => y (e i).1.1), (fun i => z (e i).1.2),
    (fun i => hp (e i)), ?_, (fun i => hyF _), (fun i => hzG _), ?_, ?_,
    hpair.comp e.injective, ?_, ?_⟩
  · exact (e.sum_comp (fun q : P => p q.1.1 q.1.2)).trans hp1
  · exact hμeq.trans (hpμ.symm.trans
      (e.sum_comp (fun q : P => ENNReal.ofReal (p q.1.1 q.1.2) •
        Measure.dirac (y q.1.1))).symm)
  · exact hνeq.trans (hpν.symm.trans
      (e.sum_comp (fun q : P => ENNReal.ofReal (p q.1.1 q.1.2) •
        Measure.dirac (z q.1.2))).symm)
  · calc
      _ = ∑ q : P, p q.1.1 q.1.2 * ‖y q.1.1 - z q.1.2‖ ^ 2 := e.sum_comp _
      _ = wasserstein2 μ ν ^ 2 := by simpa only [← hμeq, ← hνeq] using hcost
  · intro t ht0 ht1
    exact (hinj t ht0 ht1).comp e.injective

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_BoundaryStrip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise

namespace Problem358

section Geometry
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Contracting toward a point gives a translated core in a convex set. -/
theorem convex_contraction_add_mem {K : Set V} (hK : Convex ℝ K)
    {p e x : V} (hx : x ∈ K) (hpe : p + e ∈ K)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) • x + t • p + t • e ∈ K := by
  have h := hK hx hpe (sub_nonneg.mpr ht1) ht0 (by ring)
  simpa only [smul_add, add_assoc] using h

/-- The contracted image is in the forward translation core. -/
theorem convex_contraction_subset_shift_core {K : Set V} (hK : Convex ℝ K)
    {p e : V} (hp : p ∈ K) (hpe : p + e ∈ K)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (fun x => (1 - t) • x + t • p) '' K ⊆
      {x | x ∈ K ∧ x + t • e ∈ K} := by
  rintro x ⟨z, hz, rfl⟩
  exact ⟨hK hz hp (sub_nonneg.mpr ht1) ht0 (by ring),
    convex_contraction_add_mem hK hz hpe ht0 ht1⟩
end Geometry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  (μ : Measure V) [IsAddHaarMeasure μ]

/-- The Haar measure of an affine contraction, in real-valued form. -/
theorem measureReal_contraction_image (K : Set V) (p : V) {t : ℝ}
    (ht1 : t ≤ 1) :
    μ.real ((fun x => (1 - t) • x + t • p) '' K) =
      (1 - t) ^ Module.finrank ℝ V * μ.real K := by
  have hset : (fun x => (1 - t) • x + t • p) '' K =
      (fun x => x + t • p) '' ((1 - t) • K) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(1 - t) • z, ⟨z, hz, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w, hw, rfl⟩
  rw [hset, Set.image_add_right, measureReal_def, measure_preimage_add_right,
    addHaar_smul_of_nonneg μ (sub_nonneg.mpr ht1), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg (sub_nonneg.mpr ht1) _)]
  rfl

/-- A geometric boundary strip is controlled by the volume lost under contraction. -/
theorem measureReal_convex_shift_strip_le {K : Set V} (hKc : IsCompact K)
    (hK : Convex ℝ K) {p e : V} (hp : p ∈ K) (hpe : p + e ∈ K)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    μ.real {x | x ∈ K ∧ x + t • e ∉ K} ≤
      (1 - (1 - t) ^ Module.finrank ℝ V) * μ.real K := by
  let H := (fun x => (1 - t) • x + t • p) '' K
  have hHc : IsCompact H := hKc.image (by fun_prop)
  have hH : H ⊆ {x | x ∈ K ∧ x + t • e ∈ K} :=
    convex_contraction_subset_shift_core hK hp hpe ht0 ht1
  have hHK : H ⊆ K := fun x hx => (hH hx).1
  have hsub : {x | x ∈ K ∧ x + t • e ∉ K} ⊆ K \ H := by
    intro x hx
    exact ⟨hx.1, fun h => hx.2 (hH h).2⟩
  calc
    μ.real {x | x ∈ K ∧ x + t • e ∉ K} ≤ μ.real (K \ H) :=
      measureReal_mono hsub (measure_ne_top_of_subset sdiff_subset hKc.measure_lt_top.ne)
    _ = μ.real K - μ.real H := measureReal_sdiff hHK hHc.measurableSet hKc.measure_lt_top.ne
    _ = (1 - (1 - t) ^ Module.finrank ℝ V) * μ.real K := by
      rw [show μ.real H = (1 - t) ^ Module.finrank ℝ V * μ.real K from
        measureReal_contraction_image μ K p ht1]
      ring

/-- Bernoulli gives a dimension-linear bound for the boundary strip. -/
theorem measureReal_convex_shift_strip_le_linear {K : Set V} (hKc : IsCompact K)
    (hK : Convex ℝ K) {p e : V} (hp : p ∈ K) (hpe : p + e ∈ K)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    μ.real {x | x ∈ K ∧ x + t • e ∉ K} ≤
      Module.finrank ℝ V * t * μ.real K := by
  apply (measureReal_convex_shift_strip_le μ hKc hK hp hpe ht0 ht1).trans
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -t by linarith)
    (Module.finrank ℝ V)
  have hpow : 1 - (1 - t) ^ Module.finrank ℝ V ≤ Module.finrank ℝ V * t := by
    simpa only [sub_eq_add_neg] using (by linarith :
      1 - (1 + -t) ^ Module.finrank ℝ V ≤ Module.finrank ℝ V * t)
  exact mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg

/-- Interior-ball specialization of the boundary estimate for small translations. -/
theorem measureReal_convex_shift_strip_le_of_closedBall {K : Set V}
    (hKc : IsCompact K) (hK : Convex ℝ K) {p : V} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall p r ⊆ K) {v : V} (hv : ‖v‖ ≤ 1)
    {h : ℝ} (hh0 : 0 ≤ h) (hhr : h ≤ r) :
    μ.real {x | x ∈ K ∧ x + h • v ∉ K} ≤
      Module.finrank ℝ V * (h / r) * μ.real K := by
  have hp : p ∈ K := hball (Metric.mem_closedBall_self hr.le)
  have hpe : p + r • v ∈ K := by
    apply hball
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  have ht0 : 0 ≤ h / r := div_nonneg hh0 hr.le
  have ht1 : h / r ≤ 1 := (div_le_one hr).mpr hhr
  have hshift : (h / r) • (r • v) = h • v := by
    rw [smul_smul, div_mul_cancel₀ _ hr.ne']
  simpa only [hshift] using
    measureReal_convex_shift_strip_le_linear μ hKc hK hp hpe ht0 ht1

/-- A single linear constant controls every translation length, not only small ones. -/
theorem measureReal_convex_shift_strip_le_all {K : Set V}
    (hKc : IsCompact K) (hK : Convex ℝ K) {p : V} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall p r ⊆ K) {v : V} (hv : ‖v‖ ≤ 1)
    {h : ℝ} (hh : 0 ≤ h) :
    μ.real {x | x ∈ K ∧ x + h • v ∉ K} ≤
      (max (Module.finrank ℝ V : ℝ) 1 * μ.real K / r) * h := by
  have hvol : 0 ≤ μ.real K := measureReal_nonneg
  have herr : 0 ≤ h / r := div_nonneg hh hr.le
  by_cases hhr : h ≤ r
  · calc
      μ.real {x | x ∈ K ∧ x + h • v ∉ K} ≤
          Module.finrank ℝ V * (h / r) * μ.real K :=
        measureReal_convex_shift_strip_le_of_closedBall μ hKc hK hr hball hv hh hhr
      _ ≤ max (Module.finrank ℝ V : ℝ) 1 * (h / r) * μ.real K :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) herr) hvol
      _ = _ := by ring
  · have hrh : 1 ≤ h / r := (one_le_div hr).mpr (le_of_not_ge hhr)
    have hmax : 1 ≤ max (Module.finrank ℝ V : ℝ) 1 := le_max_right _ _
    have hfactor : 1 ≤ max (Module.finrank ℝ V : ℝ) 1 * (h / r) := by
      nlinarith
    calc
      μ.real {x | x ∈ K ∧ x + h • v ∉ K} ≤ μ.real K :=
        measureReal_mono (fun _ hx => hx.1) hKc.measure_lt_top.ne
      _ ≤ (max (Module.finrank ℝ V : ℝ) 1 * (h / r)) * μ.real K := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor hvol
      _ = _ := by ring

/-- Every compact convex body has a uniform linear boundary-strip constant. -/
theorem exists_convex_boundary_strip_constant {K : Set V}
    (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : V), ‖v‖ ≤ 1 → ∀ h : ℝ, 0 ≤ h →
      μ.real {x | x ∈ K ∧ x + h • v ∉ K} ≤ C * h := by
  obtain ⟨p, hp⟩ := hKi
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (mem_interior_iff_mem_nhds.mp hp)
  refine ⟨max (Module.finrank ℝ V : ℝ) 1 * μ.real K / r, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (le_trans (by norm_num) (le_max_right _ _))
      measureReal_nonneg) hr.le
  · intro v hv h hh
    exact measureReal_convex_shift_strip_le_all μ hKc hK hr hball hv hh

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Difference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Pointwise estimates for convex forward difference quotients

These are the pointwise ingredients of the coordinate-slice gradient
interpolation argument.  They do not assert an almost-everywhere derivative
existence result or any of the transport theorems.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace Problem358

variable {G : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]
variable {μ : Measure G} [IsAddRightInvariant μ]

/-- A measurable square-integrable function has a square-integrable translate
difference. -/
theorem integrable_translation_sub_sq (f : G → ℝ) (v : G) (hfm : Measurable f)
    (hf : Integrable (fun x => (f x) ^ 2) μ) :
    Integrable (fun x => (f (x + v) - f x) ^ 2) μ := by
  have hshift : Integrable (fun x => (f (x + v)) ^ 2) μ :=
    (measurePreserving_add_right μ v).integrable_comp_of_integrable hf
  have hu := (hshift.const_mul 2).add (hf.const_mul 2)
  have hm : Measurable (fun x => (f (x + v) - f x) ^ 2) := by fun_prop
  apply hu.mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    change ‖(f (x + v) - f x) ^ 2‖ ≤ 2 * (f (x + v)) ^ 2 + 2 * (f x) ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (f (x + v) + f x)]

/-- Local square-integrability on the common translation domain. -/
theorem integrableOn_translation_sub_sq (K : Set G) (hK : MeasurableSet K)
    (f : G → ℝ) (v : G) (hfm : Measurable f)
    (hf : IntegrableOn (fun x => (f x) ^ 2) K μ) :
    IntegrableOn (fun x => (f (x + v) - f x) ^ 2)
      (K ∩ (fun x => x + v) ⁻¹' K) μ := by
  let g := K.indicator f
  have hg2 : (fun x => (g x) ^ 2) = K.indicator (fun x => (f x) ^ 2) := by
    funext x
    by_cases hx : x ∈ K <;> simp [g, hx]
  have hg : Integrable (fun x => (g x) ^ 2) μ := by
    rw [hg2]
    exact hf.integrable_indicator hK
  have hgi := integrable_translation_sub_sq g v (hfm.indicator hK) hg
  apply hgi.restrict.congr
  filter_upwards [ae_restrict_mem (hK.inter (hK.preimage (measurable_id.add_const v)))] with x hx
  have hx1 : x + v ∈ K := hx.2
  simp [g, hx.1, hx1]

/-- Local square-integrability of the divided finite difference. -/
theorem integrableOn_translation_quotient_sq (K : Set G) (hK : MeasurableSet K)
    (f : G → ℝ) (v : G) (h : ℝ) (hfm : Measurable f)
    (hf : IntegrableOn (fun x => (f x) ^ 2) K μ) :
    IntegrableOn (fun x => ((f (x + v) - f x) / h) ^ 2)
      (K ∩ (fun x => x + v) ⁻¹' K) μ := by
  simpa only [IntegrableOn, div_pow] using (integrableOn_translation_sub_sq K hK f v hfm hf).div_const (h ^ 2)

/-- The finite-difference contribution on the set where both endpoints belong
to `K` is controlled by the potential's squared norm on `K`. -/
theorem setIntegral_translation_sub_sq_le (K : Set G) (hK : MeasurableSet K)
    (f : G → ℝ) (v : G) (hf : IntegrableOn (fun x => (f x) ^ 2) K μ) :
    (∫ x in K ∩ (fun x => x + v) ⁻¹' K, (f (x + v) - f x) ^ 2 ∂μ) ≤
      4 * ∫ x in K, (f x) ^ 2 ∂μ := by
  let g := K.indicator f
  have hg2 : (fun x => (g x) ^ 2) = K.indicator (fun x => (f x) ^ 2) := by
    funext x
    by_cases hx : x ∈ K <;> simp [g, hx]
  have hg : Integrable (fun x => (g x) ^ 2) μ := by
    rw [hg2]
    exact hf.integrable_indicator hK
  have hshift : Integrable (fun x => (g (x + v)) ^ 2) μ :=
    (measurePreserving_add_right μ v).integrable_comp_of_integrable hg
  let S := K ∩ (fun x => x + v) ⁻¹' K
  have hS : MeasurableSet S := hK.inter (hK.preimage (measurable_id.add_const v))
  have hu := (hshift.const_mul 2).add (hg.const_mul 2)
  calc
    (∫ x in S, (f (x + v) - f x) ^ 2 ∂μ) ≤
        ∫ x in S, 2 * (g (x + v)) ^ 2 + 2 * (g x) ^ 2 ∂μ := by
      apply integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) hu.restrict
      filter_upwards [ae_restrict_mem hS] with x hx
      have hx0 : x ∈ K := hx.1
      have hx1 : x + v ∈ K := hx.2
      change (f (x + v) - f x) ^ 2 ≤ 2 * (g (x + v)) ^ 2 + 2 * (g x) ^ 2
      simp only [g, Set.indicator_of_mem hx0, Set.indicator_of_mem hx1]
      nlinarith [sq_nonneg (f (x + v) + f x)]
    _ ≤ ∫ x, 2 * (g (x + v)) ^ 2 + 2 * (g x) ^ 2 ∂μ := by
      exact setIntegral_le_integral hu (ae_of_all _ fun x => by positivity)
    _ = 4 * ∫ x, (g x) ^ 2 ∂μ := by
      rw [integral_add (hshift.const_mul 2) (hg.const_mul 2),
        integral_const_mul, integral_const_mul,
        integral_add_right_eq_self (fun x => (g x) ^ 2) v]
      ring
    _ = 4 * ∫ x in K, (f x) ^ 2 ∂μ := by
      rw [hg2, integral_indicator hK]

/-- The divided finite-difference estimate used in the gradient interpolation
argument. It is valid for every real scale (including the harmless zero case). -/
theorem setIntegral_translation_quotient_sq_le (K : Set G) (hK : MeasurableSet K)
    (f : G → ℝ) (v : G) (h : ℝ)
    (hf : IntegrableOn (fun x => (f x) ^ 2) K μ) :
    (∫ x in K ∩ (fun x => x + v) ⁻¹' K, ((f (x + v) - f x) / h) ^ 2 ∂μ) ≤
      (4 / h ^ 2) * ∫ x in K, (f x) ^ 2 ∂μ := by
  simp_rw [div_pow]
  rw [integral_div]
  calc
    (∫ x in K ∩ (fun x => x + v) ⁻¹' K, (f (x + v) - f x) ^ 2 ∂μ) / h ^ 2 ≤
        (4 * ∫ x in K, (f x) ^ 2 ∂μ) / h ^ 2 :=
      div_le_div_of_nonneg_right (setIntegral_translation_sub_sq_le K hK f v hf) (sq_nonneg h)
    _ = (4 / h ^ 2) * ∫ x in K, (f x) ^ 2 ∂μ := by ring

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Translation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set

namespace Problem358

/-- Integrating a measure-preserving increment over a common core leaves only boundary terms. -/
theorem integral_increment_eq_boundary {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → X} (hf : MeasurePreserving f μ μ)
    (he : MeasurableEmbedding f) {K A : Set X} (hA : MeasurableSet A)
    (hAK : A ⊆ K) (hBK : f '' A ⊆ K) {g : X → ℝ} (hg : IntegrableOn g K μ) :
    (∫ x in A, (g (f x) - g x) ∂μ) =
      (∫ x in K \ A, g x ∂μ) - ∫ x in K \ (f '' A), g x ∂μ := by
  have hgB : IntegrableOn g (f '' A) μ := hg.mono_set hBK
  have hgf : IntegrableOn (fun x => g (f x)) A μ :=
    ((hf.restrict_image_emb he A).integrable_comp hgB.aestronglyMeasurable).mpr hgB
  rw [integral_sub hgf (hg.mono_set hAK),
    ← hf.setIntegral_image_emb he g A,
    setIntegral_sdiff hA hg hAK,
    setIntegral_sdiff (he.measurableSet_image.mpr hA) hg hBK]
  ring

/-- A bounded function has a small mean increment whenever the common core loses little mass. -/
theorem abs_integral_increment_le_boundary {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → X} (hf : MeasurePreserving f μ μ)
    (he : MeasurableEmbedding f) {K A : Set X} (hKfin : μ K ≠ ⊤)
    (hA : MeasurableSet A) (hAK : A ⊆ K) (hBK : f '' A ⊆ K)
    {g : X → ℝ} (hg : IntegrableOn g K μ) {L : ℝ}
    (hbound : ∀ x ∈ K, |g x| ≤ L) :
    |∫ x in A, (g (f x) - g x) ∂μ| ≤ 2 * L * μ.real (K \ A) := by
  have hAB : μ (f '' A) = μ A := by
    simpa only [Set.preimage_image_eq _ he.injective] using
      (hf.measure_preimage_emb he (f '' A)).symm
  have hdiff : μ.real (K \ (f '' A)) = μ.real (K \ A) := by
    rw [measureReal_sdiff hBK (he.measurableSet_image.mpr hA) hKfin,
      measureReal_sdiff hAK hA hKfin, measureReal_def μ (f '' A), hAB]
    rfl
  have hKA : μ (K \ A) < ⊤ :=
    lt_of_le_of_lt (measure_mono sdiff_subset) (lt_top_iff_ne_top.mpr hKfin)
  have hKB : μ (K \ (f '' A)) < ⊤ :=
    lt_of_le_of_lt (measure_mono sdiff_subset) (lt_top_iff_ne_top.mpr hKfin)
  have hbA : |∫ x in K \ A, g x ∂μ| ≤ L * μ.real (K \ A) := by
    simpa only [Real.norm_eq_abs] using
      norm_setIntegral_le_of_norm_le_const (f := g) (C := L) hKA (fun x hx => by
        simpa only [Real.norm_eq_abs] using hbound x hx.1)
  have hbB : |∫ x in K \ (f '' A), g x ∂μ| ≤ L * μ.real (K \ A) := by
    rw [← hdiff]
    simpa only [Real.norm_eq_abs] using
      norm_setIntegral_le_of_norm_le_const (f := g) (C := L) hKB (fun x hx => by
        simpa only [Real.norm_eq_abs] using hbound x hx.1)
  rw [integral_increment_eq_boundary hf he hA hAK hBK hg]
  exact (abs_sub _ _).trans (by linarith)

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_SupportingInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace Problem358.SupportingMapInterpolation

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Supporting inequalities at the two ends sandwich the forward quotient.
This avoids all differentiability and null-set choices in finite-map interpolation. -/
lemma slope_le_quotient_le_shift {u : F → ℝ} {T : F → F}
    (hs : Supports u T) {h : ℝ} (hh : 0 < h) (e x : F) :
    slope T e x ≤ quotient u h e x ∧
      quotient u h e x ≤ slope T e (x + h • e) := by
  have h₀ := hs x (x + h • e)
  have h₁ := hs (x + h • e) x
  have he₀ : x + h • e - x = h • e := by abel
  have he₁ : x - (x + h • e) = (-h) • e := by
    rw [neg_smul]
    abel
  rw [he₀, real_inner_smul_left] at h₀
  rw [he₁, real_inner_smul_left] at h₁
  unfold slope quotient
  constructor
  · apply (le_div_iff₀ hh).mpr
    linarith
  · apply (div_le_iff₀ hh).mpr
    linarith

lemma abs_slope_le {T : F → F} {L : ℝ} (hL : ∀ x, ‖T x‖ ≤ L)
    {e : F} (he : ‖e‖ ≤ 1) (x : F) : |slope T e x| ≤ L := by
  unfold slope
  calc
    |⟪e, T x⟫| ≤ ‖e‖ * ‖T x‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 * L := mul_le_mul he (hL x) (norm_nonneg _) (by norm_num)
    _ = L := one_mul _

/-- Squared quotient error is controlled by the monotone slope increment. -/
lemma quotient_error_sq_le {u : F → ℝ} {T : F → F}
    (hs : Supports u T) {h L : ℝ} (hh : 0 < h)
    (hL : ∀ x, ‖T x‖ ≤ L) {e : F} (he : ‖e‖ ≤ 1) (x : F) :
    (quotient u h e x - slope T e x) ^ 2 ≤
      2 * L * (slope T e (x + h • e) - slope T e x) := by
  have hq := slope_le_quotient_le_shift hs hh e x
  have hx := abs_le.mp (abs_slope_le hL he x)
  have hsx := abs_le.mp (abs_slope_le hL he (x + h • e))
  have hL0 : 0 ≤ L := (norm_nonneg (T x)).trans (hL x)
  have hδ : 0 ≤ quotient u h e x - slope T e x := sub_nonneg.mpr hq.1
  have hδbound : quotient u h e x - slope T e x ≤ 2 * L := by linarith
  have hprod := mul_nonneg hδ (sub_nonneg.mpr hδbound)
  nlinarith

lemma quotient_sub (u v : F → ℝ) (h : ℝ) (e x : F) :
    quotient (fun z => u z - v z) h e x = quotient u h e x - quotient v h e x := by
  unfold quotient
  ring

/-- The pointwise estimate whose integral gives cubic-root map stability. -/
lemma slope_difference_sq_le {u v : F → ℝ} {T S : F → F}
    (hu : Supports u T) (hv : Supports v S) {h L : ℝ} (hh : 0 < h)
    (hT : ∀ x, ‖T x‖ ≤ L) (hS : ∀ x, ‖S x‖ ≤ L)
    {e : F} (he : ‖e‖ ≤ 1) (x : F) :
    (slope T e x - slope S e x) ^ 2 ≤
      3 * (quotient (fun z => u z - v z) h e x) ^ 2 +
      6 * L * ((slope T e (x + h • e) - slope T e x) +
        (slope S e (x + h • e) - slope S e x)) := by
  have h₀ := quotient_error_sq_le hu hh hT he x
  have h₁ := quotient_error_sq_le hv hh hS he x
  rw [quotient_sub]
  nlinarith [sq_nonneg (quotient u h e x - quotient v h e x +
    (quotient u h e x - slope T e x)),
    sq_nonneg (quotient u h e x - quotient v h e x -
    (quotient v h e x - slope S e x)),
    sq_nonneg ((quotient u h e x - slope T e x) +
    (quotient v h e x - slope S e x))]

lemma slope_difference_sq_le_four {T S : F → F} {L : ℝ}
    (hT : ∀ x, ‖T x‖ ≤ L) (hS : ∀ x, ‖S x‖ ≤ L)
    {e : F} (he : ‖e‖ ≤ 1) (x : F) :
    (slope T e x - slope S e x) ^ 2 ≤ 4 * L ^ 2 := by
  have ht := abs_le.mp (abs_slope_le hT he x)
  have hs := abs_le.mp (abs_slope_le hS he x)
  have hL0 : 0 ≤ L := (norm_nonneg (T x)).trans (hT x)
  nlinarith [mul_nonneg (show 0 ≤ 2*L - (slope T e x - slope S e x) by linarith)
    (show 0 ≤ 2*L + (slope T e x - slope S e x) by linarith)]

end Problem358.SupportingMapInterpolation

namespace Problem358.SupportingMapInterpolation

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {μ : Measure F} [Measure.IsAddRightInvariant μ]

lemma measurable_slope {T : F → F} (hT : Measurable T) (e : F) :
    Measurable (slope T e) := by
  unfold slope
  exact (continuous_const.inner continuous_id).measurable.comp hT

omit [Measure.IsAddRightInvariant μ] in
lemma integrableOn_slope {T : F → F} (hT : Measurable T)
    {K : Set F} (hKfin : μ K ≠ ⊤) {L : ℝ} (hL : ∀ x, ‖T x‖ ≤ L)
    {e : F} (he : ‖e‖ ≤ 1) : IntegrableOn (slope T e) K μ := by
  apply μ.integrableOn_of_bounded hKfin (measurable_slope hT e).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using abs_slope_le hL he x

omit [Measure.IsAddRightInvariant μ] in
lemma integrableOn_slope_difference_sq {T S : F → F}
    (hT : Measurable T) (hS : Measurable S)
    {K : Set F} (hKfin : μ K ≠ ⊤) {L : ℝ}
    (hTL : ∀ x, ‖T x‖ ≤ L) (hSL : ∀ x, ‖S x‖ ≤ L)
    {e : F} (he : ‖e‖ ≤ 1) :
    IntegrableOn (fun x => (slope T e x - slope S e x) ^ 2) K μ := by
  have hm : Measurable (fun x => (slope T e x - slope S e x) ^ 2) :=
    ((measurable_slope hT e).sub (measurable_slope hS e)).pow_const 2
  apply μ.integrableOn_of_bounded hKfin hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact slope_difference_sq_le_four hTL hSL he x

/-- A derivative-free directional interpolation estimate.  All geometry of the
source is isolated in the lost mass of its translation core. -/
theorem integral_slope_difference_sq_le
    {u v : F → ℝ} {T S : F → F}
    (hu : Supports u T) (hv : Supports v S)
    (hT : Measurable T) (hS : Measurable S)
    {K : Set F} (hK : MeasurableSet K) (hKfin : μ K ≠ ⊤)
    {L h : ℝ} (hTL : ∀ x, ‖T x‖ ≤ L) (hSL : ∀ x, ‖S x‖ ≤ L)
    (hh : 0 < h) {e : F} (he : ‖e‖ ≤ 1)
    (hfm : Measurable (fun x => u x - v x))
    (hf : IntegrableOn (fun x => (u x - v x) ^ 2) K μ) :
    (∫ x in K, (slope T e x - slope S e x) ^ 2 ∂μ) ≤
      (12 / h ^ 2) * (∫ x in K, (u x - v x) ^ 2 ∂μ) +
      28 * L ^ 2 * μ.real (K \ (K ∩ (fun x => x + h • e) ⁻¹' K)) := by
  let A : Set F := K ∩ (fun x => x + h • e) ⁻¹' K
  have hA : MeasurableSet A := hK.inter (hK.preimage (measurable_id.add_const _))
  have hAK : A ⊆ K := Set.inter_subset_left
  have hBK : (fun x : F => x + h • e) '' A ⊆ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  have hAfin : μ A ≠ ⊤ := measure_ne_top_of_subset hAK hKfin
  have hL0 : 0 ≤ L := (norm_nonneg (T 0)).trans (hTL 0)
  have htK := integrableOn_slope hT hKfin hTL he
  have hsK := integrableOn_slope hS hKfin hSL he
  have hqK := integrableOn_slope_difference_sq hT hS hKfin hTL hSL he
  have htA := htK.mono_set hAK
  have hsA := hsK.mono_set hAK
  have htShift : IntegrableOn (fun x => slope T e (x + h • e)) A μ := by
    apply μ.integrableOn_of_bounded hAfin
      ((measurable_slope hT e).comp (measurable_id.add_const _)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, Function.comp_apply, id_eq] using abs_slope_le hTL he (x + h • e)
  have hsShift : IntegrableOn (fun x => slope S e (x + h • e)) A μ := by
    apply μ.integrableOn_of_bounded hAfin
      ((measurable_slope hS e).comp (measurable_id.add_const _)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, Function.comp_apply, id_eq] using abs_slope_le hSL he (x + h • e)
  have htInc : IntegrableOn (fun x => slope T e (x + h • e) - slope T e x) A μ := htShift.sub htA
  have hsInc : IntegrableOn (fun x => slope S e (x + h • e) - slope S e x) A μ := hsShift.sub hsA
  have hquot : IntegrableOn (fun x => (quotient (fun z => u z - v z) h e x) ^ 2) A μ :=
    integrableOn_translation_quotient_sq K hK (fun x => u x - v x) (h • e) h hfm hf
  have hcore := integral_mono_ae (hqK.mono_set hAK)
    ((hquot.const_mul 3).add ((htInc.add hsInc).const_mul (6 * L)))
    (Filter.Eventually.of_forall fun x => slope_difference_sq_le hu hv hh hTL hSL he x)
  simp only [Pi.add_apply] at hcore
  have hadd := integral_add (hquot.const_mul 3) ((htInc.add hsInc).const_mul (6 * L))
  have haddInc := integral_add htInc hsInc
  simp only [Pi.add_apply] at hadd haddInc
  rw [hadd, integral_const_mul, integral_const_mul, haddInc] at hcore
  have hpres : MeasurePreserving (fun x : F => x + h • e) μ μ :=
    measurePreserving_add_right μ (h • e)
  have hemb : MeasurableEmbedding (fun x : F => x + h • e) :=
    (MeasurableEquiv.addRight (h • e)).measurableEmbedding
  have htBound := abs_integral_increment_le_boundary hpres hemb hKfin hA hAK hBK htK
    (fun x _ => abs_slope_le hTL he x)
  have hsBound := abs_integral_increment_le_boundary hpres hemb hKfin hA hAK hBK hsK
    (fun x _ => abs_slope_le hSL he x)
  have htUpper := (le_abs_self _).trans htBound
  have hsUpper := (le_abs_self _).trans hsBound
  have hfBound := setIntegral_translation_quotient_sq_le K hK
    (fun x => u x - v x) (h • e) h hf
  change (∫ x in A, (quotient (fun z => u z - v z) h e x) ^ 2 ∂μ) ≤
    (4 / h ^ 2) * (∫ x in K, (u x - v x) ^ 2 ∂μ) at hfBound
  have hcoreBound : (∫ x in A, (slope T e x - slope S e x) ^ 2 ∂μ) ≤
      (12 / h ^ 2) * (∫ x in K, (u x - v x) ^ 2 ∂μ) +
      24 * L ^ 2 * μ.real (K \ A) := by
    calc
      _ ≤ 3 * (∫ x in A, (quotient (fun z => u z - v z) h e x) ^ 2 ∂μ) +
          6 * L * ((∫ x in A, slope T e (x + h • e) - slope T e x ∂μ) +
            ∫ x in A, slope S e (x + h • e) - slope S e x ∂μ) := hcore
      _ ≤ 3 * ((4 / h ^ 2) * (∫ x in K, (u x - v x) ^ 2 ∂μ)) +
          6 * L * (2 * L * μ.real (K \ A) + 2 * L * μ.real (K \ A)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hfBound (by norm_num))
          (mul_le_mul_of_nonneg_left (add_le_add htUpper hsUpper) (by positivity))
      _ = _ := by ring
  have hstripfin : μ (K \ A) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.sdiff_subset) hKfin.lt_top
  have hstripBound : (∫ x in K \ A, (slope T e x - slope S e x) ^ 2 ∂μ) ≤
      4 * L ^ 2 * μ.real (K \ A) := by
    have hb := norm_setIntegral_le_of_norm_le_const (f := fun x =>
        (slope T e x - slope S e x) ^ 2) (C := 4 * L ^ 2) hstripfin
      (fun x _ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact slope_difference_sq_le_four hTL hSL he x)
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hb)
  rw [setIntegral_sdiff hA hqK hAK] at hstripBound
  change (∫ x in K, (slope T e x - slope S e x) ^ 2 ∂μ) ≤
    (12 / h ^ 2) * (∫ x in K, (u x - v x) ^ 2 ∂μ) + 28 * L ^ 2 * μ.real (K \ A)
  linarith

end Problem358.SupportingMapInterpolation

namespace Problem358.SupportingMapInterpolation

variable {ι : Type*} [Fintype ι]
  {μ : Measure (EuclideanSpace ℝ ι)} [Measure.IsAddRightInvariant μ]

/-- Summing the directional estimate gives full-dimensional interpolation for
bounded supporting maps. Only a linear boundary-strip estimate is needed. -/
theorem integral_norm_sub_sq_le_of_boundary_strip
    {u v : EuclideanSpace ℝ ι → ℝ}
    {T S : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hu : Supports u T) (hv : Supports v S)
    (hT : Measurable T) (hS : Measurable S)
    {K : Set (EuclideanSpace ℝ ι)} (hK : MeasurableSet K) (hKfin : μ K ≠ ⊤)
    {L C h : ℝ} (hTL : ∀ x, ‖T x‖ ≤ L) (hSL : ∀ x, ‖S x‖ ≤ L)
    (hh : 0 < h)
    (hfm : Measurable (fun x => u x - v x))
    (hf : IntegrableOn (fun x => (u x - v x) ^ 2) K μ)
    (hstrip : ∀ e : EuclideanSpace ℝ ι, ‖e‖ ≤ 1 →
      μ.real {x | x ∈ K ∧ x + h • e ∉ K} ≤ C * h) :
    (∫ x in K, ‖T x - S x‖ ^ 2 ∂μ) ≤
      (12 * (Fintype.card ι : ℝ) / h ^ 2) * (∫ x in K, (u x - v x) ^ 2 ∂μ) +
      28 * (Fintype.card ι : ℝ) * L ^ 2 * C * h := by
  classical
  have hcoordInt (i : ι) : IntegrableOn (fun x => (T x i - S x i) ^ 2) K μ := by
    simpa only [slope, EuclideanSpace.inner_single_left, map_one, one_mul] using
      (integrableOn_slope_difference_sq hT hS hKfin hTL hSL
        (e := EuclideanSpace.single i 1) (by simp))
  have hcoordBound (i : ι) :
      (∫ x in K, (T x i - S x i) ^ 2 ∂μ) ≤
        (12 / h ^ 2) * (∫ x in K, (u x - v x) ^ 2 ∂μ) + 28 * L ^ 2 * C * h := by
    let e : EuclideanSpace ℝ ι := EuclideanSpace.single i 1
    have he : ‖e‖ ≤ 1 := by simp [e]
    have hb := integral_slope_difference_sq_le hu hv hT hS hK hKfin hTL hSL
      hh he hfm hf
    have hset : K \ (K ∩ (fun x => x + h • e) ⁻¹' K) =
        {x | x ∈ K ∧ x + h • e ∉ K} := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
      tauto
    rw [hset] at hb
    have hbound := hb.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (hstrip e he) (by positivity : 0 ≤ 28 * L ^ 2)))
    simpa only [e, slope, EuclideanSpace.inner_single_left, map_one, one_mul, mul_assoc] using hbound
  calc
    (∫ x in K, ‖T x - S x‖ ^ 2 ∂μ) =
        ∫ x in K, ∑ i, (T x i - S x i) ^ 2 ∂μ := by
      congr 1
      funext x
      simp [EuclideanSpace.real_norm_sq_eq]
    _ = ∑ i, ∫ x in K, (T x i - S x i) ^ 2 ∂μ :=
      integral_finsetSum _ fun i _ => hcoordInt i
    _ ≤ ∑ _i : ι, ((12 / h ^ 2) * (∫ x in K, (u x - v x) ^ 2 ∂μ) + 28 * L ^ 2 * C * h) :=
      Finset.sum_le_sum fun i _ => hcoordBound i
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end Problem358.SupportingMapInterpolation

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_UniformInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace Problem358.SupportingMapInterpolation

/-- Full quantitative interpolation for bounded supporting maps over an arbitrary
compact convex body. Its geometric constant is independent of the potentials,
maps, atom counts, masses, and slope separation. -/
theorem exists_integral_interpolation_constant
    {ι : Type*} [Fintype ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [Measure.IsAddHaarMeasure μ]
    {K : Set (EuclideanSpace ℝ ι)}
    (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty)
    (L : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (u v : EuclideanSpace ℝ ι → ℝ)
        (T S : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι),
      Continuous u → Continuous v → Supports u T → Supports v S →
      Measurable T → Measurable S → (∀ x, ‖T x‖ ≤ L) → (∀ x, ‖S x‖ ≤ L) →
      ∀ h : ℝ, 0 < h →
      (∫ x in K, ‖T x - S x‖ ^ 2 ∂μ) ≤
        (12 * (Fintype.card ι : ℝ) / h ^ 2) * (∫ x in K, (u x - v x) ^ 2 ∂μ) +
        B * h := by
  obtain ⟨C, hC, hstrip⟩ := exists_convex_boundary_strip_constant μ hKc hK hKi
  refine ⟨28 * (Fintype.card ι : ℝ) * L ^ 2 * C, by positivity, ?_⟩
  intro u v T S huc hvc hu hv hT hS hTL hSL h hh
  have hf : IntegrableOn (fun x => (u x - v x) ^ 2) K μ :=
    ContinuousOn.integrableOn_compact hKc ((huc.sub hvc).pow 2).continuousOn
  exact integral_norm_sub_sq_le_of_boundary_strip hu hv hT hS hKc.measurableSet
    hKc.measure_lt_top.ne hTL hSL hh (huc.sub hvc).measurable hf
    (fun e he => hstrip e he h hh.le)

end Problem358.SupportingMapInterpolation

end

noncomputable section

namespace Problem358

/-- The real one-third power is a nonnegative cube root. -/
lemma one_third_rpow_cube {w : ℝ} (hw : 0 ≤ w) :
    (Real.rpow w (1 / 3 : ℝ)) ^ 3 = w := by
  calc
    (Real.rpow w (1 / 3 : ℝ)) ^ 3 =
        Real.rpow (Real.rpow w (1 / 3 : ℝ)) (3 : ℝ) := by
          exact (Real.rpow_natCast _ 3).symm
    _ = Real.rpow w ((1 / 3 : ℝ) * 3) := (Real.rpow_mul hw _ _).symm
    _ = w := by norm_num

/-- The scalar optimization in the gradient-interpolation argument.
The hypothesis is the squared slice estimate, valid at every positive scale.
This formulation includes zero Wasserstein distance without a limiting argument. -/
theorem stability_of_slice_bound {D w A B : ℝ}
    (hD : 0 ≤ D) (hw : 0 ≤ w) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ h : ℝ, 0 < h → D ^ 2 ≤ A * w ^ 2 / h ^ 2 + B * h) :
    D ≤ Real.sqrt (A + B) * Real.rpow w (1 / 3 : ℝ) := by
  by_cases hw0 : w = 0
  · subst w
    have hDz : D = 0 := by
      by_contra hne
      have hDp : 0 < D := lt_of_le_of_ne hD (Ne.symm hne)
      have hB1 : 0 < B + 1 := by linarith
      have hD2 : 0 < D ^ 2 := sq_pos_of_pos hDp
      have hh := hbound (D ^ 2 / (B + 1)) (div_pos hD2 hB1)
      simp only [zero_pow (by omega : 2 ≠ 0), mul_zero, zero_div, zero_add] at hh
      rw [← mul_div_assoc] at hh
      have hh' := (le_div_iff₀ hB1).mp hh
      nlinarith
    simp [hDz]
  · have hwp : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
    let t := Real.rpow w (1 / 3 : ℝ)
    have ht : 0 < t := Real.rpow_pos_of_pos hwp _
    have ht3 : t ^ 3 = w := one_third_rpow_cube hw
    have hh := hbound (t ^ 2) (sq_pos_of_pos ht)
    have hquot : A * w ^ 2 / (t ^ 2) ^ 2 = A * t ^ 2 := by
      rw [← ht3]
      field_simp
    rw [hquot] at hh
    have hsum : 0 ≤ A + B := add_nonneg hA hB
    have hright : 0 ≤ Real.sqrt (A + B) * t :=
      mul_nonneg (Real.sqrt_nonneg _) ht.le
    apply (sq_le_sq₀ hD hright).mp
    calc
      D ^ 2 ≤ (A + B) * t ^ 2 := by nlinarith [hh]
      _ = (Real.sqrt (A + B) * t) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hsum]

end Problem358

open MeasureTheory

namespace Problem358.UniformInterpolation

variable {d : ℕ} (K : Set (E d))

/-- Normalizing the source multiplies every real integral by the same
nonnegative scalar. No finiteness assumptions are needed for this identity. -/
theorem integral_eq (f : E d → ℝ) :
    (∫ x, f x ∂uniformMeasure K) =
      ((volume K)⁻¹).toReal * ∫ x in K, f x := by
  simp only [uniformMeasure, integral_smul_measure, smul_eq_mul]

/-- The squared map distance is the normalized unnormalized-source energy. -/
theorem mapL2Dist_sq_eq (T S : E d → E d) :
    mapL2Dist (uniformMeasure K) T S ^ 2 =
      ((volume K)⁻¹).toReal * ∫ x in K, ‖T x - S x‖ ^ 2 := by
  unfold mapL2Dist
  rw [Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]
  exact integral_eq K _

/-- Transfer the raw finite-difference estimate to the exact normalized-source
and map-distance conventions of the qualified problem. -/
theorem slice_bound_of_raw
    {T S : E d → E d} {f : E d → ℝ} {A B h : ℝ}
    (hraw : (∫ x in K, ‖T x - S x‖ ^ 2) ≤
      (A / h ^ 2) * (∫ x in K, f x ^ 2) + B * h) :
    mapL2Dist (uniformMeasure K) T S ^ 2 ≤
      (A / h ^ 2) * (∫ x, f x ^ 2 ∂uniformMeasure K) +
        (((volume K)⁻¹).toReal * B) * h := by
  rw [mapL2Dist_sq_eq]
  calc
    _ ≤ ((volume K)⁻¹).toReal *
        ((A / h ^ 2) * (∫ x in K, f x ^ 2) + B * h) :=
      mul_le_mul_of_nonneg_left hraw ENNReal.toReal_nonneg
    _ = _ := by rw [integral_eq]; ring

/-- Raw volume interpolation plus a normalized squared-potential estimate
implies the desired one-third bound, including zero target distance. -/
theorem one_third_bound_of_raw
    {T S : E d → E d} {f : E d → ℝ} {A B P w : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hw : 0 ≤ w)
    (hpotential : (∫ x, f x ^ 2 ∂uniformMeasure K) ≤ P ^ 2 * w ^ 2)
    (hraw : ∀ h : ℝ, 0 < h → (∫ x in K, ‖T x - S x‖ ^ 2) ≤
      (A / h ^ 2) * (∫ x in K, f x ^ 2) + B * h) :
    mapL2Dist (uniformMeasure K) T S ≤
      Real.sqrt (A * P ^ 2 + ((volume K)⁻¹).toReal * B) *
        Real.rpow w (1 / 3 : ℝ) := by
  apply Problem358.stability_of_slice_bound (Real.sqrt_nonneg _) hw
    (mul_nonneg hA (sq_nonneg P)) (mul_nonneg ENNReal.toReal_nonneg hB)
  intro h hh
  calc
    _ ≤ (A / h ^ 2) * (∫ x, f x ^ 2 ∂uniformMeasure K) +
        (((volume K)⁻¹).toReal * B) * h := slice_bound_of_raw K (hraw h hh)
    _ ≤ (A / h ^ 2) * (P ^ 2 * w ^ 2) +
        (((volume K)⁻¹).toReal * B) * h := by
      exact add_le_add (mul_le_mul_of_nonneg_left hpotential
        (div_nonneg hA (sq_nonneg h))) le_rfl
    _ = _ := by ring

end Problem358.UniformInterpolation

end

noncomputable section

open MeasureTheory

namespace Problem358.UniformInterpolation

open SupportingMapInterpolation

/-- Adding a constant to a potential does not change its supporting map. -/
theorem supports_add_const {d : ℕ} {u : E d → ℝ} {T : E d → E d}
    (hu : Supports u T) (c : ℝ) : Supports (fun x => u x + c) T := by
  intro x z
  have h := hu x z
  dsimp
  linarith

/-- The full normalized interpolation theorem, with no residual geometric or
finite-difference hypotheses.  The potential estimate may be supplied modulo
an arbitrary additive constant, as in a variance bound. -/
theorem exists_normalized_one_third_constant
    {d : ℕ} {K : Set (E d)}
    (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty)
    (L P : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u v : E d → ℝ) (T S : E d → E d),
      Continuous u → Continuous v → Supports u T → Supports v S →
      Measurable T → Measurable S → (∀ x, ‖T x‖ ≤ L) → (∀ x, ‖S x‖ ≤ L) →
      ∀ w : ℝ, 0 ≤ w →
      (∃ c : ℝ, (∫ x, (u x - v x - c) ^ 2 ∂uniformMeasure K) ≤ P ^ 2 * w ^ 2) →
      mapL2Dist (uniformMeasure K) T S ≤ C * Real.rpow w (1 / 3 : ℝ) := by
  obtain ⟨B, hB, hraw⟩ := exists_integral_interpolation_constant
    (volume : Measure (E d)) hKc hK hKi L
  refine ⟨Real.sqrt (12 * (d : ℝ) * P ^ 2 + ((volume K)⁻¹).toReal * B),
    Real.sqrt_nonneg _, ?_⟩
  intro u v T S huc hvc hu hv hT hS hTL hSL w hw hpotential
  obtain ⟨c, hc⟩ := hpotential
  apply one_third_bound_of_raw K (by positivity : 0 ≤ 12 * (d : ℝ)) hB hw hc
  intro h hh
  have hb := hraw u (fun x => v x + c) T S huc (hvc.add continuous_const)
    hu (supports_add_const hv c) hT hS hTL hSL h hh
  simpa only [Fintype.card_fin, sub_add_eq_sub_sub] using hb

end Problem358.UniformInterpolation

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_AtomicPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal RealInnerProductSpace

namespace Problem358

namespace SupportingMapInterpolation

/-- A globally supporting map with bounded values makes its potential Lipschitz.
No differentiability or convexity premise is needed for this implication. -/
theorem Supports.lipschitzWith {d : ℕ} {u : E d → ℝ} {T : E d → E d}
    (h : Supports u T) {L : ℝ≥0} (hL : ∀ x, ‖T x‖ ≤ L) :
    LipschitzWith L u := by
  apply LipschitzWith.of_le_add_mul L
  intro x z
  have hs := h x z
  rw [show z - x = -(x - z) by abel, inner_neg_left] at hs
  have hi : ⟪x - z, T x⟫ ≤ (L : ℝ) * dist x z := by
    calc
      ⟪x - z, T x⟫ ≤ |⟪x - z, T x⟫| := le_abs_self _
      _ ≤ ‖x - z‖ * ‖T x‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖x - z‖ * L := mul_le_mul_of_nonneg_left (hL x) (norm_nonneg _)
      _ = (L : ℝ) * dist x z := by rw [dist_eq_norm, mul_comm]
  linarith

end SupportingMapInterpolation

/-- The exact compact-target stability conclusion reduces to a uniform potential
estimate for finite targets. The supplier only gives supporting maps and their
laws: optimality, uniqueness, the one-third interpolation, and passage to
arbitrary compactly supported probabilities are all proved here. -/
theorem one_third_stability_of_finite_potential_estimate
    {d : ℕ} {K Y : Set (E d)}
    (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hY : IsCompact Y) (hYne : Y.Nonempty)
    (L : ℝ≥0) (P : ℝ)
    (hpotential : ∀ (μ ν : Measure (E d)),
      IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      (∃ F : Set (E d), F.Finite ∧ F ⊆ Y ∧ IsSupported μ F) →
      (∃ G : Set (E d), G.Finite ∧ G ⊆ Y ∧ IsSupported ν G) →
      ∃ (u v : E d → ℝ) (T S : E d → E d),
        SupportingMapInterpolation.Supports u T ∧
        SupportingMapInterpolation.Supports v S ∧
        Measurable T ∧ Measurable S ∧
        (∀ x, ‖T x‖ ≤ L) ∧ (∀ x, ‖S x‖ ≤ L) ∧
        Measure.map T (uniformMeasure K) = μ ∧
        Measure.map S (uniformMeasure K) = ν ∧
        ∃ c : ℝ, (∫ x, (u x - v x - c) ^ 2 ∂uniformMeasure K) ≤
          P ^ 2 * wasserstein2 μ ν ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ ν : Measure (E d)),
      IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      IsSupported μ Y → IsSupported ν Y →
      ∃ Tμ Tν : E d → E d,
        IsUniqueQuadraticOptimalMap (uniformMeasure K) μ Tμ ∧
        IsUniqueQuadraticOptimalMap (uniformMeasure K) ν Tν ∧
        mapL2Dist (uniformMeasure K) Tμ Tν ≤
          C * Real.rpow (wasserstein2 μ ν) (1 / 3 : ℝ) := by
  obtain ⟨C, hC, hinterpolate⟩ :=
    UniformInterpolation.exists_normalized_one_third_constant hK hKconv hKint L P
  refine ⟨C, hC, one_third_stability_of_finite_targets hK hKconv hKint hY hYne hC ?_⟩
  intro μ ν hμprob hνprob hμfinite hνfinite
  let : IsProbabilityMeasure μ := hμprob
  let : IsProbabilityMeasure ν := hνprob
  obtain ⟨u, v, T, S, hu, hv, hT, hS, hTL, hSL, hTlaw, hSlaw, hbound⟩ :=
    hpotential μ ν hμprob hνprob hμfinite hνfinite
  have hμY : IsSupported μ Y := by
    obtain ⟨F, _, hFY, hμF⟩ := hμfinite
    exact le_antisymm ((measure_mono (Set.compl_subset_compl.mpr hFY)).trans_eq hμF)
      zero_le
  have hνY : IsSupported ν Y := by
    obtain ⟨G, _, hGY, hνG⟩ := hνfinite
    exact le_antisymm ((measure_mono (Set.compl_subset_compl.mpr hGY)).trans_eq hνG)
      zero_le
  have huLip := hu.lipschitzWith hTL
  have hvLip := hv.lipschitzWith hSL
  have hKne : K.Nonempty := hKint.mono interior_subset
  refine ⟨T, S, ?_, ?_, ?_⟩
  · apply isUniqueQuadraticOptimalMap_of_supporting_potential hK hKconv hKne
      hY hμY huLip.lipschitzOnWith hT hTlaw
    exact Filter.Eventually.of_forall fun x z _ => by
      simpa only [real_inner_comm (T x) (z - x)] using hu x z
  · apply isUniqueQuadraticOptimalMap_of_supporting_potential hK hKconv hKne
      hY hνY hvLip.lipschitzOnWith hS hSlaw
    exact Filter.Eventually.of_forall fun x z _ => by
      simpa only [real_inner_comm (S x) (z - x)] using hv x z
  · exact hinterpolate u v T S huLip.continuous hvLip.continuous hu hv hT hS
      hTL hSL (wasserstein2 μ ν) (wasserstein2_nonneg μ ν) hbound

end Problem358

end

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Problem358

/-- A potential estimate for positive fixed-mass, noncolliding atomic motions
implies the full compact-target theorem. The optimal finite coupling, zero-mass
deletion, endpoint laws and exact Wasserstein energy are supplied internally. -/
theorem one_third_stability_of_atomic_potential_estimate
    {d : ℕ} {K Y : Set (E d)}
    (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hY : IsCompact Y) (hYne : Y.Nonempty)
    (L : ℝ≥0) (hYL : ∀ z ∈ Y, ‖z‖ ≤ L) (P : ℝ)
    (hpotential : ∀ (n : ℕ), 0 < n →
      ∀ (m : Fin n → ℝ) (y z : Fin n → E d),
      (∀ i, 0 < m i) → (∑ i, m i) = 1 →
      (∀ i, ‖y i‖ ≤ L) → (∀ i, ‖z i‖ ≤ L) →
      (∀ t : ℝ, 0 < t → t < 1 →
        Function.Injective (fun i => (1-t) • y i + t • z i)) →
      ∃ (u v : E d → ℝ) (T S : E d → E d),
        SupportingMapInterpolation.Supports u T ∧
        SupportingMapInterpolation.Supports v S ∧
        Measurable T ∧ Measurable S ∧
        (∀ x, ‖T x‖ ≤ L) ∧ (∀ x, ‖S x‖ ≤ L) ∧
        Measure.map T (uniformMeasure K) =
          ∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i) ∧
        Measure.map S (uniformMeasure K) =
          ∑ i, ENNReal.ofReal (m i) • Measure.dirac (z i) ∧
        ∃ c : ℝ, (∫ x, (u x - v x - c) ^ 2 ∂uniformMeasure K) ≤
          P ^ 2 * ∑ i, m i * ‖y i - z i‖ ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ ν : Measure (E d)),
      IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      IsSupported μ Y → IsSupported ν Y →
      ∃ Tμ Tν : E d → E d,
        IsUniqueQuadraticOptimalMap (uniformMeasure K) μ Tμ ∧
        IsUniqueQuadraticOptimalMap (uniformMeasure K) ν Tν ∧
        mapL2Dist (uniformMeasure K) Tμ Tν ≤
          C * Real.rpow (wasserstein2 μ ν) (1 / 3 : ℝ) := by
  apply one_third_stability_of_finite_potential_estimate hK hKconv hKint hY hYne L P
  intro μ ν hμprob hνprob hμfinite hνfinite
  let : IsProbabilityMeasure μ := hμprob
  let : IsProbabilityMeasure ν := hνprob
  obtain ⟨F, hF, hFY, hμF⟩ := hμfinite
  obtain ⟨G, hG, hGY, hνG⟩ := hνfinite
  obtain ⟨n, hn, m, y, z, hm, hsum, hyF, hzG, hμeq, hνeq, _, henergy, hinj⟩ :=
    exists_finite_atomic_motion hF hG hμF hνG
  obtain ⟨u, v, T, S, hu, hv, hT, hS, hTL, hSL, hTlaw, hSlaw, c, hc⟩ :=
    hpotential n hn m y z hm hsum (fun i => hYL _ (hFY (hyF i)))
      (fun i => hYL _ (hGY (hzG i))) hinj
  refine ⟨u, v, T, S, hu, hv, hT, hS, hTL, hSL,
    hTlaw.trans hμeq.symm, hSlaw.trans hνeq.symm, c, ?_⟩
  simpa only [henergy] using hc

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_EndpointEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded intercept speeds give finite endpoint values in the moving-site argument. -/

noncomputable section

open Set Filter
open scoped BigOperators Topology NNReal

namespace Problem358
namespace InterceptEndpointExtension

/-- A positive weighted quadratic-energy bound controls every coordinate.
The mass dependence is used only to construct endpoint intercepts. -/
theorem abs_le_sqrt_energy_div_mass
    {ι : Type*} [Fintype ι] (m r : ι → ℝ) {energy : ℝ}
    (hm : ∀ i, 0 < m i)
    (henergy : (∑ i, m i * r i ^ 2) ≤ energy) (i : ι) :
    |r i| ≤ Real.sqrt (energy / m i) := by
  classical
  have hsingle : m i * r i ^ 2 ≤ energy :=
    (Finset.single_le_sum
      (fun j _ => mul_nonneg (hm j).le (sq_nonneg (r j)))
      (Finset.mem_univ i)).trans henergy
  have hsquare : r i ^ 2 ≤ energy / m i := by
    apply (le_div_iff₀ (hm i)).mpr
    simpa only [mul_comm] using hsingle
  simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hsquare

/-- Intercept derivatives with a uniform weighted energy bound give a
coordinatewise Lipschitz estimate on the entire open time interval. -/
theorem lipschitzOnWith_of_weighted_derivative_energy
    {ι : Type*} [Fintype ι] (m : ι → ℝ) (c r : ι → ℝ → ℝ)
    {a b energy : ℝ} (hm : ∀ i, 0 < m i)
    (hderiv : ∀ i t, t ∈ Ioo a b → HasDerivAt (c i) (r i t) t)
    (henergy : ∀ t ∈ Ioo a b, (∑ i, m i * r i t ^ 2) ≤ energy)
    (i : ι) :
    LipschitzOnWith ⟨Real.sqrt (energy / m i), Real.sqrt_nonneg _⟩ (c i) (Ioo a b) := by
  apply (convex_Ioo a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => (hderiv i t ht).hasDerivWithinAt)
  intro t ht
  change ‖r i t‖ ≤ Real.sqrt (energy / m i)
  simpa only [Real.norm_eq_abs] using
    abs_le_sqrt_energy_div_mass m (fun j => r j t) hm (henergy t ht) i

/-- A fixed-mass intercept path with bounded weighted derivative energy has
continuous endpoint values.  The extension agrees on the interior and has the
same interior derivatives.  No separation of endpoint sites is required. -/
theorem exists_lipschitz_extension
    {ι : Type*} [Fintype ι] (m : ι → ℝ) (c r : ι → ℝ → ℝ)
    {a b energy : ℝ} (hm : ∀ i, 0 < m i)
    (hderiv : ∀ i t, t ∈ Ioo a b → HasDerivAt (c i) (r i t) t)
    (henergy : ∀ t ∈ Ioo a b, (∑ i, m i * r i t ^ 2) ≤ energy) :
    ∃ C : ι → ℝ → ℝ,
      (∀ i, LipschitzWith ⟨Real.sqrt (energy / m i), Real.sqrt_nonneg _⟩ (C i)) ∧
      (∀ i, EqOn (c i) (C i) (Ioo a b)) ∧
      (∀ i t, t ∈ Ioo a b → HasDerivAt (C i) (r i t) t) := by
  classical
  choose C hC hEq using fun i =>
    (lipschitzOnWith_of_weighted_derivative_energy m c r hm hderiv henergy i).extend_real
  refine ⟨C, hC, hEq, ?_⟩
  intro i t ht
  apply (hderiv i t ht).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with q hq
  exact (hEq i hq).symm

/-- The normalization of an interior intercept path extends to both endpoints.
The extension is globally measurable, hence can be used directly by the finite
affine-potential time-integration interface. -/
theorem exists_normalized_lipschitz_extension
    {ι : Type*} [Fintype ι] (m : ι → ℝ) (c r : ι → ℝ → ℝ)
    {a b energy : ℝ} (hab : a < b) (hm : ∀ i, 0 < m i)
    (hderiv : ∀ i t, t ∈ Ioo a b → HasDerivAt (c i) (r i t) t)
    (henergy : ∀ t ∈ Ioo a b, (∑ i, m i * r i t ^ 2) ≤ energy)
    (hnormal : ∀ t ∈ Ioo a b, (∑ i, m i * c i t) = 0) :
    ∃ C : ι → ℝ → ℝ,
      (∀ i, LipschitzWith ⟨Real.sqrt (energy / m i), Real.sqrt_nonneg _⟩ (C i)) ∧
      (∀ i, EqOn (c i) (C i) (Ioo a b)) ∧
      (∀ i t, t ∈ Ioo a b → HasDerivAt (C i) (r i t) t) ∧
      (∀ t ∈ Icc a b, (∑ i, m i * C i t) = 0) ∧
      (∀ i, Measurable (C i)) := by
  classical
  obtain ⟨C, hC, hEq, hdC⟩ := exists_lipschitz_extension m c r hm hderiv henergy
  refine ⟨C, hC, hEq, hdC, ?_, fun i => (hC i).continuous.measurable⟩
  have hsum : EqOn (fun t => ∑ i, m i * C i t) (fun _ => 0) (Ioo a b) := by
    intro t ht
    rw [← hnormal t ht]
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun x => m i * x) (hEq i ht).symm)
  have hcont : Continuous (fun t => ∑ i, m i * C i t) :=
    continuous_finsetSum _ (fun i _ => continuous_const.mul (hC i).continuous)
  have hclosure := hsum.closure hcont continuous_const
  intro t ht
  apply hclosure
  simpa only [closure_Ioo hab.ne] using ht

end InterceptEndpointExtension
end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_MaxLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter

namespace Problem358

/-- A maximizer among finitely many convergent scores is eventually a maximizer
of the limiting scores. Only membership in the limiting maximizing set is asserted;
ties among the limiting scores need not be resolved consistently. -/
theorem eventually_limiting_maximizer
    {ι β : Type*} [Finite ι] {l : Filter β}
    {score : β → ι → ℝ} {limitScore : ι → ℝ} {pick : β → ι}
    (hscore : ∀ i, Tendsto (fun n => score n i) l (nhds (limitScore i)))
    (hpick : ∀ᶠ n in l, ∀ i, score n i ≤ score n (pick n)) :
    ∀ᶠ n in l, ∀ i, limitScore i ≤ limitScore (pick n) := by
  have hpair : ∀ i j, ∀ᶠ n in l,
      limitScore j < limitScore i → score n j < score n i := by
    intro i j
    by_cases hij : limitScore j < limitScore i
    · exact ((hscore j).eventually_lt (hscore i) hij).mono fun n hn _ => hn
    · exact Eventually.of_forall fun n hn => (hij hn).elim
  have hall : ∀ᶠ n in l, ∀ i j,
      limitScore j < limitScore i → score n j < score n i := by
    simpa only [eventually_all] using hpair
  filter_upwards [hpick, hall] with n hn halln
  intro i
  by_contra h
  exact (not_lt_of_ge (hn i)) (halln i (pick n) (lt_of_not_ge h))

/-- Finite active-value convergence, allowing different active indices at every
parameter and repeated limiting slopes. This is the endpoint argument for finite
maxima of moving affine functions. -/
theorem tendsto_value_of_finite_maximizer
    {ι β X : Type*} [Finite ι] [TopologicalSpace X] {l : Filter β}
    {score : β → ι → ℝ} {limitScore : ι → ℝ} {pick : β → ι}
    {value : β → ι → X} {limitValue : ι → X} {x : X}
    (hscore : ∀ i, Tendsto (fun n => score n i) l (nhds (limitScore i)))
    (hpick : ∀ᶠ n in l, ∀ i, score n i ≤ score n (pick n))
    (hvalue : ∀ i, Tendsto (fun n => value n i) l (nhds (limitValue i)))
    (hactive : ∀ i, (∀ j, limitScore j ≤ limitScore i) → limitValue i = x) :
    Tendsto (fun n => value n (pick n)) l (nhds x) := by
  rw [Filter.tendsto_def]
  intro U hU
  have hlim := eventually_limiting_maximizer hscore hpick
  have hi : ∀ i, ∀ᶠ n in l,
      (∀ j, limitScore j ≤ limitScore i) → value n i ∈ U := by
    intro i
    by_cases hmax : ∀ j, limitScore j ≤ limitScore i
    · have ht : Tendsto (fun n => value n i) l (nhds x) := by
        simpa only [hactive i hmax] using hvalue i
      exact (ht.eventually hU).mono fun n hn _ => hn
    · exact Eventually.of_forall fun n hn => (hmax hn).elim
  have hall : ∀ᶠ n in l, ∀ i,
      (∀ j, limitScore j ≤ limitScore i) → value n i ∈ U :=
    eventually_all.mpr hi
  filter_upwards [hlim, hall] with n hn hval
  exact hval (pick n) hn

/-- Endpoint convergence of the active slopes of affine maxima. The source point
is fixed; a.e. applications remove the finite union of limiting tie hyperplanes. -/
theorem tendsto_affine_active_slope
    {ι β V : Type*} [Finite ι] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {l : Filter β} {site : β → ι → V} {limitSite : ι → V}
    {offset : β → ι → ℝ} {limitOffset : ι → ℝ} {pick : β → ι}
    {point target : V}
    (hsite : ∀ i, Tendsto (fun n => site n i) l (nhds (limitSite i)))
    (hoffset : ∀ i, Tendsto (fun n => offset n i) l (nhds (limitOffset i)))
    (hpick : ∀ᶠ n in l, ∀ i,
      inner ℝ point (site n i) + offset n i ≤
        inner ℝ point (site n (pick n)) + offset n (pick n))
    (hactive : ∀ i, (∀ j,
      inner ℝ point (limitSite j) + limitOffset j ≤
        inner ℝ point (limitSite i) + limitOffset i) → limitSite i = target) :
    Tendsto (fun n => site n (pick n)) l (nhds target) := by
  apply tendsto_value_of_finite_maximizer (score := fun n i =>
    inner ℝ point (site n i) + offset n i)
    (limitScore := fun i => inner ℝ point (limitSite i) + limitOffset i)
    _ hpick hsite hactive
  intro i
  exact (tendsto_const_nhds.inner (hsite i)).add (hoffset i)

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped Topology
open scoped BoundedContinuousFunction
open scoped BigOperators ENNReal

namespace Problem358

/-- The same endpoint statement for maps specified by active-slope certificates.
No convergence of active indices, and no injectivity of limiting sites, is required. -/
theorem ae_tendsto_affine_maximizer_maps
    {d : ℕ} {ι : Type*} [Fintype ι]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {y : ℕ → ι → E d} {y₀ : ι → E d}
    {c : ℕ → ι → ℝ} {c₀ : ι → ℝ}
    {T : ℕ → E d → E d} {T₀ : E d → E d}
    (hy : ∀ i, Tendsto (fun n => y n i) atTop (𝓝 (y₀ i)))
    (hc : ∀ i, Tendsto (fun n => c n i) atTop (𝓝 (c₀ i)))
    (hT : ∀ n, ∀ᵐ x ∂ρ, ∃ i, T n x = y n i ∧
      ∀ j, inner ℝ x (y n j) + c n j ≤ inner ℝ x (y n i) + c n i)
    (hT₀ : ∀ᵐ x ∂ρ, ∃ i, T₀ x = y₀ i ∧
      ∀ j, inner ℝ x (y₀ j) + c₀ j ≤ inner ℝ x (y₀ i) + c₀ i) :
    ∀ᵐ x ∂ρ, Tendsto (fun n => T n x) atTop (𝓝 (T₀ x)) := by
  classical
  have hAll : ∀ᵐ x ∂ρ, ∀ n, ∃ i, T n x = y n i ∧
      ∀ j, inner ℝ x (y n j) + c n j ≤ inner ℝ x (y n i) + c n i :=
    ae_all_iff.mpr hT
  filter_upwards [hρ.ae_le (ae_affine_tie_implies_slopes_eq volume y₀ c₀),
    hAll, hT₀] with x hx hxn hx₀
  choose pick hpick hmax using hxn
  obtain ⟨i₀, hi₀, hmax₀⟩ := hx₀
  have ht := tendsto_affine_active_slope hy hc
    (Eventually.of_forall hmax)
    (target := y₀ i₀) (fun i hi => hx i i₀ (le_antisymm (hmax₀ i) (hi i₀)))
  simpa only [← hpick, ← hi₀] using ht

/-- Coefficient convergence also gives L² convergence for any finite absolutely
continuous source. A common compact slope range follows from convergence of the
finite family; boundedness of the source itself is not needed. -/
theorem tendsto_mapL2Dist_affine_maximizer_maps
    {d : ℕ} {ι : Type*} [Fintype ι]
    {ρ : Measure (E d)} [IsFiniteMeasure ρ] (hρ : ρ ≪ volume)
    {y : ℕ → ι → E d} {y₀ : ι → E d}
    {c : ℕ → ι → ℝ} {c₀ : ι → ℝ}
    {T : ℕ → E d → E d} {T₀ : E d → E d}
    (hy : ∀ i, Tendsto (fun n => y n i) atTop (𝓝 (y₀ i)))
    (hc : ∀ i, Tendsto (fun n => c n i) atTop (𝓝 (c₀ i)))
    (hTm : ∀ n, Measurable (T n)) (hT₀m : Measurable T₀)
    (hT : ∀ n, ∀ᵐ x ∂ρ, ∃ i, T n x = y n i ∧
      ∀ j, inner ℝ x (y n j) + c n j ≤ inner ℝ x (y n i) + c n i)
    (hT₀ : ∀ᵐ x ∂ρ, ∃ i, T₀ x = y₀ i ∧
      ∀ j, inner ℝ x (y₀ j) + c₀ j ≤ inner ℝ x (y₀ i) + c₀ i) :
    Tendsto (fun n => mapL2Dist ρ (T n) T₀) atTop (𝓝 0) := by
  have hyPi : Tendsto y atTop (𝓝 y₀) := tendsto_pi_nhds.mpr hy
  obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto y hyPi).exists_norm_le
  apply CompactIntegrability.tendsto_mapL2Dist_of_ae_tendsto hTm hT₀m
    (isCompact_closedBall (0 : E d) (max R 0)) _
    (ae_tendsto_affine_maximizer_maps hρ hy hc hT hT₀)
  intro n
  filter_upwards [hT n] with x hx
  obtain ⟨i, hi, _⟩ := hx
  rw [hi, Metric.mem_closedBall, dist_zero_right]
  exact (norm_le_pi_norm (y n) i).trans ((hR _ ⟨n, rfl⟩).trans (le_max_left _ _))

/-- Identification of an endpoint law carried by a fixed finite index measure.
Different limiting indices may have the same site; their masses are automatically merged
by the pushforward, so no endpoint injectivity is needed. -/
theorem map_eq_of_finite_site_law_limit
    {d : ℕ} {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    {ρ : Measure (E d)} [IsFiniteMeasure ρ]
    {η : Measure ι} [IsFiniteMeasure η]
    {y : ℕ → ι → E d} {y₀ : ι → E d}
    {T : ℕ → E d → E d} {T₀ : E d → E d}
    (hy : ∀ i, Tendsto (fun n => y n i) atTop (𝓝 (y₀ i)))
    (hTm : ∀ n, Measurable (T n)) (hT₀m : Measurable T₀)
    (hlim : ∀ᵐ x ∂ρ, Tendsto (fun n => T n x) atTop (𝓝 (T₀ x)))
    (hpush : ∀ n, Measure.map (T n) ρ = Measure.map (y n) η) :
    Measure.map T₀ ρ = Measure.map y₀ η := by
  apply map_eq_of_ae_tendsto_and_test_tendsto hTm hT₀m hlim
  intro f
  have heq (n : ℕ) : (∫ x, f (T n x) ∂ρ) = ∫ i, f (y n i) ∂η := by
    rw [← integral_map (hTm n).aemeasurable f.continuous.measurable.aestronglyMeasurable,
      hpush n, integral_map (measurable_of_countable (y n)).aemeasurable
        f.continuous.measurable.aestronglyMeasurable]
  have htarget : (∫ z, f z ∂Measure.map y₀ η) = ∫ i, f (y₀ i) ∂η :=
    integral_map (measurable_of_countable y₀).aemeasurable
      f.continuous.measurable.aestronglyMeasurable
  simp_rw [heq, htarget]
  exact tendsto_integral_boundedContinuous_comp_ae
    (fun n => measurable_of_countable (y n)) (ae_of_all _ hy) f

/-- Explicit atomic form of endpoint-law identification. Repeated endpoint sites are
allowed, so this applies at both ends of an optimal finite atomic motion. -/
theorem map_eq_atomic_of_finite_site_limit
    {d : ℕ} {ι : Type*} [Fintype ι]
    {ρ : Measure (E d)} [IsFiniteMeasure ρ]
    {y : ℕ → ι → E d} {y₀ : ι → E d}
    {T : ℕ → E d → E d} {T₀ : E d → E d}
    (w : ι → ℝ≥0∞) (hw : ∑ i, w i = 1)
    (hy : ∀ i, Tendsto (fun n => y n i) atTop (𝓝 (y₀ i)))
    (hTm : ∀ n, Measurable (T n)) (hT₀m : Measurable T₀)
    (hlim : ∀ᵐ x ∂ρ, Tendsto (fun n => T n x) atTop (𝓝 (T₀ x)))
    (hpush : ∀ n, Measure.map (T n) ρ = ∑ i, w i • Measure.dirac (y n i)) :
    Measure.map T₀ ρ = ∑ i, w i • Measure.dirac (y₀ i) := by
  classical
  let : MeasurableSpace ι := ⊤
  let η : Measure ι := ∑ i, w i • Measure.dirac i
  have : IsProbabilityMeasure η := by
    constructor
    simpa [η] using hw
  have hmap (z : ι → E d) : Measure.map z η = ∑ i, w i • Measure.dirac (z i) := by
    dsimp [η]
    rw [Measure.map_finset_sum' (measurable_of_countable z).aemeasurable]
    simp only [Measure.map_smul,
      Measure.map_dirac]
  rw [← hmap y₀]
  apply map_eq_of_finite_site_law_limit hy hTm hT₀m hlim
  intro n
  rw [hmap, hpush]

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ENNReal NNReal

namespace Problem358

/-- A finite-affine selected map is plan-uniquely optimal on a uniform convex source
even when the slopes are repeated. The supporting-potential certificate avoids any
choice of a merged presentation. -/
theorem isUniqueQuadraticOptimalMap_uniform_of_finite_affine_repeated
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    {K : Set (E d)} [IsFiniteMeasure (uniformMeasure K)]
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) {T : E d → E d} (hT : Measurable T)
    (hactive : ∀ᵐ x ∂uniformMeasure K, ∃ i, T x = y i ∧
      ∀ j, inner ℝ x (y j) + c j ≤ inner ℝ x (y i) + c i) :
    IsUniqueQuadraticOptimalMap (uniformMeasure K)
      (Measure.map T (uniformMeasure K)) T := by
  have hY : IsCompact (Set.range y) := (Set.finite_range y).isCompact
  obtain ⟨R, hR⟩ := hY.isBounded.exists_norm_le
  let L : ℝ≥0 := ⟨max R 0, le_max_right _ _⟩
  have hL (i : ι) : ‖y i‖ ≤ L :=
    (hR _ ⟨i, rfl⟩).trans (le_max_left _ _)
  have hsupport : IsSupported (Measure.map T (uniformMeasure K)) (Set.range y) := by
    apply ae_iff.mp
    apply (ae_map_iff hT.aemeasurable hY.measurableSet).mpr
    filter_upwards [hactive] with x hx
    obtain ⟨i, hi, _⟩ := hx
    exact ⟨i, hi.symm⟩
  apply isUniqueQuadraticOptimalMap_uniform_of_supporting_potential
    hK hne hconv hY hsupport
    (MaxPotential.lipschitzWith_potential y c L hL).lipschitzOnWith hT rfl
  filter_upwards [hactive] with x hx
  obtain ⟨i, hi, hmax⟩ := hx
  intro z _
  rw [hi]
  exact MaxPotential.supporting_inequality y c x z i hmax

/-- Coefficient limits at an endpoint of a fixed-mass finite affine motion produce
an actual measurable endpoint map, its exact atomic law, plan-unique optimality,
and both almost-everywhere and L² convergence. Endpoint slopes may coincide. -/
theorem exists_unique_optimal_finite_affine_endpoint
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hinterior : (interior K).Nonempty)
    {y : ℕ → ι → E d} {y₀ : ι → E d}
    {c : ℕ → ι → ℝ} {c₀ : ι → ℝ} {T : ℕ → E d → E d}
    (w : ι → ℝ≥0∞) (hw : ∑ i, w i = 1)
    (hy : ∀ i, Tendsto (fun n => y n i) atTop (𝓝 (y₀ i)))
    (hc : ∀ i, Tendsto (fun n => c n i) atTop (𝓝 (c₀ i)))
    (hTm : ∀ n, Measurable (T n))
    (hT : ∀ n, ∀ᵐ x ∂uniformMeasure K, ∃ i, T n x = y n i ∧
      ∀ j, inner ℝ x (y n j) + c n j ≤ inner ℝ x (y n i) + c n i)
    (hpush : ∀ n, Measure.map (T n) (uniformMeasure K) =
      ∑ i, w i • Measure.dirac (y n i)) :
    ∃ T₀ : E d → E d,
      (∀ x, ∃ i, T₀ x = y₀ i ∧
        ∀ j, inner ℝ x (y₀ j) + c₀ j ≤ inner ℝ x (y₀ i) + c₀ i) ∧
      IsUniqueQuadraticOptimalMap (uniformMeasure K)
        (∑ i, w i • Measure.dirac (y₀ i)) T₀ ∧
      (∀ᵐ x ∂uniformMeasure K, Tendsto (fun n => T n x) atTop (𝓝 (T₀ x))) ∧
      Tendsto (fun n => mapL2Dist (uniformMeasure K) (T n) T₀) atTop (𝓝 0) := by
  let : IsProbabilityMeasure (uniformMeasure K) := UniformSource.probability hK hinterior
  obtain ⟨T₀, hT₀m, hselected⟩ := exists_measurable_affine_maximizer y₀ c₀
  have hactive : ∀ x, ∃ i, T₀ x = y₀ i ∧
      ∀ j, inner ℝ x (y₀ j) + c₀ j ≤ inner ℝ x (y₀ i) + c₀ i := by
    intro x
    simpa only [real_inner_comm] using hselected x
  have hac : uniformMeasure K ≪ (volume : Measure (E d)) :=
    Measure.absolutelyContinuous_restrict.smul_left _
  have hlim := ae_tendsto_affine_maximizer_maps hac hy hc hT (ae_of_all _ hactive)
  have hlaw := map_eq_atomic_of_finite_site_limit w hw hy hTm hT₀m hlim hpush
  have hopt := isUniqueQuadraticOptimalMap_uniform_of_finite_affine_repeated
    hK (hinterior.mono interior_subset) hconv y₀ c₀ hT₀m (ae_of_all _ hactive)
  rw [hlaw] at hopt
  exact ⟨T₀, hactive, hopt, hlim,
    tendsto_mapL2Dist_affine_maximizer_maps hac hy hc hTm hT₀m hT (ae_of_all _ hactive)⟩

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ENNReal

namespace Problem358

/-- A boundary value of a continuous finite-affine family has the prescribed
atomic law and a plan-uniquely optimal selected map. Only the coefficient limits
within the parameter set are needed, and limiting sites may coincide. -/
theorem exists_unique_optimal_finite_affine_boundary
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hinterior : (interior K).Nonempty)
    {S : Set ℝ} {t₀ : ℝ} (ht₀ : t₀ ∈ closure S)
    {y : ℝ → ι → E d} {c : ℝ → ι → ℝ}
    {T : ℝ → E d → E d}
    (w : ι → ℝ≥0∞) (hw : ∑ i, w i = 1)
    (hy : ∀ i, ContinuousWithinAt (fun t => y t i) S t₀)
    (hc : ∀ i, ContinuousWithinAt (fun t => c t i) S t₀)
    (hTm : ∀ t ∈ S, Measurable (T t))
    (hT : ∀ t ∈ S, ∀ᵐ x ∂uniformMeasure K, ∃ i, T t x = y t i ∧
      ∀ j, inner ℝ x (y t j) + c t j ≤ inner ℝ x (y t i) + c t i)
    (hpush : ∀ t ∈ S, Measure.map (T t) (uniformMeasure K) =
      ∑ i, w i • Measure.dirac (y t i)) :
    ∃ T₀ : E d → E d,
      (∀ x, ∃ i, T₀ x = y t₀ i ∧
        ∀ j, inner ℝ x (y t₀ j) + c t₀ j ≤ inner ℝ x (y t₀ i) + c t₀ i) ∧
      IsUniqueQuadraticOptimalMap (uniformMeasure K)
        (∑ i, w i • Measure.dirac (y t₀ i)) T₀ := by
  obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.mp ht₀
  have hwithin : Tendsto s atTop (𝓝[S] t₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hs⟩
  obtain ⟨T₀, hactive, hopt, _, _⟩ :=
    exists_unique_optimal_finite_affine_endpoint hK hconv hinterior w hw
      (fun i => (hy i).tendsto.comp hwithin)
      (fun i => (hc i).tendsto.comp hwithin)
      (fun n => hTm (s n) (hs n))
      (fun n => hT (s n) (hs n))
      (fun n => hpush (s n) (hs n))
  exact ⟨T₀, hactive, hopt⟩

/-- Continuous coefficients on a closed time interval and the fixed-mass law
on its interior produce both exact endpoint maps. No injectivity or cell-mass
condition is required at either endpoint. -/
theorem exists_unique_optimal_finite_affine_path_endpoints
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hinterior : (interior K).Nonempty)
    {a b : ℝ} (hab : a < b)
    {y : ℝ → ι → E d} {c : ℝ → ι → ℝ}
    {T : ℝ → E d → E d}
    (w : ι → ℝ≥0∞) (hw : ∑ i, w i = 1)
    (hy : ∀ i, ContinuousOn (fun t => y t i) (Set.Icc a b))
    (hc : ∀ i, ContinuousOn (fun t => c t i) (Set.Icc a b))
    (hTm : ∀ t ∈ Set.Ioo a b, Measurable (T t))
    (hT : ∀ t ∈ Set.Ioo a b, ∀ᵐ x ∂uniformMeasure K, ∃ i,
      T t x = y t i ∧ ∀ j,
        inner ℝ x (y t j) + c t j ≤ inner ℝ x (y t i) + c t i)
    (hpush : ∀ t ∈ Set.Ioo a b, Measure.map (T t) (uniformMeasure K) =
      ∑ i, w i • Measure.dirac (y t i)) :
    ∃ Ta Tb : E d → E d,
      (∀ x, ∃ i, Ta x = y a i ∧
        ∀ j, inner ℝ x (y a j) + c a j ≤ inner ℝ x (y a i) + c a i) ∧
      (∀ x, ∃ i, Tb x = y b i ∧
        ∀ j, inner ℝ x (y b j) + c b j ≤ inner ℝ x (y b i) + c b i) ∧
      IsUniqueQuadraticOptimalMap (uniformMeasure K)
        (∑ i, w i • Measure.dirac (y a i)) Ta ∧
      IsUniqueQuadraticOptimalMap (uniformMeasure K)
        (∑ i, w i • Measure.dirac (y b i)) Tb := by
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Set.Icc a b := ⟨hab.le, le_rfl⟩
  have hclosure : closure (Set.Ioo a b) = Set.Icc a b := closure_Ioo hab.ne
  obtain ⟨Ta, hTa, hoptA⟩ :=
    exists_unique_optimal_finite_affine_boundary hK hconv hinterior
      (hclosure.symm ▸ ha) w hw
      (fun i => (hy i a ha).mono Set.Ioo_subset_Icc_self)
      (fun i => (hc i a ha).mono Set.Ioo_subset_Icc_self) hTm hT hpush
  obtain ⟨Tb, hTb, hoptB⟩ :=
    exists_unique_optimal_finite_affine_boundary hK hconv hinterior
      (hclosure.symm ▸ hb) w hw
      (fun i => (hy i b hb).mono Set.Ioo_subset_Icc_self)
      (fun i => (hc i b hb).mono Set.Ioo_subset_Icc_self) hTm hT hpush
  exact ⟨Ta, Tb, hTa, hTb, hoptA, hoptB⟩

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_NormalizedPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped NNReal BigOperators RealInnerProductSpace

namespace Problem358

/-- The bounded-energy, normalized interior intercept path itself supplies
continuous endpoint potentials with the uniform L² estimate.  In particular,
no limits or regularity of the original coefficients at times zero and one
are assumptions of this theorem. -/
theorem exists_normalized_finite_affine_endpoint_potentials
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (K : Set (E d)) [IsFiniteMeasure (uniformMeasure K)]
    (y v : ι → ℝ → E d) (c r : ι → ℝ → ℝ)
    (active : ℝ × E d → ι) (m : ι → ℝ)
    {w κ : ℝ} {R : ℝ≥0} (hw : 0 ≤ w) (hκ : 0 ≤ κ)
    (hxR : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hpositive : ∀ i, 0 < m i)
    (hy : ∀ i, Continuous (y i))
    (hv : ∀ i, ContinuousOn (v i) (Ioo 0 1))
    (hr : ∀ i, ContinuousOn (r i) (Ioo 0 1))
    (hactiveMeas : Measurable active)
    (hdy : ∀ i q, q ∈ Ioo 0 1 → HasDerivAt (y i) (v i q) q)
    (hdc : ∀ i q, q ∈ Ioo 0 1 → HasDerivAt (c i) (r i q) q)
    (hinj : ∀ q ∈ Ioo 0 1, Function.Injective (fun i => y i q))
    (hactive : ∀ q ∈ Ioo 0 1, ∀ x j,
      ⟪x, y j q⟫ + c j q ≤
        ⟪x, y (active (q, x)) q⟫ + c (active (q, x)) q)
    (hm : ∀ q ∈ Ioo 0 1, ∀ i,
      (uniformMeasure K).real {x | active (q, x) = i} = m i)
    (hnormal : ∀ q ∈ Ioo 0 1, (∑ i, m i * c i q) = 0)
    (hvEnergy : ∀ q ∈ Ioo 0 1, (∑ i, m i * ‖v i q‖ ^ 2) ≤ w ^ 2)
    (hrEnergy : ∀ q ∈ Ioo 0 1,
      (∑ i, m i * r i q ^ 2) ≤ κ * (R : ℝ) ^ 2 * w ^ 2) :
    ∃ cbar : ι → ℝ → ℝ,
      (∀ i, Continuous (cbar i)) ∧
      (∀ i, EqOn (c i) (cbar i) (Ioo 0 1)) ∧
      (∀ i q, q ∈ Ioo 0 1 → HasDerivAt (cbar i) (r i q) q) ∧
      (∀ q ∈ Icc 0 1, (∑ i, m i * cbar i q) = 0) ∧
      Real.sqrt (∫ x,
        (FiniteAffine.potential (fun i => y i 1) (fun i => cbar i 1) x -
         FiniteAffine.potential (fun i => y i 0) (fun i => cbar i 0) x) ^ 2
        ∂uniformMeasure K) ≤ Real.sqrt (2 * (1 + κ)) * R * w ∧
      (∫ x,
        (FiniteAffine.potential (fun i => y i 1) (fun i => cbar i 1) x -
         FiniteAffine.potential (fun i => y i 0) (fun i => cbar i 0) x) ^ 2
        ∂uniformMeasure K) ≤ 2 * (1 + κ) * (R : ℝ) ^ 2 * w ^ 2 := by
  obtain ⟨cbar, hLip, hEq, hdbar, hnormbar, _⟩ :=
    InterceptEndpointExtension.exists_normalized_lipschitz_extension
      m c r (by norm_num : (0 : ℝ) < 1) hpositive hdc hrEnergy hnormal
  have hcont (i : ι) : Continuous (cbar i) := (hLip i).continuous
  have hactivebar : ∀ q ∈ Ioo 0 1, ∀ x j,
      ⟪x, y j q⟫ + cbar j q ≤
        ⟪x, y (active (q, x)) q⟫ + cbar (active (q, x)) q := by
    intro q hq x j
    rw [← hEq j hq, ← hEq (active (q, x)) hq]
    exact hactive q hq x j
  have hbound := finite_affine_C1_path_endpoint_L2_bound K y v cbar r active m
    hw hκ hxR hy hcont hv hr hactiveMeas hdy hdbar hinj hactivebar hm hvEnergy hrEnergy
  refine ⟨cbar, hcont, hEq, hdbar, hnormbar, hbound, ?_⟩
  have hsquare : (Real.sqrt (2 * (1 + κ)) * R * w) ^ 2 =
      2 * (1 + κ) * (R : ℝ) ^ 2 * w ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  simpa only [hsquare] using (Real.sqrt_le_iff.mp hbound).2

end Problem358

end

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators RealInnerProductSpace

namespace Problem358

/-- A normalized positive-mass affine motion gives the actual endpoint
supporting potentials and their exact atomic laws, together with the uniform
potential estimate. Neither separation nor intercept limits at the endpoints
are assumptions. -/
theorem exists_supporting_pair_of_normalized_affine_path
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {K : Set (E d)} (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hKint : (interior K).Nonempty)
    (y v : ι → ℝ → E d) (c r : ι → ℝ → ℝ)
    (active : ℝ × E d → ι) (m : ι → ℝ)
    {w κ : ℝ} {R L : ℝ≥0} (hw : 0 ≤ w) (hκ : 0 ≤ κ)
    (hxR : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hpositive : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (hy : ∀ i, Continuous (y i))
    (hv : ∀ i, ContinuousOn (v i) (Ioo 0 1))
    (hr : ∀ i, ContinuousOn (r i) (Ioo 0 1))
    (hactiveMeas : Measurable active)
    (hdy : ∀ i q, q ∈ Ioo 0 1 → HasDerivAt (y i) (v i q) q)
    (hdc : ∀ i q, q ∈ Ioo 0 1 → HasDerivAt (c i) (r i q) q)
    (hinj : ∀ q ∈ Ioo 0 1, Function.Injective (fun i => y i q))
    (hactive : ∀ q ∈ Ioo 0 1, ∀ x j,
      ⟪x, y j q⟫ + c j q ≤
        ⟪x, y (active (q, x)) q⟫ + c (active (q, x)) q)
    (hm : ∀ q ∈ Ioo 0 1, ∀ i,
      (uniformMeasure K).real {x | active (q, x) = i} = m i)
    (hnormal : ∀ q ∈ Ioo 0 1, (∑ i, m i * c i q) = 0)
    (hvEnergy : ∀ q ∈ Ioo 0 1, (∑ i, m i * ‖v i q‖ ^ 2) ≤ w ^ 2)
    (hrEnergy : ∀ q ∈ Ioo 0 1,
      (∑ i, m i * r i q ^ 2) ≤ κ * (R : ℝ) ^ 2 * w ^ 2)
    (hy0 : ∀ i, ‖y i 0‖ ≤ L) (hy1 : ∀ i, ‖y i 1‖ ≤ L) :
    ∃ (u₀ u₁ : E d → ℝ) (T₀ T₁ : E d → E d),
      SupportingMapInterpolation.Supports u₀ T₀ ∧
      SupportingMapInterpolation.Supports u₁ T₁ ∧
      Measurable T₀ ∧ Measurable T₁ ∧
      (∀ x, ‖T₀ x‖ ≤ L) ∧ (∀ x, ‖T₁ x‖ ≤ L) ∧
      Measure.map T₀ (uniformMeasure K) =
        ∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i 0) ∧
      Measure.map T₁ (uniformMeasure K) =
        ∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i 1) ∧
      (∫ x, (u₀ x - u₁ x) ^ 2 ∂uniformMeasure K) ≤
        2 * (1 + κ) * (R : ℝ) ^ 2 * w ^ 2 := by
  let : IsProbabilityMeasure (uniformMeasure K) := UniformSource.probability hK hKint
  obtain ⟨cbar, hcbar, hEq, _, _, _, hbound⟩ :=
    exists_normalized_finite_affine_endpoint_potentials K y v c r active m
      hw hκ hxR hpositive hy hv hr hactiveMeas hdy hdc hinj hactive hm
      hnormal hvEnergy hrEnergy
  let T : ℝ → E d → E d := fun q x => y (active (q, x)) q
  have hTm (q : ℝ) : Measurable (T q) :=
    (measurable_of_countable (fun i => y i q)).comp
      (hactiveMeas.comp (measurable_const.prodMk measurable_id))
  have hweights : (∑ i, ENNReal.ofReal (m i)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (hpositive i).le), hsum]
    exact ENNReal.ofReal_one
  have hactivebar : ∀ q ∈ Ioo 0 1, ∀ x j,
      ⟪x, y j q⟫ + cbar j q ≤
        ⟪x, y (active (q, x)) q⟫ + cbar (active (q, x)) q := by
    intro q hq x j
    rw [← hEq j hq, ← hEq (active (q, x)) hq]
    exact hactive q hq x j
  have hpush (q : ℝ) (hq : q ∈ Ioo 0 1) :
      Measure.map (T q) (uniformMeasure K) =
        ∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i q) := by
    apply map_finite_selector_of_masses (uniformMeasure K)
      (fun x => active (q, x))
      (hactiveMeas.comp (measurable_const.prodMk measurable_id))
      (fun i => y i q) (fun i => ENNReal.ofReal (m i))
    intro i
    rw [← hm q hq i]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  obtain ⟨T₀, T₁, hT₀active, hT₁active, hT₀opt, hT₁opt⟩ :=
    exists_unique_optimal_finite_affine_path_endpoints hK hKconv hKint
      (by norm_num : (0 : ℝ) < 1) (fun i => ENNReal.ofReal (m i)) hweights
      (fun i => (hy i).continuousOn) (fun i => (hcbar i).continuousOn)
      (fun q _ => hTm q)
      (fun q hq => Filter.Eventually.of_forall fun x =>
        ⟨active (q, x), rfl, hactivebar q hq x⟩) hpush
  refine ⟨MaxPotential.potential (fun i => y i 0) (fun i => cbar i 0),
    MaxPotential.potential (fun i => y i 1) (fun i => cbar i 1), T₀, T₁,
    ?_, ?_, hT₀opt.1.1, hT₁opt.1.1, ?_, ?_, hT₀opt.1.2.1, hT₁opt.1.2.1, ?_⟩
  · intro x z
    obtain ⟨i, hi, hmax⟩ := hT₀active x
    rw [hi]
    exact MaxPotential.supporting_inequality _ _ x z i hmax
  · intro x z
    obtain ⟨i, hi, hmax⟩ := hT₁active x
    rw [hi]
    exact MaxPotential.supporting_inequality _ _ x z i hmax
  · intro x
    obtain ⟨i, hi, _⟩ := hT₀active x
    rw [hi]
    exact hy0 i
  · intro x
    obtain ⟨i, hi, _⟩ := hT₁active x
    rw [hi]
    exact hy1 i
  · convert hbound using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext x
    dsimp only [MaxPotential.potential, FiniteAffine.potential]
    ring

end Problem358

namespace Problem358

/-- The geometric closed-cell mass equations suffice for the endpoint potential
pair construction. A common measurable maximizing selector and all its mass
identities are derived, not supplied as additional path assumptions. -/
theorem exists_supporting_pair_of_closedCell_path
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {K : Set (E d)} (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hKint : (interior K).Nonempty)
    (y v : ι → ℝ → E d) (c r : ι → ℝ → ℝ) (m : ι → ℝ)
    {w κ : ℝ} {R L : ℝ≥0} (hw : 0 ≤ w) (hκ : 0 ≤ κ)
    (hxR : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hpositive : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (hy : ∀ i, Continuous (y i)) (hc : ∀ i, Measurable (c i))
    (hv : ∀ i, ContinuousOn (v i) (Ioo 0 1))
    (hr : ∀ i, ContinuousOn (r i) (Ioo 0 1))
    (hdy : ∀ i q, q ∈ Ioo 0 1 → HasDerivAt (y i) (v i q) q)
    (hdc : ∀ i q, q ∈ Ioo 0 1 → HasDerivAt (c i) (r i q) q)
    (hinj : ∀ q ∈ Ioo 0 1, Function.Injective (fun i => y i q))
    (hm : ∀ q ∈ Ioo 0 1, ∀ i,
      (uniformMeasure K).real
        (CellGeometry.closedCell K (fun j => y j q) (fun j => c j q) i) = m i)
    (hnormal : ∀ q ∈ Ioo 0 1, (∑ i, m i * c i q) = 0)
    (hvEnergy : ∀ q ∈ Ioo 0 1, (∑ i, m i * ‖v i q‖ ^ 2) ≤ w ^ 2)
    (hrEnergy : ∀ q ∈ Ioo 0 1,
      (∑ i, m i * r i q ^ 2) ≤ κ * (R : ℝ) ^ 2 * w ^ 2)
    (hy0 : ∀ i, ‖y i 0‖ ≤ L) (hy1 : ∀ i, ‖y i 1‖ ≤ L) :
    ∃ (u₀ u₁ : E d → ℝ) (T₀ T₁ : E d → E d),
      SupportingMapInterpolation.Supports u₀ T₀ ∧
      SupportingMapInterpolation.Supports u₁ T₁ ∧
      Measurable T₀ ∧ Measurable T₁ ∧
      (∀ x, ‖T₀ x‖ ≤ L) ∧ (∀ x, ‖T₁ x‖ ≤ L) ∧
      Measure.map T₀ (uniformMeasure K) =
        ∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i 0) ∧
      Measure.map T₁ (uniformMeasure K) =
        ∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i 1) ∧
      (∫ x, (u₀ x - u₁ x) ^ 2 ∂uniformMeasure K) ≤
        2 * (1 + κ) * (R : ℝ) ^ 2 * w ^ 2 := by
  obtain ⟨active, hactiveMeas, hactive, hmass⟩ :=
    CellGeometry.exists_joint_measurable_selector_prescribed_masses hK.measurableSet
      (fun q i => y i q) (fun q i => c i q) (fun _ i => m i) (Ioo 0 1)
      (fun i => (hy i).measurable) hc hinj hm
  exact exists_supporting_pair_of_normalized_affine_path hK hKconv hKint
    y v c r active m hw hκ hxR hpositive hsum hy hv hr hactiveMeas hdy hdc
    hinj (fun q _ => hactive q) hmass hnormal hvEnergy hrEnergy hy0 hy1

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_ClosedPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators RealInnerProductSpace

namespace Problem358

/-- Complete stability from the genuine geometric intercept-path assertion.
All endpoint construction, finite optimal coupling, potential interpolation,
optimal-map uniqueness and finite-to-general approximation are discharged.
The remaining premise is precisely a normalized positive closed-cell path
with its weighted derivative-energy bound. -/
theorem one_third_stability_of_closedCell_intercept_paths
    {d : ℕ} {K Y : Set (E d)}
    (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hY : IsCompact Y) (hYne : Y.Nonempty)
    (R L : ℝ≥0) (hxR : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hYL : ∀ z ∈ Y, ‖z‖ ≤ L) {κ : ℝ} (hκ : 0 ≤ κ)
    (hpaths : ∀ (n : ℕ), 0 < n →
      ∀ (m : Fin n → ℝ) (y z : Fin n → E d),
      (∀ i, 0 < m i) → (∑ i, m i) = 1 →
      (∀ i, ‖y i‖ ≤ L) → (∀ i, ‖z i‖ ≤ L) →
      (∀ t : ℝ, 0 < t → t < 1 →
        Function.Injective (fun i => (1-t) • y i + t • z i)) →
      ∃ c r : Fin n → ℝ → ℝ,
        (∀ i, Measurable (c i)) ∧
        (∀ i, ContinuousOn (r i) (Ioo 0 1)) ∧
        (∀ i t, t ∈ Ioo 0 1 → HasDerivAt (c i) (r i t) t) ∧
        (∀ t ∈ Ioo 0 1, ∀ i,
          (uniformMeasure K).real (CellGeometry.closedCell K
            (fun j => (1-t) • y j + t • z j) (fun j => c j t) i) = m i) ∧
        (∀ t ∈ Ioo 0 1, (∑ i, m i * c i t) = 0) ∧
        ∀ t ∈ Ioo 0 1, (∑ i, m i * r i t ^ 2) ≤
          κ * (R : ℝ) ^ 2 * ∑ i, m i * ‖y i - z i‖ ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ ν : Measure (E d)),
      IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      IsSupported μ Y → IsSupported ν Y →
      ∃ Tμ Tν : E d → E d,
        IsUniqueQuadraticOptimalMap (uniformMeasure K) μ Tμ ∧
        IsUniqueQuadraticOptimalMap (uniformMeasure K) ν Tν ∧
        mapL2Dist (uniformMeasure K) Tμ Tν ≤
          C * Real.rpow (wasserstein2 μ ν) (1 / 3 : ℝ) := by
  apply one_third_stability_of_atomic_potential_estimate hK hKconv hKint hY hYne
    L hYL (Real.sqrt (2 * (1 + κ)) * R)
  intro n hn m y z hm hsum hyL hzL hinj
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨c, r, hc, hr, hdc, hmass, hnormal, henergy⟩ :=
    hpaths n hn m y z hm hsum hyL hzL hinj
  let e : ℝ := ∑ i, m i * ‖y i - z i‖ ^ 2
  have he : 0 ≤ e := Finset.sum_nonneg fun i _ => mul_nonneg (hm i).le (sq_nonneg _)
  have hsqrt : Real.sqrt e ^ 2 = e := Real.sq_sqrt he
  let path : Fin n → ℝ → E d := fun i t => (1-t) • y i + t • z i
  let velocity : Fin n → ℝ → E d := fun i _ => z i - y i
  have hpath : ∀ i, Continuous (path i) := by intro i; dsimp [path]; fun_prop
  have hdpath : ∀ i t, HasDerivAt (path i) (velocity i t) t := by
    intro i t
    have heq : path i = fun q : ℝ => y i + q • (z i - y i) := by
      funext q
      dsimp [path]
      module
    rw [heq]
    simpa only [velocity, one_smul] using!
      ((hasDerivAt_id t).smul_const (z i - y i)).const_add (y i)
  have hvEnergy : ∀ t ∈ Ioo (0 : ℝ) 1,
      (∑ i, m i * ‖velocity i t‖ ^ 2) ≤ Real.sqrt e ^ 2 := by
    intro t _
    rw [hsqrt]
    exact le_of_eq (Finset.sum_congr rfl fun i _ => by simp only [velocity, norm_sub_rev])
  obtain ⟨u₀, u₁, T₀, T₁, hu₀, hu₁, hT₀, hT₁, hT₀L, hT₁L, hμ, hν, hb⟩ :=
    exists_supporting_pair_of_closedCell_path hK hKconv hKint path velocity c r m
      (Real.sqrt_nonneg e) hκ hxR hm hsum hpath hc
      (fun _ => continuousOn_const) hr (fun i t _ => hdpath i t) hdc
      (fun t ht => hinj t ht.1 ht.2) hmass hnormal hvEnergy
      (fun t ht => by simpa only [hsqrt] using henergy t ht)
      (fun i => by simpa [path] using hyL i)
      (fun i => by simpa [path] using hzL i)
  refine ⟨u₀, u₁, T₀, T₁, hu₀, hu₁, hT₀, hT₁, hT₀L, hT₁L,
    ?_, ?_, 0, ?_⟩
  · simpa [path] using hμ
  · simpa [path] using hν
  · have hP : (Real.sqrt (2 * (1 + κ)) * (R : ℝ)) ^ 2 =
        2 * (1 + κ) * (R : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    simpa only [sub_zero, hP, hsqrt] using hb

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Stability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Problem358

theorem one_third_stability_oai :
    ∀ (d : ℕ) (K Y : Set (E d)),
      2 ≤ d → IsCompact K → Convex ℝ K → (interior K).Nonempty →
      IsCompact Y → Y.Nonempty →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (μ ν : Measure (E d)),
          IsProbabilityMeasure μ → IsProbabilityMeasure ν →
          IsSupported μ Y → IsSupported ν Y →
          ∃ Tμ Tν : E d → E d,
            IsUniqueQuadraticOptimalMap (uniformMeasure K) μ Tμ ∧
            IsUniqueQuadraticOptimalMap (uniformMeasure K) ν Tν ∧
            mapL2Dist (uniformMeasure K) Tμ Tν ≤
              C * Real.rpow (wasserstein2 μ ν) (1 / 3 : ℝ) := by
  intro d K Y _hd hK hKconv hKint hY hYne
  obtain ⟨R, hRpos, hKR⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨L, hLpos, hYL⟩ := hY.isBounded.exists_pos_norm_le
  let Rn : ℝ≥0 := ⟨R, hRpos.le⟩
  let Ln : ℝ≥0 := ⟨L, hLpos.le⟩
  have hxR : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ Rn := by
    filter_upwards [UniformSource.ae_mem hK.measurableSet] with x hx
    exact hKR x hx
  apply one_third_stability_of_closedCell_intercept_paths hK hKconv hKint hY hYne
    Rn Ln hxR hYL (κ := 162) (by norm_num)
  intro n hn m y z hm hsum _hyL _hzL hinj
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact FixedMassIntercepts.exists_actual_atomic_intercept_path hK hKconv hKint
    m hm hsum y z Rn hxR (fun t ht => hinj t ht.1 ht.2)

end Problem358

end

end OAI
end

theorem solution : type_of% @OAI.Problem358.one_third_stability_oai := @OAI.Problem358.one_third_stability_oai
