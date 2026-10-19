-- Prove2me | solution 1 for OAI.SeparableQuotient.negative_main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T21:16:11.99344+00:00
-- url     : https://prove2.me/submissions/c983319a-d5b6-43e6-a214-72e1aee6c98f

import Mathlib
import Definitions.Def_SeparableQuotientNegative
import Definitions.Def_OAIQWSQN005
import Theorems.Thm_OAI_SeparableQuotient_negative_real

section
-- module Solutions.OAIQW_SeparableQuotient.AdjointSurjectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

namespace SeparableQuotient
open Set Metric
open scoped Topology

universe u v

section RealAdjoint
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Hahn–Banach ball inclusion with a quantitative lower bound. -/
theorem ball_image_closure_of_adjoint_bound
    (T : E →L[ℝ] F) (c : ℝ) (_hc : 0 < c)
    (hT : ∀ g : StrongDual ℝ F, c * ‖g‖ ≤ ‖g.comp T‖) :
    closedBall (0 : F) c ⊆ closure (T '' closedBall (0 : E) 1) := by
  intro y hy
  simp only [mem_closedBall, dist_zero_right] at hy
  by_contra hn
  have hconv : Convex ℝ (closure (T '' closedBall (0 : E) 1)) :=
    ((convex_closedBall (0 : E) 1).linear_image T.toLinearMap).closure
  obtain ⟨g, a, hga, hay⟩ := geometric_hahn_banach_closed_point hconv isClosed_closure hn
  have ha : 0 < a := by
    have := hga (T 0) (subset_closure ⟨0, by simp, rfl⟩)
    simpa using this
  have hnorm : ‖g.comp T‖ ≤ a := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm ha.le
    intro x hx
    have hx' : x ∈ closedBall (0 : E) 1 := by simp [mem_closedBall, hx]
    have hnx' : -x ∈ closedBall (0 : E) 1 := by simp [mem_closedBall, hx]
    have hp := hga (T x) (subset_closure ⟨x, hx', rfl⟩)
    have hm := hga (T (-x)) (subset_closure ⟨-x, hnx', rfl⟩)
    simp only [map_neg] at hm
    change |g (T x)| ≤ a
    exact abs_le.mpr ⟨by linarith, hp.le⟩
  have hgy : g y ≤ ‖g‖ * c :=
    (le_abs_self _).trans ((g.le_opNorm y).trans
      (mul_le_mul_of_nonneg_left hy (norm_nonneg g)))
  have hb := hT g
  nlinarith

/-- Approximate lifting with a quantitative norm bound. -/
theorem approximate_lift_of_adjoint_bound
    (T : E →L[ℝ] F) (c : ℝ) (hc : 0 < c)
    (hT : ∀ g : StrongDual ℝ F, c * ‖g‖ ≤ ‖g.comp T‖) (y : F) :
    ∃ x : E, ‖y - T x‖ ≤ (1 / 2 : ℝ) * ‖y‖ ∧ ‖x‖ ≤ c⁻¹ * ‖y‖ := by
  by_cases hy : y = 0
  · subst y
    exact ⟨0, by simp, by simp⟩
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hmem : (c / ‖y‖) • y ∈ closedBall (0 : F) c := by
    simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hc hn)]
    exact le_of_eq (div_mul_cancel₀ c (ne_of_gt hn))
  have hcl := ball_image_closure_of_adjoint_bound T c hc hT hmem
  obtain ⟨w, ⟨z, hz, rfl⟩, hw⟩ := Metric.mem_closure_iff.mp hcl (c / 2) (by positivity)
  refine ⟨(‖y‖ / c) • z, ?_, ?_⟩
  · have heq : y - T ((‖y‖ / c) • z) =
        (‖y‖ / c) • ((c / ‖y‖) • y - T z) := by
      rw [smul_sub, smul_smul, map_smul]
      have : ‖y‖ / c * (c / ‖y‖) = 1 := by field_simp
      rw [this, one_smul]
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hn hc)]
    rw [dist_eq_norm] at hw
    calc
      ‖y‖ / c * ‖(c / ‖y‖) • y - T z‖ ≤ ‖y‖ / c * (c / 2) :=
        mul_le_mul_of_nonneg_left hw.le (div_pos hn hc).le
      _ = (1 / 2 : ℝ) * ‖y‖ := by field_simp
  · simp only [mem_closedBall, dist_zero_right] at hz
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hn hc)]
    calc
      ‖y‖ / c * ‖z‖ ≤ ‖y‖ / c * 1 := mul_le_mul_of_nonneg_left hz (div_pos hn hc).le
      _ = c⁻¹ * ‖y‖ := by ring

/-- The elementary completion argument, with no open-mapping assumption. -/
theorem exact_lift_of_approximate [CompleteSpace E]
    (T : E →L[ℝ] F) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ y : F, ∃ x : E, ‖y - T x‖ ≤ (1 / 2 : ℝ) * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖)
    (y : F) : ∃ x : E, T x = y ∧ ‖x‖ ≤ 2 * C * ‖y‖ := by
  classical
  choose g hg using ha
  let h (z : F) := z - T (g z)
  have hle : ∀ z, ‖h z‖ ≤ (1 / 2 : ℝ) * ‖z‖ := fun z => (hg z).1
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ (1 / 2 : ℝ) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ']
      apply (hle _).trans
      rw [pow_succ', mul_assoc]
      gcongr
  let u (n : ℕ) := g (h^[n] y)
  have ule : ∀ n, ‖u n‖ ≤ (1 / 2 : ℝ) ^ n * (C * ‖y‖) := by
    intro n
    apply (hg _).2.trans
    calc
      C * ‖h^[n] y‖ ≤ C * ((1 / 2 : ℝ) ^ n * ‖y‖) := by gcongr; exact hnle n
      _ = (1 / 2 : ℝ) ^ n * (C * ‖y‖) := by ring
  have sNu : Summable (fun n => ‖u n‖) := by
    refine .of_nonneg_of_le (fun n => norm_nonneg _) ule ?_
    exact Summable.mul_right _ summable_geometric_two
  have su : Summable u := sNu.of_norm
  have xineq : ‖∑' n, u n‖ ≤ 2 * C * ‖y‖ := by
    calc
      ‖∑' n, u n‖ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm sNu
      _ ≤ ∑' n, (1 / 2 : ℝ) ^ n * (C * ‖y‖) :=
        sNu.tsum_le_tsum ule (Summable.mul_right _ summable_geometric_two)
      _ = (∑' n, (1 / 2 : ℝ) ^ n) * (C * ‖y‖) := tsum_mul_right
      _ = 2 * C * ‖y‖ := by rw [tsum_geometric_two, mul_assoc]
  have fsumeq : ∀ n : ℕ, T (∑ i ∈ Finset.range n, u i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, T.map_add, ih, Function.iterate_succ_apply', sub_add]
  have L₁ : Filter.Tendsto (fun n => T (∑ i ∈ Finset.range n, u i))
      Filter.atTop (𝓝 (T (∑' n, u n))) :=
    (T.continuous.tendsto _).comp su.hasSum.tendsto_sum_nat
  simp only [fsumeq] at L₁
  have L₂ : Filter.Tendsto (fun n => y - h^[n] y) Filter.atTop (𝓝 (y - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).mul tendsto_const_nhds
  exact ⟨∑' n, u n, by simpa using tendsto_nhds_unique L₁ L₂, xineq⟩

/-- Adjoint lower bounds force surjectivity. -/
theorem surjective_of_adjoint_bound [CompleteSpace E]
    (T : E →L[ℝ] F) (c : ℝ) (hc : 0 < c)
    (hT : ∀ g : StrongDual ℝ F, c * ‖g‖ ≤ ‖g.comp T‖) :
    Function.Surjective T := by
  intro y
  obtain ⟨x, hx, _⟩ := exact_lift_of_approximate T c⁻¹ (inv_nonneg.mpr hc.le)
    (approximate_lift_of_adjoint_bound T c hc hT) y
  exact ⟨x, hx⟩

end RealAdjoint
section RCLikeAdjoint
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The surjectivity test over either original scalar field. -/
theorem surjective_of_adjoint_bound_rclike
    (T : E →L[𝕜] F) (c : ℝ) (hc : 0 < c)
    (hT : ∀ g : StrongDual 𝕜 F, c * ‖g‖ ≤ ‖g.comp T‖) :
    Function.Surjective T := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ 𝕜 F
  have hb : ∀ g : StrongDual ℝ F, c * ‖g‖ ≤ ‖g.comp (T.restrictScalars ℝ)‖ := by
    intro g
    have heq : StrongDual.extendRCLike (g.comp (T.restrictScalars ℝ)) =
        (g.extendRCLike : StrongDual 𝕜 F).comp T := by
      ext x
      simp [StrongDual.extendRCLike_apply]
    have h := hT g.extendRCLike
    rw [StrongDual.norm_extendRCLike, ← heq, StrongDual.norm_extendRCLike] at h
    exact h
  exact surjective_of_adjoint_bound (T.restrictScalars ℝ) c hc hb

end RCLikeAdjoint
end SeparableQuotient

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PrefixNormers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

namespace SeparableQuotient
open Set Metric
open scoped BigOperators Topology
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

namespace PrefixNormers

attribute [local instance] OAI.SeparableQuotient.prefixDualNormedGroup
attribute [local instance] OAI.SeparableQuotient.prefixDualNormedSpace
variable {f : ℕ → StrongDual 𝕜 X} (H : PrefixNormers f)

include H

theorem spanCoord_basis (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) (n j : ℕ) :
    H.spanCoord a ha hf n ⟨f j, Submodule.subset_span (Set.mem_range_self j)⟩ =
      if j = n then 1 else 0 := by
  change (H.linearIndependent a ha hf).repr _ n = _
  rw [LinearIndependent.repr_eq_single _ j _ rfl]
  simp [Finsupp.single_apply]

lemma ambientCoord_spec (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) :
    (∀ n, ‖H.ambientCoord a ha hf n‖ ≤ 4 / a) ∧
    (∀ n, ∀ x : Submodule.span 𝕜 (Set.range f),
      H.ambientCoord a ha hf n x = H.spanCoord a ha hf n x) :=
  Classical.choose_spec (H.exists_ambientCoord a ha hf)

lemma coord_basis (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) (n j : ℕ) :
    H.coord a ha hf n (basisVector f j) = if j = n then 1 else 0 := by
  change H.ambientCoord a ha hf n (f j) = _
  rw [(H.ambientCoord_spec a ha hf).2 n ⟨f j, Submodule.subset_span (Set.mem_range_self j)⟩]
  exact H.spanCoord_basis a ha hf n j

attribute [local instance] OAI.SeparableQuotient.PrefixNormers.closedDualNormedGroup
attribute [local instance] OAI.SeparableQuotient.PrefixNormers.closedDualNormedSpace
lemma ambientCoord_basis (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) (n j : ℕ) :
    H.ambientCoord a ha hf n (f j) = if j = n then 1 else 0 :=
  H.coord_basis a ha hf n j

lemma evaluation_normer (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    {m : ℕ} {d : X} (hd : d ∈ H.D m) :
    evaluation f d = ∑ i ∈ Finset.range m, f i d • H.coord a ha hf i := by
  classical
  have heq : Set.EqOn (NormedSpace.inclusionInDoubleDual 𝕜 X d)
      (∑ i ∈ Finset.range m, f i d • H.ambientCoord a ha hf i :
        StrongDual 𝕜 (StrongDual 𝕜 X))
      (closure (Submodule.span 𝕜 (Set.range f) : Set (StrongDual 𝕜 X))) := by
    apply ContinuousLinearMap.eqOn_closure_span
    rintro _ ⟨n, rfl⟩
    change f n d = _
    simp only [sum_apply, smul_apply, H.ambientCoord_basis, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    by_cases hn : n < m
    · simp [hn]
    · simp [hn, H.vanish m n (Nat.le_of_not_gt hn) d hd]
  ext v
  have hv := heq v.property
  change (v : StrongDual 𝕜 X) d = _ at hv
  simpa only [evaluation_apply, sum_apply, smul_apply, coord,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using hv

lemma adjointVector_bound (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (h : StrongDual 𝕜 (StrongDual 𝕜 (closedSpan f))) (m : ℕ) :
    ‖H.adjointVector a ha hf h m‖ ≤ 2 * ‖h.comp (evaluation f)‖ := by
  classical
  by_cases hm : m = 0
  · subst m; simp [adjointVector]
  obtain ⟨d, hd, hb⟩ := H.norming m (Nat.pos_of_ne_zero hm)
    (fun n => h (H.coord a ha hf n))
  have he : (h.comp (evaluation f)) d =
      (∑ i ∈ Finset.range m, h (H.coord a ha hf i) • f i) d := by
    rw [ContinuousLinearMap.comp_apply, H.evaluation_normer a ha hf hd]
    simp [smul_eq_mul, mul_comm]
  rw [← he] at hb
  have hn := (h.comp (evaluation f)).le_opNorm d
  have hu : ‖(h.comp (evaluation f)) d‖ ≤ ‖h.comp (evaluation f)‖ :=
    hn.trans (by
      simpa using mul_le_mul_of_nonneg_left (H.unit m d hd)
        (norm_nonneg (h.comp (evaluation f))))
  have hle := hb.trans (mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 2))
  change ‖(H.adjointVector a ha hf h m : StrongDual 𝕜 X)‖ ≤ _
  simpa only [adjointVector, Submodule.coe_sum, Submodule.coe_smul, basisVector] using hle

lemma coord_adjointVector (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (h : StrongDual 𝕜 (StrongDual 𝕜 (closedSpan f))) (m n : ℕ) :
    H.coord a ha hf n (H.adjointVector a ha hf h m) =
      if n < m then h (H.coord a ha hf n) else 0 := by
  classical
  simp [adjointVector, H.coord_basis, smul_eq_mul, mul_ite]

lemma linearCombination_adjointVector (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (h : StrongDual 𝕜 (StrongDual 𝕜 (closedSpan f))) (c : ℕ →₀ 𝕜)
    {m : ℕ} (hm : c.support ⊆ Finset.range m) :
    (Finsupp.linearCombination 𝕜 (H.coord a ha hf) c) (H.adjointVector a ha hf h m) =
      h (Finsupp.linearCombination 𝕜 (H.coord a ha hf) c) := by
  classical
  change (∑ i ∈ c.support, c i • H.coord a ha hf i) (H.adjointVector a ha hf h m) =
    h (∑ i ∈ c.support, c i • H.coord a ha hf i)
  simp only [sum_apply, smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [H.coord_adjointVector, ite_eq_left (Finset.mem_range.mp (hm hi))]

lemma adjoint_bound_on_coefficientSpan (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (h : StrongDual 𝕜 (StrongDual 𝕜 (closedSpan f))) (u : H.coefficientSpan a ha hf) :
    ‖h u‖ ≤ (2 * ‖h.comp (evaluation f)‖) * ‖u‖ := by
  have hc : IsClosed {u : StrongDual 𝕜 (closedSpan f) |
      ‖h u‖ ≤ (2 * ‖h.comp (evaluation f)‖) * ‖u‖} :=
    isClosed_le h.continuous.norm (continuous_const.mul continuous_norm)
  apply closure_minimal (t := {u | ‖h u‖ ≤ (2 * ‖h.comp (evaluation f)‖) * ‖u‖})
    (fun u hu => ?_) hc u.property
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hu
  obtain ⟨m, hm⟩ := c.support.exists_nat_subset_range
  change ‖h (Finsupp.linearCombination 𝕜 (H.coord a ha hf) c)‖ ≤
    (2 * ‖h.comp (evaluation f)‖) * ‖Finsupp.linearCombination 𝕜 (H.coord a ha hf) c‖
  rw [← H.linearCombination_adjointVector a ha hf h c hm]
  exact ((Finsupp.linearCombination 𝕜 (H.coord a ha hf) c).le_opNorm _).trans
    (by
      rw [mul_comm (2 * _)]
      exact mul_le_mul_of_nonneg_left (H.adjointVector_bound a ha hf h m) (norm_nonneg _))

lemma evaluationToZ_adjoint_bound (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (hZ : ∀ x, evaluation f x ∈ H.coefficientSpan a ha hf)
    (h : StrongDual 𝕜 (H.coefficientSpan a ha hf)) :
    (1 / 2 : ℝ) * ‖h‖ ≤ ‖h.comp (H.evaluationToZ a ha hf hZ)‖ := by
  obtain ⟨h', he, _⟩ := exists_extension_norm_eq (H.coefficientSpan a ha hf) h
  have hcomp : h'.comp (evaluation f) = h.comp (H.evaluationToZ a ha hf hZ) := by
    ext x
    exact he (H.evaluationToZ a ha hf hZ x)
  have hb : ‖h‖ ≤ 2 * ‖h.comp (H.evaluationToZ a ha hf hZ)‖ := by
    apply h.opNorm_le_bound (mul_nonneg (by norm_num) (norm_nonneg _))
    intro u
    rw [← he u]
    simpa only [hcomp] using H.adjoint_bound_on_coefficientSpan a ha hf h' u
  linarith

/-- Coefficients are linearly independent, so their closed span is infinite dimensional. -/
lemma coord_linearIndependent (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) :
    LinearIndependent 𝕜 (H.coord a ha hf) := by
  classical
  refine linearIndependent_iff.mpr fun c hc => c.ext fun n => ?_
  have he := congrArg (fun u : StrongDual 𝕜 (closedSpan f) => u (basisVector f n)) hc
  simpa [Finsupp.linearCombination_apply, Finsupp.sum, H.coord_basis,
    smul_eq_mul, mul_ite] using he

lemma coefficientVector_linearIndependent (a : ℝ) (ha : 0 < a)
    (hf : ∀ n, a ≤ ‖f n‖) : LinearIndependent 𝕜 (H.coefficientVector a ha hf) :=
  LinearIndependent.of_comp (H.coefficientSpan a ha hf).subtype
    (H.coord_linearIndependent a ha hf)

lemma coefficientSpan_infiniteDimensional (a : ℝ) (ha : 0 < a)
    (hf : ∀ n, a ≤ ‖f n‖) : ¬ FiniteDimensional 𝕜 (H.coefficientSpan a ha hf) := by
  intro h
  let := h
  exact Module.Finite.not_linearIndependent_of_infinite (H.coefficientVector a ha hf)
    (H.coefficientVector_linearIndependent a ha hf)

lemma coefficientSpan_isClosed (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) :
    IsClosed (H.coefficientSpan a ha hf : Set (StrongDual 𝕜 (closedSpan f))) :=
  (Submodule.span 𝕜 (Set.range (H.coord a ha hf))).isClosed_topologicalClosure

lemma coefficientSpan_separable (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) :
    TopologicalSpace.SeparableSpace (H.coefficientSpan a ha hf) := by
  have hs := ((Set.countable_range (H.coord a ha hf)).isSeparable.span (R := 𝕜)).closure
  exact hs.separableSpace

end PrefixNormers
end SeparableQuotient

namespace SeparableQuotient
namespace PrefixNormers
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {f : ℕ → StrongDual 𝕜 X} (H : PrefixNormers f)

attribute [local instance] OAI.SeparableQuotient.PrefixNormers.outcomeDualNormedGroup
attribute [local instance] OAI.SeparableQuotient.PrefixNormers.outcomeDualNormedSpace
attribute [local instance] OAI.SeparableQuotient.PrefixNormers.outcomeClosedDualNormedGroup
attribute [local instance] OAI.SeparableQuotient.PrefixNormers.outcomeClosedDualNormedSpace
/-- The adjoint lower bound implies surjectivity of evaluation. -/
theorem evaluationToZ_surjective (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (hZ : ∀ x, evaluation f x ∈ H.coefficientSpan a ha hf) :
    Function.Surjective (H.evaluationToZ a ha hf hZ) :=
  surjective_of_adjoint_bound_rclike (𝕜 := 𝕜) (E := X)
    (F := H.coefficientSpan a ha hf) (H.evaluationToZ a ha hf hZ) (1 / 2)
    (by norm_num) (H.evaluationToZ_adjoint_bound a ha hf hZ)

/-- Finite prefix normers yield a separable quotient. -/
theorem hasSeparableQuotient_of_range (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (hZ : ∀ x, evaluation f x ∈ H.coefficientSpan a ha hf) : HasSeparableQuotient 𝕜 X := by
  let : IsClosed (H.coefficientSpan a ha hf : Set (StrongDual 𝕜 (closedSpan f))) :=
    H.coefficientSpan_isClosed a ha hf
  refine ⟨H.coefficientSpan a ha hf, inferInstance, inferInstance, inferInstance,
    H.coefficientSpan_separable a ha hf, H.coefficientSpan_infiniteDimensional a ha hf,
    H.evaluationToZ a ha hf hZ, H.evaluationToZ_surjective a ha hf hZ⟩

end PrefixNormers
end SeparableQuotient

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.FiniteNormers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

namespace SeparableQuotient
open Set Metric
open scoped Topology
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

namespace NormerStep
attribute [local instance] OAI.SeparableQuotient.selectionDualNormedGroup
attribute [local instance] OAI.SeparableQuotient.selectionDualNormedSpace
attribute [local instance] OAI.SeparableQuotient.NormerStep.instDecidableEq
attribute [local instance] OAI.SeparableQuotient.NormerStep.instDecidableEqStrongDual
variable (F : Submodule 𝕜 (StrongDual 𝕜 X)) (hF : ¬ FiniteDimensional 𝕜 F)
variable (xs : ℕ → X)

lemma seq_mem (n : ℕ) : seq F hF xs n ∈ F := (stage F hF xs n).f.property

lemma seq_vanish_x {m n : ℕ} (hmn : m ≤ n) : seq F hF xs n (xs m) = 0 := by
  classical
  apply (stage F hF xs n).vanish
  by_cases hm : m = n
  · subst m; exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    apply state_monotone F hF xs (Nat.succ_le_of_lt (lt_of_le_of_ne hmn hm))
    change xs m ∈ (state F hF xs (m + 1)).1
    rw [state_succ]
    exact Finset.mem_insert_self _ _

end NormerStep

end SeparableQuotient

namespace SeparableQuotient
open Set Metric
open scoped Topology BigOperators
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

namespace NormerStep
attribute [local instance] OAI.SeparableQuotient.criterionDualNormedGroup
attribute [local instance] OAI.SeparableQuotient.criterionDualNormedSpace
variable (F : Submodule 𝕜 (StrongDual 𝕜 X)) (hF : ¬ FiniteDimensional 𝕜 F)
variable (xs : ℕ → X)

lemma span_le [IsClosed (F : Set (StrongDual 𝕜 X))] :
    PrefixNormers.closedSpan (seq F hF xs) ≤ F := by
  apply Submodule.topologicalClosure_minimal _ (ht := ‹IsClosed (F : Set (StrongDual 𝕜 X))›)
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  exact seq_mem F hF xs n

lemma evaluation_x (j : ℕ) :
    PrefixNormers.evaluation (seq F hF xs) (xs j) =
      ∑ i ∈ Finset.range j, seq F hF xs i (xs j) •
        (prefixNormers F hF xs).coord 1 (by norm_num) (fun n => (seq_norm F hF xs n).ge) i := by
  classical
  let H := prefixNormers F hF xs
  have heq : Set.EqOn (NormedSpace.inclusionInDoubleDual 𝕜 X (xs j))
      (∑ i ∈ Finset.range j, seq F hF xs i (xs j) •
        H.ambientCoord 1 (by norm_num) (fun n => (seq_norm F hF xs n).ge) i :
          StrongDual 𝕜 (StrongDual 𝕜 X))
      (closure (Submodule.span 𝕜 (Set.range (seq F hF xs)) : Set (StrongDual 𝕜 X))) := by
    apply ContinuousLinearMap.eqOn_closure_span
    rintro _ ⟨n, rfl⟩
    change seq F hF xs n (xs j) = _
    simp only [sum_apply, smul_apply, H.ambientCoord_basis, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    by_cases hn : n < j
    · simp [hn]
    · simp [hn, seq_vanish_x F hF xs (Nat.le_of_not_gt hn)]
  ext v
  have hv := heq v.property
  change (v : StrongDual 𝕜 X) (xs j) = _ at hv
  simpa only [PrefixNormers.evaluation_apply, sum_apply, smul_apply, PrefixNormers.coord,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, H] using hv

end NormerStep

attribute [local instance] OAI.SeparableQuotient.criterionDualNormedGroup
attribute [local instance] OAI.SeparableQuotient.criterionDualNormedSpace
attribute [local instance] OAI.SeparableQuotient.criterionSubspaceDualNormedGroup
attribute [local instance] OAI.SeparableQuotient.criterionSubspaceDualNormedSpace
/-- A dense sequence of evaluations can be represented by actual vectors of `X`. -/
lemma exists_dense_evaluations (F : Submodule 𝕜 (StrongDual 𝕜 X))
    (hsep : TopologicalSpace.IsSeparable (Set.range (subspaceEvaluation F))) :
    ∃ xs : ℕ → X, ∀ x : X, subspaceEvaluation F x ∈
      closure (Set.range (fun n => subspaceEvaluation F (xs n))) := by
  classical
  let R := Set.range (subspaceEvaluation F)
  let : TopologicalSpace.SeparableSpace R := hsep.separableSpace
  let : Nonempty R := ⟨⟨subspaceEvaluation F 0, Set.mem_range_self 0⟩⟩
  obtain ⟨ys, hys⟩ := TopologicalSpace.exists_dense_seq R
  choose xs hxs using fun n => (ys n).property
  refine ⟨xs, fun x => ?_⟩
  have he : (fun n => subspaceEvaluation F (xs n)) = fun n => (ys n).val := by
    funext n; exact hxs n
  rw [he]
  have hc := image_closure_subset_closure_image
    (continuous_subtype_val : Continuous (Subtype.val : R → StrongDual 𝕜 F))
    (s := Set.range ys)
  have hm := hc ⟨⟨subspaceEvaluation F x, Set.mem_range_self x⟩,
    hys (⟨subspaceEvaluation F x, Set.mem_range_self x⟩ : R), rfl⟩
  simpa only [← Set.range_comp'] using hm

end SeparableQuotient

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.EvaluationCriterion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

namespace SeparableQuotient
open Set Metric
open scoped Topology BigOperators
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

attribute [local instance] OAI.SeparableQuotient.evaluationCriterionDualNormedGroup
attribute [local instance] OAI.SeparableQuotient.evaluationCriterionDualNormedSpace
attribute [local instance] OAI.SeparableQuotient.evaluationCriterionSubspaceDualNormedGroup
attribute [local instance] OAI.SeparableQuotient.evaluationCriterionSubspaceDualNormedSpace
/-- Norm-separable evaluation on an infinite-dimensional dual subspace yields a separable quotient. -/
theorem hasSeparableQuotient_of_separable_evaluation
    (F : Submodule 𝕜 (StrongDual 𝕜 X)) [IsClosed (F : Set (StrongDual 𝕜 X))]
    (hF : ¬ FiniteDimensional 𝕜 F)
    (hsep : TopologicalSpace.IsSeparable (Set.range (subspaceEvaluation F))) :
    HasSeparableQuotient 𝕜 X := by
  classical
  obtain ⟨xs, hxs⟩ := exists_dense_evaluations F hsep
  let f := NormerStep.seq F hF xs
  let H := NormerStep.prefixNormers F hF xs
  have hn : ∀ n, (1 : ℝ) ≤ ‖f n‖ := fun n => (NormerStep.seq_norm F hF xs n).ge
  let G := PrefixNormers.closedSpan f
  let Z := H.coefficientSpan 1 (by norm_num) hn
  let inc : G →L[𝕜] F := G.subtypeL.codRestrict F
    (fun v => NormerStep.span_le F hF xs v.property)
  let restriction : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 G :=
    ContinuousLinearMap.precomp 𝕜 inc
  have he (x : X) : restriction (subspaceEvaluation F x) = PrefixNormers.evaluation f x := by
    ext v; rfl
  have hx (j : ℕ) : restriction (subspaceEvaluation F (xs j)) ∈ Z := by
    rw [he]
    change PrefixNormers.evaluation (NormerStep.seq F hF xs) (xs j) ∈ Z
    rw [NormerStep.evaluation_x]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self i))
  have hc : IsClosed (restriction ⁻¹' (Z : Set (StrongDual 𝕜 G))) :=
    (H.coefficientSpan_isClosed 1 (by norm_num) hn).preimage restriction.continuous
  apply H.hasSeparableQuotient_of_range 1 (by norm_num) hn
  intro x
  rw [← he x]
  apply closure_minimal (t := restriction ⁻¹' (Z : Set (StrongDual 𝕜 G))) ?_ hc (hxs x)
  rintro _ ⟨j, rfl⟩
  exact hx j

end SeparableQuotient

namespace SeparableQuotient
open Set Metric
open scoped Topology
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

attribute [local instance] OAI.SeparableQuotient.necessityDualGroup
attribute [local instance] OAI.SeparableQuotient.necessityDualSpace
omit [CompleteSpace Y] in
/-- The dual of an infinite-dimensional normed space is infinite-dimensional. -/
lemma dual_infiniteDimensional (hY : ¬ FiniteDimensional 𝕜 Y) :
    ¬ FiniteDimensional 𝕜 (StrongDual 𝕜 Y) := by
  intro h
  let := h
  apply hY
  exact FiniteDimensional.of_injective (NormedSpace.inclusionInDoubleDualLi 𝕜).toLinearMap
    (NormedSpace.inclusionInDoubleDualLi 𝕜).injective

/-- The adjoint of an onto map is bounded below, with the actual open-mapping lift constant. -/
lemma precomp_antilipschitz_of_surjective (T : X →L[𝕜] Y) (hT : Function.Surjective T) :
    ∃ C : NNReal, AntilipschitzWith C
      (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 Y →L[𝕜] StrongDual 𝕜 X) := by
  obtain ⟨g, _hg⟩ := T.exists_nonlinearRightInverse_of_surjective (LinearMap.range_eq_top.mpr hT)
  let S : StrongDual 𝕜 Y →L[𝕜] StrongDual 𝕜 X := ContinuousLinearMap.precomp 𝕜 T
  refine ⟨g.nnnorm, S.antilipschitz_of_bound ?_⟩
  intro f
  apply f.opNorm_le_bound (mul_nonneg g.nnnorm.coe_nonneg (norm_nonneg _))
  intro y
  calc
    ‖f y‖ = ‖S f (g y)‖ := by
      change ‖f y‖ = ‖f (T (g y))‖
      rw [g.right_inv]
    _ ≤ ‖S f‖ * ‖g y‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖S f‖ * (g.nnnorm * ‖y‖) :=
      mul_le_mul_of_nonneg_left (g.bound y) (norm_nonneg _)
    _ = (g.nnnorm * ‖S f‖) * ‖y‖ := by ring

/-- A separable quotient yields an infinite-dimensional dual subspace with norm-separable evaluation. -/
theorem separable_evaluation_of_hasSeparableQuotient (hX : HasSeparableQuotient 𝕜 X) :
    ∃ F : Submodule 𝕜 (StrongDual 𝕜 X), IsClosed (F : Set (StrongDual 𝕜 X)) ∧
      (¬ FiniteDimensional 𝕜 F) ∧
      TopologicalSpace.IsSeparable (Set.range (subspaceEvaluation F)) := by
  obtain ⟨Y, hYn, hYs, hYc, hYsep, hYinf, T, hT⟩ := hX
  let := hYn
  let := hYs
  let := hYc
  let := hYsep
  let S : StrongDual 𝕜 Y →L[𝕜] StrongDual 𝕜 X := ContinuousLinearMap.precomp 𝕜 T
  obtain ⟨C, hC⟩ := precomp_antilipschitz_of_surjective T hT
  have hSc : IsClosed (Set.range S) := hC.isClosed_range S.uniformContinuous
  let F := S.range
  have hFc : IsClosed (F : Set (StrongDual 𝕜 X)) := hSc
  let e : StrongDual 𝕜 Y ≃L[𝕜] F := S.equivRange hC.injective hSc
  have hFi : ¬ FiniteDimensional 𝕜 F := by
    intro hf
    let := hf
    have : FiniteDimensional 𝕜 (StrongDual 𝕜 Y) := e.toLinearEquiv.symm.finiteDimensional
    exact dual_infiniteDimensional hYinf inferInstance
  let Q : Y →L[𝕜] StrongDual 𝕜 F :=
    (ContinuousLinearMap.precomp 𝕜 e.symm.toContinuousLinearMap).comp
      (NormedSpace.inclusionInDoubleDual 𝕜 Y)
  have he (x : X) : subspaceEvaluation F x = Q (T x) := by
    ext f
    obtain ⟨g, rfl⟩ := e.surjective f
    change (S g) x = (e.symm (e g)) (T x)
    rw [e.symm_apply_apply]
    rfl
  refine ⟨F, hFc, hFi, (TopologicalSpace.isSeparable_range Q.continuous).mono ?_⟩
  rintro _ ⟨x, rfl⟩
  exact ⟨T x, (he x).symm⟩

end SeparableQuotient

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.StrictSingularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Singular
open Set Metric
open scoped Classical Topology
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y Z W : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

lemma not_strictlySingular_iff (T : Y →L[𝕜] Z) :
    ¬ StrictlySingular T ↔ ∃ (M : Submodule 𝕜 Y), IsClosed (M : Set Y) ∧
      ¬ FiniteDimensional 𝕜 M ∧ ∃ c : ℝ, 0 < c ∧ ∀ x : M, c*‖x‖ ≤ ‖T x‖ := by
  simp only [StrictlySingular, not_forall, not_exists, not_lt, exists_prop]

lemma lowerBound_antilipschitz (T : Y →L[𝕜] Z) (c : ℝ) (hc : 0 < c)
    (h : ∀ x, c*‖x‖ ≤ ‖T x‖) : AntilipschitzWith ⟨c⁻¹,inv_nonneg.mpr hc.le⟩ T := by
  apply T.antilipschitz_of_bound
  intro x
  change ‖x‖ ≤ c⁻¹*‖T x‖
  exact (le_inv_mul_iff₀ hc).mpr (by simpa [mul_comm] using h x)

lemma lowerBound_isClosed_range [CompleteSpace Y] (T : Y →L[𝕜] Z) (c : ℝ) (hc : 0 < c)
    (h : ∀ x, c*‖x‖ ≤ ‖T x‖) : IsClosed (Set.range T) :=
  (lowerBound_antilipschitz T c hc h).isClosed_range T.uniformContinuous

/-- A non-strictly-singular map furnishes a closed infinite-dimensional image
and a bounded lift into its original domain. -/
theorem exists_lift_of_not_strictlySingular [CompleteSpace Y] [CompleteSpace Z] (T : Y →L[𝕜] Z)
    (hT : ¬ StrictlySingular T) :
    ∃ (H : Submodule 𝕜 Z), IsClosed (H : Set Z) ∧ ¬ FiniteDimensional 𝕜 H ∧
      ∃ U : H →L[𝕜] Y, ∀ x : H, T (U x) = x := by
  obtain ⟨M,hM,hI,c,hc,h⟩ := (not_strictlySingular_iff T).mp hT
  let : CompleteSpace M := hM.completeSpace_coe
  let A := T.comp M.subtypeL
  let e := A.equivRange (lowerBound_antilipschitz A c hc h).injective
    (lowerBound_isClosed_range A c hc h)
  refine ⟨A.range,lowerBound_isClosed_range A c hc h,?_,M.subtypeL.comp e.symm.toContinuousLinearMap,?_⟩
  · intro hF
    let : FiniteDimensional 𝕜 A.range := hF
    exact hI (FiniteDimensional.of_injective e.toLinearMap e.injective)
  · intro x
    exact congrArg (fun x : A.range => (x : Z)) (e.apply_symm_apply x)

end SeparableQuotient.Singular

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.Complexification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

/- Complexification by real-linear maps from ℂ with the operator norm and real coordinates f(1), f(i). -/
namespace SeparableQuotient
open scoped Classical
universe u
variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace Complexify

lemma infinite [CompleteSpace X] (hX : ¬ FiniteDimensional ℝ X) :
    ¬ FiniteDimensional ℂ (Complexify X) := by
  intro hh
  let := hh
  let : FiniteDimensional ℝ (Complexify X) := FiniteDimensional.trans ℝ ℂ _
  let : FiniteDimensional ℝ (X × X) := FiniteDimensional.of_injective (pairEquiv X).symm.toLinearMap (pairEquiv X).symm.injective
  exact hX (FiniteDimensional.of_injective (LinearMap.inl ℝ X X) (by intro x y h; exact Prod.mk.inj h |>.1))

end Complexify
end SeparableQuotient

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.ProductQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient
open Set TopologicalSpace Singular
open scoped Classical
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

attribute [local instance] OAI.SeparableQuotient.fsDualGroup
attribute [local instance] OAI.SeparableQuotient.fsDualSpace
omit [CompleteSpace Y] in
lemma hasSQ_of_adjoint_not_SS (a : X →L[𝕜] Y)
    (F : Submodule 𝕜 (StrongDual 𝕜 Y)) (hF : IsClosed (F : Set (StrongDual 𝕜 Y)))
    (hsep : IsSeparable (range (subspaceEvaluation F)))
    (hT : ¬ StrictlySingular ((ContinuousLinearMap.precomp 𝕜 a).comp F.subtypeL)) :
    HasSeparableQuotient 𝕜 X := by
  let : CompleteSpace F := hF.completeSpace_coe
  obtain ⟨H,hH,hHi,U,hU⟩ := exists_lift_of_not_strictlySingular _ hT
  let := hH
  apply hasSeparableQuotient_of_separable_evaluation H hHi
  let A : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 H := ContinuousLinearMap.precomp 𝕜 U
  apply (hsep.image A.continuous).mono
  rintro _ ⟨x,rfl⟩
  refine ⟨subspaceEvaluation F (a x), mem_range_self _, ?_⟩
  ext h
  exact congrArg (fun f : StrongDual 𝕜 X => f x) (hU h)

omit [CompleteSpace X] [CompleteSpace Y] in
lemma norm_dual_prod_le (f : StrongDual 𝕜 (X × Y)) :
    ‖f‖ ≤ ‖f.comp (ContinuousLinearMap.inl 𝕜 X Y)‖ +
      ‖f.comp (ContinuousLinearMap.inr 𝕜 X Y)‖ := by
  apply f.opNorm_le_bound (by positivity)
  intro z
  have he : z = (z.1,0) + (0,z.2) := by ext <;> simp
  calc
    ‖f z‖ = ‖f (z.1,0) + f (0,z.2)‖ := by rw [← map_add,← he]
    _ ≤ ‖f (z.1,0)‖ + ‖f (0,z.2)‖ := norm_add_le _ _
    _ ≤ ‖f.comp (ContinuousLinearMap.inl 𝕜 X Y)‖ * ‖z.1‖ +
        ‖f.comp (ContinuousLinearMap.inr 𝕜 X Y)‖ * ‖z.2‖ := add_le_add
          ((f.comp (ContinuousLinearMap.inl 𝕜 X Y)).le_opNorm z.1)
          ((f.comp (ContinuousLinearMap.inr 𝕜 X Y)).le_opNorm z.2)
    _ ≤ ‖f.comp (ContinuousLinearMap.inl 𝕜 X Y)‖ * ‖z‖ +
        ‖f.comp (ContinuousLinearMap.inr 𝕜 X Y)‖ * ‖z‖ := add_le_add
          (mul_le_mul_of_nonneg_left (norm_fst_le z) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (norm_snd_le z) (norm_nonneg _))
    _ = _ := by ring

omit [CompleteSpace X] [CompleteSpace Y] in
lemma top_infinite (hX : ¬ FiniteDimensional 𝕜 X) :
    ¬ FiniteDimensional 𝕜 (⊤ : Submodule 𝕜 X) := by
  intro h
  let := h
  exact hX (FiniteDimensional.of_surjective (⊤ : Submodule 𝕜 X).subtype
    (fun x => ⟨⟨x,trivial⟩,rfl⟩))

/-- The separable quotient dichotomy for a product, via the evaluation criterion. -/
theorem hasSQ_prod_cases (h : HasSeparableQuotient 𝕜 (X × Y)) :
    HasSeparableQuotient 𝕜 X ∨ HasSeparableQuotient 𝕜 Y := by
  obtain ⟨F,hF,hFi,hsep⟩ := separable_evaluation_of_hasSeparableQuotient h
  let : CompleteSpace F := hF.completeSpace_coe
  let p₁ : F →L[𝕜] StrongDual 𝕜 X :=
    (ContinuousLinearMap.precomp 𝕜 (ContinuousLinearMap.inl 𝕜 X Y)).comp F.subtypeL
  let p₂ : F →L[𝕜] StrongDual 𝕜 Y :=
    (ContinuousLinearMap.precomp 𝕜 (ContinuousLinearMap.inr 𝕜 X Y)).comp F.subtypeL
  by_cases h₁ : StrictlySingular p₁
  · right
    apply hasSQ_of_adjoint_not_SS (ContinuousLinearMap.inr 𝕜 X Y) F hF hsep
    obtain ⟨G,_hG,hGc,hGi,hsmall⟩ := StrictlySingular.exists_small_restriction p₁ h₁
      (⊤ : Submodule 𝕜 F) isClosed_univ (top_infinite hFi) (1/2) (by norm_num)
    apply (not_strictlySingular_iff p₂).mpr
    refine ⟨G,hGc,hGi,1/2,by norm_num,?_⟩
    intro g
    have hn := norm_dual_prod_le (g.val : StrongDual 𝕜 (X × Y))
    have hs := hsmall g.val g.property
    change ‖(g : F)‖ ≤ ‖p₁ g‖ + ‖p₂ g‖ at hn
    change ‖p₁ g‖ ≤ (1/2 : ℝ)*‖g‖ at hs
    change (1/2 : ℝ)*‖g‖ ≤ ‖p₂ g‖
    change ‖g‖ ≤ ‖p₁ g‖ + ‖p₂ g‖ at hn
    linarith
  · exact Or.inl (hasSQ_of_adjoint_not_SS (ContinuousLinearMap.inl 𝕜 X Y) F hF hsep h₁)

end SeparableQuotient

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.NegativeComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient
open Set TopologicalSpace
open scoped Classical
universe u

lemma HasSeparableQuotient.of_equiv {𝕜 : Type} [RCLike 𝕜]
    {X Z : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] (d : X ≃L[𝕜] Z)
    (h : HasSeparableQuotient 𝕜 Z) : HasSeparableQuotient 𝕜 X := by
  obtain ⟨Y,hYn,hYs,hYc,hYsep,hYi,T,hT⟩ := h
  let := hYn
  let := hYs
  exact ⟨Y,hYn,hYs,hYc,hYsep,hYi,T.comp d.toContinuousLinearMap,hT.comp d.surjective⟩

/-- A complex quotient gives a real quotient of the underlying real space. -/
lemma HasSeparableQuotient.restrictScalars {X : Type u}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedSpace ℝ X]
    [IsScalarTower ℝ ℂ X]
    (h : HasSeparableQuotient ℂ X) : HasSeparableQuotient ℝ X := by
  obtain ⟨Y,hYn,hYs,hYc,hYsep,hYi,T,hT⟩ := h
  let := hYn
  let := hYs
  let : NormedSpace ℝ Y := NormedSpace.restrictScalars ℝ ℂ Y
  have hi : ¬ FiniteDimensional ℝ Y := by
    intro hh
    let := hh
    exact hYi (Module.Finite.of_restrictScalars_finite ℝ ℂ Y)
  exact ⟨Y,inferInstance,inferInstance,hYc,hYsep,hi,T.restrictScalars ℝ,hT⟩

/-- A real space without a separable quotient has a complexification without a complex separable quotient. -/
lemma complexify_noSQ (X : Type u) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] (h : ¬ HasSeparableQuotient ℝ X) :
    ¬ HasSeparableQuotient ℂ (Complexify X) := by
  intro hh
  have hr := hh.restrictScalars
  have hp := hr.of_equiv (Complexify.pairEquiv X).symm
  exact (hasSQ_prod_cases hp).elim h h

/-- CH refutes the complex separable quotient assertion in every universe. -/
theorem negative_complex (hCH : CH) : ¬ SQ.{u} ℂ := by
  intro hSQ
  apply negative_real.{u} hCH
  intro X _ _ _ hXi
  by_contra hX
  have hc := hSQ (Complexify X) (Complexify.infinite X hXi)
  exact complexify_noSQ X hX hc

end SeparableQuotient

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

namespace SeparableQuotient

universe u

theorem negative_main_oai (hCH : CH) : ¬ SQ.{u} ℝ ∧ ¬ SQ.{u} ℂ :=
  ⟨negative_real hCH, negative_complex hCH⟩

end SeparableQuotient

end OAI
end

theorem solution.{u} : type_of% @OAI.SeparableQuotient.negative_main_oai.{u} := @OAI.SeparableQuotient.negative_main_oai.{u}
