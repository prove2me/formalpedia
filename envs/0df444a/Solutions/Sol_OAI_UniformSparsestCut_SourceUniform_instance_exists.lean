-- Prove2me | solution 1 for OAI.UniformSparsestCut.SourceUniform.instance_exists
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:48:41.290288+00:00
-- url     : https://prove2.me/submissions/22cb78c7-a937-4ded-8f37-c4e0796b2992

import Mathlib
import Definitions.Def_UniformSparsestCut
import Definitions.Def_OAIQWUS000
import Theorems.Thm_OAI_UniformSparsestCut_SourceContraction_integral_bound

section
-- module Solutions.OAIQW_UniformSparsestCut.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.ChartLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ChartLinear
variable {E : Type u1} {F : Type u2} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F]

lemma pseudoInverse_comp (J : E →L[ℝ] F) {a : ℝ} (ha : 0 < a)
    (hl : ∀ x, a * ‖x‖^2 ≤ ‖J x‖^2) : (pseudoInverse J ha hl).comp J = ContinuousLinearMap.id ℝ E := by
  ext x
  exact (gramEquiv J ha hl).symm_apply_apply x

lemma gramInverse_norm (J : E →L[ℝ] F) {a : ℝ} (ha : 0 < a)
    (hl : ∀ x, a * ‖x‖^2 ≤ ‖J x‖^2) (y : E) :
    ‖(gramEquiv J ha hl).symm y‖ ≤ ‖y‖/a := by
  let x := (gramEquiv J ha hl).symm y
  have hx : J.adjoint (J x) = y := (gramEquiv J ha hl).apply_symm_apply y
  have hb := hl x
  have he : ‖J x‖^2 = inner ℝ x y := by rw [← hx, J.adjoint_inner_right, real_inner_self_eq_norm_sq]
  rw [he] at hb
  have hc := real_inner_le_norm x y
  by_cases hz : ‖x‖ = 0
  · simpa [x, hz] using (div_nonneg (norm_nonneg y) ha.le)
  · have hp : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    change ‖x‖ ≤ ‖y‖/a
    apply (le_div_iff₀ ha).mpr
    nlinarith

lemma pseudoInverse_equation (J : E →L[ℝ] F) {a : ℝ} (ha : 0 < a)
    (hl : ∀ x, a * ‖x‖^2 ≤ ‖J x‖^2) (y : F) :
    J.adjoint (J (pseudoInverse J ha hl y)) = J.adjoint y :=
  (gramEquiv J ha hl).apply_symm_apply _

lemma residual_orthogonal (J : E →L[ℝ] F) {a : ℝ} (ha : 0 < a)
    (hl : ∀ x, a * ‖x‖^2 ≤ ‖J x‖^2) (y : F) (x : E) :
    inner ℝ (J x) (y - J (pseudoInverse J ha hl y)) = 0 := by
  rw [← J.adjoint_inner_right]
  simp [pseudoInverse_equation J ha hl y]

lemma residual_pythagoras (J : E →L[ℝ] F) {a : ℝ} (ha : 0 < a)
    (hl : ∀ x, a * ‖x‖^2 ≤ ‖J x‖^2) (y : F) :
    ‖J (pseudoInverse J ha hl y)‖^2 + ‖y-J (pseudoInverse J ha hl y)‖^2 = ‖y‖^2 := by
  have h := norm_add_sq_real (J (pseudoInverse J ha hl y)) (y - J (pseudoInverse J ha hl y))
  rw [residual_orthogonal] at h
  simpa using h.symm

lemma pseudoInverse_norm (J : E →L[ℝ] F) {a : ℝ} (ha : 0 < a)
    (hl : ∀ x, a * ‖x‖^2 ≤ ‖J x‖^2) (y : F) :
    ‖pseudoInverse J ha hl y‖ ≤ ‖y‖ / Real.sqrt a := by
  have hr := residual_pythagoras J ha hl y
  have hb := hl (pseudoInverse J ha hl y)
  have hs := Real.sq_sqrt ha.le
  apply (le_div_iff₀ (Real.sqrt_pos.2 ha)).mpr
  nlinarith [sq_nonneg ‖y-J (pseudoInverse J ha hl y)‖,
    norm_nonneg (pseudoInverse J ha hl y), norm_nonneg y, Real.sqrt_nonneg a]

lemma residual_norm (J : E →L[ℝ] F) {a : ℝ} (ha : 0 < a)
    (hl : ∀ x, a * ‖x‖^2 ≤ ‖J x‖^2) (y : F) :
    ‖y-J (pseudoInverse J ha hl y)‖ ≤ ‖y‖ := by
  have h := residual_pythagoras J ha hl y
  nlinarith [norm_nonneg y, norm_nonneg (y-J (pseudoInverse J ha hl y)),
    sq_nonneg ‖J (pseudoInverse J ha hl y)‖]

lemma pseudoInverse_column (J : E →L[ℝ] F) {a : ℝ} (ha : 0 < a)
    (hl : ∀ x, a * ‖x‖^2 ≤ ‖J x‖^2) (y : F) :
    ‖pseudoInverse J ha hl y‖ ≤ ‖J.adjoint y‖/a :=
  gramInverse_norm J ha hl _

end UniformSparsestCut.ChartLinear

namespace UniformSparsestCut.FrameCharts
open scoped RealInnerProductSpace BigOperators
variable {m N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

lemma chart_adjoint_single (u : Fin N → E) (i : Fin N) :
    (chart u).adjoint (EuclideanSpace.single i 1) = u i := by
  apply ext_inner_right ℝ
  intro x
  rw [(chart u).adjoint_inner_left]
  change inner ℝ (EuclideanSpace.single i 1) (chart u x) = inner ℝ (u i) x
  rw [EuclideanSpace.inner_single_left]
  simp

end UniformSparsestCut.FrameCharts

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.RoundedCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceCharts
open scoped BigOperators RealInnerProductSpace
open Filter Set
noncomputable section
variable {m : ℕ} (f : PivotFamily.PFamily m) (hm : 0 < m)
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "F" => EuclideanSpace ℝ (Fin (m^6))
include hm
lemma B_left (s : Fin (m^3)) (x : E) : B f hm s (FrameCharts.chart (u f s) x)=x := by
  have h := ChartLinear.pseudoInverse_comp (FrameCharts.chart (u f s)) (lower_pos hm) (energy f hm s)
  exact congrArg (fun L : E →L[ℝ] E => L x) h
lemma B_column (s : Fin (m^3)) (i : Fin (m^6)) :
    ‖B f hm s (EuclideanSpace.single i 1)‖≤4*((m:ℝ)/(m:ℝ)^6) := by
  have h := ChartLinear.pseudoInverse_column (FrameCharts.chart (u f s)) (lower_pos hm) (energy f hm s) (EuclideanSpace.single i 1)
  rw [FrameCharts.chart_adjoint_single] at h
  calc
    _ ≤ 2/lower m := h.trans (div_le_div_of_nonneg_right (u_norm f hm s i).2 (lower_pos hm).le)
    _ = _ := by unfold lower; field_simp; ring
lemma B_norm (s : Fin (m^3)) (x : F) : ‖B f hm s x‖≤‖x‖/Real.sqrt (lower m) :=
  ChartLinear.pseudoInverse_norm _ (lower_pos hm) (energy f hm s) x
lemma residual_norm (s : Fin (m^3)) (x : F) :
    ‖x-FrameCharts.chart (u f s) (B f hm s x)‖≤‖x‖ :=
  ChartLinear.residual_norm _ (lower_pos hm) (energy f hm s) x
end
end UniformSparsestCut.SourceCharts

namespace UniformSparsestCut.HyperplaneCount
variable {E : Type u1} {ι : Type u2} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ E] [Fintype ι] in
lemma shattered_independent (f : ι → E →ₗ[ℝ] ℝ) (A : Finset (Finset ι))
    (hA : ∀ u ∈ A, ∃ x : E, ∀ i, f i x ≠ 0 ∧ (0 < f i x ↔ i ∈ u))
    {s : Finset ι} (hs : A.Shatters s) : LinearIndependent ℝ (fun i : s => f i) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  by_contra hj
  let t := s.filter (fun i => ∀ hi : i ∈ s, 0 < c ⟨i,hi⟩)
  obtain ⟨u,hu,htu⟩ := hs (t := t) (Finset.filter_subset _ _)
  obtain ⟨x,hx⟩ := hA u hu
  have hsign (i : s) : 0 < f i x ↔ 0 < c i := by
    rw [(hx i).2]
    have he : i.val ∈ s ∩ u ↔ i.val ∈ t := by rw [htu]
    simp only [Finset.mem_inter, i.property, true_and, t, Finset.mem_filter] at he
    exact he.trans ⟨fun h => h trivial, fun h _ => h⟩
  have hprod (i : s) : 0 ≤ c i * f i x := by
    by_cases hp : 0 < c i
    · exact le_of_lt (mul_pos hp ((hsign i).mpr hp))
    · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hp)
        (le_of_not_gt (mt (hsign i).mp hp))
  have hpj : 0 < c j * f j x := by
    by_cases hp : 0 < c j
    · exact mul_pos hp ((hsign j).mpr hp)
    · have hn : c j < 0 := lt_of_le_of_ne (le_of_not_gt hp) hj
      have hf : f j x < 0 := lt_of_le_of_ne (le_of_not_gt (mt (hsign j).mp hp)) (hx j).1
      exact mul_pos_of_neg_of_neg hn hf
  have hp : 0 < ∑ i : s, c i * f i x :=
    Finset.sum_pos' (fun i _ => hprod i) ⟨j, Finset.mem_univ _, hpj⟩
  have hz := congrArg (fun L : E →ₗ[ℝ] ℝ => L x) hc
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at hz
  linarith

omit [Fintype ι] in
lemma vcDim_le (f : ι → E →ₗ[ℝ] ℝ) (A : Finset (Finset ι))
    (hA : ∀ u ∈ A, ∃ x : E, ∀ i, f i x ≠ 0 ∧ (0 < f i x ↔ i ∈ u)) :
    A.vcDim ≤ Module.finrank ℝ E := by
  apply Finset.sup_le
  intro s hs
  have h := (shattered_independent f A hA (Finset.mem_shatterer.mp hs)).fintype_card_le_finrank
  simpa using h

lemma sign_patterns_bound (f : ι → E →ₗ[ℝ] ℝ) (A : Finset (Finset ι))
    (hA : ∀ u ∈ A, ∃ x : E, ∀ i, f i x ≠ 0 ∧ (0 < f i x ↔ i ∈ u)) :
    A.card ≤ ∑ k ∈ Finset.Iic (Module.finrank ℝ E), (Fintype.card ι).choose k := by
  have hv := vcDim_le f A hA
  exact (Finset.card_le_card_shatterer A).trans
    (Finset.card_shatterer_le_sum_vcDim.trans
      (Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.mpr hv)))

end UniformSparsestCut.HyperplaneCount

namespace UniformSparsestCut.RoundedCharts
open MeasureTheory Set Filter
open scoped Topology BigOperators RealInnerProductSpace
variable {m N S : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

lemma hyperplane_null (u : E) (hu : u ≠ 0) (t : ℝ) :
    volume {x : E | inner ℝ u x = t} = 0 := by
  let H : AffineSubspace ℝ E :=
    { carrier := {x | inner ℝ u x = t}
      smul_vsub_vadd_mem' := by
        intro c x y z hx hy hz
        change inner ℝ u x = t at hx
        change inner ℝ u y = t at hy
        change inner ℝ u z = t at hz
        change inner ℝ u (c • (x-y)+z) = t
        simp only [inner_add_right, inner_smul_right, inner_sub_right, hx, hy, hz]
        ring }
  have ht : H ≠ ⊤ := by
    intro he
    have hzero : (0:E) ∈ H := by rw [he]; trivial
    have hone : u ∈ H := by rw [he]; trivial
    change inner ℝ u 0 = t at hzero
    change inner ℝ u u = t at hone
    rw [inner_zero_right] at hzero
    have := ((inner_self_eq_zero (𝕜 := ℝ)).mp (hone.trans hzero.symm))
    exact hu this
  exact Measure.addHaar_affineSubspace volume H ht

lemma ae_regular (u : Fin N → E) (τ : ℝ) (hu : ∀ i, u i ≠ 0) :
    ∀ᵐ θ : E, regular u τ θ := by
  have hi (i : Fin N) (k : ℤ) : ∀ᵐ θ : E, inner ℝ (u i) θ ≠ (k:ℝ)*τ := by
    rw [ae_iff]
    simpa only [not_not] using hyperplane_null (u i) (hu i) ((k:ℝ)*τ)
  have hi' (i : Fin N) : ∀ᵐ θ : E, ∀ k : ℤ, inner ℝ (u i) θ ≠ (k:ℝ)*τ :=
    ae_all_iff.mpr (hi i)
  exact ae_all_iff.mpr hi'

lemma rounded_error_coordinate (u : Fin N → E) {τ : ℝ} (hτ : 0 < τ) (θ : E) (i : Fin N) :
    0 ≤ inner ℝ (u i) θ-rounded u τ θ i ∧ inner ℝ (u i) θ-rounded u τ θ i < τ := by
  have hlo := Int.floor_le (inner ℝ (u i) θ/τ)
  have hhi := Int.lt_floor_add_one (inner ℝ (u i) θ/τ)
  have hl := (le_div_iff₀ hτ).mp hlo
  have hh := (div_lt_iff₀ hτ).mp hhi
  change 0 ≤ inner ℝ (u i) θ-τ*(⌊inner ℝ (u i) θ/τ⌋:ℝ) ∧
    inner ℝ (u i) θ-τ*(⌊inner ℝ (u i) θ/τ⌋:ℝ) < τ
  constructor <;> nlinarith

lemma rounded_error (u : Fin N → E) {τ : ℝ} (hτ : 0 < τ) (θ : E) :
    ‖rounded u τ θ - FrameCharts.chart u θ‖ ≤ Real.sqrt N*τ := by
  have hs : ‖rounded u τ θ - FrameCharts.chart u θ‖^2 ≤ (N:ℝ)*τ^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin N, τ^2 := by
        apply Finset.sum_le_sum; intro i _
        simp only [PiLp.sub_apply, FrameCharts.chart_apply, Real.norm_eq_abs, sq_abs]
        have hh := rounded_error_coordinate u hτ θ i
        nlinarith
      _ = _ := by simp
  have hr := Real.sq_sqrt (Nat.cast_nonneg N)
  have hp : 0 ≤ Real.sqrt N*τ := mul_nonneg (Real.sqrt_nonneg _) hτ.le
  have he : (Real.sqrt N*τ)^2 = (N:ℝ)*τ^2 := by rw [mul_pow,hr]
  nlinarith [norm_nonneg (rounded u τ θ-FrameCharts.chart u θ)]

lemma representative (u : Fin S → Fin N → E) (τ : ℝ) (v : Vertex u τ) :
    ∃ θ ∈ cube 2, regular (u v.val.1) τ θ ∧ coordinate u τ v = rounded (u v.val.1) τ θ := by
  obtain ⟨θ,hθ,hr,hl⟩ := v.property
  refine ⟨θ,hθ,hr,?_⟩
  ext i
  change τ*(v.val.2 i : ℝ) = τ*(integerLabel (u v.val.1) τ θ i : ℝ)
  rw [hl]

end UniformSparsestCut.RoundedCharts

namespace UniformSparsestCut.SourceCharts
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m : ℕ} (f : PivotFamily.PFamily m) (hm : 0 < m)
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "F" => EuclideanSpace ℝ (Fin (m^6))
lemma lower_ge_one (hm2 : 2 ≤ m) : 1≤lower m := by
  have hx : (2:ℝ) ≤ m := by exact_mod_cast hm2
  have hp := pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ m) (show 2≤6 by norm_num)
  unfold lower
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2*m)).mpr
  nlinarith
lemma B_norm_le (hm2 : 2 ≤ m) (s : Fin (m^3)) (x : F) : ‖B f hm s x‖≤‖x‖ := by
  exact (B_norm f hm s x).trans (div_le_self (norm_nonneg _) ((Real.one_le_sqrt).mpr (lower_ge_one hm2)))
lemma rounded_B_error (hm2 : 2 ≤ m) {τ : ℝ} (hτ : 0<τ) (s : Fin (m^3)) (θ : E) :
    ‖B f hm s (RoundedCharts.rounded (u f s) τ θ)-θ‖≤Real.sqrt (m^6:ℕ)*τ := by
  have he : B f hm s (RoundedCharts.rounded (u f s) τ θ)-θ=
      B f hm s (RoundedCharts.rounded (u f s) τ θ-FrameCharts.chart (u f s) θ) := by
    rw [map_sub,B_left]
  rw [he]
  exact (B_norm_le f hm hm2 s _).trans (RoundedCharts.rounded_error _ hτ θ)
lemma rounded_residual_error {τ : ℝ} (hτ : 0<τ) (s : Fin (m^3)) (θ : E) :
    ‖RoundedCharts.rounded (u f s) τ θ-FrameCharts.chart (u f s) (B f hm s (RoundedCharts.rounded (u f s) τ θ))‖≤
      Real.sqrt (m^6:ℕ)*τ := by
  let x := RoundedCharts.rounded (u f s) τ θ
  have he : x-FrameCharts.chart (u f s) (B f hm s x)=
      (x-FrameCharts.chart (u f s) θ)-FrameCharts.chart (u f s) (B f hm s (x-FrameCharts.chart (u f s) θ)) := by
    rw [map_sub,B_left,map_sub]
    abel
  change ‖x-FrameCharts.chart (u f s) (B f hm s x)‖≤_
  rw [he]
  exact (residual_norm f hm s _).trans (RoundedCharts.rounded_error _ hτ θ)
lemma vertex_B_bound (hm2 : 2 ≤ m) {τ : ℝ} (hτ : 0<τ) (v : RoundedCharts.Vertex (u f) τ) :
    ‖B f hm v.val.1 (RoundedCharts.coordinate (u f) τ v)‖≤2*Real.sqrt m+Real.sqrt (m^6:ℕ)*τ := by
  obtain ⟨θ,hθ,hr,hx⟩ := RoundedCharts.representative (u f) τ v
  rw [hx]
  have h := rounded_B_error f hm hm2 hτ v.val.1 θ
  have ht := RoundedCharts.cube_norm (by norm_num : (0:ℝ)≤2) hθ
  exact (norm_le_norm_sub_add _ θ).trans (by linarith)
lemma vertex_residual_bound {τ : ℝ} (hτ : 0<τ) (v : RoundedCharts.Vertex (u f) τ) :
    ‖RoundedCharts.coordinate (u f) τ v-FrameCharts.chart (u f v.val.1) (B f hm v.val.1 (RoundedCharts.coordinate (u f) τ v))‖≤
      Real.sqrt (m^6:ℕ)*τ := by
  obtain ⟨θ,hθ,hr,hx⟩ := RoundedCharts.representative (u f) τ v
  rw [hx]
  exact rounded_residual_error f hm hτ v.val.1 θ
end
end UniformSparsestCut.SourceCharts

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.PositiveKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut
namespace TriangleRepair

variable {ι : Type u1} [Fintype ι]

lemma gram_posSemidef {H : Type u2} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : ι → H) : (Matrix.of (fun i j => ⟪x i, x j⟫_ℝ)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp [real_inner_comm]
  · intro c
    have h := real_inner_self_nonneg (x := ∑ i, c i • x i)
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right] at h
    simp only [Matrix.mulVec, Matrix.of_apply, dotProduct, Finset.mul_sum, Pi.star_apply,
      star_trivial]
    convert h using 1
    try rfl
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [real_inner_comm (x j) (x i)]
    ring

lemma ones_posSemidef : (Matrix.of (fun _ _ : ι => (1 : ℝ))).PosSemidef := by
  convert Matrix.posSemidef_vecMulVec_self_star (fun _ : ι => (1 : ℝ)) using 1
  ext i j
  change (1 : ℝ) = 1 * 1
  ring

lemma entrywise_pow_posSemidef {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (k : ℕ) :
    Matrix.PosSemidef (fun i j => (A i j) ^ k) := by
  induction k with
  | zero => convert (ones_posSemidef (ι := ι)) using 1; rfl
  | succ k hk => convert hk.hadamard hA using 1; rfl

omit [Fintype ι] in
lemma sum_posSemidef {κ : Type u3} (s : Finset κ) (A : κ → Matrix ι ι ℝ)
    (hA : ∀ k ∈ s, (A k).PosSemidef) : (∑ k ∈ s, A k).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix ι ι ℝ).PosSemidef)
  | @insert a s ha hs =>
    rw [Finset.sum_insert ha]
    exact (hA a (Finset.mem_insert_self a s)).add
      (hs (fun k hk => hA k (Finset.mem_insert_of_mem hk)))

lemma posSemidef_of_tendsto {A : ℕ → Matrix ι ι ℝ} {B : Matrix ι ι ℝ}
    (ha : ∀ k, (A k).PosSemidef)
    (hab : ∀ i j, Tendsto (fun k => A k i j) atTop (nhds (B i j))) : B.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial]
    apply tendsto_nhds_unique (hab j i)
    have heq : (fun k => A k j i) = (fun k => A k i j) := by
      funext k
      simpa using (ha k).isHermitian.apply i j
    simpa [heq] using hab i j
  · intro c
    have ht : Tendsto (fun k => star c ⬝ᵥ (A k *ᵥ c)) atTop
        (nhds (star c ⬝ᵥ (B *ᵥ c))) := by
      simp only [dotProduct, Matrix.mulVec]
      exact tendsto_finsetSum _ fun i _ => tendsto_const_nhds.mul
        (tendsto_finsetSum _ fun j _ => (hab i j).mul tendsto_const_nhds)
    exact ge_of_tendsto' ht (fun k => (ha k).dotProduct_mulVec_nonneg c)

lemma entrywise_exp_posSemidef {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    Matrix.PosSemidef (fun i j => Real.exp (A i j)) := by
  let P (k : ℕ) : Matrix ι ι ℝ := fun i j => A i j ^ k / (k.factorial : ℝ)
  have hp (k : ℕ) : (P k).PosSemidef := by
    have h := (entrywise_pow_posSemidef hA k).smul
      (inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) k.factorial))
    convert h using 1
    ext i j
    change A i j ^ k / (k.factorial : ℝ) = (k.factorial : ℝ)⁻¹ * A i j ^ k
    exact div_eq_inv_mul _ _
  apply posSemidef_of_tendsto (A := fun k => ∑ l ∈ Finset.range k, P l)
    (fun k => sum_posSemidef _ _ (fun l _ => hp l))
  intro i j
  have h := (NormedSpace.expSeries_div_hasSum_exp (A i j)).tendsto_sum_nat
  convert h using 1
  · funext k
    exact Matrix.sum_apply i j (Finset.range k) P
  · rw [Real.exp_eq_exp_ℝ]

lemma gaussian_posSemidef {H : Type u4} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : ι → H) {l : ℝ} (hl : 0 < l) :
    Matrix.PosSemidef (fun i j => Real.exp (-‖x i - x j‖ ^ 2 / l)) := by
  let a : ι → ℝ := fun i => Real.exp (-‖x i‖ ^ 2 / l)
  have hgram := (gram_posSemidef x).smul (show 0 ≤ 2 / l by positivity)
  have hexp := entrywise_exp_posSemidef hgram
  have hrank := Matrix.posSemidef_vecMulVec_self_star a
  have heq : (fun i j => Real.exp (-‖x i - x j‖ ^ 2 / l) : Matrix ι ι ℝ) =
      Matrix.vecMulVec a (star a) ⊙ (fun i j => Real.exp ((2 / l) * ⟪x i, x j⟫_ℝ)) := by
    ext i j
    change Real.exp (-‖x i - x j‖ ^ 2 / l) =
      (a i * a j) * Real.exp ((2 / l) * ⟪x i, x j⟫_ℝ)
    simp only [a, ← Real.exp_add]
    congr 1
    rw [norm_sub_sq_real]
    ring
  rw [heq]
  exact hrank.hadamard hexp

open MeasureTheory

lemma integral_posSemidef (K : ℝ → Matrix ι ι ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hK : ∀ l ∈ Set.Icc 0 r, (K l).PosSemidef)
    (hi : ∀ i j, IntervalIntegrable (fun l => K l i j) volume 0 r) :
    Matrix.PosSemidef (fun i j => ∫ l in (0 : ℝ)..r, K l i j) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial]
    apply intervalIntegral.integral_congr
    intro l hl
    simpa using (hK l (by simpa [Set.uIcc_of_le hr] using hl)).isHermitian.apply i j
  · intro c
    have h : 0 ≤ ∫ l in (0 : ℝ)..r, star c ⬝ᵥ (K l *ᵥ c) :=
      intervalIntegral.integral_nonneg hr (fun l hl => (hK l hl).dotProduct_mulVec_nonneg c)
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial] at h ⊢
    have hrow (i : ι) : IntervalIntegrable
        (fun l => ∑ j, K l i j * c j) volume 0 r := by
      convert IntervalIntegrable.sum Finset.univ (fun j _ => (hi i j).mul_const (c j)) using 1
      try rfl
      funext l
      simp only [Finset.sum_apply]
    rw [intervalIntegral.integral_finsetSum (fun i _ => (hrow i).const_mul (c i))] at h
    simp_rw [intervalIntegral.integral_const_mul] at h
    simp_rw [intervalIntegral.integral_finsetSum (fun j _ => (hi _ j).mul_const (c j)),
      intervalIntegral.integral_mul_const] at h
    exact h

open scoped MatrixOrder in

lemma exists_gram {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    ∃ q : ι → EuclideanSpace ℝ ι, ∀ i j, ⟪q i, q j⟫_ℝ = A i j := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  refine ⟨fun i => WithLp.toLp 2 (fun k => B k i), ?_⟩
  intro i j
  rw [hB]
  simp [PiLp.inner_apply, Matrix.mul_apply, Matrix.star_eq_conjTranspose, mul_comm]

end TriangleRepair
end UniformSparsestCut

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.KernelApprox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.KernelApprox

lemma profile_nonneg (t : ℝ) : 0 ≤ profile t := by
  unfold profile
  have h : -1/(2*t^2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  linarith [Real.exp_le_one_iff.mpr h]

lemma profile_le_one (t : ℝ) : profile t ≤ 1 := by
  unfold profile
  linarith [Real.exp_pos (-1/(2*t^2))]

lemma profile_le_inv_sq (t : ℝ) : profile t ≤ 1/(2*t^2) := by
  have h := Real.add_one_le_exp (-1/(2*t^2))
  unfold profile
  rw [neg_div] at h ⊢
  linarith

lemma profile_pos {t : ℝ} (ht : t ≠ 0) : 0 < profile t := by
  unfold profile
  have h : -1/(2*t^2) < 0 := div_neg_of_neg_of_pos (by norm_num) (by positivity)
  linarith [Real.exp_lt_one_iff.mpr h]

lemma profile_measurable : Measurable profile := by unfold profile; fun_prop

lemma profile_integrable_lower : IntegrableOn profile (Ioc 0 1) := by
  apply (integrableOn_const (C := (1 : ℝ)) (s := Ioc (0 : ℝ) 1) (by simp)).mono'
    profile_measurable.aestronglyMeasurable
  filter_upwards with t
  simpa only [Real.norm_eq_abs, abs_of_nonneg (profile_nonneg t)] using profile_le_one t

lemma profile_integrable_upper : IntegrableOn profile (Ioi 1) := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 1)).const_mul (1/2 : ℝ)
  apply hi.mono' profile_measurable.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 1 < t at ht
  have he : (1/2 : ℝ)*t^(-2 : ℝ) = 1/(2*t^2) := by
    rw [Real.rpow_neg (by linarith : 0 ≤ t), Real.rpow_two]
    ring
  simpa only [Real.norm_eq_abs, abs_of_nonneg (profile_nonneg t), he] using profile_le_inv_sq t

lemma profile_integrable : IntegrableOn profile (Ioi 0) := by
  have h := profile_integrable_lower.union profile_integrable_upper
  simpa only [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] using h

lemma cstar_pos : 0 < cstar := by
  have hp : 0 < ∫ t in Ioi (0 : ℝ), profile t := by
    apply (integral_pos_iff_support_of_nonneg_ae _ profile_integrable).mpr
    · have hs : Ioi (0 : ℝ) ⊆ Function.support profile := by
        intro t ht
        exact ne_of_gt (profile_pos (ne_of_gt ht))
      have hc : (volume.restrict (Ioi (0 : ℝ))) (Ioi (0 : ℝ)) ≠ 0 := by simp
      exact bot_lt_iff_ne_bot.mpr (ne_bot_of_le_ne_bot hc (measure_mono hs))
    · filter_upwards with t using profile_nonneg t
  exact mul_pos (by norm_num) hp

lemma scaled_eq_profile (r t : ℝ) : scaled r t = profile (t/r) := by
  by_cases hr : r = 0
  · simp [hr, scaled, profile]
  by_cases ht : t = 0
  · simp [ht, scaled, profile]
  unfold scaled profile
  congr 2
  field_simp

lemma scaled_nonneg (r t : ℝ) : 0 ≤ scaled r t := by
  rw [scaled_eq_profile]; exact profile_nonneg _

lemma scaled_le_one (r t : ℝ) : scaled r t ≤ 1 := by
  rw [scaled_eq_profile]; exact profile_le_one _

lemma scaled_le_tail (r t : ℝ) : scaled r t ≤ r^2/(2*t^2) := by
  have h := Real.add_one_le_exp (-r^2/(2*t^2))
  unfold scaled
  rw [neg_div] at h ⊢
  linarith

lemma scaled_measurable (r : ℝ) : Measurable (scaled r) := by unfold scaled; fun_prop

lemma scaled_integrable_lower (r : ℝ) {a : ℝ} (_ha : 0 ≤ a) :
    IntegrableOn (scaled r) (Ioc 0 a) := by
  apply (integrableOn_const (C := (1 : ℝ)) (s := Ioc (0 : ℝ) a) (by simp)).mono'
    (scaled_measurable r).aestronglyMeasurable
  filter_upwards with t
  simpa only [Real.norm_eq_abs, abs_of_nonneg (scaled_nonneg r t)] using scaled_le_one r t

lemma scaled_integrable_upper (r : ℝ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (scaled r) (Ioi a) := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha).const_mul (r^2/2)
  apply hi.mono' (scaled_measurable r).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change a < t at ht
  have he : (r^2/2)*t^(-2 : ℝ) = r^2/(2*t^2) := by
    rw [Real.rpow_neg (by linarith : 0 ≤ t), Real.rpow_two]
    ring
  simpa only [Real.norm_eq_abs, abs_of_nonneg (scaled_nonneg r t), he] using scaled_le_tail r t

lemma scaled_integrable (r : ℝ) : IntegrableOn (scaled r) (Ioi 0) := by
  have h := (scaled_integrable_lower r (by norm_num : (0 : ℝ) ≤ 1)).union
    (scaled_integrable_upper r (by norm_num : (0 : ℝ) < 1))
  simpa only [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] using h

lemma full_integral {r : ℝ} (hr : 0 ≤ r) :
    2 * (∫ t in Ioi (0 : ℝ), scaled r t) = cstar*r := by
  rcases eq_or_lt_of_le hr with hz | hr
  · simp [← hz, scaled]
  simp_rw [scaled_eq_profile, div_eq_inv_mul]
  rw [integral_comp_mul_left_Ioi profile 0 (inv_pos.mpr hr)]
  simp only [mul_zero, inv_inv, smul_eq_mul, cstar]
  ring

lemma lower_tail_bound (r : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    (∫ t in Ioc (0 : ℝ) a, scaled r t) ≤ a := by
  have h := integral_mono (scaled_integrable_lower r ha)
    (integrableOn_const (C := (1 : ℝ)) (s := Ioc (0 : ℝ) a) (by simp))
    (fun t => scaled_le_one r t)
  simpa [integral_const, Real.volume_real_Ioc, ha] using h

lemma upper_tail_bound (r : ℝ) {b : ℝ} (hb : 0 < b) :
    (∫ t in Ioi b, scaled r t) ≤ r^2/(2*b) := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hb).const_mul (r^2/2)
  calc
    _ ≤ ∫ t in Ioi b, (r^2/2)*t^(-2 : ℝ) := by
      apply integral_mono_ae (scaled_integrable_upper r hb) hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change b < t at ht
      rw [Real.rpow_neg (by linarith : 0 ≤ t), Real.rpow_two]
      exact (scaled_le_tail r t).trans_eq (by ring)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hb]
      norm_num
      rw [Real.rpow_neg_one]
      ring

lemma truncated_error {r a b : ℝ} (hr : 0 ≤ r) (ha : 0 < a) (hab : a ≤ b) :
    |2 * (∫ t in Ioc a b, scaled r t) - cstar*r| ≤ 2*a + r^2/b := by
  have hb : 0 < b := ha.trans_le hab
  have hi1 := scaled_integrable_lower r ha.le
  have hi2 : IntegrableOn (scaled r) (Ioc a b) :=
    (scaled_integrable r).mono_set (fun t ht => ha.trans ht.1)
  have hi3 := scaled_integrable_upper r hb
  have he : (∫ t in Ioi (0 : ℝ), scaled r t) =
      (∫ t in Ioc (0 : ℝ) a, scaled r t) + (∫ t in Ioc a b, scaled r t) +
      ∫ t in Ioi b, scaled r t := by
    rw [← Ioc_union_Ioi_eq_Ioi hb.le, setIntegral_union]
    · rw [← Ioc_union_Ioc_eq_Ioc ha.le hab, setIntegral_union]
      · exact Ioc_disjoint_Ioc_of_le le_rfl
      · exact measurableSet_Ioc
      · exact hi1
      · exact hi2
    · exact Ioc_disjoint_Ioi_same
    · exact measurableSet_Ioi
    · exact scaled_integrable_lower r hb.le
    · exact hi3
  have hx := full_integral hr
  rw [he] at hx
  have hn1 : 0 ≤ ∫ t in Ioc (0 : ℝ) a, scaled r t := integral_nonneg (fun _ => scaled_nonneg _ _)
  have hn3 : 0 ≤ ∫ t in Ioi b, scaled r t := integral_nonneg (fun _ => scaled_nonneg _ _)
  have hu1 := lower_tail_bound r ha.le
  have hu3 := upper_tail_bound r hb
  have he' : r^2/b = 2*(r^2/(2*b)) := by ring
  rw [abs_of_nonpos (by linarith), he']
  linarith

end UniformSparsestCut.KernelApprox

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.CommonKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.CommonKernel
open MeasureTheory Set
open scoped RealInnerProductSpace BigOperators Matrix

variable {ι : Type u1} [Fintype ι]

lemma integral_posSemidef (K : ℝ → Matrix ι ι ℝ) {a b : ℝ} (hab : a ≤ b)
    (hK : ∀ t ∈ Icc a b, (K t).PosSemidef)
    (hi : ∀ i j, IntervalIntegrable (fun t => K t i j) volume a b) :
    Matrix.PosSemidef (fun i j => ∫ t in a..b, K t i j) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial]
    apply intervalIntegral.integral_congr
    intro t ht
    simpa using (hK t (by simpa [uIcc_of_le hab] using ht)).isHermitian.apply i j
  · intro c
    have h : 0 ≤ ∫ t in a..b, star c ⬝ᵥ (K t *ᵥ c) :=
      intervalIntegral.integral_nonneg hab (fun t ht => (hK t ht).dotProduct_mulVec_nonneg c)
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial] at h ⊢
    have hrow (i : ι) : IntervalIntegrable (fun t => ∑ j, K t i j*c j) volume a b := by
      convert IntervalIntegrable.sum Finset.univ (fun j _ => (hi i j).mul_const (c j)) using 1 <;>
        first | rfl | (funext t; simp only [Finset.sum_apply])
    rw [intervalIntegral.integral_finsetSum (fun i _ => (hrow i).const_mul (c i))] at h
    simp_rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (fun j _ => (hi _ j).mul_const (c j)),
      intervalIntegral.integral_mul_const] at h
    exact h

lemma circle_inner (t v q p : ℝ) :
    inner ℝ (circle t q) (circle v p) =
      (1+q*p)*Real.cos (v-t)+(q-p)*Real.sin (v-t) := by
  simp [circle, PiLp.inner_apply, Fin.sum_univ_two, Real.cos_sub, Real.sin_sub]

  ring

variable {E : Type u2} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {κ : Type u3} [Fintype κ]

omit [Fintype ι] [InnerProductSpace ℝ E] in
lemma gaussian_integrable (θ : ι → E) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (v w : ι) :
    IntervalIntegrable (fun σ => Real.exp (-‖θ v-θ w‖^2/(2*σ^2))) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply Real.continuous_exp.comp_continuousOn
  apply continuousOn_const.div (by fun_prop)
  intro σ hσ
  have hp : 0 < σ := ha.trans_le hσ.1
  positivity

omit [Fintype ι] [Fintype κ] in
lemma circle_integrable (g : κ → E) (θ : ι → E) (α : ι → κ → ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (v w : ι) (k : κ) :
    IntervalIntegrable (fun σ => inner ℝ (circle (inner ℝ (g k) (θ v)/σ) (α v k))
      (circle (inner ℝ (g k) (θ w)/σ) (α w k))/σ) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  have hne : ∀ σ ∈ Icc a b, σ ≠ 0 := fun σ hσ => (ha.trans_le hσ.1).ne'
  have h1 : ContinuousOn (fun σ : ℝ => inner ℝ (g k) (θ v)/σ) (Icc a b) :=
    continuousOn_const.div continuousOn_id hne
  have h2 : ContinuousOn (fun σ : ℝ => inner ℝ (g k) (θ w)/σ) (Icc a b) :=
    continuousOn_const.div continuousOn_id hne
  simp only [circle_inner]
  exact (((continuousOn_const.mul (Real.continuous_cos.comp_continuousOn (h2.sub h1))).add
    (continuousOn_const.mul (Real.continuous_sin.comp_continuousOn (h2.sub h1)))).div continuousOn_id hne)

lemma gram_posSemidef (g : κ → E) (θ : ι → E) (α : ι → κ → ℝ)
    {M ε a b : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (ha : 0 < a) (hab : a ≤ b) :
    (gram g θ α M ε a b).PosSemidef := by
  have hG := integral_posSemidef
    (fun σ v w => Real.exp (-‖θ v-θ w‖^2/(2*σ^2))) hab
    (fun σ hσ => TriangleRepair.gaussian_posSemidef θ (by have := ha.trans_le hσ.1; positivity))
    (gaussian_integrable θ ha hab)
  have hC (k : κ) := integral_posSemidef
    (fun σ v w => inner ℝ (circle (inner ℝ (g k) (θ v)/σ) (α v k))
      (circle (inner ℝ (g k) (θ w)/σ) (α w k))/σ) hab
    (fun σ hσ => by
      have h := (TriangleRepair.gram_posSemidef
        (fun v => circle (inner ℝ (g k) (θ v)/σ) (α v k))).smul
        (inv_nonneg.mpr (ha.trans_le hσ.1).le)
      change Matrix.PosSemidef (fun v w => σ⁻¹ *
        inner ℝ (circle (inner ℝ (g k) (θ v)/σ) (α v k))
          (circle (inner ℝ (g k) (θ w)/σ) (α w k))) at h
      simpa only [div_eq_inv_mul] using h)
    (fun v w => circle_integrable g θ α ha hab v w k)
  have hS := TriangleRepair.sum_posSemidef Finset.univ _ (fun k _ => hC k)
  convert (hG.smul hM).add (hS.smul hε) using 1
  ext v w
  change M * _ + ε * (∑ k, _) = M * _ + ε * ((∑ k : κ, (_ : Matrix ι ι ℝ)) v w)
  congr 2
  symm
  exact Matrix.sum_apply v w Finset.univ _

lemma gram_realization (g : κ → E) (θ : ι → E) (α : ι → κ → ℝ)
    {M ε a b : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (ha : 0 < a) (hab : a ≤ b) :
    ∃ P : ι → EuclideanSpace ℝ ι, ∀ v w, inner ℝ (P v) (P w) = gram g θ α M ε a b v w :=
  TriangleRepair.exists_gram (gram_posSemidef g θ α hM hε ha hab)

end UniformSparsestCut.CommonKernel

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.Profiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.Profile
variable {E : Type u1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type u2} [Fintype ι]

lemma pairing_hasDeriv (g : ι → E) (q ε σ : ℝ) (θ η v : E)
    (α β δ : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t => pairing g q ε σ (θ+t • v) η (fun i => α i+t*δ i) β)
      (differential g q ε σ (θ+t • v) η v (fun i => α i+t*δ i) β δ) t := by
  have hx : HasDerivAt (fun t : ℝ => η-(θ+t • v)) (-v) t :=
    by simpa using (((hasDerivAt_id t).smul_const v).const_add θ).const_sub η
  have hn := hx.norm_sq.neg.div_const (2*σ^2)
  have he := hn.exp.const_mul q
  have hi (i : ι) : HasDerivAt (fun t : ℝ => inner ℝ (g i) (η-(θ+t • v))/σ)
      (-inner ℝ (g i) v/σ) t := by
    convert ((innerSL ℝ (g i)).hasFDerivAt.comp_hasDerivAt t hx).div_const σ using 1 <;> try rfl
    simp only [innerSL_apply_apply, inner_neg_right]
  have hd (i : ι) : HasDerivAt (fun t : ℝ => α i+t*δ i) (δ i) t := by
    simpa using ((hasDerivAt_id t).mul_const (δ i)).const_add (α i)
  have hs (i : ι) := ((((hd i).mul_const (β i)).const_add 1).mul (hi i).cos).add
    (((hd i).sub_const (β i)).mul (hi i).sin)
  have hsum := (HasDerivAt.sum (u := Finset.univ) (fun i _ => hs i)).const_mul (ε/σ)
  convert he.add hsum using 1 <;> try rfl
  · funext z; simp [pairing, Finset.sum_apply]
  · simp only [differential, real_inner_smul_left, inner_neg_right, Pi.neg_apply]
    congr 1
    · ring
    · congr 1; apply Finset.sum_congr rfl; intro i _; ring

lemma differential_correction (g : ι → E) {q ε σ : ℝ} (hε : 0 ≤ ε) (hσ : 0 < σ)
    (θ η v : E) (α β δ : ι → ℝ) :
    |differential g q ε σ θ η v α β δ - differential g q ε σ θ η v 0 0 δ| ≤
      ε/σ*(∑ i, (|δ i| * |β i| + |inner ℝ (g i) v|/σ*(|α i| * |β i| + |α i| + |β i|))) := by
  have heq : differential g q ε σ θ η v α β δ - differential g q ε σ θ η v 0 0 δ =
      ε/σ*(∑ i, (δ i*β i*Real.cos (inner ℝ (g i) (η-θ)/σ) +
       (inner ℝ (g i) v/σ)*(α i*β i*Real.sin (inner ℝ (g i) (η-θ)/σ)-
         α i*Real.cos (inner ℝ (g i) (η-θ)/σ)+β i*Real.cos (inner ℝ (g i) (η-θ)/σ)))) := by
    unfold differential
    simp only [Pi.zero_apply, mul_zero, zero_mul, add_zero, sub_zero]
    rw [show ∀ a b c : ℝ, (a+b)-(a+c)=b-c by intros; ring]
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [heq, abs_mul, abs_of_nonneg (div_nonneg hε hσ.le)]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hε hσ.le)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  let t := inner ℝ (g i) (η-θ)/σ
  have hc : |Real.cos t| ≤ 1 := Real.abs_cos_le_one t
  have hs : |Real.sin t| ≤ 1 := Real.abs_sin_le_one t
  have hp : |α i*β i*Real.sin t-α i*Real.cos t+β i*Real.cos t| ≤
      |α i| * |β i| + |α i| + |β i| := by
    calc
      _ ≤ |α i*β i*Real.sin t| + |α i*Real.cos t| + |β i*Real.cos t| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ _ := by
        simp only [abs_mul]
        exact add_le_add (add_le_add
          (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hs)
          (mul_le_of_le_one_right (abs_nonneg _) hc))
          (mul_le_of_le_one_right (abs_nonneg _) hc)
  calc
    _ ≤ |δ i*β i*Real.cos t| + |(inner ℝ (g i) v/σ)*
        (α i*β i*Real.sin t-α i*Real.cos t+β i*Real.cos t)| := abs_add_le _ _
    _ = |δ i| * |β i| * |Real.cos t| + |inner ℝ (g i) v|/σ*
        |α i*β i*Real.sin t-α i*Real.cos t+β i*Real.cos t| := by
      simp only [abs_mul, abs_div, abs_of_pos hσ]
    _ ≤ _ := add_le_add
      (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hc)
      (mul_le_mul_of_nonneg_left hp (div_nonneg (abs_nonneg _) hσ.le))

end UniformSparsestCut.Profile

namespace UniformSparsestCut.Profile
variable {E : Type u3} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {S : Type u4} {N : Type u5} [Fintype S] [DecidableEq S] [Fintype N]

lemma active_cancellation (g : S → N → E) (s : S) (q ε σ k : ℝ)
    (θ η v : E) (h : N → ℝ) (hq : q ≠ 0) (hσ : σ ≠ 0)
    (hk : k = q^2/(Fintype.card N : ℝ)) (hε : ε ≠ 0) :
    differential (fun j : S × N => g j.1 j.2) q ε σ θ η v 0 0
      (fun j => if j.1 = s then k/ε*(h j.2-inner ℝ (g j.1 j.2) v/q) else 0) =
    k/σ*(∑ i, h i*Real.sin (inner ℝ (g s i) (η-θ)/σ)) +
    q/σ*inner ℝ
      (Real.exp (-‖(σ⁻¹:ℝ) • (η-θ)‖^2/2) • ((σ⁻¹:ℝ) • (η-θ)) -
       ((Fintype.card N : ℝ)⁻¹) • ∑ i, Real.sin (inner ℝ (g s i) (η-θ)/σ) • g s i) v +
    ε/σ^2*(∑ j : S × N, inner ℝ (g j.1 j.2) v*Real.sin (inner ℝ (g j.1 j.2) (η-θ)/σ)) := by
  have hn : ‖(σ⁻¹:ℝ) • (η-θ)‖^2 = ‖η-θ‖^2/σ^2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow]; ring
  have he : -(‖η-θ‖^2/σ^2)/2 = -‖η-θ‖^2/(2*σ^2) := by ring
  simp only [differential, Pi.zero_apply, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add, one_mul, Finset.sum_add_distrib]
  have hd : (∑ j : S × N, (if j.1 = s then k/ε*(h j.2-inner ℝ (g j.1 j.2) v/q) else 0) *
      Real.sin (inner ℝ (g j.1 j.2) (η-θ)/σ)) =
      k/ε*∑ i, (h i-inner ℝ (g s i) v/q)*Real.sin (inner ℝ (g s i) (η-θ)/σ) := by
    simp only [Fintype.sum_prod_type, ite_mul, zero_mul]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  rw [hd]
  simp only [inner_sub_left, real_inner_smul_left, sum_inner, hn, he]
  simp only [sub_mul, Finset.sum_sub_distrib, div_mul_eq_mul_div,
    ← Finset.sum_div]
  have hs : (∑ i, Real.sin (inner ℝ (g s i) (η-θ)/σ)*inner ℝ (g s i) v) =
      ∑ i, inner ℝ (g s i) v*Real.sin (inner ℝ (g s i) (η-θ)/σ) := by
    apply Finset.sum_congr rfl; intros; ring
  rw [hs, hk]
  field_simp
  ring

lemma active_bound (g : S → N → E) (s : S) {q ε σ k γ G : ℝ}
    (θ η v : E) (h : N → ℝ) (hq : 0 < q) (hε : 0 < ε) (hσ : 0 < σ)
    (hk : k = q^2/(Fintype.card N : ℝ)) (hg : ∀ s i, ‖g s i‖ ≤ G)
    (hf : ‖Real.exp (-‖(σ⁻¹:ℝ) • (η-θ)‖^2/2) • ((σ⁻¹:ℝ) • (η-θ)) -
       ((Fintype.card N : ℝ)⁻¹) • ∑ i, Real.sin (inner ℝ (g s i) (η-θ)/σ) • g s i‖ ≤ γ) :
    |differential (fun j : S × N => g j.1 j.2) q ε σ θ η v 0 0
      (fun j => if j.1 = s then k/ε*(h j.2-inner ℝ (g j.1 j.2) v/q) else 0)| ≤
      k/σ*(∑ i, |h i|) + q*γ/σ*‖v‖ +
        ε/σ^2*((Fintype.card S : ℝ)*(Fintype.card N : ℝ)*G)*‖v‖ := by
  have hk0 : 0 ≤ k := by rw [hk]; positivity
  rw [active_cancellation g s q ε σ k θ η v h hq.ne' hσ.ne' hk hε.ne']
  have hsum : |∑ i, h i*Real.sin (inner ℝ (g s i) (η-θ)/σ)| ≤ ∑ i, |h i| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  have hfour := (abs_real_inner_le_norm _ v).trans (mul_le_mul_of_nonneg_right hf (norm_nonneg v))
  have hglobal : |∑ j : S × N, inner ℝ (g j.1 j.2) v*Real.sin (inner ℝ (g j.1 j.2) (η-θ)/σ)| ≤
      (Fintype.card S : ℝ)*(Fintype.card N : ℝ)*G*‖v‖ := by
    calc
      _ ≤ ∑ j : S × N, |inner ℝ (g j.1 j.2) v*Real.sin (inner ℝ (g j.1 j.2) (η-θ)/σ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : S × N, G*‖v‖ := by
        apply Finset.sum_le_sum; intro j _
        rw [abs_mul]
        exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)).trans
          ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hg j.1 j.2) (norm_nonneg v)))
      _ = _ := by simp [Fintype.card_prod]; ring
  calc
    _ ≤ |k/σ*(∑ i, h i*Real.sin (inner ℝ (g s i) (η-θ)/σ))| +
        |q/σ*inner ℝ (Real.exp (-‖(σ⁻¹:ℝ) • (η-θ)‖^2/2) • ((σ⁻¹:ℝ) • (η-θ)) -
       ((Fintype.card N : ℝ)⁻¹) • ∑ i, Real.sin (inner ℝ (g s i) (η-θ)/σ) • g s i) v| +
       |ε/σ^2*(∑ j : S × N, inner ℝ (g j.1 j.2) v*Real.sin (inner ℝ (g j.1 j.2) (η-θ)/σ))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ k/σ*(∑ i, |h i|) + q/σ*(γ*‖v‖) +
        ε/σ^2*((Fintype.card S : ℝ)*(Fintype.card N : ℝ)*G*‖v‖) := by
      simp only [abs_mul, abs_of_nonneg (div_nonneg hk0 hσ.le),
        abs_of_pos (div_pos hq hσ), abs_of_pos (div_pos hε (sq_pos_of_pos hσ))]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hsum (div_nonneg hk0 hσ.le))
        (mul_le_mul_of_nonneg_left hfour (div_nonneg hq.le hσ.le)))
        (mul_le_mul_of_nonneg_left hglobal (div_nonneg hε.le (sq_nonneg σ)))
    _ = _ := by ring

end UniformSparsestCut.Profile

namespace UniformSparsestCut.Profile
variable {E : Type u6} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type u7} [Fintype ι]

lemma pairing_continuousOn (g : ι → E) (q ε : ℝ) (θ η : E) (α β : ι → ℝ)
    {a b : ℝ} (ha : 0 < a) : ContinuousOn (fun σ => pairing g q ε σ θ η α β) (Icc a b) := by
  have hn : ∀ σ ∈ Icc a b, σ ≠ 0 := fun σ h => (ha.trans_le h.1).ne'
  have hnp : ∀ σ ∈ Icc a b, 2*σ^2 ≠ 0 := fun σ h => mul_ne_zero (by norm_num) (pow_ne_zero _ (hn σ h))
  unfold pairing
  refine (continuousOn_const.mul (Real.continuous_exp.comp_continuousOn
    (continuousOn_const.div (by fun_prop) hnp))).add ?_
  apply (continuousOn_const.div continuousOn_id hn).mul
  apply continuousOn_finsetSum
  intro i _
  have hc := continuousOn_const.div continuousOn_id hn (f := fun _ : ℝ => inner ℝ (g i) (η-θ))
  exact (continuousOn_const.mul (Real.continuous_cos.comp_continuousOn hc)).add
    (continuousOn_const.mul (Real.continuous_sin.comp_continuousOn hc))

lemma pairing_integrable (g : ι → E) (q ε : ℝ) (θ η : E) (α β : ι → ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun σ => pairing g q ε σ θ η α β) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact pairing_continuousOn g q ε θ η α β ha

lemma pairing_correction (g : ι → E) {q ε σ : ℝ} (hε : 0 ≤ ε) (hσ : 0 < σ)
    (θ η : E) (α β : ι → ℝ) :
    |pairing g q ε σ θ η α β - pairing g q ε σ θ η 0 0| ≤
      ε/σ*∑ i, (|α i| * |β i|+|α i|+|β i|) := by
  have he : pairing g q ε σ θ η α β - pairing g q ε σ θ η 0 0 =
      ε/σ*∑ i, (α i*β i*Real.cos (inner ℝ (g i) (η-θ)/σ) +
        α i*Real.sin (inner ℝ (g i) (η-θ)/σ)-β i*Real.sin (inner ℝ (g i) (η-θ)/σ)) := by
    unfold pairing
    simp only [Pi.zero_apply, mul_zero, add_zero, zero_mul, sub_zero, one_mul]
    rw [show ∀ c d e : ℝ, (c+d)-(c+e)=d-e by intros; ring, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1; apply Finset.sum_congr rfl; intro i _; ring
  rw [he, abs_mul, abs_of_nonneg (div_nonneg hε hσ.le)]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hε hσ.le)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  calc
    _ ≤ |α i*β i*Real.cos (inner ℝ (g i) (η-θ)/σ)| +
        |α i*Real.sin (inner ℝ (g i) (η-θ)/σ)|+|β i*Real.sin (inner ℝ (g i) (η-θ)/σ)| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by
      simp only [abs_mul]
      exact add_le_add (add_le_add
        (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.abs_cos_le_one _))
        (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)))
        (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))

lemma kernel_correction (g : ι → E) {q ε a b A : ℝ}
    (hε : 0 ≤ ε) (ha : 0 < a) (hab : a ≤ b) (hA : 0 ≤ A)
    (θ η : E) (α β : ι → ℝ) (hα : ∀ i, |α i| ≤ A) (hβ : ∀ i, |β i| ≤ A) :
    |kernel g q ε a b θ η α β - kernel g q ε a b θ η 0 0| ≤
      ε*(Fintype.card ι : ℝ)*(A^2+2*A)*Real.log (b/a) := by
  have hip := pairing_integrable g q ε θ η α β ha hab
  have hiz := pairing_integrable g q ε θ η 0 0 ha hab
  have hiinv : IntervalIntegrable (fun σ : ℝ => σ⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact continuousOn_id.inv₀ (fun σ h => (ha.trans_le h.1).ne')
  have hi := hiinv.const_mul (ε*(Fintype.card ι : ℝ)*(A^2+2*A))
  unfold kernel
  rw [← intervalIntegral.integral_sub hip hiz]
  calc
    _ ≤ ∫ σ in a..b, |pairing g q ε σ θ η α β-pairing g q ε σ θ η 0 0| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ σ in a..b, ε*(Fintype.card ι : ℝ)*(A^2+2*A)*σ⁻¹ := by
      apply intervalIntegral.integral_mono_on hab (hip.sub hiz).abs hi
      intro σ hσ
      have hp := ha.trans_le hσ.1
      have hs : (∑ i, (|α i| * |β i|+|α i|+|β i|)) ≤ (Fintype.card ι : ℝ)*(A^2+2*A) := by
        calc
          _ ≤ ∑ _i : ι, (A^2+2*A) := by
            apply Finset.sum_le_sum; intro i _
            have hm := mul_le_mul (hα i) (hβ i) (abs_nonneg _) hA
            nlinarith [hα i, hβ i]
          _ = _ := by simp; ring
      calc
        _ ≤ ε/σ*∑ i, (|α i| * |β i|+|α i|+|β i|) := pairing_correction g hε hp θ η α β
        _ ≤ ε/σ*((Fintype.card ι : ℝ)*(A^2+2*A)) := mul_le_mul_of_nonneg_left hs (div_nonneg hε hp.le)
        _ = _ := by ring
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha (ha.trans_le hab)]

lemma integral_inv_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ σ in a..b, (σ^2)⁻¹) = a⁻¹-b⁻¹ := by
  have hd (σ : ℝ) (hσ : σ ∈ Icc a b) : HasDerivAt (fun σ : ℝ => -σ⁻¹) ((σ^2)⁻¹) σ := by
    convert ((hasDerivAt_id σ).inv (ha.trans_le hσ.1).ne').neg using 1 <;> try rfl
    simp; ring
  have hi : IntervalIntegrable (fun σ : ℝ => (σ^2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact (continuousOn_id.pow 2).inv₀ (fun σ h => pow_ne_zero _ (ha.trans_le h.1).ne')
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun σ hσ => hd σ (by simpa only [uIcc_of_le hab] using hσ)) hi
  convert h using 1 ; ring

lemma kernel_segment_bound (g : ι → E) {q ε a b C D : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hD : 0 ≤ D) (θ η v : E) (α β δ : ι → ℝ)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, ∀ σ ∈ Icc a b,
      |differential g q ε σ (θ+t • v) η v (fun i => α i+t*δ i) β δ| ≤ C/σ+D/σ^2) :
    |kernel g q ε a b (θ+v) η (fun i => α i+δ i) β-kernel g q ε a b θ η α β| ≤
      C*Real.log (b/a)+D/a := by
  have hip := pairing_integrable g q ε (θ+v) η (fun i => α i+δ i) β ha hab
  have hiz := pairing_integrable g q ε θ η α β ha hab
  have hii : IntervalIntegrable (fun σ : ℝ => σ⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact continuousOn_id.inv₀ (fun σ h => (ha.trans_le h.1).ne')
  have hiis : IntervalIntegrable (fun σ : ℝ => (σ^2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact (continuousOn_id.pow 2).inv₀ (fun σ h => pow_ne_zero _ (ha.trans_le h.1).ne')
  have hi := (hii.const_mul C).add (hiis.const_mul D)
  have hbound (σ : ℝ) (hσ : σ ∈ Icc a b) :
      |pairing g q ε σ (θ+v) η (fun i => α i+δ i) β-pairing g q ε σ θ η α β| ≤ C/σ+D/σ^2 := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun t ht => (pairing_hasDeriv g q ε σ θ η v α β δ t).hasDerivWithinAt)
      (fun t ht => by simpa only [Real.norm_eq_abs] using hd t ⟨ht.1, ht.2.le⟩ σ hσ)
    simpa only [one_smul, one_mul, zero_smul, add_zero, zero_mul, Real.norm_eq_abs] using h
  unfold kernel
  rw [← intervalIntegral.integral_sub hip hiz]
  calc
    _ ≤ ∫ σ in a..b, |pairing g q ε σ (θ+v) η (fun i => α i+δ i) β-pairing g q ε σ θ η α β| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ σ in a..b, C*σ⁻¹+D*(σ^2)⁻¹ := by
      apply intervalIntegral.integral_mono_on hab (hip.sub hiz).abs hi
      intro σ hσ; simpa only [div_eq_mul_inv] using hbound σ hσ
    _ = C*Real.log (b/a)+D*(a⁻¹-b⁻¹) := by
      rw [intervalIntegral.integral_add (hii.const_mul C) (hiis.const_mul D),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_inv_of_pos ha (ha.trans_le hab), integral_inv_sq ha hab]
    _ ≤ _ := by
      simp only [div_eq_mul_inv]
      have := mul_nonneg hD (inv_nonneg.mpr (ha.trans_le hab).le)
      nlinarith

end UniformSparsestCut.Profile

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.MetricKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.MetricKernel
open MeasureTheory Set
open scoped RealInnerProductSpace BigOperators
variable {E : Type u1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type u2} {κ : Type u3} [Fintype ι] [Fintype κ]

omit [Fintype ι] in
lemma gram_eq_kernel (g : κ → E) (θ : ι → E) (α : ι → κ → ℝ)
    (q ε : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (v w : ι) :
    CommonKernel.gram g θ α q ε a b v w =
      Profile.kernel g q ε a b (θ v) (θ w) (α v) (α w) := by
  have hf (k : κ) := CommonKernel.circle_integrable g θ α ha hab v w k
  have hi := CommonKernel.gaussian_integrable θ ha hab v w
  have hiS : IntervalIntegrable (fun σ => ∑ i, inner ℝ
      (CommonKernel.circle (inner ℝ (g i) (θ v)/σ) (α v i))
      (CommonKernel.circle (inner ℝ (g i) (θ w)/σ) (α w i))/σ) volume a b := by
    convert IntervalIntegrable.sum Finset.univ (fun i _ => hf i) using 1 <;>
      first | rfl | (funext σ; simp only [Finset.sum_apply])
  unfold CommonKernel.gram Profile.kernel Profile.pairing
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_finsetSum (fun k _ => hf k),
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (hi.const_mul q)
      (hiS.const_mul ε)]
  apply intervalIntegral.integral_congr
  intro σ hσ
  rw [norm_sub_rev (θ w) (θ v)]

  simp only [CommonKernel.circle_inner, inner_sub_right, sub_div, ← Finset.sum_div]
  ring

lemma base_pairing (g : κ → E) (q ε σ : ℝ) (θ η : E) :
    Profile.pairing g q ε σ θ θ 0 0 + Profile.pairing g q ε σ η η 0 0 -
      2*Profile.pairing g q ε σ θ η 0 0 =
      2*q*KernelApprox.scaled ‖η-θ‖ σ +
        2*ε/σ*∑ i, (1-Real.cos (inner ℝ (g i) (η-θ)/σ)) := by
  simp only [Profile.pairing, Pi.zero_apply, mul_zero, zero_mul, add_zero,
     sub_self, norm_zero, zero_pow (by decide : (2:ℕ) ≠ 0), neg_zero,
    zero_div, Real.exp_zero, inner_zero_right, Real.cos_zero, Real.sin_zero, one_mul,
    Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_sub_distrib, KernelApprox.scaled]
  ring

omit [InnerProductSpace ℝ E] in
lemma gaussian_scaled_integrable (θ η : E) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (KernelApprox.scaled ‖η-θ‖) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  unfold KernelApprox.scaled
  apply continuousOn_const.sub
  apply Real.continuous_exp.comp_continuousOn
  exact continuousOn_const.div (by fun_prop) (fun σ hσ => by have := ha.trans_le hσ.1; positivity)

omit [Fintype κ] in
lemma cos_integrable (g : κ → E) (θ η : E) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (i : κ) :
    IntervalIntegrable (fun σ => (1-Real.cos (inner ℝ (g i) (η-θ)/σ))/σ) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  have hn : ∀ σ ∈ Icc a b, σ ≠ 0 := fun σ hσ => (ha.trans_le hσ.1).ne'
  exact (continuousOn_const.sub (Real.continuous_cos.comp_continuousOn
    (continuousOn_const.div continuousOn_id hn))).div continuousOn_id hn

omit [Fintype κ] in
lemma cos_integral_bound (g : κ → E) (θ η : E) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (i : κ) :
    |∫ σ in a..b, (1-Real.cos (inner ℝ (g i) (η-θ)/σ))/σ| ≤ 2*Real.log (b/a) := by
  have hi := cos_integrable g θ η ha hab i
  have hii : IntervalIntegrable (fun σ : ℝ => σ⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact continuousOn_id.inv₀ (fun σ hσ => (ha.trans_le hσ.1).ne')
  have hn : 0 ≤ ∫ σ in a..b, (1-Real.cos (inner ℝ (g i) (η-θ)/σ))/σ := by
    apply intervalIntegral.integral_nonneg hab
    intro σ hσ
    exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (ha.trans_le hσ.1).le
  rw [abs_of_nonneg hn]
  calc
    _ ≤ ∫ σ in a..b, 2*σ⁻¹ := by
      apply intervalIntegral.integral_mono_on hab hi (hii.const_mul 2)
      intro σ hσ
      rw [← div_eq_mul_inv]
      apply div_le_div_of_nonneg_right _ (ha.trans_le hσ.1).le
      linarith [Real.neg_one_le_cos (inner ℝ (g i) (η-θ)/σ)]
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha (ha.trans_le hab)]

lemma base_distance_error (g : κ → E) {q ε a b : ℝ} (hq : 0 ≤ q) (hε : 0 ≤ ε)
    (ha : 0 < a) (hab : a ≤ b) (θ η : E) :
    |Profile.kernel g q ε a b θ θ 0 0 + Profile.kernel g q ε a b η η 0 0 -
      2*Profile.kernel g q ε a b θ η 0 0 - KernelApprox.cstar*q*‖η-θ‖| ≤
      q*(2*a+‖η-θ‖^2/b)+4*ε*(Fintype.card κ : ℝ)*Real.log (b/a) := by
  have hi1 := Profile.pairing_integrable g q ε θ θ 0 0 ha hab
  have hi2 := Profile.pairing_integrable g q ε η η 0 0 ha hab
  have hi3 := Profile.pairing_integrable g q ε θ η 0 0 ha hab
  have hic (i : κ) := cos_integrable g θ η ha hab i
  have hig := gaussian_scaled_integrable θ η ha hab
  have hiS : IntervalIntegrable (fun σ => ∑ i, (1-Real.cos (inner ℝ (g i) (η-θ)/σ))/σ) volume a b := by
    convert IntervalIntegrable.sum Finset.univ (fun i _ => hic i) using 1 <;>
      first | rfl | (funext σ; simp only [Finset.sum_apply])
  have he : Profile.kernel g q ε a b θ θ 0 0 + Profile.kernel g q ε a b η η 0 0 -
      2*Profile.kernel g q ε a b θ η 0 0 =
      2*q*(∫ σ in a..b, KernelApprox.scaled ‖η-θ‖ σ) +
      2*ε*(∑ i, ∫ σ in a..b, (1-Real.cos (inner ℝ (g i) (η-θ)/σ))/σ) := by
    unfold Profile.kernel
    rw [← intervalIntegral.integral_add hi1 hi2, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hi1.add hi2) (hi3.const_mul 2)]
    have hi : (fun σ => Profile.pairing g q ε σ θ θ 0 0 + Profile.pairing g q ε σ η η 0 0 -
        2*Profile.pairing g q ε σ θ η 0 0) =
        (fun σ => 2*q*KernelApprox.scaled ‖η-θ‖ σ +
          2*ε*∑ i, (1-Real.cos (inner ℝ (g i) (η-θ)/σ))/σ) := by
      funext σ; rw [base_pairing]; simp only [← Finset.sum_div]; ring
    rw [hi, intervalIntegral.integral_add (hig.const_mul _) (hiS.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (fun i _ => hic i)]
  rw [he]
  have ht := KernelApprox.truncated_error (norm_nonneg (η-θ)) ha hab
  rw [← intervalIntegral.integral_of_le hab] at ht
  have hs : |∑ i, ∫ σ in a..b, (1-Real.cos (inner ℝ (g i) (η-θ)/σ))/σ| ≤
      (Fintype.card κ : ℝ)*(2*Real.log (b/a)) := by
    calc
      _ ≤ ∑ i, |∫ σ in a..b, (1-Real.cos (inner ℝ (g i) (η-θ)/σ))/σ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : κ, 2*Real.log (b/a) := Finset.sum_le_sum (fun i _ => cos_integral_bound g θ η ha hab i)
      _ = _ := by simp
  have hsplit : 2*q*(∫ σ in a..b, KernelApprox.scaled ‖η-θ‖ σ) +
      2*ε*(∑ i, ∫ σ in a..b, (1-Real.cos (inner ℝ (g i) (η-θ)/σ))/σ) -
      KernelApprox.cstar*q*‖η-θ‖ =
      q*(2*(∫ σ in a..b, KernelApprox.scaled ‖η-θ‖ σ)-KernelApprox.cstar*‖η-θ‖)+
      2*ε*(∑ i, ∫ σ in a..b, (1-Real.cos (inner ℝ (g i) (η-θ)/σ))/σ) := by ring
  rw [hsplit]
  calc
    _ ≤ |q*(2*(∫ σ in a..b, KernelApprox.scaled ‖η-θ‖ σ)-KernelApprox.cstar*‖η-θ‖)|+
        |2*ε*(∑ i, ∫ σ in a..b, (1-Real.cos (inner ℝ (g i) (η-θ)/σ))/σ)| := abs_add_le ..
    _ ≤ q*(2*a+‖η-θ‖^2/b)+2*ε*((Fintype.card κ : ℝ)*(2*Real.log (b/a))) := by
      simp only [abs_mul, abs_of_nonneg hq, abs_of_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hε)]
      exact add_le_add (mul_le_mul_of_nonneg_left ht hq) (mul_le_mul_of_nonneg_left hs (by positivity))
    _ = _ := by ring

end UniformSparsestCut.MetricKernel

namespace UniformSparsestCut.MetricKernel
open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
variable {E : Type u4} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {S : Type u5} {N : Type u6} [Fintype S] [Fintype N] [DecidableEq S]

lemma full_differential_bound (g : S → N → E) (s : S)
    {q ε σ k γ G A V H D₀ : ℝ} (θ η v : E) (h : N → ℝ) (α β : S × N → ℝ)
    (hq : 0 < q) (hε : 0 < ε) (hσ : 0 < σ) (hk : k = q^2/(Fintype.card N : ℝ))
    (hG : 0 ≤ G) (hA : 0 ≤ A) (hV : 0 ≤ V) (hH : 0 ≤ H) (hD : 0 ≤ D₀) (hγ : 0 ≤ γ)
    (hg : ∀ s i, ‖g s i‖ ≤ G) (hv : ‖v‖ ≤ V*H) (hh : ∑ i, |h i| ≤ H)
    (hα : ∀ i, |α i| ≤ A) (hβ : ∀ i, |β i| ≤ A)
    (hδ : ∀ i : S × N, |(if i.1 = s then k/ε*(h i.2-inner ℝ (g i.1 i.2) v/q) else 0)| ≤ D₀*H)
    (hf : ‖Real.exp (-‖(σ⁻¹:ℝ) • (η-θ)‖^2/2) • ((σ⁻¹:ℝ) • (η-θ)) -
       ((Fintype.card N : ℝ)⁻¹) • ∑ i, Real.sin (inner ℝ (g s i) (η-θ)/σ) • g s i‖ ≤ γ) :
    |Profile.differential (fun j : S × N => g j.1 j.2) q ε σ θ η v α β
      (fun j => if j.1 = s then k/ε*(h j.2-inner ℝ (g j.1 j.2) v/q) else 0)| ≤
      ((k+q*γ*V+ε*((Fintype.card S : ℝ)*(Fintype.card N : ℝ))*D₀*A)*H)/σ +
      (ε*((Fintype.card S : ℝ)*(Fintype.card N : ℝ))*G*V*(1+A^2+2*A)*H)/σ^2 := by
  let δ : S × N → ℝ := fun j => if j.1 = s then k/ε*(h j.2-inner ℝ (g j.1 j.2) v/q) else 0
  let c : ℝ := (Fintype.card S : ℝ)*(Fintype.card N : ℝ)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hk0 : 0 ≤ k := by rw [hk]; positivity
  have hg0 := Profile.active_bound g s θ η v h hq hε hσ hk hg hf
  have hcorr := Profile.differential_correction (q := q) (fun j : S × N => g j.1 j.2) hε.le hσ θ η v α β δ
  have hc' : (∑ i : S × N, (|δ i| *|β i|+|inner ℝ (g i.1 i.2) v|/σ*
      (|α i| *|β i|+|α i|+|β i|))) ≤ c*(D₀*H*A+G*(V*H)/σ*(A^2+2*A)) := by
    calc
      _ ≤ ∑ _i : S × N, (D₀*H*A+G*(V*H)/σ*(A^2+2*A)) := by
        apply Finset.sum_le_sum; intro i _
        apply add_le_add
        · exact mul_le_mul (hδ i) (hβ i) (abs_nonneg _) (mul_nonneg hD hH)
        · apply mul_le_mul
          · apply div_le_div_of_nonneg_right _ hσ.le
            exact (abs_real_inner_le_norm _ v).trans (mul_le_mul (hg i.1 i.2) hv (norm_nonneg v) hG)
          · have hp := mul_le_mul (hα i) (hβ i) (abs_nonneg _) hA
            nlinarith [hα i,hβ i]
          · positivity
          · positivity
      _ = _ := by simp [c,Fintype.card_prod]; ring
  have hb0 : k/σ*(∑ i, |h i|) + q*γ/σ*‖v‖ + ε/σ^2*(c*G)*‖v‖ ≤
      k/σ*H+q*γ/σ*(V*H)+ε/σ^2*(c*G)*(V*H) := by
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hh (by positivity))
      (mul_le_mul_of_nonneg_left hv (by positivity))) (mul_le_mul_of_nonneg_left hv (by positivity))
  calc
    _ ≤ |Profile.differential (fun j : S × N => g j.1 j.2) q ε σ θ η v 0 0 δ|+
      |Profile.differential (fun j : S × N => g j.1 j.2) q ε σ θ η v α β δ -
        Profile.differential (fun j : S × N => g j.1 j.2) q ε σ θ η v 0 0 δ| := by
      simpa only [add_sub_cancel] using abs_add_le
        (Profile.differential (fun j : S × N => g j.1 j.2) q ε σ θ η v 0 0 δ)
        (Profile.differential (fun j : S × N => g j.1 j.2) q ε σ θ η v α β δ-
          Profile.differential (fun j : S × N => g j.1 j.2) q ε σ θ η v 0 0 δ)
    _ ≤ (k/σ*H+q*γ/σ*(V*H)+ε/σ^2*(c*G)*(V*H))+
        ε/σ*(c*(D₀*H*A+G*(V*H)/σ*(A^2+2*A))) :=
      add_le_add (hg0.trans hb0) (hcorr.trans (mul_le_mul_of_nonneg_left hc' (by positivity)))
    _ = _ := by dsimp [c]; field_simp; ring

end UniformSparsestCut.MetricKernel

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.ChartKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ChartKernel
open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
variable {m N S : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "F" => EuclideanSpace ℝ (Fin N)

lemma norm_linear_le_l1 (B : F →L[ℝ] E) {V : ℝ} (_hV : 0 ≤ V)
    (hB : ∀ i, ‖B (EuclideanSpace.single i 1)‖ ≤ V) (x : F) :
    ‖B x‖ ≤ V*∑ i, |x i| := by
  have he : x = ∑ i : Fin N, x i • EuclideanSpace.single i 1 := by
    apply PiLp.ext
    intro j
    simp [ Pi.single_apply]
  conv_lhs => rw [he, map_sum]
  calc
    _ ≤ ∑ i : Fin N, ‖B (x i • EuclideanSpace.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin N, |x i| * V := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul, norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hB i) (abs_nonneg _)
    _ = V*∑ i : Fin N, |x i| := by rw [← Finset.sum_mul]; ring

lemma alpha_linear (g : Fin S → Fin N → E) (B : Fin S → F →L[ℝ] E)
    (q k ε : ℝ) (s : Fin S) (x h : F) (t : ℝ) :
    alpha g B q k ε s (x+t • h) = fun j => alpha g B q k ε s x j+t*alpha g B q k ε s h j := by
  funext j
  simp only [alpha, map_add, map_smul, inner_add_right, real_inner_smul_right,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases hj : j.1=s <;> simp only [hj, ite_true,ite_false] <;> ring

lemma alpha_norm_bound (g : Fin S → Fin N → E) (B : Fin S → F →L[ℝ] E)
    {q k ε R : ℝ} (hk : 0 ≤ k) (hε : 0 < ε) (s : Fin S) (x : F)
    (hx : ‖residual (FrameCharts.chart (fun i => q⁻¹ • g s i)) (B s) x‖ ≤ R)
    (j : Fin S × Fin N) : |alpha g B q k ε s x j| ≤ k/ε*R := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hx
  by_cases hj : j.1=s
  · simp only [alpha,hj,ite_true,abs_mul,abs_of_nonneg (div_nonneg hk hε.le)]
    apply mul_le_mul_of_nonneg_left _ (div_nonneg hk hε.le)
    have hc := PiLp.norm_apply_le (p := (2:ENNReal))
      (residual (FrameCharts.chart (fun i => q⁻¹ • g s i)) (B s) x) j.2
    have he : residual (FrameCharts.chart (fun i => q⁻¹ • g s i)) (B s) x j.2 =
        x j.2-inner ℝ (g s j.2) (B s x)/q := by
      simp [residual,FrameCharts.chart_apply,real_inner_smul_left,div_eq_inv_mul]
    simpa only [he,Real.norm_eq_abs] using hc.trans hx
  · simp only [alpha,hj,ite_false,abs_zero]
    positivity

lemma alpha_derivative_bound (g : Fin S → Fin N → E) (B : Fin S → F →L[ℝ] E)
    {q k ε H : ℝ} (hq : 0 < q) (hk : 0 ≤ k) (hk1 : k ≤ 1) (hε : 0 < ε)
    (s : Fin S) (h : F) (hH : ∑ i, |h i| ≤ H)
    (hg : ∀ i, ‖g s i‖ ≤ 2*q) (hB : ∀ i, ‖B s (EuclideanSpace.single i 1)‖ ≤ 4*k)
    (j : Fin S × Fin N) : |alpha g B q k ε s h j| ≤ (9*k/ε)*H := by
  have hv := norm_linear_le_l1 (B s) (by positivity : 0 ≤ 4*k) hB h
  have hv' : ‖B s h‖ ≤ 4*k*H := hv.trans (mul_le_mul_of_nonneg_left hH (by positivity))
  have hH0 : 0 ≤ H := (Finset.sum_nonneg (fun _ _ => abs_nonneg _)).trans hH
  have hh (i : Fin N) : |h i| ≤ H := (Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ i)).trans hH
  by_cases hj : j.1=s
  · simp only [alpha,hj,ite_true,abs_mul,abs_of_nonneg (div_nonneg hk hε.le)]
    have hip : |inner ℝ (g s j.2) (B s h)/q| ≤ 8*k*H := by
      rw [abs_div,abs_of_pos hq]
      apply (div_le_iff₀ hq).mpr
      calc
        _ ≤ ‖g s j.2‖*‖B s h‖ := abs_real_inner_le_norm _ _
        _ ≤ (2*q)*(4*k*H) := mul_le_mul (hg _) hv' (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hb : |h j.2-inner ℝ (g s j.2) (B s h)/q| ≤ 9*H := by
      refine (abs_sub _ _).trans ?_
      have := mul_le_mul_of_nonneg_right hk1 hH0
      linarith [hh j.2,hip]
    calc
      _ ≤ (k/ε)*(9*H) := mul_le_mul_of_nonneg_left hb (div_nonneg hk hε.le)
      _ = _ := by ring
  · simp only [alpha,hj,ite_false,abs_zero]
    positivity

end UniformSparsestCut.ChartKernel

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.ChartAngles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ChartAngles
open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
variable {E : Type u1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type u2} {κ : Type u3} [Fintype ι] [Fintype κ]

lemma correction (g : κ → E) {q ε a b A : ℝ} (hε : 0≤ε) (ha : 0<a) (hab : a≤b)
    (hA : 0≤A) (θ η : E) (α β : κ → ℝ)
    (hα : ∀ i, |α i|≤A) (hβ : ∀ i, |β i|≤A) :
    |distance g q ε a b θ η α β-distance g q ε a b θ η 0 0| ≤
      4*(ε*(Fintype.card κ:ℝ)*(A^2+2*A)*Real.log (b/a)) := by
  have h1 := abs_le.mp (Profile.kernel_correction (q := q) g hε ha hab hA θ θ α α hα hα)
  have h2 := abs_le.mp (Profile.kernel_correction (q := q) g hε ha hab hA η η β β hβ hβ)
  have h3 := abs_le.mp (Profile.kernel_correction (q := q) g hε ha hab hA θ η α β hα hβ)
  unfold distance
  rw [abs_le]
  constructor <;> linarith

omit [InnerProductSpace ℝ E] in
lemma position_error (x y x' y' : E) {R : ℝ} (hx : ‖x-x'‖≤R) (hy : ‖y-y'‖≤R) :
    |‖x-y‖-‖x'-y'‖|≤2*R := by
  have he : (x-y)-(x'-y')=(x-x')-(y-y') := by abel
  calc
    _ ≤ ‖(x-y)-(x'-y')‖ := abs_norm_sub_norm_le _ _
    _ = ‖(x-x')-(y-y')‖ := by rw [he]
    _ ≤ ‖x-x'‖+‖y-y'‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

lemma rounded_distance_error (g : κ → E) {q ε a b A R T : ℝ}
    (hq : 0≤q) (hε : 0≤ε) (ha : 0<a) (hab : a≤b) (hA : 0≤A)
    (θ η θ' η' : E) (α β : κ → ℝ) (hα : ∀ i, |α i|≤A) (hβ : ∀ i, |β i|≤A)
    (hθ : ‖θ-θ'‖≤R) (hη : ‖η-η'‖≤R) (hT : ‖η-θ‖≤T) :
    |distance g q ε a b θ η α β-KernelApprox.cstar*q*‖η'-θ'‖| ≤
      q*(2*a+T^2/b)+4*ε*(Fintype.card κ:ℝ)*Real.log (b/a)+
        4*(ε*(Fintype.card κ:ℝ)*(A^2+2*A)*Real.log (b/a))+2*KernelApprox.cstar*q*R := by
  have hb := MetricKernel.base_distance_error g hq hε ha hab θ η
  change |distance g q ε a b θ η 0 0-KernelApprox.cstar*q*‖η-θ‖| ≤ _ at hb
  have hc := correction (q := q) g hε ha hab hA θ η α β hα hβ
  have hp := position_error η θ η' θ' hη hθ
  have hT0 : 0≤T := (norm_nonneg _).trans hT
  have hbb : q*(2*a+‖η-θ‖^2/b)+4*ε*(Fintype.card κ:ℝ)*Real.log (b/a) ≤
      q*(2*a+T^2/b)+4*ε*(Fintype.card κ:ℝ)*Real.log (b/a) := by
    have hb0 : 0≤b := ha.le.trans hab
    gcongr
  have hcp : 0 ≤ KernelApprox.cstar*q := mul_nonneg KernelApprox.cstar_pos.le hq
  have hpe : |KernelApprox.cstar*q*(‖η-θ‖-‖η'-θ'‖)|≤2*KernelApprox.cstar*q*R := by
    rw [abs_mul,abs_of_nonneg hcp]
    calc
      _ ≤ KernelApprox.cstar*q*(2*R) := mul_le_mul_of_nonneg_left hp hcp
      _ = _ := by ring
  have hb' := abs_le.mp (hb.trans hbb)
  have hc' := abs_le.mp hc
  have hp' := abs_le.mp hpe
  change |distance g q ε a b θ η 0 0-KernelApprox.cstar*q*‖η-θ‖| ≤ _ at hb
  rw [abs_le]
  constructor <;> nlinarith

omit [InnerProductSpace ℝ E] [Fintype ι] in

lemma global_angle {H : Type u4} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : ι → H) (θ : ι → E) {c e : ℝ} (hc : 0≤c) (_he : 0≤e)
    (hd : ∀ v w, |‖P v-P w‖^2-c*‖θ v-θ w‖|≤e) (v z y : ι) :
    -(3*e/2) ≤ inner ℝ (P v-P z) (P y-P z) := by
  have h1 := abs_le.mp (hd v z)
  have h2 := abs_le.mp (hd y z)
  have h3 := abs_le.mp (hd v y)
  have htri : ‖θ v-θ y‖≤‖θ v-θ z‖+‖θ y-θ z‖ := by
    have := norm_add_le (θ v-θ z) (θ z-θ y)
    rw [sub_add_sub_cancel,norm_sub_rev (θ z) (θ y)] at this
    exact this
  have hm := mul_le_mul_of_nonneg_left htri hc
  have hid : ‖P v-P z‖^2+‖P y-P z‖^2-‖P v-P y‖^2 =
      2*inner ℝ (P v-P z) (P y-P z) := by
    have he : P v-P y=(P v-P z)-(P y-P z) := by abel
    rw [he,norm_sub_sq_real (P v-P z) (P y-P z)]; ring
  nlinarith

end UniformSparsestCut.ChartAngles

namespace UniformSparsestCut.ChartAngles
open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
variable {m N S : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "F" => EuclideanSpace ℝ (Fin N)
lemma segment_norm_le {X : Type u5} {Y : Type u6} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (L : X →L[ℝ] Y)
    (x x' : X) {R t : ℝ} (hx : ‖L x‖≤R) (hx' : ‖L x'‖≤R) (ht : t∈Icc (0:ℝ) 1) :
    ‖L (x+t • (x'-x))‖≤R := by
  have he : x+t • (x'-x)=(1-t) • x+t • x' := by module
  rw [he,map_add,map_smul,map_smul]
  calc
    _ ≤ ‖(1-t) • L x‖+‖t • L x'‖ := norm_add_le _ _
    _ = (1-t)*‖L x‖+t*‖L x'‖ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ht.2),abs_of_nonneg ht.1]
    _ ≤ (1-t)*R+t*R := add_le_add (mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ht.2)) (mul_le_mul_of_nonneg_left hx' ht.1)
    _ = R := by ring

lemma local_profile (g : Fin S → Fin N → E) (B : Fin S → F →L[ℝ] E)
    {q k ε a b T R γ : ℝ} (hq : 0<q) (hk : 0≤k) (hk1 : k≤1)
    (hε : 0<ε) (ha : 0<a) (hab : a≤b) (hT : 0≤T) (hR : 0≤R) (hγ : 0≤γ)
    (hkq : k=q^2/(N:ℝ)) (hg : ∀ s i, ‖g s i‖≤2*q)
    (hB : ∀ s i, ‖B s (EuclideanSpace.single i 1)‖≤4*k)
    (hf : ∀ (s : Fin S) (w : E), ‖w‖≤2*T/a →
      ‖Real.exp (-‖w‖^2/2) • w-((N:ℝ)⁻¹) • ∑ i, Real.sin (inner ℝ (g s i) w) • g s i‖≤γ)
    (s t : Fin S) (x x' y : F)
    (hx : ‖B s x‖≤T) (hx' : ‖B s x'‖≤T) (hy : ‖B t y‖≤T)
    (hrx : ‖ChartKernel.residual (FrameCharts.chart (fun i => q⁻¹ • g s i)) (B s) x‖≤R)
    (hrx' : ‖ChartKernel.residual (FrameCharts.chart (fun i => q⁻¹ • g s i)) (B s) x'‖≤R)
    (hry : ‖ChartKernel.residual (FrameCharts.chart (fun i => q⁻¹ • g t i)) (B t) y‖≤R) :
    |Profile.kernel (fun j : Fin S × Fin N => g j.1 j.2) q ε a b
        (B s x') (B t y) (ChartKernel.alpha g B q k ε s x') (ChartKernel.alpha g B q k ε t y)-
      Profile.kernel (fun j : Fin S × Fin N => g j.1 j.2) q ε a b
        (B s x) (B t y) (ChartKernel.alpha g B q k ε s x) (ChartKernel.alpha g B q k ε t y)| ≤
      ((k+q*γ*(4*k)+ε*((S:ℝ)*N)*(9*k/ε)*(k/ε*R))*Real.log (b/a)+
        (ε*((S:ℝ)*N)*(2*q)*(4*k)*(1+(k/ε*R)^2+2*(k/ε*R)))/a)*
          (∑ i, |x' i-x i|) := by
  let H : ℝ := ∑ i : Fin N, |x' i-x i|
  let A : ℝ := k/ε*R
  let C : ℝ := k+q*γ*(4*k)+ε*((S:ℝ)*N)*(9*k/ε)*A
  let D : ℝ := ε*((S:ℝ)*N)*(2*q)*(4*k)*(1+A^2+2*A)
  have hH : 0≤H := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hA : 0≤A := by dsimp [A]; positivity
  have hD : 0≤D := by dsimp [D]; positivity
  have hθ (z : ℝ) (hz : z∈Icc (0:ℝ) 1) : ‖B s (x+z • (x'-x))‖≤T := segment_norm_le (B s) x x' hx hx' hz
  have hα (z : ℝ) (hz : z∈Icc (0:ℝ) 1) (j : Fin S × Fin N) :
      |ChartKernel.alpha g B q k ε s (x+z • (x'-x)) j|≤A :=
    ChartKernel.alpha_norm_bound g B hk hε s _ (segment_norm_le _ x x' hrx hrx' hz) j
  have hβ (j : Fin S × Fin N) : |ChartKernel.alpha g B q k ε t y j|≤A :=
    ChartKernel.alpha_norm_bound g B hk hε t y hry j
  have hv : ‖B s (x'-x)‖≤(4*k)*H := by
    simpa only [PiLp.sub_apply,H] using ChartKernel.norm_linear_le_l1 (B s) (by positivity : 0≤4*k) (hB s) (x'-x)
  have hd (z : ℝ) (hz : z∈Icc (0:ℝ) 1) (σ : ℝ) (hσ : σ∈Icc a b) :
      |Profile.differential (fun j : Fin S × Fin N => g j.1 j.2) q ε σ
        (B s x+z • B s (x'-x)) (B t y) (B s (x'-x))
        (fun j => ChartKernel.alpha g B q k ε s x j+z*ChartKernel.alpha g B q k ε s (x'-x) j)
        (ChartKernel.alpha g B q k ε t y) (ChartKernel.alpha g B q k ε s (x'-x))| ≤
        (C*H)/σ+(D*H)/σ^2 := by
    have hp : 0<σ := ha.trans_le hσ.1
    have he : B s x+z • B s (x'-x)=B s (x+z • (x'-x)) := by simp
    have hw : ‖(σ⁻¹:ℝ) • (B t y-B s (x+z • (x'-x)))‖≤2*T/a := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp),← div_eq_inv_mul]
      calc
        _ ≤ (2*T)/σ := div_le_div_of_nonneg_right
          ((norm_sub_le _ _).trans (by linarith [hθ z hz])) hp.le
        _ ≤ (2*T)/a := div_le_div_of_nonneg_left (by positivity) ha hσ.1
    have hfreq := hf s ((σ⁻¹:ℝ) • (B t y-B s (x+z • (x'-x)))) hw
    have hf' : ‖Real.exp (-‖(σ⁻¹:ℝ) • (B t y-B s (x+z • (x'-x)))‖^2/2) •
        ((σ⁻¹:ℝ) • (B t y-B s (x+z • (x'-x))))-
        ((Fintype.card (Fin N):ℝ)⁻¹) • ∑ i, Real.sin (inner ℝ (g s i) (B t y-B s (x+z • (x'-x)))/σ) • g s i‖≤γ := by
      simpa only [real_inner_smul_right,div_eq_inv_mul,Fintype.card_fin] using hfreq
    rw [he,← ChartKernel.alpha_linear]
    have hb := MetricKernel.full_differential_bound g s (B s (x+z • (x'-x))) (B t y)
      (B s (x'-x)) (fun i => (x'-x) i) (ChartKernel.alpha g B q k ε s (x+z • (x'-x)))
      (ChartKernel.alpha g B q k ε t y) hq hε hp (by simpa using hkq)
      (by positivity : 0≤2*q) hA (by positivity : 0≤4*k) hH (by positivity : 0≤9*k/ε) hγ hg hv
      (by simp only [PiLp.sub_apply,H]; exact le_rfl) (hα z hz) hβ
      (fun j => ChartKernel.alpha_derivative_bound g B hq hk hk1 hε s (x'-x)
        (by simp only [PiLp.sub_apply,H]; exact le_rfl) (hg s) (hB s) j) hf'
    convert! hb using 1 ; simp only [C,D,Fintype.card_fin,A]
  have hl := Profile.kernel_segment_bound (fun j : Fin S × Fin N => g j.1 j.2)
    ha hab (mul_nonneg hD hH) (B s x) (B t y) (B s (x'-x))
    (ChartKernel.alpha g B q k ε s x) (ChartKernel.alpha g B q k ε t y)
    (ChartKernel.alpha g B q k ε s (x'-x)) hd
  have heθ : B s x+B s (x'-x)=B s x' := by rw [map_sub]; abel
  have heα : (fun j => ChartKernel.alpha g B q k ε s x j+ChartKernel.alpha g B q k ε s (x'-x) j)=
      ChartKernel.alpha g B q k ε s x' := by
    have := ChartKernel.alpha_linear g B q k ε s x (x'-x) 1
    simpa only [one_smul,one_mul,add_sub_cancel] using this.symm
  rw [heθ,heα] at hl
  convert hl using 1 ; dsimp [C,D,A,H] ; ring

end UniformSparsestCut.ChartAngles

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.TriangleRepair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.TriangleRepair
variable {ι : Type u1} [Fintype ι]
lemma exp_distance_intervalIntegrable {d r : ℝ} (hd : 0 ≤ d) (hr : 0 ≤ r) :
    IntervalIntegrable (fun l => Real.exp (-d / l)) volume 0 r := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr]
  apply (integrable_const (1 : ℝ)).mono'
  · exact (Real.measurable_exp.comp (measurable_const.div measurable_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with l hl
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd) hl.1.le)

lemma min_posSemidef (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) :
    (Matrix.of (fun i j => min (u i) (u j))).PosSemidef := by
  classical
  let R : ℝ := ∑ i, u i
  have hR : 0 ≤ R := Finset.sum_nonneg (fun i _ => hu i)
  have huR (i : ι) : u i ≤ R := Finset.single_le_sum (fun j _ => hu j) (Finset.mem_univ i)
  let K : ℝ → Matrix ι ι ℝ := fun l => Matrix.of fun i j =>
    (if l ≤ u i then 1 else 0) * (if l ≤ u j then 1 else 0)
  have hk (l : ℝ) : (K l).PosSemidef := by
    convert Matrix.posSemidef_vecMulVec_self_star
      (fun i => if l ≤ u i then (1 : ℝ) else 0) using 1 ; try rfl
  have hki (i j : ι) : (fun l => K l i j) =
      (Set.Iic (min (u i) (u j))).indicator (fun _ => (1 : ℝ)) := by
    funext l
    simp only [K, Matrix.of_apply, Set.indicator_apply, Set.mem_Iic, le_min_iff]
    split_ifs <;> norm_num <;> tauto
  have hi (i j : ι) : IntervalIntegrable (fun l => K l i j) volume 0 R := by
    rw [hki]
    exact ⟨(intervalIntegrable_const (a := 0) (b := R) (c := (1 : ℝ))).1.indicator
      measurableSet_Iic,
      (intervalIntegrable_const (a := 0) (b := R) (c := (1 : ℝ))).2.indicator
      measurableSet_Iic⟩
  have h := integral_posSemidef K hR (fun l _ => hk l) hi
  suffices he : Matrix.of (fun i j => min (u i) (u j)) =
      (fun i j => ∫ l in (0 : ℝ)..R, K l i j) by
    rw [he]
    exact h
  ext i j
  rw [hki]
  change min (u i) (u j) =
    ∫ l in (0 : ℝ)..R, Set.indicator {l | l ≤ min (u i) (u j)} (fun _ => (1 : ℝ)) l
  rw [intervalIntegral.integral_indicator
    (show min (u i) (u j) ∈ Set.Icc 0 R from
      ⟨le_min (hu i) (hu j), (min_le_left _ _).trans (huR i)⟩)]
  simp

lemma abs_sub_sq_hilbert (u : ι → ℝ) :
    ∃ h : ι → EuclideanSpace ℝ ι, ∀ i j, ‖h i - h j‖ ^ 2 = |u i - u j| := by
  let b : ℝ := ∑ i, |u i|
  have hu (i : ι) : 0 ≤ u i + b := by
    have hb : |u i| ≤ b := Finset.single_le_sum (fun j _ => abs_nonneg (u j))
      (Finset.mem_univ i)
    have := neg_abs_le (u i)
    linarith
  obtain ⟨h, hh⟩ := exists_gram (min_posSemidef (fun i => u i + b) hu)
  refine ⟨h, fun i j => ?_⟩
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    hh, hh, hh]
  simp only [Matrix.of_apply, min_self]
  rcases le_total (u i) (u j) with hij | hji
  · rw [min_eq_left (add_le_add_left hij b), abs_of_nonpos (sub_nonpos.mpr hij)]
    ring
  · rw [min_eq_right (add_le_add_left hji b), abs_of_nonneg (sub_nonneg.mpr hji)]
    ring

lemma l1_sq_hilbert {κ : Type u2} [Fintype κ] (x : ι → κ → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    ∃ h : ι → EuclideanSpace ℝ (κ × ι),
      ∀ i j, ‖h i - h j‖ ^ 2 = a * ∑ k, |x i k - x j k| := by
  classical
  choose h hh using fun k => abs_sub_sq_hilbert (fun i => x i k)
  refine ⟨fun i => WithLp.toLp 2 (fun ki => Real.sqrt a * h ki.1 i ki.2), ?_⟩
  intro i j
  rw [EuclideanSpace.norm_sq_eq]
  simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs,
    Fintype.sum_prod_type]
  have hs : ∀ k, ∑ l, (Real.sqrt a * h k i l - Real.sqrt a * h k j l) ^ 2 =
      a * |x i k - x j k| := by
    intro k
    simp_rw [← mul_sub, mul_pow, Real.sq_sqrt ha]
    rw [← Finset.mul_sum, ← hh k i j, EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs]
  simp_rw [hs]
  exact (Finset.mul_sum _ _ _).symm

lemma repair_integral_le {d r : ℝ} (hd : 0 ≤ d) (hr : 0 ≤ r) :
    (∫ l in (0 : ℝ)..r, 1 - Real.exp (-d / l)) ≤ r := by
  have hi := (intervalIntegrable_const (c := (1 : ℝ))).sub (exp_distance_intervalIntegrable hd hr)
  have h := intervalIntegral.integral_mono_on hr hi
    (intervalIntegrable_const (c := (1 : ℝ))) (fun l _ => by
      have := (Real.exp_pos (-d / l)).le
      linarith)
  simpa using h

lemma repair_integral_local {d r : ℝ} (hd : 0 < d) (hdr : d ≤ r) :
    (∫ l in (0 : ℝ)..r, 1 - Real.exp (-d / l)) ≤
      d * (1 + Real.log (r / d)) := by
  have hr : 0 ≤ r := hd.le.trans hdr
  have hi := (intervalIntegrable_const (c := (1 : ℝ))).sub (exp_distance_intervalIntegrable hd.le hr)
  have hi₀ := (intervalIntegrable_const (c := (1 : ℝ))).sub (exp_distance_intervalIntegrable hd.le hd.le)
  have hi₁ : IntervalIntegrable (fun l => 1 - Real.exp (-d / l)) volume d r :=
    hi.mono_set (by
      rw [Set.uIcc_of_le hdr, Set.uIcc_of_le hr]
      exact Set.Icc_subset_Icc hd.le le_rfl)
  have hn : 0 ∉ Set.uIcc d r := by
    rw [Set.uIcc_of_le hdr]
    exact fun h => (not_le_of_gt hd) h.1
  have hj : IntervalIntegrable (fun l => d * l⁻¹) volume d r :=
    (intervalIntegrable_inv_iff.mpr (Or.inr hn)).const_mul d
  have hbound := intervalIntegral.integral_mono_on hdr hi₁ hj (fun l hl => by
    have he := Real.one_sub_le_exp_neg (d / l)
    rw [← neg_div] at he
    rw [← div_eq_mul_inv]
    linarith)
  rw [intervalIntegral.integral_const_mul, integral_inv hn] at hbound
  rw [← intervalIntegral.integral_add_adjacent_intervals hi₀ hi₁]
  have hfirst := repair_integral_le hd.le hd.le
  linarith

section Charts

variable {κ : Type u3} {H : Type u4} [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [Fintype κ] in
lemma chartKernel_posSemidef (c : ι → κ) (h : ι → H) {l : ℝ} (hl : 0 ≤ l) :
    (chartKernel c h l).PosSemidef := by
  have hm := (Matrix.PosSemidef.one (n := κ) (R := ℝ)).submatrix c
  rcases hl.eq_or_lt with rfl | hl
  · convert hm using 1
    ext i j
    simp [chartKernel, Matrix.submatrix_apply, Matrix.one_apply]
  · have hg := gaussian_posSemidef h hl
    convert hm.hadamard hg using 1 <;> first | rfl | (
    ext i j
    change (if c i = c j then _ else 0) =
      (if c i = c j then (1 : ℝ) else 0) * _
    split_ifs <;> simp)

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma chartKernel_intervalIntegrable (c : ι → κ) (h : ι → H) {r : ℝ}
    (hr : 0 ≤ r) (i j : ι) :
    IntervalIntegrable (fun l => chartKernel c h l i j) volume 0 r := by
  by_cases hij : c i = c j
  · simpa [chartKernel, hij] using exp_distance_intervalIntegrable (sq_nonneg ‖h i - h j‖) hr
  · simp only [chartKernel, Matrix.of_apply, hij, ite_false]
    exact intervalIntegrable_const

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma chartKernel_nonneg (c : ι → κ) (h : ι → H) (l : ℝ) (i j : ι) :
    0 ≤ chartKernel c h l i j := by
  simp only [chartKernel, Matrix.of_apply]
  split_ifs <;> positivity

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma chartKernel_le_one (c : ι → κ) (h : ι → H) {l : ℝ} (hl : 0 ≤ l) (i j : ι) :
    chartKernel c h l i j ≤ 1 := by
  simp only [chartKernel, Matrix.of_apply]
  split_ifs
  · exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg _)) hl)
  · norm_num

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma chartKernel_self (c : ι → κ) (h : ι → H) (l : ℝ) (i : ι) :
    chartKernel c h l i i = 1 := by simp [chartKernel]

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma chartKernel_symm (c : ι → κ) (h : ι → H) (l : ℝ) (i j : ι) :
    chartKernel c h l i j = chartKernel c h l j i := by
  simp only [chartKernel, Matrix.of_apply, norm_sub_rev (h j) (h i)]
  by_cases hij : c i = c j <;> simp [hij, eq_comm]

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma cappedDistance_nonneg (c : ι → κ) (h : ι → H) {r : ℝ} (hr : 0 ≤ r) (i j : ι) :
    0 ≤ cappedDistance c h r i j := by
  simp only [cappedDistance]
  split_ifs
  · exact le_min hr (sq_nonneg _)
  · exact hr

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma cappedDistance_le (c : ι → κ) (h : ι → H) (r : ℝ) (i j : ι) :
    cappedDistance c h r i j ≤ r := by
  simp only [cappedDistance]
  split_ifs
  · exact min_le_left _ _
  · rfl

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma chartKernel_mul_le (c : ι → κ) (h : ι → H) (ht : ChartTriangle c h)
    {l : ℝ} (hl : 0 < l) (i j z : ι) :
    chartKernel c h l i z * chartKernel c h l j z ≤ chartKernel c h l i j := by
  by_cases hiz : c i = c z
  · by_cases hjz : c j = c z
    · simp only [chartKernel, Matrix.of_apply, hiz, hjz, ite_true]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hl.le
      have htri := ht i z j hiz hjz.symm
      rw [norm_sub_rev (h z) (h j)] at htri
      linarith
    · simp only [chartKernel, Matrix.of_apply, hjz, ite_false, mul_zero]
      split_ifs <;> positivity
  · simp only [chartKernel, Matrix.of_apply, hiz, ite_false, zero_mul]
    split_ifs <;> positivity

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma chartKernel_le_half (c : ι → κ) (h : ι → H) {r l : ℝ}
    (hl : 0 < l) (i j : ι) (hle : l ≤ cappedDistance c h r i j) :
    chartKernel c h l i j ≤ 1 / 2 := by
  by_cases hij : c i = c j
  · have hd : l ≤ ‖h i - h j‖ ^ 2 := by
      exact le_trans hle (by simp [cappedDistance, hij])
    simp only [chartKernel, Matrix.of_apply, hij, ite_true]
    calc
      Real.exp (-‖h i - h j‖ ^ 2 / l) ≤ Real.exp (-1) := by
        apply Real.exp_le_exp.mpr
        apply (div_le_iff₀ hl).mpr
        linarith
      _ ≤ 1 / 2 := by
        rw [Real.exp_neg, ← one_div]
        apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
        have := Real.add_one_le_exp (1 : ℝ)
        norm_num at this ⊢
        exact this
  · simp [chartKernel, hij]

omit [Fintype κ] in
lemma exists_repairGram (c : ι → κ) (h : ι → H) {r : ℝ} (hr : 0 ≤ r) :
    ∃ q : ι → EuclideanSpace ℝ ι, IsRepairGram c h r q := by
  have hi := integral_posSemidef (chartKernel c h) hr
    (fun l hl => chartKernel_posSemidef c h hl.1) (chartKernel_intervalIntegrable c h hr)
  obtain ⟨q, hq⟩ := exists_gram (hi.smul (by norm_num : (0 : ℝ) ≤ 4))
  exact ⟨q, hq⟩

omit [Fintype κ] [InnerProductSpace ℝ H] in
lemma repairGram_norm_sq (c : ι → κ) (h : ι → H) {r : ℝ}
    {q : ι → EuclideanSpace ℝ ι} (hq : IsRepairGram c h r q) (i : ι) :
    ‖q i‖ ^ 2 = 4 * r := by
  rw [← real_inner_self_eq_norm_sq, hq]
  simp_rw [chartKernel_self]
  simp

omit [Fintype κ] [InnerProductSpace ℝ H] in
lemma repairGram_distance (c : ι → κ) (h : ι → H) {r : ℝ} (hr : 0 ≤ r)
    {q : ι → EuclideanSpace ℝ ι} (hq : IsRepairGram c h r q) (i j : ι) :
    ‖q i - q j‖ ^ 2 = 8 * ∫ l in (0 : ℝ)..r, 1 - chartKernel c h l i j := by
  rw [norm_sub_sq_real, repairGram_norm_sq c h hq, repairGram_norm_sq c h hq, hq,
    intervalIntegral.integral_sub intervalIntegrable_const
      (chartKernel_intervalIntegrable c h hr i j)]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  ring

omit [Fintype κ] [InnerProductSpace ℝ H] in
lemma repairGram_distance_le (c : ι → κ) (h : ι → H) {r : ℝ} (hr : 0 ≤ r)
    {q : ι → EuclideanSpace ℝ ι} (hq : IsRepairGram c h r q) (i j : ι) :
    ‖q i - q j‖ ^ 2 ≤ 8 * r := by
  rw [repairGram_distance c h hr hq]
  have hi := (intervalIntegrable_const (c := (1 : ℝ))).sub
    (chartKernel_intervalIntegrable c h hr i j)
  have hb := intervalIntegral.integral_mono_on hr hi
    (intervalIntegrable_const (c := (1 : ℝ))) (fun l _ => by
      have := chartKernel_nonneg c h l i j
      linarith)
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at hb
  linarith

omit [Fintype κ] [InnerProductSpace ℝ H] in
lemma repairGram_local (c : ι → κ) (h : ι → H) {r : ℝ}
    {q : ι → EuclideanSpace ℝ ι} (hq : IsRepairGram c h r q) {i j : ι}
    (hij : c i = c j) (hd : 0 < ‖h i - h j‖ ^ 2) (hdr : ‖h i - h j‖ ^ 2 ≤ r) :
    ‖q i - q j‖ ^ 2 ≤ 8 * ‖h i - h j‖ ^ 2 *
      (1 + Real.log (r / ‖h i - h j‖ ^ 2)) := by
  rw [repairGram_distance c h (hd.le.trans hdr) hq]
  simp only [chartKernel, Matrix.of_apply, hij, ite_true]
  have := repair_integral_local hd hdr
  nlinarith

omit [Fintype κ] [InnerProductSpace ℝ H] in
lemma repairGram_eq_of_zero (c : ι → κ) (h : ι → H) {r : ℝ} (hr : 0 ≤ r)
    {q : ι → EuclideanSpace ℝ ι} (hq : IsRepairGram c h r q) {i j : ι}
    (hij : c i = c j) (hd : ‖h i - h j‖ ^ 2 = 0) : q i = q j := by
  have hdq := repairGram_distance c h hr hq i j
  simp only [chartKernel, Matrix.of_apply, hij, ite_true, hd, neg_zero, zero_div,
    Real.exp_zero, sub_self, intervalIntegral.integral_zero, mul_zero] at hdq
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hdq))

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma angleIntegrand_integrable (c : ι → κ) (h : ι → H) {r : ℝ} (hr : 0 ≤ r)
    (i j z : ι) : IntervalIntegrable (angleIntegrand c h i j z) volume 0 r :=
  (((intervalIntegrable_const (c := (1 : ℝ))).sub (chartKernel_intervalIntegrable c h hr i z)).sub
    (chartKernel_intervalIntegrable c h hr j z)).add (chartKernel_intervalIntegrable c h hr i j)

omit [Fintype κ] [InnerProductSpace ℝ H] in
lemma repairGram_angle (c : ι → κ) (h : ι → H) {r : ℝ} (hr : 0 ≤ r)
    {q : ι → EuclideanSpace ℝ ι} (hq : IsRepairGram c h r q) (i j z : ι) :
    ⟪q i - q z, q j - q z⟫_ℝ = 4 * ∫ l in (0 : ℝ)..r, angleIntegrand c h i j z l := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right, hq, hq, hq, hq]
  simp_rw [chartKernel_self, chartKernel_symm c h _ z j]
  rw [show (fun l => angleIntegrand c h i j z l) =
      (fun l => 1 - chartKernel c h l i z - chartKernel c h l j z +
        chartKernel c h l i j) from rfl]
  rw [intervalIntegral.integral_add
    (((intervalIntegrable_const (c := (1 : ℝ))).sub
      (chartKernel_intervalIntegrable c h hr i z)).sub
      (chartKernel_intervalIntegrable c h hr j z)) (chartKernel_intervalIntegrable c h hr i j)]
  rw [intervalIntegral.integral_sub
    ((intervalIntegrable_const (c := (1 : ℝ))).sub (chartKernel_intervalIntegrable c h hr i z))
    (chartKernel_intervalIntegrable c h hr j z)]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (chartKernel_intervalIntegrable c h hr i z)]
  ring

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma angleIntegrand_nonneg (c : ι → κ) (h : ι → H) (ht : ChartTriangle c h)
    {l : ℝ} (hl : 0 < l) (i j z : ι) : 0 ≤ angleIntegrand c h i j z l := by
  have ha := chartKernel_le_one c h hl.le i z
  have hb := chartKernel_le_one c h hl.le j z
  have hc := chartKernel_mul_le c h ht hl i j z
  have hp := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
  dsimp only [angleIntegrand]
  nlinarith

omit [Fintype ι] [Fintype κ] [InnerProductSpace ℝ H] in
lemma angleIntegrand_ge_quarter (c : ι → κ) (h : ι → H) (ht : ChartTriangle c h)
    {r l : ℝ} (hl : 0 < l) (i j z : ι)
    (hli : l ≤ cappedDistance c h r i z) (hlj : l ≤ cappedDistance c h r j z) :
    1 / 4 ≤ angleIntegrand c h i j z l := by
  have ha := chartKernel_le_half c h hl i z hli
  have hb := chartKernel_le_half c h hl j z hlj
  have hc := chartKernel_mul_le c h ht hl i j z
  have hp := mul_le_mul
    (show (1 / 2 : ℝ) ≤ 1 - chartKernel c h l i z by linarith)
    (show (1 / 2 : ℝ) ≤ 1 - chartKernel c h l j z by linarith)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (show 0 ≤ 1 - chartKernel c h l i z by linarith)
  dsimp only [angleIntegrand]
  nlinarith

omit [Fintype κ] [InnerProductSpace ℝ H] in
lemma repairGram_angle_lower (c : ι → κ) (h : ι → H) (ht : ChartTriangle c h)
    {r : ℝ} (hr : 0 ≤ r) {q : ι → EuclideanSpace ℝ ι} (hq : IsRepairGram c h r q)
    (i j z : ι) :
    min (cappedDistance c h r i z) (cappedDistance c h r j z) ≤
      ⟪q i - q z, q j - q z⟫_ℝ := by
  let t := min (cappedDistance c h r i z) (cappedDistance c h r j z)
  have ht₀ : 0 ≤ t := le_min (cappedDistance_nonneg c h hr i z)
    (cappedDistance_nonneg c h hr j z)
  have htr : t ≤ r := (min_le_left _ _).trans (cappedDistance_le c h r i z)
  have hf : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Ioc 0 r)] angleIntegrand c h i j z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with l hl
    exact angleIntegrand_nonneg c h ht hl.1 i j z
  have hlower := intervalIntegral.integral_mono_ae_restrict ht₀
    (intervalIntegrable_const (c := (1 / 4 : ℝ))) (angleIntegrand_integrable c h ht₀ i j z)
    (show (fun _ => (1 / 4 : ℝ)) ≤ᵐ[volume.restrict (Set.Icc 0 t)]
      angleIntegrand c h i j z from by
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with l hl hne
      exact angleIntegrand_ge_quarter c h ht (lt_of_le_of_ne hl.1 (Ne.symm hne)) i j z
        (hl.2.trans (min_le_left _ _)) (hl.2.trans (min_le_right _ _)))
  have hmono := intervalIntegral.integral_mono_interval le_rfl ht₀ htr hf
    (angleIntegrand_integrable c h hr i j z)
  rw [repairGram_angle c h hr hq]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hlower
  dsimp only [t] at *
  linarith

omit [Fintype κ] [DecidableEq κ] in

lemma chart_l1_sq_hilbert {ξ : Type u5} [Fintype ξ] (c : ι → κ) (x : ι → ξ → ℝ)
    (a : κ → ℝ) (ha : ∀ s, 0 ≤ a s) :
    ∃ h : ι → EuclideanSpace ℝ (ξ × ι),
      (∀ i j, c i = c j → ‖h i - h j‖ ^ 2 = a (c i) * ∑ k, |x i k - x j k|) ∧
      ChartTriangle c h := by
  obtain ⟨g, hg⟩ := l1_sq_hilbert x (by norm_num : (0 : ℝ) ≤ 1)
  let h : ι → EuclideanSpace ℝ (ξ × ι) := fun i => Real.sqrt (a (c i)) • g i
  have hh (i j : ι) (hc : c i = c j) :
      ‖h i - h j‖ ^ 2 = a (c i) * ∑ k, |x i k - x j k| := by
    dsimp only [h]
    rw [← hc, ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (ha (c i)), hg]
    ring
  refine ⟨h, hh, fun i j k hij hjk => ?_⟩
  rw [hh i k (hij.trans hjk), hh i j hij, hh j k hjk, ← hij, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (ha (c i))
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun l _ => abs_sub_le (x i l) (x j l) (x k l))

lemma sum_sq_hilbert {E : Type u6} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : ι → E) (q : ι → H) :
    ∃ z : ι → EuclideanSpace ℝ ι, ∀ i j,
      ‖z i - z j‖ ^ 2 = ‖P i - P j‖ ^ 2 + ‖q i - q j‖ ^ 2 := by
  obtain ⟨z, hz⟩ := exists_gram ((gram_posSemidef P).add (gram_posSemidef q))
  refine ⟨z, fun i j => ?_⟩
  simp only [norm_sub_sq_real]
  simp only [← real_inner_self_eq_norm_sq, hz, Matrix.add_apply, Matrix.of_apply]
  ring

lemma angle_triangle_slack (x y z : H) :
    ‖x - y‖ ^ 2 + ‖z - y‖ ^ 2 - ‖x - z‖ ^ 2 = 2 * ⟪x - y, z - y⟫_ℝ := by
  have he : x - z = (x - y) - (z - y) := by abel
  rw [he, norm_sub_sq_real (x - y) (z - y)]
  ring

omit [Fintype κ] in

theorem triangle_repair {E : Type u7} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : ι → κ) (h : ι → H) (ht : ChartTriangle c h) {r : ℝ} (hr : 0 < r)
    (P : ι → E)
    (hP : ∀ i j z, -min (cappedDistance c h r i z) (cappedDistance c h r j z) ≤
      ⟪P i - P z, P j - P z⟫_ℝ) :
    ∃ q z : ι → EuclideanSpace ℝ ι,
      IsRepairGram c h r q ∧
      (∀ i j, ‖z i - z j‖ ^ 2 = ‖P i - P j‖ ^ 2 + ‖q i - q j‖ ^ 2) ∧
      (∀ i j k, ‖z i - z k‖ ^ 2 ≤ ‖z i - z j‖ ^ 2 + ‖z j - z k‖ ^ 2) ∧
      (∀ i j, ‖q i - q j‖ ^ 2 = 8 * ∫ l in (0 : ℝ)..r, 1 - chartKernel c h l i j) ∧
      (∀ i j, ‖q i - q j‖ ^ 2 ≤ 8 * r) ∧
      (∀ i j, c i = c j → 0 < ‖h i - h j‖ ^ 2 → ‖h i - h j‖ ^ 2 ≤ r →
        ‖q i - q j‖ ^ 2 ≤ 8 * ‖h i - h j‖ ^ 2 * (1 + Real.log (r / ‖h i - h j‖ ^ 2))) ∧
      (∀ i j, c i = c j → ‖h i - h j‖ ^ 2 = 0 → q i = q j) := by
  obtain ⟨q, hq⟩ := exists_repairGram c h hr.le
  obtain ⟨z, hz⟩ := sum_sq_hilbert P q
  refine ⟨q, z, hq, hz, ?_, repairGram_distance c h hr.le hq,
    repairGram_distance_le c h hr.le hq,
    fun _ _ hc hd hdr => repairGram_local c h hq hc hd hdr,
    fun _ _ hc hd => repairGram_eq_of_zero c h hr.le hq hc hd⟩
  intro i j k
  rw [hz, hz, hz]
  have hp := hP i k j
  have hqangle := repairGram_angle_lower c h ht hr.le hq i k j
  have hpAngle := angle_triangle_slack (P i) (P j) (P k)
  have hqAngle := angle_triangle_slack (q i) (q j) (q k)
  rw [norm_sub_rev (P k) (P j)] at hpAngle
  rw [norm_sub_rev (q k) (q j)] at hqAngle
  linarith

end Charts

end UniformSparsestCut.TriangleRepair

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.ChartMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ChartMetric
open scoped BigOperators RealInnerProductSpace
open TriangleRepair
noncomputable section
variable {ι : Type u1} {C : Type u2} {J : Type u3} {E : Type u4} {H : Type u5} [Fintype ι] [Fintype C] [Fintype J] [DecidableEq C]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma neg_min_eq (a b : ℝ) : -min a b=max (-a) (-b) := by
  rcases le_total a b with h|h
  · rw [min_eq_left h,max_eq_left (neg_le_neg h)]
  · rw [min_eq_right h,max_eq_right (neg_le_neg h)]

omit [Fintype ι] [Fintype C] [InnerProductSpace ℝ H] in
lemma capped_angle (c : ι → C) (h : ι → H) {r : ℝ} (P : ι → E)
    (hg : ∀ v z y, -r≤ inner ℝ (P v-P z) (P y-P z))
    (hl : ∀ v z y, c v=c z → |inner ℝ (P v-P z) (P y-P z)|≤‖h v-h z‖^2) :
    ∀ v y z, -min (cappedDistance c h r v z) (cappedDistance c h r y z)≤
      inner ℝ (P v-P z) (P y-P z) := by
  intro v y z
  have h1 : -cappedDistance c h r v z≤ inner ℝ (P v-P z) (P y-P z) := by
    by_cases hc : c v=c z
    · have hh := (abs_le.mp (hl v z y hc)).1
      simp only [cappedDistance,hc,ite_true,neg_min_eq]
      exact max_le (hg v z y) hh
    · simpa only [cappedDistance,hc,ite_false] using hg v z y
  have h2 : -cappedDistance c h r y z≤ inner ℝ (P v-P z) (P y-P z) := by
    by_cases hc : c y=c z
    · have hh := (abs_le.mp (hl y z v hc)).1
      rw [real_inner_comm] at hh
      simp only [cappedDistance,hc,ite_true,neg_min_eq]
      exact max_le (hg v z y) hh
    · simpa only [cappedDistance,hc,ite_false] using hg v z y
  rw [neg_min_eq]
  exact max_le h1 h2

omit [InnerProductSpace ℝ H] [Fintype C] in

lemma repair_from_angles (c : ι → C) (x : ι → J → ℝ) {L r : ℝ} (hL : 0≤L) (hr : 0<r)
    (P : ι → E) (θ : ι → H) {q e : ℝ}
    (hm : ∀ v w, |‖P v-P w‖^2-q*‖θ v-θ w‖|≤e)
    (hg : ∀ v z y, -r≤ inner ℝ (P v-P z) (P y-P z))
    (hl : ∀ v z y, c v=c z → |inner ℝ (P v-P z) (P y-P z)|≤L*∑ j, |x v j-x z j|) :
    ∃ Z : ι → EuclideanSpace ℝ ι,
      (∀ v w z, ‖Z v-Z z‖^2≤‖Z v-Z w‖^2+‖Z w-Z z‖^2) ∧
      (∀ v w, |‖Z v-Z w‖^2-q*‖θ v-θ w‖|≤e+8*r) ∧
      (∀ v w, c v=c w → 0<L*(∑ j, |x v j-x w j|) → L*(∑ j, |x v j-x w j|)≤r →
        ‖Z v-Z w‖^2≤L*(∑ j, |x v j-x w j|)*
          (9+8*Real.log (r/(L*(∑ j, |x v j-x w j|))))) ∧
      (∀ v w, c v=c w → L*(∑ j, |x v j-x w j|)=0 → Z v=Z w) := by
  obtain ⟨h,hh,ht⟩ := chart_l1_sq_hilbert c x (fun _ => L) (fun _ => hL)
  have hloc (v z y : ι) (hc : c v=c z) : |inner ℝ (P v-P z) (P y-P z)|≤‖h v-h z‖^2 := by
    rw [hh v z hc]; exact hl v z y hc
  obtain ⟨Q,Z,hQ,hZ,htri,hint,hcap,hsmall,hzero⟩ := triangle_repair c h ht hr P (capped_angle c h P hg hloc)
  refine ⟨Z,htri,?_,?_,?_⟩
  · intro v w
    rw [hZ]
    calc
      _ ≤ |‖P v-P w‖^2-q*‖θ v-θ w‖|+|‖Q v-Q w‖^2| := by
        convert abs_add_le (‖P v-P w‖^2-q*‖θ v-θ w‖) (‖Q v-Q w‖^2) using 1
        congr 1
        ring
      _ ≤ e+8*r := add_le_add (hm v w) (by simpa only [abs_sq] using hcap v w)
  · intro v w hc hpos hbound
    have hqr := hsmall v w hc (by rwa [hh v w hc]) (by rwa [hh v w hc])
    rw [hh v w hc] at hqr
    have hp := hl v w v hc
    rw [real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg _)] at hp
    rw [hZ]
    nlinarith
  · intro v w hc hz
    have hq := hzero v w hc (by rwa [hh v w hc])
    have hp := hl v w v hc
    rw [hz,real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg _)] at hp
    have hzsq : ‖Z v-Z w‖^2=0 := by rw [hZ,hq,sub_self,norm_zero]; nlinarith [sq_nonneg ‖P v-P w‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzsq))

end
end UniformSparsestCut.ChartMetric

namespace UniformSparsestCut.GramMetric
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m N S : ℕ} {V : Type u6} [Fintype V]
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "F" => EuclideanSpace ℝ (Fin N)

lemma localCost_nonneg {q k ε a b R γ : ℝ} (hq : 0≤q) (hk : 0≤k)
    (hε : 0<ε) (ha : 0<a) (hab : a≤b) (hR : 0≤R) (hγ : 0≤γ) :
    0≤localCost N S q k ε a b R γ := by
  have hl : 0≤Real.log (b/a) := Real.log_nonneg ((one_le_div ha).mpr hab)
  unfold localCost; positivity

lemma realization (g : Fin S → Fin N → E) (B : Fin S → F →L[ℝ] E)
    (c : V → Fin S) (x : V → F) (θ : V → E)
    {q k ε a b R T Rpos γ r : ℝ}
    (hq : 0<q) (hk : 0≤k) (hk1 : k≤1) (hε : 0<ε) (ha : 0<a) (hab : a≤b)
    (hR : 0≤R) (hT : 0≤T) (hγ : 0≤γ) (hkq : k=q^2/(N:ℝ))
    (hg : ∀ s i, ‖g s i‖≤2*q)
    (hB : ∀ s i, ‖B s (EuclideanSpace.single i 1)‖≤4*k)
    (hf : ∀ (s : Fin S) (w : E), ‖w‖≤2*T/a →
      ‖Real.exp (-‖w‖^2/2) • w-((N:ℝ)⁻¹) • ∑ i, Real.sin (inner ℝ (g s i) w) • g s i‖≤γ)
    (hx : ∀ v, ‖B (c v) (x v)‖≤T)
    (hrx : ∀ v, ‖ChartKernel.residual (FrameCharts.chart (fun i => q⁻¹ • g (c v) i)) (B (c v)) (x v)‖≤R)
    (hpos : ∀ v, ‖B (c v) (x v)-θ v‖≤Rpos)
    (he : 0≤ macroCost N S q k ε a b R T Rpos) (hr : 0<r)
    (her : 3*macroCost N S q k ε a b R T Rpos/2≤r) :
    ∃ Z : V → EuclideanSpace ℝ V,
      (∀ v w z, ‖Z v-Z z‖^2≤‖Z v-Z w‖^2+‖Z w-Z z‖^2) ∧
      (∀ v w, |‖Z v-Z w‖^2-KernelApprox.cstar*q*‖θ v-θ w‖|≤ macroCost N S q k ε a b R T Rpos+8*r) ∧
      (∀ v w, c v=c w → 0<localCost N S q k ε a b R γ*(∑ i, |x v i-x w i|) →
        localCost N S q k ε a b R γ*(∑ i, |x v i-x w i|)≤r →
        ‖Z v-Z w‖^2≤localCost N S q k ε a b R γ*(∑ i, |x v i-x w i|)*
          (9+8*Real.log (r/(localCost N S q k ε a b R γ*(∑ i, |x v i-x w i|))))) ∧
      (∀ v w, c v=c w → localCost N S q k ε a b R γ*(∑ i, |x v i-x w i|)=0 → Z v=Z w) := by
  let G : Fin S × Fin N → E := fun j => g j.1 j.2
  let Θ : V → E := fun v => B (c v) (x v)
  let α : V → Fin S × Fin N → ℝ := fun v => ChartKernel.alpha g B q k ε (c v) (x v)
  obtain ⟨P,hP⟩ := CommonKernel.gram_realization G Θ α hq.le hε.le ha hab
  have hPK (v w : V) : inner ℝ (P v) (P w)=Profile.kernel G q ε a b (Θ v) (Θ w) (α v) (α w) := by
    rw [hP,MetricKernel.gram_eq_kernel G Θ α q ε ha hab]
  have hPD (v w : V) : ‖P v-P w‖^2=ChartAngles.distance G q ε a b (Θ v) (Θ w) (α v) (α w) := by
    rw [norm_sub_sq_real]
    simp only [← real_inner_self_eq_norm_sq,hPK,ChartAngles.distance]
    ring
  have hα (v : V) (j : Fin S × Fin N) : |α v j|≤k/ε*R :=
    ChartKernel.alpha_norm_bound g B hk hε (c v) (x v) (hrx v) j
  have hd (v w : V) : |‖P v-P w‖^2-KernelApprox.cstar*q*‖θ v-θ w‖|≤ macroCost N S q k ε a b R T Rpos := by
    rw [hPD,norm_sub_rev (θ v) (θ w)]
    have hh := ChartAngles.rounded_distance_error (T := 2*T) G hq.le hε.le ha hab
      (mul_nonneg (div_nonneg hk hε.le) hR) (Θ v) (Θ w) (θ v) (θ w) (α v) (α w)
      (hα v) (hα w) (hpos v) (hpos w) ((norm_sub_le _ _).trans (by dsimp only [Θ]; linarith [hx v,hx w]))
    simpa only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,macroCost] using hh
  have hlocal (v z y : V) (hc : c v=c z) :
      |inner ℝ (P v-P z) (P y-P z)|≤localCost N S q k ε a b R γ*(∑ i, |x v i-x z i|) := by
    have hb (w : V) := ChartAngles.local_profile g B hq hk hk1 hε ha hab hT hR hγ hkq hg hB hf
      (c z) (c w) (x z) (x v) (x w) (hx z) (by simpa only [← hc] using hx v) (hx w)
      (hrx z) (by simpa only [← hc] using hrx v) (hrx w)
    have hy := hb y
    have hz := hb z
    rw [inner_sub_left,inner_sub_right,inner_sub_right]
    simp only [hPK,Θ,α,G,hc] at hy hz ⊢
    have hy' := abs_le.mp hy
    have hz' := abs_le.mp hz
    rw [abs_le]
    unfold localCost
    constructor <;> linarith
  apply ChartMetric.repair_from_angles c (fun v i => x v i)
    (localCost_nonneg hq.le hk hε ha hab hR hγ) hr P θ hd ?_ hlocal
  intro v z y
  exact (neg_le_neg her).trans (ChartAngles.global_angle P θ
    (mul_nonneg KernelApprox.cstar_pos.le hq.le) he hd v z y)

end
end UniformSparsestCut.GramMetric

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceParameters
open Filter
noncomputable section

lemma p_nonneg {x : ℝ} (hx : 0≤x) (n : ℕ) : 0≤p x n := by unfold p; positivity
lemma p_mul {x : ℝ} (hx : x≠0) (a b : ℕ) : p x a*p x b=p x (a+b) := by
  simp only [p,pow_add]; field_simp
lemma p_le {x : ℝ} (hx : 1≤x) {a b : ℕ} (hab : a≤b) : p x b≤p x a := by
  unfold p
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hx hab)
lemma p_one_le {x : ℝ} (hx : 1≤x) (a : ℕ) : p x a≤1 := by
  simpa [p] using p_le hx (Nat.zero_le a)
lemma p_succ {x : ℝ} (hx : x≠0) (a : ℕ) : x*p x (a+1)=p x a := by
  unfold p; rw [pow_succ]; field_simp
lemma log_ratio {x : ℝ} (hx : 0<x) : Real.log (x^40/(p x 40))=80*Real.log x := by
  rw [Real.log_div (pow_ne_zero _ hx.ne') (ne_of_gt (p_pos hx 40))]
  simp [p,Real.log_pow]; ring
lemma k_eq {x : ℝ} (hx : 0<x) : p x 5=(Real.sqrt x)^2/x^6 := by
  rw [Real.sq_sqrt hx.le]; unfold p; field_simp
lemma local_formula {m : ℕ} (hm : 0 < m) :
    GramMetric.localCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
      (p m 40) ((m:ℝ)^40) (p m 1997) (2/Real.sqrt m)=
      1440*p m 5*Real.log m+1440*p m 1798*Real.log m+
        16*Real.sqrt m*p m 156*(1+p m 1802)^2 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hq := ne_of_gt (Real.sqrt_pos.mpr hm0)
  unfold GramMetric.localCost
  rw [log_ratio hm0]
  simp only [p,Nat.cast_pow]
  field_simp
  ring
lemma macro_formula {m : ℕ} (hm : 0 < m) :
    GramMetric.macroCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
      (p m 40) ((m:ℝ)^40) (p m 1997) (3*Real.sqrt m) 0=
      2*Real.sqrt m*p m 40+36*Real.sqrt m*p m 39+
        320*p m 191*Real.log m*(1+p m 1802)^2 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  unfold GramMetric.macroCost
  rw [log_ratio hm0]
  simp only [p,Nat.cast_pow,mul_zero,add_zero]
  simp only [mul_pow,Real.sq_sqrt hm0.le]
  field_simp
  ring
end
end UniformSparsestCut.SourceParameters

namespace UniformSparsestCut.SourceParameters
open Filter
noncomputable section
lemma sqrt_le {x : ℝ} (hx : 1≤x) : Real.sqrt x≤x := by
  have h := Real.sq_sqrt (by linarith : 0≤x)
  have hx0 : 0≤x := by linarith
  nlinarith [Real.sqrt_nonneg x]
lemma correction_le {x : ℝ} (hx : 1≤x) : (1+p x 1802)^2≤4 := by
  have h0 := p_nonneg (by linarith : 0≤x) 1802
  have h1 := p_one_le hx 1802
  nlinarith
lemma local_bounds {m : ℕ} (hm1 : 1 ≤ m) (hl : 1≤Real.log m) :
    p m 5≤GramMetric.localCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
      (p m 40) ((m:ℝ)^40) (p m 1997) (2/Real.sqrt m) ∧
    GramMetric.localCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
      (p m 40) ((m:ℝ)^40) (p m 1997) (2/Real.sqrt m)≤3000*p m 5*Real.log m := by
  have hm0 : 0 < m := by omega
  have hx : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hn : (0:ℝ) ≤ m := by positivity
  rw [local_formula hm0]
  have hp5 := p_nonneg hn 5
  have hl0 : 0≤Real.log m := by linarith
  have hextra1 : 1440*p m 1798*Real.log m≤1440*p m 5*Real.log m := by
    gcongr
    exact p_le hx (by norm_num)
  have hextra2 : 16*Real.sqrt m*p m 156*(1+p m 1802)^2≤64*p m 5*Real.log m := by
    calc
      _ ≤ 16*(m:ℝ)*p m 156*4 := by
        gcongr <;> first | exact sqrt_le hx | exact correction_le hx | (unfold p; positivity)
      _ = 64*p m 155 := by
        have hh := p_succ (by positivity : (m:ℝ)≠0) 155
        nlinarith
      _ ≤ 64*p m 5*Real.log m := by
        have hh := p_le hx (show 5≤155 by norm_num)
        nlinarith
  constructor
  · have hmain : p m 5≤1440*p m 5*Real.log m := by nlinarith
    linarith [show 0≤1440*p m 1798*Real.log m by unfold p; positivity,
      show 0≤16*Real.sqrt m*p m 156*(1+p m 1802)^2 by unfold p; positivity]
  · nlinarith [mul_nonneg hp5 hl0]
lemma macro_bounds {m : ℕ} (hm1 : 1 ≤ m) :
    0≤GramMetric.macroCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
      (p m 40) ((m:ℝ)^40) (p m 1997) (3*Real.sqrt m) 0 ∧
    GramMetric.macroCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
      (p m 40) ((m:ℝ)^40) (p m 1997) (3*Real.sqrt m) 0≤1318*p m 38 := by
  have hm0 : 0 < m := by omega
  have hx : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hn : (0:ℝ) ≤ m := by positivity
  have hl0 := Real.log_nonneg hx
  have hl1 : Real.log m≤(m:ℝ) := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  rw [macro_formula hm0]
  constructor
  · unfold p; positivity
  · have h1 : 2*Real.sqrt m*p m 40≤2*p m 38 := by
      calc
        _ ≤ 2*(m:ℝ)*p m 40 := by gcongr <;> first | exact sqrt_le hx | (unfold p; positivity)
        _ = 2*p m 39 := by nlinarith [p_succ (by positivity : (m:ℝ)≠0) 39]
        _ ≤ _ := by gcongr; exact p_le hx (by norm_num)
    have h2 : 36*Real.sqrt m*p m 39≤36*p m 38 := by
      calc
        _ ≤ 36*(m:ℝ)*p m 39 := by gcongr <;> first | exact sqrt_le hx | (unfold p; positivity)
        _ = _ := by nlinarith [p_succ (by positivity : (m:ℝ)≠0) 38]
    have h3 : 320*p m 191*Real.log m*(1+p m 1802)^2≤1280*p m 38 := by
      calc
        _ ≤ 320*p m 191*(m:ℝ)*4 := by gcongr <;> first | exact correction_le hx | exact hl1 | (unfold p; positivity)
        _ = 1280*p m 190 := by nlinarith [p_succ (by positivity : (m:ℝ)≠0) 190]
        _ ≤ _ := by gcongr; exact p_le hx (by norm_num)
    linarith
lemma macro_small {m : ℕ} (hm : 3000 ≤ m) :
    GramMetric.macroCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
      (p m 40) ((m:ℝ)^40) (p m 1997) (3*Real.sqrt m) 0≤p m 8/2 := by
  have hx : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hp : (2636:ℝ)≤(m:ℝ)^30 := by
    have hh := pow_le_pow_right₀ hx (show 1≤30 by norm_num)
    simp only [pow_one] at hh
    have hm' : (3000:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  calc
    _ ≤ 1318*p m 38 := (macro_bounds (show 1 ≤ m by omega)).2
    _ ≤ p m 8/2 := by
      have hm0 : (0:ℝ) < m := by positivity
      unfold p
      rw [show (m:ℝ)^38=(m:ℝ)^8*(m:ℝ)^30 by ring]
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
      field_simp
      nlinarith
end
end UniformSparsestCut.SourceParameters

namespace UniformSparsestCut.SourceParameters
open scoped BigOperators
noncomputable section
lemma sqrt_m6 (m : ℕ) : Real.sqrt (m^6:ℕ)=(m:ℝ)^3 := by
  rw [Nat.cast_pow,show (m:ℝ)^6=((m:ℝ)^3)^2 by ring,Real.sqrt_sq (by positivity)]
lemma rounded_radius {m : ℕ} (hm : 0 < m) : Real.sqrt (m^6:ℕ)*p m 2000=p m 1997 := by
  rw [sqrt_m6]; unfold p; field_simp
lemma radius_le_sqrt {m : ℕ} (hm : 1 ≤ m) : p m 1997≤Real.sqrt m := by
  have hx : (1:ℝ) ≤ m := by exact_mod_cast hm
  exact (p_one_le hx _).trans (Real.one_le_sqrt.mpr hx)
lemma fourier_radius {m : ℕ} (hm : 6 ≤ m) : 2*(3*Real.sqrt m)/p m 40≤(m:ℝ)^42 := by
  have hx : (6:ℝ) ≤ m := by exact_mod_cast hm
  have hx1 : (1:ℝ) ≤ m := by linarith
  calc
    _ = 6*Real.sqrt m*(m:ℝ)^40 := by unfold p; field_simp ; ring
    _ ≤ (m:ℝ)*(m:ℝ)*(m:ℝ)^40 := by gcongr; exact sqrt_le hx1
    _ = _ := by ring
lemma local_tau {m : ℕ} (hm : 3000 ≤ m) (hl : 1≤Real.log m) :
    let L := GramMetric.localCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
      (p m 40) ((m:ℝ)^40) (p m 1997) (2/Real.sqrt m)
    0<L*p m 2000 ∧ L*p m 2000≤p m 8 ∧
    L*p m 2000*(9+8*Real.log (p m 8/(L*p m 2000)))≤
      50000000*p m 2000*p m 5*(Real.log m)^2 := by
  dsimp only
  let L := GramMetric.localCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
      (p m 40) ((m:ℝ)^40) (p m 1997) (2/Real.sqrt m)
  change 0<L*p m 2000 ∧ L*p m 2000≤p m 8 ∧ _
  have hx : (3000:ℝ) ≤ m := by exact_mod_cast hm
  have hx1 : (1:ℝ) ≤ m := by linarith
  have hx0 : (0:ℝ) < m := by linarith
  have hτ := p_pos hx0 2000
  have hp5 := p_pos hx0 5
  have hp8 := p_pos hx0 8
  have hL := local_bounds (show 1 ≤ m by omega) hl
  change p m 5≤L ∧ L≤3000*p m 5*Real.log m at hL
  have hδ : 0<L*p m 2000 := mul_pos (hp5.trans_le hL.1) hτ
  have hδ0 : p m 5*p m 2000≤L*p m 2000 := mul_le_mul_of_nonneg_right hL.1 hτ.le
  have hδ1 : L*p m 2000≤3000*p m 2000*p m 5*Real.log m := by nlinarith [mul_le_mul_of_nonneg_right hL.2 hτ.le]
  have hlx : Real.log m≤(m:ℝ) := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
  have hs : L*p m 2000≤p m 8 := by
    calc
      _ ≤ 3000*p m 2000*p m 5*(m:ℝ) := hδ1.trans (mul_le_mul_of_nonneg_left hlx (by unfold p; positivity))
      _ = 3000*p m 2004 := by rw [mul_assoc (3000:ℝ),p_mul hx0.ne']; norm_num; nlinarith [p_succ hx0.ne' 2004]
      _ ≤ 3000*p m 9 := mul_le_mul_of_nonneg_left (p_le hx1 (by norm_num)) (by norm_num)
      _ ≤ (m:ℝ)*p m 9 := mul_le_mul_of_nonneg_right hx (p_nonneg hx0.le _)
      _ = p m 8 := p_succ hx0.ne' 8
  have he : p m 8/(p m 5*p m 2000)=(m:ℝ)^1997 := by unfold p; field_simp
  have hlog : Real.log (p m 8/(L*p m 2000))≤1997*Real.log m := by
    calc
      _ ≤ Real.log (p m 8/(p m 5*p m 2000)) :=
        Real.log_le_log (div_pos hp8 hδ) (div_le_div_of_nonneg_left hp8.le (mul_pos hp5 hτ) hδ0)
      _ = _ := by rw [he,Real.log_pow]; norm_num
  have hlog0 : 0≤Real.log (p m 8/(L*p m 2000)) := Real.log_nonneg ((one_le_div hδ).mpr hs)
  refine ⟨hδ,hs,?_⟩
  change L*p m 2000*(9+8*Real.log (p m 8/(L*p m 2000)))≤_
  calc
    _ ≤ (3000*p m 2000*p m 5*Real.log m)*(15985*Real.log m) := by
      apply mul_le_mul hδ1 (by linarith) (by positivity) (by unfold p; positivity)
    _ ≤ _ := by nlinarith [show 0≤p m 2000*p m 5*(Real.log m)^2 by unfold p; positivity]
end
end UniformSparsestCut.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.Metric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceMetric
open scoped BigOperators RealInnerProductSpace
open SourceParameters SourceCharts
noncomputable section
variable {m : ℕ} (f : PivotFamily.PFamily m)
local notation "E" => EuclideanSpace ℝ (Fin m)
lemma realization [NeZero m] (hm : 3000 ≤ m) (hl : 1≤Real.log m) :
    ∃ Z : V f → EuclideanSpace ℝ (V f),
      (∀ v w z, ‖Z v-Z z‖^2≤‖Z v-Z w‖^2+‖Z w-Z z‖^2) ∧
      (∀ v w, |‖Z v-Z w‖^2-KernelApprox.cstar*Real.sqrt m*
         ‖B f (NeZero.pos m) v.val.1 (RoundedCharts.coordinate (u f) (p m 2000) v)-
           B f (NeZero.pos m) w.val.1 (RoundedCharts.coordinate (u f) (p m 2000) w)‖|≤err (m:=m)+8*p m 8) ∧
      (∀ v w, v.val.1=w.val.1 → (∑ i, |RoundedCharts.coordinate (u f) (p m 2000) v i-
        RoundedCharts.coordinate (u f) (p m 2000) w i|)=p m 2000 →
        ‖Z v-Z w‖^2≤50000000*p m 2000*p m 5*(Real.log m)^2) := by
  have hm0 := NeZero.pos m
  have hm1 : 1 ≤ m := by omega
  have hm2 : 2 ≤ m := by omega
  have hx : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hx0 : (0:ℝ) < m := by exact_mod_cast hm0
  have hτ := p_pos hx0 2000
  let c : V f → Fin (m^3) := fun v => v.val.1
  let x := RoundedCharts.coordinate (u f) (p m 2000)
  let θ : V f → E := fun v => B f hm0 (c v) (x v)
  have hhab : p m 40≤(m:ℝ)^40 := (p_one_le hx _).trans (one_le_pow₀ hx)
  have hb (s : Fin (m^3)) (i : Fin (m^6)) : ‖B f hm0 s (EuclideanSpace.single i 1)‖≤4*p m 5 := by
    have h := B_column f hm0 s i
    convert h using 1
    unfold p; field_simp
  have hFourier (s : Fin (m^3)) (w : E) (hw : ‖w‖≤2*(3*Real.sqrt m)/p m 40) :
      ‖Real.exp (-‖w‖^2/2) • w-((m^6:ℕ):ℝ)⁻¹ • ∑ i, Real.sin (inner ℝ (f.g s i) w) • f.g s i‖≤2/Real.sqrt m := by
    rw [norm_sub_rev]
    exact f.fourier s w (hw.trans (fourier_radius (show 6 ≤ m by omega)))
  have hB (v : V f) : ‖B f hm0 (c v) (x v)‖≤3*Real.sqrt m := by
    have h := vertex_B_bound f hm0 hm2 hτ v
    rw [rounded_radius hm0] at h
    exact h.trans (by linarith [radius_le_sqrt hm1])
  have hres (v : V f) :
      ‖ChartKernel.residual (FrameCharts.chart (fun i => (Real.sqrt m)⁻¹ • f.g (c v) i)) (B f hm0 (c v)) (x v)‖≤p m 1997 := by
    have h := vertex_residual_bound f hm0 hτ v
    rw [rounded_radius hm0] at h
    exact h
  have he := (macro_bounds hm1).1
  have her : 3*err (m:=m)/2≤p m 8 := by
    have hsmall := macro_small hm
    change err (m:=m)≤p m 8/2 at hsmall
    nlinarith [p_nonneg hx0.le 8]
  obtain ⟨Z,htri,hmac,hloc,hzero⟩ := GramMetric.realization f.g (B f hm0) c x θ
    (q:=Real.sqrt m) (k:=p m 5) (ε:=p m 200) (a:=p m 40) (b:=(m:ℝ)^40)
    (R:=p m 1997) (T:=3*Real.sqrt m) (Rpos:=0) (γ:=2/Real.sqrt m) (r:=p m 8)
    (Real.sqrt_pos.mpr hx0) (p_nonneg hx0.le 5) (p_one_le hx 5) (p_pos hx0 200) (p_pos hx0 40) hhab
    (p_nonneg hx0.le 1997) (by positivity) (by positivity)
    (by simpa only [Nat.cast_pow] using k_eq hx0)
    (fun s i => (f.norms s i).2) hb hFourier hB hres
    (fun v => by simp [θ]) he (p_pos hx0 8) her
  refine ⟨Z,htri,hmac,?_⟩
  intro v w hc hsum
  have hh := local_tau hm hl
  have h := hloc v w hc (by rw [hsum]; exact hh.1) (by rw [hsum]; exact hh.2.1)
  rw [hsum] at h
  exact h.trans hh.2.2
end
end UniformSparsestCut.SourceMetric

namespace UniformSparsestCut.SourceMetric
open scoped BigOperators RealInnerProductSpace
open SourceParameters SourceCharts
noncomputable section
variable {m : ℕ} (f : PivotFamily.PFamily m) [NeZero m]
local notation "E" => EuclideanSpace ℝ (Fin m)
lemma C₀_pos : 0<C₀ := by unfold C₀; linarith [KernelApprox.cstar_pos]
omit [NeZero m] in
lemma near_norm (hm : 3000 ≤ m) : Real.sqrt m*p m 1997≤p m 8 := by
  have hx : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  calc
    _ ≤ (m:ℝ)*p m 1997 := mul_le_mul_of_nonneg_right (sqrt_le hx) (p_nonneg (by positivity) _)
    _ = p m 1996 := p_succ (by positivity : (m:ℝ)≠0) 1996
    _ ≤ _ := p_le hx (by norm_num)
lemma macro_bound (hm : 3000 ≤ m) (Z : V f → EuclideanSpace ℝ (V f))
    (hmac : ∀ v w, |‖Z v-Z w‖^2-KernelApprox.cstar*Real.sqrt m*
         ‖B f (NeZero.pos m) v.val.1 (RoundedCharts.coordinate (u f) (p m 2000) v)-
           B f (NeZero.pos m) w.val.1 (RoundedCharts.coordinate (u f) (p m 2000) w)‖|≤err (m:=m)+8*p m 8)
    (s t : Fin (m^3)) (θ η : E) (hθ : θ∈RoundedCharts.cube 2) (hη : η∈RoundedCharts.cube 2)
    (hs : RoundedCharts.regular (u f s) (p m 2000) θ)
    (ht : RoundedCharts.regular (u f t) (p m 2000) η) :
    |‖Z (vertex f s θ hθ hs)-Z (vertex f t η hη ht)‖^2-KernelApprox.cstar*Real.sqrt m*‖θ-η‖|≤C₀*p m 8 := by
  let v := vertex f s θ hθ hs
  let w := vertex f t η hη ht
  let X := B f (NeZero.pos m) s (RoundedCharts.rounded (u f s) (p m 2000) θ)
  let Y := B f (NeZero.pos m) t (RoundedCharts.rounded (u f t) (p m 2000) η)
  have hτ : 0<p m 2000 := p_pos (by exact_mod_cast NeZero.pos m) _
  have hx : ‖X-θ‖≤p m 1997 := by
    simpa only [rounded_radius (NeZero.pos m)] using rounded_B_error f (NeZero.pos m) (show 2 ≤ m by omega) hτ s θ
  have hy : ‖Y-η‖≤p m 1997 := by
    simpa only [rounded_radius (NeZero.pos m)] using rounded_B_error f (NeZero.pos m) (show 2 ≤ m by omega) hτ t η
  have hnorm : |‖X-Y‖-‖θ-η‖|≤2*p m 1997 := by
    calc
      _ ≤ ‖(X-Y)-(θ-η)‖ := abs_norm_sub_norm_le _ _
      _ = ‖(X-θ)-(Y-η)‖ := by congr 1; abel
      _ ≤ ‖X-θ‖+‖Y-η‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hM := hmac v w
  change |‖Z v-Z w‖^2-KernelApprox.cstar*Real.sqrt m*‖X-Y‖|≤err (m:=m)+8*p m 8 at hM
  have hq : 0≤KernelApprox.cstar*Real.sqrt m := mul_nonneg KernelApprox.cstar_pos.le (Real.sqrt_nonneg _)
  have hh := mul_le_mul_of_nonneg_left (near_norm (m:=m) hm) (mul_nonneg (by norm_num : (0:ℝ)≤2) KernelApprox.cstar_pos.le)
  have he := macro_small hm
  change err (m:=m)≤p m 8/2 at he
  have hM' := abs_le.mp hM
  have hn' := abs_le.mp hnorm
  have hn1 := mul_le_mul_of_nonneg_left hn'.1 hq
  have hn2 := mul_le_mul_of_nonneg_left hn'.2 hq
  change |‖Z v-Z w‖^2-KernelApprox.cstar*Real.sqrt m*‖θ-η‖|≤_
  rw [abs_le]; unfold C₀
  constructor <;> nlinarith [p_nonneg (by positivity : (0:ℝ) ≤ m) 8]
end
end UniformSparsestCut.SourceMetric

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.ContractionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceContraction
open scoped BigOperators RealInnerProductSpace
open SourceParameters SourceCharts SourceMetric
open MeasureTheory
noncomputable section
lemma H_nonneg : 0≤H := integral_nonneg (fun _ => abs_nonneg _)
lemma C_pos : 0<C := by
  have hc := KernelApprox.cstar_pos
  have hr := C₀_pos
  have hh := H_nonneg
  unfold C
  positivity
lemma weight_ge_one {m : ℕ} (hm : 1 ≤ m) (hl : 1≤Real.log m) : 1≤weight m := by
  have hq : 1≤Real.sqrt m := Real.one_le_sqrt.mpr (by exact_mod_cast hm)
  have hll : 1≤(Real.log m)^2 := one_le_pow₀ hl
  have hs : 1≤Real.sqrt (Real.log m) := Real.one_le_sqrt.mpr hl
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hq hll) hs
end
end UniformSparsestCut.SourceContraction

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.CellInterface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.CellInterface
open Filter Set
open scoped Topology BigOperators
noncomputable section
variable {E : Type u3} {I : Type u4} {A : Type u5} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
lemma regular_floor_le (ell : I → E →L[ℝ] ℝ) {τ : ℝ} (hτ : 0<τ)
    {x : E} (hr : regular ell τ x) (i : I) (k : ℤ) :
    k≤label ell τ x i ↔ (k:ℝ)*τ<ell i x := by
  rw [label,Int.le_floor,le_div_iff₀ hτ]
  exact ⟨fun h => lt_of_le_of_ne h (Ne.symm (hr i k)),le_of_lt⟩
omit [Fintype I] [DecidableEq I] in
lemma floor_lt (ell : I → E →L[ℝ] ℝ) {τ : ℝ} (hτ : 0<τ) (x : E) (i : I) (k : ℤ) :
    label ell τ x i<k ↔ ell i x<(k:ℝ)*τ := by
  rw [label,Int.floor_lt,div_lt_iff₀ hτ]

omit [DecidableEq I] in
lemma mem_pattern (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    {τ : ℝ} (hτ : 0<τ) (s : Finset ℤ) {x : E} (hr : regular ell τ x) (i : I) (k : s) :
    (i,k)∈pattern ell pivot τ s x ↔ if 0<pivot i then label ell τ x i<k.val else k.val≤label ell τ x i := by
  simp only [pattern,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hpi : 0<pivot i
  · rw [ite_eq_left hpi,div_neg_iff]
    simp only [hpi,not_lt_of_gt hpi,and_false,false_or,and_true]
    exact sub_neg.trans (floor_lt ell hτ x i k.val).symm
  · have hpn : pivot i<0 := lt_of_le_of_ne (le_of_not_gt hpi) (hp i)
    rw [ite_eq_right hpi,div_neg_iff]
    simp only [hpn,hpi,and_false,or_false,and_true]
    exact sub_pos.trans (regular_floor_le ell hτ hr i k.val).symm

omit [DecidableEq I] in
lemma pattern_labels (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    {τ : ℝ} (hτ : 0<τ) (s : Finset ℤ) {x y : E}
    (hx : regular ell τ x) (hy : regular ell τ y)
    (hbx : ∀ i, label ell τ x i∈s) (hby : ∀ i, label ell τ y i∈s)
    (he : pattern ell pivot τ s x=pattern ell pivot τ s y) : label ell τ x=label ell τ y := by
  funext i
  have hiff (k : s) : (k.val≤label ell τ x i) ↔ (k.val≤label ell τ y i) := by
    have h : (i,k)∈pattern ell pivot τ s x ↔ (i,k)∈pattern ell pivot τ s y := by rw [he]
    rw [mem_pattern ell pivot hp hτ s hx,mem_pattern ell pivot hp hτ s hy] at h
    by_cases hpi : 0<pivot i
    · simp only [hpi,ite_true] at h
      exact not_lt.symm.trans ((not_congr h).trans not_lt)
    · simpa only [hpi,ite_false] using h
  exact le_antisymm ((hiff ⟨_,hbx i⟩).mp le_rfl) ((hiff ⟨_,hby i⟩).mpr le_rfl)

omit [DecidableEq I] in
lemma extension_eq (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    {τ : ℝ} (hτ : 0<τ) (s : Finset ℤ) (U : Set E)
    (hb : ∀ x∈U, regular ell τ x → ∀ i, label ell τ x i∈s)
    (F : LabelVertex ell τ U → A → ℝ) (x : E) (hx : x∈U) (hr : regular ell τ x) :
    extension ell pivot τ s U F (pattern ell pivot τ s x)=F (vertex ell τ x hx hr) := by
  classical
  unfold extension
  split_ifs with h
  · congr 1
    apply Subtype.ext
    exact pattern_labels ell pivot hp hτ s h.choose_spec.choose_spec.choose hr
      (hb _ h.choose_spec.choose h.choose_spec.choose_spec.choose) (hb x hx hr)
      h.choose_spec.choose_spec.choose_spec
  · exact False.elim (h ⟨x,hx,hr,rfl⟩)

end
end UniformSparsestCut.CellInterface

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.Smoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ProductSlice
open MeasureTheory Set CellInterface
open scoped BigOperators
noncomputable section
variable {Z : Type u1} {I : Type u2} {A : Type u3} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure]
  [Fintype I] [Fintype A] [DecidableEq I]

omit [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] [Fintype I] [DecidableEq I] in
lemma normalized_ell (B : I → Z →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    (τ : ℝ) (i : I) (k : ℤ) (x : ℝ × Z) :
    (ell B pivot i x-(k:ℝ)*τ)/pivot i=form (B i) x-(k:ℝ)*τ/pivot i := by
  simp only [ell,_root_.smul_apply,smul_eq_mul,sub_div,mul_div_cancel_left₀ _ (hp i)]

omit [Fintype A] [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] [DecidableEq I] in
lemma cell_eq_extension (B : I → Z →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    (τ : ℝ) (s : Finset ℤ) (U : Set (ℝ × Z)) (F : LabelVertex (ell B pivot) τ U → A → ℝ)
    (x : ℝ × Z) (α : A) :
    cell B (fun i (k : s) => -((k:ℤ)*τ/pivot i))
      (fun P => extension (ell B pivot) pivot τ s U F P α) x =
    extension (ell B pivot) pivot τ s U F (pattern (ell B pivot) pivot τ s x) α := by
  unfold cell pattern
  simp_rw [normalized_ell B pivot hp]
  simp only [sub_eq_add_neg]

end
end UniformSparsestCut.ProductSlice

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.EuclideanCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.EuclideanCells
open MeasureTheory Set ProductSlice CellInterface CoordinateSplit
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m : ℕ} {I : Type u1} {A : Type u2} [Fintype I] [Fintype A] [DecidableEq I]
local notation "E" => EuclideanSpace ℝ (Fin (m+1))
local notation "Z" => EuclideanSpace ℝ (Fin m)

omit [Fintype A] [DecidableEq I] in
lemma chartFunction_eq (u : I → E) (hu : ∀ i, u i 0≠0)
    {τ : ℝ} (hτ : 0<τ) (s : Finset ℤ) (U : Set (ℝ × Z))
    (hb : ∀ x∈U, regular (ell (B u) (pivot u)) τ x → ∀ i, label (ell (B u) (pivot u)) τ x i∈s)
    (F : LabelVertex (ell (B u) (pivot u)) τ U → A → ℝ)
    (x : E) (hx : split x∈U) (hr : regular (ell (B u) (pivot u)) τ (split x)) (a : A) :
    chartFunction u τ s U F a x=F (vertex (ell (B u) (pivot u)) τ (split x) hx hr) a := by
  change cell (B u) (fun i (k : s) => -((k:ℤ)*τ/pivot u i)) (fun P => extension (ell (B u) (pivot u)) (pivot u) τ s U F P a) (split x)=_
  rw [cell_eq_extension (B u) (pivot u) hu (F := F)]
  exact congrFun (extension_eq (ell (B u) (pivot u)) (pivot u) hu hτ s U hb F _ hx hr) a

end
end UniformSparsestCut.EuclideanCells

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.ConcreteCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ConcreteCells
open MeasureTheory Set Filter CoordinateSplit EuclideanCells
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m N S : ℕ} {A : Type u1} [Fintype A]
local notation "E" => EuclideanSpace ℝ (Fin (m+1))
local notation "Z" => EuclideanSpace ℝ (Fin m)

lemma labels_bound (u : Fin N → E) (hu : ∀ i, u i 0≠0) {τ : ℝ} (hτ : 0<τ)
    (hn : ∀ i, ‖u i‖≤2) (x : ℝ × Z) (hx : x∈domain)
    (_hr : CellInterface.regular (ProductSlice.ell (B u) (pivot u)) τ x) (i : Fin N) :
    CellInterface.label (ProductSlice.ell (B u) (pivot u)) τ x i∈labels (m := m) τ := by
  rw [label_eq u hu]
  have hb := (RoundedCharts.integerLabel_bound u hτ hn hx i).trans
    (Int.le_ceil (4*Real.sqrt (m+1:ℕ)/τ+1))
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast (abs_le.mp hb).1
  · exact_mod_cast (abs_le.mp hb).2

omit [Fintype A] in
lemma function_eq (u : Fin S → Fin N → E) (hu : ∀ s i, u s i 0≠0) {τ : ℝ}
    (hτ : 0<τ) (hn : ∀ s i, ‖u s i‖≤2) (F : RoundedCharts.Vertex u τ → A → ℝ)
    (s : Fin S) (x : E) (hx : x∈RoundedCharts.cube 2) (hr : RoundedCharts.regular (u s) τ x) (a : A) :
    function u hu τ F s a x=F ⟨(s,RoundedCharts.integerLabel (u s) τ x),x,hx,hr,rfl⟩ a := by
  have hx' : split x∈domain := by simpa only [domain,mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using hx
  have hr' : CellInterface.regular (ProductSlice.ell (B (u s)) (pivot (u s))) τ (split x) := by
    rw [regular_eq (u s) (hu s)]
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hr
  rw [function,chartFunction_eq (u s) (hu s) hτ _ _ (labels_bound (u s) (hu s) hτ (hn s)) _ x hx' hr']
  congr 1
  apply Subtype.ext
  change (s,CellInterface.label (ProductSlice.ell (B (u s)) (pivot (u s))) τ (split x))=(s,RoundedCharts.integerLabel (u s) τ x)
  congr 1
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using label_eq (u s) (hu s) τ (split x)

end
end UniformSparsestCut.ConcreteCells

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.GaussianCDF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.GaussianCDF
local notation "μ" => gaussianReal 0 1

lemma φ_pos (x : ℝ) : 0 < φ x := gaussianPDFReal_pos _ _ _ (by norm_num)
lemma φ_contDiff : ContDiff ℝ ∞ φ := by unfold φ gaussianPDFReal; fun_prop
lemma φ_integrable : Integrable φ := integrable_gaussianPDFReal _ _
lemma Φ_integral (x : ℝ) : Φ x = ∫ t in Iic x, φ t := by
  rw [Φ, cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral _ (by norm_num)]
  exact ENNReal.toReal_ofReal (integral_nonneg (fun t => gaussianPDFReal_nonneg (0:ℝ) 1 t))

lemma Φ_primitive (x : ℝ) : Φ x = Φ 0 + ∫ t in (0:ℝ)..x, φ t := by
  rw [Φ_integral, Φ_integral]
  have h := intervalIntegral.integral_Iic_sub_Iic
    (φ_integrable.integrableOn (s := Iic 0)) (φ_integrable.integrableOn (s := Iic x))
  linarith

lemma Φ_hasDeriv (x : ℝ) : HasDerivAt Φ (φ x) x := by
  have h := intervalIntegral.integral_hasDerivAt_right
    (φ_contDiff.continuous.intervalIntegrable (0:ℝ) x)
    φ_contDiff.continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    φ_contDiff.continuous.continuousAt
  have h' := h.const_add (Φ 0)
  convert h' using 1 <;> first | rfl | exact funext Φ_primitive

lemma Φ_continuous : Continuous Φ := continuous_iff_continuousAt.mpr (fun x => (Φ_hasDeriv x).continuousAt)
lemma Φ_strictMono : StrictMono Φ := strictMono_of_deriv_pos (fun x => by rw [(Φ_hasDeriv x).deriv]; exact φ_pos x)
lemma Φ_mem (x : ℝ) : Φ x ∈ Ioo (0:ℝ) 1 := by
  constructor
  · exact (cdf_nonneg μ (x-1)).trans_lt (Φ_strictMono (by linarith))
  · exact (Φ_strictMono (show x < x+1 by linarith)).trans_le (cdf_le_one μ (x+1))

lemma Φ_surj {y : ℝ} (hy : y ∈ Ioo (0:ℝ) 1) : ∃ x, Φ x = y := by
  apply intermediate_value_univ₂_eventually₂ (l₁ := atBot) (l₂ := atTop) Φ_continuous continuous_const
  · exact (tendsto_cdf_atBot μ).eventually (eventually_le_nhds hy.1)
  · exact (tendsto_cdf_atTop μ).eventually (eventually_ge_nhds hy.2)

lemma ψ_hasDeriv (x : ℝ) : HasDerivAt ψ (2*φ x) x := (Φ_hasDeriv x).const_mul 2 |>.sub_const 1
lemma ψ_mem (x : ℝ) : ψ x ∈ Ioo (-1:ℝ) 1 := by
  have h := Φ_mem x
  dsimp [ψ]; constructor <;> linarith [h.1,h.2]

lemma ψ_contDiff : ContDiff ℝ 1 ψ := by
  apply contDiff_one_iff_deriv.mpr
  constructor
  · exact fun x => (ψ_hasDeriv x).differentiableAt
  · have he : deriv ψ = fun x => 2*φ x := funext (fun x => (ψ_hasDeriv x).deriv)
    rw [he]
    exact continuous_const.mul φ_contDiff.continuous

lemma ψ_map : (μ).map ψ = uniform := by
  apply Measure.ext_of_Iic
  intro y
  rw [Measure.map_apply ψ_contDiff.continuous.measurable measurableSet_Iic]
  change μ (ψ ⁻¹' Iic y) = (2:ℝ≥0∞)⁻¹ * (volume.restrict (Ioo (-1:ℝ) 1)) (Iic y)
  rw [Measure.restrict_apply measurableSet_Iic]
  by_cases h0 : y ≤ -1
  · have he : ψ ⁻¹' Iic y = ∅ := by
      ext x; simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact not_le.mpr (h0.trans_lt (ψ_mem x).1)
    have he' : Iic y ∩ Ioo (-1:ℝ) 1 = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_empty_iff_false, iff_false]; grind
    simp [he,he']
  by_cases h1 : 1 ≤ y
  · have he : ψ ⁻¹' Iic y = univ := by
      ext x; simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact (ψ_mem x).2.le.trans h1
    have he' : Iic y ∩ Ioo (-1:ℝ) 1 = Ioo (-1:ℝ) 1 := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioo]; constructor <;> grind
    rw [he,he',measure_univ,Real.volume_Ioo]; norm_num;
    exact (ENNReal.inv_mul_cancel (by norm_num) (by norm_num)).symm
  have hy : (y+1)/2 ∈ Ioo (0:ℝ) 1 := by constructor <;> linarith
  obtain ⟨x,hx⟩ := Φ_surj hy
  have he : ψ ⁻¹' Iic y = Iic x := by
    ext z
    simp only [mem_preimage, mem_Iic, ψ]
    rw [show y = 2*Φ x-1 by linarith]
    rw [show 2*Φ z-1 ≤ 2*Φ x-1 ↔ Φ z ≤ Φ x by constructor <;> intro hn <;> linarith]
    exact Φ_strictMono.le_iff_le
  have he' : Iic y ∩ Ioo (-1:ℝ) 1 = Ioc (-1:ℝ) y := by
    ext z; simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]; grind
  rw [he,he',← ofReal_cdf μ x,Real.volume_Ioc]
  change ENNReal.ofReal (Φ x) = (2:ℝ≥0∞)⁻¹ * ENNReal.ofReal (y- -1)
  rw [hx,show y- -1 = y+1 by ring,ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2)]
  simp [div_eq_mul_inv,mul_comm]

instance uniform_probability : IsProbabilityMeasure uniform := by
  rw [← ψ_map]
  exact Measure.isProbabilityMeasure_map ψ_contDiff.continuous.measurable.aemeasurable

end UniformSparsestCut.GaussianCDF

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.CubePoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.CubePoincare
open MeasureTheory ProbabilityTheory Set
open scoped Topology ContDiff ENNReal BigOperators
variable {m : ℕ}

instance cube_probability : IsProbabilityMeasure (cube (m := m)) := by
  unfold cube
  exact Measure.isProbabilityMeasure_map (by fun_prop)

end UniformSparsestCut.CubePoincare

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.CubeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.CubeGeometry
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal
noncomputable section
variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "μ" => CubePoincare.cube (m := m)

lemma pi_uniform : Measure.pi (fun _ : Fin m => GaussianCDF.uniform)=
    (2:ℝ≥0∞)⁻¹^m • (volume : Measure (Fin m → ℝ)).restrict
      (univ.pi (fun _ => Ioo (-1:ℝ) 1)) := by
  apply Measure.pi_eq
  intro s hs
  change (2:ℝ≥0∞)⁻¹^m * ((Measure.pi (fun _ : Fin m => (volume : Measure ℝ))).restrict (univ.pi (fun _ => Ioo (-1:ℝ) 1))) (univ.pi s)=_
  rw [Measure.restrict_pi_pi,Measure.pi_pi]
  simp only [GaussianCDF.uniform,Measure.smul_apply,smul_eq_mul,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma cube_ac : μ ≪ (volume : Measure E) := by
  have h : Measure.pi (fun _ : Fin m => GaussianCDF.uniform) ≪ (volume : Measure (Fin m → ℝ)) := by
    rw [pi_uniform]
    exact (Measure.restrict_le_self.absolutelyContinuous).smul_left _
  have hh := h.map (show Measurable (WithLp.toLp 2 : (Fin m → ℝ) → E) by fun_prop)
  rw [(PiLp.volume_preserving_toLp (Fin m)).map_eq] at hh
  exact hh

lemma uniform_mem : ∀ᵐ t ∂GaussianCDF.uniform, t∈Ioo (-1:ℝ) 1 := by
  have h : GaussianCDF.uniform ≪ volume.restrict (Ioo (-1:ℝ) 1) :=
    (Measure.AbsolutelyContinuous.refl _).smul_left _
  exact h.ae_le (ae_restrict_mem measurableSet_Ioo)

lemma cube_mem : ∀ᵐ x ∂μ, ∀ j, |x j|<1 := by
  apply (ae_map_iff (by fun_prop) (by measurability)).mpr
  apply ae_all_iff.mpr
  intro j
  have h := (measurePreserving_eval (fun _ : Fin m => GaussianCDF.uniform) j).quasiMeasurePreserving.ae uniform_mem
  filter_upwards [h] with x hx
  exact abs_lt.mpr hx

lemma uniform_pow (k : ℕ) : (∫ t, t^k ∂GaussianCDF.uniform)=
    (1-(-1:ℝ)^(k+1))/(2*(k+1)) := by
  rw [GaussianCDF.uniform,integral_smul_measure,restrict_Ioo_eq_restrict_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ)≤1),integral_pow]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_ofNat,smul_eq_mul,one_pow]
  field_simp

lemma uniform_pow_integrable (k : ℕ) : Integrable (fun t : ℝ => t^k) GaussianCDF.uniform := by
  apply (integrable_const (1:ℝ)).mono' (by fun_prop)
  filter_upwards [uniform_mem] with t ht
  rw [Real.norm_eq_abs,abs_pow]
  exact (pow_le_pow_left₀ (abs_nonneg t) (abs_lt.mpr ht).le k).trans_eq (one_pow k)

lemma coordinate_preserving (j : Fin m) : MeasurePreserving (fun x : E => x j) μ GaussianCDF.uniform := by
  refine ⟨by fun_prop,?_⟩
  rw [CubePoincare.cube,Measure.map_map (by fun_prop) (by fun_prop)]
  exact (measurePreserving_eval (fun _ : Fin m => GaussianCDF.uniform) j).map_eq

lemma coordinate_pow (j : Fin m) (k : ℕ) : (∫ x : E, (x j)^k ∂μ)=
    (1-(-1:ℝ)^(k+1))/(2*(k+1)) := by
  rw [← uniform_pow k,← (coordinate_preserving j).map_eq]
  exact (integral_map (by fun_prop) (continuous_id.pow k).aestronglyMeasurable).symm

lemma coordinate_pow_integrable (j : Fin m) (k : ℕ) : Integrable (fun x : E => (x j)^k) μ :=
  ((coordinate_preserving j).integrable_comp (continuous_id.pow k).aestronglyMeasurable).mpr (uniform_pow_integrable k)

lemma cube_norm : ∀ᵐ x : E ∂μ, ‖x‖≤Real.sqrt m := by
  filter_upwards [cube_mem] with x hx
  have h : ‖x‖^2≤(m:ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _j : Fin m, (1:ℝ) := by
        apply Finset.sum_le_sum; intro j _
        rw [Real.norm_eq_abs,sq_abs]
        nlinarith [abs_lt.mp (hx j)]
      _ = _ := by simp
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) m),norm_nonneg x,Real.sqrt_nonneg (m:ℝ)]

lemma pair_norm_bound : ∀ᵐ z : E × E ∂(μ).prod μ, ‖z.1-z.2‖≤2*Real.sqrt m := by
  have hp : ∀ᵐ z : E × E ∂(μ).prod μ, ‖z.1‖≤Real.sqrt m ∧ ‖z.2‖≤Real.sqrt m := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [cube_norm (m := m)] with x hx
    filter_upwards [cube_norm (m := m)] with y hy
    exact ⟨hx,hy⟩
  filter_upwards [hp] with z hz
  exact (norm_sub_le _ _).trans (by linarith [hz.1,hz.2])

lemma pair_norm_integrable : Integrable (fun z : E × E => ‖z.1-z.2‖) ((μ).prod μ) := by
  apply (integrable_const (2*Real.sqrt m)).mono' (by fun_prop)
  simpa only [Real.norm_eq_abs,abs_norm] using pair_norm_bound (m := m)

lemma coordinate_difference_sq (j : Fin m) :
    (∫ z : E × E, (z.1 j-z.2 j)^2 ∂(μ).prod μ)=2/3 := by
  have h1 : Integrable (fun x : E => x j) μ := by simpa using coordinate_pow_integrable j 1
  have h2 := coordinate_pow_integrable j 2
  have he : (fun z : E × E => (z.1 j-z.2 j)^2) =
      (fun z => (z.1 j)^2+(z.2 j)^2-2*(z.1 j*z.2 j)) := by funext z; ring
  rw [he]
  have hsub := integral_sub ((h2.comp_fst μ).add (h2.comp_snd μ)) ((h1.mul_prod h1).const_mul 2)
  simp only [Pi.add_apply] at hsub
  rw [hsub]
  have hadd := integral_add (h2.comp_fst μ) (h2.comp_snd μ)
  rw [hadd,integral_const_mul,integral_prod_mul (fun x : E => x j) (fun x : E => x j)]
  have he0 : (∫ x : E, x j ∂μ)=0 := by simpa using coordinate_pow j 1
  have he2 : (∫ x : E, (x j)^2 ∂μ)=1/3 := by
    have hh := coordinate_pow j 2
    norm_num at hh ⊢
    exact hh
  rw [integral_fun_fst (fun x : E => (x j)^2),integral_fun_snd (fun x : E => (x j)^2)]
  simp [he0,he2]
  norm_num

lemma coordinate_difference_sq_integrable (j : Fin m) :
    Integrable (fun z : E × E => (z.1 j-z.2 j)^2) ((μ).prod μ) := by
  have h1 : Integrable (fun x : E => x j) μ := by simpa using coordinate_pow_integrable j 1
  have h2 := coordinate_pow_integrable j 2
  convert ((h2.comp_fst μ).add (h2.comp_snd μ)).sub ((h1.mul_prod h1).const_mul 2) using 1
  ext z
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

lemma pair_norm_sq_integral : (∫ z : E × E, ‖z.1-z.2‖^2 ∂(μ).prod μ)=2*(m:ℝ)/3 := by
  have hnorm (z : E × E) : ‖z.1-z.2‖^2=∑ j, (z.1 j-z.2 j)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    congr 1
    funext j
    simp only [PiLp.sub_apply,Real.norm_eq_abs,sq_abs]
  simp_rw [hnorm]
  rw [integral_finsetSum _ (fun j _ => coordinate_difference_sq_integrable j)]
  simp only [coordinate_difference_sq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

lemma pair_norm_average (hm : 0 < m) :
    Real.sqrt m/3≤∫ z : E × E, ‖z.1-z.2‖ ∂(μ).prod μ := by
  have hsq : Integrable (fun z : E × E => ‖z.1-z.2‖^2) ((μ).prod μ) := by
    apply (integrable_const ((2*Real.sqrt m)^2)).mono' (by fun_prop)
    filter_upwards [pair_norm_bound (m := m)] with z hz
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hz 2
  have hh := integral_mono_ae hsq (pair_norm_integrable.const_mul (2*Real.sqrt m)) (by
    filter_upwards [pair_norm_bound (m := m)] with z hz
    exact (show ‖z.1-z.2‖^2≤2*Real.sqrt m*‖z.1-z.2‖ by nlinarith [norm_nonneg (z.1-z.2)]))
  rw [pair_norm_sq_integral,integral_const_mul] at hh
  have hp : 0<Real.sqrt (m:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) m)
  nlinarith

end
end UniformSparsestCut.CubeGeometry

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.FiniteDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut

namespace FiniteDuality

variable {E : Type u1} {K : Type u2} [Fintype E] [Fintype K]

lemma dual_functional (f : ((E → ℝ) × ℝ) →L[ℝ] ℝ) :
    ∃ c : E → ℝ, ∃ q : ℝ, ∀ x : (E → ℝ) × ℝ,
      f x = (∑ e, c e * x.1 e) + q * x.2 := by
  classical
  refine ⟨fun e => f (Pi.single e 1, 0), f (0, 1), ?_⟩
  rintro ⟨x,y⟩
  have heq : (x,y) = (∑ e, x e • (Pi.single e 1, (0 : ℝ))) + y • (0, (1 : ℝ)) := by
    ext e <;> simp [Prod.fst_sum, Prod.snd_sum, ← Pi.single_smul,
      Finset.univ_sum_single]
  calc
    f (x,y) = f ((∑ e, x e • (Pi.single e 1, (0 : ℝ))) + y • (0, (1 : ℝ))) :=
      congrArg f heq
    _ = (∑ e, f (Pi.single e 1, 0) * x e) + f (0, 1) * y := by
      simp only [map_add, map_sum, map_smul, smul_eq_mul, mul_comm]

theorem packing_duality_strict (A : E → K → ℝ) (w : K → ℝ)
    (hA : ∀ e k, 0 ≤ A e k) (hcol : ∀ k, 0 < ∑ e, A e k)
    (d : E → ℝ) (hd : ∀ e, 0 ≤ d e) {β : ℝ} (hβ : 0 < β)
    (hbound : ∀ t : K → ℝ, (∀ k, 0 ≤ t k) →
      (∀ e, ∑ k, A e k * t k ≤ d e) → (∑ k, w k * t k) < β) :
    ∃ c : E → ℝ, (∀ e, 0 ≤ c e) ∧
      (∀ k, w k ≤ ∑ e, A e k * c e) ∧ (∑ e, c e * d e) < β := by
  classical
  let C := packingProperCone A w hA hcol
  have hnot : (d,β) ∉ C := by
    rintro ⟨t, ht0, htA, htw⟩
    exact (hbound t ht0 htA).not_ge htw
  obtain ⟨f, hf, hfb⟩ := C.hyperplane_separation_point hnot
  obtain ⟨c,q,hform⟩ := dual_functional f
  have hc (e : E) : 0 ≤ c e := by
    have hx : (Pi.single e 1, (0 : ℝ)) ∈ C := by
      refine ⟨0, by simp, ?_, ?_⟩
      · intro j; simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
        simp [Pi.single_apply]; split_ifs <;> norm_num
      · simp
    simpa [hform, Pi.single_apply, mul_ite] using hf _ hx
  have hq : q < 0 := by
    rw [hform] at hfb
    have hcd : 0 ≤ ∑ e, c e * d e :=
      Finset.sum_nonneg (fun e he => mul_nonneg (hc e) (hd e))
    nlinarith
  have hcoldual (k : K) : 0 ≤ (∑ e, c e * A e k) + q * w k := by
    have hx : ((fun e => A e k), w k) ∈ C := by
      refine ⟨Pi.single k 1, ?_, ?_, ?_⟩
      · intro j; simp [Pi.single_apply]; split_ifs <;> norm_num
      · intro e; simp [Pi.single_apply, mul_ite]
      · simp [Pi.single_apply, mul_ite]
    simpa [hform, Pi.single_apply, mul_ite] using hf _ hx
  refine ⟨fun e => c e / (-q), fun e => div_nonneg (hc e) (neg_pos.mpr hq).le, ?_, ?_⟩
  · intro k
    simp only [← mul_div_assoc, ← Finset.sum_div]
    apply (le_div_iff₀ (neg_pos.mpr hq)).mpr
    have := hcoldual k
    have hsum : (∑ e, A e k * c e) = ∑ e, c e * A e k := by
      apply Finset.sum_congr rfl; intros; ring
    rw [hsum]
    nlinarith
  · simp only [div_mul_eq_mul_div, ← Finset.sum_div]
    apply (div_lt_iff₀ (neg_pos.mpr hq)).mpr
    rw [hform] at hfb
    nlinarith

omit [Fintype K] in

lemma cap_covering (A : E → K → ℝ) (w : K → ℝ)
    (hA : ∀ e k, A e k = 0 ∨ A e k = 1) {W : ℝ} (hW : 0 ≤ W)
    (hw : ∀ k, w k ≤ W) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e)
    (hcover : ∀ k, w k ≤ ∑ e, A e k * c e) :
    ∀ k, w k ≤ ∑ e, A e k * min (c e) W := by
  classical
  intro k
  by_cases hb : ∃ e, A e k = 1 ∧ W < c e
  · obtain ⟨e, he, hce⟩ := hb
    calc
      w k ≤ W := hw k
      _ = A e k * min (c e) W := by rw [he, min_eq_right hce.le]; ring
      _ ≤ ∑ j, A j k * min (c j) W :=
        Finset.single_le_sum (fun j hj => mul_nonneg
          (show 0 ≤ A j k from by rcases hA j k with h | h <;> rw [h] ; norm_num)
          (le_min (hc j) hW)) (Finset.mem_univ e)
  · convert hcover k using 1
    apply Finset.sum_congr rfl
    intro e he
    rcases hA e k with hz | ho
    · simp [hz]
    · have hcW : c e ≤ W := le_of_not_gt (fun h => hb ⟨e, ho, h⟩)
      rw [min_eq_left hcW]

theorem packing_duality (A : E → K → ℝ) (w : K → ℝ)
    (hA : ∀ e k, A e k = 0 ∨ A e k = 1) (hcol : ∀ k, 0 < ∑ e, A e k)
    (d : E → ℝ) (hd : ∀ e, 0 ≤ d e) {β W : ℝ} (hβ : 0 ≤ β) (hW : 0 ≤ W)
    (hw : ∀ k, w k ≤ W)
    (hbound : ∀ t : K → ℝ, (∀ k, 0 ≤ t k) →
      (∀ e, ∑ k, A e k * t k ≤ d e) → (∑ k, w k * t k) ≤ β) :
    ∃ c : E → ℝ, (∀ e, 0 ≤ c e) ∧
      (∀ k, w k ≤ ∑ e, A e k * c e) ∧ (∑ e, c e * d e) ≤ β := by
  classical
  have hA0 : ∀ e k, 0 ≤ A e k := by
    intro e k; rcases hA e k with h | h <;> rw [h] ; norm_num
  let T : Set (E → ℝ) := Icc 0 (fun _ => W) ∩ {c | ∀ k, w k ≤ ∑ e, A e k * c e}
  have hTc : IsCompact T := by
    refine isCompact_Icc.inter_right ?_
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro k
    apply isClosed_le continuous_const
    exact continuous_finsetSum _ (fun e he => continuous_const.mul (continuous_apply e))
  have hcapped : ∀ γ, β < γ → ∃ c ∈ T, (∑ e, c e * d e) < γ := by
    intro γ hγ
    obtain ⟨c, hc0, hcA, hcd⟩ := packing_duality_strict A w hA0 hcol d hd
      (hβ.trans_lt hγ) (fun t ht htA => (hbound t ht htA).trans_lt hγ)
    refine ⟨fun e => min (c e) W, ⟨⟨?_, ?_⟩, cap_covering A w hA hW hw c hc0 hcA⟩, ?_⟩
    · exact fun e => le_min (hc0 e) hW
    · exact fun e => min_le_right _ _
    · exact lt_of_le_of_lt (Finset.sum_le_sum (fun e he =>
        mul_le_mul_of_nonneg_right (min_le_left _ _) (hd e))) hcd
  obtain ⟨c0, hc0, _⟩ := hcapped (β+1) (by linarith)
  have hobj : Continuous (fun c : E → ℝ => ∑ e, c e * d e) :=
    continuous_finsetSum _ (fun e he => (continuous_apply e).mul continuous_const)
  obtain ⟨c, hc, hmin⟩ := hTc.exists_isMinOn ⟨c0,hc0⟩ hobj.continuousOn
  refine ⟨c, hc.1.1, hc.2, ?_⟩
  by_contra! hstrict
  obtain ⟨c', hc', hlt⟩ := hcapped (∑ e, c e * d e) hstrict
  exact hlt.not_ge (hmin hc')

end FiniteDuality

end UniformSparsestCut

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.CutSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut

section CutSums

variable {n : ℕ}

lemma pairSum_nonneg {f : Fin n → Fin n → ℝ} (hf : ∀ i j, 0 ≤ f i j) :
    0 ≤ pairSum f := by
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  split_ifs
  · exact hf _ _
  · exact le_rfl

lemma pairSum_add (f g : Fin n → Fin n → ℝ) :
    pairSum (fun i j => f i j + g i j) = pairSum f + pairSum g := by
  simp only [pairSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

lemma pairSum_smul (a : ℝ) (f : Fin n → Fin n → ℝ) :
    pairSum (fun i j => a * f i j) = a * pairSum f := by
  simp only [pairSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

lemma pairSum_swap (f : Fin n → Fin n → ℝ) (hd : ∀ i, f i i = 0) :
    pairSum f + pairSum (fun i j => f j i) = ∑ i, ∑ j, f i j := by
  unfold pairSum
  conv_lhs => rhs; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rcases lt_trichotomy i j with h | h | h
  · simp [h, not_lt.mpr h.le]
  · subst j; simp [hd]
  · simp [h, not_lt.mpr h.le]

lemma orderedSum_eq_two_pairSum (f : Fin n → Fin n → ℝ)
    (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = 2 * pairSum f := by
  have he : (fun i j => f j i) = f := funext (fun i => funext (fun j => hs j i))
  simpa [he, two_mul] using (pairSum_swap f hd).symm

lemma le_pairSum {f : Fin n → Fin n → ℝ} (hf : ∀ i j, 0 ≤ f i j)
    {i j : Fin n} (hij : i < j) : f i j ≤ pairSum f := by
  calc
    f i j ≤ ∑ k, if i < k then f i k else 0 := by
      have := Finset.single_le_sum (s := Finset.univ)
        (f := fun k => if i < k then f i k else 0)
        (fun k hk => by split_ifs; exact hf _ _; exact le_rfl) (Finset.mem_univ j)
      simpa [hij] using this
    _ ≤ pairSum f := by
      unfold pairSum
      apply Finset.single_le_sum (f := fun k => ∑ l, if k < l then f k l else 0) (a := i)
      · intro k hk
        apply Finset.sum_nonneg
        intro l hl
        split_ifs
        · exact hf _ _
        · exact le_rfl
      · exact Finset.mem_univ i

lemma cutDist_symm (B : Finset (Fin n)) (i j : Fin n) : cutDist B i j = cutDist B j i :=
  abs_sub_comm _ _

lemma cutDist_binary (B : Finset (Fin n)) (i j : Fin n) :
    cutDist B i j = 0 ∨ cutDist B i j = 1 := by
  classical
  unfold cutDist cutIndicator
  split_ifs <;> norm_num

lemma cutDist_triangle (B : Finset (Fin n)) (i j k : Fin n) :
    cutDist B i k ≤ cutDist B i j + cutDist B j k := abs_sub_le _ _ _

lemma cutDemand_eq (B : Finset (Fin n)) :
    cutDemand B = (B.card : ℝ) * ((n : ℝ) - B.card) := by
  unfold cutDemand
  rw [Finset.card_compl, Fintype.card_fin, Nat.cast_sub (show B.card ≤ n by simpa using B.card_le_univ)]

lemma cutDemand_pos (B : Cut n) : 0 < cutDemand B.1 := by
  unfold cutDemand
  apply mul_pos
  · exact_mod_cast Finset.card_pos.mpr B.2.1
  · exact_mod_cast Finset.card_pos.mpr (by simpa [Finset.nonempty_iff_ne_empty] using B.2.2)

lemma ordered_cut_sum (B : Finset (Fin n)) (f : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, f i j * cutDist B i j) =
      (∑ i ∈ B, ∑ j ∈ Bᶜ, f i j) + (∑ i ∈ Bᶜ, ∑ j ∈ B, f i j) := by
  classical
  have hp (i j : Fin n) : f i j * cutDist B i j =
      (if i ∈ B then if j ∈ Bᶜ then f i j else 0 else 0) +
      (if i ∈ Bᶜ then if j ∈ B then f i j else 0 else 0) := by
    unfold cutDist cutIndicator
    by_cases hi : i ∈ B <;> by_cases hj : j ∈ B <;> simp [hi, hj]
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_mem, Finset.univ_inter]

lemma ordered_cut_sum_symm (B : Finset (Fin n)) (f : Fin n → Fin n → ℝ)
    (hs : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, f i j * cutDist B i j) = 2 * (∑ i ∈ B, ∑ j ∈ Bᶜ, f i j) := by
  rw [ordered_cut_sum, two_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact hs j i

lemma pairSum_cut (B : Finset (Fin n)) : pairSum (cutDist B) = cutDemand B := by
  have h := ordered_cut_sum_symm B (fun _ _ => 1) (fun _ _ => rfl)
  simp only [one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [orderedSum_eq_two_pairSum _ (cutDist_symm B) (cutDist_self B)] at h
  unfold cutDemand
  nlinarith

lemma cut_capacity_pair (C : Capacity n) (B : Finset (Fin n)) :
    pairSum (fun i j => C.cap i j * cutDist B i j) =
      ∑ i ∈ B, ∑ j ∈ Bᶜ, C.cap i j := by
  have h := ordered_cut_sum_symm B C.cap C.symm
  rw [orderedSum_eq_two_pairSum _ (fun i j => by rw [C.symm i j, cutDist_symm B i j])
    (fun i => by simp)] at h
  linarith

end CutSums

end UniformSparsestCut

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.Semimetrics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut

section SemimetricBounds

variable {n : ℕ}

lemma NegativeType.semimetric {d : Fin n → Fin n → ℝ} (hd : NegativeType d) :
    IsSemimetric d := by
  obtain ⟨x,hx⟩ := hd.1
  refine ⟨fun i j => by rw [hx]; positivity, ?_, ?_, hd.2⟩
  · intro i j; rw [hx, hx, norm_sub_rev]
  · intro i; simp [hx]

lemma NegativeType.scale {d : Fin n → Fin n → ℝ} (hd : NegativeType d)
    {a : ℝ} (ha : 0 ≤ a) : NegativeType (fun i j => a * d i j) := by
  obtain ⟨x,hx⟩ := hd.1
  refine ⟨⟨fun i => Real.sqrt a • x i, ?_⟩, ?_⟩
  · intro i j
    change a * d i j = _
    rw [← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg a), Real.sq_sqrt ha, hx]
  · intro i j k
    simpa [mul_add] using mul_le_mul_of_nonneg_left (hd.2 i j k) ha

lemma cutDist_negativeType (B : Finset (Fin n)) (hn : 0 < n) : NegativeType (cutDist B) := by
  classical
  let i0 : Fin n := ⟨0,hn⟩
  refine ⟨⟨fun i => EuclideanSpace.single i0 (cutIndicator B i), ?_⟩,
    cutDist_triangle B⟩
  intro i j
  change cutDist B i j = ‖PiLp.single (β := fun _ : Fin n => ℝ) 2 i0 (cutIndicator B i) -
    PiLp.single (β := fun _ : Fin n => ℝ) 2 i0 (cutIndicator B j)‖ ^ 2
  rw [← PiLp.single_sub]
  change cutDist B i j = ‖EuclideanSpace.single i0
    (cutIndicator B i - cutIndicator B j)‖ ^ 2
  rw [PiLp.norm_single, Real.norm_eq_abs]
  change cutDist B i j = cutDist B i j ^ 2
  rcases cutDist_binary B i j with h | h <;> rw [h] <;> norm_num

lemma cut_nonempty (hn : 2 ≤ n) : Nonempty (Cut n) := by
  classical
  let i : Fin n := ⟨0,by omega⟩
  refine ⟨⟨{i}, Finset.singleton_nonempty i, ?_⟩⟩
  intro he
  have hh := congrArg Finset.card he
  simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at hh
  omega

lemma feasible_nonempty (hn : 2 ≤ n) : ∃ d : Fin n → Fin n → ℝ, Feasible d := by
  classical
  obtain ⟨B⟩ := cut_nonempty hn
  refine ⟨fun i j => (cutDemand B.1)⁻¹ * cutDist B.1 i j, ?_, ?_⟩
  · exact (cutDist_negativeType B.1 (by omega)).scale (inv_nonneg.mpr (cutDemand_pos B).le)
  · rw [pairSum_smul, pairSum_cut, inv_mul_cancel₀ (cutDemand_pos B).ne']

lemma normalized_pair_le_one {d : Fin n → Fin n → ℝ} (hd : IsSemimetric d)
    (hD : pairSum d = 1) (i j : Fin n) : d i j ≤ 1 := by
  rcases lt_trichotomy i j with h | h | h
  · simpa [hD] using le_pairSum hd.1 h
  · subst j; rw [hd.2.2.1]; norm_num
  · rw [hd.2.1 i j]; simpa [hD] using le_pairSum hd.1 h

lemma continuous_pairSum : Continuous (pairSum (n := n)) := by
  unfold pairSum
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro j hj
  split_ifs
  · exact (continuous_apply j).comp (continuous_apply i)
  · exact continuous_const

lemma semimetric_closed : IsClosed {d : Fin n → Fin n → ℝ | IsSemimetric d} := by
  unfold IsSemimetric
  simp only [ofPred_and, ofPred_forall]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
  · apply isClosed_iInter; intro i; apply isClosed_iInter; intro j
    exact isClosed_le continuous_const ((continuous_apply j).comp (continuous_apply i))
  · apply isClosed_iInter; intro i; apply isClosed_iInter; intro j
    exact isClosed_eq ((continuous_apply j).comp (continuous_apply i))
      ((continuous_apply i).comp (continuous_apply j))
  · apply isClosed_iInter; intro i
    exact isClosed_eq ((continuous_apply i).comp (continuous_apply i)) continuous_const
  · apply isClosed_iInter; intro i; apply isClosed_iInter; intro j
    apply isClosed_iInter; intro k
    exact isClosed_le (by fun_prop) (by fun_prop)

lemma normalized_semimetric_compact :
    IsCompact {d : Fin n → Fin n → ℝ | IsSemimetric d ∧ pairSum d = 1} := by
  have hclosed : IsClosed {d : Fin n → Fin n → ℝ | IsSemimetric d ∧ pairSum d = 1} :=
    semimetric_closed.inter (isClosed_eq continuous_pairSum continuous_const)
  apply (isCompact_Icc : IsCompact (Icc (0 : Fin n → Fin n → ℝ) (fun _ _ => 1))).of_isClosed_subset hclosed
  intro d hd
  exact ⟨hd.1.1, normalized_pair_le_one hd.1 hd.2⟩

lemma objective_nonneg (C : Capacity n) {d : Fin n → Fin n → ℝ} (hd : IsSemimetric d) :
    0 ≤ pairSum (fun i j => C.cap i j * d i j) :=
  pairSum_nonneg (fun i j => mul_nonneg (C.nonneg i j) (hd.1 i j))

lemma objective_pos_of_cuts (C : Capacity n)
    (hC : ∀ B : Cut n, cutDemand B.1 ≤ ∑ i ∈ B.1, ∑ j ∈ B.1ᶜ, C.cap i j)
    {d : Fin n → Fin n → ℝ} (hd : IsSemimetric d) (hD : pairSum d = 1) :
    0 < pairSum (fun i j => C.cap i j * d i j) := by
  classical
  have hnonneg := objective_nonneg C hd
  by_contra! hnot
  have hzero := le_antisymm hnot hnonneg
  have hp (i j : Fin n) : C.cap i j * d i j = 0 := by
    have h0 : 0 ≤ C.cap i j * d i j := mul_nonneg (C.nonneg i j) (hd.1 i j)
    rcases lt_trichotomy i j with h | h | h
    · have hh := le_pairSum (fun i j => mul_nonneg (C.nonneg i j) (hd.1 i j)) h
      rw [hzero] at hh
      exact le_antisymm hh h0
    · subst j; simp [C.diagonal]
    · rw [C.symm i j, hd.2.1 i j]
      have hh := le_pairSum (fun i j => mul_nonneg (C.nonneg i j) (hd.1 i j)) h
      rw [hzero] at hh
      exact le_antisymm hh (mul_nonneg (C.nonneg _ _) (hd.1 _ _))
  have hd0 : ∀ i j, d i j = 0 := by
    intro i j
    let B : Finset (Fin n) := Finset.univ.filter (fun k => d i k = 0)
    have hi : i ∈ B := by simp [B, hd.2.2.1]
    have hBall : B = Finset.univ := by
      by_contra hne
      let B' : Cut n := ⟨B, ⟨i,hi⟩, hne⟩
      have hjump (u : Fin n) (hu : u ∈ B) (v : Fin n) (hv : v ∈ Bᶜ) : C.cap u v = 0 := by
        have hu0 : d i u = 0 := (Finset.mem_filter.mp hu).2
        have hv0 : d i v ≠ 0 := by simpa [B] using hv
        have hduv : d u v ≠ 0 := by
          intro huv
          have ht := hd.2.2.2 i u v
          rw [hu0,huv] at ht
          exact hv0 (le_antisymm (by simpa using ht) (hd.1 i v))
        exact (mul_eq_zero.mp (hp u v)).resolve_right hduv
      have hsum : (∑ u ∈ B, ∑ v ∈ Bᶜ, C.cap u v) = 0 := by
        apply Finset.sum_eq_zero
        intro u hu
        exact Finset.sum_eq_zero (fun v hv => hjump u hu v hv)
      have hh := hC B'
      change cutDemand B ≤ _ at hh
      rw [hsum] at hh
      exact (cutDemand_pos B').not_ge hh
    have hj : j ∈ B := by rw [hBall]; exact Finset.mem_univ j
    exact (Finset.mem_filter.mp hj).2
  simp [pairSum,hd0] at hD

lemma glValue_pos_of_cuts (C : Capacity n) (hn : 2 ≤ n)
    (hC : ∀ B : Cut n, cutDemand B.1 ≤ ∑ i ∈ B.1, ∑ j ∈ B.1ᶜ, C.cap i j) :
    0 < glValue C := by
  obtain ⟨d0,hd0⟩ := feasible_nonempty hn
  have hobj : Continuous (fun d : Fin n → Fin n → ℝ => pairSum (fun i j => C.cap i j * d i j)) := by
    apply continuous_pairSum.comp
    apply continuous_pi; intro i; apply continuous_pi; intro j
    exact continuous_const.mul ((continuous_apply j).comp (continuous_apply i))
  obtain ⟨d,hd,hmin⟩ := normalized_semimetric_compact.exists_isMinOn
    ⟨d0,hd0.1.semimetric,hd0.2⟩ hobj.continuousOn
  apply (objective_pos_of_cuts C hC hd.1 hd.2).trans_le
  apply le_csInf
  · exact ⟨_,d0,hd0,rfl⟩
  · rintro b ⟨d',hd',rfl⟩
    exact hmin ⟨hd'.1.semimetric,hd'.2⟩

lemma OPT_ge_one_of_cuts (C : Capacity n) (hn : 2 ≤ n)
    (hC : ∀ B : Cut n, cutDemand B.1 ≤ ∑ i ∈ B.1, ∑ j ∈ B.1ᶜ, C.cap i j) :
    1 ≤ OPT C := by
  obtain ⟨B0⟩ := cut_nonempty hn
  apply le_csInf
  · exact ⟨_,B0.1,B0.2.1,B0.2.2,rfl⟩
  · rintro b ⟨B,hB,hB',rfl⟩
    unfold cutRatio
    rw [← cutDemand_eq]
    exact (one_le_div (cutDemand_pos ⟨B,hB,hB'⟩)).mpr (hC ⟨B,hB,hB'⟩)

end SemimetricBounds

end UniformSparsestCut

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.CutDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut

section CutConeDuality
variable {n : ℕ}

lemma pairSum_sum {K : Type u1} [Fintype K] (f : K → Fin n → Fin n → ℝ) :
    pairSum (fun i j => ∑ k, f k i j) = ∑ k, pairSum (f k) := by
  classical
  unfold pairSum
  have hh (i j : Fin n) : (if i < j then ∑ k, f k i j else 0) =
      ∑ k, if i < j then f k i j else 0 := by
    split_ifs <;> simp_all
  simp_rw [hh]
  conv_lhs => arg 2; intro i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

lemma symmetrize_objective (c : (Fin n × Fin n) → ℝ) (hc : ∀ e, 0 ≤ c e)
    (d : Fin n → Fin n → ℝ) (hs : ∀ i j, d i j = d j i) (hd : ∀ i, d i i = 0) :
    pairSum (fun i j => (symmetrizeCapacity c hc).cap i j * d i j) =
      ∑ e, c e * d e.1 e.2 := by
  have hfun : (fun i j => (symmetrizeCapacity c hc).cap i j * d i j) =
      (fun i j => c (i,j) * d i j + c (j,i) * d j i) := by
    funext i j
    by_cases h : i = j
    · subst j; simp [hd]
    · simp [symmetrizeCapacity, h, hs j i, add_mul]
  rw [hfun, pairSum_add, pairSum_swap _ (fun i => by simp [hd])]
  exact (Fintype.sum_prod_type (fun e : Fin n × Fin n => c e * d e.1 e.2)).symm

theorem cut_cone_duality (hn : 2 ≤ n) (d : Fin n → Fin n → ℝ)
    (hd : NegativeType d) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (havg : (n : ℝ)^2 * a ≤ ∑ i, ∑ j, d i j)
    (hcon : ∀ (K : Type) [Fintype K] (F : Fin n → K → ℝ),
      (∀ i j, (∑ k, |F i k - F j k|) ≤ d i j) →
      (∑ i, ∑ j, ∑ k, |F i k - F j k|) ≤ (n : ℝ)^2 * b) :
    ∃ C : Capacity n, 1 ≤ OPT C ∧ 0 < glValue C ∧ glValue C ≤ b / a := by
  classical
  have hsemi := hd.semimetric
  let A : (Fin n × Fin n) → Cut n → ℝ := fun e B => cutDist B.1 e.1 e.2
  let w : Cut n → ℝ := fun B => cutDemand B.1
  have hcol (B : Cut n) : 0 < ∑ e, A e B := by
    change 0 < ∑ e : Fin n × Fin n, cutDist B.1 e.1 e.2
    rw [Fintype.sum_prod_type, orderedSum_eq_two_pairSum _ (cutDist_symm _) (cutDist_self _), pairSum_cut]
    exact mul_pos (by norm_num) (cutDemand_pos B)
  have hbound (t : Cut n → ℝ) (ht : ∀ B, 0 ≤ t B)
      (htd : ∀ e, ∑ B, A e B * t B ≤ d e.1 e.2) :
      (∑ B, w B * t B) ≤ (n : ℝ)^2 * b / 2 := by
    let F : Fin n → Cut n → ℝ := fun i B => t B * cutIndicator B.1 i
    have hFd (i j : Fin n) : (∑ B, |F i B - F j B|) = ∑ B, t B * cutDist B.1 i j := by
      apply Finset.sum_congr rfl
      intro B hB
      simp [F, cutDist, ← mul_sub, abs_mul, abs_of_nonneg (ht B)]
    have hcontract (i j : Fin n) : (∑ B, |F i B - F j B|) ≤ d i j := by
      rw [hFd]
      simpa only [A, mul_comm] using htd (i,j)
    have htavg := hcon (Cut n) F hcontract
    simp_rw [hFd] at htavg
    have hsym (i j : Fin n) : (∑ B, t B * cutDist B.1 i j) =
        ∑ B, t B * cutDist B.1 j i := by simp_rw [cutDist_symm _ i j]
    rw [orderedSum_eq_two_pairSum _ hsym (fun i => by simp), pairSum_sum] at htavg
    simp_rw [pairSum_smul, pairSum_cut] at htavg
    have he : (∑ B, w B * t B) = ∑ B, t B * cutDemand B.1 := by
      unfold w; simp_rw [mul_comm]
    rw [he]
    linarith
  let W : ℝ := ∑ B : Cut n, w B
  have hw0 (B : Cut n) : 0 ≤ w B := (cutDemand_pos B).le
  obtain ⟨c,hc,hcover,hobj⟩ := FiniteDuality.packing_duality A w
    (fun e B => cutDist_binary B.1 e.1 e.2) hcol
    (fun e => d e.1 e.2) (fun e => hsemi.1 _ _)
    (show 0 ≤ (n : ℝ)^2 * b / 2 by positivity)
    (show 0 ≤ W from Finset.sum_nonneg (fun B hB => hw0 B))
    (fun B => Finset.single_le_sum (fun B hB => hw0 B) (Finset.mem_univ B)) hbound
  let C := symmetrizeCapacity c hc
  have hC (B : Cut n) : cutDemand B.1 ≤ ∑ i ∈ B.1, ∑ j ∈ B.1ᶜ, C.cap i j := by
    rw [← cut_capacity_pair, symmetrize_objective c hc _ (cutDist_symm _) (cutDist_self _)]
    simpa only [A, w, mul_comm] using hcover B
  refine ⟨C, OPT_ge_one_of_cuts C hn hC, glValue_pos_of_cuts C hn hC, ?_⟩
  let D := pairSum d
  have havg' : (n : ℝ)^2 * a ≤ 2 * D := by
    simpa only [orderedSum_eq_two_pairSum d hsemi.2.1 hsemi.2.2.1] using havg
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hD : 0 < D := by nlinarith [mul_pos (sq_pos_of_pos hn0) ha]
  let d' := fun i j => D⁻¹ * d i j
  have hd' : Feasible d' := by
    refine ⟨hd.scale (inv_nonneg.mpr hD.le), ?_⟩
    change pairSum (fun i j => D⁻¹ * d i j) = 1
    rw [pairSum_smul, inv_mul_cancel₀ hD.ne']
  have hbdd : BddBelow {r | ∃ d : Fin n → Fin n → ℝ, Feasible d ∧
      r = pairSum (fun i j => C.cap i j * d i j)} := by
    refine ⟨0, ?_⟩
    rintro r ⟨d,hd,rfl⟩
    exact objective_nonneg C hd.1.semimetric
  have hgl : glValue C ≤ pairSum (fun i j => C.cap i j * d' i j) :=
    csInf_le hbdd ⟨d',hd',rfl⟩
  apply hgl.trans
  have hscale : pairSum (fun i j => C.cap i j * d' i j) =
      (pairSum (fun i j => C.cap i j * d i j)) / D := by
    simp only [d', div_eq_mul_inv]
    rw [mul_comm _ D⁻¹, ← pairSum_smul D⁻¹]
    congr 1
    funext i j; ring
  rw [hscale, symmetrize_objective c hc d hsemi.2.1 hsemi.2.2.1,
    div_le_div_iff₀ hD ha]
  have hh1 := mul_le_mul_of_nonneg_right hobj ha.le
  have hh2 := mul_le_mul_of_nonneg_right havg' hb.le
  nlinarith

end CutConeDuality

end UniformSparsestCut

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.VertexMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.VertexMeasure
open MeasureTheory Set Filter
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m N S : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "μ" => (CubePoincare.cube (m:=m))
attribute [local instance] OAI.UniformSparsestCut.VertexMeasure.instMeasurableSpaceVertex
local instance instMeasurableSingletonClassVertex {u : Fin S → Fin N → E} {τ : ℝ} : MeasurableSingletonClass (RoundedCharts.Vertex u τ) := by unfold RoundedCharts.Vertex; infer_instance
lemma cube_measurable (R : ℝ) : MeasurableSet (RoundedCharts.cube (m:=m) R) := by
  rw [show RoundedCharts.cube (m:=m) R=(⋂ j : Fin m, {x : E | |x j|<R}) by ext x; simp [RoundedCharts.cube]]
  apply MeasurableSet.iInter
  intro j
  exact measurableSet_lt (by fun_prop) measurable_const
lemma regular_measurable (u : Fin N → E) (τ : ℝ) : MeasurableSet {x | RoundedCharts.regular u τ x} := by
  rw [show {x | RoundedCharts.regular u τ x}=(⋂ i : Fin N, ⋂ k : ℤ, {x : E | inner ℝ (u i) x ≠ (k:ℝ)*τ}) by ext x; simp [RoundedCharts.regular]]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro k
  exact (isClosed_eq (by fun_prop : Continuous (fun x : E => inner ℝ (u i) x)) continuous_const).measurableSet.compl
lemma integer_measurable (u : Fin N → E) (τ : ℝ) : Measurable (RoundedCharts.integerLabel u τ) := by
  apply Measurable.of_eval
  intro i
  exact Int.measurable_floor.comp (by fun_prop)
lemma label_measurable (u : Fin S → Fin N → E) (τ : ℝ) (s : Fin S) (v₀ : RoundedCharts.Vertex u τ) :
    Measurable (label u τ s v₀) := by
  classical
  have hh : Measurable (fun x : E => if x∈RoundedCharts.cube 2 ∧ RoundedCharts.regular (u s) τ x then
      (s,RoundedCharts.integerLabel (u s) τ x) else v₀.val) :=
    (measurable_const.prodMk (integer_measurable (u s) τ)).ite ((cube_measurable 2).inter (regular_measurable (u s) τ)) measurable_const
  have hval : Measurable (fun x => (label u τ s v₀ x).val) := by
    convert hh using 1
    funext x
    by_cases hgood : x ∈ RoundedCharts.cube 2 ∧ RoundedCharts.regular (u s) τ x <;>
      simp [label, hgood]
  exact hval.subtype_mk
lemma ae_good (u : Fin N → E) (hu : ∀ i, u i≠0) (τ : ℝ) :
    ∀ᵐ x : E ∂μ, x∈RoundedCharts.cube 2 ∧ RoundedCharts.regular u τ x := by
  filter_upwards [CubeGeometry.cube_mem (m:=m), CubeGeometry.cube_ac.ae_le (RoundedCharts.ae_regular u τ hu)] with x hx hr
  exact ⟨fun j => (hx j).trans (by norm_num),hr⟩
lemma vertex_nonempty (u : Fin S → Fin N → E) (hu : ∀ s i, u s i≠0) (τ : ℝ) (s : Fin S) :
    Nonempty (RoundedCharts.Vertex u τ) := by
  obtain ⟨x,hx,hr⟩ := (ae_good (u s) (hu s) τ).exists
  exact ⟨⟨(s,RoundedCharts.integerLabel (u s) τ x),x,hx,hr,rfl⟩⟩
instance probability (u : Fin S → Fin N → E) (τ : ℝ) (s : Fin S) (v₀ : RoundedCharts.Vertex u τ) :
    IsProbabilityMeasure (measure u τ s v₀) := by
  change IsProbabilityMeasure ((μ).map (label u τ s v₀))
  exact Measure.isProbabilityMeasure_map (label_measurable u τ s v₀).aemeasurable
lemma finite_weights {V : Type u1} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (ν : Measure V) [IsProbabilityMeasure ν] : (∑ v, ν.real {v})=1 := by
  have h : (∫ _ : V, (1:ℝ) ∂ν)=∑ v, ν.real {v} • (1:ℝ) := integral_fintype (integrable_const _)
  simp
lemma pair_average (u : Fin S → Fin N → E) (τ : ℝ) (s : Fin S) (v₀ : RoundedCharts.Vertex u τ)
    [Fintype (RoundedCharts.Vertex u τ)] (d : RoundedCharts.Vertex u τ → RoundedCharts.Vertex u τ → ℝ) :
    (∑ v, ∑ w, (measure u τ s v₀).real {v}*(measure u τ s v₀).real {w}*d v w)=
      ∫ z : E × E, d (label u τ s v₀ z.1) (label u τ s v₀ z.2) ∂(μ).prod μ := by
  let ν := measure u τ s v₀
  calc
    _ = ∫ z : RoundedCharts.Vertex u τ × RoundedCharts.Vertex u τ, d z.1 z.2 ∂ν.prod ν := by
      rw [integral_fintype Integrable.of_finite, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro w hw
      rw [show ({(v,w)} : Set (RoundedCharts.Vertex u τ × RoundedCharts.Vertex u τ))={v}×ˢ{w} by ext z; simp]
      rw [measureReal_prod_prod]
      rfl
    _ = _ := by
      change (∫ z, d z.1 z.2 ∂((μ).map (label u τ s v₀)).prod ((μ).map (label u τ s v₀)))=_
      rw [Measure.map_prod_map μ μ (label_measurable u τ s v₀) (label_measurable u τ s v₀)]
      exact integral_map ((label_measurable u τ s v₀).prodMap (label_measurable u τ s v₀)).aemeasurable
        (measurable_of_countable _).aestronglyMeasurable
end
end UniformSparsestCut.VertexMeasure

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.WeightedMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceWeighted
open MeasureTheory Set Filter
open scoped BigOperators RealInnerProductSpace
open SourceCharts SourceParameters SourceMetric
noncomputable section
attribute [local instance] OAI.UniformSparsestCut.SourceWeighted.instMeasurableSpaceVertex
local instance instMeasurableSingletonClassVertex {m N S : ℕ} {u : Fin S → Fin N → EuclideanSpace ℝ (Fin m)} {τ : ℝ} :
    MeasurableSingletonClass (RoundedCharts.Vertex u τ) := by unfold RoundedCharts.Vertex; infer_instance

lemma D_pos : 0<D := by
  have hc := KernelApprox.cstar_pos
  have hr := C₀_pos
  unfold D
  positivity
lemma diameter {m : ℕ} [NeZero m] (f : PivotFamily.PFamily m) (hm : 3000 ≤ m)
    (Z : V f → EuclideanSpace ℝ (V f))
    (hmac : ∀ v w, |‖Z v-Z w‖^2-KernelApprox.cstar*Real.sqrt m*
         ‖B f (NeZero.pos m) v.val.1 (RoundedCharts.coordinate (u f) (p m 2000) v)-
           B f (NeZero.pos m) w.val.1 (RoundedCharts.coordinate (u f) (p m 2000) w)‖|≤err (m:=m)+8*p m 8)
    (v w : V f) : ‖Z v-Z w‖^2≤D*m := by
  obtain ⟨θ,hθ,hr,he⟩ := v.property
  obtain ⟨η,hη,hs,hf⟩ := w.property
  have hv : vertex f v.val.1 θ hθ hr=v := by apply Subtype.ext; change (v.val.1,_)=(v.val.1,_); rw [he]
  have hw : vertex f w.val.1 η hη hs=w := by apply Subtype.ext; change (w.val.1,_)=(w.val.1,_); rw [hf]
  have hh := (abs_le.mp (macro_bound f hm Z hmac v.val.1 w.val.1 θ η hθ hη hr hs)).2
  rw [hv,hw] at hh
  have hn : ‖θ-η‖≤4*Real.sqrt m := by
    have h1 := RoundedCharts.cube_norm (by norm_num : (0:ℝ)≤2) hθ
    have h2 := RoundedCharts.cube_norm (by norm_num : (0:ℝ)≤2) hη
    have h3 := norm_sub_le θ η
    linarith
  have hx : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hp : p m 8 ≤ (m:ℝ) := (p_one_le hx _).trans hx
  have hq := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) m)
  have h1 := mul_le_mul_of_nonneg_left hn (mul_nonneg KernelApprox.cstar_pos.le (Real.sqrt_nonneg m))
  have h2 := mul_le_mul_of_nonneg_left hp C₀_pos.le
  have he : KernelApprox.cstar*Real.sqrt m*(4*Real.sqrt m)=4*KernelApprox.cstar*(m:ℝ) := by
    calc
      _ = 4*KernelApprox.cstar*(Real.sqrt m)^2 := by ring
      _ = _ := by rw [hq]
  rw [he] at h1
  unfold D
  linarith only [hh,h1,h2]

lemma weighted_instance {m : ℕ} (f : PivotFamily.PFamily (m+1))
    (hm : 3000 ≤ m+1) (hl : 1≤Real.log (m+1:ℕ)) (hH : SourceContraction.H ≤ (m+1:ℕ)) :
    ∃ (Z : V f → EuclideanSpace ℝ (V f)) (w : V f → ℝ),
      (∀ v, 0≤w v) ∧ (∑ v, w v)=1 ∧
      (∀ v w z, ‖Z v-Z z‖^2≤‖Z v-Z w‖^2+‖Z w-Z z‖^2) ∧
      (∀ v z, ‖Z v-Z z‖^2≤D*(m+1:ℕ)) ∧
      KernelApprox.cstar/3*(m+1:ℕ)-C₀*p (m+1:ℕ) 8≤∑ v, ∑ z, w v*w z*‖Z v-Z z‖^2 ∧
      ∀ (A : Type) [Fintype A] (F : V f → A → ℝ),
        (∀ v z, (∑ a, |F v a-F z a|)≤‖Z v-Z z‖^2) →
        (∑ v, ∑ z, w v*w z*(∑ a, |F v a-F z a|))≤SourceContraction.C*SourceContraction.weight (m+1) := by
  classical
  let d := m+1
  let E := EuclideanSpace ℝ (Fin d)
  let μ := CubePoincare.cube (m:=d)
  have hm0 : 0 < d := Nat.succ_pos m
  have hx0 : (0:ℝ) < d := by exact_mod_cast hm0
  have hτ := p_pos hx0 2000
  have hu0 : ∀ s i, u f s i 0≠0 := by
    intro s i h
    have hp := u_pivot f hm0 s i 0
    rw [h,abs_zero] at hp
    have hh : (0:ℝ)<1/((d:ℝ)^30*Real.sqrt d) := by positivity
    linarith
  have hu : ∀ s i, u f s i≠0 := by
    intro s i h
    exact hu0 s i (by rw [h]; rfl)
  let s : Fin (d^3) := ⟨0,by positivity⟩
  obtain ⟨v₀⟩ := VertexMeasure.vertex_nonempty (u f) hu (p d 2000) s
  let L := VertexMeasure.label (u f) (p d 2000) s v₀
  let ν := VertexMeasure.measure (u f) (p d 2000) s v₀
  let w : V f → ℝ := fun v => ν.real {v}
  have hws : (∑ v, w v)=1 := VertexMeasure.finite_weights ν
  have hw : ∀ v, 0≤w v := fun v => measureReal_nonneg
  have hL := VertexMeasure.label_measurable (u f) (p d 2000) s v₀
  have hgood : ∀ᵐ x : E ∂μ, x∈RoundedCharts.cube 2 ∧ RoundedCharts.regular (u f s) (p d 2000) x :=
    VertexMeasure.ae_good (u f s) (hu s) (p d 2000)
  have hgoodpair : ∀ᵐ z : E × E ∂μ.prod μ,
      (z.1∈RoundedCharts.cube 2 ∧ RoundedCharts.regular (u f s) (p d 2000) z.1) ∧
      (z.2∈RoundedCharts.cube 2 ∧ RoundedCharts.regular (u f s) (p d 2000) z.2) := by
    apply (Measure.ae_prod_iff_ae_ae (MeasurableSet.prod
      ((VertexMeasure.cube_measurable 2).inter (VertexMeasure.regular_measurable (u f s) (p d 2000)))
      ((VertexMeasure.cube_measurable 2).inter (VertexMeasure.regular_measurable (u f s) (p d 2000))))).mpr
    filter_upwards [hgood] with x hx
    filter_upwards [hgood] with y hy
    exact ⟨hx,hy⟩
  obtain ⟨Z,htri,hmac,hloc⟩ := SourceMetric.realization f hm hl
  have hdiam := diameter f hm Z hmac
  refine ⟨Z,w,hw,hws,htri,hdiam,?_,?_⟩
  · rw [VertexMeasure.pair_average (u f) (p d 2000) s v₀]
    have hi : Integrable (fun z : E × E => ‖Z (L z.1)-Z (L z.2)‖^2) (μ.prod μ) := by
      apply (integrable_const (D*d)).mono'
      · exact ((measurable_of_countable (fun z : V f × V f => ‖Z z.1-Z z.2‖^2)).comp (hL.prodMap hL)).aestronglyMeasurable
      · exact ae_of_all _ (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]; exact hdiam _ _)
    have hb : (∫ z : E × E, KernelApprox.cstar*Real.sqrt d*‖z.1-z.2‖-C₀*p d 8 ∂μ.prod μ)≤
        ∫ z : E × E, ‖Z (L z.1)-Z (L z.2)‖^2 ∂μ.prod μ := by
      apply integral_mono_ae ((CubeGeometry.pair_norm_integrable.const_mul _).sub (integrable_const _)) hi
      filter_upwards [hgoodpair] with z hz
      have he1 : L z.1=vertex f s z.1 hz.1.1 hz.1.2 := by
        exact dite_eq_left hz.1
      have he2 : L z.2=vertex f s z.2 hz.2.1 hz.2.2 := by
        exact dite_eq_left hz.2
      rw [he1,he2]
      have hh := (abs_le.mp (macro_bound f hm Z hmac s s z.1 z.2 hz.1.1 hz.2.1 hz.1.2 hz.2.2)).1
      change KernelApprox.cstar*Real.sqrt (m+1:ℕ)*‖z.1-z.2‖-C₀*p (m+1:ℕ) 8≤_
      linarith only [hh]
    rw [integral_sub (CubeGeometry.pair_norm_integrable.const_mul _) (integrable_const _),integral_const_mul,integral_const] at hb
    simp at hb
    have ha := mul_le_mul_of_nonneg_left (CubeGeometry.pair_norm_average hm0)
      (mul_nonneg KernelApprox.cstar_pos.le (Real.sqrt_nonneg d))
    have hs := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) d)
    change KernelApprox.cstar/3*(d:ℝ)-C₀*p d 8≤_
    have he : KernelApprox.cstar*Real.sqrt d*(Real.sqrt d/3)=KernelApprox.cstar/3*(d:ℝ) := by
      calc
        _ = KernelApprox.cstar/3*(Real.sqrt d)^2 := by ring
        _ = _ := by rw [hs]
    rw [he] at ha
    linarith only [ha,hb]
  · intro A hA F hF
    rw [VertexMeasure.pair_average (u f) (p d 2000) s v₀]
    have he : (fun z : E × E => ∑ a, |F (L z.1) a-F (L z.2) a|)=ᵐ[μ.prod μ]
        (fun z => ∑ a, |ConcreteCells.function (u f) hu0 (p d 2000) F s a z.1-
          ConcreteCells.function (u f) hu0 (p d 2000) F s a z.2|) := by
      filter_upwards [hgoodpair] with z hz
      apply Finset.sum_congr rfl
      intro a ha
      rw [ConcreteCells.function_eq (u f) hu0 hτ (fun s i => (u_norm f hm0 s i).2) F s z.1 hz.1.1 hz.1.2 a,
        ConcreteCells.function_eq (u f) hu0 hτ (fun s i => (u_norm f hm0 s i).2) F s z.2 hz.2.1 hz.2.2 a]
      simp [L, VertexMeasure.label, hz.1, hz.2]
    rw [integral_congr_ae he]
    exact SourceContraction.integral_bound f hm hl hH Z hmac hloc F hF s
end
end UniformSparsestCut.SourceWeighted

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.LabelCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.LabelCount
open scoped BigOperators RealInnerProductSpace
open UniformSparsestCut
variable {m N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

lemma signature_injective (B : ℤ) (A : Finset (Fin N → ℤ))
    (hA : ∀ l ∈ A, ∀ i, l i ∈ Finset.Icc (-B) B) :
    Set.InjOn (signature B) (↑A : Set (Fin N → ℤ)) := by
  intro l hl k hk he
  funext i
  apply le_antisymm
  · have hm : (i,⟨l i,hA l hl i⟩) ∈ signature B l := by simp [signature]
    rw [he] at hm
    simpa [signature] using hm
  · have hm : (i,⟨k i,hA k hk i⟩) ∈ signature B k := by simp [signature]
    rw [← he] at hm
    simpa [signature] using hm

lemma regular_floor_iff (u : Fin N → E) {τ : ℝ} (hτ : 0 < τ)
    {θ : E} (hθ : RoundedCharts.regular u τ θ) (i : Fin N) (k : ℤ) :
    k ≤ RoundedCharts.integerLabel u τ θ i ↔ (k:ℝ)*τ < inner ℝ (u i) θ := by
  rw [RoundedCharts.integerLabel, Int.le_floor]
  rw [le_div_iff₀ hτ]
  exact ⟨fun h => lt_of_le_of_ne h (Ne.symm (hθ i k)), le_of_lt⟩

lemma label_count (u : Fin N → E) {τ : ℝ} (hτ : 0 < τ) (B : ℤ)
    (A : Finset (Fin N → ℤ))
    (hb : ∀ l ∈ A, ∀ i, l i ∈ Finset.Icc (-B) B)
    (hA : ∀ l ∈ A, ∃ θ : E, RoundedCharts.regular u τ θ ∧ RoundedCharts.integerLabel u τ θ = l) :
    A.card ≤ ∑ j ∈ Finset.Iic (m+1), (N*(Finset.Icc (-B) B).card).choose j := by
  let P := A.image (signature B)
  have hP : ∀ p ∈ P, ∃ θ : E × ℝ, ∀ i,
      affineForm u τ B i θ ≠ 0 ∧ (0 < affineForm u τ B i θ ↔ i ∈ p) := by
    intro p hp
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨θ,hr,hθ⟩ := hA l hl
    refine ⟨(θ,1),?_⟩
    intro i
    have he : affineForm u τ B i (θ,1) = inner ℝ (u i.1) θ-(i.2.val:ℝ)*τ := by
      simp [affineForm]
    rw [he]
    refine ⟨sub_ne_zero.mpr (hr _ _),?_⟩
    rw [sub_pos, ← regular_floor_iff u hτ hr,hθ]
    simp [signature]
  have hc := HyperplaneCount.sign_patterns_bound (affineForm u τ B) P hP
  have hdim : Module.finrank ℝ (E × ℝ) = m+1 := by simp [Module.finrank_prod]
  have hcard : Fintype.card (Fin N × ↥(Finset.Icc (-B) B)) = N*(Finset.Icc (-B) B).card := by simp
  rw [hdim,hcard] at hc
  rwa [Finset.card_image_of_injOn (signature_injective B A hb)] at hc

end UniformSparsestCut.LabelCount

namespace UniformSparsestCut.LabelCount
open scoped BigOperators
noncomputable section
lemma power_sum_le (H d : ℕ) : (∑ j∈Finset.range (d+1), H^j)≤(H+1)^d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ]
    calc
      _ ≤ (H+1)^d+H^(d+1) := Nat.add_le_add_right ih _
      _ ≤ (H+1)^d+(H+1)^d*H := by
        rw [pow_succ]
        gcongr
        omega
      _ = (H+1)^(d+1) := by ring
lemma binomial_sum_le (H d : ℕ) : (∑ j∈Finset.Iic d, H.choose j)≤(H+1)^d := by
  have he : Finset.Iic d=Finset.range (d+1) := by ext j; simp
  rw [he]
  exact (Finset.sum_le_sum (fun j _ => Nat.choose_le_pow H j)).trans (power_sum_le H d)
variable {m N S : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
lemma vertex_count (u : Fin S → Fin N → E) {τ : ℝ} (hτ : 0<τ)
    [Fintype (RoundedCharts.Vertex u τ)] (B : ℤ)
    (hb : ∀ v : RoundedCharts.Vertex u τ, ∀ i, v.val.2 i∈Finset.Icc (-B) B) :
    Fintype.card (RoundedCharts.Vertex u τ)≤S*(N*(Finset.Icc (-B) B).card+1)^(m+1) := by
  classical
  let T (s : Fin S) := Finset.univ.filter (fun v : RoundedCharts.Vertex u τ => v.val.1=s)
  let A (s : Fin S) := (T s).image (fun v => v.val.2)
  have hcard (s : Fin S) : (T s).card=(A s).card := by
    apply (Finset.card_image_of_injOn _).symm
    intro v hv w hw h
    apply Subtype.ext
    apply Prod.ext
    · exact (Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm
    · exact h
  have hs (s : Fin S) : (T s).card≤(N*(Finset.Icc (-B) B).card+1)^(m+1) := by
    rw [hcard]
    apply (label_count (u s) hτ B (A s) ?_ ?_).trans (binomial_sum_le _ _)
    · intro l hl i
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
      exact hb v i
    · intro l hl
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨θ,hθ,hr,hl⟩ := v.property
      have he : v.val.1=s := (Finset.mem_filter.mp hv).2
      exact ⟨θ,by simpa only [← he] using hr,by simpa only [← he] using hl⟩
  calc
    _ = ∑ s, (T s).card := by
      simpa only [Finset.card_univ] using (Finset.card_eq_sum_card_fiberwise
        (f := fun v : RoundedCharts.Vertex u τ => v.val.1)
        (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _))
    _ ≤ ∑ _s : Fin S, (N*(Finset.Icc (-B) B).card+1)^(m+1) := Finset.sum_le_sum (fun s _ => hs s)
    _ = _ := by simp
end
end UniformSparsestCut.LabelCount

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.Replication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.Replication
variable {V : Type u1} [Fintype V]
lemma n_sum (M : ℕ) (w : V → ℝ) : n M w=∑ v, count M w v := by
  change Fintype.card ((v : V) × Fin (count M w v)) = _
  simp [Fintype.card_sigma]
omit [Fintype V] in
lemma count_error (M : ℕ) (w : V → ℝ) (hw : ∀ v, 0≤w v) (v : V) :
    0<(count M w v:ℝ)-(M:ℝ)*w v ∧ (count M w v:ℝ)-(M:ℝ)*w v≤1 := by
  have h0 : 0≤(M:ℝ)*w v := mul_nonneg (Nat.cast_nonneg _) (hw v)
  have h1 := Nat.floor_le h0
  have h2 := Nat.lt_floor_add_one ((M:ℝ)*w v)
  simp only [count,Nat.cast_add,Nat.cast_one]
  constructor <;> linarith
lemma n_bounds (M : ℕ) (w : V → ℝ) (hw : ∀ v, 0≤w v) (hws : ∑ v, w v=1) :
    M≤n M w ∧ n M w≤M+Fintype.card V := by
  have hs : (n M w:ℝ)-(M:ℝ)=∑ v, ((count M w v:ℝ)-(M:ℝ)*w v) := by
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,hws,mul_one,n_sum,Nat.cast_sum]
  have h0 : 0≤(n M w:ℝ)-(M:ℝ) := by rw [hs]; exact Finset.sum_nonneg (fun v _ => (count_error M w hw v).1.le)
  have h1 : (n M w:ℝ)-(M:ℝ)≤Fintype.card V := by
    rw [hs]
    calc
      _ ≤ ∑ _v : V, (1:ℝ) := Finset.sum_le_sum (fun v _ => (count_error M w hw v).2)
      _ = _ := by simp
  constructor
  · exact_mod_cast (show (M:ℝ)≤n M w by linarith)
  · exact_mod_cast (show (n M w:ℝ)≤(M:ℝ)+Fintype.card V by linarith)
lemma q_nonneg (M : ℕ) (w : V → ℝ) (v : V) : 0≤q M w v := by unfold q; positivity
lemma q_sum (M : ℕ) (w : V → ℝ) (hn : 0<n M w) : ∑ v, q M w v=1 := by
  simp only [q,← Finset.sum_div,← Nat.cast_sum,← n_sum]
  exact div_self (by exact_mod_cast hn.ne')
lemma q_l1_bound (M : ℕ) (hM : 0<M) (w : V → ℝ) (hw : ∀ v, 0≤w v) (hws : ∑ v, w v=1) :
    (∑ v, |q M w v-w v|)≤2*(Fintype.card V:ℝ)/M := by
  have hb := n_bounds M w hw hws
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hn : (0:ℝ)<n M w := lt_of_lt_of_le hMr (by exact_mod_cast hb.1)
  have hE : (n M w:ℝ)-(M:ℝ)=∑ v, ((count M w v:ℝ)-(M:ℝ)*w v) := by
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,hws,mul_one,n_sum,Nat.cast_sum]
  have hE0 : 0≤(n M w:ℝ)-(M:ℝ) := by
    have hh : (M:ℝ)≤n M w := by exact_mod_cast hb.1
    linarith
  have he (v : V) : |q M w v-w v|≤
      (((count M w v:ℝ)-(M:ℝ)*w v)+((n M w:ℝ)-(M:ℝ))*w v)/(n M w:ℝ) := by
    have heq : q M w v-w v=
        (((count M w v:ℝ)-(M:ℝ)*w v)-((n M w:ℝ)-(M:ℝ))*w v)/(n M w:ℝ) := by
      unfold q; field_simp; ring
    rw [heq,abs_div,abs_of_pos hn]
    apply div_le_div_of_nonneg_right _ hn.le
    exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (count_error M w hw v).1.le,abs_of_nonneg (mul_nonneg hE0 (hw v))])
  calc
    _ ≤ ∑ v, (((count M w v:ℝ)-(M:ℝ)*w v)+((n M w:ℝ)-(M:ℝ))*w v)/(n M w:ℝ) := Finset.sum_le_sum (fun v _ => he v)
    _ = 2*((n M w:ℝ)-(M:ℝ))/(n M w:ℝ) := by
      rw [← Finset.sum_div,Finset.sum_add_distrib,← Finset.mul_sum,hws,mul_one,← hE]; ring
    _ ≤ 2*(Fintype.card V:ℝ)/(n M w:ℝ) := by
      apply div_le_div_of_nonneg_right _ hn.le
      have h : (n M w:ℝ)≤(M:ℝ)+Fintype.card V := by exact_mod_cast hb.2
      linarith
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hMr (by exact_mod_cast hb.1)

lemma product_expectation_bound (p q : V → ℝ) (hp : ∀ v, 0≤p v) (hq : ∀ v, 0≤q v)
    (hps : ∑ v, p v=1) (hqs : ∑ v, q v=1) (g : V → V → ℝ) {D : ℝ}
    (_hD : 0≤D) (hg : ∀ v z, |g v z|≤D) :
    |(∑ v, ∑ z, p v*p z*g v z)-(∑ v, ∑ z, q v*q z*g v z)|≤
      2*D*(∑ v, |p v-q v|) := by
  have he (v z : V) : p v*p z*g v z-q v*q z*g v z=
      (p v-q v)*p z*g v z+q v*(p z-q z)*g v z := by ring
  calc
    _ = |∑ v, ∑ z, ((p v-q v)*p z*g v z+q v*(p z-q z)*g v z)| := by
      simp only [← Finset.sum_sub_distrib,he]
    _ ≤ ∑ v, ∑ z, |(p v-q v)*p z*g v z+q v*(p z-q z)*g v z| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun v _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ v, ∑ z, (|p v-q v| *p z*D+q v*|p z-q z| *D) := by
      apply Finset.sum_le_sum; intro v hv
      apply Finset.sum_le_sum; intro z hz
      calc
        _ ≤ |(p v-q v)*p z*g v z|+|q v*(p z-q z)*g v z| := abs_add_le _ _
        _ ≤ _ := by
          rw [abs_mul,abs_mul,abs_mul,abs_mul,abs_of_nonneg (hp z),abs_of_nonneg (hq v)]
          exact add_le_add (mul_le_mul_of_nonneg_left (hg v z) (mul_nonneg (abs_nonneg _) (hp z)))
            (mul_le_mul_of_nonneg_left (hg v z) (mul_nonneg (hq v) (abs_nonneg _)))
    _ = _ := by
      simp only [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum,hps,hqs,mul_one,one_mul]
      ring
end UniformSparsestCut.Replication

namespace UniformSparsestCut.Replication
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {V : Type u2} [Fintype V]
lemma rep_section (M : ℕ) (w : V → ℝ) (v : V) : rep M w (representative M w v)=v := by
  exact congrArg (fun copy : Copies M w => copy.1)
    ((Fintype.equivFin (Copies M w)).symm_apply_apply ⟨v, ⟨0, count_pos M w v⟩⟩)
lemma sum_rep (M : ℕ) (w : V → ℝ) (g : V → ℝ) :
    (∑ i : Fin (n M w), g (rep M w i))=∑ v, (count M w v:ℝ)*g v := by
  classical
  calc
    _ = ∑ c : Copies M w, g (rep M w ((Fintype.equivFin (Copies M w)) c)) :=
      ((Fintype.equivFin (Copies M w)).sum_comp (fun i => g (rep M w i))).symm
    _ = ∑ c : Copies M w, g c.1 := Finset.sum_congr rfl (fun copy _ =>
      congrArg (fun copy : Copies M w => g copy.1)
        ((Fintype.equivFin (Copies M w)).symm_apply_apply copy))
    _ = _ := by
      change (∑ c : (v : V) × Fin (count M w v), g c.1) = _
      simp [Fintype.sum_sigma]
lemma ordered_sum (M : ℕ) (w : V → ℝ) (hn : 0 < n M w) (g : V → V → ℝ) :
    (∑ i : Fin (n M w), ∑ j, g (rep M w i) (rep M w j))=
      (n M w:ℝ)^2*(∑ v, ∑ z, q M w v*q M w z*g v z) := by
  have hn0 : (n M w:ℝ)≠0 := by exact_mod_cast hn.ne'
  calc
    _ = ∑ i : Fin (n M w), ∑ z, (count M w z:ℝ)*g (rep M w i) z :=
      Finset.sum_congr rfl (fun i _ => sum_rep M w (g (rep M w i)))
    _ = ∑ v, (count M w v:ℝ)*(∑ z, (count M w z:ℝ)*g v z) :=
      sum_rep M w (fun v => ∑ z, (count M w z:ℝ)*g v z)
    _ = _ := by
      simp only [Finset.mul_sum,q]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro z hz
      field_simp

lemma collapse (M : ℕ) (w : V → ℝ) (d : V → V → ℝ) (hself : ∀ v, d v v=0)
    {A : Type u3} [Fintype A] (F : Fin (n M w) → A → ℝ)
    (hF : ∀ i j, (∑ a, |F i a-F j a|)≤d (rep M w i) (rep M w j)) (i : Fin (n M w)) (a : A) :
    F i a=F (representative M w (rep M w i)) a := by
  classical
  have h := hF i (representative M w (rep M w i))
  rw [rep_section,hself] at h
  have hh := (Finset.single_le_sum (fun b _ => abs_nonneg (F i b-F (representative M w (rep M w i)) b)) (Finset.mem_univ a)).trans h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hh)
lemma descend_contraction (M : ℕ) (w : V → ℝ) (d : V → V → ℝ)
    {A : Type u4} [Fintype A] (F : Fin (n M w) → A → ℝ)
    (hF : ∀ i j, (∑ a, |F i a-F j a|)≤d (rep M w i) (rep M w j)) :
    ∀ v z, (∑ a, |F (representative M w v) a-F (representative M w z) a|)≤d v z := by
  intro v z
  simpa only [rep_section] using hF (representative M w v) (representative M w z)
lemma expectation_error (M : ℕ) (hM : 0 < M) (w : V → ℝ) (hw : ∀ v, 0≤w v) (hws : (∑ v,w v)=1)
    (g : V → V → ℝ) {D : ℝ} (hD : 0≤D) (hg : ∀ v z, |g v z|≤D) :
    |(∑ v, ∑ z, q M w v*q M w z*g v z)-(∑ v, ∑ z, w v*w z*g v z)|≤
      4*D*(Fintype.card V:ℝ)/M := by
  have hn : 0 < n M w := hM.trans_le (n_bounds M w hw hws).1
  have h := product_expectation_bound (q M w) w (q_nonneg M w) hw (q_sum M w hn) hws g hD hg
  calc
    _ ≤ 2*D*(∑ v, |q M w v-w v|) := h
    _ ≤ 2*D*(2*(Fintype.card V:ℝ)/M) := mul_le_mul_of_nonneg_left (q_l1_bound M hM w hw hws) (by positivity)
    _ = _ := by ring
end
end UniformSparsestCut.Replication

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.UniformReplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.UniformReplication
open scoped BigOperators RealInnerProductSpace
noncomputable section
lemma negative_pullback {V : Type u1} {H : Type u2} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Z : V → H) (htri : ∀ v w z, ‖Z v-Z z‖^2 ≤ ‖Z v-Z w‖^2+‖Z w-Z z‖^2)
    {n : ℕ} (r : Fin n → V) : NegativeType (fun i j => ‖Z (r i)-Z (r j)‖^2) := by
  classical
  obtain ⟨Y,hY⟩ := TriangleRepair.exists_gram (TriangleRepair.gram_posSemidef (fun i => Z (r i)))
  refine ⟨⟨Y,?_⟩,fun i j k => htri (r i) (r j) (r k)⟩
  intro i j
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, hY, Matrix.of_apply]

variable {V : Type u3} {H : Type u4} [Fintype V] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma estimates (M : ℕ) (hM : 0<M) (w : V → ℝ) (hw : ∀ v, 0≤w v) (hws : (∑ v,w v)=1)
    (Z : V → H) (htri : ∀ v w z, ‖Z v-Z z‖^2 ≤ ‖Z v-Z w‖^2+‖Z w-Z z‖^2)
    {D a b : ℝ} (hD : 0≤D) (hdiam : ∀ v z, ‖Z v-Z z‖^2≤D)
    (havg : a≤∑ v, ∑ z, w v*w z*‖Z v-Z z‖^2)
    (hcon : ∀ (A : Type) [Fintype A] (F : V → A → ℝ),
      (∀ v z, (∑ k, |F v k-F z k|)≤‖Z v-Z z‖^2) →
      (∑ v, ∑ z, w v*w z*(∑ k, |F v k-F z k|))≤b) :
    let n := Replication.n M w
    let d := fun i j : Fin n => ‖Z (Replication.rep M w i)-Z (Replication.rep M w j)‖^2
    let ε := 4*D*(Fintype.card V:ℝ)/M
    NegativeType d ∧ (n:ℝ)^2*(a-ε)≤∑ i, ∑ j,d i j ∧
      ∀ (A : Type) [Fintype A] (F : Fin n → A → ℝ),
        (∀ i j, (∑ k, |F i k-F j k|)≤d i j) →
        (∑ i, ∑ j, ∑ k, |F i k-F j k|)≤(n:ℝ)^2*(b+ε) := by
  dsimp only
  have hn : 0<Replication.n M w := hM.trans_le (Replication.n_bounds M w hw hws).1
  refine ⟨negative_pullback Z htri _,?_,?_⟩
  · rw [Replication.ordered_sum M w hn (fun v z => ‖Z v-Z z‖^2)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have he := Replication.expectation_error M hM w hw hws
      (fun v z => ‖Z v-Z z‖^2) hD (fun v z => by rw [abs_of_nonneg (sq_nonneg _)]; exact hdiam v z)
    linarith [(abs_le.mp he).1]
  · intro A hA F hF
    let G : V → A → ℝ := fun v k => F (Replication.representative M w v) k
    have hG : ∀ v z, (∑ k, |G v k-G z k|)≤‖Z v-Z z‖^2 :=
      Replication.descend_contraction M w _ F hF
    have he : (∑ i, ∑ j, ∑ k, |F i k-F j k|)=
        ∑ i, ∑ j, ∑ k, |G (Replication.rep M w i) k-G (Replication.rep M w j) k| := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      have h1 := Replication.collapse M w (fun v z => ‖Z v-Z z‖^2) (by simp) F hF i k
      have h2 := Replication.collapse M w (fun v z => ‖Z v-Z z‖^2) (by simp) F hF j k
      change |F i k-F j k|=|F (Replication.representative M w (Replication.rep M w i)) k-
        F (Replication.representative M w (Replication.rep M w j)) k|
      rw [h1,h2]
    rw [he,Replication.ordered_sum M w hn (fun v z => ∑ k, |G v k-G z k|)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have herr := Replication.expectation_error M hM w hw hws
      (fun v z => ∑ k, |G v k-G z k|) hD (fun v z => by
        rw [abs_of_nonneg (Finset.sum_nonneg (fun k _ => abs_nonneg _))]
        exact (hG v z).trans (hdiam v z))
    have hbound := hcon A G hG
    linarith [(abs_le.mp herr).2]
end
end UniformSparsestCut.UniformReplication

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.VertexCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceCount
open SourceCharts SourceParameters SourceMetric
open scoped BigOperators
noncomputable section
variable {m : ℕ} (f : PivotFamily.PFamily m) [NeZero m]
lemma integer_bound (hm : 5 ≤ m) (v : V f) (i : Fin (m^6)) : |(v.val.2 i:ℝ)|≤(m:ℝ)^2003 := by
  have hm0 := NeZero.pos m
  have hx : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hx5 : (5:ℝ) ≤ m := by exact_mod_cast hm
  have hx0 : (0:ℝ)< m := by exact_mod_cast hm0
  obtain ⟨θ,hθ,hr,he⟩ := v.property
  have h := RoundedCharts.integerLabel_bound (u f v.val.1) (p_pos hx0 2000)
    (fun i => (u_norm f hm0 v.val.1 i).2) hθ i
  rw [he] at h
  calc
    _ ≤ 4*Real.sqrt m/p m 2000+1 := h
    _ ≤ 4*(m:ℝ)/p m 2000+1 := by
      apply add_le_add_left
      apply div_le_div_of_nonneg_right _ (p_nonneg hx0.le _)
      exact mul_le_mul_of_nonneg_left (sqrt_le hx) (by norm_num)
    _ = 4*(m:ℝ)^2001+1 := by unfold p; field_simp
    _ ≤ 5*(m:ℝ)^2001 := by nlinarith [one_le_pow₀ hx (n:=2001)]
    _ ≤ (m:ℝ)*(m:ℝ)^2001 := mul_le_mul_of_nonneg_right hx5 (by positivity)
    _ = (m:ℝ)^2002 := by ring
    _ ≤ _ := pow_le_pow_right₀ hx (by norm_num)
lemma card_bound (hm : 5 ≤ m) : Fintype.card (V f)≤ m^(4025*m) := by
  have hm0 := NeZero.pos m
  have hx0 : (0:ℝ)< m := by exact_mod_cast hm0
  let B : ℤ := (m:ℤ)^2003
  have hB : ∀ v : V f, ∀ i, v.val.2 i∈Finset.Icc (-B) B := by
    intro v i
    have h := integer_bound f hm v i
    have h' : |v.val.2 i|≤B := by exact_mod_cast h
    simpa only [Finset.mem_Icc,abs_le] using h'
  have h := LabelCount.vertex_count (u f) (p_pos hx0 2000) B hB
  have hI : (Finset.Icc (-B) B).card=2*m^2003+1 := by
    rw [Int.card_Icc]
    dsimp [B]
    have he : (m:ℤ)^2003+1-(-(m:ℤ)^2003)=((2*m^2003+1:ℕ):ℤ) := by push_cast; ring
    rw [he,Int.toNat_natCast]
  rw [hI] at h
  have hm1 : 1 ≤ m := by omega
  have hp : 1≤ m^2003 := one_le_pow₀ hm1
  have hI' : 2*m^2003+1≤ m^2004 := by
    calc
      _ ≤ 3*m^2003 := by omega
      _ ≤ m*m^2003 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have hH : m^6*(2*m^2003+1)+1≤ m^2011 := by
    calc
      _ ≤ m^6*m^2004+1 := Nat.add_le_add_right (Nat.mul_le_mul_left _ hI') _
      _ = m^2010+1 := by ring
      _ ≤ 2*m^2010 := by have hh := one_le_pow₀ hm1 (n:=2010); omega
      _ ≤ m*m^2010 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  calc
    _ ≤ m^3*(m^6*(2*m^2003+1)+1)^(m+1) := h
    _ ≤ m^3*(m^2011)^(m+1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hH _)
    _ = m^(3+2011*(m+1)) := by rw [← pow_mul,← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right hm1 (by omega)
end
end UniformSparsestCut.SourceCount

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.UniformMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceUniform
open scoped BigOperators
open SourceMetric SourceParameters
noncomputable section
lemma size_upper {d v : ℕ} (hd : 3≤d) (hv : v≤d^(4025*d)) :
    d^d+d^2*v+v≤d^(4030*d) := by
  have hd1 : 1≤d := by omega
  have hp : d^d≤d^(4025*d+2) := Nat.pow_le_pow_right hd1 (by omega)
  have hv' : v≤d^(4025*d+2) := hv.trans (Nat.pow_le_pow_right hd1 (by omega))
  have hprod : d^2*v≤d^(4025*d+2) := by
    calc
      _ ≤ d^2*d^(4025*d) := Nat.mul_le_mul_left _ hv
      _ = _ := by rw [←pow_add]; congr 1; omega
  calc
    _ ≤ 3*d^(4025*d+2) := by omega
    _ ≤ d*d^(4025*d+2) := Nat.mul_le_mul_right _ hd
    _ = d^(4025*d+3) := by rw [←pow_succ']
    _ ≤ _ := Nat.pow_le_pow_right hd1 (by omega)

lemma instance_exists_oai {m : ℕ} (f : PivotFamily.PFamily (m+1))
    (hm : 3000 ≤ m+1) (hl : 1≤Real.log (m+1:ℕ)) (hH : SourceContraction.H≤(m+1:ℕ))
    (hD : 4*SourceWeighted.D≤(m+1:ℕ))
    (ha : C₀+1≤KernelApprox.cstar/6*(m+1:ℕ)) :
    ∃ (n : ℕ) (C : Capacity n), (m+1)^(m+1)≤n ∧ n≤(m+1)^(4030*(m+1)) ∧
      2≤n ∧ 1≤OPT C ∧ 0<glValue C ∧
      glValue C≤(SourceContraction.C+1)*SourceContraction.weight (m+1)/
        (KernelApprox.cstar/6*(m+1:ℕ)) := by
  classical
  let d := m+1
  have hd0 : 0<d := Nat.succ_pos m
  have hx0 : (0:ℝ)<d := by exact_mod_cast hd0
  have hd1 : 1≤d := by omega
  have hx : (1:ℝ)≤d := by exact_mod_cast hd1
  obtain ⟨Z,w,hw,hws,htri,hdiam,havg,hcon⟩ := SourceWeighted.weighted_instance f hm hl hH
  let M := d^d+d^2*Fintype.card (V f)
  have hM : 0<M := lt_of_lt_of_le (pow_pos hd0 _) (Nat.le_add_right _ _)
  let n := Replication.n M w
  let δ := fun i j : Fin n => ‖Z (Replication.rep M w i)-Z (Replication.rep M w j)‖^2
  let ε : ℝ := 4*(SourceWeighted.D*d)*(Fintype.card (V f):ℝ)/M
  have hε : ε≤1 := by
    apply (div_le_one (by exact_mod_cast hM)).mpr
    have hM' : (d:ℝ)^2*(Fintype.card (V f):ℝ)≤M := by
      exact_mod_cast (Nat.le_add_left (d^2*Fintype.card (V f)) (d^d))
    calc
      _ = (4*SourceWeighted.D)*(d:ℝ)*(Fintype.card (V f):ℝ) := by ring
      _ ≤ (d:ℝ)*(d:ℝ)*(Fintype.card (V f):ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD hx0.le) (Nat.cast_nonneg _)
      _ = (d:ℝ)^2*(Fintype.card (V f):ℝ) := by ring
      _ ≤ _ := hM'
  have hsize := Replication.n_bounds M w hw hws
  have hlo : d^d≤n := (Nat.le_add_right _ _).trans hsize.1
  have hhi : n≤d^(4030*d) := hsize.2.trans (size_upper (by omega) (SourceCount.card_bound f (by omega)))
  have hn : 2≤n := by
    have hh : d≤d^d := by simpa using (Nat.pow_le_pow_right hd1 hd1 : d^1≤d^d)
    omega
  obtain ⟨hδ,hav,hco⟩ := UniformReplication.estimates M hM w hw hws Z htri
    (mul_nonneg SourceWeighted.D_pos.le hx0.le) hdiam havg hcon
  have ha0 : 0<KernelApprox.cstar/6*(d:ℝ) := mul_pos (div_pos KernelApprox.cstar_pos (by norm_num)) hx0
  have hb0 : 0<(SourceContraction.C+1)*SourceContraction.weight d := by
    have hc := SourceContraction.C_pos
    have hw' := SourceContraction.weight_ge_one hd1 hl
    positivity
  have hlow : KernelApprox.cstar/6*(d:ℝ)≤KernelApprox.cstar/3*(d:ℝ)-C₀*p d 8-ε := by
    have hp : C₀*p d 8≤C₀ := mul_le_of_le_one_right C₀_pos.le (p_one_le hx _)
    linarith only [ha,hp,hε]
  have hupp : SourceContraction.C*SourceContraction.weight d+ε≤
      (SourceContraction.C+1)*SourceContraction.weight d := by
    have hh := SourceContraction.weight_ge_one hd1 hl
    linarith only [hh,hε]
  obtain ⟨C,hopt,hgl,hbound⟩ := cut_cone_duality hn δ hδ ha0 hb0
    ((mul_le_mul_of_nonneg_left hlow (sq_nonneg (n:ℝ))).trans hav)
    (fun A hA F hF => (hco A F hF).trans (mul_le_mul_of_nonneg_left hupp (sq_nonneg (n:ℝ))))
  exact ⟨n,C,hlo,hhi,hn,hopt,hgl,hbound⟩
end
end UniformSparsestCut.SourceUniform

end

end OAI
end

theorem solution : type_of% @OAI.UniformSparsestCut.SourceUniform.instance_exists_oai := @OAI.UniformSparsestCut.SourceUniform.instance_exists_oai
