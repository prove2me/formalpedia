-- Prove2me | solution 1 for OAI.UniformSparsestCut.SourceContraction.integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:48:18.081975+00:00
-- url     : https://prove2.me/submissions/412bf532-bf8a-4b5d-aaaa-27347e6fe275

import Mathlib
import Definitions.Def_OAIQWUS000
import Theorems.Thm_OAI_UniformSparsestCut_CubePoincare_uniform_cube_first_moment

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

end UniformSparsestCut.ChartLinear

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
lemma u_nonparallel (s : Fin (m^3)) (i j : Fin (m^6)) (hij : i≠j) (t : ℝ) :
    u f s i≠t • u f s j := by
  intro h
  apply f.nonparallel s i j hij t
  have hq : (Real.sqrt m)⁻¹≠0 := inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hm)))
  have he := congrArg (fun x : E => Real.sqrt m • x) h
  have hq0 : Real.sqrt (m:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hm))
  have hmul : Real.sqrt (m:ℝ)*(t*(Real.sqrt (m:ℝ))⁻¹)=t := by field_simp
  simpa only [u,smul_smul,mul_inv_cancel₀ hq0,hmul,one_smul] using he
lemma B_norm (s : Fin (m^3)) (x : F) : ‖B f hm s x‖≤‖x‖/Real.sqrt (lower m) :=
  ChartLinear.pseudoInverse_norm _ (lower_pos hm) (energy f hm s) x
end
end UniformSparsestCut.SourceCharts

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
end
end UniformSparsestCut.SourceCharts

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

end UniformSparsestCut.KernelApprox

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
lemma one_step (vp vm : V f) (i : Fin (m^6))
    (hi : vp.val.2 i=vm.val.2 i+1) (hj : ∀ j, j≠i → vp.val.2 j=vm.val.2 j) :
    (∑ j, |RoundedCharts.coordinate (u f) (p m 2000) vp j-
        RoundedCharts.coordinate (u f) (p m 2000) vm j|)=p m 2000 := by
  classical
  rw [Finset.sum_eq_single i]
  · change |p m 2000*(vp.val.2 i:ℝ)-p m 2000*(vm.val.2 i:ℝ)|=_
    rw [hi,Int.cast_add,Int.cast_one]
    have h : p m 2000*((vm.val.2 i:ℝ)+1)-p m 2000*(vm.val.2 i:ℝ)=p m 2000 := by ring
    rw [h,abs_of_pos (p_pos (by exact_mod_cast NeZero.pos m) _)]
  · intro j hmem hji
    change |p m 2000*(vp.val.2 j:ℝ)-p m 2000*(vm.val.2 j:ℝ)|=0
    rw [hj j hji,sub_self,abs_zero]
  · simp
end
end UniformSparsestCut.SourceMetric

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.Mollifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ProductMollifier

lemma rho_nonneg (x : ℝ) : 0 ≤ rho x := bump.nonneg_normed x
lemma rho_integral : ∫ x, rho x = 1 := bump.integral_normed
lemma rho_smooth : ContDiff ℝ (⊤:ℕ∞) rho := bump.contDiff_normed
lemma rho_support {x : ℝ} (hx : rho x ≠ 0) : |x| < 1 := by
  have h : x ∈ Function.support rho := hx
  rw [rho,bump.support_normed_eq] at h
  simpa [bump,Metric.mem_ball,dist_eq_norm] using h
lemma density_nonneg {ell : ℝ} (hell : 0 ≤ ell) (x : ℝ) : 0 ≤ density ell x := by
  exact mul_nonneg (inv_nonneg.mpr hell) (rho_nonneg _)
lemma density_smooth (ell : ℝ) : ContDiff ℝ (⊤:ℕ∞) (density ell) := by
  unfold density
  exact contDiff_const.mul (rho_smooth.comp (contDiff_id.div_const ell))
lemma density_integral {ell : ℝ} (hell : 0 < ell) : ∫ x, density ell x = 1 := by
  unfold density
  rw [integral_const_mul,Measure.integral_comp_div,rho_integral,smul_eq_mul,abs_of_pos hell]
  simp [hell.ne']
lemma density_support {ell x : ℝ} (hell : 0 < ell) (hx : density ell x ≠ 0) : |x| < ell := by
  have hρ : rho (x/ell) ≠ 0 := by intro he; exact hx (by simp [density,he])
  have h := rho_support hρ
  rwa [abs_div,abs_of_pos hell,div_lt_one hell] at h
lemma density_compact {ell : ℝ} (hell : 0 < ell) : HasCompactSupport (density ell) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -ell) (b := ell))
  intro x hx
  by_contra hn
  exact hx (abs_le.mp (density_support hell hn).le)
lemma density_integrable {ell : ℝ} (hell : 0 < ell) : Integrable (density ell) :=
  (density_smooth ell).continuous.integrable_of_hasCompactSupport (density_compact hell)
lemma density_hasDeriv {ell : ℝ} (x : ℝ) : HasDerivAt (density ell)
    (ell⁻¹/ell*deriv rho (x/ell)) x := by
  have hd := ((rho_smooth.differentiable (by simp) (x/ell)).hasDerivAt.comp x
    ((hasDerivAt_id x).div_const ell)).const_mul (ell⁻¹)
  convert hd using 1 <;> try rfl
  ring
lemma density_deriv_integral {ell : ℝ} (hell : 0 < ell) :
    (∫ x, |deriv (density ell) x|) = ell⁻¹*(∫ x, |deriv rho x|) := by
  simp_rw [(density_hasDeriv (ell := ell) _).deriv,abs_mul,abs_of_pos (div_pos (inv_pos.mpr hell) hell)]
  rw [integral_const_mul]
  rw [Measure.integral_comp_div (fun t => |deriv rho t|),smul_eq_mul,abs_of_pos hell]
  field_simp

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
lemma kernel_smooth (φ : ℝ → ℝ) {n : ℕ∞} (hc : ContDiff ℝ n φ) : ContDiff ℝ n (kernel (m := m) φ) := by
  unfold kernel
  apply contDiff_prod
  intro i _
  exact hc.comp (coordinate i).contDiff
lemma kernel_nonneg {φ : ℝ → ℝ} (hn : ∀ t, 0 ≤ φ t) (x : E) : 0 ≤ kernel φ x :=
  Finset.prod_nonneg (fun _i _ => hn _)
lemma kernel_integral (φ : ℝ → ℝ) : (∫ x : E, kernel φ x) = (∫ t, φ t)^m := by
  rw [← (PiLp.volume_preserving_toLp (Fin m)).integral_comp (MeasurableEquiv.measurableEmbedding (MeasurableEquiv.toLp 2 _))]
  simpa only [kernel,Fintype.card_fin] using integral_fintype_prod_volume_eq_pow (ι := Fin m) φ

lemma coordinate_norm_bound {R : ℝ} (hR : 0 ≤ R) (x : E) (hx : ∀ j, |x j| ≤ R) :
    ‖x‖ ≤ R*Real.sqrt m := by
  have hs : ‖x‖^2 ≤ (m:ℝ)*R^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _j : Fin m, R^2 := by
        apply Finset.sum_le_sum; intro j _
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hx j) _
      _ = _ := by simp
  have hroot := Real.sq_sqrt (Nat.cast_nonneg m)
  have hp : 0 ≤ R*Real.sqrt m := mul_nonneg hR (Real.sqrt_nonneg _)
  have he : (R*Real.sqrt m)^2 = (m:ℝ)*R^2 := by rw [mul_pow,hroot]; ring
  nlinarith [norm_nonneg x]

lemma kernel_support_bound {φ : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hφ : ∀ t, φ t ≠ 0 → |t| ≤ R) {x : E} (hx : kernel φ x ≠ 0) : ‖x‖ ≤ R*Real.sqrt m := by
  apply coordinate_norm_bound hR x
  intro j
  apply hφ _
  intro hj
  exact hx (Finset.prod_eq_zero (Finset.mem_univ j) hj)

lemma kernel_compact {φ : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hφ : ∀ t, φ t ≠ 0 → |t| ≤ R) : HasCompactSupport (kernel (m := m) φ) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0:E) (R*Real.sqrt m))
  intro x hx
  by_contra hn
  exact hx (by simpa using kernel_support_bound hR hφ hn)

lemma kernel_hasFDeriv {φ φ' : ℝ → ℝ} (hd : ∀ t, HasDerivAt φ (φ' t) t) (x : E) :
    HasFDerivAt (kernel φ)
      (∑ i, ((∏ j ∈ Finset.univ.erase i, φ (x j))*φ' (x i)) • coordinate i) x := by
  have h (i : Fin m) : HasFDerivAt (fun x : E => φ (x i)) (φ' (x i) • coordinate i) x :=
    (hd (x i)).comp_hasFDerivAt x (coordinate i).hasFDerivAt
  convert! HasFDerivAt.finsetProd (u := Finset.univ) (fun i _ => h i) using 1
  simp only [smul_smul]

lemma kernel_partial {φ φ' : ℝ → ℝ} (hd : ∀ t, HasDerivAt φ (φ' t) t) (x : E) (i : Fin m) :
    fderiv ℝ (kernel φ) x (EuclideanSpace.single i 1) =
      φ' (x i)*(∏ j ∈ Finset.univ.erase i, φ (x j)) := by
  rw [(kernel_hasFDeriv hd x).fderiv]
  simp [coordinate,mul_comm]

lemma kernel_partial_integral {φ φ' : ℝ → ℝ} (hd : ∀ t, HasDerivAt φ (φ' t) t)
    (hn : ∀ t, 0 ≤ φ t) (h1 : ∫ t, φ t = 1) (i : Fin m) :
    (∫ x : E, |fderiv ℝ (kernel φ) x (EuclideanSpace.single i 1)|) = ∫ t, |φ' t| := by
  classical
  simp_rw [kernel_partial hd,abs_mul,abs_of_nonneg (Finset.prod_nonneg (fun j _ => hn _))]
  let f : Fin m → ℝ → ℝ := fun j t => if j=i then |φ' t| else φ t
  have he (x : E) : |φ' (x i)| *(∏ j ∈ Finset.univ.erase i, φ (x j)) = ∏ j, f j (x j) := by
    rw [← Finset.mul_prod_erase (s := Finset.univ) (fun j => f j (x j)) (Finset.mem_univ i)]
    simp only [f,ite_eq_left rfl]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Finset.mem_erase,Finset.mem_univ,and_true] at hj
    simp [hj]
  simp_rw [he]
  rw [← (PiLp.volume_preserving_toLp (Fin m)).integral_comp (MeasurableEquiv.measurableEmbedding (MeasurableEquiv.toLp 2 _))]
  rw [integral_fintype_prod_volume_eq_prod]
  rw [← Finset.mul_prod_erase (s := Finset.univ) (fun j => ∫ t, f j t) (Finset.mem_univ i)]
  simp only [f,ite_eq_left rfl]
  have ho : (∏ j ∈ Finset.univ.erase i, ∫ t, if j=i then |φ' t| else φ t) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    simp only [Finset.mem_erase,Finset.mem_univ,and_true] at hj
    simpa [hj] using h1
  rw [ho,mul_one]

end UniformSparsestCut.ProductMollifier

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

namespace UniformSparsestCut.KernelGeometry
open MeasureTheory Set ProductMollifier
open scoped BigOperators Topology
noncomputable section
variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
lemma smooth (lam : ℝ) : ContDiff ℝ (⊤:ℕ∞) (κ (m := m) lam) :=
  kernel_smooth _ (density_smooth _)
lemma compact {lam : ℝ} (hlam : 0<lam) : HasCompactSupport (κ (m := m) lam) :=
  kernel_compact hlam.le (fun _ hx => (density_support hlam hx).le)
lemma nonneg {lam : ℝ} (hlam : 0≤lam) (z : E) : 0≤κ lam z :=
  kernel_nonneg (density_nonneg hlam) z
lemma integral_one {lam : ℝ} (hlam : 0<lam) : (∫ z : E, κ lam z)=1 := by
  rw [κ,kernel_integral,density_integral hlam,one_pow]
lemma integrable {lam : ℝ} (hlam : 0<lam) : Integrable (κ (m := m) lam) :=
  (smooth lam).continuous.integrable_of_hasCompactSupport (compact hlam)
lemma support_coord {lam : ℝ} (hlam : 0<lam) {z : E} (hz : κ lam z≠0) (j : Fin m) : |z j|<lam := by
  apply density_support hlam
  intro hj
  exact hz (Finset.prod_eq_zero (Finset.mem_univ j) hj)
lemma tsupport_coord {lam : ℝ} (hlam : 0<lam) {z : E} (hz : z∈tsupport (κ lam)) (j : Fin m) : |z j|≤lam := by
  have hc : IsClosed {w : E | |w j|≤lam} := isClosed_le (by fun_prop) continuous_const
  exact (closure_minimal (fun _ h => (support_coord hlam h j).le) hc) hz
lemma shifted_mem {lam : ℝ} (hlam : 0<lam) (hlam1 : lam<1) (x : E) (hx : ∀ j, |x j|≤1)
    {z : E} (hz : z∈tsupport (κ lam)) : ∀ j, |(x-z) j|<2 := by
  intro j
  have h := tsupport_coord hlam hz j
  change |x j-z j|<2
  exact (abs_sub (x j) (z j)).trans_lt (by linarith [hx j])
lemma derivative_shifted_mem {lam : ℝ} (hlam : 0<lam) (hlam1 : lam<1) (x : E) (hx : ∀ j, |x j|≤1)
    {z h : E} (hz : fderiv ℝ (κ lam) z h≠0) : ∀ j, |(x-z) j|<2 := by
  apply shifted_mem hlam hlam1 x hx
  apply support_fderiv_subset ℝ
  intro he
  exact hz (by rw [he]; rfl)
lemma norm_bound {lam : ℝ} (hlam : 0<lam) {z : E} (hz : κ lam z≠0) : ‖z‖≤lam*Real.sqrt m :=
  coordinate_norm_bound hlam.le z (fun j => (support_coord hlam hz j).le)
lemma partial_integrable {lam : ℝ} (hlam : 0<lam) (j : Fin m) :
    Integrable (fun z : E => |fderiv ℝ (κ lam) z (EuclideanSpace.single j 1)|) := by
  have hc := (smooth (m := m) lam).continuous_fderiv (by simp)
  exact ((hc.clm_apply continuous_const).integrable_of_hasCompactSupport
    ((compact (m := m) hlam).fderiv_apply ℝ (EuclideanSpace.single j 1))).abs
lemma partial_integral {lam : ℝ} (hlam : 0<lam) (j : Fin m) :
    (∫ z : E, |fderiv ℝ (κ lam) z (EuclideanSpace.single j 1)|)=L lam := by
  change (∫ z : E, |fderiv ℝ (kernel (density lam)) z (EuclideanSpace.single j 1)|)=_
  rw [kernel_partial_integral (fun t => ((density_smooth lam).differentiable (by simp) t).hasDerivAt)
    (density_nonneg hlam.le) (density_integral hlam),density_deriv_integral hlam]
  rfl
end
end UniformSparsestCut.KernelGeometry

namespace UniformSparsestCut.SourceContraction
open scoped BigOperators RealInnerProductSpace
open SourceParameters SourceCharts SourceMetric
open MeasureTheory
noncomputable section
lemma H_nonneg : 0≤H := integral_nonneg (fun _ => abs_nonneg _)
lemma weight_ge_one {m : ℕ} (hm : 1 ≤ m) (hl : 1≤Real.log m) : 1≤weight m := by
  have hq : 1≤Real.sqrt m := Real.one_le_sqrt.mpr (by exact_mod_cast hm)
  have hll : 1≤(Real.log m)^2 := one_le_pow₀ hl
  have hs : 1≤Real.sqrt (Real.log m) := Real.one_le_sqrt.mpr hl
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hq hll) hs
lemma scale_L {m : ℕ} (_hm : 0 < m) : KernelGeometry.L (p m 2)=(m:ℝ)^2*H := by
  simp [KernelGeometry.L,p,H]
lemma small {m : ℕ} (f : PivotFamily.PFamily m) (hm : 1 ≤ m) (hH : H ≤ m)
    (s : Fin (m^3)) (i : Fin (m^6)) (j : Fin m) :
    p m 2000/|u f s i j| *KernelGeometry.L (p m 2)≤1 := by
  have hm0 : 0 < m := by omega
  have hx0 : (0:ℝ)< m := by exact_mod_cast hm0
  have hx : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hq := u_pivot f hm0 s i j
  have ha : 0 < |u f s i j| := lt_trans (by positivity) hq
  have hp : p m 31≤|u f s i j| := by
    apply le_trans _ hq.le
    apply one_div_le_one_div_of_le (by positivity)
    calc
      (m:ℝ)^30*Real.sqrt m≤(m:ℝ)^30*m := mul_le_mul_of_nonneg_left (sqrt_le hx) (by positivity)
      _ = (m:ℝ)^31 := by ring
  have hb : p m 2000*KernelGeometry.L (p m 2)≤|u f s i j| := by
    rw [scale_L hm0]
    calc
      _ ≤ p m 2000*((m:ℝ)^2*m) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hH (by positivity)) (p_nonneg hx0.le _)
      _ = p m 1997 := by unfold p; field_simp
      _ ≤ p m 31 := p_le hx (by norm_num)
      _ ≤ _ := hp
  rw [div_mul_eq_mul_div,div_le_one ha]
  exact hb
lemma contraction_numeric {m : ℕ} (hm : 1 ≤ m) (hl : 1≤Real.log m) :
    2*(KernelApprox.cstar*Real.sqrt m*(p m 2*Real.sqrt m)+C₀*p m 8)+
      Real.pi*((11*Real.sqrt (Real.log m)/Real.sqrt m)*
        (((m^6:ℕ):ℝ)*(2*(50000000*p m 2000*p m 5*(Real.log m)^2)/p m 2000))+
        (m:ℝ)*(C₀*p m 8)*KernelGeometry.L (p m 2))≤C*weight m := by
  have hx : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hx0 : (0:ℝ)< m := by linarith
  have hm0 : 0 < m := by omega
  have hq0 := ne_of_gt (Real.sqrt_pos.mpr hx0)
  have hq2 := Real.sq_sqrt hx0.le
  have hR := C₀_pos.le
  have hcs := KernelApprox.cstar_pos.le
  have hH := H_nonneg
  have hw := weight_ge_one hm hl
  have he : (11*Real.sqrt (Real.log m)/Real.sqrt m)*
      (((m^6:ℕ):ℝ)*(2*(50000000*p m 2000*p m 5*(Real.log m)^2)/p m 2000))=
      1100000000*weight m := by
    have hdiv : (m:ℝ)/Real.sqrt m=Real.sqrt m := (div_eq_iff hq0).mpr (by nlinarith)
    calc
      _ = 1100000000*((m:ℝ)/Real.sqrt m)*(Real.log m)^2*Real.sqrt (Real.log m) := by
        unfold p; push_cast; field_simp ; ring
      _ = _ := by rw [hdiv]; unfold weight; ring
  have hG : KernelApprox.cstar*Real.sqrt m*(p m 2*Real.sqrt m)≤KernelApprox.cstar := by
    have he : Real.sqrt m*(p m 2*Real.sqrt m)=p m 1 := by
      calc
        _ = (Real.sqrt m)^2*p m 2 := by ring
        _ = (m:ℝ)*p m 2 := by rw [Real.sq_sqrt hx0.le]
        _ = p m 1 := p_succ hx0.ne' 1
    calc
      _ = KernelApprox.cstar*(Real.sqrt m*(p m 2*Real.sqrt m)) := by ring
      _ = KernelApprox.cstar*p m 1 := by rw [he]
      _ ≤ _ := mul_le_of_le_one_right hcs (p_one_le hx _)
  have heR : (m:ℝ)*(C₀*p m 8)*KernelGeometry.L (p m 2)=C₀*H*p m 5 := by
    rw [scale_L hm0]; unfold p; field_simp
  rw [he,heR]
  have h1 := mul_le_of_le_one_right hR (p_one_le hx 8)
  have h2 := mul_le_of_le_one_right (mul_nonneg hR hH) (p_one_le hx 5)
  have h3 := mul_le_mul_of_nonneg_left hw (mul_nonneg hR hH)
  have h4 := mul_le_mul_of_nonneg_left hw (by positivity : 0≤2*(KernelApprox.cstar+C₀))
  calc
    _ ≤ 2*(KernelApprox.cstar+C₀)+Real.pi*(1100000000*weight m+C₀*H) := add_le_add (mul_le_mul_of_nonneg_left (add_le_add hG h1) (by norm_num))
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl h2) Real.pi_pos.le)
    _ ≤ 2*(KernelApprox.cstar+C₀)*weight m+
        Real.pi*(1100000000*weight m+C₀*H*weight m) := add_le_add (by simpa using h4)
          (mul_le_mul_of_nonneg_left (add_le_add le_rfl (by simpa using h3)) Real.pi_pos.le)
    _ ≤ _ := by unfold C; nlinarith
end
end UniformSparsestCut.SourceContraction

namespace UniformSparsestCut.SourceCharts
open scoped BigOperators RealInnerProductSpace
open Set
noncomputable section
variable {m : ℕ} (f : PivotFamily.PFamily m) (hm : 0 < m)
local notation "E" => EuclideanSpace ℝ (Fin m)
include hm
lemma good_dual (D : StrongDual ℝ E) :
    ∃ good : Finset (Fin (m^3)), ((m^3:ℕ):ℝ)/2≤good.card ∧
      ∀ s∈good, ∀ i, |D (u f s i)|≤(11*Real.sqrt (Real.log m)/Real.sqrt m)*‖D‖ := by
  classical
  by_cases hz : D=0
  · refine ⟨Finset.univ,?_,?_⟩
    · simp only [Finset.card_univ,Fintype.card_fin]; linarith [show (0:ℝ)≤((m^3:ℕ):ℝ) by positivity]
    · intro s hs i; simp [hz]
  let w : E := (InnerProductSpace.toDual ℝ E).symm D
  have hwn : ‖w‖=‖D‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map D
  have hw0 : 0<‖w‖ := by rw [hwn]; exact norm_pos_iff.mpr hz
  let v : E := ‖w‖⁻¹ • w
  have hv : ‖v‖=1 := by simp [v,norm_smul,hw0.ne']
  have hw : w=‖w‖ • v := by simp [v,smul_smul,hw0.ne']
  let Q := 11*Real.sqrt (Real.log m)
  let good : Finset (Fin (m^3)) := Finset.univ.filter (fun s => f.g s∉Directions.projectionBad Q v)
  have hb := f.good v hv
  have hcard : Directions.badCount (Directions.projectionBad Q v) f.g+good.card=m^3 := by
    simpa only [Directions.badCount,good,Finset.card_univ,Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (m^3)))) (fun s => f.g s∈Directions.projectionBad Q v))
  refine ⟨good,?_,?_⟩
  · have hc : ((Directions.badCount (Directions.projectionBad Q v) f.g):ℝ)+(good.card:ℝ)=((m^3:ℕ):ℝ) := by exact_mod_cast hcard
    change ((Directions.badCount (Directions.projectionBad Q v) f.g):ℝ)≤((m^3:ℕ):ℝ)/2 at hb
    linarith
  · intro s hs i
    have hp : |inner ℝ v (f.g s i)|≤Q := by
      by_contra h
      exact (Finset.mem_filter.mp hs).2 ⟨i,lt_of_not_ge h⟩
    have hq : 0<Real.sqrt (m:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hm)
    have he : |D (u f s i)|=‖w‖*(Real.sqrt m)⁻¹*|inner ℝ v (f.g s i)| := by
      rw [← InnerProductSpace.toDual_symm_apply]
      change |inner ℝ w ((Real.sqrt m)⁻¹ • f.g s i)|=_
      conv_lhs => rw [hw]
      rw [real_inner_smul_left,real_inner_smul_right,abs_mul,abs_mul,
        abs_of_nonneg (norm_nonneg _),abs_of_pos (inv_pos.mpr hq)]
      ring
    rw [he]
    calc
      _ ≤ ‖w‖*(Real.sqrt m)⁻¹*Q := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by rw [hwn]; unfold Q; ring
end
end UniformSparsestCut.SourceCharts

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.InterfaceStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.InterfaceStep
variable {ι : Type u1} {V : Type u2} [DecidableEq ι] [AddCommGroup V]

lemma telescoping_events (s : Finset ι) (t : ι → ℝ) (ht : Set.InjOn t s)
    (F : Finset ι → V) :
    (∑ i ∈ s, (F (s.filter (fun j => t j ≤ t i))-F (s.filter (fun j => t j < t i)))) =
      F s-F ∅ := by
  revert ht
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    intro ht
    by_cases hs : s.Nonempty
    · obtain ⟨a,ha,hmax⟩ := s.exists_max_image t hs
      let r := s.erase a
      have hr : r ⊂ s := Finset.erase_ssubset ha
      have htr : Set.InjOn t (↑r : Set ι) := ht.mono (by intro i hi; exact Finset.mem_of_mem_erase hi)
      have hind := ih r hr htr
      have hle : s.filter (fun j => t j ≤ t a) = s := by
        apply Finset.filter_eq_self.mpr; intro j hj; exact hmax j hj
      have hlt : s.filter (fun j => t j < t a) = r := by
        ext j
        simp only [Finset.mem_filter, r, Finset.mem_erase]
        constructor
        · rintro ⟨hj,h⟩; exact ⟨fun he => by simp [he] at h,hj⟩
        · rintro ⟨hne,hj⟩
          exact ⟨hj,lt_of_le_of_ne (hmax j hj) (fun he => hne (ht hj ha he))⟩
      have hfilters (i : ι) (hi : i ∈ r) :
          s.filter (fun j => t j ≤ t i) = r.filter (fun j => t j ≤ t i) ∧
          s.filter (fun j => t j < t i) = r.filter (fun j => t j < t i) := by
        have hia : t i < t a := (Finset.mem_filter.mp (show i ∈ s.filter (fun j => t j < t a) by rw [hlt]; exact hi)).2
        constructor <;> (ext j; simp only [Finset.mem_filter, r, Finset.mem_erase]; constructor)
        · rintro ⟨hj,hji⟩
          exact ⟨⟨fun he => by subst j; linarith,hj⟩,hji⟩
        · rintro ⟨⟨_,hj⟩,hji⟩; exact ⟨hj,hji⟩
        · rintro ⟨hj,hji⟩
          exact ⟨⟨fun he => by subst j; linarith,hj⟩,hji⟩
        · rintro ⟨⟨_,hj⟩,hji⟩; exact ⟨hj,hji⟩
      rw [← Finset.sum_erase_add _ _ ha, hle,hlt]
      change (∑ i ∈ r, _) + (F s-F r) = _
      have he : (∑ i ∈ r, (F (s.filter (fun j => t j ≤ t i))-F (s.filter (fun j => t j < t i)))) =
          ∑ i ∈ r, (F (r.filter (fun j => t j ≤ t i))-F (r.filter (fun j => t j < t i))) := by
        apply Finset.sum_congr rfl; intro i hi; rw [(hfilters i hi).1,(hfilters i hi).2]
      rw [he,hind]
      abel
    · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

lemma threshold_decomposition (s : Finset ι) (t : ι → ℝ) (ht : Set.InjOn t s)
    (F : Finset ι → V) (x : ℝ) :
    F (s.filter (fun i => t i < x)) = F ∅+
      ∑ i ∈ s, if t i < x then
        F (s.filter (fun j => t j ≤ t i))-F (s.filter (fun j => t j < t i)) else 0 := by
  let r := s.filter (fun i => t i < x)
  have htr : Set.InjOn t (↑r : Set ι) := ht.mono (by intro i hi; exact (Finset.mem_filter.mp hi).1)
  have h := telescoping_events r t htr F
  have hfilters (i : ι) (hi : i ∈ r) :
      r.filter (fun j => t j ≤ t i) = s.filter (fun j => t j ≤ t i) ∧
      r.filter (fun j => t j < t i) = s.filter (fun j => t j < t i) := by
    have hix : t i < x := (Finset.mem_filter.mp hi).2
    constructor <;> (ext j; simp only [r,Finset.mem_filter]; constructor)
    · rintro ⟨⟨hj,_⟩,hji⟩; exact ⟨hj,hji⟩
    · rintro ⟨hj,hji⟩; exact ⟨⟨hj,lt_of_le_of_lt hji hix⟩,hji⟩
    · rintro ⟨⟨hj,_⟩,hji⟩; exact ⟨hj,hji⟩
    · rintro ⟨hj,hji⟩; exact ⟨⟨hj,hji.trans hix⟩,hji⟩
  have he : (∑ i ∈ r, (F (r.filter (fun j => t j ≤ t i))-F (r.filter (fun j => t j < t i)))) =
      ∑ i ∈ r, (F (s.filter (fun j => t j ≤ t i))-F (s.filter (fun j => t j < t i))) := by
    apply Finset.sum_congr rfl; intro i hi; rw [(hfilters i hi).1,(hfilters i hi).2]
  rw [he] at h
  rw [← Finset.sum_filter]
  change F r = F ∅+_
  rw [h]
  abel

section MovingEvents
variable {X : Type u4} [MeasurableSpace X]

lemma measurable_filter_apply (s : Finset ι) (P : ι → X → Prop)
    [∀ i, DecidablePred (P i)] (hP : ∀ i, MeasurableSet {x | P i x})
    (F : Finset ι → ℝ) : Measurable (fun x => F (s.filter (fun i => P i x))) := by
  classical
  induction s using Finset.induction_on generalizing F with
  | empty => simp
  | @insert i s hi ih =>
    have h₁ := ih (fun a => F (insert i a))
    have h₂ := ih F
    have h : Measurable (fun x => if P i x then F (insert i (s.filter (fun j => P j x))) else F (s.filter (fun j => P j x))) := Measurable.ite (hP i) h₁ h₂
    convert h using 1
    funext x
    by_cases hx : P i x <;> simp [Finset.filter_insert, hx]

end MovingEvents

section ContinuousEvents
variable [Fintype ι] {X : Type u5} [TopologicalSpace X] [FirstCountableTopology X]

omit [Fintype ι] in
lemma threshold_integral (s : Finset ι) (t : ι → ℝ) (ht : Set.InjOn t s)
    (F : Finset ι → ℝ) {φ : ℝ → ℝ} (hφ : Integrable φ) :
    (∫ x, φ x * F (s.filter (fun i => t i < x))) =
      (∫ x, φ x)*F ∅ + ∑ i ∈ s, (∫ x in Ioi (t i), φ x) *
        (F (s.filter (fun j => t j ≤ t i))-F (s.filter (fun j => t j < t i))) := by
  let Δ := fun i => F (s.filter (fun j => t j ≤ t i))-F (s.filter (fun j => t j < t i))
  have hi (i : ι) : Integrable (fun x => φ x * (if t i < x then Δ i else 0)) := by
    have he : (fun x => φ x * (if t i < x then Δ i else 0)) =
        (Ioi (t i)).indicator (fun x => φ x * Δ i) := by
      funext x; by_cases hx : t i < x <;> simp [hx]
    rw [he]
    exact (hφ.mul_const _).indicator measurableSet_Ioi
  have he (x : ℝ) : φ x * F (s.filter (fun i => t i < x)) =
      φ x * F ∅ + ∑ i ∈ s, φ x * (if t i < x then Δ i else 0) := by
    rw [threshold_decomposition s t ht F x, mul_add, Finset.mul_sum]
  simp_rw [he]
  rw [integral_add (hφ.mul_const _) (integrable_finsetSum _ (fun i _ => hi i)),
    integral_mul_const, integral_finsetSum _ (fun i _ => hi i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi'
  have he : (fun x => φ x * (if t i < x then Δ i else 0)) =
      (Ioi (t i)).indicator (fun x => φ x * Δ i) := by
    funext x; by_cases hx : t i < x <;> simp [hx]
  rw [he, integral_indicator measurableSet_Ioi, integral_mul_const]

lemma tail_integral_hasDerivAt {φ : ℝ → ℝ} (hφ : Integrable φ) (hc : Continuous φ) (x : ℝ) :
    HasDerivAt (fun t => ∫ z in Ioi t, φ z) (-φ x) x := by
  have he (t : ℝ) : (∫ z in Ioi t, φ z) = (∫ z in Ioi (0:ℝ), φ z)-(∫ z in (0:ℝ)..t, φ z) := by
    rw [← intervalIntegral.integral_Ioi_sub_Ioi' hφ.integrableOn hφ.integrableOn]
    ring
  rw [show (fun t => ∫ z in Ioi t, φ z) = (fun t => (∫ z in Ioi (0:ℝ), φ z)-(∫ z in (0:ℝ)..t, φ z)) from funext he]
  exact (intervalIntegral.integral_hasDerivAt_right (hφ.intervalIntegrable) hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_sub _
end ContinuousEvents

section Slope
variable [Fintype ι]

omit [Fintype ι] in
lemma eventually_order_eq {X : Type u6} [TopologicalSpace X] (s : Finset ι) (t : ι → X → ℝ) {y : X}
    (ht : ∀ i ∈ s, ContinuousAt (t i) y) (hi : Set.InjOn (fun i => t i y) s) :
    ∀ᶠ z in 𝓝 y, Set.InjOn (fun i => t i z) s ∧
      ∀ i ∈ s, s.filter (fun j => t j z ≤ t i z) = s.filter (fun j => t j y ≤ t i y) ∧
        s.filter (fun j => t j z < t i z) = s.filter (fun j => t j y < t i y) := by
  have hp (i : ι) (his : i ∈ s) (j : ι) (hjs : j ∈ s) :
      ∀ᶠ z in 𝓝 y, (t i z < t j z ↔ t i y < t j y) := by
    by_cases hij : i = j
    · subst j; simp
    have hne : t i y ≠ t j y := fun he => hij (hi his hjs he)
    rcases hne.lt_or_gt with h | h
    · filter_upwards [(ht i his).eventually_lt (ht j hjs) h] with z hz
      exact iff_of_true hz h
    · filter_upwards [(ht j hjs).eventually_lt (ht i his) h] with z hz
      exact iff_of_false (not_lt.mpr hz.le) (not_lt.mpr h.le)
  have hall : ∀ᶠ z in 𝓝 y, ∀ i ∈ s, ∀ j ∈ s, (t i z < t j z ↔ t i y < t j y) :=
    s.eventually_all.mpr (fun i his => s.eventually_all.mpr (fun j hjs => hp i his j hjs))
  filter_upwards [hall] with z hz
  refine ⟨?_,?_⟩
  · intro i his j hjs he
    change t i z=t j z at he
    apply hi his hjs
    apply le_antisymm
    · apply not_lt.mp
      intro h
      have := (hz j hjs i his).mpr h
      rw [he] at this
      exact (lt_irrefl _ this)
    · apply not_lt.mp
      intro h
      have := (hz i his j hjs).mpr h
      rw [he] at this
      exact (lt_irrefl _ this)
  · intro i his
    constructor <;> ext j <;> simp only [Finset.mem_filter]
    · apply and_congr_right
      intro hjs
      simp only [← not_lt, hz i his j hjs]
    · exact and_congr_right (fun hjs => hz j hjs i his)

end Slope

section Lipschitz
variable [Fintype ι]

lemma threshold_integrable (s : Finset ι) (t : ι → ℝ) (F : Finset ι → ℝ)
    {φ : ℝ → ℝ} (hφ : Integrable φ) :
    Integrable (fun x => φ x * F (s.filter (fun i => t i < x))) := by
  classical
  let M := ∑ a : Finset ι, |F a|
  apply hφ.mul_bdd (measurable_filter_apply s (fun i x => t i < x)
      (fun _ => measurableSet_Ioi) F).aestronglyMeasurable
  apply ae_of_all
  intro x
  exact Finset.single_le_sum (f := fun a : Finset ι => |F a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)

lemma threshold_pointwise_bound (s : Finset ι) (t u : ι → ℝ) (F : Finset ι → ℝ)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ a, |F a| ≤ M) (x : ℝ) :
    |F (s.filter (fun i => t i < x))-F (s.filter (fun i => u i < x))| ≤
      2*M*∑ i ∈ s, (uIoc (t i) (u i)).indicator (fun _ => (1:ℝ)) x := by
  classical
  have hn (i : ι) : 0 ≤ (uIoc (t i) (u i)).indicator (fun _ => (1:ℝ)) x := by
    by_cases hx : x ∈ uIoc (t i) (u i) <;> simp [hx]
  by_cases he : ∀ i ∈ s, t i < x ↔ u i < x
  · have he' : s.filter (fun i => t i < x) = s.filter (fun i => u i < x) := by
      ext i; simp only [Finset.mem_filter]; exact and_congr_right (he i)
    rw [he',sub_self,abs_zero]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => hn i))
  · simp only [not_forall] at he
    obtain ⟨i,his,hi⟩ := he
    have hx : x ∈ uIoc (t i) (u i) := by
      change min (t i) (u i) < x ∧ x ≤ max (t i) (u i)
      rcases lt_or_ge (t i) x with ht | ht <;> rcases lt_or_ge (u i) x with hu | hu
      · exact False.elim (hi (iff_of_true ht hu))
      · exact ⟨(min_le_left _ _).trans_lt ht,hu.trans (le_max_right _ _)⟩
      · exact ⟨(min_le_right _ _).trans_lt hu,ht.trans (le_max_left _ _)⟩
      · exact False.elim (hi (iff_of_false (not_lt.mpr ht) (not_lt.mpr hu)))
    have hs : 1 ≤ ∑ i ∈ s, (uIoc (t i) (u i)).indicator (fun _ => (1:ℝ)) x := by
      have hh := Finset.single_le_sum (fun j _ => hn j) his
      simpa [hx] using hh
    calc
      _ ≤ |F (s.filter (fun i => t i < x))|+|F (s.filter (fun i => u i < x))| := abs_sub _ _
      _ ≤ 2*M := by linarith [hM (s.filter (fun i => t i < x)),hM (s.filter (fun i => u i < x))]
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hs

lemma threshold_integral_diff_bound (s : Finset ι) (t u : ι → ℝ) (F : Finset ι → ℝ)
    {φ : ℝ → ℝ} (hφ : Integrable φ) {M C : ℝ} (hM0 : 0 ≤ M) (hC : 0 ≤ C)
    (hM : ∀ a, |F a| ≤ M) (hφC : ∀ x, |φ x| ≤ C) :
    |(∫ x, φ x * F (s.filter (fun i => t i < x)))-
      (∫ x, φ x * F (s.filter (fun i => u i < x)))| ≤
      2*M*C*∑ i ∈ s, |u i-t i| := by
  classical
  let I := fun i x => (uIoc (t i) (u i)).indicator (fun _ => (1:ℝ)) x
  have hi (i : ι) : Integrable (I i) := by
    exact (integrable_indicator_iff measurableSet_uIoc).mpr (integrableOn_const (μ := volume) (s := uIoc (t i) (u i)) (C := (1:ℝ)) (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top))
  have hiS : Integrable (fun x => 2*M*C*∑ i ∈ s, I i x) :=
    (integrable_finsetSum s (fun i _ => hi i)).const_mul _
  have hbound (x : ℝ) : ‖φ x*(F (s.filter (fun i => t i < x))-F (s.filter (fun i => u i < x)))‖ ≤
      2*M*C*∑ i ∈ s, I i x := by
    rw [Real.norm_eq_abs,abs_mul]
    have hp := mul_le_mul (hφC x) (threshold_pointwise_bound s t u F hM0 hM x) (abs_nonneg _) hC
    dsimp [I]
    convert hp using 1 <;> first | rfl | ring1
  rw [← integral_sub (threshold_integrable s t F hφ) (threshold_integrable s u F hφ)]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∫ x, 2*M*C*∑ i ∈ s, I i x := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le hiS (ae_of_all _ hbound)
    _ = 2*M*C*∑ i ∈ s, |u i-t i| := by
      rw [integral_const_mul,integral_finsetSum s (fun i _ => hi i)]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      dsimp [I]
      change (∫ x, (uIoc (t i) (u i)).indicator (1 : ℝ → ℝ) x) = _
      rw [integral_indicator_one measurableSet_uIoc,measureReal_def,Real.volume_uIoc,ENNReal.toReal_ofReal (abs_nonneg _)]

end Lipschitz

section FDeriv
variable [Fintype ι]
variable {X : Type u7} [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [Fintype ι] in
lemma moving_threshold_integral_hasFDerivAt (s : Finset ι) (t : ι → X → ℝ)
    (F : Finset ι → ℝ) {y : X} (t' : ι → X →L[ℝ] ℝ)
    (ht : ∀ i ∈ s, HasFDerivAt (t i) (t' i) y) (hi : Set.InjOn (fun i => t i y) s)
    {φ : ℝ → ℝ} (hφ : Integrable φ) (hc : Continuous φ) :
    HasFDerivAt (fun z => ∫ x, φ x * F (s.filter (fun i => t i z < x)))
      (∑ i ∈ s, (-(φ (t i y) *
        (F (s.filter (fun j => t j y ≤ t i y))-F (s.filter (fun j => t j y < t i y))))) • t' i) y := by
  let Δ := fun i => F (s.filter (fun j => t j y ≤ t i y))-F (s.filter (fun j => t j y < t i y))
  have he : (fun z => ∫ x, φ x * F (s.filter (fun i => t i z < x))) =ᶠ[𝓝 y]
      (fun z => (∫ x, φ x)*F ∅ + ∑ i ∈ s, (∫ x in Ioi (t i z), φ x)*Δ i) := by
    filter_upwards [eventually_order_eq s t (fun i his => (ht i his).continuousAt) hi] with z hz
    rw [threshold_integral s (fun i => t i z) hz.1 F hφ]
    congr 1
    apply Finset.sum_congr rfl
    intro i his
    rw [(hz.2 i his).1,(hz.2 i his).2]
  have hd (i : ι) (his : i ∈ s) : HasFDerivAt (fun z => (∫ x in Ioi (t i z), φ x)*Δ i)
      (-(φ (t i y)*Δ i) • t' i) y := by
    convert ((tail_integral_hasDerivAt hφ hc (t i y)).comp_hasFDerivAt y (ht i his)).mul_const (Δ i) using 1 <;> try rfl
    simp only [smul_smul]
    congr 1; ring
  have hs := (HasFDerivAt.sum (fun i his => hd i his)).const_add ((∫ x, φ x)*F ∅)
  simp only [Finset.sum_apply] at hs
  exact hs.congr_of_eventuallyEq he

lemma affine_threshold_lipschitz (s : Finset ι) (L : ι → X →L[ℝ] ℝ) (b : ι → ℝ)
    (F : Finset ι → ℝ) {φ : ℝ → ℝ} (hφ : Integrable φ)
    {M C : ℝ} (hM0 : 0 ≤ M) (hC : 0 ≤ C) (hM : ∀ a, |F a| ≤ M) (hφC : ∀ x, |φ x| ≤ C) :
    LipschitzWith (Real.nnabs (2*M*C*∑ i ∈ s, ‖L i‖))
      (fun y => ∫ x, φ x * F (s.filter (fun i => L i y+b i < x))) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  simp only [dist_eq_norm]
  have hb := threshold_integral_diff_bound s (fun i => L i y+b i) (fun i => L i z+b i) F hφ hM0 hC hM hφC
  simp only [Real.norm_eq_abs] at ⊢
  refine hb.trans ?_
  have hs : (∑ i ∈ s, |L i z+b i-(L i y+b i)|) ≤ (∑ i ∈ s, ‖L i‖)*‖y-z‖ := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have ht := (L i).le_opNorm (z-y)
    simpa only [map_sub, Real.norm_eq_abs, add_sub_add_right_eq_sub, norm_sub_rev z y] using ht
  exact mul_le_mul_of_nonneg_left hs (by positivity) |>.trans_eq (by simp only [Real.coe_nnabs, abs_of_nonneg (show 0 ≤ 2*M*C*∑ i ∈ s, ‖L i‖ by positivity)]; ring)

end FDeriv

end UniformSparsestCut.InterfaceStep

namespace UniformSparsestCut.InterfaceStep
open MeasureTheory Set
open scoped BigOperators Topology
variable {ι : Type u8} {X : Type u9} {Z : Type u10} [DecidableEq ι] [Fintype ι]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace Z]

lemma averaged_threshold_derivative (s : Finset ι) (L : ι → X →L[ℝ] ℝ)
    (b : ι → Z → ℝ) (hb : ∀ i, Measurable (b i)) (F : Finset ι → ℝ)
    {φ : ℝ → ℝ} (hφ : Integrable φ) (hc : Continuous φ)
    {M C : ℝ} (hM0 : 0 ≤ M) (hC : 0 ≤ C) (hM : ∀ a, |F a| ≤ M) (hφC : ∀ x, |φ x| ≤ C)
    (μ : Measure Z) [IsFiniteMeasure μ] (y : X)
    (hi : ∀ᵐ z ∂μ, Set.InjOn (fun i => L i y+b i z) s) :
    HasFDerivAt (fun y => ∫ z, (∫ x, φ x * F (s.filter (fun i => L i y+b i z < x))) ∂μ)
      (∑ i ∈ s, (∫ z, -(φ (L i y+b i z) *
        (F (s.filter (fun j => L j y+b j z ≤ L i y+b i z))-
          F (s.filter (fun j => L j y+b j z < L i y+b i z)))) ∂μ) • L i) y := by
  let H : X → Z → ℝ := fun y z => ∫ x, φ x * F (s.filter (fun i => L i y+b i z < x))
  let c : ι → Z → ℝ := fun i z => -(φ (L i y+b i z) *
    (F (s.filter (fun j => L j y+b j z ≤ L i y+b i z))-
      F (s.filter (fun j => L j y+b j z < L i y+b i z))))
  have hmH (y : X) : StronglyMeasurable (H y) := by
    apply StronglyMeasurable.integral_prod_right
    apply Measurable.stronglyMeasurable
    exact (hc.measurable.comp measurable_snd).mul (measurable_filter_apply s
      (fun i (p : Z × ℝ) => L i y+b i p.1 < p.2)
      (fun i => measurableSet_lt ((measurable_const.add ((hb i).comp measurable_fst))) measurable_snd) F)
  have hmC (i : ι) : Measurable (c i) := by
    apply Measurable.neg
    apply Measurable.mul (hc.measurable.comp (measurable_const.add (hb i)))
    exact (measurable_filter_apply s (fun j z => L j y+b j z ≤ L i y+b i z)
      (fun j => measurableSet_le (measurable_const.add (hb j)) (measurable_const.add (hb i))) F).sub
      (measurable_filter_apply s (fun j z => L j y+b j z < L i y+b i z)
      (fun j => measurableSet_lt (measurable_const.add (hb j)) (measurable_const.add (hb i))) F)
  have hcB (i : ι) (z : Z) : ‖c i z‖ ≤ C*(2*M) := by
    dsimp [c]
    simp only [abs_neg,abs_mul]
    have hd := abs_sub_le (F (s.filter (fun j => L j y+b j z ≤ L i y+b i z))) 0
      (F (s.filter (fun j => L j y+b j z < L i y+b i z)))
    simp only [sub_zero,zero_sub,abs_neg] at hd
    apply mul_le_mul (hφC _) _ (abs_nonneg _) hC
    linarith [hM (s.filter (fun j => L j y+b j z ≤ L i y+b i z)),
      hM (s.filter (fun j => L j y+b j z < L i y+b i z))]
  have hiC (i : ι) : Integrable (c i) μ :=
    (integrable_const (C*(2*M))).mono' (hmC i).aestronglyMeasurable (ae_of_all _ (hcB i))
  have hiH : Integrable (H y) μ := by
    apply (integrable_const (∫ x, |φ x| * M)).mono' (hmH y).aestronglyMeasurable
    filter_upwards with z
    apply norm_integral_le_of_norm_le (hφ.abs.mul_const M)
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
  let K : NNReal := Real.nnabs (2*M*C*∑ i ∈ s, ‖L i‖)
  have hLip (z : Z) : LipschitzWith K (fun y => H y z) :=
    affine_threshold_lipschitz s L (fun i => b i z) F hφ hM0 hC hM hφC
  have hD : ∀ᵐ z ∂μ, HasFDerivAt (fun y => H y z) (∑ i ∈ s, c i z • L i) y := by
    filter_upwards [hi] with z hz
    exact moving_threshold_integral_hasFDerivAt s (fun i y => L i y+b i z) F L
      (fun i _ => (L i).hasFDerivAt.add_const _) hz hφ hc
  have hres := hasFDerivAt_integral_of_dominated_loc_of_lip (μ := μ) (F := H)
    (s := Set.univ) (bound := fun _ => (K : ℝ)) (F' := fun z => ∑ i ∈ s, c i z • L i)
    (Filter.univ_mem) (Filter.Eventually.of_forall (fun x => (hmH x).aestronglyMeasurable)) hiH
    (by
      have hm := (Finset.stronglyMeasurable_sum s (fun i _ => (hmC i).stronglyMeasurable.smul_const (L i))).aestronglyMeasurable (μ := μ)
      have he : (∑ i ∈ s, (fun z => c i z • L i)) = (fun z => ∑ i ∈ s, c i z • L i) := by
        funext z; exact Finset.sum_apply z s _
      rw [he] at hm
      exact hm)
    (ae_of_all _ (fun z => by simpa using (hLip z).lipschitzOnWith (s := Set.univ)))
    (integrable_const _) hD
  rw [integral_finsetSum s (fun i _ => (hiC i).smul_const (L i))] at hres
  simp only [integral_smul_const] at hres
  exact hres.2

end UniformSparsestCut.InterfaceStep

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.SliceCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SliceCoefficients
open MeasureTheory Set
open scoped BigOperators Topology
variable {X : Type u1} {Z : Type u2} {I : Type u3} {K : Type u4} {A : Type u5} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] [Fintype I] [Fintype K] [Fintype A]
  [DecidableEq I] [DecidableEq K]

lemma affine_hyperplane_null (L : Z →L[ℝ] ℝ) (hL : L ≠ 0) (t : ℝ)
    (ν : Measure Z) [ν.IsAddHaarMeasure] : ν {z | L z=t}=0 := by
  let H : AffineSubspace ℝ Z :=
    { carrier := {z | L z=t}
      smul_vsub_vadd_mem' := by
        intro c x y z hx hy hz
        change L x=t at hx
        change L y=t at hy
        change L z=t at hz
        change L (c • (x-y)+z)=t
        simp only [map_add,map_smul,map_sub,smul_eq_mul,hx,hy,hz]
        ring }
  have ht : H ≠ ⊤ := by
    intro he
    have hzero : (0:Z) ∈ H := by rw [he]; trivial
    change L 0=t at hzero
    rw [map_zero] at hzero
    apply hL
    ext x
    have hx : x ∈ H := by rw [he]; trivial
    change L x=t at hx
    simpa [← hzero] using hx
  exact Measure.addHaar_affineSubspace ν H ht

lemma thresholds_injective_ae (L : I → X →L[ℝ] ℝ) (B : I → Z →L[ℝ] ℝ)
    (q : I → K → ℝ) (hq : ∀ i, Function.Injective (q i))
    (hB : Function.Injective B) (ν : Measure Z) [ν.IsAddHaarMeasure]
    (μ : Measure Z) (hμ : μ ≪ ν) (y : X) :
    ∀ᵐ z ∂μ, Function.Injective (fun p : I × K => L p.1 y+B p.1 z+q p.1 p.2) := by
  have hp (p r : I × K) (hpr : p ≠ r) :
      ∀ᵐ z ∂μ, L p.1 y+B p.1 z+q p.1 p.2 ≠ L r.1 y+B r.1 z+q r.1 r.2 := by
    by_cases hi : p.1=r.1
    · filter_upwards with z hz
      have hk : p.2=r.2 := hq p.1 (by rw [← hi] at hz; linarith)
      exact hpr (Prod.ext hi hk)
    · have hn : B p.1-B r.1 ≠ 0 := sub_ne_zero.mpr (fun he => hi (hB he))
      have hnul := affine_hyperplane_null (B p.1-B r.1) hn
        (L r.1 y+q r.1 r.2-(L p.1 y+q p.1 p.2)) ν
      have hae : ∀ᵐ z ∂ν, (B p.1-B r.1) z ≠ L r.1 y+q r.1 r.2-(L p.1 y+q p.1 p.2) := by
        rw [ae_iff]; simpa only [not_not] using hnul
      filter_upwards [hμ.ae_le hae] with z hz he
      apply hz
      simp only [_root_.sub_apply]
      linarith
  have ha (p r : I × K) : ∀ᵐ z ∂μ,
      L p.1 y+B p.1 z+q p.1 p.2 = L r.1 y+B r.1 z+q r.1 r.2 → p=r := by
    by_cases hpr : p=r
    · exact ae_of_all _ (fun _ _ => hpr)
    · filter_upwards [hp p r hpr] with z hz he using (hz he).elim
  exact ae_all_iff.mpr (fun p => ae_all_iff.mpr (ha p))

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [BorelSpace Z] in

lemma family_derivative (L : I → X →L[ℝ] ℝ) (b : I × K → Z → ℝ)
    (hb : ∀ p, Measurable (b p)) (F : Finset (I × K) → ℝ)
    {φ : ℝ → ℝ} (hφ : Integrable φ) (hc : Continuous φ)
    {M C : ℝ} (hM0 : 0 ≤ M) (hC : 0 ≤ C)
    (hM : ∀ a, |F a| ≤ M) (hφC : ∀ x, |φ x| ≤ C)
    (μ : Measure Z) [IsFiniteMeasure μ] (y : X)
    (hi : ∀ᵐ z ∂μ, Function.Injective (fun p : I × K => L p.1 y+b p z)) :
    HasFDerivAt (fun y => ∫ z, (∫ x, φ x*F (Finset.univ.filter (fun p => L p.1 y+b p z<x))) ∂μ)
      (∑ i, (∑ k, ∫ z, -(φ (L i y+b (i,k) z)*
        (F (Finset.univ.filter (fun p => L p.1 y+b p z ≤ L i y+b (i,k) z))-
          F (Finset.univ.filter (fun p => L p.1 y+b p z < L i y+b (i,k) z)))) ∂μ) • L i) y := by
  have hd := InterfaceStep.averaged_threshold_derivative Finset.univ (fun p : I × K => L p.1)
    b hb F hφ hc hM0 hC hM hφC μ y (hi.mono (fun z hz => hz.injOn))
  rw [Fintype.sum_prod_type] at hd
  simp only [← Finset.sum_smul] at hd
  exact hd

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [BorelSpace Z] [DecidableEq K] in

lemma coefficient_budget (μ : Measure Z) [IsProbabilityMeasure μ]
    (w : K → Z → ℝ) (Δ : K → Z → A → ℝ) {J B : ℝ}
    (hJ : 0 ≤ J) (hw : ∀ k z, 0 ≤ w k z)
    (_hiw : ∀ k, Integrable (w k) μ)
    (hid : ∀ k a, Integrable (fun z => w k z*Δ k z a) μ)
    (hj : ∀ᵐ z ∂μ, ∀ k, w k z ≠ 0 → ∑ a, |Δ k z a| ≤ J)
    (hs : ∀ᵐ z ∂μ, ∑ k, w k z ≤ B) :
    (∑ a, |∑ k, ∫ z, -(w k z*Δ k z a) ∂μ|) ≤ J*B := by
  have hle (a : A) : |∑ k, ∫ z, -(w k z*Δ k z a) ∂μ| ≤
      ∑ k, ∫ z, w k z*|Δ k z a| ∂μ := by
    calc
      _ ≤ ∑ k, |∫ z, -(w k z*Δ k z a) ∂μ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum (fun k _ => by
        simpa only [Real.norm_eq_abs,abs_neg,abs_mul,abs_of_nonneg (hw k _)] using
          norm_integral_le_integral_norm (fun z => -(w k z*Δ k z a)))
  have hia (k : K) (a : A) : Integrable (fun z => w k z*|Δ k z a|) μ := by
    simpa only [abs_mul,abs_of_nonneg (hw k _)] using (hid k a).abs
  have hisum : Integrable (fun z => ∑ k, w k z*(∑ a, |Δ k z a|)) μ := by
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun a _ => hia k a))
  calc
    _ ≤ ∑ a, ∑ k, ∫ z, w k z*|Δ k z a| ∂μ := Finset.sum_le_sum (fun a _ => hle a)
    _ = ∫ z, ∑ k, w k z*(∑ a, |Δ k z a|) ∂μ := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
      rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun a _ => hia k a))]
      apply Finset.sum_congr rfl
      intro k _
      exact (integral_finsetSum _ (fun a _ => hia k a)).symm
    _ ≤ ∫ z, J*B ∂μ := by
      apply integral_mono_ae hisum (integrable_const _)
      filter_upwards [hj,hs] with z hz hzB
      calc
        _ ≤ ∑ k, w k z*J := Finset.sum_le_sum (fun k _ => by
          by_cases hk : w k z=0
          · simp [hk]
          · exact mul_le_mul_of_nonneg_left (hz k hk) (hw k z))
        _ = J*∑ k, w k z := by rw [← Finset.sum_mul]; ring
        _ ≤ J*B := mul_le_mul_of_nonneg_left hzB hJ
    _ = J*B := by simp

end UniformSparsestCut.SliceCoefficients

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.ProductSlice
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
open MeasureTheory Set
open scoped BigOperators
noncomputable section
variable {Z : Type u1} {I : Type u2} {K : Type u3} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure]
  [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]

omit [(volume : Measure Z).IsAddHaarMeasure] in
lemma cell_measurable (B : I → Z →L[ℝ] ℝ) (q : I → K → ℝ) (F : Finset (I × K) → ℝ) :
    Measurable (cell B q F) := by
  unfold cell
  apply InterfaceStep.measurable_filter_apply
  intro p
  exact measurableSet_lt ((form (B p.1)).measurable.add_const (q p.1 p.2)) measurable_const

omit [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] [DecidableEq I] [DecidableEq K] in
lemma cell_translate (B : I → Z →L[ℝ] ℝ) (q : I → K → ℝ)
    (F : Finset (I × K) → ℝ) (θ : ℝ × Z) (x : ℝ) (z : Z) :
    cell B q F (θ-(x,z)) =
      F (Finset.univ.filter (fun p => form (B p.1) θ+B p.1 z+q p.1 p.2<x)) := by
  unfold cell
  congr 1
  apply Finset.filter_congr
  intro p _
  change (θ.1-x-B p.1 (θ.2-z)+q p.1 p.2<0) ↔
    (θ.1-B p.1 θ.2+B p.1 z+q p.1 p.2<x)
  rw [map_sub]
  constructor <;> intro hp <;> linarith

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] in
lemma law_ac (ψ : Z → ℝ) (ν : Measure Z) : law ψ ν ≪ ν := withDensity_absolutelyContinuous _ _
omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] in
lemma law_integral {ψ : Z → ℝ} (hm : Measurable ψ) (hn : ∀ z, 0≤ψ z)
    (ν : Measure Z) (f : Z → ℝ) :
    (∫ z, f z ∂law ψ ν) = ∫ z, ψ z*f z ∂ν := by
  rw [law,integral_withDensity_eq_integral_toReal_smul (hm.ennreal_ofReal)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hn _),smul_eq_mul]
omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] in
lemma law_probability {ψ : Z → ℝ} (_hm : Measurable ψ) (hn : ∀ z, 0≤ψ z)
    (ν : Measure Z) (hi : Integrable ψ ν) (h1 : ∫ z, ψ z ∂ν=1) :
    IsProbabilityMeasure (law ψ ν) := by
  refine ⟨?_⟩
  change (ν.withDensity (fun z => ENNReal.ofReal (ψ z))) Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hn),h1]
  simp

lemma convolution_slice (B : I → Z →L[ℝ] ℝ) (q : I → K → ℝ)
    (F : Finset (I × K) → ℝ) {M : ℝ} (_hM0 : 0 ≤ M) (hM : ∀ a, |F a| ≤ M)
    {φ : ℝ → ℝ} {ψ : Z → ℝ} (hmφ : Measurable φ) (hmψ : Measurable ψ)
    (hφ : Integrable φ) (hψ : Integrable ψ) (hnψ : ∀ z, 0≤ψ z) (θ : ℝ × Z) :
    convolution (fun p : ℝ × Z => φ p.1*ψ p.2) (cell B q F)
        (ContinuousLinearMap.mul ℝ ℝ) volume θ =
      ∫ z, (∫ x, φ x*F (Finset.univ.filter
        (fun p => form (B p.1) θ+B p.1 z+q p.1 p.2<x))) ∂law ψ volume := by
  have hi : Integrable (fun p : ℝ × Z => (φ p.1*ψ p.2)*cell B q F (θ-p)) := by
    apply (((hφ.abs).mul_prod hψ.abs).mul_const M).mono'
      (((hmφ.comp measurable_fst).mul (hmψ.comp measurable_snd)).mul
        ((cell_measurable B q F).comp (measurable_const.sub measurable_id))).aestronglyMeasurable
    filter_upwards with p
    change |φ p.1*ψ p.2*cell B q F (θ-p)| ≤ |φ p.1| * |ψ p.2| * M
    simp only [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  change (∫ p : ℝ × Z, (φ p.1*ψ p.2)*cell B q F (θ-p) ∂(volume : Measure ℝ).prod (volume : Measure Z)) = _
  rw [integral_prod_symm _ hi,law_integral hmψ hnψ]
  apply integral_congr_ae
  filter_upwards with z
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [cell_translate]
  ring

lemma convolution_derivative (B : I → Z →L[ℝ] ℝ) (hB : Function.Injective B)
    (q : I → K → ℝ) (hq : ∀ i, Function.Injective (q i))
    (F : Finset (I × K) → ℝ) {M C : ℝ} (hM0 : 0≤M) (hC : 0≤C)
    (hM : ∀ a, |F a|≤M) {φ : ℝ → ℝ} {ψ : Z → ℝ}
    (hφ : Integrable φ) (hcφ : Continuous φ) (hφC : ∀ t, |φ t|≤C)
    (hmψ : Measurable ψ) (hnψ : ∀ z, 0≤ψ z) (hψ : Integrable ψ) (hψ1 : ∫ z, ψ z=1)
    (θ : ℝ × Z) :
    HasFDerivAt (convolution (fun p : ℝ × Z => φ p.1*ψ p.2) (cell B q F)
      (ContinuousLinearMap.mul ℝ ℝ) volume)
      (∑ i, (∑ k, ∫ z, -(φ (form (B i) θ+B i z+q i k)*
        (F (Finset.univ.filter (fun p => form (B p.1) θ+B p.1 z+q p.1 p.2 ≤ form (B i) θ+B i z+q i k))-
          F (Finset.univ.filter (fun p => form (B p.1) θ+B p.1 z+q p.1 p.2 < form (B i) θ+B i z+q i k))))
        ∂law ψ volume) • form (B i)) θ := by
  let := law_probability hmψ hnψ volume hψ hψ1
  have he : convolution (fun p : ℝ × Z => φ p.1*ψ p.2) (cell B q F)
      (ContinuousLinearMap.mul ℝ ℝ) volume =
      (fun θ => ∫ z, (∫ x, φ x*F (Finset.univ.filter
        (fun p => form (B p.1) θ+B p.1 z+q p.1 p.2<x))) ∂law ψ volume) :=
    funext (convolution_slice B q F hM0 hM hcφ.measurable hmψ hφ hψ hnψ)
  rw [he]
  have hi : ∀ᵐ z ∂law ψ volume, Function.Injective
      (fun p : I × K => form (B p.1) θ+(B p.1 z+q p.1 p.2)) := by
    simpa only [add_assoc] using SliceCoefficients.thresholds_injective_ae
      (fun i => form (B i)) B q hq hB volume (law ψ volume) (law_ac ψ volume) θ
  simpa only [add_assoc] using SliceCoefficients.family_derivative (fun i => form (B i))
    (fun p z => B p.1 z+q p.1 p.2) (fun p => (B p.1).measurable.add_const _) F
    hφ hcφ hM0 hC hM hφC (law ψ volume) θ hi
end
end UniformSparsestCut.ProductSlice

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.LatticeDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.LatticeDensity

lemma cell_bound {h h' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ t, HasDerivAt h (h' t) t) (hi : IntervalIntegrable h' volume a b) :
    (b-a)*h a ≤ (∫ t in a..b, h t)+(b-a)*(∫ t in a..b, |h' t|) := by
  have hc : Continuous h := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hh : ∀ t ∈ Icc a b, h a ≤ h t+∫ x in a..b, |h' x| := by
    intro t ht
    have hid : IntervalIntegrable h' volume a t := hi.mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl ht.2)
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hid
    have hm : (∫ x in a..t, |h' x|) ≤ ∫ x in a..b, |h' x| := by
      apply intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      · filter_upwards with x using abs_nonneg (h' x)
      · exact hi.abs
    have hn := intervalIntegral.abs_integral_le_integral_abs (f := h') (μ := volume) ht.1
    rw [he] at hn
    have habs : h a-h t ≤ |h t-h a| := by rw [abs_sub_comm]; exact le_abs_self _
    linarith
  have h := intervalIntegral.integral_mono_on (μ := volume) hab intervalIntegrable_const
    ((hc.intervalIntegrable a b).add intervalIntegrable_const) hh
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add (hc.intervalIntegrable a b) intervalIntegrable_const,
    intervalIntegral.integral_const] at h
  simpa only [smul_eq_mul] using h

lemma lattice_intervals_disjoint {τ : ℝ} (hτ : 0 < τ) :
    ∀ k l : ℤ, k ≠ l → Disjoint (Ioc ((k:ℝ)*τ) (((k:ℝ)+1)*τ))
      (Ioc ((l:ℝ)*τ) (((l:ℝ)+1)*τ)) := by
  intro k l hkl
  rcases lt_or_gt_of_ne hkl with h | h
  · apply Set.disjoint_left.mpr
    intro x hx hy
    have hkl' : (k:ℝ)+1 ≤ l := by exact_mod_cast (Int.add_one_le_iff.mpr h)
    have hz := mul_le_mul_of_nonneg_right hkl' hτ.le
    linarith [hx.2, hy.1]
  · apply Set.disjoint_left.mpr
    intro x hx hy
    have hkl' : (l:ℝ)+1 ≤ k := by exact_mod_cast (Int.add_one_le_iff.mpr h)
    have hz := mul_le_mul_of_nonneg_right hkl' hτ.le
    linarith [hy.2, hx.1]

lemma lattice_bound {h h' : ℝ → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hd : ∀ t, HasDerivAt h (h' t) t) (hh : ∀ t, 0 ≤ h t)
    (hi : Integrable h) (hi' : Integrable h') (s : Finset ℤ) :
    τ*(∑ k ∈ s, h ((k:ℝ)*τ)) ≤ (∫ t, h t)+τ*(∫ t, |h' t|) := by
  let U := ⋃ k ∈ s, Ioc ((k:ℝ)*τ) (((k:ℝ)+1)*τ)
  have hle (k : ℤ) : (k:ℝ)*τ ≤ ((k:ℝ)+1)*τ := by linarith
  have hs (f : ℝ → ℝ) (hf : Integrable f) :
      (∑ k ∈ s, ∫ t in ((k:ℝ)*τ)..(((k:ℝ)+1)*τ), f t) = ∫ t in U, f t := by
    simp_rw [intervalIntegral.integral_of_le (hle _)]
    exact (integral_biUnion_finset s (fun _ _ => measurableSet_Ioc)
      (fun k _ l _ hkl => lattice_intervals_disjoint hτ k l hkl)
      (fun _ _ => hf.integrableOn)).symm
  have he (k : ℤ) : (((k:ℝ)+1)*τ-(k:ℝ)*τ) = τ := by ring
  have hb (k : ℤ) : τ*h ((k:ℝ)*τ) ≤
      (∫ t in ((k:ℝ)*τ)..(((k:ℝ)+1)*τ), h t)+
        τ*(∫ t in ((k:ℝ)*τ)..(((k:ℝ)+1)*τ), |h' t|) := by
    simpa only [he] using cell_bound (a := (k:ℝ)*τ) (b := ((k:ℝ)+1)*τ)
      (by linarith) hd hi'.intervalIntegrable
  calc
    _ = ∑ k ∈ s, τ*h ((k:ℝ)*τ) := Finset.mul_sum ..
    _ ≤ ∑ k ∈ s, ((∫ t in ((k:ℝ)*τ)..(((k:ℝ)+1)*τ), h t)+
        τ*(∫ t in ((k:ℝ)*τ)..(((k:ℝ)+1)*τ), |h' t|)) := Finset.sum_le_sum (fun k _ => hb k)
    _ = (∫ t in U, h t)+τ*(∫ t in U, |h' t|) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hs h hi, hs (fun t => |h' t|) hi'.abs]
    _ ≤ _ := add_le_add
      (integral_mono_measure Measure.restrict_le_self (by filter_upwards with t using hh t) hi)
      (mul_le_mul_of_nonneg_left
        (integral_mono_measure Measure.restrict_le_self (by filter_upwards with t using abs_nonneg (h' t)) hi'.abs) hτ.le)

end UniformSparsestCut.LatticeDensity

namespace UniformSparsestCut.LatticeDensity
open MeasureTheory Set
open scoped BigOperators

lemma affine_integral (f : ℝ → ℝ) (c a : ℝ) :
    (∫ t, f (c-t/a)) = |a| *(∫ t, f t) := by
  rw [Measure.integral_comp_div (fun x => f (c-x)),smul_eq_mul,integral_sub_left_eq_self]

lemma affine_integrable {f : ℝ → ℝ} (hf : Integrable f) (c : ℝ) {a : ℝ} (ha : a ≠ 0) :
    Integrable (fun t => f (c-t/a)) :=
  ((integrable_comp_sub_left f c).mpr hf).comp_div ha

lemma affine_lattice_bound {φ φ' : ℝ → ℝ} (hd : ∀ t, HasDerivAt φ (φ' t) t)
    (hn : ∀ t, 0 ≤ φ t) (hi : Integrable φ) (hi' : Integrable φ')
    (h1 : ∫ t, φ t=1) {τ a : ℝ} (hτ : 0 < τ) (ha : a ≠ 0) (c : ℝ) (s : Finset ℤ) :
    τ/|a| *(∑ k ∈ s, φ (c-(k:ℝ)*τ/a)) ≤ 1+τ/|a| *(∫ t, |φ' t|) := by
  let h : ℝ → ℝ := fun t => φ (c-t/a)/|a|
  let h' : ℝ → ℝ := fun t => -(φ' (c-t/a)/a)/|a|
  have ha' : 0 < |a| := abs_pos.mpr ha
  have hD (t : ℝ) : HasDerivAt h (h' t) t := by
    convert! ((hd (c-t/a)).comp t (((hasDerivAt_id t).div_const a).const_sub c)).div_const |a| using 1
    dsimp [h']
    ring
  have hint : (∫ t, h t)=1 := by
    dsimp [h]
    rw [integral_div,affine_integral,h1,mul_one,div_self ha'.ne']
  have h'int : (∫ t, |h' t|)=(∫ t, |φ' t|)/|a| := by
    dsimp [h']
    simp only [abs_div,abs_neg,abs_abs]
    rw [integral_div,integral_div,affine_integral (fun t => |φ' t|)]
    field_simp
  have hb := lattice_bound hτ hD (fun t => div_nonneg (hn _) (abs_nonneg _))
    ((affine_integrable hi c ha).div_const _) (((affine_integrable hi' c ha).div_const a).neg.div_const _) s
  rw [hint,h'int] at hb
  dsimp [h] at hb
  rw [← Finset.sum_div] at hb
  convert hb using 1 <;> ring

end UniformSparsestCut.LatticeDensity

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.SliceIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ProductSlice
open MeasureTheory Set
open scoped BigOperators
noncomputable section
variable {Z : Type u1} {I : Type u2} {K : Type u3} {A : Type u4} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure]
  [Fintype I] [Fintype K] [Fintype A] [DecidableEq I] [DecidableEq K]

omit [FiniteDimensional ℝ Z] [(volume : Measure Z).IsAddHaarMeasure] [Fintype A] in
lemma jump_measurable (B : I → Z →L[ℝ] ℝ) (q : I → K → ℝ) (F : Finset (I × K) → A → ℝ)
    (θ : ℝ × Z) (i : I) (k : K) (α : A) : Measurable (fun z => jump B q F θ i k z α) := by
  unfold jump
  apply Measurable.sub
  · apply InterfaceStep.measurable_filter_apply Finset.univ _ _ (fun a => F a α)
    intro p
    exact measurableSet_le ((measurable_const.add (B p.1).measurable).add_const _)
      ((measurable_const.add (B i).measurable).add_const _)
  · apply InterfaceStep.measurable_filter_apply Finset.univ _ _ (fun a => F a α)
    intro p
    exact measurableSet_lt ((measurable_const.add (B p.1).measurable).add_const _)
      ((measurable_const.add (B i).measurable).add_const _)

omit [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] [Fintype A] [DecidableEq I] [DecidableEq K] in
lemma jump_bound (B : I → Z →L[ℝ] ℝ) (q : I → K → ℝ) (F : Finset (I × K) → A → ℝ)
    {M : ℝ} (hM : ∀ a α, |F a α|≤M) (θ : ℝ × Z) (i : I) (k : K) (z : Z) (α : A) :
    |jump B q F θ i k z α|≤2*M := by
  unfold jump
  exact (abs_sub _ _).trans (add_le_add (hM _ α) (hM _ α) |>.trans (by ring_nf; rfl))

omit [FiniteDimensional ℝ Z] [(volume : Measure Z).IsAddHaarMeasure] in

lemma common_coefficient_budget (B : I → Z →L[ℝ] ℝ) (s : Finset ℤ)
    (pivot : I → ℝ) (hp : ∀ i, pivot i≠0) {τ : ℝ} (hτ : 0<τ)
    (F : Finset (I × s) → A → ℝ) {M C J : ℝ}
    (_hM0 : 0≤M) (hC : 0≤C) (hJ : 0≤J) (hM : ∀ a α, |F a α|≤M)
    {φ φ' : ℝ → ℝ} (hd : ∀ t, HasDerivAt φ (φ' t) t) (hn : ∀ t, 0≤φ t)
    (hi : Integrable φ) (hi' : Integrable φ') (h1 : ∫ t, φ t=1) (hφC : ∀ t, |φ t|≤C)
    {ψ : Z → ℝ} (hmψ : Measurable ψ) (hnψ : ∀ z, 0≤ψ z) (hiψ : Integrable ψ) (hψ1 : ∫ z, ψ z=1)
    (θ : ℝ × Z) (i : I)
    (hj : ∀ᵐ z ∂law ψ volume, ∀ k : s,
      φ (form (B i) θ+B i z-(k:ℤ)*τ/pivot i)≠0 →
        (∑ α, |jump B (fun i (k : s) => -((k:ℤ)*τ/pivot i)) F θ i k z α|)≤J)
    (hsmall : τ/|pivot i| *(∫ t, |φ' t|)≤1) :
    (∑ α, |(pivot i)⁻¹ * ∑ k : s, ∫ z,
      -(φ (form (B i) θ+B i z-(k:ℤ)*τ/pivot i)*
        jump B (fun i (k : s) => -((k:ℤ)*τ/pivot i)) F θ i k z α) ∂law ψ volume|) ≤ 2*J/τ := by
  let μ := law ψ volume
  let q : I → s → ℝ := fun i (k : s) => -((k:ℤ)*τ/pivot i)
  let w : s → Z → ℝ := fun k z => φ (form (B i) θ+B i z-(k:ℤ)*τ/pivot i)
  have : IsProbabilityMeasure μ := law_probability hmψ hnψ volume hiψ hψ1
  have hcφ : Continuous φ := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hw (k : s) : Measurable (w k) :=
    hcφ.measurable.comp ((measurable_const.add (B i).measurable).sub_const _)
  have hiw (k : s) : Integrable (w k) μ :=
    (integrable_const C).mono' (hw k).aestronglyMeasurable (ae_of_all _ (fun z => hφC _))
  have hid (k : s) (α : A) : Integrable (fun z => w k z*jump B q F θ i k z α) μ := by
    apply (integrable_const (C*(2*M))).mono' ((hw k).mul (jump_measurable B q F θ i k α)).aestronglyMeasurable
    filter_upwards with z
    simp only [Pi.mul_apply, Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (hφC _) (jump_bound B q F hM θ i k z α) (abs_nonneg _) hC
  have hs (z : Z) : (∑ k : s, w k z)≤2*|pivot i|/τ := by
    have h := LatticeDensity.affine_lattice_bound hd hn hi hi' h1 hτ (hp i) (form (B i) θ+B i z) s
    rw [← Finset.sum_coe_sort] at h
    have hp0 : 0 < |pivot i| := abs_pos.mpr (hp i)
    have hmul : τ/|pivot i| *(∑ k : s, w k z)≤2 := by exact h.trans (by linarith)
    apply (le_div_iff₀ hτ).mpr
    have hh := mul_le_mul_of_nonneg_right hmul hp0.le
    have he : (τ/|pivot i| *(∑ k : s, w k z))*|pivot i| = (∑ k : s, w k z)*τ := by
      field_simp
    rwa [he] at hh
  have hb := SliceCoefficients.coefficient_budget μ w (jump B q F θ i) hJ
    (fun k z => hn _) hiw hid hj (ae_of_all _ hs)
  simp_rw [abs_mul,abs_inv,← Finset.mul_sum]
  calc
    _ ≤ |pivot i|⁻¹*(J*(2*|pivot i|/τ)) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (abs_nonneg _))
    _ = _ := by field_simp [abs_ne_zero.mpr (hp i)]

end
end UniformSparsestCut.ProductSlice

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
variable {E : Type u1} {I : Type u2} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype I] [DecidableEq I]

lemma neighboring_labels (ell : I → E →L[ℝ] ℝ) {τ : ℝ} (hτ : 0<τ)
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x∈U) (i : I) (k : ℤ)
    (heq : ell i x=(k:ℝ)*τ)
    (hother : ∀ j, j≠i → ∀ l : ℤ, ell j x≠(l:ℝ)*τ)
    (v : E) (hv : ell i v>0) :
    ∃ xp xm : E, xp∈U ∧ xm∈U ∧
      (∀ j (l : ℤ), ell j xp≠(l:ℝ)*τ) ∧
      (∀ j (l : ℤ), ell j xm≠(l:ℝ)*τ) ∧
      (∀ j, j≠i → ⌊ell j xp/τ⌋=⌊ell j x/τ⌋ ∧ ⌊ell j xm/τ⌋=⌊ell j x/τ⌋) ∧
      ⌊ell i xp/τ⌋=k ∧ ⌊ell i xm/τ⌋=k-1 := by
  let f (t : ℝ) := x+t • v
  have hf : Continuous f := (continuous_const.add (continuous_id.smul continuous_const))
  have h0 : f 0=x := by simp [f]
  have hmem : ∀ᶠ t in 𝓝 (0:ℝ), f t∈U := by
    have h := hf.continuousAt.eventually (hU.mem_nhds (show f 0∈U by simpa only [h0] using hx))
    exact h
  have ho : ∀ᶠ t in 𝓝 (0:ℝ), ∀ j, j≠i →
      (∀ l : ℤ, ell j (f t)≠(l:ℝ)*τ) ∧ ⌊ell j (f t)/τ⌋=⌊ell j x/τ⌋ := by
    apply eventually_all.mpr
    intro j
    by_cases hji : j=i
    · simp [hji]
    have hc : ContinuousAt (fun t => ell j (f t)/τ) (0:ℝ) :=
      (((ell j).continuous.comp hf).div_const τ).continuousAt
    have hn : ∀ l : ℤ, ell j (f 0)/τ≠(l:ℝ) := by
      intro l h
      apply hother j hji l
      simpa only [h0] using (div_eq_iff hτ.ne').mp h
    have ha : (⌊ell j (f 0)/τ⌋:ℝ)<ell j (f 0)/τ :=
      lt_of_le_of_ne (Int.floor_le _) (Ne.symm (hn _))
    have hb := Int.lt_floor_add_one (ell j (f 0)/τ)
    filter_upwards [hc.eventually_const_lt ha, hc.eventually_lt_const hb] with t ht ht'
    intro _
    have hfloor := Int.floor_eq_iff.mpr ⟨ht.le,ht'⟩
    refine ⟨?_, by simpa only [h0] using hfloor⟩
    intro l he
    have hl : ell j (f t)/τ=(l:ℝ) := by rw [he,mul_div_cancel_right₀ _ hτ.ne']
    rw [hl] at ht ht'
    have hli : ⌊ell j (f 0)/τ⌋<l := by exact_mod_cast ht
    have hli' : l<⌊ell j (f 0)/τ⌋+1 := by exact_mod_cast ht'
    omega
  have hsmall : ∀ᶠ t in 𝓝 (0:ℝ), |t|<τ/ell i v :=
    isOpen_lt continuous_abs continuous_const |>.mem_nhds (by simpa using div_pos hτ hv)
  have both := hmem.and (ho.and hsmall)
  obtain ⟨d,hd,hdsub⟩ := Metric.mem_nhds_iff.mp both
  let t := d/2
  have ht : 0<t := half_pos hd
  have htm : t<d := half_lt_self hd
  have hp := hdsub (show t∈Metric.ball (0:ℝ) d by simpa [Real.dist_eq,abs_of_pos ht] using htm)
  have hm := hdsub (show -t∈Metric.ball (0:ℝ) d by simpa [Real.dist_eq,abs_neg,abs_of_pos ht] using htm)
  have hb : t*ell i v<τ := (lt_div_iff₀ hv).mp (by simpa [abs_of_pos ht] using hp.2.2)
  have htpos : 0<t*ell i v := mul_pos ht hv
  have hep : ell i (f t)/τ=(k:ℝ)+t*ell i v/τ := by
    simp only [f,map_add,map_smul,smul_eq_mul,heq,add_div,mul_div_cancel_right₀ _ hτ.ne']
  have hem : ell i (f (-t))/τ=(k:ℝ)-t*ell i v/τ := by
    simp only [f,map_add,map_smul,smul_eq_mul,heq,add_div,mul_div_cancel_right₀ _ hτ.ne']
    ring
  have hfrac : 0<t*ell i v/τ ∧ t*ell i v/τ<1 := ⟨div_pos htpos hτ,(div_lt_one hτ).mpr hb⟩
  have hfp : ⌊ell i (f t)/τ⌋=k := Int.floor_eq_iff.mpr (by rw [hep]; constructor <;> linarith [hfrac.1,hfrac.2])
  have hfm : ⌊ell i (f (-t))/τ⌋=k-1 := Int.floor_eq_iff.mpr (by rw [hem]; push_cast; constructor <;> linarith [hfrac.1,hfrac.2])
  refine ⟨f t,f (-t),hp.1,hm.1,?_,?_,?_,hfp,hfm⟩
  · intro j l he
    by_cases hji : j=i
    · subst j
      have hl : ell i (f t)/τ=(l:ℝ) := by rw [he,mul_div_cancel_right₀ _ hτ.ne']
      have hkl : l=k := by simpa [hl] using hfp
      rw [hl,hkl] at hep
      linarith [hfrac.1]
    · exact (hp.2.1 j hji).1 l he
  · intro j l he
    by_cases hji : j=i
    · subst j
      have hl : ell i (f (-t))/τ=(l:ℝ) := by rw [he,mul_div_cancel_right₀ _ hτ.ne']
      have hkl : l=k-1 := by simpa [hl] using hfm
      rw [hl,hkl] at hem
      push_cast at hem
      linarith [hfrac.2]
    · exact (hm.2.1 j hji).1 l he
  · intro j hji
    exact ⟨(hp.2.1 j hji).2,(hm.2.1 j hji).2⟩

end UniformSparsestCut.CellInterface

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

omit [DecidableEq I] in
lemma extension_bounded (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (τ : ℝ) (s : Finset ℤ)
    (U : Set E) (F : LabelVertex ell τ U → A → ℝ) {M : ℝ} (hM0 : 0≤M)
    (hM : ∀ v a, |F v a|≤M) (P : Finset (I × s)) (a : A) :
    |extension ell pivot τ s U F P a|≤M := by
  classical
  unfold extension
  split_ifs
  · exact hM _ _
  · simpa using hM0

end
end UniformSparsestCut.CellInterface

namespace UniformSparsestCut.CellInterface
open Filter Set
open scoped Topology BigOperators
noncomputable section
variable {E : Type u6} {I : Type u7} {A : Type u8} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma mem_pattern_at (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    {τ : ℝ} (hτ : 0<τ) (s : Finset ℤ) {x : E} (i : I)
    (hr : ∀ k : ℤ, ell i x≠(k:ℝ)*τ) (k : s) :
    (i,k)∈pattern ell pivot τ s x ↔ if 0<pivot i then label ell τ x i<k.val else k.val≤label ell τ x i := by
  simp only [pattern,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hpi : 0<pivot i
  · rw [ite_eq_left hpi,div_neg_iff]
    simp only [hpi,not_lt_of_gt hpi,and_false,false_or,and_true]
    exact sub_neg.trans (floor_lt ell hτ x i k.val).symm
  · have hpn : pivot i<0 := lt_of_le_of_ne (le_of_not_gt hpi) (hp i)
    rw [ite_eq_right hpi,div_neg_iff]
    simp only [hpn,hpi,and_false,or_false,and_true]
    rw [sub_pos]
    symm
    change k.val≤⌊ell i x/τ⌋ ↔ _
    rw [Int.le_floor,le_div_iff₀ hτ]
    exact ⟨fun h => lt_of_le_of_ne h (Ne.symm (hr k.val)),le_of_lt⟩

omit [DecidableEq I] in
lemma mem_weakPattern_at (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    (τ : ℝ) (s : Finset ℤ) (x : E) (i : I) (k : s) (hr : ell i x≠(k.val:ℝ)*τ) :
    (i,k)∈weakPattern ell pivot τ s x ↔ (i,k)∈pattern ell pivot τ s x := by
  simp only [weakPattern,pattern,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨fun h => lt_of_le_of_ne h (div_ne_zero (sub_ne_zero.mpr hr) (hp i)), le_of_lt⟩

omit [DecidableEq I] in
lemma boundary_pattern (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    {τ : ℝ} (hτ : 0<τ) (s : Finset ℤ) {x : E} (i : I) (k : ℤ)
    (heq : ell i x=(k:ℝ)*τ) (l : s) :
    ((i,l)∈pattern ell pivot τ s x ↔ if 0<pivot i then k<l.val else l.val<k) ∧
    ((i,l)∈weakPattern ell pivot τ s x ↔ if 0<pivot i then k≤l.val else l.val≤k) := by
  simp only [pattern,weakPattern,Finset.mem_filter,Finset.mem_univ,true_and,heq]
  by_cases hpi : 0<pivot i
  · simp only [hpi,ite_true]
    rw [div_neg_iff,div_nonpos_iff]
    simp only [hpi,hpi.le,not_le_of_gt hpi,not_lt_of_gt hpi,and_false,false_or,and_true]
    constructor
    · rw [sub_neg,mul_lt_mul_iff_left₀ hτ]; exact_mod_cast Iff.rfl
    · rw [sub_nonpos,mul_le_mul_iff_left₀ hτ]; exact_mod_cast Iff.rfl
  · have hpn : pivot i<0 := lt_of_le_of_ne (le_of_not_gt hpi) (hp i)
    simp only [hpi,ite_false]
    rw [div_neg_iff,div_nonpos_iff]
    simp only [hpi,hpn,hpn.le,not_le_of_gt hpn,and_false,or_false,and_true]
    constructor
    · rw [sub_pos,mul_lt_mul_iff_left₀ hτ]; exact_mod_cast Iff.rfl
    · rw [sub_nonneg,mul_le_mul_iff_left₀ hτ]; exact_mod_cast Iff.rfl

lemma interface_extension_traces (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    {τ : ℝ} (hτ : 0<τ) (s : Finset ℤ) {U : Set E} (hU : IsOpen U)
    (hb : ∀ x∈U, regular ell τ x → ∀ i, label ell τ x i∈s)
    (F : LabelVertex ell τ U → A → ℝ) {x : E} (hx : x∈U) (i : I) (k : ℤ)
    (heq : ell i x=(k:ℝ)*τ) (hother : ∀ j, j≠i → ∀ l : ℤ, ell j x≠(l:ℝ)*τ)
    (v : E) (hv : ell i v>0) :
    ∃ vp vm : LabelVertex ell τ U,
      vp.val i=k ∧ vm.val i=k-1 ∧ (∀ j, j≠i → vp.val j=vm.val j) ∧
      (if 0<pivot i then
        extension ell pivot τ s U F (pattern ell pivot τ s x)=F vp ∧
        extension ell pivot τ s U F (weakPattern ell pivot τ s x)=F vm
      else
        extension ell pivot τ s U F (pattern ell pivot τ s x)=F vm ∧
        extension ell pivot τ s U F (weakPattern ell pivot τ s x)=F vp) := by
  obtain ⟨xp,xm,hxp,hxm,hrp,hrm,ho,hp0,hm0⟩ := neighboring_labels ell hτ hU hx i k heq hother v hv
  let vp := vertex ell τ xp hxp hrp
  let vm := vertex ell τ xm hxm hrm
  have hpv : vp.val i=k := hp0
  have hmv : vm.val i=k-1 := hm0
  refine ⟨vp,vm,hpv,hmv,(fun j hj => (ho j hj).1.trans (ho j hj).2.symm),?_⟩
  have hpp := extension_eq ell pivot hp hτ s U hb F xp hxp hrp
  have hpm := extension_eq ell pivot hp hτ s U hb F xm hxm hrm
  have hotherp (j : I) (hj : j≠i) (l : s) :
      ((j,l)∈pattern ell pivot τ s x ↔ (j,l)∈pattern ell pivot τ s xp) ∧
      ((j,l)∈pattern ell pivot τ s x ↔ (j,l)∈pattern ell pivot τ s xm) := by
    rw [mem_pattern_at ell pivot hp hτ s j (hother j hj),
      mem_pattern ell pivot hp hτ s hrp,mem_pattern ell pivot hp hτ s hrm]
    change (_ ↔ if _ then ⌊ell j xp/τ⌋<_ else _≤⌊ell j xp/τ⌋) ∧ _
    simp only [(ho j hj).1,(ho j hj).2,label]
    trivial
  by_cases hpi : 0<pivot i
  · rw [ite_eq_left hpi]
    have ep : pattern ell pivot τ s x=pattern ell pivot τ s xp := by
      ext ⟨j,l⟩
      by_cases hj : j=i
      · subst j
        rw [(boundary_pattern ell pivot hp hτ s i k heq l).1,mem_pattern ell pivot hp hτ s hrp]
        simp only [hpi,ite_true]
        change k<l.val ↔ ⌊ell i xp/τ⌋<l.val
        rw [hp0]
      · exact (hotherp j hj l).1
    have em : weakPattern ell pivot τ s x=pattern ell pivot τ s xm := by
      ext ⟨j,l⟩
      by_cases hj : j=i
      · subst j
        rw [(boundary_pattern ell pivot hp hτ s i k heq l).2,mem_pattern ell pivot hp hτ s hrm]
        simp only [hpi,ite_true]
        change k≤l.val ↔ ⌊ell i xm/τ⌋<l.val
        rw [hm0]; omega
      · rw [mem_weakPattern_at ell pivot hp τ s x j l (hother j hj l.val)]
        exact (hotherp j hj l).2
    rw [ep,em]; exact ⟨hpp,hpm⟩
  · rw [ite_eq_right hpi]
    have em : pattern ell pivot τ s x=pattern ell pivot τ s xm := by
      ext ⟨j,l⟩
      by_cases hj : j=i
      · subst j
        rw [(boundary_pattern ell pivot hp hτ s i k heq l).1,mem_pattern ell pivot hp hτ s hrm]
        simp only [hpi,ite_false]
        change l.val<k ↔ l.val≤⌊ell i xm/τ⌋
        rw [hm0]; omega
      · exact (hotherp j hj l).2
    have ep : weakPattern ell pivot τ s x=pattern ell pivot τ s xp := by
      ext ⟨j,l⟩
      by_cases hj : j=i
      · subst j
        rw [(boundary_pattern ell pivot hp hτ s i k heq l).2,mem_pattern ell pivot hp hτ s hrp]
        simp only [hpi,ite_false]
        change l.val≤k ↔ l.val≤⌊ell i xp/τ⌋
        rw [hp0]
      · rw [mem_weakPattern_at ell pivot hp τ s x j l (hother j hj l.val)]
        exact (hotherp j hj l).1
    rw [em,ep]; exact ⟨hpm,hpp⟩

lemma interface_jump_bound [Fintype A]
    (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    {τ : ℝ} (hτ : 0<τ) (s : Finset ℤ) {U : Set E} (hU : IsOpen U)
    (hb : ∀ x∈U, regular ell τ x → ∀ i, label ell τ x i∈s)
    (F : LabelVertex ell τ U → A → ℝ) {J : ℝ}
    (hF : ∀ (vp vm : LabelVertex ell τ U) (i : I), vp.val i=vm.val i+1 →
      (∀ j, j≠i → vp.val j=vm.val j) → ∑ a, |F vp a-F vm a|≤J)
    {x : E} (hx : x∈U) (i : I) (k : ℤ)
    (heq : ell i x=(k:ℝ)*τ) (hother : ∀ j, j≠i → ∀ l : ℤ, ell j x≠(l:ℝ)*τ)
    (v : E) (hv : ell i v>0) :
    ∑ a, |extension ell pivot τ s U F (weakPattern ell pivot τ s x) a-
      extension ell pivot τ s U F (pattern ell pivot τ s x) a|≤J := by
  obtain ⟨vp,vm,hvp,hvm,ho,htr⟩ := interface_extension_traces ell pivot hp hτ s hU hb F hx i k heq hother v hv
  have hbnd := hF vp vm i (by rw [hvp,hvm]; omega) ho
  by_cases hpi : 0<pivot i
  · rw [ite_eq_left hpi] at htr
    rw [htr.1,htr.2]
    simpa only [abs_sub_comm] using hbnd
  · rw [ite_eq_right hpi] at htr
    rwa [htr.1,htr.2]

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

omit [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] [Fintype I] [DecidableEq I] in
lemma event_form (B : I → Z →L[ℝ] ℝ) (pivot : I → ℝ) (τ : ℝ)
    (θ : ℝ × Z) (i : I) (k : ℤ) (z : Z) (j : I) :
    form (B j) (eventPoint B pivot τ θ i k z) =
      form (B j) θ+B j z-(form (B i) θ+B i z-(k:ℝ)*τ/pivot i) := by
  simp only [eventPoint,form_apply,map_sub]
  ring
omit [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] [Fintype I] [DecidableEq I] in
lemma event_on_plane (B : I → Z →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    (τ : ℝ) (θ : ℝ × Z) (i : I) (k : ℤ) (z : Z) :
    ell B pivot i (eventPoint B pivot τ θ i k z)=(k:ℝ)*τ := by
  change pivot i*form (B i) _=_
  rw [event_form]
  field_simp [hp i]
  ring

lemma event_other_regular (B : I → Z →L[ℝ] ℝ) (hB : Function.Injective B)
    (pivot : I → ℝ) (hp : ∀ i, pivot i≠0) (τ : ℝ) (θ : ℝ × Z) (i : I) (k : ℤ)
    (μ : Measure Z) (hμ : μ ≪ volume) :
    ∀ᵐ z ∂μ, ∀ j, j≠i → ∀ l : ℤ, ell B pivot j (eventPoint B pivot τ θ i k z)≠(l:ℝ)*τ := by
  apply ae_all_iff.mpr
  intro j
  by_cases hj : j=i
  · simp [hj]
  have hpair (l : ℤ) : ∀ᵐ z ∂μ, ell B pivot j (eventPoint B pivot τ θ i k z)≠(l:ℝ)*τ := by
    have hn : B j-B i≠0 := sub_ne_zero.mpr (fun he => hj (hB he))
    let t := (l:ℝ)*τ/pivot j-(k:ℝ)*τ/pivot i-form (B j) θ+form (B i) θ
    have hnul := SliceCoefficients.affine_hyperplane_null (B j-B i) hn t volume
    have hae : ∀ᵐ z ∂volume, (B j-B i) z≠t := by rw [ae_iff]; simpa only [not_not] using hnul
    filter_upwards [hμ.ae_le hae] with z hz he
    apply hz
    change pivot j*form (B j) _=_ at he
    rw [event_form] at he
    have he' : form (B j) θ+B j z-(form (B i) θ+B i z-(k:ℝ)*τ/pivot i)=(l:ℝ)*τ/pivot j :=
      (eq_div_iff (hp j)).mpr (by nlinarith [he])
    simp only [_root_.sub_apply]
    dsimp only [t]
    linarith
  filter_upwards [ae_all_iff.mpr hpair] with z hz _ using hz

omit [Fintype A] [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] [DecidableEq I] in
lemma jump_eq_traces (B : I → Z →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    (τ : ℝ) (s : Finset ℤ) (U : Set (ℝ × Z)) (F : LabelVertex (ell B pivot) τ U → A → ℝ)
    (θ : ℝ × Z) (i : I) (k : s) (z : Z) (α : A) :
    jump B (fun i (k : s) => -((k:ℤ)*τ/pivot i))
      (extension (ell B pivot) pivot τ s U F) θ i k z α =
    extension (ell B pivot) pivot τ s U F
      (weakPattern (ell B pivot) pivot τ s (eventPoint B pivot τ θ i k.val z)) α-
    extension (ell B pivot) pivot τ s U F
      (pattern (ell B pivot) pivot τ s (eventPoint B pivot τ θ i k.val z)) α := by
  unfold jump weakPattern pattern
  congr 2 <;> apply Finset.filter_congr <;> intro p _ <;>
    rw [normalized_ell B pivot hp,event_form] <;> constructor <;> intro h <;> linarith

lemma actual_jump_budget (B : I → Z →L[ℝ] ℝ) (hB : Function.Injective B)
    (pivot : I → ℝ) (hp : ∀ i, pivot i≠0) {τ : ℝ} (hτ : 0<τ) (s : Finset ℤ)
    {U : Set (ℝ × Z)} (hU : IsOpen U)
    (hb : ∀ x∈U, regular (ell B pivot) τ x → ∀ i, label (ell B pivot) τ x i∈s)
    (F : LabelVertex (ell B pivot) τ U → A → ℝ) {J : ℝ}
    (hF : ∀ (vp vm : LabelVertex (ell B pivot) τ U) (i : I), vp.val i=vm.val i+1 →
      (∀ j, j≠i → vp.val j=vm.val j) → ∑ a, |F vp a-F vm a|≤J)
    (φ : ℝ → ℝ) (ψ : Z → ℝ) (θ : ℝ × Z) (i : I)
    (hsupp : ∀ᵐ z ∂law ψ volume, ∀ k : s,
      φ (form (B i) θ+B i z-(k:ℤ)*τ/pivot i)≠0 → eventPoint B pivot τ θ i k.val z∈U) :
    ∀ᵐ z ∂law ψ volume, ∀ k : s,
      φ (form (B i) θ+B i z-(k:ℤ)*τ/pivot i)≠0 →
        ∑ a, |jump B (fun i (k : s) => -((k:ℤ)*τ/pivot i))
          (extension (ell B pivot) pivot τ s U F) θ i k z a|≤J := by
  have hae := ae_all_iff.mpr (fun k : s => event_other_regular B hB pivot hp τ θ i k.val _ (law_ac ψ volume))
  filter_upwards [hsupp,hae] with z hz hreg k hk
  simp_rw [jump_eq_traces B pivot hp]
  apply interface_jump_bound (ell B pivot) pivot hp hτ s hU hb F hF (hz k hk) i k.val
    (event_on_plane B pivot hp τ θ i k.val z) (hreg k) (pivot i,0)
  simp only [ell_apply,map_zero,sub_zero]
  exact mul_self_pos.mpr (hp i)

end
end UniformSparsestCut.ProductSlice

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.CoordinateSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.CoordinateSplit
variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (m+1))
local notation "Z" => EuclideanSpace ℝ (Fin m)

lemma preserving : MeasurePreserving (split (m := m)) volume volume := by
  have h₁ := MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin (m+1) → ℝ))
    (PiLp.volume_preserving_toLp (Fin (m+1)))
  have h₂ := volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0
  have h₃ : MeasurePreserving (Prod.map (id : ℝ → ℝ) (WithLp.toLp 2 : (Fin m → ℝ) → Z)) volume volume :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod (PiLp.volume_preserving_toLp (Fin m))
  have heq : (split (m := m) : E → ℝ × Z) = Prod.map (id : ℝ → ℝ) (WithLp.toLp 2) ∘
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0) ∘
      (MeasurableEquiv.toLp 2 (Fin (m+1) → ℝ)).symm := by
    ext x <;>
    simp [split,splitLinear,MeasurableEquiv.piFinSuccAbove_apply,Fin.tail]
  rw [heq]
  exact h₃.comp (h₂.comp h₁)

lemma integral_split (f : ℝ × Z → ℝ) : (∫ x : E, f (split x))=∫ p, f p :=
  preserving.integral_comp splitMeasurable.measurableEmbedding f

lemma convolution_split (φ : E → ℝ) (f : (ℝ × Z) → ℝ)
    (θ : E) :
    convolution φ (f ∘ split) (ContinuousLinearMap.mul ℝ ℝ) volume θ =
    convolution (φ ∘ split.symm) f (ContinuousLinearMap.mul ℝ ℝ) volume (split θ) := by
  change (∫ x : E, φ x*f (split (θ-x))) =
    ∫ p : ℝ × Z, φ (split.symm p)*f (split θ-p)
  rw [← integral_split]
  congr 1
  ext x
  simp only [ContinuousLinearEquiv.symm_apply_apply,map_sub]

lemma derivative_transport (h : (ℝ × Z) → ℝ) (D : (ℝ × Z) →L[ℝ] ℝ)
    (θ : E) (hd : HasFDerivAt h D (split θ)) :
    HasFDerivAt (h ∘ split) (D.comp split.toContinuousLinearMap) θ :=
  hd.comp θ split.hasFDerivAt

lemma slope_injective {I : Type u1} (u : I → E) (hu : ∀ i, u i 0≠0)
    (hn : ∀ i j, i≠j → ∀ t : ℝ, u i≠t • u j) : Function.Injective (fun i => slope (u i)) := by
  intro i j he
  by_contra hij
  apply hn i j hij (u i 0/u j 0)
  apply (InnerProductSpace.toDual ℝ E).injective
  ext x
  have hh := congrArg (fun L : Z →L[ℝ] ℝ => L (split x).2) he
  simp only [slope,_root_.smul_apply,smul_eq_mul] at hh
  change inner ℝ (u i) x=inner ℝ ((u i 0/u j 0) • u j) x
  rw [real_inner_smul_left]
  rw [inner_formula (u i),inner_formula (u j)]
  field_simp [hu i,hu j] at hh ⊢
  nlinarith
end UniformSparsestCut.CoordinateSplit

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

lemma form_comp (u : E) (hu : u 0≠0) :
    (form (slope u)).comp split.toContinuousLinearMap=(u 0)⁻¹ • InnerProductSpace.toDual ℝ E u := by
  ext x
  have hh := normalized_form u hu x
  change (split x).1-slope u (split x).2=(u 0)⁻¹*inner ℝ u x
  rw [← hh,div_eq_mul_inv,mul_comm]

lemma kernel_split (φ : ℝ → ℝ) :
    (ProductMollifier.kernel (m := m+1) φ) ∘ split.symm =
      (fun p : ℝ × Z => φ p.1*ProductMollifier.kernel φ p.2) := by
  funext p
  simp [ProductMollifier.kernel,Fin.prod_univ_succ]

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

omit [Fintype A] in
lemma chartFunction_measurable (u : I → E) (τ : ℝ) (s : Finset ℤ) (U : Set (ℝ × Z))
    (F : LabelVertex (ell (B u) (pivot u)) τ U → A → ℝ) (a : A) :
    Measurable (chartFunction u τ s U F a) :=
  (cell_measurable _ _ _).comp split.continuous.measurable

omit [Fintype A] in
lemma chartFunction_integrable (u : I → E) (τ : ℝ) (s : Finset ℤ) (U : Set (ℝ × Z))
    (F : LabelVertex (ell (B u) (pivot u)) τ U → A → ℝ) {M : ℝ} (hM : 0≤M)
    (hF : ∀ v a, |F v a|≤M) (a : A) : LocallyIntegrable (chartFunction u τ s U F a) := by
  apply (locallyIntegrable_const M).mono (chartFunction_measurable _ _ _ _ _ _).aestronglyMeasurable
  filter_upwards with x
  simpa only [chartFunction,Function.comp_apply,cell,values,Real.norm_eq_abs,abs_of_nonneg hM] using extension_bounded _ _ _ _ _ F hM hF _ a

lemma coefficients (u : I → E) (hu : ∀ i, u i 0≠0)
    (hnp : ∀ i j, i≠j → ∀ t : ℝ, u i≠t • u j)
    {τ lam : ℝ} (hτ : 0<τ) (hlam : 0<lam) (s : Finset ℤ)
    {U : Set (ℝ × Z)} (hU : IsOpen U)
    (hb : ∀ x∈U, regular (ell (B u) (pivot u)) τ x → ∀ i, label (ell (B u) (pivot u)) τ x i∈s)
    (F : LabelVertex (ell (B u) (pivot u)) τ U → A → ℝ) {M J : ℝ}
    (hM : 0≤M) (hJ : 0≤J) (hbound : ∀ v a, |F v a|≤M)
    (hF : ∀ (vp vm : LabelVertex (ell (B u) (pivot u)) τ U) (i : I), vp.val i=vm.val i+1 →
      (∀ j, j≠i → vp.val j=vm.val j) → ∑ a, |F vp a-F vm a|≤J)
    (θ : E)
    (hsupp : ∀ᵐ z ∂law (ProductMollifier.kernel (m := m) (ProductMollifier.density lam)) volume,
      ∀ t : ℝ, |t|<lam → split θ-(t,z)∈U)
    (hsmall : ∀ i, τ/|pivot u i| *(lam⁻¹*(∫ t, |deriv ProductMollifier.rho t|))≤1) :
    ∃ β : I → A → ℝ,
      (∀ a, HasFDerivAt (convolution (ProductMollifier.kernel (m := m+1) (ProductMollifier.density lam))
          (chartFunction u τ s U F a) (ContinuousLinearMap.mul ℝ ℝ) volume)
        (∑ i, β i a • InnerProductSpace.toDual ℝ E (u i)) θ) ∧
      (∀ i, ∑ a, |β i a|≤2*J/τ) := by
  let φ := ProductMollifier.density lam
  let ψ : Z → ℝ := ProductMollifier.kernel φ
  let Ξ := values u τ s U F
  let q (i : I) (k : s) := -((k:ℤ)*τ/pivot u i)
  have hBij := slope_injective u hu hnp
  have hq (i : I) : Function.Injective (q i) := by
    intro k l he
    apply Subtype.ext
    have he' : (k.val:ℝ)=(l.val:ℝ) := by
      dsimp only [q] at he
      exact (mul_left_inj' hτ.ne').mp ((div_left_inj' (show pivot u i≠0 from hu i)).mp (neg_injective he))
    exact_mod_cast he'
  have hcφ := (ProductMollifier.density_smooth lam).continuous
  have hiφ := ProductMollifier.density_integrable hlam
  have hcompφ := ProductMollifier.density_compact hlam
  have hdφ (t : ℝ) : HasDerivAt φ (deriv φ t) t :=
    ((ProductMollifier.density_smooth lam).differentiable (by simp) t).hasDerivAt
  have hiφ' : Integrable (deriv φ) :=
    ((ProductMollifier.density_smooth lam).continuous_deriv (by simp)).integrable_of_hasCompactSupport hcompφ.deriv
  have hnφ := ProductMollifier.density_nonneg hlam.le
  have hcψ := ProductMollifier.kernel_smooth (m := m) φ (ProductMollifier.density_smooth lam)
  have hcompψ := ProductMollifier.kernel_compact (m := m) hlam.le (fun t ht => (ProductMollifier.density_support hlam ht).le)
  have hiψ : Integrable ψ := hcψ.continuous.integrable_of_hasCompactSupport hcompψ
  have hnψ := ProductMollifier.kernel_nonneg (m := m) hnφ
  have hψ1 : ∫ z, ψ z=1 := by rw [ProductMollifier.kernel_integral,ProductMollifier.density_integral hlam,one_pow]
  obtain ⟨C,hC⟩ := hcφ.bounded_above_of_compact_support hcompφ
  have hC0 : 0≤C := (norm_nonneg (φ 0)).trans (hC 0)
  have hΞ : ∀ P a, |Ξ P a|≤M := extension_bounded _ _ _ _ _ F hM hbound
  let d (i : I) (a : A) : ℝ := ∑ k : s, ∫ z,
      -(φ (form (B u i) (split θ)+B u i z-(k:ℤ)*τ/pivot u i)*
        jump (B u) q Ξ (split θ) i k z a) ∂law ψ volume
  refine ⟨fun i a => (pivot u i)⁻¹*d i a,?_,?_⟩
  · intro a
    have hd := convolution_derivative (B u) hBij q hq (fun P => Ξ P a) hM hC0 (fun P => hΞ P a)
      hiφ hcφ hC hcψ.continuous.measurable hnψ hiψ hψ1 (split θ)
    have he : convolution (ProductMollifier.kernel (m := m+1) φ) (chartFunction u τ s U F a)
        (ContinuousLinearMap.mul ℝ ℝ) volume =
        (convolution (fun p : ℝ × Z => φ p.1*ψ p.2) (cell (B u) q (fun P => Ξ P a))
          (ContinuousLinearMap.mul ℝ ℝ) volume) ∘ split := by
      funext x
      rw [chartFunction,convolution_split,kernel_split]
      rfl
    rw [he]
    have hd' : HasFDerivAt
        (convolution (fun p : ℝ × Z => φ p.1*ψ p.2) (cell (B u) q (fun P => Ξ P a))
          (ContinuousLinearMap.mul ℝ ℝ) volume)
        (∑ i, d i a • form (B u i)) (split θ) := by
      simpa only [d,jump,q,sub_eq_add_neg] using hd
    have ht := derivative_transport _ _ θ hd'
    have hL : (∑ i, d i a • form (B u i)).comp split.toContinuousLinearMap =
        ∑ i, ((pivot u i)⁻¹*d i a) • InnerProductSpace.toDual ℝ E (u i) := by
      ext x
      simp only [ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      have hi := congrArg (fun L : E →L[ℝ] ℝ => L x) (form_comp (u i) (hu i))
      change form (B u i) (split x)=(pivot u i)⁻¹*inner ℝ (u i) x at hi
      change d i a * form (B u i) (split x)=((pivot u i)⁻¹*d i a)*inner ℝ (u i) x
      rw [hi]
      ring
    rw [hL] at ht
    exact ht
  · intro i
    have hj := actual_jump_budget (B u) hBij (pivot u) hu hτ s hU hb F hF φ ψ (split θ) i (by
      filter_upwards [hsupp] with z hz k hk
      exact hz _ (ProductMollifier.density_support hlam hk))
    have hh := common_coefficient_budget (B u) s (pivot u) hu hτ Ξ hM hC0 hJ hΞ
      hdφ hnφ hiφ hiφ' (ProductMollifier.density_integral hlam) hC
      hcψ.continuous.measurable hnψ hiψ hψ1 (split θ) i hj (by
        rw [ProductMollifier.density_deriv_integral hlam]
        exact hsmall i)
    exact hh
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

lemma domain_open : IsOpen (domain (m := m)) := by
  apply IsOpen.preimage split.symm.continuous
  change IsOpen {θ : E | ∀ j, |θ j|<2}
  simp only [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_lt (by fun_prop) continuous_const

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

omit [Fintype A] in
lemma function_measurable (u : Fin S → Fin N → E) (hu : ∀ s i, u s i 0≠0) (τ : ℝ)
    (F : RoundedCharts.Vertex u τ → A → ℝ) (s : Fin S) (a : A) : Measurable (function u hu τ F s a) :=
  chartFunction_measurable _ _ _ _ _ _
omit [Fintype A] in
lemma function_bounded (u : Fin S → Fin N → E) (hu : ∀ s i, u s i 0≠0) (τ : ℝ)
    (F : RoundedCharts.Vertex u τ → A → ℝ) {M : ℝ} (hM : 0≤M) (hF : ∀ v a, |F v a|≤M)
    (s : Fin S) (a : A) (x : E) : |function u hu τ F s a x|≤M := by
  exact CellInterface.extension_bounded (ProductSlice.ell (B (u s)) (pivot (u s))) (pivot (u s)) τ (labels (m := m) τ) domain (fun v => F (mapVertex u hu τ s v)) hM (fun v a => hF _ a) _ a
omit [Fintype A] in
lemma function_integrable (u : Fin S → Fin N → E) (hu : ∀ s i, u s i 0≠0) (τ : ℝ)
    (F : RoundedCharts.Vertex u τ → A → ℝ) {M : ℝ} (hM : 0≤M) (hF : ∀ v a, |F v a|≤M)
    (s : Fin S) (a : A) : LocallyIntegrable (function u hu τ F s a) :=
  chartFunction_integrable _ _ _ _ _ hM (fun _v a => hF _ a) a

lemma support_domain {lam : ℝ} (hlam : 0<lam) (hlam1 : lam<1) (θ : E)
    (hθ : ∀ j, |θ j|≤1) :
    ∀ᵐ z ∂ProductSlice.law (ProductMollifier.kernel (m := m) (ProductMollifier.density lam)) volume,
      ∀ t : ℝ, |t|<lam → split θ-(t,z)∈domain := by
  apply (ae_withDensity_iff ((ProductMollifier.kernel_smooth (m := m) _ (ProductMollifier.density_smooth lam)).continuous.measurable.ennreal_ofReal)).mpr
  filter_upwards with z hz t ht
  have hψ : ProductMollifier.kernel (ProductMollifier.density lam) z≠0 := by
    intro he
    exact hz (by simp [he])
  have hz' (j : Fin m) : |z j|<lam := by
    apply ProductMollifier.density_support hlam
    intro he
    exact hψ (Finset.prod_eq_zero (Finset.mem_univ j) he)
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · change |θ 0-t|<2
    exact (abs_sub _ _).trans_lt (by linarith [hθ 0])
  · change |θ i.succ-z i|<2
    exact (abs_sub _ _).trans_lt (by linarith [hθ i.succ,hz' i])

lemma normal_coefficients (u : Fin S → Fin N → E) (hu : ∀ s i, u s i 0≠0)
    (hnp : ∀ s i j, i≠j → ∀ t : ℝ, u s i≠t • u s j) (hn : ∀ s i, ‖u s i‖≤2)
    {τ lam : ℝ} (hτ : 0<τ) (hlam : 0<lam) (hlam1 : lam<1)
    (F : RoundedCharts.Vertex u τ → A → ℝ) {M J : ℝ} (hM : 0≤M) (hJ : 0≤J)
    (hbound : ∀ v a, |F v a|≤M)
    (hF : ∀ (vp vm : RoundedCharts.Vertex u τ) (i : Fin N), vp.val.1=vm.val.1 →
      vp.val.2 i=vm.val.2 i+1 → (∀ j, j≠i → vp.val.2 j=vm.val.2 j) →
      ∑ a, |F vp a-F vm a|≤J)
    (hsmall : ∀ s i, τ/|u s i 0| *(lam⁻¹*(∫ t, |deriv ProductMollifier.rho t|))≤1)
    (s : Fin S) (θ : E) (hθ : ∀ j, |θ j|≤1) :
    ∃ β : Fin N → A → ℝ,
      (∀ a, HasFDerivAt (convolution (ProductMollifier.kernel (m := m+1) (ProductMollifier.density lam))
          (function u hu τ F s a) (ContinuousLinearMap.mul ℝ ℝ) volume)
        (∑ i, β i a • InnerProductSpace.toDual ℝ E (u s i)) θ) ∧
      (∀ i, ∑ a, |β i a|≤2*J/τ) := by
  exact EuclideanCells.coefficients (u s) (hu s) (hnp s) hτ hlam _ domain_open
    (labels_bound (u s) (hu s) hτ (hn s)) (fun v => F (mapVertex u hu τ s v))
    hM hJ (fun v a => hbound _ a)
    (fun vp vm i hi hj => hF _ _ i rfl hi hj) θ (support_domain hlam hlam1 θ hθ) (hsmall s)

lemma regular_sub (u : Fin N → E) (hu : ∀ i, u i 0≠0) (τ : ℝ) (θ : E) :
    ∀ᵐ z : E, RoundedCharts.regular u τ (θ-z) := by
  have hh := RoundedCharts.ae_regular u τ (fun i h => hu i (by rw [h]; rfl))
  have hmp := (measurePreserving_add_left volume θ).comp (Measure.measurePreserving_neg (volume : Measure E))
  simpa only [Function.comp_apply, sub_eq_add_neg] using hmp.quasiMeasurePreserving.ae hh

end
end UniformSparsestCut.ConcreteCells

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.GradientBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.GradientBudget
variable {E : Type u1} {S : Type u2} {I : Type u3} {A : Type u4} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype S] [Fintype I] [Fintype A] [DecidableEq S]

lemma directional_control (u : I → E) (β : I → ℝ) (a e : E) {δ : ℝ}
    (hδ : 0 ≤ δ) (ha : a+e=∑ i, β i • u i)
    (hu : ∀ i, |inner ℝ (u i) a| ≤ δ*‖a‖) :
    ‖a‖ ≤ δ*∑ i, |β i|+‖e‖ := by
  by_cases hz : a=0
  · simp only [hz,norm_zero]; positivity
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr hz
  have hs : |inner ℝ (∑ i, β i • u i) a| ≤ δ*‖a‖*∑ i, |β i| := by
    rw [sum_inner]
    calc
      _ ≤ ∑ i, |inner ℝ (β i • u i) a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |β i| * (δ*‖a‖) := by
        apply Finset.sum_le_sum; intro i _
        rw [real_inner_smul_left,abs_mul]
        exact mul_le_mul_of_nonneg_left (hu i) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hip : ‖a‖^2 ≤ |inner ℝ (∑ i, β i • u i) a|+‖e‖*‖a‖ := by
    rw [← ha,inner_add_left]
    have h := abs_real_inner_le_norm e a
    rw [real_inner_self_eq_norm_sq]
    have hab := le_abs_self (‖a‖^2+inner ℝ e a)
    have hab' := neg_le_abs (inner ℝ e a)
    nlinarith
  have hmul : ‖a‖*‖a‖ ≤ (δ*∑ i, |β i|+‖e‖)*‖a‖ := by nlinarith
  nlinarith

omit [DecidableEq S] in
lemma good_chart_average (u : S → I → E) (β : S → I → ℝ) (a : E) (e : S → E)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ s, a+e s=∑ i, β s i • u s i)
    (good : Finset S) (hgood : (Fintype.card S : ℝ)/2 ≤ good.card)
    (hu : ∀ s ∈ good, ∀ i, |inner ℝ (u s i) a| ≤ δ*‖a‖) :
    (Fintype.card S : ℝ)*‖a‖ ≤ 2*∑ s, (δ*∑ i, |β s i|+‖e s‖) := by
  have hg : (good.card:ℝ)*‖a‖ ≤ ∑ s ∈ good, (δ*∑ i, |β s i|+‖e s‖) := by
    calc
      _ = ∑ _s ∈ good, ‖a‖ := by simp
      _ ≤ _ := Finset.sum_le_sum (fun s hs => directional_control (u s) (β s) a (e s) hδ (ha s) (hu s hs))
  have hsub : (∑ s ∈ good, (δ*∑ i, |β s i|+‖e s‖)) ≤ ∑ s, (δ*∑ i, |β s i|+‖e s‖) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro s _ _; positivity
  have hmult := mul_le_mul_of_nonneg_right hgood (norm_nonneg a)
  linarith

omit [DecidableEq S] in
lemma total_gradient (u : S → I → E) (β : S → I → A → ℝ) (a : A → E) (e : S → A → E)
    {δ B R : ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ s α, a α+e s α=∑ i, β s i α • u s i)
    (hg : ∀ α, ∃ good : Finset S, (Fintype.card S : ℝ)/2 ≤ good.card ∧
      ∀ s ∈ good, ∀ i, |inner ℝ (u s i) (a α)| ≤ δ*‖a α‖)
    (hβ : ∀ s, ∑ i, ∑ α, |β s i α| ≤ B)
    (he : ∀ s, ∑ α, ‖e s α‖ ≤ R) (hS : 0 < Fintype.card S) :
    ∑ α, ‖a α‖ ≤ 2*(δ*B+R) := by
  have hcomp (α : A) : (Fintype.card S : ℝ)*‖a α‖ ≤
      2*∑ s, (δ*∑ i, |β s i α|+‖e s α‖) := by
    obtain ⟨good,hgood,hu⟩ := hg α
    exact good_chart_average u (fun s i => β s i α) (a α) (fun s => e s α) hδ
      (fun s => ha s α) good hgood hu
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun α _ => hcomp α)
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm] at hs
  have hb (s : S) : (∑ α, (δ*∑ i, |β s i α|+‖e s α‖)) ≤ δ*B+R := by
    rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_comm]
    exact add_le_add (mul_le_mul_of_nonneg_left (hβ s) hδ) (he s)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hb s)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  have hcard : (0:ℝ) < Fintype.card S := by exact_mod_cast hS
  nlinarith

end UniformSparsestCut.GradientBudget

namespace UniformSparsestCut.ConvolutionBounds
open MeasureTheory Set
open scoped BigOperators
variable {G : Type u5} {A : Type u6} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasurableSpace G] [BorelSpace G] [Fintype A]
  {μ : Measure G} [SFinite μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant]

omit [NormedSpace ℝ G] [BorelSpace G] [SFinite μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant] in
lemma smooth_eq (κ f : G → ℝ) (x : G) :
    smooth κ f μ x = ∫ z, κ z*f (x-z) ∂μ := rfl

lemma smooth_deriv {κ f : G → ℝ} (hk : HasCompactSupport κ)
    (hc : ContDiff ℝ 1 κ) (hf : LocallyIntegrable f μ) (x h : G) :
    fderiv ℝ (smooth κ f μ) x h = ∫ z, (fderiv ℝ κ z h)*f (x-z) ∂μ := by
  unfold smooth
  rw [(hk.hasFDerivAt_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hc hf x).fderiv]
  have hi := (hk.fderiv ℝ).convolutionExists_left
    ((ContinuousLinearMap.mul ℝ ℝ).precompL G) (hc.continuous_fderiv (by norm_num)) hf x
  exact ContinuousLinearMap.integral_apply hi h

omit [SFinite μ] in
lemma smooth_deriv_integrable {κ f : G → ℝ} (hk : HasCompactSupport κ)
    (hc : ContDiff ℝ 1 κ) (hf : LocallyIntegrable f μ) (x h : G) :
    Integrable (fun z => (fderiv ℝ κ z h)*f (x-z)) μ := by
  have hi := (hk.fderiv ℝ).convolutionExists_left
    ((ContinuousLinearMap.mul ℝ ℝ).precompL G) (hc.continuous_fderiv (by norm_num)) hf x
  exact hi.apply_continuousLinearMap h

omit [NormedAddCommGroup G] [NormedSpace ℝ G] [BorelSpace G] [SFinite μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant] in

lemma integral_l1_bound (f : A → G → ℝ) (hf : ∀ a, Integrable (f a) μ)
    {B : G → ℝ} (hB : Integrable B μ) (hb : ∀ᵐ z ∂μ, ∑ a, |f a z| ≤ B z) :
    (∑ a, |∫ z, f a z ∂μ|) ≤ ∫ z, B z ∂μ := by
  calc
    _ ≤ ∑ a, ∫ z, |f a z| ∂μ := Finset.sum_le_sum (fun a _ => by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (f a))
    _ = ∫ z, ∑ a, |f a z| ∂μ := (integral_finsetSum _ (fun a _ => (hf a).abs)).symm
    _ ≤ _ := integral_mono_ae (integrable_finsetSum _ (fun a _ => (hf a).abs)) hB hb

lemma mismatch {κ : G → ℝ} (hk : HasCompactSupport κ) (hc : ContDiff ℝ 1 κ)
    (f g : A → G → ℝ) (hf : ∀ a, LocallyIntegrable (f a) μ)
    (hg : ∀ a, LocallyIntegrable (g a) μ) (x h : G) {B : ℝ}
    (hki : Integrable (fun z => |fderiv ℝ κ z h|) μ)
    (hb : ∀ᵐ z ∂μ, fderiv ℝ κ z h ≠ 0 → ∑ a, |f a (x-z)-g a (x-z)| ≤ B) :
    (∑ a, |fderiv ℝ (smooth κ (f a) μ) x h-fderiv ℝ (smooth κ (g a) μ) x h|) ≤
      B*(∫ z, |fderiv ℝ κ z h| ∂μ) := by
  simp_rw [smooth_deriv hk hc (hf _),smooth_deriv hk hc (hg _)]
  have hi (a : A) : Integrable (fun z => fderiv ℝ κ z h*(f a (x-z)-g a (x-z))) μ := by
    convert! (smooth_deriv_integrable hk hc (hf a) x h).sub
      (smooth_deriv_integrable hk hc (hg a) x h) using 1
    ext z
    simp only [Pi.sub_apply,mul_sub]
  have he (a : A) : (∫ z, fderiv ℝ κ z h*f a (x-z) ∂μ)-
      (∫ z, fderiv ℝ κ z h*g a (x-z) ∂μ) =
      ∫ z, fderiv ℝ κ z h*(f a (x-z)-g a (x-z)) ∂μ := by
    simp only [mul_sub]
    exact (integral_sub (smooth_deriv_integrable hk hc (hf a) x h)
      (smooth_deriv_integrable hk hc (hg a) x h)).symm
  simp_rw [he]
  rw [← integral_const_mul]
  apply integral_l1_bound _ hi (hki.const_mul B)
  filter_upwards [hb] with z hz
  by_cases hn : fderiv ℝ κ z h=0
  · simp [hn]
  · simp_rw [abs_mul,← Finset.mul_sum]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hz hn) (abs_nonneg (fderiv ℝ κ z h))

omit [NormedSpace ℝ G] [SFinite μ] in

lemma error {κ : G → ℝ} (hk : HasCompactSupport κ) (hc : Continuous κ)
    (hki : Integrable κ μ) (hkn : ∀ z, 0 ≤ κ z) (hk1 : ∫ z, κ z ∂μ=1)
    (f : A → G → ℝ) (hf : ∀ a, LocallyIntegrable (f a) μ) (x : G) {B : ℝ}
    (hb : ∀ᵐ z ∂μ, κ z ≠ 0 → ∑ a, |f a (x-z)-f a x| ≤ B) :
    (∑ a, |smooth κ (f a) μ x-f a x|) ≤ B := by
  have hi0 (a : A) : Integrable (fun z => κ z*f a (x-z)) μ :=
    hk.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) hc (hf a) x
  have hi (a : A) : Integrable (fun z => κ z*(f a (x-z)-f a x)) μ := by
    convert! (hi0 a).sub (hki.mul_const (f a x)) using 1
    ext z
    simp only [Pi.sub_apply,mul_sub]
  have he (a : A) : smooth κ (f a) μ x-f a x = ∫ z, κ z*(f a (x-z)-f a x) ∂μ := by
    rw [smooth_eq]
    simp only [mul_sub]
    rw [integral_sub (hi0 a)
      (hki.mul_const (f a x)),integral_mul_const,hk1,one_mul]
  simp_rw [he]
  have hres := integral_l1_bound (μ := μ) _ hi (hki.const_mul B) (by
    filter_upwards [hb] with z hz
    by_cases hn : κ z=0
    · simp [hn]
    · simp_rw [abs_mul,abs_of_nonneg (hkn z),← Finset.mul_sum]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hz hn) (hkn z))
  simpa only [integral_const_mul,hk1,mul_one] using hres

end UniformSparsestCut.ConvolutionBounds

namespace UniformSparsestCut.GradientCalculus
open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m : ℕ} {A : Type u7} {S : Type u8} {I : Type u9} [Fintype A] [Fintype S] [Fintype I] [DecidableEq S]
local notation "E" => EuclideanSpace ℝ (Fin m)

lemma vector_coordinate (D : StrongDual ℝ E) (j : Fin m) :
    vector D j=D (EuclideanSpace.single j 1) := by
  have h := vector_inner D (EuclideanSpace.single j 1)
  simpa [PiLp.inner_apply,PiLp.single_apply] using h
lemma norm_le_partials (D : StrongDual ℝ E) : ‖D‖≤∑ j, |D (EuclideanSpace.single j 1)| := by
  rw [← vector_norm]
  have he : vector D=∑ j, EuclideanSpace.single j (vector D j) := by
    ext i
    simp
  calc
    _ = ‖∑ j, EuclideanSpace.single j (vector D j)‖ := congrArg norm he
    _ ≤ ∑ j, ‖EuclideanSpace.single j (vector D j)‖ := norm_sum_le _ _
    _ = _ := by simp only [PiLp.norm_single,Real.norm_eq_abs,vector_coordinate]
lemma vector_representation (D : StrongDual ℝ E) (u : I → E) (β : I → ℝ)
    (hd : D=∑ i, β i • InnerProductSpace.toDual ℝ E (u i)) :
    vector D=∑ i, β i • u i := by
  apply (InnerProductSpace.toDual ℝ E).injective
  simp only [vector,LinearIsometryEquiv.apply_symm_apply,map_sum,map_smul,hd]

lemma gradient_mismatch {κ : E → ℝ} (hk : HasCompactSupport κ) (hc : ContDiff ℝ 1 κ)
    (f g : A → E → ℝ) (hf : ∀ a, LocallyIntegrable (f a))
    (hg : ∀ a, LocallyIntegrable (g a)) (x : E) {B L : ℝ}
    (hki : ∀ j : Fin m, Integrable (fun z => |fderiv ℝ κ z (EuclideanSpace.single j 1)|))
    (hL : ∀ j : Fin m, ∫ z, |fderiv ℝ κ z (EuclideanSpace.single j 1)| = L)
    (hb : ∀ᵐ z, (∃ j : Fin m, fderiv ℝ κ z (EuclideanSpace.single j 1)≠0) →
      ∑ a, |f a (x-z)-g a (x-z)|≤B) :
    (∑ a, ‖fderiv ℝ (ConvolutionBounds.smooth κ (f a) volume) x-
      fderiv ℝ (ConvolutionBounds.smooth κ (g a) volume) x‖)≤(m:ℝ)*B*L := by
  calc
    _ ≤ ∑ a, ∑ j : Fin m, |fderiv ℝ (ConvolutionBounds.smooth κ (f a) volume) x (EuclideanSpace.single j 1)-
        fderiv ℝ (ConvolutionBounds.smooth κ (g a) volume) x (EuclideanSpace.single j 1)| := by
      apply Finset.sum_le_sum; intro a _
      exact norm_le_partials _
    _ = ∑ j : Fin m, ∑ a, |fderiv ℝ (ConvolutionBounds.smooth κ (f a) volume) x (EuclideanSpace.single j 1)-
        fderiv ℝ (ConvolutionBounds.smooth κ (g a) volume) x (EuclideanSpace.single j 1)| := Finset.sum_comm
    _ ≤ ∑ _j : Fin m, B*L := by
      apply Finset.sum_le_sum; intro j _
      rw [← hL j]
      apply ConvolutionBounds.mismatch hk hc f g hf hg x _ (hki j)
      filter_upwards [hb] with z hz hj using hz ⟨j,hj⟩
    _ = _ := by simp; ring

omit [DecidableEq S] in
lemma gradient_budget (u : S → I → E) (β : S → I → A → ℝ)
    (D : S → A → StrongDual ℝ E) (base : A → StrongDual ℝ E)
    {δ B R : ℝ} (hδ : 0≤δ)
    (hd : ∀ s a, D s a=∑ i, β s i a • InnerProductSpace.toDual ℝ E (u s i))
    (hgood : ∀ a, ∃ good : Finset S, (Fintype.card S:ℝ)/2≤good.card ∧
      ∀ s∈good, ∀ i, |base a (u s i)|≤δ*‖base a‖)
    (hβ : ∀ s, ∑ i, ∑ a, |β s i a|≤B)
    (he : ∀ s, ∑ a, ‖D s a-base a‖≤R) (hS : 0<Fintype.card S) :
    ∑ a, ‖base a‖≤2*(δ*B+R) := by
  have hvec (s : S) (a : A) : vector (base a)+vector (D s a-base a)=∑ i, β s i a • u s i := by
    change (InnerProductSpace.toDual ℝ E).symm (base a)+(InnerProductSpace.toDual ℝ E).symm (D s a-base a)=_
    rw [← map_add,add_sub_cancel]
    exact vector_representation _ _ _ (hd s a)
  have hg (a : A) : ∃ good : Finset S, (Fintype.card S:ℝ)/2≤good.card ∧
      ∀ s∈good, ∀ i, |inner ℝ (u s i) (vector (base a))|≤δ*‖vector (base a)‖ := by
    obtain ⟨good,hc,hg⟩ := hgood a
    refine ⟨good,hc,?_⟩
    intro s hs i
    rw [real_inner_comm,vector_inner,vector_norm]
    exact hg s hs i
  simpa only [vector_norm] using GradientBudget.total_gradient u β (fun a => vector (base a))
    (fun s a => vector (D s a-base a)) hδ hvec hg hβ
    (by intro s; simpa only [vector_norm] using he s) hS
end
end UniformSparsestCut.GradientCalculus

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.ContractionCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ContractionCore
open MeasureTheory Set Filter
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m N S : ℕ} {A : Type u1} [Fintype A]
local notation "E" => EuclideanSpace ℝ (Fin (m+1))

lemma chart_mismatch (u : Fin S → Fin N → E) (hu : ∀ s i, u s i 0≠0)
    {τ lam R : ℝ} (hτ : 0<τ) (hlam : 0<lam) (hlam1 : lam<1) (hn : ∀ s i, ‖u s i‖≤2)
    (F : RoundedCharts.Vertex u τ → A → ℝ) {M : ℝ} (hM : 0≤M) (hbound : ∀ v a, |F v a|≤M)
    (hclose : ∀ s t x (hx : x∈RoundedCharts.cube 2)
      (hs : RoundedCharts.regular (u s) τ x) (ht : RoundedCharts.regular (u t) τ x),
      ∑ a, |F (vertex u τ s x hx hs) a-F (vertex u τ t x hx ht) a|≤R)
    (s t : Fin S) (x : E) (hx : ∀ j, |x j|≤1) :
    (∑ a, ‖fderiv ℝ (ConvolutionBounds.smooth (KernelGeometry.κ lam) (ConcreteCells.function u hu τ F s a) volume) x-
      fderiv ℝ (ConvolutionBounds.smooth (KernelGeometry.κ lam) (ConcreteCells.function u hu τ F t a) volume) x‖)≤
      (m+1:ℕ)*R*KernelGeometry.L lam := by
  apply GradientCalculus.gradient_mismatch (KernelGeometry.compact hlam)
    ((KernelGeometry.smooth lam).of_le (by simp)) _ _
    (fun a => ConcreteCells.function_integrable u hu τ F hM hbound s a)
    (fun a => ConcreteCells.function_integrable u hu τ F hM hbound t a) x
    (KernelGeometry.partial_integrable hlam) (KernelGeometry.partial_integral hlam)
  filter_upwards [ConcreteCells.regular_sub (u s) (hu s) τ x,
      ConcreteCells.regular_sub (u t) (hu t) τ x] with z hzs hzt
  rintro ⟨j,hj⟩
  have hmem : x-z∈RoundedCharts.cube 2 := KernelGeometry.derivative_shifted_mem hlam hlam1 x hx hj
  simp_rw [ConcreteCells.function_eq u hu hτ hn F s (x-z) hmem hzs,
    ConcreteCells.function_eq u hu hτ hn F t (x-z) hmem hzt]
  exact hclose s t (x-z) hmem hzs hzt

lemma smoothing_error (u : Fin S → Fin N → E) (hu : ∀ s i, u s i 0≠0)
    {τ lam G R : ℝ} (hτ : 0<τ) (hlam : 0<lam) (hlam1 : lam<1) (hn : ∀ s i, ‖u s i‖≤2) (hG : 0≤G)
    (F : RoundedCharts.Vertex u τ → A → ℝ) {M : ℝ} (hM : 0≤M) (hbound : ∀ v a, |F v a|≤M)
    (hmacro : ∀ s x y (hx : x∈RoundedCharts.cube 2) (hy : y∈RoundedCharts.cube 2)
      (hs : RoundedCharts.regular (u s) τ x) (ht : RoundedCharts.regular (u s) τ y),
      ∑ a, |F (vertex u τ s x hx hs) a-F (vertex u τ s y hy ht) a|≤G*‖x-y‖+R)
    (s : Fin S) (x : E) (hx : ∀ j, |x j|≤1) (hr : RoundedCharts.regular (u s) τ x) :
    (∑ a, |ConvolutionBounds.smooth (KernelGeometry.κ lam) (ConcreteCells.function u hu τ F s a) volume x-
      ConcreteCells.function u hu τ F s a x|)≤G*(lam*Real.sqrt (m+1:ℕ))+R := by
  apply ConvolutionBounds.error (KernelGeometry.compact hlam) (KernelGeometry.smooth lam).continuous
    (KernelGeometry.integrable hlam) (KernelGeometry.nonneg hlam.le) (KernelGeometry.integral_one hlam)
    _ (fun a => ConcreteCells.function_integrable u hu τ F hM hbound s a) x
  filter_upwards [ConcreteCells.regular_sub (u s) (hu s) τ x] with z hzr hz
  have hxU : x∈RoundedCharts.cube 2 := fun j => (hx j).trans_lt (by norm_num)
  have hmem : x-z∈RoundedCharts.cube 2 := KernelGeometry.shifted_mem hlam hlam1 x hx (subset_closure hz)
  simp_rw [ConcreteCells.function_eq u hu hτ hn F s (x-z) hmem hzr,
    ConcreteCells.function_eq u hu hτ hn F s x hxU hr]
  have h := hmacro s (x-z) x hmem hxU hzr hr
  have hnz : ‖x-z-x‖=‖z‖ := by rw [sub_sub_cancel_left,norm_neg]
  rw [hnz] at h
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left (KernelGeometry.norm_bound hlam hz) hG) le_rfl)

lemma gradient_bound (u : Fin S → Fin N → E) (hu : ∀ s i, u s i 0≠0)
    (hnp : ∀ s i j, i≠j → ∀ t : ℝ, u s i≠t • u s j) (hn : ∀ s i, ‖u s i‖≤2)
    {τ lam δ R J : ℝ} (hτ : 0<τ) (hlam : 0<lam) (hlam1 : lam<1) (hδ : 0≤δ) (hJ : 0≤J)
    (F : RoundedCharts.Vertex u τ → A → ℝ) {M : ℝ} (hM : 0≤M) (hbound : ∀ v a, |F v a|≤M)
    (hclose : ∀ s t x (hx : x∈RoundedCharts.cube 2)
      (hs : RoundedCharts.regular (u s) τ x) (ht : RoundedCharts.regular (u t) τ x),
      ∑ a, |F (vertex u τ s x hx hs) a-F (vertex u τ t x hx ht) a|≤R)
    (hjump : ∀ (vp vm : RoundedCharts.Vertex u τ) (i : Fin N), vp.val.1=vm.val.1 →
      vp.val.2 i=vm.val.2 i+1 → (∀ j, j≠i → vp.val.2 j=vm.val.2 j) → ∑ a, |F vp a-F vm a|≤J)
    (hsmall : ∀ s i, τ/|u s i 0| *KernelGeometry.L lam≤1)
    (hgood : ∀ D : StrongDual ℝ E, ∃ good : Finset (Fin S), (S:ℝ)/2≤good.card ∧
      ∀ s∈good, ∀ i, |D (u s i)|≤δ*‖D‖)
    (s0 : Fin S) (x : E) (hx : ∀ j, |x j|≤1) :
    (∑ a, ‖fderiv ℝ (ConvolutionBounds.smooth (KernelGeometry.κ lam) (ConcreteCells.function u hu τ F s0 a) volume) x‖)≤
      2*(δ*((N:ℝ)*(2*J/τ))+(m+1:ℕ)*R*KernelGeometry.L lam) := by
  classical
  have hex (s : Fin S) := ConcreteCells.normal_coefficients u hu hnp hn hτ hlam hlam1 F hM hJ hbound hjump hsmall s x hx
  choose β hβd hβ using hex
  let D (s : Fin S) (a : A) : StrongDual ℝ E :=
    fderiv ℝ (ConvolutionBounds.smooth (KernelGeometry.κ lam) (ConcreteCells.function u hu τ F s a) volume) x
  apply GradientCalculus.gradient_budget u β D (D s0) hδ
  · intro s a
    exact (hβd s a).fderiv
  · intro a
    simpa only [Fintype.card_fin] using hgood (D s0 a)
  · intro s
    calc
      _ ≤ ∑ _i : Fin N, 2*J/τ := Finset.sum_le_sum (fun i _ => hβ s i)
      _ = _ := by simp
  · intro s
    exact chart_mismatch u hu hτ hlam hlam1 hn F hM hbound hclose s s0 x hx
  · simpa only [Fintype.card_fin] using Nat.zero_lt_of_lt s0.isLt

end
end UniformSparsestCut.ContractionCore

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
local notation "E" => EuclideanSpace ℝ (Fin m)

instance cube_probability : IsProbabilityMeasure (cube (m := m)) := by
  unfold cube
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma cube_first_moment (h : E → ℝ) (hh : ContDiff ℝ 1 h) :
    (∫ z : E × E, |h z.1-h z.2| ∂((cube (m := m)).prod cube)) ≤
      (Real.pi/2)*(∫ x : E, ‖fderiv ℝ h x‖ ∂cube) :=
  uniform_cube_first_moment h hh

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

lemma bounded_integrable {f : E → ℝ} (hf : AEStronglyMeasurable f μ) {B : ℝ}
    (hb : ∀ᵐ x ∂μ, |f x|≤B) : Integrable f μ :=
  (integrable_const B).mono' hf (by simpa only [Real.norm_eq_abs] using hb)

end
end UniformSparsestCut.CubeGeometry

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.CubeTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.CubeTransfer
open MeasureTheory Set Filter
open scoped BigOperators
noncomputable section
variable {m : ℕ} {A : Type u1} [Fintype A]
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "μ" => CubePoincare.cube (m := m)
lemma continuous_integrable (f : E → ℝ) (hf : Continuous f) : Integrable f μ := by
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0:E) (Real.sqrt m)).exists_bound_of_continuousOn hf.continuousOn
  apply CubeGeometry.bounded_integrable hf.aestronglyMeasurable
  filter_upwards [CubeGeometry.cube_norm (m := m)] with x hx
  simpa only [Real.norm_eq_abs] using hB x (by simpa using hx)
lemma pair_continuous_integrable (f : E × E → ℝ) (hf : Continuous f) : Integrable f ((μ).prod μ) := by
  let K : Set E := Metric.closedBall 0 (Real.sqrt m)
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨B,hB⟩ := (hK.prod hK).exists_bound_of_continuousOn hf.continuousOn
  have hm : ∀ᵐ x : E ∂μ, x∈K := by simpa only [K,Metric.mem_closedBall,dist_zero_right] using CubeGeometry.cube_norm (m := m)
  have hp : ∀ᵐ z : E × E ∂(μ).prod μ, z∈K ×ˢ K := by
    apply (Measure.ae_prod_iff_ae_ae (hK.measurableSet.prod hK.measurableSet)).mpr
    filter_upwards [hm] with x hx
    filter_upwards [hm] with y hy
    exact ⟨hx,hy⟩
  apply (integrable_const B).mono' hf.aestronglyMeasurable
  filter_upwards [hp] with z hz
  exact hB z hz

lemma average_from_gradient (f H : A → E → ℝ) {M B K : ℝ}
    (hf : ∀ a, Measurable (f a)) (hM : ∀ a x, |f a x|≤M)
    (hH : ∀ a, ContDiff ℝ 1 (H a))
    (he : ∀ᵐ x : E ∂μ, ∑ a, |H a x-f a x|≤B)
    (hg : ∀ᵐ x : E ∂μ, ∑ a, ‖fderiv ℝ (H a) x‖≤K) :
    (∫ z : E × E, ∑ a, |f a z.1-f a z.2| ∂(μ).prod μ)≤2*B+(Real.pi/2)*K := by
  classical
  have hfi (a : A) : Integrable (f a) μ :=
    CubeGeometry.bounded_integrable (hf a).aestronglyMeasurable (Eventually.of_forall (hM a))
  have hfdi (a : A) : Integrable (fun z : E × E => |f a z.1-f a z.2|) ((μ).prod μ) :=
    ((hfi a).comp_fst μ |>.sub ((hfi a).comp_snd μ)).abs
  have hHd (a : A) : Integrable (fun z : E × E => |H a z.1-H a z.2|) ((μ).prod μ) :=
    pair_continuous_integrable _ (by have hh := (hH a).continuous; fun_prop)
  have hDi (a : A) : Integrable (fun x : E => ‖fderiv ℝ (H a) x‖) μ :=
    continuous_integrable _ (by exact ((hH a).continuous_fderiv (by norm_num)).norm)
  have hgb : (∫ z : E × E, ∑ a, |H a z.1-H a z.2| ∂(μ).prod μ)≤(Real.pi/2)*K := by
    rw [integral_finsetSum _ (fun a _ => hHd a)]
    calc
      _ ≤ ∑ a, (Real.pi/2)*(∫ x : E, ‖fderiv ℝ (H a) x‖ ∂μ) :=
        Finset.sum_le_sum (fun a _ => CubePoincare.cube_first_moment (H a) (hH a))
      _ = (Real.pi/2)*(∫ x : E, ∑ a, ‖fderiv ℝ (H a) x‖ ∂μ) := by
        rw [integral_finsetSum _ (fun a _ => hDi a),Finset.mul_sum]
      _ ≤ (Real.pi/2)*K := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          _ ≤ ∫ _x : E, K ∂μ := integral_mono_ae (integrable_finsetSum _ (fun a _ => hDi a)) (integrable_const K) hg
          _ = _ := by simp
  have hep : ∀ᵐ z : E × E ∂(μ).prod μ,
      (∑ a, |H a z.1-f a z.1|≤B) ∧ (∑ a, |H a z.2-f a z.2|≤B) := by
    have hem : Measurable (fun x : E => ∑ a, |H a x-f a x|) :=
      Finset.measurable_sum _ (fun a _ => ((hH a).continuous.measurable.sub (hf a)).abs)
    apply (Measure.ae_prod_iff_ae_ae
      ((measurableSet_le (hem.comp measurable_fst) measurable_const).inter
        (measurableSet_le (hem.comp measurable_snd) measurable_const))).mpr
    filter_upwards [he] with x hx
    filter_upwards [he] with y hy
    exact ⟨hx,hy⟩
  have hpoint : ∀ᵐ z : E × E ∂(μ).prod μ, (∑ a, |f a z.1-f a z.2|)≤2*B+∑ a, |H a z.1-H a z.2| := by
    filter_upwards [hep] with z hz
    have hle (a : A) : |f a z.1-f a z.2|≤|H a z.1-f a z.1|+|H a z.1-H a z.2|+|H a z.2-f a z.2| := by
      calc
        _ = |-(H a z.1-f a z.1)+(H a z.1-H a z.2)+(H a z.2-f a z.2)| := by congr 1; ring
        _ ≤ _ := by simpa only [abs_neg] using (abs_add_three (-(H a z.1-f a z.1)) (H a z.1-H a z.2) (H a z.2-f a z.2))
    have hh := Finset.sum_le_sum (fun a (_ : a∈(Finset.univ : Finset A)) => hle a)
    simp only [Finset.sum_add_distrib] at hh
    linarith [hz.1,hz.2]
  have hfinal := integral_mono_ae (integrable_finsetSum _ (fun a _ => hfdi a))
    ((integrable_const (2*B)).add (integrable_finsetSum _ (fun a _ => hHd a))) hpoint
  simp only [Pi.add_apply] at hfinal
  have hadd := integral_add (show Integrable (fun _ : E × E => 2*B) ((μ).prod μ) from integrable_const _)
    (integrable_finsetSum Finset.univ (fun a _ => hHd a))
  rw [hadd] at hfinal
  simpa using hfinal.trans (add_le_add le_rfl hgb)
end
end UniformSparsestCut.CubeTransfer

namespace UniformSparsestCut.ContractionAverage
open MeasureTheory Set Filter
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m N S : ℕ} {A : Type u2} [Fintype A]
local notation "E" => EuclideanSpace ℝ (Fin (m+1))
local notation "μ" => CubePoincare.cube (m := m+1)
open ContractionCore

lemma average (u : Fin S → Fin N → E) (hu : ∀ s i, u s i 0≠0)
    (hnp : ∀ s i j, i≠j → ∀ t : ℝ, u s i≠t • u s j) (hn : ∀ s i, ‖u s i‖≤2)
    {τ lam δ R J G : ℝ} (hτ : 0<τ) (hlam : 0<lam) (hlam1 : lam<1)
    (hδ : 0≤δ) (hJ : 0≤J) (hG : 0≤G)
    (F : RoundedCharts.Vertex u τ → A → ℝ) {M : ℝ} (hM : 0≤M) (hbound : ∀ v a, |F v a|≤M)
    (hclose : ∀ s t x (hx : x∈RoundedCharts.cube 2)
      (hs : RoundedCharts.regular (u s) τ x) (ht : RoundedCharts.regular (u t) τ x),
      ∑ a, |F (vertex u τ s x hx hs) a-F (vertex u τ t x hx ht) a|≤R)
    (hmacro : ∀ s x y (hx : x∈RoundedCharts.cube 2) (hy : y∈RoundedCharts.cube 2)
      (hs : RoundedCharts.regular (u s) τ x) (ht : RoundedCharts.regular (u s) τ y),
      ∑ a, |F (vertex u τ s x hx hs) a-F (vertex u τ s y hy ht) a|≤G*‖x-y‖+R)
    (hjump : ∀ (vp vm : RoundedCharts.Vertex u τ) (i : Fin N), vp.val.1=vm.val.1 →
      vp.val.2 i=vm.val.2 i+1 → (∀ j, j≠i → vp.val.2 j=vm.val.2 j) → ∑ a, |F vp a-F vm a|≤J)
    (hsmall : ∀ s i, τ/|u s i 0| *KernelGeometry.L lam≤1)
    (hgood : ∀ D : StrongDual ℝ E, ∃ good : Finset (Fin S), (S:ℝ)/2≤good.card ∧
      ∀ s∈good, ∀ i, |D (u s i)|≤δ*‖D‖)
    (s0 : Fin S) :
    (∫ z : E × E, ∑ a, |ConcreteCells.function u hu τ F s0 a z.1-
        ConcreteCells.function u hu τ F s0 a z.2| ∂(μ).prod μ)≤
      2*(G*(lam*Real.sqrt (m+1:ℕ))+R)+Real.pi*(δ*((N:ℝ)*(2*J/τ))+(m+1:ℕ)*R*KernelGeometry.L lam) := by
  let f : A → E → ℝ := ConcreteCells.function u hu τ F s0
  let H : A → E → ℝ := fun a => ConvolutionBounds.smooth (KernelGeometry.κ lam) (f a) volume
  have hc (a : A) : ContDiff ℝ 1 (H a) := by
    exact (KernelGeometry.compact hlam).contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ)
      ((KernelGeometry.smooth lam).of_le (by simp)) (ConcreteCells.function_integrable u hu τ F hM hbound s0 a)
  have he : ∀ᵐ x : E ∂μ, (∑ a, |H a x-f a x|)≤G*(lam*Real.sqrt (m+1:ℕ))+R := by
    have hr := CubeGeometry.cube_ac.ae_le (RoundedCharts.ae_regular (u s0) τ (by
      intro i h; exact hu s0 i (by rw [h]; rfl)))
    filter_upwards [CubeGeometry.cube_mem (m := m+1),hr] with x hx hrx
    exact smoothing_error u hu hτ hlam hlam1 hn hG F hM hbound hmacro s0 x (fun j => (hx j).le) hrx
  have hg : ∀ᵐ x : E ∂μ, (∑ a, ‖fderiv ℝ (H a) x‖)≤
      2*(δ*((N:ℝ)*(2*J/τ))+(m+1:ℕ)*R*KernelGeometry.L lam) := by
    filter_upwards [CubeGeometry.cube_mem (m := m+1)] with x hx
    exact gradient_bound u hu hnp hn hτ hlam hlam1 hδ hJ F hM hbound hclose hjump hsmall hgood s0 x (fun j => (hx j).le)
  have h := CubeTransfer.average_from_gradient f H (fun a => ConcreteCells.function_measurable u hu τ F s0 a)
    (fun a x => ConcreteCells.function_bounded u hu τ F hM hbound s0 a x) hc he hg
  convert h using 1 ; ring
end
end UniformSparsestCut.ContractionAverage

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.ContractionAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceContraction
open MeasureTheory
open scoped BigOperators RealInnerProductSpace
open SourceParameters SourceCharts SourceMetric
noncomputable section
variable {m : ℕ}
local notation "d" => (m+1:ℕ)
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "μ" => (CubePoincare.cube (m:=d))
lemma integral_bound_oai (f : PivotFamily.PFamily d) (hm : 3000 ≤ d) (hl : 1≤Real.log d) (hH : H ≤ d)
    (Z : V f → EuclideanSpace ℝ (V f))
    (hmac : ∀ v w, |‖Z v-Z w‖^2-KernelApprox.cstar*Real.sqrt d*
         ‖B f (NeZero.pos d) v.val.1 (RoundedCharts.coordinate (u f) (p d 2000) v)-
           B f (NeZero.pos d) w.val.1 (RoundedCharts.coordinate (u f) (p d 2000) w)‖|≤err (m:=d)+8*p d 8)
    (hlocal : ∀ v w, v.val.1=w.val.1 → (∑ i, |RoundedCharts.coordinate (u f) (p d 2000) v i-
        RoundedCharts.coordinate (u f) (p d 2000) w i|)=p d 2000 →
        ‖Z v-Z w‖^2≤50000000*p d 2000*p d 5*(Real.log d)^2)
    {A : Type u1} [Fintype A] (F : V f → A → ℝ)
    (hcon : ∀ v w, (∑ a, |F v a-F w a|)≤‖Z v-Z w‖^2)
    (s0 : Fin (d^3)) :
    (∫ z : E × E, ∑ a, |ConcreteCells.function (u f) (fun s i =>
        abs_pos.mp ((show 0<1/((d:ℝ)^30*Real.sqrt d) by positivity).trans
          (u_pivot f (Nat.succ_pos m) s i 0))) (p d 2000) F s0 a z.1-
        ConcreteCells.function (u f) (fun s i =>
        abs_pos.mp ((show 0<1/((d:ℝ)^30*Real.sqrt d) by positivity).trans
          (u_pivot f (Nat.succ_pos m) s i 0))) (p d 2000) F s0 a z.2| ∂(μ).prod μ)≤C*weight d := by
  classical
  have hm0 := Nat.succ_pos m
  have hm1 : 1 ≤ d := by omega
  have hx : (1:ℝ) ≤ d := by exact_mod_cast hm1
  have hx0 : (0:ℝ)<d := by exact_mod_cast hm0
  have hu0 : ∀ s i, u f s i 0≠0 := by
    intro s i h
    have hh := u_pivot f hm0 s i 0
    rw [h,abs_zero] at hh
    have hp : 0<1/((d:ℝ)^30*Real.sqrt d) := by positivity
    linarith
  have hτ := p_pos hx0 2000
  have hlam := p_pos hx0 2
  have hlam1 : p d 2<1 := by
    unfold p
    apply (div_lt_one (by positivity)).mpr
    have hh : (2:ℝ) ≤ d := by exact_mod_cast (show 2 ≤ d by omega)
    nlinarith only [hh]
  let M : ℝ := ∑ v : V f, ∑ a, |F v a|
  have hM : 0≤M := Finset.sum_nonneg (fun v _ => Finset.sum_nonneg (fun a _ => abs_nonneg _))
  have hbound (v : V f) (a : A) : |F v a|≤M := by
    exact (Finset.single_le_sum (fun a _ => abs_nonneg (F v a)) (Finset.mem_univ a)).trans
      (Finset.single_le_sum (fun v _ => Finset.sum_nonneg (fun a _ => abs_nonneg (F v a))) (Finset.mem_univ v))
  have hclose : ∀ s t x (hx : x∈RoundedCharts.cube 2)
      (hs : RoundedCharts.regular (u f s) (p d 2000) x) (ht : RoundedCharts.regular (u f t) (p d 2000) x),
      (∑ a, |F (ContractionCore.vertex (u f) (p d 2000) s x hx hs) a-
        F (ContractionCore.vertex (u f) (p d 2000) t x hx ht) a|)≤C₀*p d 8 := by
    intro s t x hx hs ht
    have hh := (abs_le.mp (macro_bound f hm Z hmac s t x x hx hx hs ht)).2
    simp only [sub_self,norm_zero,mul_zero,sub_zero] at hh
    exact (hcon _ _).trans hh
  have hmacro : ∀ s x y (hx : x∈RoundedCharts.cube 2) (hy : y∈RoundedCharts.cube 2)
      (hs : RoundedCharts.regular (u f s) (p d 2000) x) (ht : RoundedCharts.regular (u f s) (p d 2000) y),
      (∑ a, |F (ContractionCore.vertex (u f) (p d 2000) s x hx hs) a-
        F (ContractionCore.vertex (u f) (p d 2000) s y hy ht) a|)≤KernelApprox.cstar*Real.sqrt d*‖x-y‖+C₀*p d 8 := by
    intro s x y hx hy hs ht
    have hh := (abs_le.mp (macro_bound f hm Z hmac s s x y hx hy hs ht)).2
    exact (hcon _ _).trans (by simpa only [ContractionCore.vertex,SourceMetric.vertex,add_comm] using (sub_le_iff_le_add.mp hh))
  have hjump : ∀ (vp vm : V f) (i : Fin (d^6)), vp.val.1=vm.val.1 → vp.val.2 i=vm.val.2 i+1 →
      (∀ j, j≠i → vp.val.2 j=vm.val.2 j) → (∑ a, |F vp a-F vm a|)≤50000000*p d 2000*p d 5*(Real.log d)^2 := by
    intro vp vm i hc hi hj
    exact (hcon vp vm).trans (hlocal vp vm hc (one_step f vp vm i hi hj))
  have h := ContractionAverage.average (u f) hu0 (u_nonparallel f hm0) (fun s i => (u_norm f hm0 s i).2)
    hτ hlam hlam1 (by positivity : 0≤11*Real.sqrt (Real.log d)/Real.sqrt d)
    (by unfold p; positivity : 0≤50000000*p d 2000*p d 5*(Real.log d)^2)
    (mul_nonneg KernelApprox.cstar_pos.le (Real.sqrt_nonneg _))
    F hM hbound hclose hmacro hjump (fun s i => small f hm1 hH s i 0) (good_dual f hm0) s0
  exact h.trans (contraction_numeric hm1 hl)
end
end UniformSparsestCut.SourceContraction

end

end OAI
end

theorem solution.{u1} : type_of% @OAI.UniformSparsestCut.SourceContraction.integral_bound_oai.{u1} := @OAI.UniformSparsestCut.SourceContraction.integral_bound_oai.{u1}
