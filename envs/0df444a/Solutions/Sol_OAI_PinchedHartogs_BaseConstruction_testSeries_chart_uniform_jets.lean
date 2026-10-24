-- Prove2me | solution 1 for OAI.PinchedHartogs.BaseConstruction.testSeries_chart_uniform_jets
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:07:04.908834+00:00
-- url     : https://prove2.me/submissions/6320e5c8-2f96-4e11-8f75-49d609547cdc

import Mathlib
import Definitions.Def_PinchedKahler
import Definitions.Def_OAIQWPH000
import Definitions.Def_OAIQWPH001
import Theorems.Thm_OAI_PinchedHartogs_BaseConstruction_analytic_jet_bound

section
-- module Solutions.OAIQW_PinchedHartogs.Compat
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
-- module Solutions.OAIQW_PinchedHartogs.HartogsCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

lemma centeredChart_norm_identity {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) (z : Base) (hd : 1 + (r : ℂ) * z 0 ≠ 0) :
    1 - ‖centeredChart r U z‖ ^ 2 =
      (1-r^2) * (1-‖z‖^2) / ‖1 + (r : ℂ) * z 0‖^2 := by
  have hsq : (Real.sqrt (1-r^2))^2 = 1-r^2 := Real.sq_sqrt (by nlinarith)
  have hdn : ‖1 + (r : ℂ) * z 0‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hd)
  simp only [centeredChart, LinearIsometryEquiv.norm_map, EuclideanSpace.norm_sq_eq,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    div_pow, mul_pow, sq_abs, hsq]
  field_simp [hdn]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
  ring

lemma centeredChart_den_ne_zero {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {z : Base} (hz : z ∈ ball) : 1 + (r : ℂ) * z 0 ≠ 0 := by
  have hz0 := PiLp.norm_apply_le (p := (2 : ENNReal)) z 0
  have hnz : ‖z‖ < 1 := hz
  have hm : ‖(r : ℂ) * z 0‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    have := norm_nonneg (z 0)
    nlinarith
  intro he
  have hh : (r : ℂ) * z 0 = -1 := by linear_combination he
  rw [hh] at hm
  norm_num at hm

lemma centeredChart_mapsTo {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) : MapsTo (centeredChart r U) ball ball := by
  intro z hz
  have hd := centeredChart_den_ne_zero hr hr1 hz
  have he := centeredChart_norm_identity hr hr1 U z hd
  have hpos : 0 < (1-r^2) * (1-‖z‖^2) / ‖1 + (r : ℂ)*z 0‖^2 := by
    apply div_pos
    · apply mul_pos <;> have hn : ‖z‖ < 1 := hz <;> nlinarith [norm_nonneg z]
    · exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hd)
  change ‖centeredChart r U z‖ < 1
  nlinarith [norm_nonneg (centeredChart r U z)]

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseLogTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ComplexOrder
namespace PinchedHartogs
namespace BaseConstruction

lemma bracket_analytic (p : Base) : AnalyticOnNhd ℂ (fun z => bracket z p) univ :=
  fun z _ => (innerSL ℂ p).analyticAt z

lemma peakPolynomial_analytic (P : Finset Sphere) (k : ℕ) :
    AnalyticOnNhd ℂ (peakPolynomial P k) univ := by
  intro z hz
  apply Finset.analyticAt_fun_sum
  intro p hp
  exact (bracket_analytic p z (mem_univ _)).pow k

lemma regularizedLog_eq (a ε : ℝ) (v : ℂ) (hε : ε ≠ 0) :
    regularizedLog a ε v = Real.log (‖1-(a:ℂ)*v‖^2+ε^2)-Real.log (1+ε^2) := by
  apply Real.log_div <;> positivity

lemma regularizedLog_contDiff (a : ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ ∞ (regularizedLog a ε) := by
  have hn : ContDiff ℝ ∞ (fun v : ℂ => ‖1-(a:ℂ)*v‖^2+ε^2) :=
    ((contDiff_norm_sq ℂ).comp (contDiff_const.sub (contDiff_const.mul contDiff_id))).add contDiff_const
  have hh : ContDiff ℝ ∞ (fun v : ℂ => Real.log (‖1-(a:ℂ)*v‖^2+ε^2)-Real.log (1+ε^2)) :=
    (hn.log (fun v => by positivity)).sub contDiff_const
  have he : regularizedLog a ε = (fun v : ℂ => Real.log (‖1-(a:ℂ)*v‖^2+ε^2)-Real.log (1+ε^2)) :=
    funext (fun v => regularizedLog_eq a ε v hε)
  rw [he]
  exact hh

lemma logarithmicTest_contDiff (a : ℝ) {ε : ℝ} (hε : ε ≠ 0) (P : Finset Sphere) (k : ℕ) :
    ContDiff ℝ ∞ (logarithmicTest a ε P k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact (regularizedLog_contDiff a hε).contDiffAt.comp z
    (((peakPolynomial_analytic P k) z (mem_univ _)).contDiffAt.restrict_scalars ℝ)

lemma peakPolynomial_zero (P : Finset Sphere) {k : ℕ} (hk : k ≠ 0) :
    peakPolynomial P k 0 = 0 := by simp [peakPolynomial,bracket,hk]

lemma peakPolynomial_homogeneous (P : Finset Sphere) (k : ℕ) (c : ℂ) (z : Base) :
    peakPolynomial P k (c • z) = c^k * peakPolynomial P k z := by
  simp only [peakPolynomial,bracket, inner_smul_right,mul_pow,Finset.mul_sum]

lemma regularizedLog_lipschitz_bound (a : ℝ) {ε : ℝ} (hε : ε ≠ 0) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℂ, ‖v‖ ≤ A → |regularizedLog a ε v| ≤ C*‖v‖ := by
  have hs := regularizedLog_contDiff a hε
  have hc : Continuous (fderiv ℝ (regularizedLog a ε)) := hs.continuous_fderiv (by norm_num)
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:ℂ) A).bddAbove_image hc.norm.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro v hv
  have hbound : ∀ x ∈ Metric.closedBall (0:ℂ) A, ‖fderiv ℝ (regularizedLog a ε) x‖ ≤ max C 0 := by
    intro x hx
    exact (hC (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  have hm := (convex_closedBall (0:ℂ) A).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hs.differentiable (by norm_num) x) hbound
    (show (0:ℂ) ∈ Metric.closedBall 0 A by simpa using hA)
    (show v ∈ Metric.closedBall 0 A by simpa using hv)
  simpa [Real.norm_eq_abs] using hm

end BaseConstruction
end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseCauchyJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler8342_1 uKahler8342_2 uKahler8392_1 uKahler8392_2

open scoped ContDiff
open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open Set Filter Topology MeasureTheory
open scoped ContDiff ComplexOrder
noncomputable section

open Set Filter Topology
namespace PinchedHartogs.BaseConstruction

lemma cauchyJetConstant_pos (n : ℕ) : 0 < cauchyJetConstant n := by
  induction n with
  | zero => norm_num [cauchyJetConstant]
  | succ n ih => simp only [cauchyJetConstant]; positivity

lemma analytic_positive_jet_bound {E : Type uKahler8392_1} {F : Type uKahler8392_2} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {c : E} {R A : ℝ} (hR : 0 < R) (hA : 0 ≤ A)
    (hf : AnalyticOnNhd ℂ f (Metric.ball c R))
    (hb : ∀ x ∈ Metric.ball c R, ‖f x-f c‖ ≤ A) {n : ℕ} (hn : 0 < n) :
    ‖iteratedFDeriv ℂ n f c‖ ≤ cauchyJetConstant n*A/(R/2)^n := by
  have hs : AnalyticOnNhd ℂ (fun x => f x-f c) (Metric.ball c R) := hf.sub analyticOnNhd_const
  have hh := analytic_jet_bound (by linarith : R/2<R) (by positivity : 0 ≤ R/2) hA hs hb n c
    (Metric.mem_ball_self (by positivity : 0 < R/2))
  have he : iteratedFDeriv ℂ n (fun x => f x-f c) c=iteratedFDeriv ℂ n f c := by
    change iteratedFDeriv ℂ n (f - fun _ => f c) c = _
    rw [iteratedFDeriv_sub_apply (hf c (Metric.mem_ball_self hR)).contDiffAt contDiffAt_const,
      iteratedFDeriv_const_of_ne (by omega)]
    simp
  rw [he,show R-R/2=R/2 by ring] at hh
  exact hh

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseCompositionJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler8418_1 uKahler8418_2 uKahler8437_1 uKahler8437_2 uKahler8437_3 uKahler8458_1 uKahler8458_2

open scoped ContDiff
open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open Set Filter Topology MeasureTheory
open scoped ContDiff ComplexOrder
open Set Filter Topology
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma analytic_real_jet_norm {E : Type uKahler8418_1} {F : Type uKahler8418_2} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {x : E} (hf : AnalyticAt ℂ f x) (n : ℕ) :
    ‖iteratedFDeriv ℝ n f x‖=‖iteratedFDeriv ℂ n f x‖ := by
  rw [← (hf.contDiffAt : ContDiffAt ℂ n f x).restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  exact ContinuousMultilinearMap.norm_restrictScalars _

lemma small_power_bound {t B : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hB : 1 ≤ B)
    {i n : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) :
    B*t ≤ (B*t^((n:ℝ)⁻¹))^i := by
  have hn : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  rw [mul_pow,← Real.rpow_mul_natCast ht.le]
  have hex : (n:ℝ)⁻¹*(i:ℝ) ≤ 1 := by
    rw [← div_eq_inv_mul]
    exact (div_le_one hn).mpr (by exact_mod_cast hin)
  have hp : t ≤ t^((n:ℝ)⁻¹*(i:ℝ)) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ht ht1 hex
  exact mul_le_mul (by simpa using pow_le_pow_right₀ hB hi) hp ht.le (by positivity)

lemma norm_composition_jet_linear {E : Type uKahler8437_1} {F : Type uKahler8437_2} {G : Type uKahler8437_3}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : F → G} {s : Set E} (hs : IsOpen s) {x : E} (hx : x ∈ s)
    {n : ℕ} (hn : 1 ≤ n) (hf : ContDiffOn ℝ n f s) (hg : ContDiff ℝ n g)
    {B C t : ℝ} (hB : 1 ≤ B) (ht : 0 < t) (ht1 : t ≤ 1)
    (hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hbound : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ B*t) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ n.factorial*C*B^n*t := by
  have hh := norm_iteratedFDerivWithin_comp_le hg.contDiffOn hf le_rfl uniqueDiffOn_univ
    (hs.uniqueDiffOn) (mapsTo_univ f s) hx
    (C := C) (D := B*t^((n:ℝ)⁻¹))
    (by simpa only [iteratedFDerivWithin_univ] using hC)
    (fun i hi hin => by
      rw [iteratedFDerivWithin_of_isOpen i hs hx]
      exact (hbound i hi hin).trans (small_power_bound ht ht1 hB hi hin))
  rw [iteratedFDerivWithin_of_isOpen n hs hx] at hh
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [mul_pow,← Real.rpow_mul_natCast ht.le,inv_mul_cancel₀ hn0,Real.rpow_one] at hh
  exact hh.trans_eq (by ring)

lemma smooth_jet_bound_compact {E : Type uKahler8458_1} {F : Type uKahler8458_2} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F} (hg : ContDiff ℝ ∞ g)
    {s : Set E} (hs : IsCompact s) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i, i ≤ n → ∀ x ∈ s, ‖iteratedFDeriv ℝ i g x‖ ≤ C := by
  have hex (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ s, ‖iteratedFDeriv ℝ i g x‖ ≤ C := by
    have hc : Continuous (iteratedFDeriv ℝ i g) := ContDiff.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (i:ℕ∞) ≤ ⊤)) hg
    obtain ⟨C,hC⟩ := hs.bddAbove_image hc.norm.continuousOn
    exact ⟨max C 0,le_max_right _ _,fun x hx => (hC (mem_image_of_mem _ hx)).trans (le_max_left _ _)⟩
  choose C hC hbound using hex
  refine ⟨1+∑ j ∈ Finset.range (n+1), C j,?_,?_⟩
  · have := Finset.sum_nonneg (s := Finset.range (n+1)) (fun j _ => hC j)
    linarith
  · intro i hi x hx
    have hh := Finset.single_le_sum (s := Finset.range (n+1)) (fun j _ => hC j) (show i ∈ Finset.range (n+1) by simp; omega)
    exact (hbound i x hx).trans (by linarith)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseLogJetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open Set Filter Topology MeasureTheory
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma regularizedLog_positive_jet_bound (a : ℝ) {ε R A B : ℝ} (he : ε ≠ 0)
    (hR : 0 < R) (hA : 0 ≤ A) (hB : 0 ≤ B) {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Base → ℂ) (c : Base) (t : ℝ),
      AnalyticOnNhd ℂ f (Metric.ball c R) → ‖f c‖ ≤ A → 0 < t → t ≤ 1 →
      (∀ x ∈ Metric.ball c R, ‖f x-f c‖ ≤ B*t) →
      ‖iteratedFDeriv ℝ n (regularizedLog a ε ∘ f) c‖ ≤ C*t := by
  let radius : NNReal := ⟨A, hA⟩
  obtain ⟨C,hC,hCb⟩ := smooth_jet_bound_compact (regularizedLog_contDiff a he)
    (isCompact_closedBall (0:ℂ) (radius : ℝ)) n
  let D : ℝ := 1+∑ i ∈ Finset.range (n+1), cauchyJetConstant i*B/(R/2)^i
  have hterm (i : ℕ) : 0 ≤ cauchyJetConstant i*B/(R/2)^i := by
    exact div_nonneg (mul_nonneg (cauchyJetConstant_pos i).le hB) (by positivity)
  have hD : 1 ≤ D := by
    have hh := Finset.sum_nonneg (s := Finset.range (n+1)) (fun i _ => hterm i)
    dsimp [D]; linarith
  have hDb (i : ℕ) (hi : i ≤ n) : cauchyJetConstant i*B/(R/2)^i ≤ D := by
    have hh := Finset.single_le_sum (s := Finset.range (n+1)) (fun j _ => hterm j)
      (show i ∈ Finset.range (n+1) by simp; omega)
    dsimp [D]; linarith
  refine ⟨n.factorial*C*D^n,by positivity,?_⟩
  intro f c t hf hfc ht ht1 hb
  have hfn : ContDiffOn ℝ n f (Metric.ball c R) := (hf.contDiffOn Metric.isOpen_ball.uniqueDiffOn).restrict_scalars ℝ
  have hh := norm_composition_jet_linear Metric.isOpen_ball (Metric.mem_ball_self hR) hn hfn
    ((regularizedLog_contDiff a he).of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))) hD ht ht1
    (fun i hi => hCb i hi (f c) (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hfc))
    (fun i hi hin => ?_)
  · exact hh
  rw [analytic_real_jet_norm (hf c (Metric.mem_ball_self hR)) i]
  have hbound := analytic_positive_jet_bound hR (mul_nonneg hB ht.le) hf hb (by omega : 0 < i)
  apply hbound.trans
  calc cauchyJetConstant i*(B*t)/(R/2)^i = (cauchyJetConstant i*B/(R/2)^i)*t := by ring
       _ ≤ D*t := mul_le_mul_of_nonneg_right (hDb i hin) ht.le

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler8561_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open Set Filter Topology MeasureTheory
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
namespace PinchedHartogs.BaseConstruction

lemma continuous_integrable {E : Type uKahler8561_1} [NormedAddCommGroup E] {μ : Measure Sphere}
    [IsFiniteMeasure μ] {f : Sphere → E} (hf : Continuous f) : Integrable f μ := by
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseSphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler8786_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma sphereAction_preserves (U : Base ≃ₗᵢ[ℂ] Base) :
    MeasurePreserving (sphereAction U) sigma sigma := by
  have hm : MeasurePreserving (sphereAction U)
      (volume : Measure Base).toSphere (volume : Measure Base).toSphere := by
    refine ⟨(sphereAction U).measurable, ?_⟩
    apply Measure.ext
    intro s hs
    rw [Measure.map_apply (sphereAction U).measurable hs,
      (volume : Measure Base).toSphere_apply' ((sphereAction U).measurable hs),
      (volume : Measure Base).toSphere_apply' hs]
    congr 1
    have he : Ioo (0:ℝ) 1 • ((↑) '' (sphereAction U ⁻¹' s)) =
        U ⁻¹' (Ioo (0:ℝ) 1 • ((↑) '' s)) := by
      ext z
      simp only [mem_preimage, Set.mem_smul, mem_image]
      constructor
      · rintro ⟨r,hr,v,⟨ξ,hξ,rfl⟩,rfl⟩
        exact ⟨r,hr,U (ξ:Base),⟨sphereAction U ξ,hξ,rfl⟩,(realIsometry U).map_smul r ξ |>.symm⟩
      · rintro ⟨r,hr,v,⟨ξ,hξ,rfl⟩,hz⟩
        refine ⟨r,hr,U.symm (ξ:Base),⟨(sphereAction U).symm ξ, ?_, rfl⟩,?_⟩
        · simpa using hξ
        · apply U.injective
          rw [← hz]
          calc
            U (r • U.symm (ξ:Base)) = r • U (U.symm (ξ:Base)) := (realIsometry U).map_smul _ _
            _ = _ := by rw [U.apply_symm_apply]
    rw [he]
    exact (realIsometry U).measurePreserving.measure_preimage_emb
      U.toHomeomorph.measurableEmbedding _
  exact hm.smul_measure _

lemma sigma_integral_unitary {E : Type uKahler8786_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Base ≃ₗᵢ[ℂ] Base) (f : Sphere → E) :
    (∫ ξ, f (sphereAction U ξ) ∂sigma) = ∫ ξ, f ξ ∂sigma :=
  (sphereAction_preserves U).integral_comp (sphereAction U).measurableEmbedding f

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseRadialMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma radialRI (ξ : Sphere) : radialR ξ^2+radialJ ξ^2 = radialU ξ*radialV ξ := by
  simp [radialR,radialJ,radialU,radialV,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,
    Complex.conj_re,Complex.conj_im]
  ring

lemma radialJ_continuous : Continuous radialJ := by
  exact Complex.continuous_im.comp (((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val).mul
    (((EuclideanSpace.proj 1).continuous.comp continuous_subtype_val).star))

lemma radial_phase_square (n : ℕ) :
    (∫ ξ, radialU ξ^n * radialR ξ^2 ∂sigma) =
      ∫ ξ, radialU ξ^n * radialJ ξ^2 ∂sigma := by
  have hi := sigma_integral_unitary (diagIsometry Complex.I 1 (by simp) (by simp))
    (fun ξ => radialU ξ^n * radialR ξ^2)
  have he : ∀ ξ : Sphere,
      radialU (sphereAction (diagIsometry Complex.I 1 (by simp) (by simp)) ξ)^n *
      radialR (sphereAction (diagIsometry Complex.I 1 (by simp) (by simp)) ξ)^2 =
      radialU ξ^n*radialJ ξ^2 := by
    intro ξ
    simp [radialU,radialR,radialJ,Complex.normSq_mul,mul_assoc]
    left
    ring
  simpa only [he] using hi.symm

lemma radial_square_integral (n : ℕ) :
    2*(∫ ξ, radialU ξ^n*radialR ξ^2 ∂sigma) =
      ∫ ξ, radialU ξ^(n+1)*radialV ξ ∂sigma := by
  have hR : Integrable (fun ξ => radialU ξ^n*radialR ξ^2) sigma :=
    continuous_integrable ((radialU_continuous.pow n).mul (radialR_continuous.pow 2))
  have hJ : Integrable (fun ξ => radialU ξ^n*radialJ ξ^2) sigma :=
    continuous_integrable ((radialU_continuous.pow n).mul (radialJ_continuous.pow 2))
  calc
    _ = (∫ ξ, radialU ξ^n*radialR ξ^2 ∂sigma) +
        (∫ ξ, radialU ξ^n*radialJ ξ^2 ∂sigma) := by rw [← radial_phase_square n]; ring
    _ = ∫ ξ, radialU ξ^n*radialR ξ^2 + radialU ξ^n*radialJ ξ^2 ∂sigma :=
      (integral_add hR hJ).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [← mul_add,radialRI,pow_succ]
      ring

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseRadialMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma hasDerivAt_sphere_integral {F F' : ℝ → Sphere → ℝ}
    (hF : Continuous (fun p : ℝ × Sphere => F p.1 p.2))
    (hF' : Continuous (fun p : ℝ × Sphere => F' p.1 p.2))
    (hd : ∀ t ξ, HasDerivAt (fun r => F r ξ) (F' t ξ) t) (t : ℝ) :
    HasDerivAt (fun r => ∫ ξ, F r ξ ∂sigma) (∫ ξ, F' t ξ ∂sigma) t := by
  obtain ⟨C,hC⟩ := ((isCompact_closedBall t 1).prod (isCompact_univ : IsCompact (univ : Set Sphere))).bddAbove_image hF'.norm.continuousOn
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := sigma)
    (F := F) (F' := F') (bound := fun _ => C) (s := Metric.ball t 1)
    (Metric.ball_mem_nhds t (by norm_num)) ?_ ?_ ?_ ?_ (integrable_const C) ?_).2
  · exact Eventually.of_forall (fun r => (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact continuous_integrable (hF.comp (continuous_const.prodMk continuous_id))
  · exact (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [] with ξ r hr
    exact hC (mem_image_of_mem (fun p : ℝ × Sphere => ‖F' p.1 p.2‖)
      (show (r,ξ) ∈ Metric.closedBall t 1 ×ˢ (univ : Set Sphere) from ⟨Metric.ball_subset_closedBall hr,mem_univ _⟩))
  · exact Eventually.of_forall (fun ξ r _ => hd r ξ)

private lemma rotA_deriv (u v r t : ℝ) : HasDerivAt (rotA u v r) (rotA' u v r t) t := by
  convert (((Real.hasDerivAt_cos t).pow 2 |>.mul_const u).add
    ((Real.hasDerivAt_sin t).pow 2 |>.mul_const v)).add
    ((((Real.hasDerivAt_cos t).const_mul 2).mul (Real.hasDerivAt_sin t)).mul_const r) using 1 <;> try rfl
  all_goals
    (try dsimp [rotA,rotA']); ring

private lemma rotA'_deriv (u v r t : ℝ) : HasDerivAt (rotA' u v r) (rotA'' u v r t) t := by
  convert (((((Real.hasDerivAt_cos t).const_mul 2).mul (Real.hasDerivAt_sin t)).mul_const (v-u)).add
    (((((Real.hasDerivAt_cos t).pow 2).sub ((Real.hasDerivAt_sin t).pow 2)).const_mul 2).mul_const r)) using 1 <;> try rfl
  all_goals
    (try dsimp [rotA',rotA'']); ring

private lemma rotated_radialU (t : ℝ) (ξ : Sphere) :
    radialU (sphereAction (rotationIsometry t) ξ) = rotA (radialU ξ) (radialV ξ) (radialR ξ) t := by
  simp only [radialU,radialV,radialR,rotationIsometry,rotA,sphereAction_coe,suIsometry_zero,Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

private lemma rotF_deriv (n : ℕ) (t : ℝ) (ξ : Sphere) :
    HasDerivAt (fun s => rotF n s ξ) (rotF' n t ξ) t := by
  convert (rotA_deriv (radialU ξ) (radialV ξ) (radialR ξ) t).pow (n+2) using 1 <;> try rfl
  all_goals
    (try simp only [rotF',Nat.cast_add,Nat.cast_ofNat]); try rfl

private lemma rotF'_deriv (n : ℕ) (t : ℝ) (ξ : Sphere) :
    HasDerivAt (fun s => rotF' n s ξ) (rotF'' n t ξ) t := by
  convert ((((rotA_deriv (radialU ξ) (radialV ξ) (radialR ξ) t).pow (n+1)).const_mul (n+2:ℝ)).mul
    (rotA'_deriv (radialU ξ) (radialV ξ) (radialR ξ) t)) using 1 <;> try rfl
  all_goals
    (try simp only [rotF'',Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,Pi.pow_apply]); ring

attribute [local fun_prop] radialU_continuous radialV_continuous radialR_continuous

private lemma rotF_continuous (n : ℕ) : Continuous (fun p : ℝ × Sphere => rotF n p.1 p.2) := by
  unfold rotF rotA
  fun_prop
private lemma rotF'_continuous (n : ℕ) : Continuous (fun p : ℝ × Sphere => rotF' n p.1 p.2) := by
  unfold rotF' rotA rotA'
  fun_prop
private lemma rotF''_continuous (n : ℕ) : Continuous (fun p : ℝ × Sphere => rotF'' n p.1 p.2) := by
  unfold rotF'' rotA rotA' rotA''
  fun_prop

lemma radial_moment_recurrence (n : ℕ) :
    (n+3 : ℝ)*(∫ ξ, radialU ξ^(n+2) ∂sigma) =
      (n+2 : ℝ)*(∫ ξ, radialU ξ^(n+1) ∂sigma) := by
  have hconst : ∀ t, (∫ ξ, rotF n t ξ ∂sigma) = ∫ ξ, radialU ξ^(n+2) ∂sigma := by
    intro t
    simpa only [rotated_radialU,rotF] using sigma_integral_unitary (rotationIsometry t)
      (fun ξ => radialU ξ^(n+2))
  have hzero : ∀ t, (∫ ξ, rotF' n t ξ ∂sigma) = 0 := by
    intro t
    have hc : HasDerivAt (fun s => ∫ ξ, rotF n s ξ ∂sigma) 0 t := by
      simpa only [hconst] using hasDerivAt_const t (∫ ξ, radialU ξ^(n+2) ∂sigma)
    exact (hasDerivAt_sphere_integral (rotF_continuous n) (rotF'_continuous n) (rotF_deriv n) t).unique hc
  have hsecond : (∫ ξ, rotF'' n 0 ξ ∂sigma) = 0 := by
    have hc : HasDerivAt (fun s => ∫ ξ, rotF' n s ξ ∂sigma) 0 0 := by
      simpa only [hzero] using hasDerivAt_const (0:ℝ) (0:ℝ)
    exact (hasDerivAt_sphere_integral (rotF'_continuous n) (rotF''_continuous n) (rotF'_deriv n) 0).unique hc
  have he : ∀ ξ : Sphere, rotF'' n 0 ξ = (n+2:ℝ)*
      (4*(n+1:ℝ)*(radialU ξ^n*radialR ξ^2)+
        2*(radialU ξ^(n+1)*radialV ξ)-2*radialU ξ^(n+2)) := by
    intro ξ
    simp only [rotF'',rotA,rotA',rotA'',Real.cos_zero,Real.sin_zero,zero_mul,mul_zero,one_pow,one_mul,add_zero,sub_zero,pow_succ]
    ring
  simp_rw [he] at hsecond
  have hR : Integrable (fun ξ => radialU ξ^n*radialR ξ^2) sigma :=
    continuous_integrable ((radialU_continuous.pow n).mul (radialR_continuous.pow 2))
  have hUV : Integrable (fun ξ => radialU ξ^(n+1)*radialV ξ) sigma :=
    continuous_integrable ((radialU_continuous.pow (n+1)).mul radialV_continuous)
  have hU : Integrable (fun ξ => radialU ξ^(n+2)) sigma := continuous_integrable (radialU_continuous.pow (n+2))
  have hparts := integral_sub (μ := sigma)
    (f := fun ξ => 4*(n+1:ℝ)*(radialU ξ^n*radialR ξ^2)+2*(radialU ξ^(n+1)*radialV ξ))
    (g := fun ξ => 2*radialU ξ^(n+2))
    ((hR.const_mul (4*(n+1:ℝ))).add (hUV.const_mul 2)) (hU.const_mul 2)
  have hparts' := integral_add (μ := sigma)
    (f := fun ξ => 4*(n+1:ℝ)*(radialU ξ^n*radialR ξ^2))
    (g := fun ξ => 2*(radialU ξ^(n+1)*radialV ξ))
    (hR.const_mul (4*(n+1:ℝ))) (hUV.const_mul 2)
  rw [integral_const_mul,hparts,hparts',integral_const_mul,integral_const_mul,integral_const_mul] at hsecond
  have huv : (∫ ξ, radialU ξ^(n+1)*radialV ξ ∂sigma) =
      (∫ ξ, radialU ξ^(n+1) ∂sigma)-(∫ ξ, radialU ξ^(n+2) ∂sigma) := by
    rw [← integral_sub (f := fun ξ => radialU ξ^(n+1)) (g := fun ξ => radialU ξ^(n+2))
      (continuous_integrable (radialU_continuous.pow (n+1))) hU]
    apply integral_congr_ae
    filter_upwards [] with ξ
    have hv : radialV ξ = 1-radialU ξ := by linarith [radialUV ξ]
    rw [hv,show n+2 = (n+1)+1 from rfl,pow_succ]
    ring
  have hs := radial_square_integral n
  rw [huv] at hs hsecond
  have hn : (0:ℝ) < n+2 := by positivity
  have hh := (mul_eq_zero.mp hsecond).resolve_left hn.ne'
  linear_combination (n+1:ℝ)*hs-hh/2

lemma radial_first_moment : (∫ ξ, radialU ξ ∂sigma) = 1/2 := by
  have hi := sigma_integral_unitary (suIsometry 0 1 (by simp)) radialU
  have he : ∀ ξ : Sphere, radialU (sphereAction (suIsometry 0 1 (by simp)) ξ) = radialV ξ := by
    intro ξ
    simp [radialU,radialV]
  simp_rw [he] at hi
  have huv : (∫ ξ, radialU ξ ∂sigma)+(∫ ξ, radialV ξ ∂sigma) = 1 := by
    rw [← integral_add (continuous_integrable radialU_continuous) (continuous_integrable radialV_continuous)]
    simp_rw [radialUV]
    simp
  linarith

lemma radial_moment (n : ℕ) : (∫ ξ, radialU ξ^n ∂sigma) = 1/(n+1:ℝ) := by
  rcases n with _|n
  · simp
  induction n with
  | zero => simpa only [Nat.zero_add,Nat.cast_one,pow_one,show (1:ℝ)+1 = 2 by norm_num] using radial_first_moment
  | succ n ih =>
    have hr := radial_moment_recurrence n
    rw [ih] at hr
    have hn : (n+2:ℝ) ≠ 0 := by positivity
    have hn' : (n+3:ℝ) ≠ 0 := by positivity
    simp only [Nat.cast_add,Nat.cast_one] at *
    field_simp at hr ⊢
    nlinarith

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseRadialLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler9159_1 uKahler9161_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma radialUnit_continuous : Continuous radialUnit := radialU_continuous.subtype_mk _

lemma unit_moment (n : ℕ) : (∫ t : unitInterval, (t:ℝ)^n) = 1/(n+1:ℝ) := by
  rw [unitInterval.volume_def,integral_subtype_comap measurableSet_Icc (fun t : ℝ => t^n)]
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),integral_pow]
  simp

lemma radial_polynomial_integral (p : Polynomial ℝ) :
    (∫ ξ, p.eval (radialU ξ) ∂sigma) = ∫ t : unitInterval, p.eval (t:ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    rw [integral_add,integral_add,hp,hq]
    all_goals first
      | exact continuous_integrable (p.continuous.comp radialU_continuous)
      | exact continuous_integrable (q.continuous.comp radialU_continuous)
      | exact (p.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      | exact (q.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  | monomial n a =>
    simp only [Polynomial.eval_monomial,integral_const_mul,radial_moment,unit_moment]

lemma radial_continuous_integral (f : C(unitInterval,ℝ)) :
    (∫ ξ, f (radialUnit ξ) ∂sigma) = ∫ t : unitInterval, f t := by
  let L := integralCM sigma radialUnit radialUnit_continuous
  let R := integralCM (volume : Measure unitInterval) id continuous_id
  have hc : IsClosed {f : C(unitInterval,ℝ) | L f = R f} := isClosed_eq L.continuous R.continuous
  have hpoly : (polynomialFunctions (Icc (0:ℝ) 1) : Set C(unitInterval,ℝ)) ⊆ {f | L f = R f} := by
    rw [polynomialFunctions_coe]
    rintro _ ⟨p,rfl⟩
    exact radial_polynomial_integral p
  have hcl := hc.closure_subset_iff.mpr hpoly
  have hd : closure (polynomialFunctions (Icc (0:ℝ) 1) : Set C(unitInterval,ℝ)) = univ := by
    simpa only [Subalgebra.topologicalClosure_coe,show ((⊤ : Subalgebra ℝ C(unitInterval,ℝ)) : Set C(unitInterval,ℝ)) = univ from rfl] using
      congrArg (fun A : Subalgebra ℝ C(unitInterval,ℝ) => (A : Set C(unitInterval,ℝ)))
        (polynomialFunctions.topologicalClosure (Icc (0:ℝ) 1))
  exact hcl (by rw [hd]; trivial)

lemma radial_law : Measure.map radialUnit sigma = (volume : Measure unitInterval) := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [integral_map (f := fun x => f x) radialUnit_continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  exact radial_continuous_integral f.toContinuousMap

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma bloch_continuous : Continuous bloch := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact radialU_continuous
  · exact radialR_continuous
  · exact radialJ_continuous

lemma bracket_coordinates (z p : Base) : bracket z p = z 0*star (p 0)+z 1*star (p 1) := by
  simp [bracket,Fin.sum_univ_two,inner]

lemma bracket_radial_identity (ξ p : Sphere) :
    ‖bracket (ξ:Base) (p:Base)‖^2 = radialU ξ*radialU p+radialV ξ*radialV p+
      2*(radialR ξ*radialR p+radialJ ξ*radialJ p) := by
  rw [← Complex.normSq_eq_norm_sq,bracket_coordinates]
  simp only [radialU,radialV,radialR,radialJ,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

lemma bloch_dist_sq (ξ p : Sphere) :
    dist (bloch ξ) (bloch p)^2 = 1-‖bracket (ξ:Base) (p:Base)‖^2 := by
  rw [dist_eq_norm,EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_three,PiLp.sub_apply]
  change |radialU ξ-radialU p|^2+|radialR ξ-radialR p|^2+|radialJ ξ-radialJ p|^2 = _
  simp only [sq_abs]
  rw [bracket_radial_identity]
  have hvξ : radialV ξ = 1-radialU ξ := by linarith [radialUV ξ]
  have hvp : radialV p = 1-radialU p := by linarith [radialUV p]
  have hξ := radialRI ξ
  have hp := radialRI p
  rw [hvξ] at hξ ⊢
  rw [hvp] at hp ⊢
  linarith

lemma projectiveDistance_eq_dist (ξ p : Sphere) : projectiveDistance ξ p = dist (bloch ξ) (bloch p) := by
  rw [projectiveDistance,← bloch_dist_sq,Real.sqrt_sq (dist_nonneg)]

lemma projectiveDistance_triangle (ξ p q : Sphere) :
    projectiveDistance ξ q ≤ projectiveDistance ξ p+projectiveDistance p q := by
  simp only [projectiveDistance_eq_dist]
  exact dist_triangle _ _ _

lemma projectiveDistance_nonneg (ξ p : Sphere) : 0 ≤ projectiveDistance ξ p := Real.sqrt_nonneg _
lemma projectiveDistance_symm (ξ p : Sphere) : projectiveDistance ξ p = projectiveDistance p ξ := by
  simp only [projectiveDistance_eq_dist,dist_comm]

lemma projectiveDistance_continuous (p : Sphere) : Continuous (fun ξ => projectiveDistance ξ p) := by
  simpa only [projectiveDistance_eq_dist] using bloch_continuous.dist continuous_const

lemma projectiveDistance_sq (ξ p : Sphere) : projectiveDistance ξ p^2 = 1-‖bracket (ξ:Base) (p:Base)‖^2 := by
  rw [projectiveDistance_eq_dist,bloch_dist_sq]

lemma adaptedIsometry_zero (p : Sphere) (z : Base) : adaptedIsometry p z 0 = bracket z (p:Base) := by
  simp only [adaptedIsometry,suIsometry_zero,bracket_coordinates]
  ring

lemma adapted_radialU (ξ p : Sphere) : radialU (sphereAction (adaptedIsometry p) ξ) = ‖bracket (ξ:Base) (p:Base)‖^2 := by
  simp only [radialU,sphereAction_coe,adaptedIsometry_zero,Complex.normSq_eq_norm_sq]

lemma projective_cap_measure (p : Sphere) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    sigma {ξ | projectiveDistance ξ p < s} = ENNReal.ofReal (s^2) := by
  let a : unitInterval := ⟨1-s^2,by constructor <;> nlinarith⟩
  have he : {ξ | projectiveDistance ξ p < s} =
      (sphereAction (adaptedIsometry p)) ⁻¹' (radialUnit ⁻¹' Ioi a) := by
    ext ξ
    change projectiveDistance ξ p < s ↔ (a:ℝ) < radialU (sphereAction (adaptedIsometry p) ξ)
    rw [adapted_radialU]
    dsimp [a]
    have hp := projectiveDistance_sq ξ p
    have hnn := projectiveDistance_nonneg ξ p
    constructor <;> intro h <;> nlinarith
  rw [he,(sphereAction_preserves (adaptedIsometry p)).measure_preimage_emb (sphereAction _).measurableEmbedding,
    ← Measure.map_apply radialUnit_continuous.measurable measurableSet_Ioi,radial_law,unitInterval.volume_Ioi]
  congr 1
  dsimp [a]
  ring

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma projectiveCap_measurable (p : Sphere) (s : ℝ) : MeasurableSet (projectiveCap p s) :=
  (projectiveDistance_continuous p).measurable measurableSet_Iio

lemma projectiveCap_real (p : Sphere) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    sigma.real (projectiveCap p s) = s^2 := by
  rw [measureReal_def,projectiveCap,projective_cap_measure p hs hs1,ENNReal.toReal_ofReal (sq_nonneg _)]

lemma separated_caps_disjoint {ρ : ℝ} {P : Finset Sphere} (hP : ProjectivelySeparated ρ P) :
    (P : Set Sphere).PairwiseDisjoint (fun p => projectiveCap p (ρ/2)) := by
  intro p hp q hq hpq
  apply disjoint_left.mpr
  intro ξ hξp hξq
  have ht := projectiveDistance_triangle p ξ q
  rw [projectiveDistance_symm p ξ] at ht
  have hs := hP p hp q hq hpq
  change projectiveDistance ξ p < ρ/2 at hξp
  change projectiveDistance ξ q < ρ/2 at hξq
  linarith

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma separated_local_count {D : ℝ} (hD : 1 ≤ D) {k : ℕ} (hk : 1 ≤ k)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P)
    (ξ : Sphere) {u : ℝ} (hu : 0 ≤ u) :
    ((P.filter (fun p => projectiveDistance ξ p < u/Real.sqrt k)).card : ℝ) ≤ 9*(u+1/3)^2 := by
  classical
  let S := P.filter (fun p => projectiveDistance ξ p < u/Real.sqrt k)
  have hk0 : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hs : 1 ≤ Real.sqrt (k:ℝ) := (Real.one_le_sqrt).mpr (by exact_mod_cast hk)
  have hs0 : 0 < Real.sqrt (k:ℝ) := lt_of_lt_of_le zero_lt_one hs
  let r := 1/(3*Real.sqrt (k:ℝ))
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by dsimp [r]; apply (div_le_one (by positivity)).mpr; linarith
  have hsep : ProjectivelySeparated (2*r) S := by
    intro p hp q hq hpq
    have ht := hP p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1 hpq
    have he : 2*r ≤ D/Real.sqrt (k:ℝ) := by dsimp [r]; field_simp; linarith
    exact he.trans ht
  have hd := separated_caps_disjoint hsep
  have he : 2*r/2 = r := by ring
  rw [he] at hd
  have hm : sigma.real (⋃ p ∈ S, projectiveCap p r) = (S.card:ℝ)*r^2 := by
    rw [measureReal_biUnion_finset hd (fun p _ => projectiveCap_measurable p r)]
    simp only [projectiveCap_real _ hr.le hr1,Finset.sum_const,nsmul_eq_mul]
  have hsmall : (⋃ p ∈ S, projectiveCap p r) ⊆ projectiveCap ξ ((u+1/3)/Real.sqrt (k:ℝ)) := by
    intro η hη
    obtain ⟨p,hp,hηp⟩ := mem_iUnion₂.mp hη
    have hp' := (Finset.mem_filter.mp hp).2
    change projectiveDistance η p < r at hηp
    change projectiveDistance η ξ < _
    have ht := projectiveDistance_triangle η p ξ
    rw [projectiveDistance_symm p ξ] at ht
    dsimp [r] at hηp
    have he : u/Real.sqrt (k:ℝ)+1/(3*Real.sqrt (k:ℝ)) = (u+1/3)/Real.sqrt (k:ℝ) := by field_simp
    linarith
  have hb : (S.card:ℝ)*r^2 ≤ ((u+1/3)/Real.sqrt (k:ℝ))^2 := by
    by_cases hh : (u+1/3)/Real.sqrt (k:ℝ) ≤ 1
    · rw [← hm]
      simpa only [projectiveCap_real _ (by positivity : 0 ≤ (u+1/3)/Real.sqrt (k:ℝ)) hh] using measureReal_mono (μ := sigma) hsmall
    · have hv := measureReal_mono (μ := sigma) (subset_univ (⋃ p ∈ S, projectiveCap p r))
      rw [hm] at hv
      have hv1 : sigma.real univ = 1 := by simp [measureReal_def]
      rw [hv1] at hv
      have hh' : 1 < (u+1/3)/Real.sqrt (k:ℝ) := lt_of_not_ge hh
      nlinarith
  change (S.card:ℝ) ≤ _
  dsimp [r] at hb
  have hsq := Real.sq_sqrt hk0.le
  field_simp at hb
  linarith

lemma peak_exponential_bound (ξ p : Sphere) (k : ℕ) :
    ‖bracket (ξ:Base) (p:Base)‖^k ≤ Real.exp (-(k:ℝ)*projectiveDistance ξ p^2/2) := by
  have hd := projectiveDistance_sq ξ p
  have he := Real.one_sub_le_exp_neg (projectiveDistance ξ p^2)
  have hp := pow_le_pow_left₀ (sq_nonneg ‖bracket (ξ:Base) (p:Base)‖) (show ‖bracket (ξ:Base) (p:Base)‖^2 ≤ Real.exp (-projectiveDistance ξ p^2) by linarith) k
  rw [← Real.exp_nat_mul] at hp
  have he' : Real.exp (-(k:ℝ)*projectiveDistance ξ p^2/2)^2 = Real.exp ((k:ℝ)*(-projectiveDistance ξ p^2)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hp' : (‖bracket (ξ:Base) (p:Base)‖^k)^2 ≤ Real.exp (-(k:ℝ)*projectiveDistance ξ p^2/2)^2 := by simpa only [he',← pow_mul,mul_comm k 2] using hp
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hp'

lemma gaussian_sequence_summable : Summable (fun n : ℕ => 9*((n:ℝ)+2)^2*Real.exp (-(n:ℝ)^2/4)) := by
  have he : ‖Real.exp (-1:ℝ)‖ < 1 := by rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]; exact Real.exp_lt_one_iff.mpr (by norm_num)
  have h0 := summable_geometric_of_norm_lt_one he
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 he
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 he
  have hsum : Summable (fun n : ℕ => 9*Real.exp 1*((n:ℝ)+2)^2*Real.exp (-(n:ℝ))) := by
    apply Summable.congr (((h2.add (h1.mul_left 4)).add (h0.mul_left 4)).mul_left (9*Real.exp 1))
    intro n
    rw [← Real.exp_nat_mul]
    simp only [mul_neg,mul_one]
    ring
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ hsum
  intro n
  have hn : -(n:ℝ)^2/4 ≤ 1-(n:ℝ) := by linarith [sq_nonneg ((n:ℝ)-2)]
  have hp := Real.exp_le_exp.mpr hn
  rw [Real.exp_sub] at hp
  have heq : Real.exp 1/Real.exp (n:ℝ) = Real.exp 1*Real.exp (-(n:ℝ)) := by rw [Real.exp_neg,div_eq_mul_inv]
  rw [heq] at hp
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 9*((n:ℝ)+2)^2 by positivity)
  linarith

lemma gaussianConstant_pos : 0 < gaussianConstant := by
  have h := gaussian_sequence_summable.le_tsum 0 (fun n hn => by positivity)
  norm_num at h
  exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 36) h

lemma gaussian_full_sum {D : ℝ} (hD : 1 ≤ D) {k : ℕ} (hk : 1 ≤ k)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P) (ξ : Sphere) :
    (∑ p ∈ P, Real.exp (-(Real.sqrt k*projectiveDistance ξ p)^2/4)) ≤ gaussianConstant := by
  classical
  let t : Sphere → ℝ := fun p => Real.sqrt k*projectiveDistance ξ p
  let f : Sphere → ℕ := fun p => ⌊t p⌋₊
  let N := P.sup f+1
  have hmap : ∀ p ∈ P, f p ∈ Finset.range N := by
    intro p hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hp))
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun p => Real.exp (-(t p)^2/4))]
  have hs0 : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < k))
  have hbin : ∀ n : ℕ, (∑ p ∈ P with f p = n, Real.exp (-(t p)^2/4)) ≤
      9*((n:ℝ)+2)^2*Real.exp (-(n:ℝ)^2/4) := by
    intro n
    have hsub : P.filter (fun p => f p=n) ⊆ P.filter (fun p => projectiveDistance ξ p < ((n:ℝ)+1)/Real.sqrt k) := by
      intro p hp
      obtain ⟨hpP,hpn⟩ := Finset.mem_filter.mp hp
      refine Finset.mem_filter.mpr ⟨hpP,?_⟩
      apply (lt_div_iff₀ hs0).mpr
      have hn := Nat.lt_floor_add_one (t p)
      change t p < (f p:ℝ)+1 at hn
      rw [hpn] at hn
      simpa only [t,mul_comm] using hn
    have hc := (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_card hsub)
    have hcount := separated_local_count hD hk hP ξ (show 0 ≤ (n:ℝ)+1 by positivity)
    have hcount' : ((P.filter (fun p => f p=n)).card:ℝ) ≤ 9*((n:ℝ)+2)^2 := by
      have hc' := hc.trans hcount
      linarith [show (0:ℝ) ≤ n by positivity]
    calc
      _ ≤ ∑ p ∈ P with f p=n, Real.exp (-(n:ℝ)^2/4) := by
        apply Finset.sum_le_sum
        intro p hp
        have hn := Nat.floor_le (show 0 ≤ t p from mul_nonneg hs0.le (projectiveDistance_nonneg ξ p))
        change (f p:ℝ) ≤ t p at hn
        rw [(Finset.mem_filter.mp hp).2] at hn
        apply Real.exp_le_exp.mpr
        nlinarith [show (0:ℝ) ≤ n by positivity]
      _ = ((P.filter (fun p => f p=n)).card:ℝ)*Real.exp (-(n:ℝ)^2/4) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcount' (Real.exp_pos _).le
  exact (Finset.sum_le_sum (fun n _ => hbin n)).trans
    (gaussian_sequence_summable.sum_le_tsum _ (fun n hn => by positivity))

lemma peak_gaussian {D : ℝ} (hD : 1 ≤ D) {k : ℕ} (hk : 1 ≤ k)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P)
    (ξ : Sphere) {u : ℝ} (hu : 0 ≤ u) :
    (∑ p ∈ P with u ≤ Real.sqrt k*projectiveDistance ξ p, ‖bracket (ξ:Base) (p:Base)‖^k)
      ≤ gaussianConstant*Real.exp (-u^2/4) := by
  classical
  have hk0 : (0:ℝ) ≤ k := by positivity
  have hs := Real.sq_sqrt hk0
  let S := P.filter (fun p => u ≤ Real.sqrt k*projectiveDistance ξ p)
  have hp : ∀ p ∈ S, ‖bracket (ξ:Base) (p:Base)‖^k ≤
      Real.exp (-u^2/4)*Real.exp (-(Real.sqrt k*projectiveDistance ξ p)^2/4) := by
    intro p hp
    apply (peak_exponential_bound ξ p k).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ht := (Finset.mem_filter.mp hp).2
    have hz : 0 ≤ Real.sqrt k*projectiveDistance ξ p := mul_nonneg (Real.sqrt_nonneg _) (projectiveDistance_nonneg _ _)
    have he : (Real.sqrt k*projectiveDistance ξ p)^2 = (k:ℝ)*projectiveDistance ξ p^2 := by rw [mul_pow,hs]
    nlinarith
  calc
    _ ≤ ∑ p ∈ S, Real.exp (-u^2/4)*Real.exp (-(Real.sqrt k*projectiveDistance ξ p)^2/4) := Finset.sum_le_sum hp
    _ = Real.exp (-u^2/4)*(∑ p ∈ S, Real.exp (-(Real.sqrt k*projectiveDistance ξ p)^2/4)) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-u^2/4)*(∑ p ∈ P, Real.exp (-(Real.sqrt k*projectiveDistance ξ p)^2/4)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun p hp hn => (Real.exp_pos _).le)
    _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left (gaussian_full_sum hD hk hP ξ) (Real.exp_pos (-u^2/4)).le

lemma peak_sphere_bound {D : ℝ} (hD : 1 ≤ D) {k : ℕ} (hk : 1 ≤ k)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P) (ξ : Sphere) :
    ‖peakPolynomial P k (ξ:Base)‖ ≤ gaussianConstant := by
  classical
  have h := peak_gaussian hD hk hP ξ (u := 0) le_rfl
  have hn : ∀ p : Sphere, 0 ≤ Real.sqrt k*projectiveDistance ξ p := fun p => mul_nonneg (Real.sqrt_nonneg _) (projectiveDistance_nonneg _ _)
  simp only [hn,Finset.filter_true,zero_pow (by norm_num : (2:ℕ) ≠ 0),neg_zero,zero_div,Real.exp_zero,mul_one] at h
  apply (norm_sum_le _ _).trans
  simpa only [norm_pow] using h

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePeakBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma peak_global_bound {D : ℝ} (hD : 1 ≤ D) {k : ℕ} (hk : 1 ≤ k)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P) (z : Base) :
    ‖peakPolynomial P k z‖ ≤ gaussianConstant*‖z‖^k := by
  by_cases hz : z=0
  · subst z
    simp [peakPolynomial_zero P (by omega : k ≠ 0),show k ≠ 0 by omega]
  have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let ξ : Sphere := ⟨(‖z‖:ℂ)⁻¹ • z, by
    simp only [Metric.mem_sphere,dist_zero_right,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_norm]
    field_simp⟩
  have he : (‖z‖:ℂ) • (ξ:Base) = z := by
    exact smul_inv_smul₀ (by exact_mod_cast hzn : (‖z‖:ℂ) ≠ 0) z
  rw [← he,peakPolynomial_homogeneous,norm_mul,norm_pow]
  have hh := peak_sphere_bound hD hk hP ξ
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ ‖(‖z‖:ℂ)‖^k by positivity)
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_norm,he,mul_comm] using hm

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseChartScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma chart_small_ball {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {z : Base} (hz : ‖z‖ < (1/32:ℝ)) :
    1/2 ≤ ‖1+(r:ℂ)*z 0‖ ∧ ‖1+(r:ℂ)*z 0‖ ≤ 2 := by
  have hz0 := PiLp.norm_apply_le (p := (2:ENNReal)) z 0
  have hm : ‖(r:ℂ)*z 0‖ ≤ 1/32 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]
    have := norm_nonneg (z 0)
    nlinarith
  have hupper := norm_add_le (1:ℂ) ((r:ℂ)*z 0)
  have hlower := norm_add_le (1+(r:ℂ)*z 0) (-((r:ℂ)*z 0))
  simp only [norm_one] at hupper
  simp only [add_neg_cancel_right,norm_one,norm_neg] at hlower
  constructor <;> linarith

lemma chart_norm_deficit {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) {z : Base} (hz : ‖z‖ < (1/32:ℝ)) :
    ‖centeredChart r U z‖ ≤ 1-(1-r)/16 := by
  have hzb : z ∈ ball := by change ‖z‖ < 1; linarith
  have hd := centeredChart_den_ne_zero hr hr1 hzb
  have he := centeredChart_norm_identity hr hr1 U z hd
  have hnorm : ‖centeredChart r U z‖ < 1 := centeredChart_mapsTo hr hr1 U hzb
  have hden := chart_small_ball hr hr1 hz
  have hsqden : ‖1+(r:ℂ)*z 0‖^2 ≤ 4 := by nlinarith [norm_nonneg (1+(r:ℂ)*z 0)]
  have hnum : (1-r)/2 ≤ (1-r^2)*(1-‖z‖^2) := by
    have hn : ‖z‖^2 ≤ 1/2 := by nlinarith [norm_nonneg z]
    have hrr : 1-r ≤ 1-r^2 := by nlinarith
    nlinarith
  have hdiv : (1-r)/8 ≤ (1-r^2)*(1-‖z‖^2)/‖1+(r:ℂ)*z 0‖^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < ‖1+(r:ℂ)*z 0‖))).2
    nlinarith
  rw [← he] at hdiv
  nlinarith [norm_nonneg (centeredChart r U z)]

lemma peak_chart_high {D : ℝ} (hD : 1 ≤ D) {k : ℕ} (hk : 1 ≤ k)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (U : Base ≃ₗᵢ[ℂ] Base)
    {z : Base} (hz : ‖z‖ < (1/32:ℝ)) :
    ‖peakPolynomial P k (centeredChart r U z)‖ ≤ gaussianConstant*Real.exp (-(k:ℝ)*(1-r)/16) := by
  have hb := chart_norm_deficit hr hr1 U hz
  have he : ‖centeredChart r U z‖ ≤ Real.exp (-(1-r)/16) :=
    hb.trans (by simpa only [neg_div] using Real.one_sub_le_exp_neg ((1-r)/16))
  have hp := pow_le_pow_left₀ (norm_nonneg (centeredChart r U z)) he k
  rw [← Real.exp_nat_mul] at hp
  have hex : (k:ℝ)*(-(1-r)/16)=-(k:ℝ)*(1-r)/16 := by ring
  rw [hex] at hp
  exact (peak_global_bound hD hk hP _).trans (mul_le_mul_of_nonneg_left hp gaussianConstant_pos.le)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseAnisotropic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma anisotropicMap_analytic (k : ℕ) (r : ℝ) : AnalyticOnNhd ℂ (anisotropicMap k r) univ := by
  intro z _
  apply (baseCoordinateEquiv.symm.analyticAt _).comp
  apply analyticAt_pi_iff.mpr
  intro i
  fin_cases i
  · exact analyticAt_const.add ((baseCoordinate 0).analyticAt z).div_const
  · exact ((baseCoordinate 1).analyticAt z).div_const

lemma anisotropicMap_norm {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {z : Base} (hz : ‖z‖ ≤ 1) : ‖anisotropicMap k r z‖ ≤ 1+2/(k:ℝ) := by
  have hkpos : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hk1 : 1 ≤ (k:ℝ) := by exact_mod_cast hk
  have hs : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr hkpos
  have hsq := Real.sq_sqrt hkpos.le
  have h0 : ‖z 0‖ ≤ 1 := (PiLp.norm_apply_le (p := (2:ENNReal)) z 0).trans hz
  have h1 : ‖z 1‖ ≤ 1 := (PiLp.norm_apply_le (p := (2:ENNReal)) z 1).trans hz
  have hn0 : ‖(r:ℂ)+z 0/(k:ℂ)‖ ≤ 1+1/(k:ℝ) := by
    apply (norm_add_le _ _).trans
    simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,Complex.norm_natCast]
    exact add_le_add hr1 (div_le_div_of_nonneg_right h0 hkpos.le)
  have hn1 : ‖z 1/(Real.sqrt (k:ℝ):ℂ)‖ ≤ 1/Real.sqrt (k:ℝ) := by
    simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs]
    exact div_le_div_of_nonneg_right h1 hs.le
  have he : ‖anisotropicMap k r z‖^2 = ‖(r:ℂ)+z 0/(k:ℂ)‖^2+‖z 1/(Real.sqrt (k:ℝ):ℂ)‖^2 := by
    simp [anisotropicMap,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  have hi : (1/Real.sqrt (k:ℝ))^2=1/(k:ℝ) := by rw [div_pow,hsq,one_pow]
  have hb : ‖anisotropicMap k r z‖^2 ≤ (1+1/(k:ℝ))^2+1/(k:ℝ) := by
    have ha0 := norm_nonneg ((r:ℂ)+z 0/(k:ℂ))
    have ha1 := norm_nonneg (z 1/(Real.sqrt (k:ℝ):ℂ))
    linarith [sq_le_sq₀ ha0 (by positivity : 0 ≤ 1+1/(k:ℝ)) |>.mpr hn0,
      sq_le_sq₀ ha1 (by positivity : 0 ≤ 1/Real.sqrt (k:ℝ)) |>.mpr hn1]
  have hipos : 0 ≤ 1/(k:ℝ) := by positivity
  rw [show (2:ℝ)/(k:ℝ)=2*(1/(k:ℝ)) by ring]
  nlinarith [sq_nonneg (1/(k:ℝ)),norm_nonneg (anisotropicMap k r z)]

lemma peak_anisotropic_bound {D : ℝ} (hD : 1 ≤ D) {k : ℕ} (hk : 1 ≤ k)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (U : Base ≃ₗᵢ[ℂ] Base)
    {z : Base} (hz : ‖z‖ ≤ 1) :
    ‖peakPolynomial P k (U (anisotropicMap k r z))‖ ≤ gaussianConstant*Real.exp 2 := by
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have he : 1+2/(k:ℝ) ≤ Real.exp (2/(k:ℝ)) := by simpa only [add_comm] using Real.add_one_le_exp (2/(k:ℝ))
  have hp := pow_le_pow_left₀ (norm_nonneg (anisotropicMap k r z))
    ((anisotropicMap_norm hk hr hr1 hz).trans he) k
  rw [← Real.exp_nat_mul] at hp
  have hex : (k:ℝ)*(2/(k:ℝ))=2 := mul_div_cancel₀ 2 hk0
  rw [hex] at hp
  simpa only [LinearIsometryEquiv.norm_map] using
    (peak_global_bound hD hk hP (U (anisotropicMap k r z))).trans
      (mul_le_mul_of_nonneg_left (by simpa only [LinearIsometryEquiv.norm_map] using hp) gaussianConstant_pos.le)

lemma peak_anisotropic_lipschitz : ∃ B : ℝ, 0 ≤ B ∧ ∀ {D : ℝ}, 1 ≤ D → ∀ {k : ℕ}, 1 ≤ k →
    ∀ {P : Finset Sphere}, ProjectivelySeparated (D/Real.sqrt k) P → ∀ {r : ℝ}, 0 ≤ r → r ≤ 1 →
    ∀ U : Base ≃ₗᵢ[ℂ] Base, ∀ z : Base, ‖z‖ ≤ 1/2 →
    ‖peakPolynomial P k (U (anisotropicMap k r z))-peakPolynomial P k (U (anisotropicMap k r 0))‖ ≤ B*‖z‖ := by
  let B := cauchyJetConstant 1*(gaussianConstant*Real.exp 2)/(1-3/4)
  have hB : 0 ≤ B := div_nonneg (mul_nonneg (cauchyJetConstant_pos 1).le
    (mul_nonneg gaussianConstant_pos.le (Real.exp_pos _).le)) (by norm_num)
  refine ⟨B,hB,?_⟩
  intro D hD k hk P hP r hr hr1 U z hz
  let f := fun z => peakPolynomial P k (U (anisotropicMap k r z))
  have hf : AnalyticOnNhd ℂ f univ := by
    intro z _
    exact (peakPolynomial_analytic P k _ (mem_univ _)).comp
      ((U.toContinuousLinearEquiv.analyticAt _).comp (anisotropicMap_analytic k r z (mem_univ _)))
  have hb (x : Base) (hx : ‖x‖ ≤ 1/2) : ‖fderiv ℂ f x‖ ≤ B := by
    have hh := analytic_jet_bound (E := Base) (F := ℂ) (c := 0) (R := 1) (r := 3/4)
      (by norm_num) (by norm_num) (mul_nonneg gaussianConstant_pos.le (Real.exp_pos _).le)
      (hf.mono (subset_univ _)) (fun y hy => peak_anisotropic_bound hD hk hP hr hr1 U (by exact (show ‖y‖ < 1 by simpa using hy).le)) 1 x
      (by simpa using (by linarith : ‖x‖ < (3/4:ℝ)))
    simpa only [norm_iteratedFDeriv_one,pow_one,B] using hh
  have hh := (convex_closedBall (0:Base) (1/2:ℝ)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (hf x (mem_univ _)).differentiableAt) (fun x hx => hb x (by simpa using hx))
    (show (0:Base) ∈ Metric.closedBall 0 (1/2:ℝ) by simp)
    (show z ∈ Metric.closedBall 0 (1/2:ℝ) by simpa using hz)
  simpa only [sub_zero] using hh

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseChartLow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma anisotropicChart_identity {k : ℕ} (hk : 1 ≤ k) (r : ℝ)
    (U : Base ≃ₗᵢ[ℂ] Base) (z : Base) :
    U (anisotropicMap k r (anisotropicChart k r z))=centeredChart r U z := by
  have hk0 : (k:ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hs0 : (Real.sqrt (k:ℝ):ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < k by omega))).ne'
  congr 1
  ext i
  fin_cases i <;> dsimp [anisotropicMap,anisotropicChart,centeredChart]
  all_goals
    by_cases hd : 1+(r:ℂ)*z 0=0
    · simp [hd]
      <;> field_simp [hk0,hs0]
      <;> ring
    · field_simp [hk0,hs0,hd]
      <;> ring

lemma anisotropicChart_norm {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hkr : (k:ℝ)*(1-r) ≤ 1) {z : Base} (hz : ‖z‖ < (1/32:ℝ)) :
    ‖anisotropicChart k r z‖ ≤ Real.sqrt ((k:ℝ)*(1-r))/4 := by
  have hkpos : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hδ : 0 < 1-r := by linarith
  have hs : 0 < Real.sqrt ((k:ℝ)*(1-r)) := Real.sqrt_pos.mpr (mul_pos hkpos hδ)
  have hs2 := Real.sq_sqrt (mul_nonneg hkpos.le hδ.le)
  have hs1 : Real.sqrt ((k:ℝ)*(1-r)) ≤ 1 := (Real.sqrt_le_one).2 hkr
  have hkst : (k:ℝ)*(1-r) ≤ Real.sqrt ((k:ℝ)*(1-r)) := by nlinarith
  have hden := chart_small_ball hr hr1 hz
  have hdenpos : 0 < ‖1+(r:ℂ)*z 0‖ := by linarith
  have hd : 1+(r:ℂ)*z 0 ≠ 0 := norm_ne_zero_iff.mp hdenpos.ne'
  have hz0 := PiLp.norm_apply_le (p := (2:ENNReal)) z 0
  have hz1 := PiLp.norm_apply_le (p := (2:ENNReal)) z 1
  have hrr : 0 ≤ 1-r^2 := by nlinarith
  have hid : ((r:ℂ)+z 0)/(1+(r:ℂ)*z 0)-(r:ℂ) = ((1-r^2:ℝ):ℂ)*z 0/(1+(r:ℂ)*z 0) := by
    push_cast
    field_simp
    ring
  have hfirst : ‖(k:ℂ)*(((r:ℂ)+z 0)/(1+(r:ℂ)*z 0)-(r:ℂ))‖ ≤ Real.sqrt ((k:ℝ)*(1-r))/8 := by
    rw [hid,norm_mul,norm_div,norm_mul,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hrr]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hdenpos).2
    have hn : (k:ℝ)*(1-r^2) ≤ 2*((k:ℝ)*(1-r)) := by nlinarith
    have hmul : (k:ℝ)*(1-r^2)*‖z 0‖ ≤ 2*Real.sqrt ((k:ℝ)*(1-r))*(1/32) := by
      calc _ ≤ (2*((k:ℝ)*(1-r)))*‖z 0‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
           _ ≤ (2*Real.sqrt ((k:ℝ)*(1-r)))*(1/32) :=
             mul_le_mul (by linarith) (by linarith) (norm_nonneg _) (by positivity)
    nlinarith
  have hsprod : Real.sqrt (k:ℝ)*Real.sqrt (1-r^2) ≤ 2*Real.sqrt ((k:ℝ)*(1-r)) := by
    have h1 := Real.sq_sqrt hkpos.le
    have h2 := Real.sq_sqrt hrr
    have he : (Real.sqrt (k:ℝ)*Real.sqrt (1-r^2))^2=(k:ℝ)*(1-r^2) := by rw [mul_pow,h1,h2]
    have hn : (k:ℝ)*(1-r^2) ≤ 4*((k:ℝ)*(1-r)) := by nlinarith
    nlinarith [mul_nonneg (Real.sqrt_nonneg (k:ℝ)) (Real.sqrt_nonneg (1-r^2))]
  have hsecond : ‖(Real.sqrt (k:ℝ):ℂ)*(Real.sqrt (1-r^2):ℂ)*z 1/(1+(r:ℂ)*z 0)‖ ≤ Real.sqrt ((k:ℝ)*(1-r))/8 := by
    rw [norm_div,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (div_le_iff₀ hdenpos).2
    have hm : Real.sqrt (k:ℝ)*Real.sqrt (1-r^2)*‖z 1‖ ≤ 2*Real.sqrt ((k:ℝ)*(1-r))*(1/32) :=
      mul_le_mul hsprod (by linarith) (norm_nonneg _) (by positivity)
    nlinarith
  have hnorm : ‖anisotropicChart k r z‖^2 =
      ‖(k:ℂ)*(((r:ℂ)+z 0)/(1+(r:ℂ)*z 0)-(r:ℂ))‖^2+
      ‖(Real.sqrt (k:ℝ):ℂ)*(Real.sqrt (1-r^2):ℂ)*z 1/(1+(r:ℂ)*z 0)‖^2 := by
    simp [anisotropicChart,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  have hn0 := norm_nonneg ((k:ℂ)*(((r:ℂ)+z 0)/(1+(r:ℂ)*z 0)-(r:ℂ)))
  have hn1 := norm_nonneg ((Real.sqrt (k:ℝ):ℂ)*(Real.sqrt (1-r^2):ℂ)*z 1/(1+(r:ℂ)*z 0))
  nlinarith [norm_nonneg (anisotropicChart k r z)]

lemma peak_chart_low : ∃ B : ℝ, 0 ≤ B ∧ ∀ {D : ℝ}, 1 ≤ D → ∀ {k : ℕ}, 1 ≤ k →
    ∀ {P : Finset Sphere}, ProjectivelySeparated (D/Real.sqrt k) P → ∀ {r : ℝ}, 0 ≤ r → r < 1 →
    (k:ℝ)*(1-r) ≤ 1 → ∀ U : Base ≃ₗᵢ[ℂ] Base, ∀ z : Base, ‖z‖ < 1/32 →
    ‖peakPolynomial P k (centeredChart r U z)-peakPolynomial P k (centeredChart r U 0)‖ ≤ B*Real.sqrt ((k:ℝ)*(1-r)) := by
  obtain ⟨B,hB,hBb⟩ := peak_anisotropic_lipschitz
  refine ⟨B,hB,?_⟩
  intro D hD k hk P hP r hr hr1 hkr U z hz
  have hn := anisotropicChart_norm hk hr hr1 hkr hz
  have hs1 : Real.sqrt ((k:ℝ)*(1-r)) ≤ 1 := Real.sqrt_le_one.mpr hkr
  have hn1 : ‖anisotropicChart k r z‖ ≤ 1/2 := by linarith
  have hh := hBb hD hk hP hr hr1.le U _ hn1
  rw [anisotropicChart_identity hk] at hh
  have hzero : U (anisotropicMap k r 0)=centeredChart r U 0 := by
    unfold anisotropicMap centeredChart
    simp
  rw [hzero] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left hn hB).trans (by nlinarith [Real.sqrt_nonneg ((k:ℝ)*(1-r))]))

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseChartJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma logarithmicTest_chart_jets (a : ℝ) {ε : ℝ} (he : ε ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {D : ℝ}, 1 ≤ D → ∀ {k : ℕ}, 1 ≤ k →
      ∀ {P : Finset Sphere}, ProjectivelySeparated (D/Real.sqrt k) P →
      ∀ {r : ℝ}, 0 ≤ r → r < 1 → ∀ U : Base ≃ₗᵢ[ℂ] Base,
      ‖iteratedFDeriv ℝ n (logarithmicTest a ε P k ∘ centeredChart r U) 0‖ ≤ C*chartScale k (1-r) := by
  obtain ⟨B,hB,hBlow⟩ := peak_chart_low
  let B' := B+2*gaussianConstant
  have hB' : 0 ≤ B' := by dsimp [B']; linarith [gaussianConstant_pos]
  obtain ⟨C,hC,hCb⟩ := regularizedLog_positive_jet_bound a he (by norm_num : (0:ℝ) < 1/32)
    gaussianConstant_pos.le hB' hn
  refine ⟨C,hC,?_⟩
  intro D hD k hk P hP r hr hr1 U
  let f := peakPolynomial P k ∘ centeredChart r U
  have hf : AnalyticOnNhd ℂ f (Metric.ball (0:Base) (1/32)) := by
    intro z hz
    have hzb : z ∈ ball := by
      have hz' : ‖z‖ < 1/32 := by simpa using hz
      change ‖z‖ < 1
      linarith
    exact (peakPolynomial_analytic P k _ (mem_univ _)).comp
      (centeredChart_analyticAt U (centeredChart_den_ne_zero hr hr1 hzb))
  have hfc : ‖f 0‖ ≤ gaussianConstant := by
    apply (peak_global_bound hD hk hP _).trans
    apply mul_le_of_le_one_right gaussianConstant_pos.le
    exact pow_le_one₀ (norm_nonneg _) (centeredChart_zero_mem hr hr1 U).le
  have hkδ : 0 < (k:ℝ)*(1-r) := mul_pos (by exact_mod_cast (show 0 < k by omega)) (by linarith)
  by_cases hlow : (k:ℝ)*(1-r) ≤ 1
  · rw [chartScale,ite_eq_left hlow]
    apply hCb f 0 (Real.sqrt ((k:ℝ)*(1-r))) hf hfc (Real.sqrt_pos.mpr hkδ) (Real.sqrt_le_one.mpr hlow)
    intro z hz
    apply (hBlow hD hk hP hr hr1 hlow U z (by simpa using hz)).trans
    exact mul_le_mul_of_nonneg_right (by dsimp [B']; linarith [gaussianConstant_pos]) (Real.sqrt_nonneg _)
  · rw [chartScale,ite_eq_right hlow]
    apply hCb f 0 (Real.exp (-(k:ℝ)*(1-r)/16)) hf hfc (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr (by linarith))
    intro z hz
    have hb := peak_chart_high hD hk hP hr hr1 U (by simpa using hz : ‖z‖ < (1/32:ℝ))
    have hb0 := peak_chart_high hD hk hP hr hr1 U (z := 0) (by simp)
    apply (norm_sub_le _ _).trans
    dsimp [f,Function.comp_def]
    dsimp [B']
    nlinarith [Real.exp_pos (-(k:ℝ)*(1-r)/16)]

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePotentialSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma lacunary_degree_ge {Q : ℕ} (hQ : 2 ≤ Q) (j : ℕ) : j+1 ≤ Q^(j+1) := by
  have hh : j+1 ≤ 2^(j+1) := (Nat.lt_two_pow_self (n := j+1)).le
  exact hh.trans (Nat.pow_le_pow_left hQ _)

lemma summable_lacunary {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) {Q : ℕ} (hQ : 2 ≤ Q) :
    Summable (fun j : ℕ => R^(Q^(j+1))) := by
  apply Summable.of_nonneg_of_le (fun j => pow_nonneg hR _) _
    ((summable_geometric_of_lt_one hR hR1).mul_right R)
  intro j
  rw [← pow_succ]
  exact pow_le_pow_of_le_one hR hR1.le (lacunary_degree_ge hQ j)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseLocalSmoothSeriesOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler10148_1 uKahler10148_2 uKahler10162_1 uKahler10162_2 uKahler10184_1 uKahler10184_2

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma local_jet_series_derivative_on {E : Type uKahler10148_1} {F : Type uKahler10148_2} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℕ → E → F} {s : Set E} (hf : ∀ j y, y ∈ s → ContDiffAt ℝ ∞ (f j) y)
    (hs : IsOpen s) (hc : IsPreconnected s) {x : E} (hx : x ∈ s)
    {v : ℕ → ℕ → ℝ} (hv : ∀ n, Summable (v n))
    (hb : ∀ n j y, y ∈ s → ‖iteratedFDeriv ℝ n (f j) y‖ ≤ v n j) (n : ℕ) :
    HasFDerivAt (fun y => ∑' j, iteratedFDeriv ℝ n (f j) y)
      (∑' j, fderiv ℝ (iteratedFDeriv ℝ n (f j)) x) x := by
  apply hasFDerivAt_tsum_of_isPreconnected (hv (n+1)) hs hc
    (fun j y hy => ((hf j y hy).differentiableAt_iteratedFDeriv (by exact_mod_cast (ENat.natCast_lt_top n))).hasFDerivAt)
    (fun j y hy => ?_) hx
    (Summable.of_norm_bounded (hv n) (fun j => hb n j x hx)) hx
  simpa only [norm_fderiv_iteratedFDeriv] using hb (n+1) j y hy

lemma local_iteratedFDeriv_tsum_on {E : Type uKahler10162_1} {F : Type uKahler10162_2} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℕ → E → F} {s : Set E} (hf : ∀ j y, y ∈ s → ContDiffAt ℝ ∞ (f j) y)
    (hs : IsOpen s) (hc : IsPreconnected s)
    {v : ℕ → ℕ → ℝ} (hv : ∀ n, Summable (v n))
    (hb : ∀ n j y, y ∈ s → ‖iteratedFDeriv ℝ n (f j) y‖ ≤ v n j) (n : ℕ) :
    EqOn (iteratedFDeriv ℝ n (fun y => ∑' j, f j y))
      (fun y => ∑' j, iteratedFDeriv ℝ n (f j) y) s := by
  induction n with
  | zero =>
    intro x hx
    simp_rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.map_tsum
  | succ n ih =>
    intro x hx
    have he : iteratedFDeriv ℝ n (fun y => ∑' j, f j y) =ᶠ[𝓝 x]
        (fun y => ∑' j, iteratedFDeriv ℝ n (f j) y) :=
      Filter.eventuallyEq_of_mem (hs.mem_nhds hx) (fun y hy => ih hy)
    simp_rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply]
    rw [he.fderiv_eq,(local_jet_series_derivative_on hf hs hc hx hv hb n).fderiv]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) F).symm.toContinuousLinearEquiv.map_tsum

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseChartSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma logarithmicTest_chart_contDiffAt (a : ℝ) {ε : ℝ} (he : ε ≠ 0)
    (P : Finset Sphere) (k : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) {z : Base} (hz : z ∈ ball) :
    ContDiffAt ℝ ∞ (logarithmicTest a ε P k ∘ centeredChart r U) z :=
  (logarithmicTest_contDiff a he P k).contDiffAt.comp z
    ((centeredChart_analyticAt U (centeredChart_den_ne_zero hr hr1 hz)).contDiffAt.restrict_scalars ℝ)

lemma logarithmicTest_chart_local_jets (a : ℝ) {ε D r : ℝ} (he : ε ≠ 0)
    (hD : 1 ≤ D) (hr : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ P : Finset Sphere,
      ProjectivelySeparated (D/Real.sqrt k) P → ∀ U : Base ≃ₗᵢ[ℂ] Base,
      ∀ z ∈ Metric.ball (0:Base) (1/64),
      ‖iteratedFDeriv ℝ n (logarithmicTest a ε P k ∘ centeredChart r U) z‖ ≤ C*(1-(1-r)/16)^k := by
  have hG := gaussianConstant_pos
  let R := 1-(1-r)/16
  have hR : 0 < R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hpb (k : ℕ) (hk : 1 ≤ k) (P : Finset Sphere)
      (hP : ProjectivelySeparated (D/Real.sqrt k) P) (U : Base ≃ₗᵢ[ℂ] Base)
      (z : Base) (hz : ‖z‖ < 1/32) :
      ‖peakPolynomial P k (centeredChart r U z)‖ ≤ gaussianConstant*R^k :=
    (peak_global_bound hD hk hP _).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (chart_norm_deficit hr hr1 U hz) k) gaussianConstant_pos.le)
  by_cases hn : n=0
  · subst n
    obtain ⟨C,hC,hCb⟩ := regularizedLog_lipschitz_bound a he gaussianConstant_pos.le
    refine ⟨C*gaussianConstant,by positivity,?_⟩
    intro k hk P hP U z hz
    have hp := hpb k hk P hP U z (by
      have hz' : ‖z‖ < 1/64 := by simpa using hz
      linarith)
    have hpG : ‖peakPolynomial P k (centeredChart r U z)‖ ≤ gaussianConstant :=
      hp.trans (mul_le_of_le_one_right gaussianConstant_pos.le (pow_le_one₀ hR.le hR1.le))
    rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs]
    exact (hCb _ hpG).trans ((mul_le_mul_of_nonneg_left hp hC).trans_eq (by ring))
  · obtain ⟨C,hC,hCb⟩ := regularizedLog_positive_jet_bound a he (by norm_num : (0:ℝ)<1/64)
      gaussianConstant_pos.le (by positivity : 0 ≤ 2*gaussianConstant) (by omega : 1 ≤ n)
    refine ⟨C,hC,?_⟩
    intro k hk P hP U z hz
    have hz' : ‖z‖ < 1/64 := by simpa using hz
    have hsub (x : Base) (hx : x ∈ Metric.ball z (1/64)) : ‖x‖ < 1/32 := by
      have hh := dist_triangle x z 0
      have hx' : dist x z < 1/64 := hx
      simp only [dist_zero_right] at hh
      linarith
    have hf : AnalyticOnNhd ℂ (peakPolynomial P k ∘ centeredChart r U) (Metric.ball z (1/64)) := by
      intro x hx
      have hxb : x ∈ ball := by change ‖x‖ < 1; linarith [hsub x hx]
      exact (peakPolynomial_analytic P k _ (mem_univ _)).comp
        (centeredChart_analyticAt U (centeredChart_den_ne_zero hr hr1 hxb))
    have hp := hpb k hk P hP U z (by linarith)
    have hpG : ‖peakPolynomial P k (centeredChart r U z)‖ ≤ gaussianConstant :=
      hp.trans (mul_le_of_le_one_right gaussianConstant_pos.le (pow_le_one₀ hR.le hR1.le))
    apply hCb _ z (R^k) hf hpG (pow_pos hR _) (pow_le_one₀ hR.le hR1.le)
    intro x hx
    apply (norm_sub_le _ _).trans
    dsimp only [Function.comp_apply]
    linarith [hpb k hk P hP U x (hsub x hx)]

lemma testSeries_chart_iteratedFDeriv (a : ℝ) {ε D : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D)
    {Q : ℕ} (hQ : 2 ≤ Q) (P : ℕ → Finset Sphere)
    (hP : ∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1))))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (U : Base ≃ₗᵢ[ℂ] Base) (n : ℕ) :
    iteratedFDeriv ℝ n ((fun y => ∑' j, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) y) ∘ centeredChart r U) 0 =
      ∑' j, iteratedFDeriv ℝ n (logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ∘ centeredChart r U) 0 := by
  choose C hC hb using (fun n => logarithmicTest_chart_local_jets a he hD hr hr1 n)
  have hs := summable_lacunary (by linarith : 0 ≤ 1-(1-r)/16) (by linarith : 1-(1-r)/16 < 1) hQ
  exact local_iteratedFDeriv_tsum_on
    (fun j z hz => logarithmicTest_chart_contDiffAt a he _ _ hr hr1 U
      (by
        have hz' : ‖z‖ < 1/64 := by simpa using hz
        change ‖z‖ < 1
        linarith))
    Metric.isOpen_ball (convex_ball (0:Base) (1/64)).isPreconnected
    (fun n => hs.mul_left (C n))
    (fun n j z hz => hb n _ (Nat.one_le_pow _ _ (by omega)) _ (hP j) U z hz) n
    (Metric.mem_ball_self (by norm_num))

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseScaleSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
namespace PinchedHartogs.BaseConstruction

lemma chartScale_nonneg (k : ℕ) (δ : ℝ) : 0 ≤ chartScale k δ := by
  unfold chartScale
  split <;> positivity

lemma chartScale_le_inverse {k : ℕ} {δ : ℝ} (hkδ : 0 < (k:ℝ)*δ) :
    chartScale k δ ≤ 16/((k:ℝ)*δ) := by
  unfold chartScale
  split_ifs with h
  · have hs := Real.sqrt_le_one.mpr h
    have hi : 1 ≤ 16/((k:ℝ)*δ) := (le_div_iff₀ hkδ).mpr (by linarith)
    exact hs.trans hi
  · have hpos : 0 < (k:ℝ)*δ/16 := by positivity
    have he : (k:ℝ)*δ/16 ≤ Real.exp ((k:ℝ)*δ/16) := by linarith [Real.add_one_le_exp ((k:ℝ)*δ/16)]
    have hh := one_div_le_one_div_of_le hpos he
    rw [one_div, ← Real.exp_neg] at hh
    calc Real.exp (-(k:ℝ)*δ/16) = Real.exp (-((k:ℝ)*δ/16)) := congrArg Real.exp (by ring)
         _ ≤ 1/((k:ℝ)*δ/16) := hh
         _ = 16/((k:ℝ)*δ) := by field_simp

lemma chartScale_summable {Q : ℕ} (hQ : 2 ≤ Q) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun j => chartScale (Q^(j+1)) δ) := by
  have hQ0 : 0 < (Q:ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hi : (Q:ℝ)⁻¹ < 1 := (inv_lt_one₀ hQ0).mpr (by exact_mod_cast hQ)
  have hs := (summable_geometric_of_lt_one (inv_nonneg.mpr hQ0.le) hi).mul_left (16/δ*(Q:ℝ)⁻¹)
  apply Summable.of_nonneg_of_le (fun j => chartScale_nonneg _ _) _ hs
  intro j
  apply (chartScale_le_inverse (by rw [Nat.cast_pow]; positivity : 0 < ((Q^(j+1):ℕ):ℝ)*δ)).trans_eq
  rw [Nat.cast_pow,pow_succ,inv_pow]
  field_simp

lemma chartScale_sum_uniform {Q : ℕ} (hQ : 2 ≤ Q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ δ : ℝ, 0 < δ → (∑' j, chartScale (Q^(j+1)) δ) ≤ B := by
  have hQ1 : 1 < (Q:ℝ) := by exact_mod_cast (show 1 < Q by omega)
  have hQ0 : 0 < (Q:ℝ) := by linarith
  let s := Real.sqrt (Q:ℝ)
  have hs : 1 < s := by
    dsimp [s]
    exact (Real.lt_sqrt (by norm_num)).mpr (by simpa using hQ1)
  have hsPow (n : ℕ) : Real.sqrt ((Q:ℝ)^n) = s^n := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hQ0.le _), ih, pow_succ]
  have hspos : 0 < s-1 := by linarith
  have hi : (Q:ℝ)⁻¹ < 1 := (inv_lt_one₀ hQ0).mpr hQ1
  let B := s/(s-1)+16/(1-(Q:ℝ)⁻¹)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  intro δ hδ
  have hex : ∃ J : ℕ, 1 < (Q:ℝ)^(J+1)*δ := by
    obtain ⟨J,hJ⟩ := exists_nat_gt (1/δ)
    have hd := (div_lt_iff₀ hδ).mp hJ
    have hg : (J+1:ℝ) ≤ (Q:ℝ)^(J+1) := by exact_mod_cast lacunary_degree_ge hQ J
    refine ⟨J,?_⟩
    nlinarith
  let J := Nat.find hex
  have hJ : 1 < (Q:ℝ)^(J+1)*δ := Nat.find_spec hex
  have hlow (j : ℕ) (hj : j < J) : (Q:ℝ)^(j+1)*δ ≤ 1 := le_of_not_gt (Nat.find_min hex hj)
  have hpow : J=0 ∨ (Q:ℝ)^J*δ ≤ 1 := by
    by_cases hzero : J=0
    · exact Or.inl hzero
    · right
      obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      have hh := hlow m (by omega)
      simpa [hm,Nat.succ_eq_add_one] using hh
  have hlo : (∑ j ∈ Finset.range J, chartScale (Q^(j+1)) δ) ≤ s/(s-1) := by
    by_cases hzero : J=0
    · simp only [hzero,Finset.range_zero,Finset.sum_empty]
      exact div_nonneg (by linarith) hspos.le
    have hp : (Q:ℝ)^J*δ ≤ 1 := hpow.resolve_left hzero
    have hsδ : s^J*Real.sqrt δ ≤ 1 := by
      have hh := Real.sqrt_le_one.mpr hp
      simpa only [Real.sqrt_mul (pow_nonneg hQ0.le _),hsPow] using hh
    have heach (j : ℕ) (hj : j ∈ Finset.range J) : chartScale (Q^(j+1)) δ = s*Real.sqrt δ*s^j := by
      rw [chartScale,ite_eq_left (by rw [Nat.cast_pow]; exact hlow j (Finset.mem_range.mp hj)),Nat.cast_pow,
        Real.sqrt_mul (pow_nonneg hQ0.le _),hsPow,pow_succ]
      dsimp [s]
      ring
    rw [Finset.sum_congr rfl heach,← Finset.mul_sum]
    apply (le_div_iff₀ hspos).mpr
    have hg := geom_sum_mul s J
    have heq : (s*Real.sqrt δ*∑ j ∈ Finset.range J, s^j)*(s-1)=s*Real.sqrt δ*(s^J-1) := by
      rw [mul_assoc,geom_sum_mul]
    rw [heq]
    have hsq := Real.sqrt_nonneg δ
    nlinarith
  have htail : (∑' m, chartScale (Q^(m+J+1)) δ) ≤ 16/(1-(Q:ℝ)⁻¹) := by
    have hsum := summable_geometric_of_lt_one (inv_nonneg.mpr hQ0.le) hi
    have ht : Summable (fun m => chartScale (Q^(m+J+1)) δ) :=
      (chartScale_summable hQ hδ).comp_injective (fun m n h => Nat.add_right_cancel h)
    have hh := ht.tsum_le_tsum (g := fun m => 16*((Q:ℝ)⁻¹)^m) (fun m => ?_) (hsum.mul_left 16)
    · rw [tsum_mul_left,tsum_geometric_of_lt_one (inv_nonneg.mpr hQ0.le) hi] at hh
      exact hh.trans_eq (by ring)
    apply (chartScale_le_inverse (by rw [Nat.cast_pow]; positivity : 0 < ((Q^(m+J+1):ℕ):ℝ)*δ)).trans
    have heq : 16/(((Q^(m+J+1):ℕ):ℝ)*δ) = (16/((Q:ℝ)^(J+1)*δ))*((Q:ℝ)⁻¹)^m := by
      rw [Nat.cast_pow,show m+J+1=(J+1)+m by omega,pow_add,inv_pow]
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right ((div_le_iff₀ (by positivity : 0 < (Q:ℝ)^(J+1)*δ)).mpr (by linarith)) (by positivity)
  rw [← (chartScale_summable hQ hδ).sum_add_tsum_nat_add J]
  exact add_le_add hlo htail

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseChartUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma testSeries_chart_uniform_jets_oai (a : ℝ) {ε D : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D)
    {Q : ℕ} (hQ : 2 ≤ Q) (P : ℕ → Finset Sphere)
    (hP : ∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1))))
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ U : Base ≃ₗᵢ[ℂ] Base,
      ‖iteratedFDeriv ℝ n ((fun y => ∑' j, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) y) ∘ centeredChart r U) 0‖ ≤ C := by
  obtain ⟨C,hC,hCb⟩ := logarithmicTest_chart_jets a he hn
  obtain ⟨B,hB,hBb⟩ := chartScale_sum_uniform hQ
  refine ⟨C*B,mul_nonneg hC hB,?_⟩
  intro r hr hr1 U
  let f := fun j => iteratedFDeriv ℝ n (logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ∘ centeredChart r U) 0
  have hs : Summable (fun j => C*chartScale (Q^(j+1)) (1-r)) :=
    (chartScale_summable hQ (by linarith : 0 < 1-r)).mul_left C
  have hb (j : ℕ) : ‖f j‖ ≤ C*chartScale (Q^(j+1)) (1-r) :=
    hCb hD (Nat.one_le_pow _ _ (by omega)) (hP j) hr hr1 U
  have hnS := Summable.of_nonneg_of_le (fun j => norm_nonneg (f j)) hb hs
  rw [testSeries_chart_iteratedFDeriv a he hD hQ P hP hr hr1 U n]
  exact (norm_tsum_le_tsum_norm hnS).trans ((hnS.tsum_le_tsum hb hs).trans (by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hBb (1-r) (by linarith)) hC))

end PinchedHartogs.BaseConstruction

end

end OAI
end

theorem solution : type_of% @OAI.PinchedHartogs.BaseConstruction.testSeries_chart_uniform_jets_oai := @OAI.PinchedHartogs.BaseConstruction.testSeries_chart_uniform_jets_oai
