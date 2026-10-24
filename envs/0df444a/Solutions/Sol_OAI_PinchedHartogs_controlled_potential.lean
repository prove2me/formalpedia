-- Prove2me | solution 1 for OAI.PinchedHartogs.controlled_potential
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:07:30.587036+00:00
-- url     : https://prove2.me/submissions/8342c5f6-a824-4e17-b89d-79592fb6a10b

import Mathlib
import Definitions.Def_PinchedKahler
import Definitions.Def_OAIQWPH000
import Definitions.Def_OAIQWPH001
import Theorems.Thm_OAI_PinchedHartogs_BaseConstruction_analytic_jet_bound
import Theorems.Thm_OAI_PinchedHartogs_BaseConstruction_basePotential_chart_control
import Theorems.Thm_OAI_PinchedHartogs_BaseConstruction_uniform_representing_densities

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
-- module Solutions.OAIQW_PinchedHartogs.MetricCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler1607_1 uKahler1618_1

open Set Filter Topology
open scoped ContDiff
noncomputable section

namespace PinchedHartogs

open scoped Matrix.Norms.Elementwise

lemma psi_contDiffAt {z : Base} (hz : z ∈ ball) : ContDiffAt ℝ ∞ psi z := by
  have hp : 0 < 1 - ‖z‖ ^ 2 := by
    have h := norm_nonneg z
    change ‖z‖ < 1 at hz
    nlinarith
  exact ((contDiffAt_const.sub (contDiff_norm_sq ℂ).contDiffAt).log hp.ne').neg

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

lemma base_eq_sum_single (z : Base) : z = ∑ i : Fin 2, z i • EuclideanSpace.single i 1 := by
  ext j
  fin_cases j <;> simp

lemma multilinear_diagonal_polynomial {n : ℕ} (M : ContinuousMultilinearMap ℂ (fun _ : Fin n => Base) ℂ) :
    ∃ p : MvPolynomial (Fin 2) ℂ, ∀ z : Base,
      M (fun _ => z) = MvPolynomial.eval (fun i => z i) p := by
  classical
  refine ⟨∑ r : Fin n → Fin 2, MvPolynomial.C (M (fun i => EuclideanSpace.single (r i) 1)) *
    ∏ i : Fin n, MvPolynomial.X (r i), ?_⟩
  intro z
  calc
    M (fun _ => z) = M (fun _ => ∑ j : Fin 2, z j • EuclideanSpace.single j 1) := by
      congr 1
      funext i
      exact base_eq_sum_single z
    _ = ∑ r : Fin n → Fin 2, M (fun i => z (r i) • EuclideanSpace.single (r i) 1) :=
      M.toMultilinearMap.map_sum _
    _ = ∑ r : Fin n → Fin 2, (∏ i : Fin n, z (r i)) * M (fun i => EuclideanSpace.single (r i) 1) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact M.toMultilinearMap.map_smul_univ _ _
    _ = _ := by simp [map_sum,map_mul,map_prod,mul_comm]

lemma continuous_integrable {E : Type uKahler8561_1} [NormedAddCommGroup E] {μ : Measure Sphere}
    [IsFiniteMeasure μ] {f : Sphere → E} (hf : Continuous f) : Integrable f μ := by
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

lemma Represents.multilinear_moment {μ : Measure Sphere} (hμ : Represents μ) {n : ℕ}
    (M : ContinuousMultilinearMap ℂ (fun _ : Fin n => Base) ℂ) :
    (∫ ξ : Sphere, M (fun _ => (ξ:Base)) ∂μ) = M (fun _ => 0) := by
  obtain ⟨p,hp⟩ := multilinear_diagonal_polynomial M
  simpa [hp] using hμ p

lemma Represents.partialSum_moment {μ : Measure Sphere} [IsFiniteMeasure μ] (hμ : Represents μ)
    (p : FormalMultilinearSeries ℂ Base ℂ) (n : ℕ) (c : ℂ) :
    (∫ ξ : Sphere, p.partialSum n (c • (ξ:Base)) ∂μ) = p.partialSum n 0 := by
  classical
  simp only [FormalMultilinearSeries.partialSum]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m hm
    have he : ∀ z : Base, p m (fun _ => c • z) = c^m * p m (fun _ => z) := by
      intro z
      simpa [smul_eq_mul] using (p m).toMultilinearMap.map_smul_univ (fun _ => c) (fun _ => z)
    simp_rw [he]
    rw [integral_const_mul,hμ.multilinear_moment]
    simpa using (he (0:Base)).symm
  · intro m hm
    apply continuous_integrable
    exact (p m).cont.comp (continuous_pi (fun _ => (continuous_subtype_val : Continuous (fun ξ : Sphere => (ξ:Base))).const_smul c))

lemma Represents.local_analytic_mean {μ : Measure Sphere} [IsProbabilityMeasure μ]
    (hμ : Represents μ) {H : Base → ℂ} (hH : AnalyticAt ℂ H 0) :
    (fun c : ℂ => ∫ ξ : Sphere, H (c • (ξ:Base)) ∂μ) =ᶠ[𝓝 0] fun _ => H 0 := by
  obtain ⟨p,r,hp⟩ := hH
  obtain ⟨r',hr'0,hr'r⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  obtain ⟨a,ha,C,hC,hbound⟩ := hp.uniform_geometric_approx hr'r
  have hr' : 0 < (r':ℝ) := by exact_mod_cast hr'0
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) hr'] with c hc
  have hc' : ‖c‖ < r' := by simpa using hc
  have hm : ∀ n : ℕ, ‖(∫ ξ : Sphere, H (c • (ξ:Base)) ∂μ)-H 0‖ ≤ C*a^(n+1) := by
    intro n
    have hint : Integrable (fun ξ : Sphere => H (c • (ξ:Base))) μ := by
      apply continuous_integrable
      apply hp.continuousOn.comp_continuous (f := fun ξ : Sphere => c • (ξ:Base))
        ((continuous_subtype_val : Continuous (fun ξ : Sphere => (ξ:Base))).const_smul c)
      intro ξ
      rw [mem_eball_zero_iff]
      calc
        ‖c • (ξ:Base)‖ₑ = ↑(‖c‖₊) := by
          change ((‖c • (ξ:Base)‖₊:ℝ≥0∞)) = _
          congr 1
          apply NNReal.coe_injective
          simp [norm_smul]
        _ < ↑r' := by exact_mod_cast hc'
        _ < r := hr'r
    have hintp : Integrable (fun ξ : Sphere => p.partialSum (n+1) (c • (ξ:Base))) μ := by
      apply continuous_integrable
      exact (p.partialSum_continuous _).comp ((continuous_subtype_val : Continuous (fun ξ : Sphere => (ξ:Base))).const_smul c)
    have hzero : p.partialSum (n+1) 0 = H 0 := by
      simp only [FormalMultilinearSeries.partialSum]
      rw [Finset.sum_eq_single 0]
      · exact hp.coeff_zero _
      · intro m hm hm0
        exact (p m).map_coord_zero ⟨0, Nat.pos_of_ne_zero hm0⟩ rfl
      · simp
    rw [← hzero, ← hμ.partialSum_moment p (n+1) c, ← integral_sub hint hintp]
    refine (norm_integral_le_of_norm_le_const (C := C*a^(n+1)) ?_).trans_eq (by simp)
    filter_upwards [] with ξ
    simpa using hbound (c • (ξ:Base)) (by simpa [norm_smul] using hc') (n+1)
  have hlim : Tendsto (fun n : ℕ => C*a^(n+1)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul ((tendsto_pow_atTop_nhds_zero_of_lt_one ha.1.le ha.2).comp (tendsto_add_atTop_nat 1))
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hm)) (norm_nonneg _)))

lemma radial_mem_ball {c : ℂ} (hc : ‖c‖ < 1) (ξ : Sphere) : c • (ξ:Base) ∈ ball := by
  simpa [ball,norm_smul] using hc

lemma radial_continuous {H : Base → ℂ} (hH : ContinuousOn H ball) {c : ℂ} (hc : ‖c‖ < 1) :
    Continuous (fun ξ : Sphere => H (c • (ξ:Base))) :=
  hH.comp_continuous
    ((continuous_subtype_val : Continuous (fun ξ : Sphere => (ξ:Base))).const_smul c)
    (radial_mem_ball hc)

lemma analytic_radial_integral {μ : Measure Sphere} [IsFiniteMeasure μ]
    {H : Base → ℂ} (hH : AnalyticOnNhd ℂ H ball) :
    AnalyticOnNhd ℂ (fun c : ℂ => ∫ ξ : Sphere, H (c • (ξ:Base)) ∂μ) (Metric.ball 0 1) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  intro c hc
  have hc' : ‖c‖ < 1 := by simpa using hc
  obtain ⟨R,hcR,hR1⟩ := exists_between hc'
  have hR0 : 0 < R := (norm_nonneg _).trans_lt hcR
  have hsubset : Metric.closedBall (0:Base) R ⊆ ball := by
    intro z hz
    exact (show ‖z‖ ≤ R by simpa using hz).trans_lt hR1
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:Base) R).bddAbove_image
    (hH.fderiv.continuousOn.norm.mono hsubset)
  let F' : ℂ → Sphere → ℂ := fun d ξ => fderiv ℂ H (d • (ξ:Base)) (ξ:Base)
  have hF' : ∀ d : ℂ, ‖d‖ < 1 → Continuous (F' d) := by
    intro d hd
    exact ((hH.fderiv.continuousOn.comp_continuous
      ((continuous_subtype_val : Continuous (fun ξ : Sphere => (ξ:Base))).const_smul d)
      (radial_mem_ball hd)).clm_apply continuous_subtype_val)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun d : ℂ => fun ξ : Sphere => H (d • (ξ:Base)))
    (F' := F') (bound := fun _ => C) (s := Metric.ball 0 R)
    (Metric.isOpen_ball.mem_nhds (by simpa using hcR))
    (?_) (continuous_integrable (radial_continuous hH.continuousOn hc'))
    ((hF' c hc').aestronglyMeasurable) (?_) (integrable_const C) (?_)
  · exact hd.2.differentiableAt.differentiableWithinAt
  · filter_upwards [Metric.isOpen_ball.mem_nhds (show c ∈ Metric.ball (0:ℂ) R by simpa using hcR)] with d hd
    exact (radial_continuous hH.continuousOn
      ((show ‖d‖ < R by simpa using hd).trans hR1)).aestronglyMeasurable
  · filter_upwards [] with ξ d hd
    have hdR : ‖d‖ < R := by simpa using hd
    calc
      ‖F' d ξ‖ ≤ ‖fderiv ℂ H (d • (ξ:Base))‖ * ‖(ξ:Base)‖ := (fderiv ℂ H _).le_opNorm _
      _ = ‖fderiv ℂ H (d • (ξ:Base))‖ := by simp
      _ ≤ C := hC (mem_image_of_mem _ (by simpa [norm_smul] using hdR.le))
  · filter_upwards [] with ξ d hd
    have ha := (hH (d • (ξ:Base)) (radial_mem_ball
      ((show ‖d‖ < R by simpa using hd).trans hR1) ξ)).differentiableAt
    convert ha.hasFDerivAt.comp_hasDerivAt d ((hasDerivAt_id d).smul_const (ξ:Base)) using 1 <;> simp [F',Function.comp_def]

lemma Represents.analytic_mean {μ : Measure Sphere} [IsProbabilityMeasure μ]
    (hμ : Represents μ) {H : Base → ℂ} (hH : AnalyticOnNhd ℂ H ball) {c : ℂ} (hc : ‖c‖ < 1) :
    (∫ ξ : Sphere, H (c • (ξ:Base)) ∂μ) = H 0 := by
  have he := (analytic_radial_integral hH).eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_const (v := H 0)) (convex_ball (0:ℂ) 1).isPreconnected
    (show (0:ℂ) ∈ Metric.ball 0 1 by simp)
    (hμ.local_analytic_mean (hH 0 (by simp [ball])))
  exact he (by simpa using hc)

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
lemma projectiveDistance_self (ξ : Sphere) : projectiveDistance ξ ξ = 0 := by
  simp [projectiveDistance_eq_dist]

lemma projectiveDistance_continuous (p : Sphere) : Continuous (fun ξ => projectiveDistance ξ p) := by
  simpa only [projectiveDistance_eq_dist] using bloch_continuous.dist continuous_const

lemma bracket_norm_le_one (ξ p : Sphere) : ‖bracket (ξ:Base) (p:Base)‖ ≤ 1 := by
  simpa only [bracket,sphere_norm,one_mul] using norm_inner_le_norm (p:Base) (ξ:Base)

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

lemma separated_card_bound {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {P : Finset Sphere} (hP : ProjectivelySeparated ρ P) :
    (P.card:ℝ) ≤ 4/ρ^2 := by
  have hu := measureReal_mono (μ := sigma) (subset_univ (⋃ p ∈ P, projectiveCap p (ρ/2)))
  rw [measureReal_biUnion_finset (separated_caps_disjoint hP) (fun p _ => projectiveCap_measurable p _)] at hu
  simp_rw [projectiveCap_real _ (by linarith : 0 ≤ ρ/2) (by linarith : ρ/2 ≤ 1)] at hu
  simp only [Finset.sum_const,nsmul_eq_mul] at hu
  have hu1 : sigma.real univ = 1 := by simp [measureReal_def]
  rw [hu1] at hu
  apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
  linarith

lemma covering_card_bound {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {P : Finset Sphere} (hP : ProjectiveCover ρ P) :
    1 ≤ (P.card:ℝ)*ρ^2 := by
  have he : (⋃ p ∈ P, projectiveCap p ρ) = univ := by
    ext ξ
    constructor
    · exact fun _ => mem_univ _
    · intro _
      obtain ⟨p,hp,hd⟩ := hP ξ
      exact mem_iUnion₂.mpr ⟨p,hp,hd⟩
  have hu := measureReal_biUnion_finset_le (μ := sigma) P (fun p => projectiveCap p ρ)
  rw [he] at hu
  have hu1 : sigma.real univ = 1 := by simp [measureReal_def]
  rw [hu1] at hu
  simpa only [projectiveCap_real _ hρ hρ1,Finset.sum_const,nsmul_eq_mul] using hu

lemma exists_separated_cover {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ P : Finset Sphere, ProjectivelySeparated ρ P ∧ ProjectiveCover ρ P := by
  classical
  let N := ⌈4/ρ^2⌉₊
  let B (n : ℕ) := ∃ P : Finset Sphere, ProjectivelySeparated ρ P ∧ P.card = n
  have hbound : ∀ P : Finset Sphere, ProjectivelySeparated ρ P → P.card ≤ N := by
    intro P hP
    exact_mod_cast (separated_card_bound hρ hρ1 hP).trans (Nat.le_ceil _)
  have hzero : B 0 := ⟨∅,by simp [ProjectivelySeparated],rfl⟩
  obtain ⟨P,hP,hcard⟩ := Nat.findGreatest_spec (Nat.zero_le N) hzero
  refine ⟨P,hP,?_⟩
  intro ξ
  by_contra hn
  push Not at hn
  have hξ : ξ ∉ P := by
    intro h
    have := hn ξ h
    rw [projectiveDistance_self] at this
    linarith
  have hi : ProjectivelySeparated ρ (insert ξ P) := by
    intro p hp q hq hpq
    rcases Finset.mem_insert.mp hp with he|hpp
    · subst p
      rcases Finset.mem_insert.mp hq with he|hqq
      · exact (hpq he.symm).elim
      · exact hn q hqq
    · rcases Finset.mem_insert.mp hq with he|hqq
      · subst q; rw [projectiveDistance_symm]; exact hn p hpp
      · exact hP p hpp q hqq hpq

  have hb : B (P.card+1) := ⟨insert ξ P,hi,Finset.card_insert_of_notMem hξ⟩
  have hle : P.card+1 ≤ N := by simpa only [Finset.card_insert_of_notMem hξ] using hbound (insert ξ P) hi
  have := Nat.le_findGreatest hle hb
  omega

lemma peak_count {D : ℝ} (hD : 1 ≤ D) {k : ℕ} (hk : D^2 ≤ k)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P)
    (hcover : ProjectiveCover (D/Real.sqrt k) P) :
    (k:ℝ)/D^2 ≤ P.card ∧ (P.card:ℝ) ≤ 4*k/D^2 := by
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hk0 : (0:ℝ) < k := lt_of_lt_of_le (sq_pos_of_pos hD0) hk
  have hs : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr hk0
  have hρ : 0 < D/Real.sqrt (k:ℝ) := div_pos hD0 hs
  have hρ1 : D/Real.sqrt (k:ℝ) ≤ 1 := by
    apply (div_le_one hs).mpr
    exact (Real.le_sqrt hD0.le hk0.le).mpr hk
  have hu := separated_card_bound hρ hρ1 hP
  have hl := covering_card_bound hρ.le hρ1 hcover
  have he : (D/Real.sqrt (k:ℝ))^2 = D^2/k := by rw [div_pow,Real.sq_sqrt hk0.le]
  rw [he] at hu hl
  constructor
  · apply (div_le_iff₀ (sq_pos_of_pos hD0)).mpr
    have := (le_div_iff₀ hk0).mp (show 1 ≤ (P.card:ℝ)*D^2/k by simpa only [mul_div_assoc] using hl)
    linarith
  · convert hu using 1
    field_simp

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

lemma norm_coordinate_integral (k : ℕ) :
    (∫ ξ, ‖(ξ:Base) 0‖^k ∂sigma) = 2/(k+2:ℝ) := by
  let f : C(unitInterval,ℝ) := ⟨fun t => (Real.sqrt (t:ℝ))^k,by fun_prop⟩
  have hf := radial_continuous_integral f
  have he : ∀ ξ : Sphere, f (radialUnit ξ) = ‖(ξ:Base) 0‖^k := by
    intro ξ
    simp [f,radialUnit,radialU,Complex.normSq_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]
  simp_rw [he] at hf
  rw [hf]
  change (∫ t : unitInterval, (Real.sqrt (t:ℝ))^k) = _
  rw [unitInterval.volume_def,integral_subtype_comap measurableSet_Icc (fun t : ℝ => (Real.sqrt t)^k)]
  have hr : ∀ t ∈ Icc (0:ℝ) 1, (Real.sqrt t)^k = t^((k:ℝ)/2) := by
    intro t ht
    rw [Real.sqrt_eq_rpow,← Real.rpow_natCast,← Real.rpow_mul ht.1]
    congr 1
    ring
  rw [setIntegral_congr_fun measurableSet_Icc hr,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),integral_rpow (Or.inl (by linarith [Nat.cast_nonneg (α := ℝ) k] : -1 < (k:ℝ)/2))]
  rw [Real.one_rpow,Real.zero_rpow (by positivity : (k:ℝ)/2+1 ≠ 0)]
  field_simp
  ring

lemma single_peak_integral (p : Sphere) (k : ℕ) :
    (∫ ξ, ‖bracket (ξ:Base) (p:Base)‖^k ∂sigma) = 2/(k+2:ℝ) := by
  have h := sigma_integral_unitary (adaptedIsometry p) (fun ξ : Sphere => ‖(ξ:Base) 0‖^k)
  simpa only [sphereAction_coe,adaptedIsometry_zero,norm_coordinate_integral] using h

lemma peak_integral_bound (P : Finset Sphere) (k : ℕ) :
    (∫ ξ, ‖peakPolynomial P k (ξ:Base)‖ ∂sigma) ≤ 2*P.card/(k+2:ℝ) := by
  have hcont : Continuous (fun ξ : Sphere => ‖peakPolynomial P k (ξ:Base)‖) :=
    ((peakPolynomial_analytic P k).continuous.comp continuous_subtype_val).norm
  have hpc : ∀ p ∈ P, Continuous (fun ξ : Sphere => ‖bracket (ξ:Base) (p:Base)‖^k) := by
    intro p hp
    exact (((bracket_analytic (p:Base)).continuous.comp continuous_subtype_val).norm).pow k
  calc
    _ ≤ ∫ ξ, ∑ p ∈ P, ‖bracket (ξ:Base) (p:Base)‖^k ∂sigma := by
      apply integral_mono (continuous_integrable hcont)
        (continuous_integrable (continuous_finsetSum _ hpc))
      intro ξ
      exact (norm_sum_le _ _).trans_eq (by simp only [norm_pow])
    _ = ∑ p ∈ P, ∫ ξ, ‖bracket (ξ:Base) (p:Base)‖^k ∂sigma := MeasureTheory.integral_finsetSum _ (fun p hp => continuous_integrable (hpc p hp))
    _ = _ := by simp only [single_peak_integral,Finset.sum_const,nsmul_eq_mul]; ring

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseLocalSmoothSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler10013_1 uKahler10013_2 uKahler10035_1 uKahler10035_2 uKahler9999_1 uKahler9999_2

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

lemma local_jet_series_derivative {E : Type uKahler9999_1} {F : Type uKahler9999_2} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℕ → E → F} (hf : ∀ j, ContDiff ℝ ∞ (f j))
    {s : Set E} (hs : IsOpen s) (hc : IsPreconnected s) {x : E} (hx : x ∈ s)
    {v : ℕ → ℕ → ℝ} (hv : ∀ n, Summable (v n))
    (hb : ∀ n j y, y ∈ s → ‖iteratedFDeriv ℝ n (f j) y‖ ≤ v n j) (n : ℕ) :
    HasFDerivAt (fun y => ∑' j, iteratedFDeriv ℝ n (f j) y)
      (∑' j, fderiv ℝ (iteratedFDeriv ℝ n (f j)) x) x := by
  apply hasFDerivAt_tsum_of_isPreconnected (hv (n+1)) hs hc
    (fun j y _ => ((hf j).differentiable_iteratedFDeriv (by exact_mod_cast (ENat.natCast_lt_top n))).differentiableAt.hasFDerivAt)
    (fun j y hy => ?_) hx
    (Summable.of_norm_bounded (hv n) (fun j => hb n j x hx)) hx
  simpa only [norm_fderiv_iteratedFDeriv] using hb (n+1) j y hy

lemma local_iteratedFDeriv_tsum {E : Type uKahler10013_1} {F : Type uKahler10013_2} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℕ → E → F} (hf : ∀ j, ContDiff ℝ ∞ (f j))
    {s : Set E} (hs : IsOpen s) (hc : IsPreconnected s)
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
    rw [he.fderiv_eq,(local_jet_series_derivative hf hs hc hx hv hb n).fderiv]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) F).symm.toContinuousLinearEquiv.map_tsum

lemma local_contDiff_tsum {E : Type uKahler10035_1} {F : Type uKahler10035_2} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℕ → E → F} (hf : ∀ j, ContDiff ℝ ∞ (f j))
    {s : Set E} (hs : IsOpen s) (hc : IsPreconnected s)
    {v : ℕ → ℕ → ℝ} (hv : ∀ n, Summable (v n))
    (hb : ∀ n j y, y ∈ s → ‖iteratedFDeriv ℝ n (f j) y‖ ≤ v n j) :
    ContDiffOn ℝ ∞ (fun y => ∑' j, f j y) s := by
  apply contDiffOn_of_differentiableOn
  intro n hn x hx
  have he : iteratedFDerivWithin ℝ n (fun y => ∑' j, f j y) s =ᶠ[𝓝 x]
      (fun y => ∑' j, iteratedFDeriv ℝ n (f j) y) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    rw [iteratedFDerivWithin_of_isOpen n hs hy]
    exact local_iteratedFDeriv_tsum hf hs hc hv hb n hy
  exact ((local_jet_series_derivative hf hs hc hx hv hb n).differentiableAt.congr_of_eventuallyEq he).differentiableWithinAt

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

lemma logarithmicTest_local_jets (a : ℝ) {ε D r R : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D)
    (hr : 0 ≤ r) (hrR : r < R) (hR1 : R < 1) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ P : Finset Sphere,
      ProjectivelySeparated (D/Real.sqrt k) P → ∀ z ∈ Metric.ball (0:Base) r,
      ‖iteratedFDeriv ℝ n (logarithmicTest a ε P k) z‖ ≤ C*R^k := by
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  have hG : 0 < gaussianConstant := gaussianConstant_pos
  by_cases hn : n=0
  · subst n
    obtain ⟨C,hC,hCb⟩ := regularizedLog_lipschitz_bound a he hG.le
    refine ⟨C*gaussianConstant,by positivity,?_⟩
    intro k hk P hP z hz
    have hzn : ‖z‖ ≤ R := (show ‖z‖ < r by simpa using hz).le.trans hrR.le
    have hp := (peak_global_bound hD hk hP z).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hzn _) hG.le)
    have hpG : ‖peakPolynomial P k z‖ ≤ gaussianConstant := hp.trans (by
      exact mul_le_of_le_one_right hG.le (pow_le_one₀ hR.le hR1.le))
    rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs]
    exact (hCb _ hpG).trans ((mul_le_mul_of_nonneg_left hp hC).trans_eq (by ring))
  · let ρ : ℝ := (R-r)/2
    have hρ : 0 < ρ := by dsimp [ρ]; linarith
    obtain ⟨C,hC,hCb⟩ := regularizedLog_positive_jet_bound a he hρ hG.le
      (by positivity : 0 ≤ 2*gaussianConstant) (by omega : 1 ≤ n)
    refine ⟨C,hC,?_⟩
    intro k hk P hP z hz
    have hzn : ‖z‖ < r := by simpa using hz
    have hpr (x : Base) (hx : ‖x‖ ≤ R) : ‖peakPolynomial P k x‖ ≤ gaussianConstant*R^k :=
      (peak_global_bound hD hk hP x).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx _) hG.le)
    have hnormz := hpr z (by linarith)
    have hpG : ‖peakPolynomial P k z‖ ≤ gaussianConstant := hnormz.trans
      (mul_le_of_le_one_right hG.le (pow_le_one₀ hR.le hR1.le))
    apply hCb (peakPolynomial P k) z (R^k) ((peakPolynomial_analytic P k).mono (subset_univ _)) hpG
      (pow_pos hR _) (pow_le_one₀ hR.le hR1.le)
    intro x hx
    have hdist : dist x z < ρ := hx
    have htriangle := dist_triangle x z 0
    have hxR : ‖x‖ ≤ R := by rw [dist_zero_right,dist_zero_right] at htriangle; dsimp [ρ] at hdist; linarith
    exact (norm_sub_le _ _).trans (by linarith [hpr x hxR])

lemma testSeries_contDiffOn (a : ℝ) {ε D : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D)
    {Q : ℕ} (hQ : 2 ≤ Q) (P : ℕ → Finset Sphere)
    (hP : ∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1)))) :
    ContDiffOn ℝ ∞ (fun z => ∑' j, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) z) ball := by
  intro z hz
  have hz1 : ‖z‖ < 1 := hz
  let r := (‖z‖+1)/2
  let R := (r+1)/2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hzR : z ∈ Metric.ball 0 r := by simpa [r] using (by linarith : ‖z‖ < (‖z‖+1)/2)
  choose C hC hb using (fun n => logarithmicTest_local_jets a he hD hr hrR hR1 n)
  have hs := local_contDiff_tsum (fun j => logarithmicTest_contDiff a he _ _)
    Metric.isOpen_ball (convex_ball (0:Base) r).isPreconnected
    (fun n => (summable_lacunary (hr.trans hrR.le) hR1 hQ).mul_left (C n))
    (fun n j y hy => hb n (Q^(j+1)) (Nat.one_le_pow _ _ (by omega)) _ (hP j) y hy)
  exact (hs.contDiffAt (Metric.isOpen_ball.mem_nhds hzR)).contDiffWithinAt

lemma basePotential_contDiffOn (a L : ℝ) {ε D : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D)
    {Q : ℕ} (hQ : 2 ≤ Q) (P : ℕ → Finset Sphere)
    (hP : ∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1)))) :
    ContDiffOn ℝ ∞ (basePotential P a ε L Q) ball := by
  apply ContDiffOn.add (fun z hz => (psi_contDiffAt hz).contDiffWithinAt)
  exact contDiffOn_const.mul (testSeries_contDiffOn a he hD hQ P hP)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseHopf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler10884_1 uKahler10884_2 uKahler10889_1 uKahler10889_2 uKahler10889_3

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

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma exists_circle_norm_factor (z : ℂ) : ∃ a : Circle, (a:ℂ)*(‖z‖:ℂ) = z := by
  by_cases hz : z = 0
  · subst z; exact ⟨1,by simp⟩
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  refine ⟨⟨z/(‖z‖:ℂ),?_⟩,?_⟩
  · apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),div_self hn]
  · exact div_mul_cancel₀ z (by exact_mod_cast hn)

lemma compact_continuous_integrable {X : Type uKahler10884_1} {E : Type uKahler10884_2} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → E} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePhaseFourier
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
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma phaseChar_add (n m : ℤ) (z : Circle) : phaseChar (n+m) z=phaseChar n z*phaseChar m z := by
  simp [phaseChar,zpow_add]
lemma phaseChar_exp (n : ℤ) (t : ℝ) : phaseChar n (Circle.exp t)=Complex.exp ((n:ℂ)*t*Complex.I) := by
  simp only [phaseChar,Circle.coe_zpow,Circle.coe_exp,← Complex.exp_int_mul]
  congr 1
  ring
lemma phaseChar_continuous (n : ℤ) : Continuous (phaseChar n) := by
  exact continuous_subtype_val.comp (continuous_id.zpow n)

lemma circle_char_mean (n : ℤ) : (∫ z, phaseChar n z ∂circleMeasure) = if n=0 then 1 else 0 := by
  by_cases hn : n=0
  · subst n; simp
  rw [ite_eq_right hn]
  let w := Circle.exp (Real.pi/(n:ℝ))
  have hw : phaseChar n w = -1 := by
    rw [phaseChar_exp]
    have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast hn
    have hh : (n:ℂ)*(Real.pi/(n:ℝ):ℝ)*Complex.I = Real.pi*Complex.I := by push_cast; field_simp
    rw [hh,Complex.exp_pi_mul_I]
  apply integral_eq_zero_of_mul_left_eq_neg (g := w)
  intro z
  rw [phaseChar_mul,hw,neg_one_mul]

lemma phaseSum_continuous (s : Finset ℤ) (a : ℤ → ℂ) : Continuous (phaseSum s a) :=
  continuous_finsetSum _ (fun n _ => continuous_const.mul (phaseChar_continuous n))

lemma phaseSum_mean (s : Finset ℤ) (a : ℤ → ℂ) :
    (∫ z, phaseSum s a z ∂circleMeasure) = if 0 ∈ s then a 0 else 0 := by
  classical
  unfold phaseSum
  rw [MeasureTheory.integral_finsetSum s (fun n _ => (compact_continuous_integrable (phaseChar_continuous n)).const_mul (a n))]
  simp_rw [integral_const_mul,circle_char_mean]
  simp

lemma phaseBandwidth_one : PhaseBandwidth (fun _ => 1) 0 := by
  intro p
  refine ⟨{0},fun _ => 1,?_,?_⟩
  · intro n hn; have hn0 : n=0 := Finset.mem_singleton.mp hn; simp [hn0]
  · intro z; simp [phaseSum]

lemma orbitMean_one : OrbitMeanOne (fun _ => 1) := by intro p; simp

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePhaseSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler11043_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma mem_phaseBand (ℓ : ℕ) (n : ℤ) : n ∈ phaseBand ℓ ↔ |n| ≤ (ℓ:ℤ) := by simp [phaseBand,abs_le]

lemma phaseSum_extend {s t : Finset ℤ} (hst : s ⊆ t) (a : ℤ → ℂ) (z : Circle) :
    phaseSum s a z = phaseSum t (fun n => if n ∈ s then a n else 0) z := by
  classical
  unfold phaseSum
  calc
    _ = ∑ n ∈ s, (if n ∈ s then a n else 0)*phaseChar n z := by
      apply Finset.sum_congr rfl; intro n hn; simp [hn]
    _ = _ := Finset.sum_subset hst (fun n _ hn => by simp [hn])

lemma phaseBandwidth_band {W : Base → ℝ} {ℓ : ℕ} (hW : PhaseBandwidth W ℓ) (p : Sphere) :
    ∃ a : ℤ → ℂ, ∀ z : Circle, (W ((z:ℂ) • (p:Base)):ℂ) = phaseSum (phaseBand ℓ) a z := by
  classical
  obtain ⟨s,a,hs,he⟩ := hW p
  refine ⟨fun n => if n ∈ s then a n else 0,?_⟩
  intro z
  rw [he]
  exact phaseSum_extend (fun n hn => (mem_phaseBand ℓ n).mpr (hs n hn)) a z

lemma phaseBandwidth_mono {W : Base → ℝ} {ℓ m : ℕ} (hW : PhaseBandwidth W ℓ) (hℓ : ℓ ≤ m) :
    PhaseBandwidth W m := by
  intro p
  obtain ⟨s,a,hs,he⟩ := hW p
  exact ⟨s,a,fun n hn => le_trans (hs n hn) (by exact_mod_cast hℓ),he⟩

lemma phaseBandwidth_add {W V : Base → ℝ} {ℓ : ℕ} (hW : PhaseBandwidth W ℓ) (hV : PhaseBandwidth V ℓ) :
    PhaseBandwidth (fun z => W z+V z) ℓ := by
  intro p
  obtain ⟨a,ha⟩ := phaseBandwidth_band hW p
  obtain ⟨b,hb⟩ := phaseBandwidth_band hV p
  refine ⟨phaseBand ℓ,fun n => a n+b n,fun n hn => (mem_phaseBand ℓ n).mp hn,?_⟩
  intro z
  simp only [Complex.ofReal_add,ha,hb,phaseSum,add_mul,Finset.sum_add_distrib]

lemma phaseBandwidth_zero (ℓ : ℕ) : PhaseBandwidth (fun _ => 0) ℓ := by
  intro p
  exact ⟨∅,fun _ => 0,by simp,by simp [phaseSum]⟩

lemma phaseBandwidth_sum {ι : Type uKahler11043_1} (s : Finset ι) (W : ι → Base → ℝ) {ℓ : ℕ}
    (hW : ∀ i ∈ s, PhaseBandwidth (W i) ℓ) : PhaseBandwidth (fun z => ∑ i ∈ s, W i z) ℓ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using phaseBandwidth_zero ℓ
  | @insert a s ha ih =>
    simpa [Finset.sum_insert ha] using phaseBandwidth_add (hW a (by simp))
      (ih (fun i hi => hW i (by simp [hi])))

lemma phaseChar_conj (n : ℤ) (z : Circle) : star (phaseChar n z)=phaseChar (-n) z := by
  unfold phaseChar
  rw [zpow_neg,Circle.coe_inv_eq_conj]
  rfl

lemma phaseSum_shift (s : Finset ℤ) (a : ℤ → ℂ) (k : ℤ) (z : Circle) :
    (∑ n ∈ s, a n*phaseChar (k+n) z) =
      phaseSum (s.image (fun n => k+n)) (fun m => a (m-k)) z := by
  classical
  unfold phaseSum
  rw [Finset.sum_image (s := s) (g := fun n : ℤ => k+n) (fun n _ m _ he => add_left_cancel he)]
  apply Finset.sum_congr rfl
  intro n hn
  congr 2
  omega

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePhaseReal
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
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma phaseSum_conj (s : Finset ℤ) (a : ℤ → ℂ) (z : Circle) :
    star (phaseSum s a z) = phaseSum (s.image Neg.neg) (fun n => star (a (-n))) z := by
  classical
  unfold phaseSum
  rw [star_sum]
  simp only [star_mul,phaseChar_conj]
  rw [Finset.sum_image (s := s) (g := Neg.neg) (fun n _ m _ he => neg_injective he)]
  simp [mul_comm]

lemma phaseSum_real_band {s : Finset ℤ} {ℓ : ℕ} (hs : ∀ n ∈ s, |n| ≤ (ℓ:ℤ))
    (a : ℤ → ℂ) : ∃ b : ℤ → ℂ, ∀ z : Circle,
      ((phaseSum s a z).re:ℂ) = phaseSum (phaseBand ℓ) b z := by
  classical
  let t := s.image Neg.neg
  let a' : ℤ → ℂ := fun n => if n ∈ s then a n else 0
  let b' : ℤ → ℂ := fun n => if n ∈ t then star (a (-n)) else 0
  have hs' : s ⊆ phaseBand ℓ := fun n hn => (mem_phaseBand ℓ n).mpr (hs n hn)
  have ht' : t ⊆ phaseBand ℓ := by
    intro n hn
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    exact (mem_phaseBand ℓ (-m)).mpr (by simpa using hs m hm)
  refine ⟨fun n => (a' n + b' n)/2,?_⟩
  intro z
  have hr : ((phaseSum s a z).re:ℂ) = (phaseSum s a z+star (phaseSum s a z))/2 := by
    apply Complex.ext <;> simp
  rw [hr,phaseSum_conj,phaseSum_extend hs' a z,phaseSum_extend ht' (fun n => star (a (-n))) z]
  simp only [phaseSum,← Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp [a',b',t]
  ring

lemma phaseSum_integral {s : Finset ℤ} (a : ℤ → ℂ) (hs : 0 ∉ s) :
    (∫ z : Circle, phaseSum s a z ∂circleMeasure) = 0 := by
  rw [phaseSum_mean,ite_eq_right hs]

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePhaseMoments
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
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma real_cast_eq_conj (z : ℂ) : (z.re:ℂ)=(z+star z)/2 := by
  apply Complex.ext <;> simp

lemma phase_real_moment (a : ℂ) (m : ℤ) (n : ℕ) (hm : 0 < m) :
    (∫ z : Circle, phaseChar n z*((a*phaseChar m z).re:ℂ) ∂circleMeasure) =
      if m=(n:ℤ) then star a/2 else 0 := by
  have he : ∀ z : Circle, phaseChar n z*((a*phaseChar m z).re:ℂ) =
      (a/2)*phaseChar ((n:ℤ)+m) z + (star a/2)*phaseChar ((n:ℤ)-m) z := by
    intro z
    rw [real_cast_eq_conj,star_mul,phaseChar_conj]
    rw [phaseChar_add,sub_eq_add_neg,phaseChar_add]
    ring
  simp_rw [he]
  rw [integral_add]
  · rw [integral_const_mul,integral_const_mul,circle_char_mean,circle_char_mean]
    have hplus : (n:ℤ)+m ≠ 0 := by omega
    rw [ite_eq_right hplus,mul_zero,zero_add]
    by_cases heq : m=(n:ℤ)
    · simp [heq]
    · have hminus : (n:ℤ)-m ≠ 0 := by omega
      simp [hminus,heq]
  · exact (compact_continuous_integrable (phaseChar_continuous _)).const_mul _
  · exact (compact_continuous_integrable (phaseChar_continuous _)).const_mul _

lemma phase_real_sum_moment (s : Finset ℤ) (a : ℤ → ℂ) (n : ℕ)
    (hs : ∀ m ∈ s, 0 < m) :
    (∫ z : Circle, phaseChar n z*((phaseSum s a z).re:ℂ) ∂circleMeasure) =
      ∑ m ∈ s, if m=(n:ℤ) then star (a m)/2 else 0 := by
  classical
  have he : ∀ z : Circle, phaseChar n z*((phaseSum s a z).re:ℂ) =
      ∑ m ∈ s, phaseChar n z*((a m*phaseChar m z).re:ℂ) := by
    intro z
    simp only [phaseSum,Complex.re_sum,Complex.ofReal_sum,Finset.mul_sum]
  simp_rw [he]
  rw [MeasureTheory.integral_finsetSum s (fun m hm => compact_continuous_integrable (by
    exact (phaseChar_continuous _).mul (Complex.continuous_ofReal.comp
      (Complex.continuous_re.comp (continuous_const.mul (phaseChar_continuous _))))))]
  exact Finset.sum_congr rfl (fun m hm => phase_real_moment _ _ _ (hs m hm))

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseProfiles
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
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma cosh_strict_quadratic {x : ℝ} (hx : 0 < x) : x^2 < 2*(Real.cosh x-1) := by
  have hh := (Real.hasSum_cosh x).summable.sum_le_tsum (Finset.range 3) (fun n hn => by positivity)
  rw [(Real.hasSum_cosh x).tsum_eq] at hh
  norm_num [Finset.sum_range_succ] at hh
  linarith [pow_pos hx 4]

lemma exists_profile_amplitude {a : ℝ} (ha : 1 < a) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ (Real.log a)^2-2*s*(Real.cosh (Real.log a)-1) < 0 := by
  have hα := Real.log_pos ha
  have hq := cosh_strict_quadratic hα
  have hd : 0 < 2*(Real.cosh (Real.log a)-1) := lt_of_le_of_lt (sq_nonneg _) hq
  have hr : (Real.log a)^2/(2*(Real.cosh (Real.log a)-1)) < 1 := (div_lt_one hd).mpr hq
  obtain ⟨s,hs,hs1⟩ := exists_between hr
  refine ⟨s,lt_of_le_of_lt (div_nonneg (sq_nonneg _) hd.le) hs,hs1,?_⟩
  have hh := (div_lt_iff₀ hd).mp hs
  linarith

lemma profile_transition_width {a s : ℝ} (ha : 1 < a) (ha2 : a < 2) (hs : 0 < s) (hs1 : s < 1) :
    ∃ δ : ℝ, 0 < δ ∧ s*(1-Real.exp (-(Real.log a+δ))) < Real.exp (-(Real.log a+3*δ)) := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have he : Real.exp (-Real.log a) = a⁻¹ := by rw [Real.exp_neg,Real.exp_log ha0]
  have hi : (1:ℝ)/2 < a⁻¹ := by
    have hh := (one_div_lt_one_div_of_lt ha0 ha2)
    simpa only [one_div] using hh
  have hi1 : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha
  have hzero : s*(1-Real.exp (-(Real.log a+0))) < Real.exp (-(Real.log a+3*0)) := by
    simp only [add_zero,mul_zero,he]
    nlinarith
  have hc1 : ContinuousAt (fun d : ℝ => s*(1-Real.exp (-(Real.log a+d)))) 0 := by fun_prop
  have hc2 : ContinuousAt (fun d : ℝ => Real.exp (-(Real.log a+3*d))) 0 := by fun_prop
  obtain ⟨ε,hε,heps⟩ := Metric.eventually_nhds_iff.mp (hc1.eventually_lt hc2 hzero)
  refine ⟨ε/2,by positivity,heps ?_⟩
  simp only [dist_zero_right,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < ε/2)]
  linarith

lemma leftCut_smooth (α δ : ℝ) : ContDiff ℝ ∞ (leftCut α δ) := by
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ))
lemma rightCut_smooth (α δ R : ℝ) : ContDiff ℝ ∞ (rightCut α δ R) := by
  exact (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ)).mul
    (contDiff_const.sub (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ)))

lemma leftCut_bounds (α δ y : ℝ) : 0 ≤ leftCut α δ y ∧ leftCut α δ y ≤ 1 := by
  unfold leftCut
  constructor <;> linarith [Real.smoothTransition.nonneg ((y-α)/δ),Real.smoothTransition.le_one ((y-α)/δ)]
lemma rightCut_bounds (α δ R y : ℝ) : 0 ≤ rightCut α δ R y ∧ rightCut α δ R y ≤ 1 := by
  have h1 := Real.smoothTransition.nonneg ((y-(α+2*δ))/δ)
  have h2 := Real.smoothTransition.le_one ((y-(α+2*δ))/δ)
  have h3 := Real.smoothTransition.nonneg ((y-R)/δ)
  have h4 := Real.smoothTransition.le_one ((y-R)/δ)
  unfold rightCut
  constructor
  · positivity
  · nlinarith

lemma leftCut_one {α δ y : ℝ} (hδ : 0 < δ) (hy : y ≤ α) : leftCut α δ y = 1 := by
  rw [leftCut, Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)]
  ring
lemma leftCut_zero {α δ y : ℝ} (hδ : 0 < δ) (hy : α+δ ≤ y) : leftCut α δ y = 0 := by
  rw [leftCut, Real.smoothTransition.one_of_one_le ((le_div_iff₀ hδ).mpr (by linarith))]
  ring
lemma rightCut_zero_left {α δ R y : ℝ} (hδ : 0 < δ) (hy : y ≤ α+2*δ) : rightCut α δ R y = 0 := by
  rw [rightCut,Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le),zero_mul]
lemma rightCut_zero_right {α δ R y : ℝ} (hδ : 0 < δ) (hy : R+δ ≤ y) : rightCut α δ R y = 0 := by
  rw [rightCut,Real.smoothTransition.one_of_one_le (x := (y-R)/δ) ((le_div_iff₀ hδ).mpr (by linarith)),sub_self,mul_zero]
lemma rightCut_one {α δ R y : ℝ} (hδ : 0 < δ) (hy : α+3*δ ≤ y) (hyR : y ≤ R) : rightCut α δ R y = 1 := by
  rw [rightCut,Real.smoothTransition.one_of_one_le ((le_div_iff₀ hδ).mpr (by linarith)),
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)]
  ring

lemma integral_exp_neg_interval (a b : ℝ) : (∫ y in a..b, Real.exp (-y)) = Real.exp (-a)-Real.exp (-b) := by
  rw [intervalIntegral.integral_comp_neg,integral_exp]

lemma cutoff_negative_mass {α δ s : ℝ} (hα : 0 ≤ α) (hδ : 0 < δ) (hs : 0 ≤ s) :
    0 ≤ s*(∫ y in 0..α+δ, Real.exp (-y)*leftCut α δ y) ∧
    s*(∫ y in 0..α+δ, Real.exp (-y)*leftCut α δ y) ≤ s*(1-Real.exp (-(α+δ))) := by
  have hc : Continuous (fun y => Real.exp (-y)*leftCut α δ y) :=
    (Real.continuous_exp.comp continuous_neg).mul (leftCut_smooth α δ).continuous
  constructor
  · apply mul_nonneg hs
    exact intervalIntegral.integral_nonneg (by linarith) (fun y hy => mul_nonneg (Real.exp_pos _).le (leftCut_bounds _ _ _).1)
  · apply mul_le_mul_of_nonneg_left _ hs
    have hh := intervalIntegral.integral_mono_on (μ := volume) (a := 0) (b := α+δ) (by linarith) (hc.intervalIntegrable _ _)
      ((Real.continuous_exp.comp continuous_neg).intervalIntegrable _ _)
      (fun y hy => mul_le_of_le_one_right (Real.exp_pos _).le (leftCut_bounds α δ y).2)
    simpa only [Function.comp_def,integral_exp_neg_interval,neg_zero,Real.exp_zero] using hh

lemma cutoff_positive_mass {α δ R : ℝ} (hα : 0 ≤ α) (hδ : 0 < δ) (hR : α+3*δ ≤ R) :
    Real.exp (-(α+3*δ))-Real.exp (-R) ≤ ∫ y in 0..R+δ, Real.exp (-y)*rightCut α δ R y := by
  have hc : Continuous (fun y => Real.exp (-y)*rightCut α δ R y) :=
    (Real.continuous_exp.comp continuous_neg).mul (rightCut_smooth α δ R).continuous
  have hh := intervalIntegral.integral_mono_interval (μ := volume) (a := α+3*δ) (b := R) (c := 0) (d := R+δ)
    (by linarith) hR (by linarith)
    (Eventually.of_forall (fun y => mul_nonneg (Real.exp_pos _).le (rightCut_bounds α δ R y).1)) (hc.intervalIntegrable _ _)
  have he : (∫ y in α+3*δ..R, Real.exp (-y)*rightCut α δ R y) = ∫ y in α+3*δ..R, Real.exp (-y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hR] at hy
    dsimp only
    rw [rightCut_one hδ hy.1 hy.2,mul_one]
  simpa only [he,integral_exp_neg_interval] using hh

lemma profilePrimitive_deriv {f : ℝ → ℝ} (hf : Continuous f) (y : ℝ) :
    HasDerivAt (profilePrimitive f) (profilePrimitive f y+f y) y := by
  have hc : Continuous (fun v => Real.exp (-v)*f v) := (Real.continuous_exp.comp continuous_neg).mul hf
  have hp : HasDerivAt (fun y : ℝ => ∫ v in 0..y, Real.exp (-v)*f v) (Real.exp (-y)*f y) y := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 y)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hd : HasDerivAt (fun y : ℝ => Real.exp y * ∫ v in 0..y, Real.exp (-v)*f v)
      (Real.exp y * (∫ v in 0..y, Real.exp (-v)*f v) + Real.exp y * (Real.exp (-y)*f y)) y :=
    (Real.hasDerivAt_exp y).mul hp
  have he : Real.exp y*Real.exp (-y) = 1 := by rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  unfold profilePrimitive
  simpa only [← mul_assoc,he,one_mul] using hd

lemma profilePrimitive_smooth {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (profilePrimitive f) := by
  have hc : ContDiff ℝ ∞ (fun v => Real.exp (-v)*f v) := Real.contDiff_exp.comp contDiff_id.neg |>.mul hf
  have hp : ∀ y : ℝ, HasDerivAt (fun y => ∫ v in 0..y, Real.exp (-v)*f v) (Real.exp (-y)*f y) y := fun y =>
    intervalIntegral.integral_hasDerivAt_right (hc.continuous.intervalIntegrable _ _)
      hc.continuous.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuous.continuousAt
  have hi : ContDiff ℝ ∞ (fun y => ∫ v in 0..y, Real.exp (-v)*f v) := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun y => (hp y).differentiableAt,?_⟩
    rw [show (deriv fun y => ∫ v in 0..y, Real.exp (-v)*f v) = (fun y => Real.exp (-y)*f y) from funext (fun y => (hp y).deriv)]
    exact hc
  exact Real.contDiff_exp.mul hi

lemma profilePrimitive_zero (f : ℝ → ℝ) : profilePrimitive f 0 = 0 := by simp [profilePrimitive]

lemma profilePrimitive_tail {f : ℝ → ℝ} (hf : Continuous f) {E : ℝ}
    (hE : ∫ v in 0..E, Real.exp (-v)*f v = 0)
    (htail : ∀ y, E ≤ y → f y = 0) {y : ℝ} (hy : E ≤ y) : profilePrimitive f y = 0 := by
  have hc : Continuous (fun v : ℝ => Real.exp (-v)*f v) := (Real.continuous_exp.comp continuous_neg).mul hf
  have hzero : (∫ v in E..y, Real.exp (-v)*f v) = 0 := by
    calc
      _ = ∫ v in E..y, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le hy] at hv
        dsimp only
        rw [htail v hv.1,mul_zero]
      _ = 0 := by simp
  have hh := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hc.intervalIntegrable 0 E) (hc.intervalIntegrable E y)
  rw [hE,hzero,zero_add] at hh
  simp only [profilePrimitive,← hh,mul_zero]

lemma exists_radialProfiles {a : ℝ} (ha : 1 < a) (ha2 : a < 2) (Rmin : ℝ) :
    ∃ p : RadialProfiles a, Rmin < p.R := by
  obtain ⟨s,hs,hs1,hsneg⟩ := exists_profile_amplitude ha
  obtain ⟨δ,hδ,hwidth⟩ := profile_transition_width ha ha2 hs hs1
  let α := Real.log a
  have hα : 0 < α := Real.log_pos ha
  let N := s*(∫ y in 0..α+δ, Real.exp (-y)*leftCut α δ y)
  have hN := cutoff_negative_mass hα.le hδ hs.le
  change 0 ≤ N ∧ N ≤ s*(1-Real.exp (-(α+δ))) at hN
  have hgap : 0 < Real.exp (-(α+3*δ))-N := by linarith
  obtain ⟨R,hR,hsmall⟩ := ((eventually_gt_atTop (α+3*δ)).and
    (Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds hgap))).exists
  let P := ∫ y in 0..R+δ, Real.exp (-y)*rightCut α δ R y
  have hPbound := cutoff_positive_mass hα.le hδ hR.le
  change Real.exp (-(α+3*δ))-Real.exp (-R) ≤ P at hPbound
  have hNP : N < P := by linarith
  have hP : 0 < P := lt_of_le_of_lt hN.1 hNP
  have hratio : 0 ≤ N/P := div_nonneg hN.1 hP.le
  have hratio1 : N/P < 1 := (div_lt_one hP).mpr hNP
  let f : ℝ → ℝ := fun y => -s*leftCut α δ y+(N/P)*rightCut α δ R y
  let E := R+δ
  have hE : 0 < E := by dsimp [E]; linarith
  have hf : ContDiff ℝ ∞ f := (contDiff_const.mul (leftCut_smooth α δ)).add (contDiff_const.mul (rightCut_smooth α δ R))
  have htail : ∀ y, E ≤ y → f y = 0 := by
    intro y hy
    dsimp [f]
    rw [leftCut_zero hδ (by dsimp [E] at hy; linarith),rightCut_zero_right hδ hy]
    ring
  have hplateau : ∀ y ∈ Icc 0 (Real.log a), f y = -s := by
    intro y hy
    dsimp [f]
    rw [leftCut_one hδ hy.2,rightCut_zero_left hδ (by linarith [hy.2])]
    ring
  have hfsmall : ∀ y, 0 ≤ y → |f y| ≤ max s (N/P) := by
    intro y hy
    by_cases hyl : y ≤ α+δ
    · have hν : rightCut α δ R y = 0 := rightCut_zero_left hδ (by linarith)
      have hχ := leftCut_bounds α δ y
      dsimp [f]
      rw [hν,mul_zero,add_zero,abs_mul,abs_neg,abs_of_pos hs,abs_of_nonneg hχ.1]
      exact (mul_le_of_le_one_right hs.le hχ.2).trans (le_max_left _ _)
    · have hχ : leftCut α δ y = 0 := leftCut_zero hδ (le_of_not_ge hyl)
      have hν := rightCut_bounds α δ R y
      dsimp [f]
      rw [hχ,mul_zero,zero_add,abs_mul,abs_of_nonneg hratio,abs_of_nonneg hν.1]
      exact (mul_le_of_le_one_right hratio hν.2).trans (le_max_right _ _)
  have hχc : Continuous (fun y => Real.exp (-y)*leftCut α δ y) :=
    (Real.continuous_exp.comp continuous_neg).mul (leftCut_smooth α δ).continuous
  have hνc : Continuous (fun y => Real.exp (-y)*rightCut α δ R y) :=
    (Real.continuous_exp.comp continuous_neg).mul (rightCut_smooth α δ R).continuous
  have hχint : (∫ y in 0..E, Real.exp (-y)*leftCut α δ y) = ∫ y in 0..α+δ, Real.exp (-y)*leftCut α δ y := by
    have hh := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hχc.intervalIntegrable 0 (α+δ)) (hχc.intervalIntegrable (α+δ) E)
    have hz : (∫ y in α+δ..E, Real.exp (-y)*leftCut α δ y) = 0 := by
      calc
        _ = ∫ y in α+δ..E, (0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro y hy
          rw [uIcc_of_le (by dsimp [E]; linarith : α+δ ≤ E)] at hy
          dsimp only
          rw [leftCut_zero hδ hy.1,mul_zero]
        _ = 0 := by simp
    rw [hz,add_zero] at hh
    exact hh.symm
  have hcancel : (∫ y in 0..E, Real.exp (-y)*f y) = 0 := by
    have he : (fun y => Real.exp (-y)*f y) =
        (fun y => -s*(Real.exp (-y)*leftCut α δ y)+(N/P)*(Real.exp (-y)*rightCut α δ R y)) := by
      funext y
      dsimp [f]
      ring
    rw [he,intervalIntegral.integral_add ((hχc.const_mul (-s)).intervalIntegrable _ _) ((hνc.const_mul (N/P)).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,hχint]
    change -s*(∫ y in 0..α+δ, Real.exp (-y)*leftCut α δ y)+(N/P)*P = 0
    rw [div_mul_cancel₀ _ (ne_of_gt hP)]
    dsimp [N]
    ring
  have himproper : (∫ y in Ioi 0, Real.exp (-y)*f y) = 0 := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Ioc 0 E) measurableSet_Ioi (fun y hy => hy.1) (fun y hy => ?_),
      ← intervalIntegral.integral_of_le hE.le,hcancel]
    have hyE : E ≤ y := by
      by_contra hn
      exact hy.2 ⟨hy.1,(le_of_lt (lt_of_not_ge hn))⟩
    rw [htail y hyE,mul_zero]
  let p : RadialProfiles a :=
    { s := s, F := max s (N/P), R := max E Rmin+1, cutoff := E, f := f, b := profilePrimitive f
      s_pos := hs, s_lt := hs1, F_nonneg := (le_max_left s (N/P)).trans' hs.le
      F_lt := max_lt hs1 hratio1, R_pos := by linarith [le_max_left E Rmin]
      cutoff_pos := hE, cutoff_lt := by linarith [le_max_left E Rmin]
      smooth_f := hf, smooth_b := profilePrimitive_smooth hf, small := hfsmall, plateau := hplateau
      cancellation := himproper, ode := profilePrimitive_deriv hf.continuous, b_zero := profilePrimitive_zero f
      tail := fun y hy => ⟨htail y hy,profilePrimitive_tail hf.continuous hcancel htail hy⟩
      negativity := hsneg }
  refine ⟨p,?_⟩
  dsimp [p]
  linarith [le_max_right E Rmin]

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityDefinitions
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
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma phaseDerivative_smooth {W : Base → ℝ} (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (phaseDerivative W) := by
  exact (hW.fderiv_right (by simp)).clm_apply ((Complex.I • (1 : Base →L[ℂ] Base)).restrictScalars ℝ).contDiff

lemma centralPoint_smoothAt (p : Sphere) {z : Base} (hz : bracket z (p:Base) ≠ 0) :
    ContDiffAt ℝ ∞ (centralPoint p) z := by
  have hc : ContDiff ℝ ∞ (fun z : Base => bracket z (p:Base)) := (bracket_analytic (p:Base)).contDiff.restrict_scalars ℝ
  have hn : ContDiffAt ℝ ∞ (fun z : Base => ‖bracket z (p:Base)‖) z := hc.contDiffAt.norm ℂ hz
  simpa only [centralPoint,div_eq_mul_inv,Function.comp_def,Complex.ofRealCLM_apply] using!
    ((hc.contDiffAt.mul ((Complex.ofRealCLM.contDiff.comp_contDiffAt z hn).inv
      (by simpa only [Function.comp_def,Complex.ofRealCLM_apply,ne_eq,Complex.ofReal_eq_zero] using norm_ne_zero_iff.mpr hz))).smul (contDiffAt_const (c := (p:Base))))

lemma densityHeight_smoothAt (k : ℕ) (p : Sphere) {z : Base} (hz : bracket z (p:Base) ≠ 0) :
    ContDiffAt ℝ ∞ (densityHeight k p) z := by
  have hc : ContDiff ℝ ∞ (fun z : Base => bracket z (p:Base)) := (bracket_analytic (p:Base)).contDiff.restrict_scalars ℝ
  exact contDiffAt_const.mul ((hc.contDiffAt.norm ℂ hz).log (norm_ne_zero_iff.mpr hz))

lemma densityCorrectionRaw_smoothAt (k : ℕ) {f b : ℝ → ℝ} {W : Base → ℝ}
    (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b) (hW : ContDiff ℝ ∞ W)
    (p : Sphere) {z : Base} (hz : bracket z (p:Base) ≠ 0) :
    ContDiffAt ℝ ∞ (densityCorrectionRaw k f b W p) z := by
  have hc : ContDiff ℝ ∞ (fun z : Base => bracket z (p:Base)) := (bracket_analytic (p:Base)).contDiff.restrict_scalars ℝ
  have hn := hc.contDiffAt.norm ℂ hz
  have hn0 := norm_ne_zero_iff.mpr hz
  have hphase : ContDiffAt ℝ ∞ (fun z : Base => bracket z (p:Base)/(‖bracket z (p:Base)‖:ℂ)) z := by
    simpa only [div_eq_mul_inv,Function.comp_def,Complex.ofRealCLM_apply] using! hc.contDiffAt.mul ((Complex.ofRealCLM.contDiff.comp_contDiffAt z hn).inv
      (by exact_mod_cast hn0 : (‖bracket z (p:Base)‖:ℂ) ≠ 0))
  have hy := densityHeight_smoothAt k p hz
  have hs := centralPoint_smoothAt p hz
  have hreal := Complex.reCLM.contDiff.comp_contDiffAt z (hphase.pow k)
  have him := Complex.imCLM.contDiff.comp_contDiffAt z (hphase.pow k)
  exact ((hn.pow 2).inv (pow_ne_zero 2 hn0)).mul
    ((((hf.contDiffAt.comp z hy).mul (hW.contDiffAt.comp z hs)).mul hreal).sub
      ((((hb.contDiffAt.comp z hy).div_const (k:ℝ)).mul ((phaseDerivative_smooth hW).contDiffAt.comp z hs)).mul him))

lemma densityCorrection_zero_low {k : ℕ} (hk : 0 < k) {R E : ℝ} {f b : ℝ → ℝ}
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (W : Base → ℝ) (p : Sphere) (z : Base)
    (hz : ‖bracket z (p:Base)‖ ≤ Real.exp (-E/k)) : densityCorrection k R f b W p z=0 := by
  unfold densityCorrection
  split_ifs with hc
  · have hn : 0 < ‖bracket z (p:Base)‖ := lt_trans (Real.exp_pos _) hc
    have hh := Real.log_le_log hn hz
    rw [Real.log_exp] at hh
    have hk0 : (0:ℝ) < k := by exact_mod_cast hk
    have hhy : E ≤ densityHeight k p z := by
      have hm := (le_div_iff₀ hk0).mp hh
      unfold densityHeight
      linarith
    obtain ⟨hf,hb⟩ := htail _ hhy
    simp [densityCorrectionRaw,hf,hb]
  · rfl

lemma densityCorrection_smooth {k : ℕ} (hk : 0 < k) {R E : ℝ} (hER : E < R)
    {f b : ℝ → ℝ} {W : Base → ℝ}
    (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b) (hW : ContDiff ℝ ∞ W)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (p : Sphere) :
    ContDiff ℝ ∞ (densityCorrection k R f b W p) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  have hc : Continuous (fun z : Base => ‖bracket z (p:Base)‖) := (bracket_analytic (p:Base)).continuous.norm
  by_cases hz : Real.exp (-R/k) < ‖bracket z (p:Base)‖
  · have he : densityCorrection k R f b W p =ᶠ[𝓝 z] densityCorrectionRaw k f b W p := by
      filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hz] with v hv
      exact ite_eq_left hv
    exact (densityCorrectionRaw_smoothAt k hf hb hW p (norm_pos_iff.mp (lt_trans (Real.exp_pos _) hz))).congr_of_eventuallyEq he
  · have hk0 : (0:ℝ) < k := by exact_mod_cast hk
    have hcut : Real.exp (-R/k) < Real.exp (-E/k) := Real.exp_lt_exp.mpr ((div_lt_div_iff_of_pos_right hk0).mpr (neg_lt_neg hER))
    have hzE : ‖bracket z (p:Base)‖ < Real.exp (-E/k) := lt_of_le_of_lt (le_of_not_gt hz) hcut
    have he : densityCorrection k R f b W p =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [(isOpen_lt hc continuous_const).mem_nhds hzE] with v hv
      exact densityCorrection_zero_low hk htail W p v hv.le
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma density_smooth {Q : ℕ} (hQ : 0 < Q) {R E : ℝ} (hER : E < R)
    {f b : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (P : ℕ → Finset Sphere) (j : ℕ) :
    ContDiff ℝ ∞ (density Q R f b P j) := by
  induction j with
  | zero => exact contDiff_const
  | succ j ih =>
    exact ih.add (ContDiff.sum (fun p hp => densityCorrection_smooth (pow_pos hQ _) hER hf hb ih htail p))

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePhaseDerivatives
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

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma phaseChar_derivative (n : ℤ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => phaseChar n (Circle.exp t))
      ((n:ℂ)*Complex.I*phaseChar n (Circle.exp θ)) θ := by
  have hh : HasDerivAt (fun t : ℝ => (n:ℂ)*(t:ℂ)*Complex.I) ((n:ℂ)*Complex.I) θ := by
    simpa using (Complex.ofRealCLM.hasDerivAt.const_mul (n:ℂ)).mul_const Complex.I
  simpa only [phaseChar_exp,mul_comm] using hh.cexp

lemma phaseSum_derivative (s : Finset ℤ) (a : ℤ → ℂ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => phaseSum s a (Circle.exp t))
      (phaseSum s (fun n => (n:ℂ)*Complex.I*a n) (Circle.exp θ)) θ := by
  have hh := HasDerivAt.sum (u := s) (fun n _ => (phaseChar_derivative n θ).const_mul (a n))
  convert! hh using 1
  · ext t; simp only [phaseSum,Finset.sum_apply]
  · unfold phaseSum
    apply Finset.sum_congr rfl
    intro n hn
    ring

lemma phase_curve_derivative (z : Base) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => (Circle.exp t:ℂ) • z)
      (Complex.I • ((Circle.exp θ:ℂ) • z)) θ := by
  have hh : HasDerivAt (fun t : ℝ => Complex.exp ((t:ℂ)*Complex.I))
      (Complex.exp ((θ:ℂ)*Complex.I)*Complex.I) θ := by
    simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] using (Complex.ofRealCLM.hasDerivAt.mul_const Complex.I).cexp
  simpa only [Circle.coe_exp,smul_smul,mul_comm] using hh.smul_const z

lemma phaseDerivative_curve {W : Base → ℝ} (hW : Differentiable ℝ W) (z : Base) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => W ((Circle.exp t:ℂ) • z))
      (phaseDerivative W ((Circle.exp θ:ℂ) • z)) θ := by
  exact (hW _).hasFDerivAt.comp_hasDerivAt θ (phase_curve_derivative z θ)

lemma phaseDerivative_expansion {W : Base → ℝ} (hW : Differentiable ℝ W) (p : Sphere)
    (s : Finset ℤ) (a : ℤ → ℂ)
    (he : ∀ z : Circle, (W ((z:ℂ) • (p:Base)):ℂ) = phaseSum s a z) (z : Circle) :
    (phaseDerivative W ((z:ℂ) • (p:Base)):ℂ) = phaseSum s (fun n => (n:ℂ)*Complex.I*a n) z := by
  obtain ⟨θ,rfl⟩ := Circle.exp_surjective z
  have hleft := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt θ (phaseDerivative_curve hW (p:Base) θ)
  have hfun : (fun t : ℝ => (W ((Circle.exp t:ℂ) • (p:Base)):ℂ)) =
      (fun t : ℝ => phaseSum s a (Circle.exp t)) := funext (fun t => he _)
  change HasDerivAt (fun t : ℝ => (W ((Circle.exp t:ℂ) • (p:Base)):ℂ))
    (phaseDerivative W ((Circle.exp θ:ℂ) • (p:Base)):ℂ) θ at hleft
  rw [hfun] at hleft
  exact hleft.unique (phaseSum_derivative s a θ)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityFourier
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
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma circle_bracket_norm (z : Circle) (ξ : Base) (p : Sphere) :
    ‖bracket ((z:ℂ) • ξ) (p:Base)‖ = ‖bracket ξ (p:Base)‖ := by simp [bracket_smul,z.norm_coe]

lemma centralPoint_phase (p : Sphere) (z : Circle) (ξ : Base) :
    centralPoint p ((z:ℂ) • ξ) = (z:ℂ) • centralPoint p ξ := by
  unfold centralPoint
  rw [circle_bracket_norm,bracket_smul,smul_smul]
  congr 1
  ring

lemma densityHeight_phase (k : ℕ) (p : Sphere) (z : Circle) (ξ : Base) :
    densityHeight k p ((z:ℂ) • ξ) = densityHeight k p ξ := by simp only [densityHeight,circle_bracket_norm]

lemma densityCorrectionRaw_eq_re (k : ℕ) (f b : ℝ → ℝ) (W : Base → ℝ) (p : Sphere) (ξ : Base) :
    densityCorrectionRaw k f b W p ξ =
      (((‖bracket ξ (p:Base)‖^2)⁻¹:ℝ) *
        (bracket ξ (p:Base)/(‖bracket ξ (p:Base)‖:ℂ))^k *
        ((f (densityHeight k p ξ)*W (centralPoint p ξ):ℝ) + Complex.I*
          (b (densityHeight k p ξ)/k*phaseDerivative W (centralPoint p ξ):ℝ))).re := by
  simp only [densityCorrectionRaw,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,
    zero_add,add_zero,sub_zero,one_mul]
  ring

lemma densityCorrectionRaw_phase_expansion (k : ℕ) (f b : ℝ → ℝ) {W : Base → ℝ}
    (hW : Differentiable ℝ W) (p : Sphere) (ξ : Base) (hξ : bracket ξ (p:Base) ≠ 0)
    (s : Finset ℤ) (a : ℤ → ℂ)
    (he : ∀ z : Circle, (W ((z:ℂ) • centralPoint p ξ):ℂ) = phaseSum s a z) (z : Circle) :
    densityCorrectionRaw k f b W p ((z:ℂ) • ξ) =
      (∑ n ∈ s,
        (((‖bracket ξ (p:Base)‖^2)⁻¹:ℝ) *
          (bracket ξ (p:Base)/(‖bracket ξ (p:Base)‖:ℂ))^k * a n *
          ((f (densityHeight k p ξ) - (n:ℝ)/k*b (densityHeight k p ξ):ℝ):ℂ)) *
          phaseChar ((k:ℤ)+n) z).re := by
  let q : Sphere := ⟨centralPoint p ξ,by simpa only [Metric.mem_sphere,dist_zero_right] using centralPoint_norm p hξ⟩
  have hT := phaseDerivative_expansion hW q s a he z
  rw [densityCorrectionRaw_eq_re,circle_bracket_norm,bracket_smul,centralPoint_phase,densityHeight_phase]
  have hph : ((z:ℂ)*bracket ξ (p:Base)/(‖bracket ξ (p:Base)‖:ℂ))^k =
      (z:ℂ)^k*(bracket ξ (p:Base)/(‖bracket ξ (p:Base)‖:ℂ))^k := by rw [mul_div_assoc,mul_pow]
  rw [hph]
  change (phaseDerivative W ((z:ℂ) • centralPoint p ξ):ℂ) = _ at hT
  push_cast
  rw [he,hT]
  unfold phaseSum
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [phaseChar_add]
  simp only [phaseChar,Circle.coe_zpow,zpow_natCast]
  have hi : Complex.I*Complex.I = -1 := Complex.I_mul_I
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityBandwidth
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
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma densityCorrection_phase_band {W : Base → ℝ} (hW : Differentiable ℝ W)
    {ℓ k : ℕ} (hband : PhaseBandwidth W ℓ) (R : ℝ) (f b : ℝ → ℝ) (p : Sphere) :
    PhaseBandwidth (densityCorrection k R f b W p) (k+ℓ) := by
  classical
  intro ξ
  by_cases hc : Real.exp (-R/k) < ‖bracket (ξ:Base) (p:Base)‖
  · have hξ : bracket (ξ:Base) (p:Base) ≠ 0 := norm_pos_iff.mp (lt_trans (Real.exp_pos _) hc)
    let q : Sphere := ⟨centralPoint p ξ,by simpa only [Metric.mem_sphere,dist_zero_right] using centralPoint_norm p hξ⟩
    obtain ⟨s,a,hs,he⟩ := hband q
    let A : ℤ → ℂ := fun n => (((‖bracket (ξ:Base) (p:Base)‖^2)⁻¹:ℝ) *
          (bracket (ξ:Base) (p:Base)/(‖bracket (ξ:Base) (p:Base)‖:ℂ))^k * a n *
          ((f (densityHeight k p ξ) - (n:ℝ)/k*b (densityHeight k p ξ):ℝ):ℂ))
    have hh : ∀ z : Circle, densityCorrection k R f b W p ((z:ℂ) • (ξ:Base)) =
        (phaseSum (s.image (fun n => (k:ℤ)+n)) (fun n => A (n-k)) z).re := by
      intro z
      rw [densityCorrection,circle_bracket_norm,ite_eq_left hc]
      rw [densityCorrectionRaw_phase_expansion k f b hW p ξ hξ s a he z]
      rw [phaseSum_shift]
    have hbound : ∀ n ∈ s.image (fun n => (k:ℤ)+n), |n| ≤ ((k+ℓ:ℕ):ℤ) := by
      intro n hn
      obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
      have ht := abs_add_le (k:ℤ) m
      have hm' := hs m hm
      simpa only [Nat.cast_add,abs_of_nonneg (Int.natCast_nonneg k)] using
        le_trans ht (by simpa using add_le_add_right hm' (k:ℤ))
    obtain ⟨b',hb'⟩ := phaseSum_real_band hbound (fun n => A (n-k))
    refine ⟨phaseBand (k+ℓ),b',fun n hn => (mem_phaseBand _ _).mp hn,?_⟩
    intro z
    rw [hh,hb']
  · refine ⟨∅,fun _ => 0,by simp,?_⟩
    intro z
    simp only [densityCorrection,circle_bracket_norm,ite_eq_right hc,Complex.ofReal_zero,phaseSum,Finset.sum_empty]

lemma densityCorrection_orbit_zero {W : Base → ℝ} (hW : Differentiable ℝ W)
    {ℓ k : ℕ} (hband : PhaseBandwidth W ℓ) (hℓ : ℓ < k)
    (R : ℝ) (f b : ℝ → ℝ) (p ξ : Sphere) :
    (∫ z : Circle, densityCorrection k R f b W p ((z:ℂ) • (ξ:Base)) ∂circleMeasure) = 0 := by
  classical
  by_cases hc : Real.exp (-R/k) < ‖bracket (ξ:Base) (p:Base)‖
  · have hξ : bracket (ξ:Base) (p:Base) ≠ 0 := norm_pos_iff.mp (lt_trans (Real.exp_pos _) hc)
    let q : Sphere := ⟨centralPoint p ξ,by simpa only [Metric.mem_sphere,dist_zero_right] using centralPoint_norm p hξ⟩
    obtain ⟨s,a,hs,he⟩ := hband q
    let A : ℤ → ℂ := fun n => (((‖bracket (ξ:Base) (p:Base)‖^2)⁻¹:ℝ) *
          (bracket (ξ:Base) (p:Base)/(‖bracket (ξ:Base) (p:Base)‖:ℂ))^k * a n *
          ((f (densityHeight k p ξ) - (n:ℝ)/k*b (densityHeight k p ξ):ℝ):ℂ))
    have hh : ∀ z : Circle, densityCorrection k R f b W p ((z:ℂ) • (ξ:Base)) =
        (phaseSum (s.image (fun n => (k:ℤ)+n)) (fun n => A (n-k)) z).re := by
      intro z
      rw [densityCorrection,circle_bracket_norm,ite_eq_left hc]
      rw [densityCorrectionRaw_phase_expansion k f b hW p ξ hξ s a he z,phaseSum_shift]
    simp_rw [hh]
    rw [show (∫ z : Circle, (phaseSum (s.image (fun n => (k:ℤ)+n)) (fun n => A (n-k)) z).re ∂circleMeasure) =
      (∫ z : Circle, phaseSum (s.image (fun n => (k:ℤ)+n)) (fun n => A (n-k)) z ∂circleMeasure).re from
      integral_re (compact_continuous_integrable (phaseSum_continuous _ _))]
    have hn : 0 ∉ s.image (fun n => (k:ℤ)+n) := by
      intro hn
      obtain ⟨m,hm,he⟩ := Finset.mem_image.mp hn
      have hm' := (abs_le.mp (hs m hm)).1
      omega
    rw [phaseSum_integral _ hn]
    rfl
  · simp only [densityCorrection,circle_bracket_norm,ite_eq_right hc,integral_zero]

lemma densityBandwidth_succ (Q j : ℕ) : densityBandwidth Q (j+1)=Q^(j+1)+densityBandwidth Q j := by
  simp [densityBandwidth,Finset.sum_range_succ,Nat.add_comm]

lemma densityBandwidth_lt {Q : ℕ} (hQ : 2 ≤ Q) (j : ℕ) : densityBandwidth Q j < Q^(j+1) := by
  induction j with
  | zero => simp [densityBandwidth]; omega
  | succ j ih =>
    rw [densityBandwidth_succ]
    have hp : 0 < Q^(j+1) := pow_pos (by omega) _
    calc
      Q^(j+1)+densityBandwidth Q j < Q^(j+1)*2 := by omega
      _ ≤ Q^(j+1)*Q := Nat.mul_le_mul_left _ hQ
      _ = _ := by simp only [pow_succ]

lemma density_bandwidth {Q : ℕ} (hQ : 0 < Q) {R E : ℝ} (hER : E < R)
    {f b : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (P : ℕ → Finset Sphere) (j : ℕ) :
    PhaseBandwidth (density Q R f b P j) (densityBandwidth Q j) := by
  induction j with
  | zero => exact phaseBandwidth_one
  | succ j ih =>
    rw [densityBandwidth_succ]
    apply phaseBandwidth_add (phaseBandwidth_mono ih (Nat.le_add_left _ _))
    apply phaseBandwidth_sum
    intro p hp
    exact densityCorrection_phase_band ((density_smooth hQ hER hf hb htail P j).differentiable (by simp)) ih R f b p

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseRootAveraging
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
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma phaseChar_root {k : ℕ} (hk : 0 < k) :
    phaseChar (k:ℤ) (Circle.exp (2*Real.pi/k))=1 := by
  rw [phaseChar_exp]
  have hk0 : (k:ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have he : (k:ℂ)*(2*Real.pi/k:ℝ)*Complex.I=2*(Real.pi:ℂ)*Complex.I := by push_cast; field_simp
  norm_cast at *
  rw [he]
  push_cast
  exact Complex.exp_two_pi_mul_I

lemma phaseChar_root_ne_one {k : ℕ} (hk : 0 < k) {n : ℤ} (hn : n ≠ 0) (hbound : |n| < (k:ℤ)) :
    phaseChar n (Circle.exp (2*Real.pi/k)) ≠ 1 := by
  intro he
  have hec : Circle.exp ((n:ℝ)*(2*Real.pi/k))=1 := by
    apply Subtype.ext
    simpa only [Circle.coe_one,Circle.coe_exp,phaseChar_exp,Complex.ofReal_mul,Complex.ofReal_intCast,mul_assoc] using he
  obtain ⟨m,hm⟩ := Circle.exp_eq_one.mp hec
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hp := Real.pi_pos
  have hnm : (n:ℝ)=(m:ℝ)*k := by
    have hh := congrArg (fun t : ℝ => t*k) hm
    field_simp at hh
    linarith
  have hni : n=m*k := by exact_mod_cast hnm
  have hmn : m ≠ 0 := by intro hz; simp [hz] at hni; exact hn hni
  have hm1 : (1:ℤ) ≤ |m| := by have := abs_pos.mpr hmn; omega
  rw [hni,abs_mul,abs_of_nonneg (show (0:ℤ) ≤ k by positivity)] at hbound
  have hh := mul_le_mul_of_nonneg_right hm1 (show (0:ℤ) ≤ k by positivity)
  omega

lemma root_invariant_char_integral {k : ℕ} (hk : 0 < k) {V : Circle → ℂ}
    (hV : ∀ z, V (Circle.exp (2*Real.pi/k)*z)=V z)
    {n : ℤ} (hn : n ≠ 0) (hbound : |n| < (k:ℤ)) :
    (∫ z, V z*phaseChar n z ∂circleMeasure)=0 := by
  let w := Circle.exp (2*Real.pi/k)
  have he := integral_mul_left_eq_self (μ := circleMeasure) (fun z => V z*phaseChar n z) w
  have hf : ∀ z, V (w*z)*phaseChar n (w*z)=phaseChar n w*(V z*phaseChar n z) := by
    intro z
    rw [hV,phaseChar_mul]
    ring
  simp_rw [hf] at he
  rw [integral_const_mul] at he
  by_contra hz
  exact phaseChar_root_ne_one hk hn hbound ((mul_eq_right₀ hz).mp he)

lemma root_invariant_phaseSum {k ℓ : ℕ} (hk : 0 < k) (hl : ℓ < k)
    {V : Circle → ℂ} (hi : Integrable V circleMeasure)
    (hV : ∀ z, V (Circle.exp (2*Real.pi/k)*z)=V z)
    (s : Finset ℤ) (b : ℤ → ℂ) (hband : ∀ n ∈ s, |n| ≤ (ℓ:ℤ)) :
    (∫ z, V z*phaseSum s b z ∂circleMeasure) =
      (∫ z, V z ∂circleMeasure)*(∫ z, phaseSum s b z ∂circleMeasure) := by
  classical
  have hi' : ∀ n, Integrable (fun z => V z*phaseChar n z) circleMeasure := by
    intro n
    exact hi.mul_bdd (phaseChar_continuous n).aestronglyMeasurable
      (Eventually.of_forall (fun z => le_of_eq (phaseChar_norm n z)))
  simp only [phaseSum,Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum s (fun n _ => by simpa [mul_left_comm,mul_assoc] using (hi' n).const_mul (b n))]
  have he : ∀ n ∈ s, (∫ z, V z*(b n*phaseChar n z) ∂circleMeasure)=
      if n=0 then b n*(∫ z, V z ∂circleMeasure) else 0 := by
    intro n hn
    simp_rw [show ∀ z, V z*(b n*phaseChar n z)=b n*(V z*phaseChar n z) by intro z; ring]
    rw [integral_const_mul]
    by_cases hn0 : n=0
    · simp [hn0]
    · rw [ite_eq_right hn0,root_invariant_char_integral hk hV hn0 (lt_of_le_of_lt (hband n hn) (by exact_mod_cast hl)),mul_zero]
  rw [Finset.sum_congr rfl he]
  have hm := phaseSum_mean s b
  unfold phaseSum at hm
  rw [hm]
  by_cases hz : 0 ∈ s <;> simp [hz,mul_comm]

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePhaseAveraging
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
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma phase_average_product {k ℓ : ℕ} (hk : 0 < k) (hl : ℓ < k)
    {W : Base → ℝ} (hb : PhaseBandwidth W ℓ) (p : Sphere)
    {V : Circle → ℝ} (hi : Integrable V circleMeasure)
    (hV : ∀ z, V (Circle.exp (2*Real.pi/k)*z)=V z) :
    (∫ z, V z*W ((z:ℂ) • (p:Base)) ∂circleMeasure) =
      (∫ z, V z ∂circleMeasure)*(∫ z : Circle, W ((z:ℂ) • (p:Base)) ∂circleMeasure) := by
  obtain ⟨s,b,hs,he⟩ := hb p
  have hvi : Integrable (fun z : Circle => (V z:ℂ)) circleMeasure := hi.ofReal
  have hh := root_invariant_phaseSum hk hl hvi (fun z => congrArg (fun t : ℝ => (t:ℂ)) (hV z)) s b hs
  simp_rw [← he,← Complex.ofReal_mul] at hh
  rw [integral_complex_ofReal,integral_complex_ofReal,integral_complex_ofReal,← Complex.ofReal_mul] at hh
  exact Complex.ofReal_injective hh

lemma phaseAction_continuous : Continuous (fun p : Circle × Sphere => phaseAction p.1 p.2) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd)

lemma sigma_phase_average {V : Sphere → ℝ} (hV : Continuous V) :
    (∫ ξ, V ξ ∂sigma) = ∫ ξ, ∫ z : Circle, V (phaseAction z ξ) ∂circleMeasure ∂sigma := by
  have hc : Continuous (fun p : Circle × Sphere => V (phaseAction p.1 p.2)) := hV.comp phaseAction_continuous
  have hi := compact_continuous_integrable (μ := circleMeasure.prod sigma) hc
  have hunit : ∀ z : Circle, (∫ ξ, V (phaseAction z ξ) ∂sigma)=∫ ξ, V ξ ∂sigma := by
    intro z
    exact sigma_integral_unitary (phaseIsometry z z.norm_coe) V
  rw [← integral_integral_swap hi]
  simp_rw [hunit]
  simp

lemma sigma_root_average {k ℓ : ℕ} (hk : 0 < k) (hl : ℓ < k)
    {W V : Base → ℝ} (hW : Continuous W) (hV : Continuous V)
    (hb : PhaseBandwidth W ℓ) (hm : OrbitMeanOne W)
    (hroot : ∀ ξ : Sphere, V ((Circle.exp (2*Real.pi/k):ℂ) • (ξ:Base))=V ξ) :
    (∫ ξ : Sphere, V ξ*W ξ ∂sigma)=∫ ξ : Sphere, V ξ ∂sigma := by
  have hc : Continuous (fun ξ : Sphere => V ξ*W ξ) := (hV.mul hW).comp continuous_subtype_val
  have hcV : Continuous (fun ξ : Sphere => V ξ) := hV.comp continuous_subtype_val
  rw [sigma_phase_average hc,sigma_phase_average hcV]
  apply integral_congr_ae
  exact Eventually.of_forall (fun ξ => by
    change (∫ z : Circle, V ((z:ℂ) • (ξ:Base))*W ((z:ℂ) • (ξ:Base)) ∂circleMeasure)=_
    have hi : Integrable (fun z : Circle => V ((z:ℂ) • (ξ:Base))) circleMeasure :=
      by
        have hcZ : Continuous (fun z : Circle => V ((z:ℂ) • (ξ:Base))) := by fun_prop
        exact compact_continuous_integrable hcZ
    rw [phase_average_product hk hl hb ξ hi
      (fun z => by simpa only [Circle.coe_mul,mul_smul,phaseAction_coe] using hroot (phaseAction z ξ)),hm ξ,mul_one]
    rfl)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityLowMoments
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
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma densityCorrection_low_moment {W : Base → ℝ} (hW : Differentiable ℝ W)
    {ℓ k n : ℕ} (hband : PhaseBandwidth W ℓ) (hgap : n+ℓ < k)
    (R : ℝ) (f b : ℝ → ℝ) (p ξ : Sphere) :
    (∫ z : Circle, phaseChar n z*(densityCorrection k R f b W p ((z:ℂ) • (ξ:Base)):ℂ) ∂circleMeasure)=0 := by
  classical
  by_cases hc : Real.exp (-R/k) < ‖bracket (ξ:Base) (p:Base)‖
  · have hξ : bracket (ξ:Base) (p:Base) ≠ 0 := norm_pos_iff.mp (lt_trans (Real.exp_pos _) hc)
    let q : Sphere := ⟨centralPoint p ξ,by simpa only [Metric.mem_sphere,dist_zero_right] using centralPoint_norm p hξ⟩
    obtain ⟨s,a,hs,he⟩ := hband q
    let A : ℤ → ℂ := fun m => (((‖bracket (ξ:Base) (p:Base)‖^2)⁻¹:ℝ) *
          (bracket (ξ:Base) (p:Base)/(‖bracket (ξ:Base) (p:Base)‖:ℂ))^k * a m *
          ((f (densityHeight k p ξ) - (m:ℝ)/k*b (densityHeight k p ξ):ℝ):ℂ))
    have hh : ∀ z : Circle, densityCorrection k R f b W p ((z:ℂ) • (ξ:Base)) =
        (phaseSum (s.image (fun m => (k:ℤ)+m)) (fun m => A (m-k)) z).re := by
      intro z
      rw [densityCorrection,circle_bracket_norm,ite_eq_left hc]
      rw [densityCorrectionRaw_phase_expansion k f b hW p ξ hξ s a he z,phaseSum_shift]
    simp_rw [hh]
    have hb : ∀ m ∈ s.image (fun m => (k:ℤ)+m), (n:ℤ) < m := by
      intro m hm
      obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hm
      have hl' := (abs_le.mp (hs l hl)).1
      omega
    rw [phase_real_sum_moment _ _ n (fun m hm => lt_of_le_of_lt (by exact_mod_cast Nat.zero_le n) (hb m hm))]
    exact Finset.sum_eq_zero (fun m hm => ite_eq_right (ne_of_gt (hb m hm)))
  · simp only [densityCorrection,circle_bracket_norm,ite_eq_right hc,Complex.ofReal_zero,mul_zero,integral_zero]

lemma circle_real_product_zero {f : Circle → ℝ} (hf : Continuous f) (n : ℕ) (v : ℂ)
    (hz : (∫ z : Circle, phaseChar n z*(f z:ℂ) ∂circleMeasure)=0) :
    (∫ z : Circle, (phaseChar n z*v).re*f z ∂circleMeasure)=0 := by
  have hi : Integrable (fun z : Circle => v*(phaseChar n z*(f z:ℂ))) circleMeasure :=
    compact_continuous_integrable (continuous_const.mul ((phaseChar_continuous _).mul (Complex.continuous_ofReal.comp hf)))
  have he : ∀ z : Circle, (phaseChar n z*v).re*f z=(v*(phaseChar n z*(f z:ℂ))).re := by
    intro z
    simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero]
    ring
  simp_rw [he]
  have hh : (∫ z : Circle, (v*(phaseChar n z*(f z:ℂ))).re ∂circleMeasure)=
      (∫ z : Circle, v*(phaseChar n z*(f z:ℂ)) ∂circleMeasure).re := integral_re hi
  rw [hh,integral_const_mul,hz,mul_zero]
  rfl

lemma sphere_eigen_integral_zero {W : Sphere → ℝ} (hW : Continuous W) {n : ℕ}
    {V : Sphere → ℂ} (hV : Continuous V)
    (hphase : ∀ z ξ, V (phaseAction z ξ)=phaseChar n z*V ξ)
    (hz : ∀ ξ : Sphere, (∫ z : Circle, phaseChar n z*(W (phaseAction z ξ):ℂ) ∂circleMeasure)=0) :
    (∫ ξ : Sphere, (V ξ).re*W ξ ∂sigma)=0 := by
  have hcont : Continuous (fun ξ : Sphere => (V ξ).re*W ξ) := (Complex.continuous_re.comp hV).mul hW
  rw [sigma_phase_average hcont]
  apply integral_eq_zero_of_ae
  refine Eventually.of_forall (fun ξ => ?_)
  simp only [hphase]
  exact circle_real_product_zero (hW.comp (phaseAction_continuous.comp (continuous_id.prodMk continuous_const))) n (V ξ) (hz ξ)

lemma correction_eigenfunction_integral {a : ℝ} (pr : RadialProfiles a) {W : Base → ℝ}
    (hW : ContDiff ℝ ∞ W) {ℓ k n : ℕ} (hband : PhaseBandwidth W ℓ) (hgap : n+ℓ < k)
    (p : Sphere) {V : Sphere → ℂ} (hV : Continuous V)
    (hphase : ∀ z ξ, V (phaseAction z ξ)=phaseChar n z*V ξ) :
    (∫ ξ : Sphere, (V ξ).re*densityCorrection k pr.R pr.f pr.b W p ξ ∂sigma)=0 := by
  have hk : 0 < k := by omega
  have hco : Continuous (fun ξ : Sphere => densityCorrection k pr.R pr.f pr.b W p ξ) :=
    (densityCorrection_smooth hk pr.cutoff_lt pr.smooth_f pr.smooth_b hW pr.tail p).continuous.comp continuous_subtype_val
  exact sphere_eigen_integral_zero hco hV hphase
    (fun ξ => densityCorrection_low_moment (hW.differentiable (by norm_num)) hband hgap pr.R pr.f pr.b p ξ)

lemma density_low_moment_step {a : ℝ} (pr : RadialProfiles a) {Q : ℕ} (hQ : 0 < Q)
    (P : ℕ → Finset Sphere) (j : ℕ) {n : ℕ} (hgap : n+densityBandwidth Q j < Q^(j+1))
    {V : Sphere → ℂ} (hV : Continuous V)
    (hphase : ∀ z ξ, V (phaseAction z ξ)=phaseChar n z*V ξ) :
    (∫ ξ : Sphere, (V ξ).re*density Q pr.R pr.f pr.b P (j+1) ξ ∂sigma)=
      ∫ ξ : Sphere, (V ξ).re*density Q pr.R pr.f pr.b P j ξ ∂sigma := by
  have hW := density_smooth hQ pr.cutoff_lt pr.smooth_f pr.smooth_b pr.tail P j
  have hband := density_bandwidth hQ pr.cutoff_lt pr.smooth_f pr.smooth_b pr.tail P j
  have hc : ∀ p ∈ P (Q^(j+1)), Integrable (fun ξ : Sphere => (V ξ).re*
      densityCorrection (Q^(j+1)) pr.R pr.f pr.b (density Q pr.R pr.f pr.b P j) p ξ) sigma := by
    intro p hp
    exact compact_continuous_integrable ((Complex.continuous_re.comp hV).mul
      ((densityCorrection_smooth (pow_pos hQ _) pr.cutoff_lt pr.smooth_f pr.smooth_b hW pr.tail p).continuous.comp continuous_subtype_val))
  simp only [density,mul_add,Finset.mul_sum]
  have hi : Integrable (fun ξ : Sphere => (V ξ).re*density Q pr.R pr.f pr.b P j ξ) sigma :=
    compact_continuous_integrable ((Complex.continuous_re.comp hV).mul (hW.continuous.comp continuous_subtype_val))
  rw [integral_add hi
    (integrable_finsetSum _ hc),integral_finsetSum _ hc]
  simp_rw [correction_eigenfunction_integral pr hW hband hgap _ hV hphase]
  simp

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseCircleLog
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
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma circle_real_char_mean {n : ℤ} (hn : n ≠ 0) :
    (∫ z, (phaseChar n z).re ∂circleMeasure)=0 := by
  have he : (∫ z, (phaseChar n z).re ∂circleMeasure) = (∫ z, phaseChar n z ∂circleMeasure).re := integral_re (compact_continuous_integrable (phaseChar_continuous n))
  rw [he,circle_char_mean,ite_eq_right hn]
  rfl

lemma circle_real_char_cos {n : ℕ} (hn : 0 < n) :
    (∫ z : Circle, (phaseChar n z).re*(z:ℂ).re ∂circleMeasure)=if n=1 then 1/2 else 0 := by
  obtain ⟨index, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hh := phase_real_moment (1:ℂ) (1:ℤ) (index+1) (by norm_num)
  have he : ∫ z : Circle, (phaseChar (index+1) z*((z:ℂ).re:ℂ)) ∂circleMeasure = if index+1=1 then (1/2:ℂ) else 0 := by
    simpa [phaseChar,eq_comm] using hh
  have hh' := congrArg Complex.re he
  have hei : (∫ z : Circle, (phaseChar (index+1) z*((z:ℂ).re:ℂ)).re ∂circleMeasure) = (∫ z : Circle, phaseChar (index+1) z*((z:ℂ).re:ℂ) ∂circleMeasure).re := integral_re (compact_continuous_integrable ((phaseChar_continuous _).mul (Complex.continuous_ofReal.comp (Complex.continuous_re.comp continuous_subtype_val))))
  rw [← hei] at hh'
  simpa only [Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one,apply_ite,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,Complex.zero_re,Complex.div_ofNat_re,Complex.one_re] using hh'

lemma hasSum_circle_log {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (z : Circle) :
    HasSum (fun n : ℕ => (-2*r^(n+1)/(n+1))*(phaseChar (n+1) z).re)
      (Real.log (‖1-(r:ℂ)*(z:ℂ)‖^2)) := by
  have hnorm : ‖(r:ℂ)*(z:ℂ)‖ < 1 := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,z.norm_coe,mul_one]; exact hr1
  have hh := (Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log' hnorm)).mul_left (-2)
  have heq : -2 * (-Complex.log (1-(r:ℂ)*(z:ℂ))).re = Real.log (‖1-(r:ℂ)*(z:ℂ)‖^2) := by
    rw [Complex.neg_re,Complex.log_re,Real.log_pow]
    ring
  rw [heq] at hh
  apply hh.congr_fun
  intro n
  have he : ((r:ℂ)*(z:ℂ))^(n+1)/((n:ℂ)+1) =
      ((r^(n+1)/(n+1):ℝ):ℂ)*phaseChar ((n:ℤ)+1) z := by
    have hz : phaseChar ((n:ℤ)+1) z=(z:ℂ)^(n+1) := by
      rw [show (n:ℤ)+1=((n+1:ℕ):ℤ) by omega]
      simp only [phaseChar,zpow_natCast,Circle.coe_pow]
    rw [hz]
    push_cast
    rw [mul_pow]
    ring
  rw [he]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

lemma circle_log_moments {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    (∫ z : Circle, Real.log (‖1-(r:ℂ)*(z:ℂ)‖^2) ∂circleMeasure)=0 ∧
    (∫ z : Circle, Real.log (‖1-(r:ℂ)*(z:ℂ)‖^2)*(z:ℂ).re ∂circleMeasure)=-r := by
  let T : ℕ → Circle → ℝ := fun n z => (-2*r^(n+1)/(n+1))*(phaseChar (n+1) z).re
  have hb : ∀ n z, |T n z| ≤ 2*r^(n+1) := by
    intro n z
    have hz : |(phaseChar (n+1) z).re| ≤ 1 := (Complex.abs_re_le_norm _).trans_eq (phaseChar_norm _ _)
    have hn : (1:ℝ) ≤ n+1 := by have := Nat.cast_nonneg (α:=ℝ) n; linarith
    calc
      _ = (2*r^(n+1)/(n+1))*|(phaseChar (n+1) z).re| := by dsimp [T]; rw [abs_mul,abs_div,abs_mul,abs_pow,abs_of_nonneg hr,abs_of_pos (by positivity : (0:ℝ)<n+1)]; norm_num
      _ ≤ 2*r^(n+1)/(n+1) := by nlinarith [div_nonneg (by positivity : 0 ≤ 2*r^(n+1)) (by positivity : (0:ℝ) ≤ n+1)]
      _ ≤ 2*r^(n+1) := div_le_self (by positivity) hn
  have hsum : Summable (fun n : ℕ => 2*r^(n+1)) := by
    simpa only [pow_succ,mul_assoc,mul_left_comm,mul_comm] using
      (summable_geometric_of_lt_one hr hr1).mul_left (2*r)
  have hzre : ∀ z : Circle, |(z:ℂ).re| ≤ 1 := fun z => (Complex.abs_re_le_norm _).trans_eq z.norm_coe
  have hmean : HasSum (fun n => ∫ z, T n z ∂circleMeasure) (∫ z : Circle, Real.log (‖1-(r:ℂ)*(z:ℂ)‖^2) ∂circleMeasure) := by
    apply hasSum_integral_of_dominated_convergence (fun n _ => 2*r^(n+1))
    · intro n; exact (continuous_const.mul (Complex.continuous_re.comp (phaseChar_continuous _))).aestronglyMeasurable
    · intro n; exact Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hb n z)
    · exact Eventually.of_forall (fun _ => hsum)
    · exact integrable_const _
    · exact Eventually.of_forall (hasSum_circle_log hr hr1)
  have hcos : HasSum (fun n => ∫ z, T n z*(z:ℂ).re ∂circleMeasure) (∫ z : Circle, Real.log (‖1-(r:ℂ)*(z:ℂ)‖^2)*(z:ℂ).re ∂circleMeasure) := by
    apply hasSum_integral_of_dominated_convergence (fun n _ => 2*r^(n+1))
    · intro n; exact ((continuous_const.mul (Complex.continuous_re.comp (phaseChar_continuous _))).mul (Complex.continuous_re.comp continuous_subtype_val)).aestronglyMeasurable
    · intro n; exact Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs,abs_mul]
        calc _ ≤ (2*r^(n+1))*1 := mul_le_mul (hb n z) (hzre z) (abs_nonneg _) (by positivity)
             _ = _ := mul_one _)
    · exact Eventually.of_forall (fun _ => hsum)
    · exact integrable_const _
    · exact Eventually.of_forall (fun z => (hasSum_circle_log hr hr1 z).mul_right _)
  have hm0 : ∀ n, (∫ z, T n z ∂circleMeasure)=0 := by
    intro n
    dsimp only [T]
    rw [integral_const_mul,circle_real_char_mean (by omega : (n:ℤ)+1 ≠ 0),mul_zero]
  have hc0 : ∀ n, (∫ z : Circle, T n z*(z:ℂ).re ∂circleMeasure)=if n=0 then -r else 0 := by
    intro n
    simp only [T,mul_assoc]
    rw [integral_const_mul]
    have hh := circle_real_char_cos (Nat.succ_pos n)
    simp only [Nat.succ_eq_add_one, Nat.cast_add,Nat.cast_one] at hh
    rw [hh]
    by_cases hn : n=0
    · subst n
      norm_num
      ring
    · simp [hn]
  constructor
  · simpa only [hm0,tsum_zero] using hmean.tsum_eq.symm
  · simpa only [hc0,tsum_ite_eq,mem_univ,ite_true] using hcos.tsum_eq.symm

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseLogFactor
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
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma logFactor_discriminant (q ε : ℝ) :
    (1-q^2)^2 ≤ (1+q^2+ε^2)^2-4*q^2 := by
  linarith [sq_nonneg ε,mul_nonneg (sq_nonneg ε) (sq_nonneg q),sq_nonneg (ε^2)]

lemma logFactor_one_le (q ε : ℝ) : 1 ≤ logFactor q ε := by
  have hh := Real.sqrt_le_sqrt (logFactor_discriminant q ε)
  rw [Real.sqrt_sq_eq_abs] at hh
  have hl := le_abs_self (1-q^2)
  unfold logFactor
  linarith [sq_nonneg ε]

lemma logFactor_pos (q ε : ℝ) : 0 < logFactor q ε := lt_of_lt_of_le zero_lt_one (logFactor_one_le q ε)

lemma logFactor_gt {q ε : ℝ} (hε : ε ≠ 0) : q < logFactor q ε := by
  have he := sq_pos_of_ne_zero hε
  have hs := Real.sqrt_nonneg ((1+q^2+ε^2)^2-4*q^2)
  unfold logFactor
  linarith [sq_nonneg (q-1)]

lemma logFactor_equation (q ε : ℝ) :
    logFactor q ε+q^2/logFactor q ε=1+q^2+ε^2 := by
  have hd : 0 ≤ (1+q^2+ε^2)^2-4*q^2 := (sq_nonneg _).trans (logFactor_discriminant q ε)
  have hs := Real.sq_sqrt hd
  have hl := (logFactor_pos q ε).ne'
  field_simp
  unfold logFactor
  linarith

lemma logFactor_norm_identity (q ε : ℝ) (z : Circle) :
    ‖1-(q:ℂ)*(z:ℂ)‖^2+ε^2 = logFactor q ε*‖1-(q/logFactor q ε:ℝ)*(z:ℂ)‖^2 := by
  have hz : (z:ℂ).re^2+(z:ℂ).im^2=1 := by
    have hh := Complex.sq_norm (z:ℂ)
    rw [z.norm_coe] at hh
    simp only [Complex.normSq_apply] at hh
    linarith
  have he := logFactor_equation q ε
  have hl := (logFactor_pos q ε).ne'
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,zero_sub,add_zero]
  field_simp at he ⊢
  linarith [congrArg (fun t => q^2*t) hz,congrArg (fun t => logFactor q ε*q^2*t) hz]

lemma logFactor_zero (q : ℝ) : logFactor q 0 = max 1 (q^2) := by
  have he : (1+q^2+(0:ℝ)^2)^2-4*q^2=(1-q^2)^2 := by ring
  unfold logFactor
  rw [he,Real.sqrt_sq_eq_abs]
  by_cases hq : q^2 ≤ 1
  · rw [abs_of_nonneg (by linarith),max_eq_left hq]; ring
  · rw [abs_of_nonpos (by linarith),max_eq_right (by linarith)]; ring

lemma logFactor_continuous : Continuous (fun p : ℝ × ℝ => logFactor p.1 p.2) := by
  unfold logFactor
  fun_prop

lemma circle_log_continuous {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Continuous (fun z : Circle => Real.log (‖1-(r:ℂ)*(z:ℂ)‖^2)) := by
  apply Continuous.log
  · fun_prop
  · intro z
    apply pow_ne_zero
    apply norm_ne_zero_iff.mpr
    intro hz
    have hh := congrArg norm (sub_eq_zero.mp hz)
    rw [norm_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,z.norm_coe,mul_one] at hh
    linarith

lemma regularized_circle_moments {q ε : ℝ} (hq : 0 ≤ q) (hε : ε ≠ 0) (f : ℝ) :
    (∫ z : Circle, regularizedLog 1 ε ((q:ℂ)*(z:ℂ))*(1+f*(z:ℂ).re) ∂circleMeasure) =
      Real.log (logFactor q ε)-Real.log (1+ε^2)-f*q/logFactor q ε := by
  let r := q/logFactor q ε
  have hr : 0 ≤ r := div_nonneg hq (logFactor_pos q ε).le
  have hr1 : r < 1 := (div_lt_one (logFactor_pos q ε)).mpr (logFactor_gt hε)
  have hmom := circle_log_moments hr hr1
  have hi := compact_continuous_integrable (μ := circleMeasure) (circle_log_continuous hr hr1)
  have hic : Integrable (fun z : Circle => Real.log (‖1-(r:ℂ)*(z:ℂ)‖^2)*(z:ℂ).re) circleMeasure := by
    apply compact_continuous_integrable
    exact (circle_log_continuous hr hr1).mul (by fun_prop)
  have he : ∀ z : Circle, regularizedLog 1 ε ((q:ℂ)*(z:ℂ)) =
      Real.log (logFactor q ε)-Real.log (1+ε^2)+Real.log (‖1-(r:ℂ)*(z:ℂ)‖^2) := by
    intro z
    rw [regularizedLog_eq 1 ε _ hε]
    simp only [Complex.ofReal_one,one_mul]
    rw [logFactor_norm_identity,Real.log_mul (logFactor_pos q ε).ne' (by
      have hh := logFactor_norm_identity q ε z
      have hp : 0 < ‖1-(q:ℂ)*(z:ℂ)‖^2+ε^2 := by positivity
      exact ne_of_gt (pos_of_mul_pos_right (hh ▸ hp) (logFactor_pos q ε).le))]
    dsimp [r]
    ring
  let A := Real.log (logFactor q ε)-Real.log (1+ε^2)
  let g : Circle → ℝ := fun z => Real.log (‖1-(r:ℂ)*(z:ℂ)‖^2)
  have hz : (∫ z : Circle, (z:ℂ).re ∂circleMeasure)=0 := by
    simpa [phaseChar] using circle_real_char_mean (by norm_num : (1:ℤ) ≠ 0)
  have he' : ∀ z : Circle, regularizedLog 1 ε ((q:ℂ)*(z:ℂ))*(1+f*(z:ℂ).re) =
      A+(A*f)*(z:ℂ).re+g z+f*(g z*(z:ℂ).re) := by
    intro z
    rw [he]
    dsimp [A,g]
    ring
  simp_rw [he']
  have hiz : Integrable (fun z : Circle => (z:ℂ).re) circleMeasure :=
    compact_continuous_integrable (by fun_prop)
  erw [integral_add (((integrable_const A).add (hiz.const_mul _)).add hi) (hic.const_mul _),
    integral_add ((integrable_const A).add (hiz.const_mul _)) hi,
    integral_add (integrable_const A) (hiz.const_mul _),integral_const_mul,integral_const_mul]
  change (∫ z : Circle, A ∂circleMeasure)+(A*f)*_+_+f*_=_
  rw [hmom.1,hmom.2,hz]
  simp [A,r]
  ring

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseLogApproximation
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
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma logFactor_complex_identity (ε : ℝ) (v : ℂ) :
    ‖1-v‖^2+ε^2 = logFactor ‖v‖ ε*‖1-v/(logFactor ‖v‖ ε:ℂ)‖^2 := by
  have hl := (logFactor_pos ‖v‖ ε).ne'
  have he := logFactor_equation ‖v‖ ε
  have hn := Complex.sq_norm v
  simp only [Complex.normSq_apply] at hn
  have hdiv : v/(logFactor ‖v‖ ε:ℂ)=( (logFactor ‖v‖ ε)⁻¹:ℝ) * v := by
    push_cast; ring
  rw [hdiv]
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,
    Complex.one_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,zero_sub,add_zero]
  field_simp at he ⊢
  nlinarith

lemma logFactor_ratio_bound {ε : ℝ} (he : ε ≠ 0) {A : ℝ} (hA : 0 ≤ A) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∀ q ∈ Icc 0 A, q/logFactor q ε ≤ θ := by
  have hc : Continuous (fun q : ℝ => q/logFactor q ε) :=
    continuous_id.div (logFactor_continuous.comp (continuous_id.prodMk continuous_const))
      (fun q => (logFactor_pos q ε).ne')
  obtain ⟨q,hq,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hA) hc.continuousOn
  let θ := (1+q/logFactor q ε)/2
  have hr : q/logFactor q ε < 1 := (div_lt_one (logFactor_pos q ε)).mpr (logFactor_gt he)
  have hr0 : 0 ≤ q/logFactor q ε := div_nonneg hq.1 (logFactor_pos q ε).le
  refine ⟨θ,by dsimp [θ]; linarith,by dsimp [θ]; linarith,?_⟩
  intro r hr'
  exact (hmax hr').trans (by dsimp [θ]; linarith)

lemma logNormalized_norm_lt {ε : ℝ} (he : ε ≠ 0) (v : ℂ) : ‖logNormalized ε v‖ < 1 := by
  rw [logNormalized,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (logFactor_pos _ _)]
  exact (div_lt_one (logFactor_pos _ _)).mpr (logFactor_gt he)

lemma regularizedLog_hasSum {ε : ℝ} (he : ε ≠ 0) (v : ℂ) :
    HasSum (fun n => logTerm ε n v) (regularizedLog 1 ε v-logMean ε v) := by
  have hs := (Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log' (logNormalized_norm_lt he v))).mul_left (-2)
  have heq : Real.log (‖1-v‖^2+ε^2)=Real.log (logFactor ‖v‖ ε)+Real.log (‖1-logNormalized ε v‖^2) := by
    rw [logFactor_complex_identity]
    apply Real.log_mul (logFactor_pos _ _).ne'
    apply pow_ne_zero
    apply norm_ne_zero_iff.mpr
    intro hz
    have hh := congrArg norm (sub_eq_zero.mp hz)
    rw [norm_one] at hh
    exact (ne_of_lt (logNormalized_norm_lt he v)) hh.symm
  have hval : -2 * (-Complex.log (1-logNormalized ε v)).re = regularizedLog 1 ε v-logMean ε v := by
    rw [Complex.neg_re,Complex.log_re,regularizedLog_eq 1 ε v he]
    simp only [Complex.ofReal_one,one_mul,logMean]
    rw [heq,Real.log_pow]
    ring
  rw [hval] at hs
  apply hs.congr_fun
  intro n
  simp only [logTerm,Complex.div_re,Complex.add_re,Complex.natCast_re,Complex.one_re,
    Complex.add_im,Complex.natCast_im,Complex.one_im,add_zero,mul_zero,add_zero,
    Complex.normSq_apply]
  field_simp
  ring

lemma logTerm_bound {ε θ : ℝ} (hθ : 0 ≤ θ) {v : ℂ} (hv : ‖logNormalized ε v‖ ≤ θ) (n : ℕ) :
    |logTerm ε n v| ≤ 2*θ^(n+1) := by
  have hn : (1:ℝ) ≤ n+1 := by have := Nat.cast_nonneg (α:=ℝ) n; linarith
  calc
    _ = 2*|((logNormalized ε v)^(n+1)).re|/(n+1) := by
      simp only [logTerm,abs_div,abs_mul,abs_of_pos (by positivity : (0:ℝ)<n+1)]
      norm_num
    _ ≤ 2*‖(logNormalized ε v)^(n+1)‖/(n+1) := by gcongr; exact Complex.abs_re_le_norm _
    _ ≤ 2*θ^(n+1)/(n+1) := by rw [norm_pow]; gcongr
    _ ≤ 2*θ^(n+1) := div_le_self (by positivity) hn

lemma logTruncation_error {ε θ : ℝ} (he : ε ≠ 0) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    {v : ℂ} (hv : ‖logNormalized ε v‖ ≤ θ) (M : ℕ) :
    |regularizedLog 1 ε v-logTruncation ε M v| ≤ 2*θ^(M+1)/(1-θ) := by
  have hsum := regularizedLog_hasSum he v
  have htail : regularizedLog 1 ε v-logTruncation ε M v = ∑' n : ℕ, logTerm ε (n+M) v := by
    have h := hsum.summable.sum_add_tsum_nat_add M
    rw [hsum.tsum_eq] at h
    dsimp [logTruncation]
    linarith
  rw [htail,← Real.norm_eq_abs]
  have hbound : ∀ n : ℕ, ‖logTerm ε (n+M) v‖ ≤ (2*θ^(M+1))*θ^n := by
    intro n
    rw [Real.norm_eq_abs]
    calc
      _ ≤ 2*θ^(n+M+1) := logTerm_bound hθ hv (n+M)
      _ = _ := by rw [show n+M+1=(M+1)+n by omega,pow_add]; ring
  have hg : Summable (fun n : ℕ => (2*θ^(M+1))*θ^n) := (summable_geometric_of_lt_one hθ hθ1).mul_left _
  have hn : Summable (fun n : ℕ => ‖logTerm ε (n+M) v‖) :=
    hg.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  calc
    _ ≤ ∑' n : ℕ, ‖logTerm ε (n+M) v‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n : ℕ, (2*θ^(M+1))*θ^n := hn.tsum_le_tsum hbound hg
    _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one hθ hθ1]; rfl

lemma logNormalized_continuous (ε : ℝ) : Continuous (logNormalized ε) := by
  unfold logNormalized
  exact continuous_id.div
    (Complex.continuous_ofReal.comp (logFactor_continuous.comp (continuous_norm.prodMk continuous_const)))
    (fun v => Complex.ofReal_ne_zero.mpr (logFactor_pos _ _).ne')

lemma logMean_continuous (ε : ℝ) : Continuous (logMean ε) := by
  unfold logMean
  exact ((logFactor_continuous.comp (continuous_norm.prodMk continuous_const)).log
    (fun v => (logFactor_pos _ _).ne')).sub continuous_const

lemma logTerm_continuous (ε : ℝ) (n : ℕ) : Continuous (logTerm ε n) := by
  unfold logTerm
  exact (continuous_const.mul (Complex.continuous_re.comp ((logNormalized_continuous ε).pow _))).div_const _

lemma logTruncation_continuous (ε : ℝ) (M : ℕ) : Continuous (logTruncation ε M) := by
  unfold logTruncation
  exact (logMean_continuous ε).add (continuous_finsetSum _ (fun n _ => logTerm_continuous ε n))

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseLogPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler12650_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma logNormalized_unit_mul (ε : ℝ) {c : ℂ} (hc : ‖c‖=1) (v : ℂ) :
    logNormalized ε (c*v)=c*logNormalized ε v := by
  simp only [logNormalized,norm_mul,hc,one_mul,mul_div_assoc]

lemma logMean_unit_mul (ε : ℝ) {c : ℂ} (hc : ‖c‖=1) (v : ℂ) :
    logMean ε (c*v)=logMean ε v := by simp only [logMean,norm_mul,hc,one_mul]

lemma logNormalized_peak_phase (ε : ℝ) (c : ℂ) (P : Finset Sphere) (k n : ℕ) :
    ∀ z : Circle, ∀ ξ : Sphere,
      (logNormalized ε (c*peakPolynomial P k (phaseAction z ξ)))^n =
        phaseChar (k*n) z*(logNormalized ε (c*peakPolynomial P k ξ))^n := by
  intro z ξ
  rw [phaseAction_coe,peakPolynomial_homogeneous]
  have he : c*((z:ℂ)^k*peakPolynomial P k ξ)=(z:ℂ)^k*(c*peakPolynomial P k ξ) := by ring
  rw [he,logNormalized_unit_mul ε (by rw [norm_pow,z.norm_coe,one_pow] : ‖(z:ℂ)^k‖=1),mul_pow,← pow_mul]
  simp only [← Nat.cast_mul,phaseChar,zpow_natCast,Circle.coe_pow]

lemma logMean_peak_phase (ε : ℝ) (c : ℂ) (P : Finset Sphere) (k : ℕ) :
    ∀ z : Circle, ∀ ξ : Sphere,
      (logMean ε (c*peakPolynomial P k (phaseAction z ξ)):ℂ) =
        phaseChar (0:ℕ) z*(logMean ε (c*peakPolynomial P k ξ):ℂ) := by
  intro z ξ
  rw [phaseAction_coe,peakPolynomial_homogeneous]
  have he : c*((z:ℂ)^k*peakPolynomial P k ξ)=(z:ℂ)^k*(c*peakPolynomial P k ξ) := by ring
  rw [he,logMean_unit_mul ε (by rw [norm_pow,z.norm_coe,one_pow] : ‖(z:ℂ)^k‖=1)]
  simp

lemma probability_integral_error {X : Type uKahler12650_1} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    {E : ℝ} (h : ∀ x, |f x-g x| ≤ E) : |(∫ x,f x ∂μ)-(∫ x,g x ∂μ)| ≤ E := by
  rw [← integral_sub hf hg,← Real.norm_eq_abs]
  calc
    _ ≤ ∫ x, ‖f x-g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, E ∂μ := integral_mono (hf.sub hg).norm (integrable_const E)
      (fun x => by simpa only [Real.norm_eq_abs] using h x)
    _ = E := by simp

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseRadialSubstitution
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
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma weight_profile_integral {f b : ℝ → ℝ} (hf : Continuous f) (hb : Continuous b)
    (hode : ∀ y, HasDerivAt b (b y+f y) y) {R : ℝ} (hR : 0 ≤ R)
    (hzero : b 0=0) (htail : b R=0) (v : ℝ) :
    (∫ y in 0..R, Real.exp (-v*y)*(f y+(1-v)*b y)) = 0 := by
  have hd : ∀ y, HasDerivAt (fun y => Real.exp (-v*y)*b y)
      (Real.exp (-v*y)*(f y+(1-v)*b y)) y := by
    intro y
    have hh := (((hasDerivAt_id y).const_mul (-v)).exp).mul (hode y)
    convert! hh using 1; dsimp [id]; ring
  have hc : Continuous (fun y => Real.exp (-v*y)*(f y+(1-v)*b y)) := by fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => hd y) (hc.intervalIntegrable 0 R)
  rw [intervalIntegral.integral_of_le hR] at hh ⊢
  simpa [hzero,htail] using hh

lemma log_radial_substitution {k R : ℝ} (hk : 0 < k) (hR : 0 < R)
    {F : ℝ → ℂ} (hF : Continuous F) :
    (∫ t in Real.exp (-2*R/k)..1, (t⁻¹:ℝ) • F (-k/2*Real.log t)) =
      (2/k:ℝ) • ∫ y in 0..R, F y := by
  let g : ℝ → ℂ := fun t => (t⁻¹:ℝ) • F (-k/2*Real.log t)
  let e : ℝ → ℝ := fun y => Real.exp (-2*y/k)
  let e' : ℝ → ℝ := fun y => (-2/k)*Real.exp (-2*y/k)
  have he : ∀ y ∈ uIcc 0 R, HasDerivAt e (e' y) y := by
    rw [uIcc_of_le hR.le]
    intro y hy
    convert! (((hasDerivAt_id y).const_mul (-2)).div_const k).exp using 1; dsimp [e,e']; ring
  have he' : ContinuousOn e' (uIcc 0 R) := by unfold e'; fun_prop
  have heg : ContinuousOn g (e '' uIcc 0 R) := by
    intro t ht
    obtain ⟨y,hy,rfl⟩ := ht
    have hp : 0 < e y := Real.exp_pos _
    exact ((continuousAt_id.inv₀ hp.ne').smul
      (hF.continuousAt.comp ((continuousAt_const.mul (Real.continuousAt_log hp.ne'))))).continuousWithinAt
  have hs := intervalIntegral.integral_deriv_smul_comp' he he' heg
  have hcomp : ∀ y, e' y • g (e y) = (-2/k:ℝ) • F y := by
    intro y
    change ((-2/k)*Real.exp (-2*y/k):ℝ) •
      ((Real.exp (-2*y/k))⁻¹:ℝ) • F (-k/2*Real.log (Real.exp (-2*y/k))) = _
    rw [smul_smul,Real.log_exp]
    have hh : -k/2*(-2*y/k)=y := by field_simp
    rw [hh]
    congr 1
    field_simp
  change (∫ y in 0..R, e' y • g (e y)) = _ at hs
  simp_rw [hcomp] at hs
  rw [intervalIntegral.integral_smul] at hs
  have he0 : e 0=1 := by simp [e]
  have heR : e R=Real.exp (-2*R/k) := rfl
  rw [he0,heR] at hs
  conv_rhs at hs => rw [intervalIntegral.integral_symm]
  change _ = -(∫ t in Real.exp (-2*R/k)..1, (t⁻¹:ℝ) • F (-k/2*Real.log t)) at hs
  have hh := congrArg Neg.neg hs
  simpa only [neg_neg,← neg_smul,neg_div,neg_neg] using hh.symm

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler13116_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
namespace PinchedHartogs.BaseConstruction

lemma densityMeasure_integral {W : Base → ℝ} (hW : Continuous W) (hpos : ∀ ξ : Sphere, 0 ≤ W ξ)
    {E : Type uKahler13116_1} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Sphere → E) :
    (∫ ξ, g ξ ∂densityMeasure W) = ∫ ξ, W ξ • g ξ ∂sigma := by
  change (∫ ξ, g ξ ∂sigma.withDensity (fun ξ : Sphere => ENNReal.ofReal (W ξ))) = _
  have hm : Measurable (fun ξ : Sphere => ENNReal.ofReal (W ξ)) := (hW.comp continuous_subtype_val).measurable.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hm (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) g]
  simp_rw [ENNReal.toReal_ofReal (hpos _)]

lemma density_orbit_mean {Q : ℕ} (hQ : 2 ≤ Q) {R E : ℝ} (hER : E < R)
    {f b : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (P : ℕ → Finset Sphere) (j : ℕ) :
    OrbitMeanOne (density Q R f b P j) := by
  classical
  have hq : 0 < Q := by omega
  induction j with
  | zero => exact orbitMean_one
  | succ j ih =>
    intro ξ
    have hw := density_smooth hq hER hf hb htail P j
    have hi : Integrable (fun z : Circle => density Q R f b P j ((z:ℂ) • (ξ:Base))) circleMeasure := by
      apply compact_continuous_integrable
      exact hw.continuous.comp ((continuous_subtype_val : Continuous (fun z : Circle => (z:ℂ))).smul continuous_const)
    have hic : ∀ p ∈ P (Q^(j+1)), Integrable (fun z : Circle => densityCorrection (Q^(j+1)) R f b (density Q R f b P j) p ((z:ℂ) • (ξ:Base))) circleMeasure := by
      intro p hp
      apply compact_continuous_integrable
      exact (densityCorrection_smooth (pow_pos hq _) hER hf hb hw htail p).continuous.comp ((continuous_subtype_val : Continuous (fun z : Circle => (z:ℂ))).smul continuous_const)
    simp only [density]
    rw [integral_add hi (integrable_finsetSum _ hic),integral_finsetSum _ hic,ih ξ]
    have hz : (∑ p ∈ P (Q^(j+1)), ∫ z : Circle, densityCorrection (Q^(j+1)) R f b (density Q R f b P j) p ((z:ℂ) • (ξ:Base)) ∂circleMeasure)=0 := by
      apply Finset.sum_eq_zero
      intro p hp
      exact densityCorrection_orbit_zero (hw.differentiable (by simp)) (density_bandwidth hq hER hf hb htail P j) (densityBandwidth_lt hQ j) R f b p ξ
    rw [hz,add_zero]

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseLaterMoments
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
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma densityBandwidth_le_two {Q : ℕ} (hQ : 2 ≤ Q) (j : ℕ) : densityBandwidth Q j ≤ 2*Q^j := by
  cases j with
  | zero => simp [densityBandwidth]
  | succ j =>
    rw [densityBandwidth_succ]
    have h := densityBandwidth_lt hQ j
    omega

lemma density_low_moment_persist {a : ℝ} (pr : RadialProfiles a) {Q M i N n : ℕ}
    (hQ : 2 ≤ Q) (hM : M+2 < Q) (hiN : i ≤ N) (hn : n ≤ M*Q^i)
    (P : ℕ → Finset Sphere) {V : Sphere → ℂ} (hV : Continuous V)
    (hphase : ∀ z ξ, V (phaseAction z ξ)=phaseChar n z*V ξ) :
    (∫ ξ : Sphere, (V ξ).re*density Q pr.R pr.f pr.b P N ξ ∂sigma)=
      ∫ ξ : Sphere, (V ξ).re*density Q pr.R pr.f pr.b P i ξ ∂sigma := by
  induction N,hiN using Nat.le_induction with
  | base => rfl
  | succ N hiN ih =>
    have hp : Q^i ≤ Q^N := Nat.pow_le_pow_right (by omega : 0 < Q) hiN
    have hb := densityBandwidth_le_two hQ N
    have hn' : n ≤ M*Q^N := hn.trans (Nat.mul_le_mul_left _ hp)
    have hpow : 0 < Q^N := pow_pos (by omega) _
    have hgap : n+densityBandwidth Q N < Q^(N+1) := by
      rw [pow_succ]
      nlinarith
    rw [density_low_moment_step pr (by omega) P N hgap hV hphase,ih]

lemma logTruncation_density_persist {a : ℝ} (pr : RadialProfiles a) {Q M i N : ℕ}
    (hQ : 2 ≤ Q) (hM : M+2 < Q) (hiN : i ≤ N) (P : ℕ → Finset Sphere)
    (ε : ℝ) (c : ℂ) :
    (∫ ξ : Sphere, logTruncation ε M (c*peakPolynomial (P (Q^i)) (Q^i) ξ)*
      density Q pr.R pr.f pr.b P N ξ ∂sigma)=
    ∫ ξ : Sphere, logTruncation ε M (c*peakPolynomial (P (Q^i)) (Q^i) ξ)*
      density Q pr.R pr.f pr.b P i ξ ∂sigma := by
  classical
  let V : Sphere → ℂ := fun ξ => c*peakPolynomial (P (Q^i)) (Q^i) ξ
  have hV : Continuous V := continuous_const.mul ((peakPolynomial_analytic _ _).continuous.comp continuous_subtype_val)
  have hW (j : ℕ) : Continuous (fun ξ : Sphere => density Q pr.R pr.f pr.b P j ξ) :=
    (density_smooth (by omega : 0 < Q) pr.cutoff_lt pr.smooth_f pr.smooth_b pr.tail P j).continuous.comp continuous_subtype_val
  have hm : (∫ ξ : Sphere, logMean ε (V ξ)*density Q pr.R pr.f pr.b P N ξ ∂sigma)=
      ∫ ξ : Sphere, logMean ε (V ξ)*density Q pr.R pr.f pr.b P i ξ ∂sigma := by
    exact density_low_moment_persist pr hQ hM hiN (Nat.zero_le _) P
      (Complex.continuous_ofReal.comp ((logMean_continuous ε).comp hV)) (logMean_peak_phase ε c _ _)
  have ht : ∀ n ∈ Finset.range M,
      (∫ ξ : Sphere, logTerm ε n (V ξ)*density Q pr.R pr.f pr.b P N ξ ∂sigma)=
      ∫ ξ : Sphere, logTerm ε n (V ξ)*density Q pr.R pr.f pr.b P i ξ ∂sigma := by
    intro n hn
    have hbound : Q^i*(n+1) ≤ M*Q^i := by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (Q^i) (show n+1 ≤ M by have := Finset.mem_range.mp hn; omega)
    have he : (∫ ξ : Sphere, ((logNormalized ε (V ξ))^(n+1)).re*density Q pr.R pr.f pr.b P N ξ ∂sigma)=
        ∫ ξ : Sphere, ((logNormalized ε (V ξ))^(n+1)).re*density Q pr.R pr.f pr.b P i ξ ∂sigma := density_low_moment_persist pr hQ hM hiN hbound P
      (((logNormalized_continuous ε).comp hV).pow (n+1)) (logNormalized_peak_phase ε c _ _ (n+1))
    have hfun : ∀ ξ : Sphere, ∀ j : ℕ, logTerm ε n (V ξ)*density Q pr.R pr.f pr.b P j ξ=
      (-2/(n+1))*(((logNormalized ε (V ξ))^(n+1)).re*density Q pr.R pr.f pr.b P j ξ) := by
      intro ξ j; dsimp [logTerm]; ring
    simp_rw [hfun,integral_const_mul,he]
  have he (j : ℕ) : (∫ ξ : Sphere, logTruncation ε M (V ξ)*density Q pr.R pr.f pr.b P j ξ ∂sigma)=
      (∫ ξ : Sphere, logMean ε (V ξ)*density Q pr.R pr.f pr.b P j ξ ∂sigma)+
      ∑ n ∈ Finset.range M, ∫ ξ : Sphere, logTerm ε n (V ξ)*density Q pr.R pr.f pr.b P j ξ ∂sigma := by
    simp only [logTruncation,add_mul,Finset.sum_mul]
    have him : Integrable (fun ξ : Sphere => logMean ε (V ξ)*density Q pr.R pr.f pr.b P j ξ) sigma :=
      compact_continuous_integrable (((logMean_continuous ε).comp hV).mul (hW j))
    have hit : ∀ n ∈ Finset.range M, Integrable (fun ξ : Sphere => logTerm ε n (V ξ)*density Q pr.R pr.f pr.b P j ξ) sigma :=
      fun n _ => compact_continuous_integrable (((logTerm_continuous ε n).comp hV).mul (hW j))
    rw [integral_add him (integrable_finsetSum _ hit),integral_finsetSum _ hit]
  change (∫ ξ : Sphere, logTruncation ε M (V ξ)*density Q pr.R pr.f pr.b P N ξ ∂sigma)=_
  rw [he N,he i,hm]
  congr 1
  exact Finset.sum_congr rfl ht

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseLaterComparison
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
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma regularizedLog_scale (a ε : ℝ) (v : ℂ) : regularizedLog a ε v=regularizedLog 1 ε ((a:ℂ)*v) := by
  simp only [regularizedLog,Complex.ofReal_one,one_mul]

lemma density_log_comparison {a : ℝ} (pr : RadialProfiles a) {Q M i N : ℕ}
    (hQ : 2 ≤ Q) (hM : M+2 < Q) (hiN : i ≤ N) (P : ℕ → Finset Sphere)
    {ε θ : ℝ} (he : ε ≠ 0) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (c : ℂ)
    (hratio : ∀ ξ : Sphere, ‖logNormalized ε (c*peakPolynomial (P (Q^i)) (Q^i) ξ)‖ ≤ θ)
    (hposi : ∀ ξ : Sphere, 0 ≤ density Q pr.R pr.f pr.b P i ξ)
    (hposN : ∀ ξ : Sphere, 0 ≤ density Q pr.R pr.f pr.b P N ξ)
    [IsProbabilityMeasure (densityMeasure (density Q pr.R pr.f pr.b P i))]
    [IsProbabilityMeasure (densityMeasure (density Q pr.R pr.f pr.b P N))] :
    |(∫ ξ : Sphere, regularizedLog 1 ε (c*peakPolynomial (P (Q^i)) (Q^i) ξ) ∂densityMeasure (density Q pr.R pr.f pr.b P N))-
      (∫ ξ : Sphere, regularizedLog 1 ε (c*peakPolynomial (P (Q^i)) (Q^i) ξ) ∂densityMeasure (density Q pr.R pr.f pr.b P i))| ≤
      4*θ^(M+1)/(1-θ) := by
  let V : Sphere → ℂ := fun ξ => c*peakPolynomial (P (Q^i)) (Q^i) ξ
  have hV : Continuous V := continuous_const.mul ((peakPolynomial_analytic _ _).continuous.comp continuous_subtype_val)
  let f : Sphere → ℝ := fun ξ => regularizedLog 1 ε (V ξ)
  let g : Sphere → ℝ := fun ξ => logTruncation ε M (V ξ)
  have hf : Continuous f := (regularizedLog_contDiff 1 he).continuous.comp hV
  have hg : Continuous g := (logTruncation_continuous ε M).comp hV
  have hb : ∀ ξ, |f ξ-g ξ| ≤ 2*θ^(M+1)/(1-θ) := fun ξ => logTruncation_error he hθ hθ1 (hratio ξ) M
  have h1 := probability_integral_error (μ := densityMeasure (density Q pr.R pr.f pr.b P N))
    (compact_continuous_integrable hf) (compact_continuous_integrable hg) hb
  have h2 := probability_integral_error (μ := densityMeasure (density Q pr.R pr.f pr.b P i))
    (compact_continuous_integrable hf) (compact_continuous_integrable hg) hb
  have hW (j : ℕ) : Continuous (density Q pr.R pr.f pr.b P j) :=
    (density_smooth (by omega : 0 < Q) pr.cutoff_lt pr.smooth_f pr.smooth_b pr.tail P j).continuous
  have hpersist : (∫ ξ, g ξ ∂densityMeasure (density Q pr.R pr.f pr.b P N))=
      ∫ ξ, g ξ ∂densityMeasure (density Q pr.R pr.f pr.b P i) := by
    rw [densityMeasure_integral (hW N) hposN,densityMeasure_integral (hW i) hposi]
    simp only [smul_eq_mul]
    simpa only [mul_comm] using logTruncation_density_persist pr hQ hM hiN P ε c
  rw [hpersist] at h1
  have hh := abs_sub_le (∫ ξ, f ξ ∂densityMeasure (density Q pr.R pr.f pr.b P N))
    (∫ ξ, g ξ ∂densityMeasure (density Q pr.R pr.f pr.b P i))
    (∫ ξ, f ξ ∂densityMeasure (density Q pr.R pr.f pr.b P i))
  rw [abs_sub_comm (∫ ξ, g ξ ∂densityMeasure (density Q pr.R pr.f pr.b P i))] at hh
  exact hh.trans (by convert add_le_add h1 h2 using 1; ring)

lemma logarithmicTest_later_threshold {a : ℝ} (ha : 0 ≤ a) {ε : ℝ} (he : ε ≠ 0) {d : ℝ} (hd : 0 < d) :
    ∃ M : ℕ, ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ 4*θ^(M+1)/(1-θ) ≤ d ∧
      ∀ q ∈ Icc 0 (a*gaussianConstant), q/logFactor q ε ≤ θ := by
  obtain ⟨θ,hθ,hθ1,hb⟩ := logFactor_ratio_bound he (mul_nonneg ha gaussianConstant_pos.le)
  have ht : Tendsto (fun M : ℕ => 4*θ^(M+1)/(1-θ)) atTop (𝓝 0) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one hθ.le hθ1).mul_const θ
    simpa only [← pow_succ,mul_zero,zero_mul,zero_div] using (hh.const_mul 4).div_const (1-θ)
  obtain ⟨M,hM⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hd))
  exact ⟨M,θ,hθ,hθ1,(hM M le_rfl).le,hb⟩

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseShiftAveraging
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
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma root_invariant_shift_sum {k ℓ : ℕ} (hk : 0 < k) (hl : ℓ < k)
    {V : Circle → ℂ} (hi : Integrable V circleMeasure)
    (hV : ∀ z, V (Circle.exp (2*Real.pi/k)*z)=V z)
    (s : Finset ℤ) (b : ℤ → ℂ) (hband : ∀ n ∈ s, |n| ≤ (ℓ:ℤ)) :
    (∫ z, V z*(∑ n ∈ s, b n*phaseChar ((k:ℤ)+n) z) ∂circleMeasure) =
      (∫ z, V z*phaseChar k z ∂circleMeasure)*(if 0 ∈ s then b 0 else 0) := by
  have hki : Integrable (fun z => V z*phaseChar k z) circleMeasure :=
    hi.mul_bdd (phaseChar_continuous _).aestronglyMeasurable
      (Eventually.of_forall (fun z => (phaseChar_norm _ z).le))
  have hkiV : ∀ z, V (Circle.exp (2*Real.pi/k)*z)*phaseChar k (Circle.exp (2*Real.pi/k)*z)=V z*phaseChar k z := by
    intro z
    rw [hV,phaseChar_mul,phaseChar_root hk,one_mul]
  have hh := root_invariant_phaseSum hk hl hki hkiV s b hband
  rw [phaseSum_mean] at hh
  convert hh using 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    simp only [phaseSum,Finset.mul_sum,phaseChar_add]
    apply Finset.sum_congr rfl
    intro n hn
    ring)

lemma phase_real_integral {V : Circle → ℝ} {A : Circle → ℂ}
    (hi : Integrable (fun z => (V z:ℂ)*A z) circleMeasure) :
    (∫ z, V z*(A z).re ∂circleMeasure)=(∫ z, (V z:ℂ)*A z ∂circleMeasure).re := by
  have he : (∫ z, ((V z:ℂ)*A z).re ∂circleMeasure)=(∫ z, (V z:ℂ)*A z ∂circleMeasure).re := integral_re hi
  simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using he

lemma correction_orbit_averaging {k ℓ : ℕ} (hk : 0 < k) (hl : ℓ < k)
    (R : ℝ) (f b : ℝ → ℝ) {W : Base → ℝ} (hd : Differentiable ℝ W)
    (hb : PhaseBandwidth W ℓ) (hm : ∀ p : Sphere, (∫ z : Circle, W ((z:ℂ) • (p:Base)) ∂circleMeasure)=1)
    (p ξ : Sphere) {V : Circle → ℝ} (hVc : Continuous V)
    (hV : ∀ z, V (Circle.exp (2*Real.pi/k)*z)=V z) :
    (∫ z, V z*densityCorrection k R f b W p ((z:ℂ) • (ξ:Base)) ∂circleMeasure)=
      (∫ z, V z*densityCorrection k R f b (fun _ => 1) p ((z:ℂ) • (ξ:Base)) ∂circleMeasure) := by
  classical
  by_cases hpatch : Real.exp (-R/k) < ‖bracket (ξ:Base) (p:Base)‖
  swap
  · simp only [densityCorrection,circle_bracket_norm,ite_eq_right hpatch,mul_zero,integral_zero]
  have hξ : bracket (ξ:Base) (p:Base) ≠ 0 := norm_pos_iff.mp (lt_trans (Real.exp_pos _) hpatch)
  let q : Sphere := ⟨centralPoint p ξ,by simpa only [Metric.mem_sphere,dist_zero_right] using centralPoint_norm p hξ⟩
  obtain ⟨s,a,hs,he⟩ := hb q
  have hmean : (if 0 ∈ s then a 0 else 0)=1 := by
    rw [← phaseSum_mean]
    simp_rw [← he]
    rw [integral_complex_ofReal,hm,Complex.ofReal_one]
  have hz : 0 ∈ s := by by_contra hz; simp [hz] at hmean
  have ha0 : a 0=1 := by simpa [hz] using hmean
  let C : ℂ := (((‖bracket (ξ:Base) (p:Base)‖^2)⁻¹:ℝ):ℂ)*
    (bracket (ξ:Base) (p:Base)/(‖bracket (ξ:Base) (p:Base)‖:ℂ))^k
  let A : ℤ → ℂ := fun n => C*a n*((f (densityHeight k p ξ)-(n:ℝ)/k*b (densityHeight k p ξ):ℝ):ℂ)
  have hex : ∀ z : Circle, densityCorrection k R f b W p ((z:ℂ) • (ξ:Base))=
      (∑ n ∈ s, A n*phaseChar ((k:ℤ)+n) z).re := by
    intro z
    rw [densityCorrection,circle_bracket_norm,ite_eq_left hpatch]
    exact densityCorrectionRaw_phase_expansion k f b hd p ξ hξ s a he z
  have hcA : Continuous (fun z : Circle => ∑ n ∈ s, A n*phaseChar ((k:ℤ)+n) z) :=
    continuous_finsetSum _ (fun n _ => continuous_const.mul (phaseChar_continuous _))
  have hvi : Integrable (fun z : Circle => (V z:ℂ)) circleMeasure := compact_continuous_integrable (Complex.continuous_ofReal.comp hVc)
  have hhv := root_invariant_shift_sum hk hl hvi (fun z => congrArg Complex.ofReal (hV z)) s A hs
  rw [ite_eq_left hz] at hhv
  have hzero : A 0=C*(f (densityHeight k p ξ):ℂ) := by simp [A,ha0]
  rw [hzero] at hhv
  have heone : ∀ z : Circle, densityCorrection k R f b (fun _ => 1) p ((z:ℂ) • (ξ:Base))=
      ((C*(f (densityHeight k p ξ):ℂ))*phaseChar k z).re := by
    intro z
    rw [densityCorrection,circle_bracket_norm,ite_eq_left hpatch,densityCorrectionRaw_eq_re,
      circle_bracket_norm,bracket_smul,densityHeight_phase]
    have hfder : phaseDerivative (fun _ : Base => (1:ℝ)) (centralPoint p ((z:ℂ) • (ξ:Base)))=0 := by
      simp only [phaseDerivative,(hasFDerivAt_const (1:ℝ) _).fderiv,zero_apply]
    rw [hfder]
    simp only [mul_one,mul_zero,Complex.ofReal_zero,add_zero]
    have hchar : phaseChar (k:ℤ) z=(z:ℂ)^k := by simp only [phaseChar,zpow_natCast,Circle.coe_pow]
    rw [hchar,mul_div_assoc,mul_pow]
    dsimp [C]
    congr 1
    ring
  simp_rw [hex,heone]
  rw [phase_real_integral (compact_continuous_integrable ((Complex.continuous_ofReal.comp hVc).mul hcA)),hhv]
  have hright := phase_real_integral (V := V) (A := fun z : Circle => (C*(f (densityHeight k p ξ):ℂ))*phaseChar k z)
    (compact_continuous_integrable ((Complex.continuous_ofReal.comp hVc).mul (continuous_const.mul (phaseChar_continuous _))))
  rw [hright]
  congr 1
  simp_rw [show ∀ z : Circle, (V z:ℂ)*((C*(f (densityHeight k p ξ):ℂ))*phaseChar k z)=
      ((V z:ℂ)*phaseChar k z)*(C*(f (densityHeight k p ξ):ℂ)) by intro z; ring]
  rw [integral_mul_const]

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseTestAveraging
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
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff ENNReal
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma correction_sigma_average {k ℓ : ℕ} (hk : 0 < k) (hl : ℓ < k)
    {R E : ℝ} (hER : E < R) {f b : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) {W V : Base → ℝ}
    (hW : ContDiff ℝ ∞ W) (hV : Continuous V) (hband : PhaseBandwidth W ℓ) (hm : OrbitMeanOne W)
    (hroot : ∀ ξ : Sphere, V ((Circle.exp (2*Real.pi/k):ℂ) • (ξ:Base))=V ξ) (p : Sphere) :
    (∫ ξ : Sphere, V ξ*densityCorrection k R f b W p ξ ∂sigma)=
      ∫ ξ : Sphere, V ξ*densityCorrection k R f b (fun _ => 1) p ξ ∂sigma := by
  have hs := (densityCorrection_smooth hk hER hf hb hW htail p).continuous
  have hsone := (densityCorrection_smooth hk hER hf hb (contDiff_const (c := (1:ℝ))) htail p).continuous
  erw [sigma_phase_average ((hV.mul hs).comp continuous_subtype_val),
    sigma_phase_average ((hV.mul hsone).comp continuous_subtype_val)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun ξ => by
    change (∫ z : Circle, V ((z:ℂ) • (ξ:Base))*densityCorrection k R f b W p ((z:ℂ) • (ξ:Base)) ∂circleMeasure)=_
    apply correction_orbit_averaging hk hl R f b (hW.differentiable (by norm_num)) hband hm p ξ
    · fun_prop
    · intro z
      simpa only [Circle.coe_mul,mul_smul,phaseAction_coe] using hroot (phaseAction z ξ))

lemma logarithmicTest_root (a ε r : ℝ) (P : Finset Sphere) {k : ℕ} (hk : 0 < k) (ξ : Sphere) :
    logarithmicTest a ε P k ((r:ℂ) • ((Circle.exp (2*Real.pi/k):ℂ) • (ξ:Base)))=
    logarithmicTest a ε P k ((r:ℂ) • (ξ:Base)) := by
  have hrt : (Circle.exp (2*Real.pi/k):ℂ)^k=1 := by
    simpa only [phaseChar,zpow_natCast,Circle.coe_pow] using phaseChar_root hk
  rw [smul_comm (r:ℂ),logarithmicTest,peakPolynomial_homogeneous,hrt,one_mul]
  rfl

theorem logarithmicTests_exact_averaging {a ε : ℝ} (p : RadialProfiles a) (he : ε ≠ 0)
    {Q : ℕ} (hQ : 2 ≤ Q) (P : ℕ → Finset Sphere) (j : ℕ) (r : ℝ) :
    (∫ ξ : Sphere, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ((r:ℂ) • (ξ:Base))*
      density Q p.R p.f p.b P (j+1) ξ ∂sigma) =
    (∫ ξ : Sphere, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ((r:ℂ) • (ξ:Base)) ∂sigma)+
    ∑ v ∈ P (Q^(j+1)), ∫ ξ : Sphere, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ((r:ℂ) • (ξ:Base))*
      densityCorrection (Q^(j+1)) p.R p.f p.b (fun _ => 1) v ξ ∂sigma := by
  have hq : 0 < Q := by omega
  have hk := pow_pos hq (j+1)
  let V : Base → ℝ := fun ξ => logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ((r:ℂ) • ξ)
  let W := density Q p.R p.f p.b P j
  have hV : Continuous V := (logarithmicTest_contDiff a he _ _).continuous.comp (by fun_prop)
  have hW : ContDiff ℝ ∞ W := density_smooth hq p.cutoff_lt p.smooth_f p.smooth_b p.tail P j
  have hband := density_bandwidth hq p.cutoff_lt p.smooth_f p.smooth_b p.tail P j
  have hm := density_orbit_mean hQ p.cutoff_lt p.smooth_f p.smooth_b p.tail P j
  have hgap : densityBandwidth Q j < Q^(j+1) := densityBandwidth_lt hQ j
  have hroot : ∀ ξ : Sphere, V ((Circle.exp (2*Real.pi/(Q^(j+1):ℕ)):ℂ) • (ξ:Base))=V ξ :=
    logarithmicTest_root a ε r _ hk
  have hci : ∀ v : Sphere, Integrable (fun ξ : Sphere => V ξ*densityCorrection (Q^(j+1)) p.R p.f p.b W v ξ) sigma := by
    intro v
    exact compact_continuous_integrable ((hV.mul (densityCorrection_smooth hk p.cutoff_lt p.smooth_f p.smooth_b hW p.tail v).continuous).comp continuous_subtype_val)
  simp only [density,mul_add,Finset.mul_sum]
  change (∫ ξ : Sphere, V ξ*W ξ+∑ v ∈ P (Q^(j+1)), V ξ*densityCorrection (Q^(j+1)) p.R p.f p.b W v ξ ∂sigma)=_
  erw [integral_add (compact_continuous_integrable ((hV.mul hW.continuous).comp continuous_subtype_val)) (integrable_finsetSum (P (Q^(j+1))) (fun v _ => hci v)),integral_finsetSum (P (Q^(j+1))) (fun v _ => hci v)]
  change (∫ ξ : Sphere, V ξ*W ξ ∂sigma)+_=_
  rw [sigma_root_average hk hgap hW.continuous hV hband hm hroot]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  exact correction_sigma_average hk hgap p.cutoff_lt p.smooth_f p.smooth_b p.tail hW hV hband hm hroot v

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePatches
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
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma peakPatch_open (k : ℕ) (R : ℝ) (p : Sphere) : IsOpen (peakPatch k R p) :=
  isOpen_lt continuous_const (((bracket_analytic (p:Base)).continuous.comp continuous_subtype_val).norm)

lemma peakPatch_norm_pos {k : ℕ} {R : ℝ} {p ξ : Sphere} (hξ : ξ ∈ peakPatch k R p) :
    0 < ‖bracket (ξ:Base) (p:Base)‖ := lt_trans (Real.exp_pos _) hξ

lemma patchHeight_nonneg (k : ℕ) (p ξ : Sphere) : 0 ≤ patchHeight k p (ξ:Base) := by
  unfold patchHeight
  exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (Nat.cast_nonneg k)) (Real.log_nonpos (norm_nonneg _) (bracket_norm_le_one ξ p))

lemma peakPatch_iff_height {k : ℕ} (hk : 0 < k) (R : ℝ) (p ξ : Sphere) :
    ξ ∈ peakPatch k R p ↔ 0 < ‖bracket (ξ:Base) (p:Base)‖ ∧ patchHeight k p (ξ:Base) < R := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  constructor
  · intro hξ
    refine ⟨peakPatch_norm_pos hξ,?_⟩
    have hh := Real.log_lt_log (Real.exp_pos (-R/k)) hξ
    rw [Real.log_exp] at hh
    unfold patchHeight
    have hm := (div_lt_iff₀ hk0).mp hh
    linarith
  · rintro ⟨hn,hy⟩
    apply (Real.log_lt_log_iff (Real.exp_pos _) hn).mp
    rw [Real.log_exp]
    apply (div_lt_iff₀ hk0).mpr
    unfold patchHeight at hy
    linarith

lemma peakPatch_radius {k : ℕ} (hk : 0 < k) {R : ℝ} (hR : 0 < R)
    {p ξ : Sphere} (hξ : ξ ∈ peakPatch k R p) :
    Real.sqrt (k:ℝ)*projectiveDistance ξ p < Real.sqrt (2*R) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hnorm := peakPatch_norm_pos hξ
  have he : Real.exp (-R/k)^2 = Real.exp (-2*R/k) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hsq : Real.exp (-2*R/k) < ‖bracket (ξ:Base) (p:Base)‖^2 := by
    rw [← he]
    have hp : Real.exp (-R/k) < ‖bracket (ξ:Base) (p:Base)‖ := hξ
    exact sq_lt_sq₀ (Real.exp_pos _).le (norm_nonneg _) |>.mpr hp
  have hl := Real.one_sub_le_exp_neg (2*R/k)
  rw [← neg_div] at hl
  have hh2 : -(2*R) / (k:ℝ) = -2*R/k := by ring
  rw [hh2] at hl
  have hd := projectiveDistance_sq ξ p
  have hmul : (k:ℝ)*projectiveDistance ξ p^2 < 2*R := by
    have hh : projectiveDistance ξ p^2 < 2*R/k := by linarith
    simpa only [mul_comm] using (lt_div_iff₀ hk0).mp hh
  have hkn := Real.sq_sqrt hk0.le
  have hrn := Real.sq_sqrt (show 0 ≤ 2*R by positivity)
  have hd0 := projectiveDistance_nonneg ξ p
  have hk1 := Real.sqrt_nonneg (k:ℝ)
  have hr1 := Real.sqrt_nonneg (2*R)
  have heq : (Real.sqrt (k:ℝ)*projectiveDistance ξ p)^2 = (k:ℝ)*projectiveDistance ξ p^2 := by rw [mul_pow,hkn]
  nlinarith

lemma peakPatch_disjoint {k : ℕ} (hk : 0 < k) {R D : ℝ} (hR : 0 < R)
    (hD : 2*Real.sqrt (2*R) < D) {P : Finset Sphere}
    (hP : ProjectivelySeparated (D/Real.sqrt k) P) :
    (P : Set Sphere).PairwiseDisjoint (peakPatch k R) := by
  intro p hp q hq hpq
  apply Set.disjoint_left.mpr
  intro ξ hξp hξq
  have hs : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  have hp1 := peakPatch_radius hk hR hξp
  have hq1 := peakPatch_radius hk hR hξq
  have hh := hP p hp q hq hpq
  have ht := projectiveDistance_triangle p ξ q
  rw [projectiveDistance_symm p ξ] at ht
  have hm := mul_le_mul_of_nonneg_left ht hs.le
  have hd := (div_le_iff₀ hs).mp hh
  linarith

lemma peakPatch_single {k : ℕ} (hk : 1 ≤ k) {R D : ℝ} (hR : 0 < R)
    (hD : 1 ≤ D) (hDR : Real.sqrt (2*R) ≤ D) {P : Finset Sphere}
    (hP : ProjectivelySeparated (D/Real.sqrt k) P) {p ξ : Sphere}
    (hp : p ∈ P) (hξ : ξ ∈ peakPatch k R p) :
    ‖peakPolynomial P k (ξ:Base) - bracket (ξ:Base) (p:Base)^k‖ ≤
      gaussianConstant*Real.exp (-(D-Real.sqrt (2*R))^2/4) := by
  classical
  have hk0 : 0 < k := by omega
  have hs : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hk0)
  have hξp := peakPatch_radius hk0 hR hξ
  have hsub : P.erase p ⊆ P.filter (fun q => D-Real.sqrt (2*R) ≤ Real.sqrt k*projectiveDistance ξ q) := by
    intro q hq
    obtain ⟨hqp,hqP⟩ := Finset.mem_erase.mp hq
    refine Finset.mem_filter.mpr ⟨hqP,?_⟩
    have hh := (div_le_iff₀ hs).mp (hP p hp q hqP hqp.symm)
    have ht := projectiveDistance_triangle p ξ q
    rw [projectiveDistance_symm p ξ] at ht
    have hm := mul_le_mul_of_nonneg_left ht hs.le
    linarith
  have he : peakPolynomial P k (ξ:Base) - bracket (ξ:Base) (p:Base)^k =
      ∑ q ∈ P.erase p, bracket (ξ:Base) (q:Base)^k := by
    unfold peakPolynomial
    rw [← Finset.add_sum_erase _ _ hp]
    ring
  rw [he]
  apply (norm_sum_le _ _).trans
  simp only [norm_pow]
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)).trans
    (peak_gaussian hD hk hP ξ (sub_nonneg.mpr hDR))

lemma off_peakPatch_radius {k : ℕ} (hk : 0 < k) {R : ℝ} (hR : 0 < R)
    (hkR : 2*R ≤ k) {p ξ : Sphere} (hξ : ξ ∉ peakPatch k R p) :
    Real.sqrt R ≤ Real.sqrt (k:ℝ)*projectiveDistance ξ p := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hs : 0 ≤ 2*R/k := by positivity
  have hs1 : 2*R/k ≤ 1 := (div_le_one hk0).mpr hkR
  have he0 : 0 < Real.exp (2*R/k) := Real.exp_pos _
  have he1 := Real.add_one_le_exp (2*R/k)
  have hc0 : 0 ≤ ‖bracket (ξ:Base) (p:Base)‖ := norm_nonneg _
  have hcn : ‖bracket (ξ:Base) (p:Base)‖ ≤ Real.exp (-R/k) := le_of_not_gt hξ
  have he : Real.exp (-R/k)^2 = (Real.exp (2*R/k))⁻¹ := by
    rw [← Real.exp_nat_mul,← Real.exp_neg]; congr 1; ring
  have hsq : ‖bracket (ξ:Base) (p:Base)‖^2 ≤ (Real.exp (2*R/k))⁻¹ := by
    rw [← he]
    exact (sq_le_sq₀ hc0 (Real.exp_pos _).le).mpr hcn
  have hm : ‖bracket (ξ:Base) (p:Base)‖^2*Real.exp (2*R/k) ≤ 1 := by
    have ht := mul_le_mul_of_nonneg_right hsq he0.le
    simpa only [inv_mul_cancel₀ he0.ne',one_mul] using ht
  have hm1 : ‖bracket (ξ:Base) (p:Base)‖^2*(1+2*R/k) ≤ 1 := by
    have ht := mul_le_mul_of_nonneg_left he1 (sq_nonneg ‖bracket (ξ:Base) (p:Base)‖)
    linarith
  have hd := projectiveDistance_sq ξ p
  have hd0 := projectiveDistance_nonneg ξ p
  have hds : R/k ≤ projectiveDistance ξ p^2 := by
    have hh := mul_le_mul_of_nonneg_left hs1 (sq_nonneg (projectiveDistance ξ p))
    have hs2 : 2*R/(k:ℝ) = 2*(R/k) := by ring
    have hn : ‖bracket (ξ:Base) (p:Base)‖^2 = 1-projectiveDistance ξ p^2 := by linarith
    rw [hn,hs2] at hm1
    rw [hs2] at hh
    linarith
  have hh := (div_le_iff₀ hk0).mp hds
  have hkn := Real.sq_sqrt hk0.le
  have hrn := Real.sq_sqrt hR.le
  have heq : (Real.sqrt (k:ℝ)*projectiveDistance ξ p)^2 = (k:ℝ)*projectiveDistance ξ p^2 := by rw [mul_pow,hkn]
  have hprod : 0 ≤ Real.sqrt (k:ℝ)*projectiveDistance ξ p := mul_nonneg (Real.sqrt_nonneg _) hd0
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) hprod).mp (by linarith)

lemma peak_off_patch {k : ℕ} (hk : 1 ≤ k) {R D : ℝ} (hR : 0 < R)
    (hkR : 2*R ≤ k) (hD : 1 ≤ D) {P : Finset Sphere}
    (hP : ProjectivelySeparated (D/Real.sqrt k) P) (ξ : Sphere)
    (hξ : ∀ p ∈ P, ξ ∉ peakPatch k R p) :
    ‖peakPolynomial P k (ξ:Base)‖ ≤ gaussianConstant*Real.exp (-R/4) := by
  classical
  have hfilter : P.filter (fun p => Real.sqrt R ≤ Real.sqrt k*projectiveDistance ξ p) = P := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    exact off_peakPatch_radius (by omega) hR hkR (hξ p hp)
  have hh := peak_gaussian hD hk hP ξ (Real.sqrt_nonneg R)
  rw [hfilter,Real.sq_sqrt hR.le] at hh
  exact (norm_sum_le _ _).trans (by simpa only [norm_pow] using hh)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseCirclePowerLog
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
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma circle_pow_surjective {k : ℕ} (hk : 0 < k) : Function.Surjective (fun z : Circle => z^k) := by
  intro z
  obtain ⟨x,rfl⟩ := Circle.exp_surjective z
  refine ⟨Circle.exp (x/k),?_⟩
  dsimp only
  rw [← Circle.exp_nsmul,nsmul_eq_mul]
  congr 1
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

lemma circle_pow_measurePreserving {k : ℕ} (hk : 0 < k) :
    MeasurePreserving (fun z : Circle => z^k) circleMeasure circleMeasure :=
  (powMonoidHom (α := Circle) k).measurePreserving (continuous_pow k) (circle_pow_surjective hk) rfl

lemma circle_pow_integral {k : ℕ} (hk : 0 < k) {F : Circle → ℝ} (hF : Continuous F) :
    (∫ z : Circle, F (z^k) ∂circleMeasure)=∫ z : Circle, F z ∂circleMeasure := by
  have hp := circle_pow_measurePreserving hk
  calc
    _ = ∫ z : Circle, F z ∂Measure.map (fun z : Circle => z^k) circleMeasure :=
      (integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable).symm
    _ = _ := by rw [hp.map_eq]

lemma regularizedLog_rescale (a ε : ℝ) (v : ℂ) : regularizedLog a ε v=regularizedLog 1 ε ((a:ℂ)*v) := by
  simp only [regularizedLog,Complex.ofReal_one,one_mul]

lemma circle_regularized_mean {q ε : ℝ} (hq : 0 ≤ q) (hε : ε ≠ 0) :
    (∫ z : Circle, regularizedLog 1 ε ((q:ℂ)*(z:ℂ)) ∂circleMeasure)=
      Real.log (logFactor q ε)-Real.log (1+ε^2) := by
  simpa only [zero_mul,add_zero,mul_one,zero_div,sub_zero] using regularized_circle_moments hq hε 0

lemma circle_regularized_power_moments {q ε : ℝ} (hq : 0 ≤ q) (hε : ε ≠ 0)
    {k : ℕ} (hk : 0 < k) (f : ℝ) :
    (∫ z : Circle, regularizedLog 1 ε ((q:ℂ)*(z:ℂ)^k)*(1+f*((z:ℂ)^k).re) ∂circleMeasure)=
      Real.log (logFactor q ε)-Real.log (1+ε^2)-f*q/logFactor q ε := by
  have hc : Continuous (fun z : Circle => regularizedLog 1 ε ((q:ℂ)*(z:ℂ))*(1+f*(z:ℂ).re)) :=
    ((regularizedLog_contDiff 1 hε).continuous.comp (by fun_prop)).mul (by fun_prop)
  have he := circle_pow_integral hk hc
  simp only [Circle.coe_pow] at he
  rw [he,regularized_circle_moments hq hε]

lemma circle_regularized_complex_mean {ε : ℝ} (hε : ε ≠ 0) (v : ℂ) {k : ℕ} (hk : 0 < k) :
    (∫ z : Circle, regularizedLog 1 ε ((z:ℂ)^k*v) ∂circleMeasure)=
      Real.log (logFactor ‖v‖ ε)-Real.log (1+ε^2) := by
  by_cases hv : v=0
  · subst v
    simp only [mul_zero,regularizedLog_zero,integral_zero,norm_zero]
    have hh : logFactor 0 ε=1+ε^2 := by simpa using logFactor_equation 0 ε
    rw [hh,sub_self]
  have hn := norm_pos_iff.mpr hv
  let u : Circle := ⟨v/(‖v‖:ℂ),by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hn,div_self hn.ne']⟩
  have hu : (‖v‖:ℂ)*(u:ℂ)=v := by
    dsimp [u]
    have hnc : (‖v‖:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp [hnc]
  have hc : Continuous (fun z : Circle => regularizedLog 1 ε ((z:ℂ)*v)) :=
    (regularizedLog_contDiff 1 hε).continuous.comp (by fun_prop)
  have he := circle_pow_integral hk hc
  simp only [Circle.coe_pow] at he
  rw [he]
  have hm := integral_mul_right_eq_self (μ := circleMeasure)
    (fun z : Circle => regularizedLog 1 ε ((‖v‖:ℂ)*(z:ℂ))) u
  have heq : ∀ z : Circle, (‖v‖:ℂ)*((z*u:Circle):ℂ)=(z:ℂ)*v := by
    intro z
    rw [Circle.coe_mul,mul_left_comm,hu]
  simp_rw [heq] at hm
  rw [hm,circle_regularized_mean (norm_nonneg _) hε]

lemma logFactor_small_mean_bound {q ε : ℝ} (hq : q^2 ≤ 1/4) :
    Real.log (logFactor q ε)-Real.log (1+ε^2) ≤ 2*ε^2*q^2 := by
  let L := logFactor q ε
  have hL : 1 ≤ L := logFactor_one_le q ε
  have hp : 0 < L := logFactor_pos q ε
  have hA : 0 < 1+ε^2 := by positivity
  have he := logFactor_equation q ε
  change L+q^2/L=1+q^2+ε^2 at he
  have hle : q^2/L ≤ q^2 := div_le_self (sq_nonneg _) hL
  have hAL : 1+ε^2 ≤ L := by linarith
  have hpoly : (L-(1+ε^2))*(L-q^2)=q^2*ε^2 := by
    field_simp at he
    linarith
  have hdiff : L-(1+ε^2) ≤ 2*ε^2*q^2 := by
    linarith [mul_nonneg (sub_nonneg.mpr hAL) (show 0 ≤ L-q^2-1/2 by linarith)]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hp hA)
  rw [Real.log_div hp.ne' hA.ne'] at hlog
  apply hlog.trans
  have hm : L-(1+ε^2) ≤ (2*ε^2*q^2)*(1+ε^2) :=
    hdiff.trans (le_mul_of_one_le_right (by positivity) (by linarith [sq_nonneg ε]))
  rw [div_sub_one hA.ne']
  exact (div_le_iff₀ hA).mpr hm

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePatchPhase
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
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma phaseAction_patch (k : ℕ) (R : ℝ) (p ξ : Sphere) (z : Circle) :
    phaseAction z ξ ∈ peakPatch k R p ↔ ξ ∈ peakPatch k R p := by
  change (Real.exp (-R/k) < ‖bracket ((z:ℂ) • (ξ:Base)) (p:Base)‖) ↔ _
  rw [circle_bracket_norm]
  rfl

lemma sigma_phase_average_restrict {V : Sphere → ℝ} (hV : Continuous V)
    {s : Set Sphere} (hs : MeasurableSet s)
    (hinv : ∀ (z : Circle) (ξ : Sphere), phaseAction z ξ ∈ s ↔ ξ ∈ s) :
    (∫ ξ in s, V ξ ∂sigma)=∫ ξ in s, ∫ z : Circle, V (phaseAction z ξ) ∂circleMeasure ∂sigma := by
  classical
  have hc : Continuous (fun p : Circle × Sphere => V (phaseAction p.1 p.2)) := hV.comp phaseAction_continuous
  have hi := (compact_continuous_integrable (μ := circleMeasure.prod sigma) hc).indicator (hs.preimage measurable_snd)
  have he : (fun p : Circle × Sphere => (Prod.snd ⁻¹' s).indicator (fun p => V (phaseAction p.1 p.2)) p)=
      fun p : Circle × Sphere => (s.indicator V) (phaseAction p.1 p.2) := by
    funext p
    simp only [indicator_apply,mem_preimage,hinv]
  change Integrable (fun p : Circle × Sphere => (Prod.snd ⁻¹' s).indicator (fun p => V (phaseAction p.1 p.2)) p) (circleMeasure.prod sigma) at hi
  rw [he] at hi
  have hunit : ∀ z : Circle, (∫ ξ, (s.indicator V) (phaseAction z ξ) ∂sigma)=∫ ξ, (s.indicator V) ξ ∂sigma := by
    intro z
    exact sigma_integral_unitary (phaseIsometry z z.norm_coe) (s.indicator V)
  have havg : (∫ ξ, (s.indicator V) ξ ∂sigma)= ∫ ξ, ∫ z : Circle, (s.indicator V) (phaseAction z ξ) ∂circleMeasure ∂sigma := by
    rw [← integral_integral_swap hi]
    simp_rw [hunit]
    simp
  have heinner : ∀ ξ : Sphere, (∫ z : Circle, (s.indicator V) (phaseAction z ξ) ∂circleMeasure)=
      s.indicator (fun ξ => ∫ z : Circle, V (phaseAction z ξ) ∂circleMeasure) ξ := by
    intro ξ
    by_cases hξ : ξ ∈ s
    · simp only [indicator_of_mem hξ]
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => indicator_of_mem ((hinv z ξ).mpr hξ) V)
    · rw [indicator_of_notMem hξ]
      apply integral_eq_zero_of_ae
      exact Eventually.of_forall (fun z => indicator_of_notMem (fun h => hξ ((hinv z ξ).mp h)) V)
  simp_rw [heinner] at havg
  simpa only [integral_indicator hs] using havg

lemma circle_regularized_shifted_moments {q ε : ℝ} (hq : 0 ≤ q) (hε : ε ≠ 0)
    {k : ℕ} (hk : 0 < k) (f : ℝ) (w : Circle) :
    (∫ z : Circle, regularizedLog 1 ε ((q:ℂ)*((z*w:Circle):ℂ)^k)*
      (1+f*(((z*w:Circle):ℂ)^k).re) ∂circleMeasure)=
    Real.log (logFactor q ε)-Real.log (1+ε^2)-f*q/logFactor q ε := by
  rw [integral_mul_right_eq_self (μ := circleMeasure) (fun z : Circle =>
    regularizedLog 1 ε ((q:ℂ)*(z:ℂ)^k)*(1+f*((z:ℂ)^k).re)) w]
  exact circle_regularized_power_moments hq hε hk f

lemma densityCorrection_constant_phase {k : ℕ} {R : ℝ} {f b : ℝ → ℝ} {p ξ : Sphere}
    (hpatch : ξ ∈ peakPatch k R p) (w : Circle)
    (hw : bracket (ξ:Base) (p:Base)=(‖bracket (ξ:Base) (p:Base)‖:ℂ)*(w:ℂ)) (z : Circle) :
    densityCorrection k R f b (fun _ => 1) p (phaseAction z ξ)=
    (‖bracket (ξ:Base) (p:Base)‖^2)⁻¹*f (densityHeight k p ξ)*(((z*w:Circle):ℂ)^k).re := by
  have hn : 0 < ‖bracket (ξ:Base) (p:Base)‖ := peakPatch_norm_pos hpatch
  have hnC : (‖bracket (ξ:Base) (p:Base)‖:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hder : ∀ x : Base, phaseDerivative (fun _ : Base => (1:ℝ)) x=0 := by
    intro x
    simp only [phaseDerivative,(hasFDerivAt_const (1:ℝ) x).fderiv,zero_apply]
  change densityCorrection k R f b (fun _ => 1) p ((z:ℂ) • (ξ:Base))=_
  have hpatch' : Real.exp (-R/k) < ‖bracket (ξ:Base) (p:Base)‖ := hpatch
  rw [densityCorrection,circle_bracket_norm,ite_eq_left hpatch']
  dsimp only [densityCorrectionRaw]
  rw [circle_bracket_norm,densityHeight_phase,hder]
  have hphase : bracket ((z:ℂ) • (ξ:Base)) (p:Base)/(‖bracket (ξ:Base) (p:Base)‖:ℂ)=((z*w:Circle):ℂ) := by
    rw [bracket_smul,Circle.coe_mul]
    nth_rw 1 [hw]
    field_simp
  rw [hphase]
  simp only [mul_one,mul_zero,zero_mul,sub_zero,mul_assoc]

lemma ideal_patch_phase_mean {a ε ρ : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ ρ) (hε : ε ≠ 0)
    {k : ℕ} (hk : 0 < k) {R : ℝ} (f b : ℝ → ℝ) {p ξ : Sphere}
    (hpatch : ξ ∈ peakPatch k R p) :
    (∫ z : Circle, regularizedLog a ε ((ρ:ℂ)*bracket (phaseAction z ξ : Base) (p:Base)^k)*
      (1+densityCorrection k R f b (fun _ => 1) p (phaseAction z ξ)) ∂circleMeasure)=
    Real.log (logFactor (a*ρ*‖bracket (ξ:Base) (p:Base)‖^k) ε)-Real.log (1+ε^2)-
      (‖bracket (ξ:Base) (p:Base)‖^2)⁻¹*f (densityHeight k p ξ)*
      (a*ρ*‖bracket (ξ:Base) (p:Base)‖^k)/logFactor (a*ρ*‖bracket (ξ:Base) (p:Base)‖^k) ε := by
  obtain ⟨w,hw⟩ := exists_circle_norm_factor (bracket (ξ:Base) (p:Base))
  have hw' : bracket (ξ:Base) (p:Base)=(‖bracket (ξ:Base) (p:Base)‖:ℂ)*(w:ℂ) := by rw [mul_comm]; exact hw.symm
  have he : ∀ z : Circle, regularizedLog a ε ((ρ:ℂ)*bracket (phaseAction z ξ : Base) (p:Base)^k)=
      regularizedLog 1 ε ((a*ρ*‖bracket (ξ:Base) (p:Base)‖^k:ℝ)*((z*w:Circle):ℂ)^k) := by
    intro z
    rw [regularizedLog_rescale,phaseAction_coe,bracket_smul,Circle.coe_mul]
    nth_rw 1 [hw']
    congr 1
    push_cast
    simp only [mul_pow]
    ring
  simp_rw [he,densityCorrection_constant_phase hpatch w hw']
  exact circle_regularized_shifted_moments (by positivity) hε hk _ w

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseRadialPatch
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
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma bracketUnit_continuous (p : Sphere) : Continuous (bracketUnit p) :=
  radialUnit_continuous.comp (sphereAction _).continuous

lemma bracketUnit_coe (p ξ : Sphere) : (bracketUnit p ξ:ℝ)=‖bracket (ξ:Base) (p:Base)‖^2 :=
  adapted_radialU ξ p

lemma bracketUnit_preserves (p : Sphere) : MeasurePreserving (bracketUnit p) sigma volume :=
  (show MeasurePreserving radialUnit sigma volume from ⟨radialUnit_continuous.measurable,radial_law⟩).comp
    (sphereAction_preserves (adaptedIsometry p))

lemma peakPatch_iff_radial {k : ℕ} (hk : 0 < k) (R : ℝ) (p ξ : Sphere) :
    ξ ∈ peakPatch k R p ↔ Real.exp (-2*R/k) < (bracketUnit p ξ:ℝ) := by
  rw [bracketUnit_coe]
  have he : Real.exp (-2*R/k)=Real.exp (-R/k)^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp [show (k:ℝ) ≠ 0 by exact_mod_cast hk.ne']
    ring
  rw [he]
  exact (sq_lt_sq₀ (Real.exp_pos _).le (norm_nonneg _)).symm

lemma densityHeight_radial (k : ℕ) (p ξ : Sphere) :
    densityHeight k p ξ=-(k:ℝ)/2*Real.log (bracketUnit p ξ:ℝ) := by
  rw [bracketUnit_coe,Real.log_pow,densityHeight]
  ring

lemma radial_patch_integral {k : ℕ} (hk : 0 < k) {R : ℝ} (hR : 0 < R)
    (p : Sphere) {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ ξ in peakPatch k R p, g (densityHeight k p ξ) ∂sigma)=
      ∫ t in Real.exp (-2*R/k)..1, g (-(k:ℝ)/2*Real.log t) := by
  classical
  let a := Real.exp (-2*R/k)
  let G : ℝ → ℝ := fun t => g (-(k:ℝ)/2*Real.log t)
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have ha : 0 < a := Real.exp_pos _
  have ha1 : a ≤ 1 := Real.exp_le_one_iff.mpr (by exact div_nonpos_of_nonpos_of_nonneg (by linarith) hk0.le)
  have hG : AEStronglyMeasurable (fun t : unitInterval => (Ioi a).indicator G t) volume := by
    apply Measurable.aestronglyMeasurable
    exact ((hg.measurable.comp (measurable_const.mul Real.measurable_log)).indicator measurableSet_Ioi).comp measurable_subtype_coe
  have he : (fun ξ : Sphere => (peakPatch k R p).indicator (fun ξ => g (densityHeight k p ξ)) ξ) =
      fun ξ : Sphere => (Ioi a).indicator G (bracketUnit p ξ) := by
    funext ξ
    simp only [indicator_apply,peakPatch_iff_radial hk,mem_Ioi]
    split_ifs <;> simp only [G,densityHeight_radial]
  rw [← integral_indicator (peakPatch_open k R p).measurableSet,he]
  have hm := (bracketUnit_preserves p).map_eq
  calc
    _ = ∫ t : unitInterval, (Ioi a).indicator G t := by
      rw [← hm,integral_map (bracketUnit_continuous p).measurable.aemeasurable]
      rwa [hm]
    _ = ∫ t in Icc (0:ℝ) 1, (Ioi a).indicator G t := by
      rw [unitInterval.volume_def,integral_subtype_comap measurableSet_Icc]
    _ = ∫ t in Ioc a 1, G t := by
      rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
      have hs : Ioi a ∩ Icc (0:ℝ) 1 = Ioc a 1 := by
        ext t
        simp only [mem_inter_iff,mem_Ioi,mem_Icc,mem_Ioc]
        constructor
        · rintro ⟨ht,_,ht1⟩
          exact ⟨ht,ht1⟩
        · rintro ⟨ht,ht1⟩
          exact ⟨ht,ha.le.trans ht.le,ht1⟩
      rw [hs]
    _ = _ := (intervalIntegral.integral_of_le ha1).symm

lemma log_radial_substitution_real {k R : ℝ} (hk : 0 < k) (hR : 0 < R)
    {F : ℝ → ℝ} (hF : Continuous F) :
    (∫ t in Real.exp (-2*R/k)..1, t⁻¹*F (-k/2*Real.log t)) =
      2/k*(∫ y in 0..R, F y) := by
  have hh := log_radial_substitution hk hR (Complex.continuous_ofReal.comp hF)
  change (∫ t in Real.exp (-2*R/k)..1, (t⁻¹:ℝ) • (F (-k/2*Real.log t):ℂ)) = _ at hh
  simp only [Function.comp_apply,Complex.real_smul,← Complex.ofReal_mul] at hh
  rw [intervalIntegral.integral_ofReal,intervalIntegral.integral_ofReal,← Complex.ofReal_mul] at hh
  exact Complex.ofReal_injective hh

lemma radial_patch_integral_exp {k : ℕ} (hk : 0 < k) {R : ℝ} (hR : 0 < R)
    (p : Sphere) {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ ξ in peakPatch k R p, g (densityHeight k p ξ) ∂sigma)=
      2/(k:ℝ)*(∫ y in 0..R, Real.exp (-2*y/k)*g y) := by
  rw [radial_patch_integral hk hR p hg]
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hc : Continuous (fun y : ℝ => Real.exp (-2*y/k)*g y) := (by fun_prop : Continuous (fun y : ℝ => Real.exp (-2*y/k))).mul hg
  have hh := log_radial_substitution_real hk0 hR hc
  rw [← hh]
  apply intervalIntegral.integral_congr
  intro t ht
  have ha1 : Real.exp (-2*R/(k:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by exact div_nonpos_of_nonpos_of_nonneg (by linarith) hk0.le)
  rw [uIcc_of_le ha1] at ht
  have ht0 : 0 < t := (Real.exp_pos _).trans_le ht.1
  have he : -2*(-(k:ℝ)/2*Real.log t)/k=Real.log t := by field_simp
  dsimp only
  rw [he,Real.exp_log ht0,← mul_assoc,inv_mul_cancel₀ ht0.ne',one_mul]

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseModelSign
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
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma modelIntegrand_continuous {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) :
    Continuous (fun p : (ℝ × ℝ) × ℝ => modelIntegrand a p.1.1 p.1.2 f p.2) := by
  have hL : Continuous (fun p : (ℝ × ℝ) × ℝ => logFactor (a*p.1.2*Real.exp (-p.2)) p.1.1) :=
    logFactor_continuous.comp (show Continuous (fun p : (ℝ × ℝ) × ℝ => (a*p.1.2*Real.exp (-p.2),p.1.1)) from by fun_prop)
  have hD : Continuous (fun p : (ℝ × ℝ) × ℝ => Real.log (1+p.1.1^2)) := by
    apply Continuous.log
    · fun_prop
    · intro p
      positivity
  have hN : Continuous (fun p : (ℝ × ℝ) × ℝ => f p.2*(a*p.1.2*Real.exp (-p.2))) :=
    (hf.comp continuous_snd).mul (show Continuous (fun p : (ℝ × ℝ) × ℝ => a*p.1.2*Real.exp (-p.2)) from by fun_prop)
  exact ((hL.log (fun p => (logFactor_pos _ _).ne')).sub hD).sub
    (hN.div hL (fun p => (logFactor_pos _ _).ne'))

lemma modelIntegrand_continuous_y {f : ℝ → ℝ} (hf : Continuous f) (a ε ρ : ℝ) :
    Continuous (modelIntegrand a ε ρ f) := by
  have hc : Continuous (fun y : ℝ => ((ε,ρ),y)) := by fun_prop
  exact Continuous.comp (g := fun p : (ℝ × ℝ) × ℝ => modelIntegrand a p.1.1 p.1.2 f p.2)
    (f := fun y : ℝ => ((ε,ρ),y)) (modelIntegrand_continuous hf a) hc

lemma RadialProfiles.log_lt_cutoff {a : ℝ} (ha : 1 < a) (p : RadialProfiles a) : Real.log a < p.cutoff := by
  by_contra h
  have hp := p.plateau (Real.log a) ⟨(Real.log_pos ha).le,le_rfl⟩
  have ht := (p.tail (Real.log a) (le_of_not_gt h)).1
  linarith [p.s_pos]

lemma modelIntegrand_zero_low {a y : ℝ} (ha : 0 < a) (hy : y ≤ Real.log a) (f : ℝ → ℝ) :
    modelIntegrand a 0 1 f y = 2*(Real.log a-y)-f y*Real.exp (y-Real.log a) := by
  have hq : a*Real.exp (-y)=Real.exp (Real.log a-y) := by rw [Real.exp_sub,Real.exp_log ha,Real.exp_neg,div_eq_mul_inv]
  have hge : 1 ≤ a*Real.exp (-y) := by rw [hq]; exact Real.one_le_exp_iff.mpr (by linarith)
  have hsq : 1 ≤ (a*Real.exp (-y))^2 := by nlinarith
  unfold modelIntegrand
  simp only [mul_one,logFactor_zero,zero_pow (by norm_num : 2 ≠ 0),add_zero,Real.log_one,sub_zero,max_eq_right hsq]
  rw [hq,Real.log_pow,Real.log_exp]
  have he : Real.exp (y-Real.log a)=(Real.exp (Real.log a-y))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
  rw [he]
  field_simp
  ring

lemma modelIntegrand_zero_high {a y : ℝ} (ha : 0 < a) (hy : Real.log a ≤ y) (f : ℝ → ℝ) :
    modelIntegrand a 0 1 f y = -f y*(a*Real.exp (-y)) := by
  have hq : a*Real.exp (-y)=Real.exp (Real.log a-y) := by rw [Real.exp_sub,Real.exp_log ha,Real.exp_neg,div_eq_mul_inv]
  have hle : a*Real.exp (-y) ≤ 1 := by rw [hq]; exact Real.exp_le_one_iff.mpr (by linarith)
  have hpos : 0 ≤ a*Real.exp (-y) := by positivity
  have hsq : (a*Real.exp (-y))^2 ≤ 1 := by nlinarith
  unfold modelIntegrand
  simp only [mul_one,logFactor_zero,zero_pow (by norm_num : 2 ≠ 0),add_zero,Real.log_one,sub_zero,max_eq_left hsq,div_one,zero_sub,neg_mul]

lemma RadialProfiles.model_weight_zero {a : ℝ} (p : RadialProfiles a) :
    (∫ y in 0..p.R, p.f y*(a*Real.exp (-y)))=0 := by
  have hh := weight_profile_integral p.smooth_f.continuous p.smooth_b.continuous p.ode p.R_pos.le p.b_zero
    ((p.tail p.R p.cutoff_lt.le).2) 1
  simp only [sub_self,zero_mul,add_zero,neg_one_mul] at hh
  have he : (fun y => p.f y*(a*Real.exp (-y))) = fun y => a*(Real.exp (-y)*p.f y) := by ext y; ring
  rw [he,intervalIntegral.integral_const_mul,hh,mul_zero]

lemma model_small_integral {a : ℝ} (ha : 1 < a) (p : RadialProfiles a) :
    (∫ y in 0..Real.log a, modelIntegrand a 0 1 p.f y+p.f y*(a*Real.exp (-y))) =
      (Real.log a)^2-2*p.s*(Real.cosh (Real.log a)-1) := by
  let α := Real.log a
  have hα : 0 < α := Real.log_pos ha
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have he : ∀ y ∈ uIcc 0 α, modelIntegrand a 0 1 p.f y+p.f y*(a*Real.exp (-y)) =
      2*(α-y)+p.s*(Real.exp (y-α)-Real.exp (α-y)) := by
    intro y hy
    rw [uIcc_of_le hα.le] at hy
    rw [modelIntegrand_zero_low ha0 hy.2,p.plateau y hy]
    have hq : a*Real.exp (-y)=Real.exp (α-y) := by
      dsimp [α]
      rw [Real.exp_sub,Real.exp_log ha0,Real.exp_neg,div_eq_mul_inv]
    rw [hq]
    dsimp [α]
    ring
  rw [intervalIntegral.integral_congr he]
  have hd : ∀ y, HasDerivAt (fun y => 2*α*y-y^2+p.s*(Real.exp (y-α)+Real.exp (α-y)))
    (2*(α-y)+p.s*(Real.exp (y-α)-Real.exp (α-y))) y := by
    intro y
    convert! (((hasDerivAt_id y).const_mul (2*α)).sub ((hasDerivAt_id y).pow 2)).add
      ((((hasDerivAt_id y).sub_const α).exp).add (((hasDerivAt_const y α).sub (hasDerivAt_id y)).exp) |>.const_mul p.s) using 1; dsimp; ring
  have hc : Continuous (fun y : ℝ => 2*(α-y)+p.s*(Real.exp (y-α)-Real.exp (α-y))) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y) (hc.intervalIntegrable 0 α)]
  simp only [sub_self,Real.exp_zero,mul_zero,pow_two,sub_zero,zero_sub]
  rw [Real.cosh_eq]
  dsimp [α]
  ring

lemma model_large_integral {a : ℝ} (ha : 1 < a) (p : RadialProfiles a) :
    (∫ y in Real.log a..p.R, modelIntegrand a 0 1 p.f y+p.f y*(a*Real.exp (-y)))=0 := by
  have hαR : Real.log a < p.R := (p.log_lt_cutoff ha).trans p.cutoff_lt
  calc
    _ = ∫ y in Real.log a..p.R, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [uIcc_of_le hαR.le] at hy
      dsimp only
      rw [modelIntegrand_zero_high (lt_trans zero_lt_one ha) hy.1]
      ring
    _ = 0 := by simp

lemma modelMean_zero {a : ℝ} (ha : 1 < a) (p : RadialProfiles a) :
    modelMean a 0 1 p.R p.f = (Real.log a)^2-2*p.s*(Real.cosh (Real.log a)-1) := by
  let M := modelIntegrand a 0 1 p.f
  let F : ℝ → ℝ := fun y => p.f y*(a*Real.exp (-y))
  have hM : Continuous M := modelIntegrand_continuous_y p.smooth_f.continuous a 0 1
  have hF : Continuous F := by
    apply Continuous.mul p.smooth_f.continuous
    fun_prop
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hM.add hF).intervalIntegrable 0 (Real.log a)) ((hM.add hF).intervalIntegrable (Real.log a) p.R)
  change (∫ y in 0..Real.log a, M y+F y)+(∫ y in Real.log a..p.R, M y+F y)=(∫ y in 0..p.R, M y+F y) at hadd
  rw [model_small_integral ha p,model_large_integral ha p,add_zero,
    intervalIntegral.integral_add (hM.intervalIntegrable 0 p.R) (hF.intervalIntegrable 0 p.R),
    p.model_weight_zero,add_zero] at hadd
  exact hadd.symm

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseModelParameters
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
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma modelMean_continuous {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    Continuous (fun p : ℝ × ℝ => modelMean a p.1 p.2 R f) := by
  have hc : Continuous (fun p : ℝ × ℝ => ∫ y in Icc (0:ℝ) R, modelIntegrand a p.1 p.2 f y) :=
    continuous_parametric_integral_of_continuous (modelIntegrand_continuous hf a) isCompact_Icc
  have he : (fun p : ℝ × ℝ => modelMean a p.1 p.2 R f) =
    fun p : ℝ × ℝ => ∫ y in Icc (0:ℝ) R, modelIntegrand a p.1 p.2 f y := by
    funext p
    rw [modelMean,intervalIntegral.integral_of_le hR,integral_Icc_eq_integral_Ioc]
  rwa [he]

lemma modelGap_pos {a : ℝ} (p : RadialProfiles a) : 0 < modelGap a p := by
  unfold modelGap
  linarith [p.negativity]

lemma model_regularization_parameters {a : ℝ} (ha : 1 < a) (p : RadialProfiles a)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ ε η : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < η ∧ η < 1/2 ∧
      κ*ε^2 ≤ modelGap a p/8 ∧ ∀ ρ ∈ Icc (1-η) 1,
      modelMean a ε ρ p.R p.f ≤ -(3/4)*modelGap a p := by
  let Δ := modelGap a p
  have hΔ : 0 < Δ := modelGap_pos p
  have hzero : modelMean a 0 1 p.R p.f < -(3/4)*Δ := by
    rw [modelMean_zero ha p]
    dsimp [Δ,modelGap] at *
    linarith [p.negativity]
  have hc := (modelMean_continuous p.smooth_f.continuous a p.R_pos.le).continuousAt (x := ((0,1):ℝ × ℝ))
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp (hc.eventually_lt_const hzero)
  let ε := min (δ/4) (min (1/2) (Real.sqrt (Δ/(8*κ))))
  let η := min (δ/4) (1/4)
  have he : 0 < ε := by dsimp [ε]; positivity
  have heta : 0 < η := by dsimp [η]; positivity
  have hed : ε ≤ δ/4 := min_le_left _ _
  have he1 : ε ≤ 1/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hes : ε ≤ Real.sqrt (Δ/(8*κ)) := (min_le_right _ _).trans (min_le_right _ _)
  have hetad : η ≤ δ/4 := min_le_left _ _
  have heta1 : η ≤ 1/4 := min_le_right _ _
  refine ⟨ε,η,he,by linarith,heta,by linarith,?_,?_⟩
  · have hsq := sq_le_sq₀ he.le (Real.sqrt_nonneg _) |>.mpr hes
    rw [Real.sq_sqrt (by positivity : 0 ≤ Δ/(8*κ))] at hsq
    have hm := (le_div_iff₀ (by positivity : 0 < 8*κ)).mp hsq
    change κ*ε^2 ≤ Δ/8
    linarith
  · intro ρ hρ
    have hdist : dist ((ε,ρ):ℝ × ℝ) (0,1) < δ := by
      rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,sub_zero,abs_of_pos he,
        abs_of_nonpos (by linarith [hρ.2] : ρ-1 ≤ 0)]
      apply max_lt
      · linarith
      · linarith [hρ.1]

    exact le_of_lt (hd (y := (ε,ρ)) hdist)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePatchModel
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
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma densityHeight_power (k : ℕ) (p : Sphere) {ξ : Base} (hξ : 0 < ‖bracket ξ (p:Base)‖) :
    ‖bracket ξ (p:Base)‖^k = Real.exp (-densityHeight k p ξ) := by
  rw [densityHeight,neg_mul,neg_neg,Real.exp_nat_mul,Real.exp_log hξ]

lemma densityHeight_inv_sq {k : ℕ} (hk : 0 < k) (p : Sphere) {ξ : Base}
    (hξ : 0 < ‖bracket ξ (p:Base)‖) :
    (‖bracket ξ (p:Base)‖^2)⁻¹ = Real.exp (2*densityHeight k p ξ/k) := by
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have he : 2*densityHeight k p ξ/(k:ℝ) = -2*Real.log ‖bracket ξ (p:Base)‖ := by
    unfold densityHeight
    field_simp
  rw [he,show -2*Real.log ‖bracket ξ (p:Base)‖ = -(2*Real.log ‖bracket ξ (p:Base)‖) by ring,
    Real.exp_neg,show (2:ℝ) = (2:ℕ) by norm_num,Real.exp_nat_mul,Real.exp_log hξ]

lemma radialMean_continuous (a ε ρ : ℝ) :
    Continuous (fun y : ℝ => Real.log (logFactor (a*ρ*Real.exp (-y)) ε)-Real.log (1+ε^2)) := by
  have hc : Continuous (fun y : ℝ => logFactor (a*ρ*Real.exp (-y)) ε) :=
    logFactor_continuous.comp (show Continuous (fun y : ℝ => (a*ρ*Real.exp (-y),ε)) from by fun_prop)
  exact (hc.log (fun y => (logFactor_pos _ _).ne')).sub continuous_const

lemma radialPatchModel_continuous (a ε ρ : ℝ) (k : ℕ) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (radialPatchModel a ε ρ k f) := by
  have hr := radialMean_continuous a ε ρ
  have hq : Continuous (fun y : ℝ => a*ρ*Real.exp (-y)) := by fun_prop
  have hL : Continuous (fun y : ℝ => logFactor (a*ρ*Real.exp (-y)) ε) := logFactor_continuous.comp (hq.prodMk (continuous_const (y := ε)))
  exact ((show Continuous (fun y : ℝ => Real.exp (-2*y/k)) from by fun_prop).mul hr).sub
    ((hf.mul hq).div hL (fun y => (logFactor_pos _ _).ne'))

lemma ideal_patch_integral {a ε ρ : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ ρ) (hε : ε ≠ 0)
    (pr : RadialProfiles a) {k : ℕ} (hk : 0 < k) (p : Sphere) :
    (∫ ξ in peakPatch k pr.R p, regularizedLog a ε ((ρ:ℂ)*bracket (ξ:Base) (p:Base)^k)*
      (1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) ∂sigma)=
      2/(k:ℝ)*(∫ y in 0..pr.R, radialPatchModel a ε ρ k pr.f y) := by
  let V : Sphere → ℝ := fun ξ => regularizedLog a ε ((ρ:ℂ)*bracket (ξ:Base) (p:Base)^k)*
    (1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ)
  have hC := densityCorrection_smooth hk pr.cutoff_lt pr.smooth_f pr.smooth_b
    (show ContDiff ℝ ∞ (fun _ : Base => (1:ℝ)) from contDiff_const) pr.tail p
  have hV : Continuous V := ((regularizedLog_contDiff a hε).continuous.comp
    (continuous_const.mul (((bracket_analytic (p:Base)).continuous.comp continuous_subtype_val).pow k))).mul
      (continuous_const.add (hC.continuous.comp continuous_subtype_val))
  let H : ℝ → ℝ := fun y => Real.log (logFactor (a*ρ*Real.exp (-y)) ε)-Real.log (1+ε^2)-
    Real.exp (2*y/k)*pr.f y*(a*ρ*Real.exp (-y))/logFactor (a*ρ*Real.exp (-y)) ε
  have hq : Continuous (fun y : ℝ => a*ρ*Real.exp (-y)) := by fun_prop
  have hL : Continuous (fun y : ℝ => logFactor (a*ρ*Real.exp (-y)) ε) := logFactor_continuous.comp (hq.prodMk (continuous_const (y := ε)))
  have hH : Continuous H := (radialMean_continuous a ε ρ).sub
    ((((show Continuous (fun y : ℝ => Real.exp (2*y/k)) from by fun_prop).mul pr.smooth_f.continuous).mul hq).div hL
      (fun y => (logFactor_pos _ _).ne'))
  change (∫ ξ in peakPatch k pr.R p, V ξ ∂sigma)=_
  rw [sigma_phase_average_restrict hV (peakPatch_open k pr.R p).measurableSet
    (fun z ξ => phaseAction_patch k pr.R p ξ z)]
  calc
    _ = ∫ ξ in peakPatch k pr.R p, H (densityHeight k p ξ) ∂sigma := by
      apply setIntegral_congr_fun (peakPatch_open k pr.R p).measurableSet
      intro ξ hξ
      change (∫ z : Circle, regularizedLog a ε ((ρ:ℂ)*bracket (phaseAction z ξ : Base) (p:Base)^k)*
        (1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p (phaseAction z ξ)) ∂circleMeasure)=_
      rw [ideal_patch_phase_mean ha hr hε hk pr.f pr.b hξ,
        densityHeight_power k p (peakPatch_norm_pos hξ),densityHeight_inv_sq hk p (peakPatch_norm_pos hξ)]
    _ = 2/(k:ℝ)*(∫ y in 0..pr.R, Real.exp (-2*y/k)*H y) := radial_patch_integral_exp hk pr.R_pos p hH
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro y hy
      dsimp only [H,radialPatchModel]
      have he : Real.exp (-2*y/k)*Real.exp (2*y/k)=1 := by
        rw [← Real.exp_add, show -2*y/(k:ℝ)+2*y/k=0 by ring, Real.exp_zero]
      calc
        _ = Real.exp (-2*y/k)*(Real.log (logFactor (a*ρ*Real.exp (-y)) ε)-Real.log (1+ε^2))-
          (Real.exp (-2*y/k)*Real.exp (2*y/k))*(pr.f y*(a*ρ*Real.exp (-y))/logFactor (a*ρ*Real.exp (-y)) ε) := by ring
        _ = _ := by rw [he,one_mul]

lemma peakPatch_measure_real {k : ℕ} (hk : 0 < k) {R : ℝ} (hR : 0 < R) (p : Sphere) :
    sigma.real (peakPatch k R p)=1-Real.exp (-2*R/k) := by
  have hh := radial_patch_integral hk hR p (continuous_const (y := (1:ℝ)))
  simpa using hh

lemma peakPatch_measure_le {k : ℕ} (hk : 0 < k) {R : ℝ} (hR : 0 < R) (p : Sphere) :
    sigma.real (peakPatch k R p) ≤ 2*R/k := by
  rw [peakPatch_measure_real hk hR]
  have hh := Real.one_sub_le_exp_neg (2*R/(k:ℝ))
  rw [← neg_div,← neg_mul] at hh
  linarith

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseLogBounds
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
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma regularizedLog_uniform_bounds (a : ℝ) {ε : ℝ} (hε : ε ≠ 0) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ v : ℂ, ‖v‖ ≤ A → |regularizedLog a ε v| ≤ C) ∧
      ∀ v w : ℂ, ‖v‖ ≤ A → ‖w‖ ≤ A →
        |regularizedLog a ε v-regularizedLog a ε w| ≤ C*‖v-w‖ := by
  have hs := regularizedLog_contDiff a hε
  have hc : Continuous (fderiv ℝ (regularizedLog a ε)) := hs.continuous_fderiv (by norm_num)
  obtain ⟨L,hL⟩ := (isCompact_closedBall (0:ℂ) A).bddAbove_image hc.norm.continuousOn
  let B := max L 0
  have hB : 0 ≤ B := le_max_right _ _
  have hb : ∀ x ∈ Metric.closedBall (0:ℂ) A, ‖fderiv ℝ (regularizedLog a ε) x‖ ≤ B := by
    intro x hx
    exact (hL (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  have hlip : ∀ v w : ℂ, ‖v‖ ≤ A → ‖w‖ ≤ A → |regularizedLog a ε v-regularizedLog a ε w| ≤ B*‖v-w‖ := by
    intro v w hv hw
    have hm := (convex_closedBall (0:ℂ) A).norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => hs.differentiable (by norm_num) x) hb
      (show w ∈ Metric.closedBall 0 A by simpa using hw)
      (show v ∈ Metric.closedBall 0 A by simpa using hv)
    simpa only [Real.norm_eq_abs] using hm
  refine ⟨B*(1+A),by positivity,?_,?_⟩
  · intro v hv
    have hh := hlip v 0 hv (by simpa using hA)
    simp only [regularizedLog_zero,sub_zero] at hh
    exact hh.trans (by gcongr; linarith)
  · intro v w hv hw
    exact (hlip v w hv hw).trans (by gcongr; nlinarith)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePatchComparison
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
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma densityCorrection_one_bound {a : ℝ} (pr : RadialProfiles a) {k : ℕ}
    (hk : 0 < k) (hkR : 2*pr.R ≤ k) {p ξ : Sphere} (hξ : ξ ∈ peakPatch k pr.R p) :
    |densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ| ≤ Real.exp 1 := by
  have hn := peakPatch_norm_pos hξ
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hy : 0 ≤ densityHeight k p ξ := patchHeight_nonneg k p ξ
  have hyR : densityHeight k p ξ < pr.R := ((peakPatch_iff_height hk pr.R p ξ).mp hξ).2
  obtain ⟨w,hw⟩ := exists_circle_norm_factor (bracket (ξ:Base) (p:Base))
  have hw' : bracket (ξ:Base) (p:Base)=(‖bracket (ξ:Base) (p:Base)‖:ℂ)*(w:ℂ) := by rw [mul_comm]; exact hw.symm
  have he := densityCorrection_constant_phase (f := pr.f) (b := pr.b) hξ w hw' (1:Circle)
  simp only [phaseAction_coe, Circle.coe_one, one_smul, one_mul] at he
  rw [he,densityHeight_inv_sq hk p hn,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
  have hwre : |((w:ℂ)^k).re| ≤ 1 := by
    exact (Complex.abs_re_le_norm _).trans_eq (by simp [w.norm_coe])
  have hex : Real.exp (2*densityHeight k p ξ/k) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    apply (div_le_one hk0).mpr
    linarith
  calc
    _ ≤ Real.exp 1 * 1 * 1 := mul_le_mul (mul_le_mul hex (le_trans (pr.small _ hy) pr.F_lt.le) (abs_nonneg _) (Real.exp_pos _).le) hwre (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma peak_log_difference_bound {a ε ρ C D : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hC : 0 ≤ C)
    (hlip : ∀ v w : ℂ, ‖v‖ ≤ max gaussianConstant 1 → ‖w‖ ≤ max gaussianConstant 1 →
      |regularizedLog a ε v-regularizedLog a ε w| ≤ C*‖v-w‖)
    {k : ℕ} (hk : 0 < k) (pr : RadialProfiles a) (hD : 1 ≤ D) (hDR : Real.sqrt (2*pr.R) ≤ D)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P)
    {p ξ : Sphere} (hp : p ∈ P) (hξ : ξ ∈ peakPatch k pr.R p) :
    |regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ)-regularizedLog a ε ((ρ:ℂ)*bracket (ξ:Base) (p:Base)^k)| ≤
      C*gaussianConstant*Real.exp (-(D-Real.sqrt (2*pr.R))^2/4) := by
  have hnρ : ‖(ρ:ℂ)‖ = ρ := by simp [abs_of_nonneg hρ]
  have hg0 : 0 ≤ gaussianConstant := gaussianConstant_pos.le
  have hp1 : ‖peakPolynomial P k (ξ:Base)‖ ≤ gaussianConstant := peak_sphere_bound hD (by omega) hP ξ
  have hs1 : ‖bracket (ξ:Base) (p:Base)^k‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (bracket_norm_le_one ξ p)
  have harg : ‖(ρ:ℂ)*peakPolynomial P k ξ‖ ≤ max gaussianConstant 1 := by
    rw [norm_mul,hnρ]
    exact (mul_le_mul hρ1 hp1 (norm_nonneg _) (by norm_num)).trans (by simp)
  have harg' : ‖(ρ:ℂ)*bracket (ξ:Base) (p:Base)^k‖ ≤ max gaussianConstant 1 := by
    rw [norm_mul,hnρ]
    exact (mul_le_mul hρ1 hs1 (norm_nonneg _) (by norm_num)).trans (by simp)
  have herr := peakPatch_single (by omega : 1 ≤ k) pr.R_pos hD hDR hP hp hξ
  apply (hlip _ _ harg harg').trans
  rw [← mul_sub,norm_mul,hnρ]
  calc
    _ ≤ C*(1*(gaussianConstant*Real.exp (-(D-Real.sqrt (2*pr.R))^2/4))) := by gcongr
    _ = _ := by ring

lemma weighted_patch_error {a ε ρ C D : ℝ} (hε : ε ≠ 0) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hC : 0 ≤ C)
    (hlip : ∀ v w : ℂ, ‖v‖ ≤ max gaussianConstant 1 → ‖w‖ ≤ max gaussianConstant 1 →
      |regularizedLog a ε v-regularizedLog a ε w| ≤ C*‖v-w‖)
    {k : ℕ} (hk : 0 < k) (pr : RadialProfiles a) (hkR : 2*pr.R ≤ k)
    (hD : 1 ≤ D) (hDR : Real.sqrt (2*pr.R) ≤ D)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P) {p : Sphere} (hp : p ∈ P) :
    |(∫ ξ in peakPatch k pr.R p, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ)*
      (1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) ∂sigma)-
     (∫ ξ in peakPatch k pr.R p, regularizedLog a ε ((ρ:ℂ)*bracket (ξ:Base) (p:Base)^k)*
      (1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) ∂sigma)| ≤
      (2*pr.R/k)*(C*gaussianConstant*Real.exp (-(D-Real.sqrt (2*pr.R))^2/4))*(1+Real.exp 1) := by
  have hg0 : 0 ≤ gaussianConstant := gaussianConstant_pos.le
  have hco : Continuous (fun ξ : Sphere => densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) := (densityCorrection_smooth hk pr.cutoff_lt pr.smooth_f pr.smooth_b
    (show ContDiff ℝ ∞ (fun _ : Base => (1:ℝ)) from contDiff_const) pr.tail p).continuous.comp continuous_subtype_val
  have hu := (regularizedLog_contDiff a hε).continuous
  have h1 : Continuous (fun ξ : Sphere => regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ)*
      (1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ)) :=
    (hu.comp (continuous_const.mul ((peakPolynomial_analytic P k).continuous.comp continuous_subtype_val))).mul (continuous_const.add hco)
  have h2 : Continuous (fun ξ : Sphere => regularizedLog a ε ((ρ:ℂ)*bracket (ξ:Base) (p:Base)^k)*
      (1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ)) :=
    (hu.comp (continuous_const.mul (((bracket_analytic (p:Base)).continuous.comp continuous_subtype_val).pow k))).mul (continuous_const.add hco)
  rw [← integral_sub (compact_continuous_integrable h1) (compact_continuous_integrable h2)]
  have hh : |(∫ ξ in peakPatch k pr.R p,
      regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ)*(1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ)-
      regularizedLog a ε ((ρ:ℂ)*bracket (ξ:Base) (p:Base)^k)*(1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) ∂sigma)| ≤
      sigma.real (peakPatch k pr.R p)*((C*gaussianConstant*Real.exp (-(D-Real.sqrt (2*pr.R))^2/4))*(1+Real.exp 1)) := by
    rw [mul_comm (sigma.real _), ← Real.norm_eq_abs]
    apply norm_setIntegral_le_of_norm_le_const (measure_lt_top sigma (peakPatch k pr.R p))
    intro ξ hξ
    rw [Real.norm_eq_abs,← sub_mul,abs_mul]
    apply mul_le_mul (peak_log_difference_bound hρ hρ1 hC hlip hk pr hD hDR hP hp hξ)
    · exact (abs_add_le _ _).trans (by simpa using add_le_add_left (densityCorrection_one_bound pr hk hkR hξ) 1)
    · positivity
    · positivity
  apply hh.trans
  have hm := peakPatch_measure_le hk pr.R_pos p
  calc
    _ ≤ (2*pr.R/k)*((C*gaussianConstant*Real.exp (-(D-Real.sqrt (2*pr.R))^2/4))*(1+Real.exp 1)) := by gcongr
    _ = _ := by ring

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseRadialModelError
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
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma radial_log_bound (a ε : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ρ ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) R,
      |Real.log (logFactor (a*ρ*Real.exp (-y)) ε)-Real.log (1+ε^2)| ≤ M := by
  have hq : Continuous (fun p : ℝ × ℝ => a*p.1*Real.exp (-p.2)) := by fun_prop
  have hL := logFactor_continuous.comp (hq.prodMk (continuous_const (y := ε)))
  have hc := (hL.log (fun p => (logFactor_pos _ _).ne')).sub (continuous_const (y := Real.log (1+ε^2)))
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hc.continuousOn (s := Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) R))
  refine ⟨M,(norm_nonneg _).trans (hM (0,0) ⟨⟨le_rfl,zero_le_one⟩,⟨le_rfl,hR⟩⟩),?_⟩
  intro ρ hρ y hy
  exact hM (ρ,y) ⟨hρ,hy⟩

lemma exp_radial_weight_error {k : ℕ} (hk : 0 < k) {R y : ℝ} (hy : 0 ≤ y) (hyR : y ≤ R) :
    |Real.exp (-2*y/k)-1| ≤ 2*R/k := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have ht : 0 ≤ 2*y/(k:ℝ) := by positivity
  have he1 : Real.exp (-2*y/k) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) hk0.le)
  rw [abs_of_nonpos (sub_nonpos.mpr he1)]
  have he := Real.one_sub_le_exp_neg (2*y/(k:ℝ))
  have hrep : -(2*y/(k:ℝ)) = -2*y/k := by ring
  rw [hrep] at he
  have hm : 2*y/(k:ℝ) ≤ 2*R/k := by gcongr
  linarith

lemma radial_patch_model_error {a ε ρ M : ℝ} (hM : 0 ≤ M)
    (pr : RadialProfiles a) {k : ℕ} (hk : 0 < k)
    (hb : ∀ y ∈ Icc 0 pr.R, |Real.log (logFactor (a*ρ*Real.exp (-y)) ε)-Real.log (1+ε^2)| ≤ M) :
    |(∫ y in 0..pr.R, radialPatchModel a ε ρ k pr.f y)-modelMean a ε ρ pr.R pr.f| ≤ 2*pr.R^2*M/k := by
  have hR : 0 ≤ pr.R := pr.R_pos.le
  rw [modelMean,← intervalIntegral.integral_sub
    ((radialPatchModel_continuous a ε ρ k pr.smooth_f.continuous).intervalIntegrable 0 pr.R)
    ((modelIntegrand_continuous_y pr.smooth_f.continuous a ε ρ).intervalIntegrable 0 pr.R)]
  have he : ∀ y, radialPatchModel a ε ρ k pr.f y-modelIntegrand a ε ρ pr.f y=
      (Real.exp (-2*y/k)-1)*(Real.log (logFactor (a*ρ*Real.exp (-y)) ε)-Real.log (1+ε^2)) := by
    intro y; unfold radialPatchModel modelIntegrand; ring
  simp_rw [he]
  have hh : ‖∫ y in (0:ℝ)..pr.R, (Real.exp (-2*y/k)-1)*
      (Real.log (logFactor (a*ρ*Real.exp (-y)) ε)-Real.log (1+ε^2))‖ ≤
      ((2*pr.R/k)*M)*|pr.R-0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    have hy' : y ∈ Icc 0 pr.R := by
      rw [uIoc_of_le pr.R_pos.le] at hy
      exact ⟨hy.1.le,hy.2⟩
    rw [Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul_of_nonneg_left (hb y hy') (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (exp_radial_weight_error hk hy'.1 hy'.2) hM)
  rw [Real.norm_eq_abs,sub_zero,abs_of_pos pr.R_pos] at hh
  exact hh.trans_eq (by ring)

lemma ideal_patch_upper {a ε ρ M : ℝ} (ha : 0 ≤ a) (hε : ε ≠ 0) (hρ : 0 ≤ ρ)
    (hM : 0 ≤ M) (pr : RadialProfiles a) {k : ℕ} (hk : 0 < k) (p : Sphere)
    (hb : ∀ y ∈ Icc 0 pr.R, |Real.log (logFactor (a*ρ*Real.exp (-y)) ε)-Real.log (1+ε^2)| ≤ M) :
    (∫ ξ in peakPatch k pr.R p, regularizedLog a ε ((ρ:ℂ)*bracket (ξ:Base) (p:Base)^k)*
      (1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) ∂sigma) ≤
      2/(k:ℝ)*(modelMean a ε ρ pr.R pr.f+2*pr.R^2*M/k) := by
  rw [ideal_patch_integral ha hρ hε pr hk p]
  gcongr
  have hh := (abs_le.mp (radial_patch_model_error hM pr hk hb)).2
  linarith

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePatchDecomposition
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
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma peakPatchUnion_open (P : Finset Sphere) (k : ℕ) (R : ℝ) : IsOpen (peakPatchUnion P k R) :=
  isOpen_iUnion (fun p => isOpen_iUnion (fun _ => peakPatch_open k R p))

lemma peakPatchUnion_phase (P : Finset Sphere) (k : ℕ) (R : ℝ) (z : Circle) (ξ : Sphere) :
    phaseAction z ξ ∈ peakPatchUnion P k R ↔ ξ ∈ peakPatchUnion P k R := by
  simp only [peakPatchUnion,mem_iUnion,phaseAction_patch]

lemma densityCorrection_off {k : ℕ} {R : ℝ} {f b : ℝ → ℝ} {W : Base → ℝ} {p ξ : Sphere}
    (hξ : ξ ∉ peakPatch k R p) : densityCorrection k R f b W p ξ=0 := by
  exact ite_eq_right hξ

lemma patch_decomposition {a : ℝ} (pr : RadialProfiles a) {k : ℕ} (hk : 0 < k)
    (P : Finset Sphere) (hdis : (P : Set Sphere).PairwiseDisjoint (peakPatch k pr.R))
    {V : Sphere → ℝ} (hV : Continuous V) :
    (∫ ξ : Sphere, V ξ ∂sigma)+∑ p ∈ P, ∫ ξ : Sphere,
      V ξ*densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ ∂sigma =
    (∫ ξ in (peakPatchUnion P k pr.R)ᶜ, V ξ ∂sigma)+
      ∑ p ∈ P, ∫ ξ in peakPatch k pr.R p,
        V ξ*(1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) ∂sigma := by
  have hU := (peakPatchUnion_open P k pr.R).measurableSet
  have hsplit := integral_add_compl hU (compact_continuous_integrable hV (μ := sigma))
  have hu : (∫ ξ in peakPatchUnion P k pr.R, V ξ ∂sigma)=
      ∑ p ∈ P, ∫ ξ in peakPatch k pr.R p, V ξ ∂sigma := by
    exact integral_biUnion_finset P (fun p _ => (peakPatch_open k pr.R p).measurableSet)
      hdis (fun p _ => compact_continuous_integrable hV)
  have hc : ∀ p : Sphere, Continuous (fun ξ : Sphere => V ξ*densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) := by
    intro p
    exact hV.mul ((densityCorrection_smooth hk pr.cutoff_lt pr.smooth_f pr.smooth_b
      (contDiff_const (c := (1:ℝ))) pr.tail p).continuous.comp continuous_subtype_val)
  have hp : ∀ p : Sphere, (∫ ξ : Sphere, V ξ*densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ ∂sigma)=
      ∫ ξ in peakPatch k pr.R p, V ξ*densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ ∂sigma := by
    intro p
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro ξ hξ
    rw [densityCorrection_off hξ,mul_zero]
  have hsum : ∀ p : Sphere, (∫ ξ in peakPatch k pr.R p, V ξ ∂sigma)+
      (∫ ξ in peakPatch k pr.R p, V ξ*densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ ∂sigma)=
      ∫ ξ in peakPatch k pr.R p, V ξ*(1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) ∂sigma := by
    intro p
    rw [← integral_add (compact_continuous_integrable hV) (compact_continuous_integrable (hc p))]
    congr 1
    ext ξ
    ring
  rw [← hsplit,hu]
  simp_rw [hp]
  rw [add_right_comm,← Finset.sum_add_distrib]
  simp_rw [hsum]
  ring

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseOffPatchMean
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
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma regularized_peak_phase_mean {a ε ρ : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ ρ) (hε : ε ≠ 0)
    (P : Finset Sphere) {k : ℕ} (hk : 0 < k) (ξ : Sphere) :
    (∫ z : Circle, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k (phaseAction z ξ)) ∂circleMeasure)=
      Real.log (logFactor (a*ρ*‖peakPolynomial P k ξ‖) ε)-Real.log (1+ε^2) := by
  have he : ∀ z : Circle, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k (phaseAction z ξ))=
      regularizedLog 1 ε ((z:ℂ)^k*((a:ℂ)*(ρ:ℂ)*peakPolynomial P k ξ)) := by
    intro z
    rw [regularizedLog_rescale,phaseAction_coe,peakPolynomial_homogeneous]
    congr 1
    ring
  simp_rw [he]
  rw [circle_regularized_complex_mean hε _ hk]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hr]

lemma regularized_peak_phase_mean_bound {a ε ρ : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ ρ) (hr1 : ρ ≤ 1)
    (hε : ε ≠ 0) (P : Finset Sphere) {k : ℕ} (hk : 0 < k) (ξ : Sphere)
    (hsmall : a*‖peakPolynomial P k ξ‖ ≤ 1/2) :
    (∫ z : Circle, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k (phaseAction z ξ)) ∂circleMeasure) ≤
      a*ε^2*‖peakPolynomial P k ξ‖ := by
  rw [regularized_peak_phase_mean ha hr hε P hk ξ]
  let n := ‖peakPolynomial P k ξ‖
  let q := a*ρ*n
  have hn : 0 ≤ n := norm_nonneg _
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqn : q ≤ a*n := by dsimp [q]; nlinarith [mul_nonneg ha hn]
  have hq1 : q ≤ 1/2 := hqn.trans hsmall
  have hsq : q^2 ≤ 1/4 := by nlinarith
  have hh := logFactor_small_mean_bound (ε := ε) hsq
  change Real.log (logFactor q ε)-Real.log (1+ε^2) ≤ a*ε^2*n
  apply hh.trans
  have hq2 : 2*q^2 ≤ a*n := by nlinarith
  linarith [mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr hq2)]

lemma regularized_peak_phase_mean_continuous {a ε ρ : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ ρ)
    (hε : ε ≠ 0) (P : Finset Sphere) {k : ℕ} (hk : 0 < k) :
    Continuous (fun ξ : Sphere => ∫ z : Circle,
      regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k (phaseAction z ξ)) ∂circleMeasure) := by
  simp_rw [regularized_peak_phase_mean ha hr hε P hk]
  have hP : Continuous (fun ξ : Sphere => peakPolynomial P k ξ) :=
    (peakPolynomial_analytic P k).continuous.comp continuous_subtype_val
  have hL : Continuous (fun ξ : Sphere => logFactor (a*ρ*‖peakPolynomial P k ξ‖) ε) :=
    logFactor_continuous.comp ((continuous_const.mul hP.norm).prodMk continuous_const)
  exact (hL.log (fun ξ => (logFactor_pos _ _).ne')).sub continuous_const

lemma peak_off_set_integral {a ε ρ : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ ρ) (hr1 : ρ ≤ 1)
    (hε : ε ≠ 0) (P : Finset Sphere) {k : ℕ} (hk : 0 < k)
    {s : Set Sphere} (hs : MeasurableSet s)
    (hinv : ∀ z ξ, phaseAction z ξ ∈ s ↔ ξ ∈ s)
    (hsmall : ∀ ξ ∈ s, a*‖peakPolynomial P k ξ‖ ≤ 1/2) :
    (∫ ξ in s, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ) ∂sigma) ≤
      2*a*ε^2*(P.card:ℝ)/k := by
  let V : Sphere → ℝ := fun ξ => regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ)
  have hP : Continuous (fun ξ : Sphere => peakPolynomial P k ξ) :=
    (peakPolynomial_analytic P k).continuous.comp continuous_subtype_val
  have hV : Continuous V := (regularizedLog_contDiff a hε).continuous.comp (continuous_const.mul hP)
  have hA : Continuous (fun ξ : Sphere => ∫ z : Circle, V (phaseAction z ξ) ∂circleMeasure) :=
    regularized_peak_phase_mean_continuous ha hr hε P hk
  have hN : Continuous (fun ξ : Sphere => a*ε^2*‖peakPolynomial P k ξ‖) := continuous_const.mul hP.norm
  change (∫ ξ in s, V ξ ∂sigma) ≤ _
  rw [sigma_phase_average_restrict hV hs hinv]
  calc
    _ ≤ ∫ ξ in s, a*ε^2*‖peakPolynomial P k ξ‖ ∂sigma := by
      apply setIntegral_mono_on (compact_continuous_integrable hA) (compact_continuous_integrable hN) hs
      intro ξ hξ
      exact regularized_peak_phase_mean_bound ha hr hr1 hε P hk ξ (hsmall ξ hξ)
    _ ≤ ∫ ξ, a*ε^2*‖peakPolynomial P k ξ‖ ∂sigma := by
      apply setIntegral_le_integral (compact_continuous_integrable hN)
      exact Eventually.of_forall (fun ξ => by positivity)
    _ = a*ε^2*(∫ ξ, ‖peakPolynomial P k ξ‖ ∂sigma) := integral_const_mul _ _
    _ ≤ a*ε^2*(2*(P.card:ℝ)/(k+2)) := by
      gcongr
      exact peak_integral_bound P k
    _ ≤ _ := by
      have hk0 : (0:ℝ) < k := by exact_mod_cast hk
      have hm : 2*(P.card:ℝ)/(k+2:ℝ) ≤ 2*(P.card:ℝ)/k := by gcongr; linarith
      have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ a*ε^2 by positivity)
      convert! hh using 1; ring

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseNegativeScaleBound
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
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma weighted_patch_negative {a ε ρ C M D Δ : ℝ} (ha : 0 ≤ a) (hε : ε ≠ 0)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hlip : ∀ v w : ℂ, ‖v‖ ≤ max gaussianConstant 1 → ‖w‖ ≤ max gaussianConstant 1 →
      |regularizedLog a ε v-regularizedLog a ε w| ≤ C*‖v-w‖)
    {k : ℕ} (hk : 0 < k) (pr : RadialProfiles a) (hkR : 2*pr.R ≤ k)
    (hD : 1 ≤ D) (hDR : Real.sqrt (2*pr.R) ≤ D)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P) {p : Sphere} (hp : p ∈ P)
    (hb : ∀ y ∈ Icc 0 pr.R, |Real.log (logFactor (a*ρ*Real.exp (-y)) ε)-Real.log (1+ε^2)| ≤ M)
    (hm : modelMean a ε ρ pr.R pr.f ≤ -(3/4)*Δ)
    (hweight : 2*pr.R^2*M/k ≤ Δ/8)
    (herror : pr.R*(C*gaussianConstant*Real.exp (-(D-Real.sqrt (2*pr.R))^2/4))*(1+Real.exp 1) ≤ Δ/8) :
    (∫ ξ in peakPatch k pr.R p, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ)*
      (1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) ∂sigma) ≤ -Δ/k := by
  have h1 := (abs_le.mp (weighted_patch_error hε hρ hρ1 hC hlip hk pr hkR hD hDR hP hp)).2
  have h2 := ideal_patch_upper ha hε hρ hM pr hk p hb
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have h3 := mul_le_mul_of_nonneg_left herror (show 0 ≤ 2/(k:ℝ) by positivity)
  have h4 : 2/(k:ℝ)*(modelMean a ε ρ pr.R pr.f+2*pr.R^2*M/k) ≤ 2/(k:ℝ)*(-(3/4)*Δ+Δ/8) := by gcongr
  have he : (2*pr.R/k)*(C*gaussianConstant*Real.exp (-(D-Real.sqrt (2*pr.R))^2/4))*(1+Real.exp 1)=
      (2/(k:ℝ))*(pr.R*(C*gaussianConstant*Real.exp (-(D-Real.sqrt (2*pr.R))^2/4))*(1+Real.exp 1)) := by ring
  rw [he] at h1
  calc
    _ ≤ 2/(k:ℝ)*(-(3/4)*Δ+Δ/8)+(2/(k:ℝ))*(Δ/8) := by linarith
    _ = _ := by ring

lemma one_scale_average_negative {a ε ρ Δ D : ℝ} (ha : 0 ≤ a) (hε : ε ≠ 0)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hΔ : 0 < Δ) (pr : RadialProfiles a)
    {k : ℕ} (hk : 0 < k) (hkR : 2*pr.R ≤ k) (hD : 1 ≤ D)
    (hoff : a*(gaussianConstant*Real.exp (-pr.R/4)) ≤ 1/2)
    (hsep : 2*Real.sqrt (2*pr.R) < D) {P : Finset Sphere}
    (hP : ProjectivelySeparated (D/Real.sqrt k) P)
    (heps : 2*a*ε^2 ≤ Δ/8)
    (hpatch : ∀ p ∈ P, (∫ ξ in peakPatch k pr.R p, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ)*
      (1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) ∂sigma) ≤ -Δ/k) :
    (∫ ξ : Sphere, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ) ∂sigma)+
      ∑ p ∈ P, ∫ ξ : Sphere, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ)*
        densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ ∂sigma ≤ -(Δ/2)*((P.card:ℝ)/k) := by
  have hV : Continuous (fun ξ : Sphere => regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ)) :=
    (regularizedLog_contDiff a hε).continuous.comp
      (continuous_const.mul ((peakPolynomial_analytic P k).continuous.comp continuous_subtype_val))
  rw [patch_decomposition pr hk P (peakPatch_disjoint hk pr.R_pos hsep hP) hV]
  have ho := peak_off_set_integral ha hρ hρ1 hε P hk
    (peakPatchUnion_open P k pr.R).measurableSet.compl
    (fun z ξ => not_congr (peakPatchUnion_phase P k pr.R z ξ)) (fun ξ hξ => ?_)
  · have hs := Finset.sum_le_sum hpatch
    have he : (∑ p ∈ P, (-Δ/(k:ℝ)))= -Δ*((P.card:ℝ)/k) := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
    rw [he] at hs
    have hk0 : (0:ℝ) < k := by exact_mod_cast hk
    have hc : 0 ≤ (P.card:ℝ)/(k:ℝ) := by positivity
    have hεbound := mul_le_mul_of_nonneg_right heps hc
    have he' : 2*a*ε^2*(P.card:ℝ)/k=(2*a*ε^2)*((P.card:ℝ)/k) := by ring
    rw [he'] at ho
    nlinarith
  · apply le_trans (mul_le_mul_of_nonneg_left (peak_off_patch (by omega) pr.R_pos hkR hD hP ξ ?_) ha) hoff
    intro p hp hmem
    exact hξ (mem_iUnion.mpr ⟨p,mem_iUnion.mpr ⟨hp,hmem⟩⟩)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseNegativeThreshold
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
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma gaussian_shift_tendsto (R : ℝ) :
    Tendsto (fun D : ℝ => Real.exp (-(D-R)^2/4)) atTop (𝓝 0) := by
  have hs : Tendsto (fun D : ℝ => D-R) atTop atTop := by
    apply tendsto_atTop.2
    intro B
    filter_upwards [eventually_ge_atTop (B+R)] with D hD
    linarith
  have hh : Tendsto (fun D : ℝ => (D-R)^2/4) atTop atTop :=
    ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hs).atTop_div_const (by norm_num)
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hh using 1
  ext D
  congr 1
  ring

lemma profiles_off_patch {a : ℝ} (ha : 1 < a) (ha2 : a < 2) :
    ∃ pr : RadialProfiles a, a*(gaussianConstant*Real.exp (-pr.R/4)) ≤ 1/2 := by
  have hh : Tendsto (fun R : ℝ => a*(gaussianConstant*Real.exp (-R/4))) atTop (𝓝 0) := by
    have he : Tendsto (fun R : ℝ => Real.exp (-R/4)) atTop (𝓝 0) := by
      convert Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<4)) using 1
      ext R; congr 1; dsimp; ring
    simpa only [mul_assoc,mul_zero] using he.const_mul (a*gaussianConstant)
  obtain ⟨R,hR⟩ := eventually_atTop.mp (hh.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)))
  obtain ⟨pr,hpr⟩ := exists_radialProfiles ha ha2 R
  exact ⟨pr,(hR pr.R hpr.le).le⟩

theorem negative_scale_parameters {a : ℝ} (ha : 1 < a) (pr : RadialProfiles a)
    (hoff : a*(gaussianConstant*Real.exp (-pr.R/4)) ≤ 1/2) :
    ∃ ε η Dstar : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < η ∧ η < 1/2 ∧ 1 ≤ Dstar ∧
      ∀ D : ℝ, Dstar ≤ D → ∃ kmin : ℕ, ∃ d : ℝ, 0 < d ∧
        ∀ k : ℕ, kmin ≤ k → ∀ P : Finset Sphere,
          ProjectivelySeparated (D/Real.sqrt k) P → ProjectiveCover (D/Real.sqrt k) P →
          ∀ ρ ∈ Icc (1-η) 1,
            (∫ ξ : Sphere, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ) ∂sigma)+
              ∑ p ∈ P, ∫ ξ : Sphere, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ)*
                densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ ∂sigma ≤ -d := by
  have ha0 : 0 < a := by linarith
  obtain ⟨ε,η,he,he1,heta,heta1,heps,hmodel⟩ := model_regularization_parameters ha pr (by positivity : 0 < 2*a)
  obtain ⟨C,hC,hval,hlip⟩ := regularizedLog_uniform_bounds a he.ne' (A := max gaussianConstant 1) (by positivity)
  obtain ⟨M,hM,hlog⟩ := radial_log_bound a ε pr.R_pos.le
  let Δ := modelGap a pr
  have hΔ : 0 < Δ := modelGap_pos pr
  have herror : Tendsto (fun D : ℝ => pr.R*(C*gaussianConstant*Real.exp (-(D-Real.sqrt (2*pr.R))^2/4))*(1+Real.exp 1)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using ((gaussian_shift_tendsto (Real.sqrt (2*pr.R))).const_mul (C*gaussianConstant)).const_mul pr.R |>.mul_const (1+Real.exp 1)
  obtain ⟨D₁,hD₁⟩ := eventually_atTop.mp (herror.eventually (gt_mem_nhds (by positivity : 0 < Δ/8)))
  let Dstar := max D₁ (max 1 (2*Real.sqrt (2*pr.R)+1))
  refine ⟨ε,η,Dstar,he,he1,heta,heta1,(le_max_left 1 _).trans (le_max_right _ _),?_⟩
  intro D hD
  have hD1 : D₁ ≤ D := (le_max_left _ _).trans hD
  have hDge : 1 ≤ D := (le_max_left 1 _).trans ((le_max_right _ _).trans hD)
  have hDsep : 2*Real.sqrt (2*pr.R) < D := by
    have hh := (le_max_right 1 (2*Real.sqrt (2*pr.R)+1)).trans ((le_max_right D₁ _).trans hD)
    linarith
  have hDR : Real.sqrt (2*pr.R) ≤ D := by linarith [Real.sqrt_nonneg (2*pr.R)]
  have hweight : Tendsto (fun t : ℝ => 2*pr.R^2*M/t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  obtain ⟨n,hn⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually
    (hweight.eventually (gt_mem_nhds (by positivity : 0 < Δ/8))))
  obtain ⟨nR,hnR⟩ := exists_nat_ge (max (2*pr.R) (D^2))
  refine ⟨max 1 (max n nR),Δ/(2*D^2),by positivity,?_⟩
  intro k hk P hP hcover ρ hρ
  have hk1 : 1 ≤ k := (le_max_left _ _).trans hk
  have hkn : n ≤ k := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hkr : nR ≤ k := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  have hkR : 2*pr.R ≤ k := (le_max_left _ _).trans (hnR.trans (by exact_mod_cast hkr))
  have hkD : D^2 ≤ k := (le_max_right _ _).trans (hnR.trans (by exact_mod_cast hkr))
  have hρ0 : 0 ≤ ρ := by linarith [hρ.1]
  have hpatch : ∀ p ∈ P, (∫ ξ in peakPatch k pr.R p, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ)*
      (1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) ∂sigma) ≤ -Δ/k := by
    intro p hp
    exact weighted_patch_negative ha0.le he.ne' hρ0 hρ.2 hC hM hlip
      (by omega : 0 < k) pr hkR hDge hDR hP hp (hlog ρ ⟨hρ0,hρ.2⟩)
      (hmodel ρ hρ) (hn k hkn).le (hD₁ D hD1).le
  have hh := one_scale_average_negative ha0.le he.ne' hρ0 hρ.2 hΔ pr (by omega) hkR hDge hoff hDsep hP heps hpatch
  apply hh.trans
  have hcount := (peak_count hDge hkD hP hcover).1
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hcnt : 1/D^2 ≤ (P.card:ℝ)/k := by
    apply (le_div_iff₀ hk0).mpr
    simpa only [one_div,mul_comm,div_eq_mul_inv,mul_one] using hcount
  have hn' := mul_le_mul_of_nonneg_left hcnt (show 0 ≤ Δ/2 by positivity)
  convert neg_le_neg hn' using 1 <;> ring

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseLaterNegative
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
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma logarithmicTest_scaled (a ε r : ℝ) (P : Finset Sphere) (k : ℕ) (ξ : Sphere) :
    logarithmicTest a ε P k ((r:ℂ) • (ξ:Base)) =
      regularizedLog 1 ε (((a:ℂ)*(r:ℂ)^k)*peakPolynomial P k ξ) := by
  rw [logarithmicTest,peakPolynomial_homogeneous,regularizedLog_scale]
  congr 1
  ring

lemma logarithmicTest_later_comparison {a : ℝ} (ha : 0 ≤ a) (pr : RadialProfiles a)
    {Q M i N : ℕ} (hQ : 2 ≤ Q) (hM : M+2 < Q) (hi : 1 ≤ i) (hiN : i ≤ N)
    (P : ℕ → Finset Sphere) {D : ℝ} (hD : 1 ≤ D)
    (hP : ProjectivelySeparated (D/Real.sqrt (Q^i:ℕ)) (P (Q^i)))
    {ε θ r : ℝ} (he : ε ≠ 0) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hb : ∀ q ∈ Icc 0 (a*gaussianConstant), q/logFactor q ε ≤ θ)
    (hposi : ∀ ξ : Sphere, 0 ≤ density Q pr.R pr.f pr.b P i ξ)
    (hposN : ∀ ξ : Sphere, 0 ≤ density Q pr.R pr.f pr.b P N ξ)
    [IsProbabilityMeasure (densityMeasure (density Q pr.R pr.f pr.b P i))]
    [IsProbabilityMeasure (densityMeasure (density Q pr.R pr.f pr.b P N))] :
    |(∫ ξ : Sphere, logarithmicTest a ε (P (Q^i)) (Q^i) ((r:ℂ) • (ξ:Base)) ∂densityMeasure (density Q pr.R pr.f pr.b P N))-
      (∫ ξ : Sphere, logarithmicTest a ε (P (Q^i)) (Q^i) ((r:ℂ) • (ξ:Base)) ∂densityMeasure (density Q pr.R pr.f pr.b P i))| ≤
      4*θ^(M+1)/(1-θ) := by
  simp_rw [logarithmicTest_scaled]
  apply density_log_comparison pr hQ hM hiN P he hθ hθ1 _ _ hposi hposN
  intro ξ
  rw [logNormalized,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (logFactor_pos _ _)]
  apply hb _
  constructor
  · exact norm_nonneg _
  · rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hr]
    have hk : 1 ≤ Q^i := (show 1 ≤ Q by omega).trans
      (le_self_pow (by omega) (Nat.ne_of_gt hi))
    calc a*r^(Q^i)*‖peakPolynomial (P (Q^i)) (Q^i) ξ‖ ≤ a*1*gaussianConstant :=
          mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_one₀ hr hr1) ha)
            (peak_sphere_bound hD hk hP ξ) (norm_nonneg _) (by positivity)
         _ = _ := by ring

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseTestSystem
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
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma exists_testSystem : Nonempty TestSystem := by
  classical
  let a : ℝ := 3/2
  have ha : 1 < a := by norm_num [a]
  have ha2 : a < 2 := by norm_num [a]
  have ha0 : 0 < a := by linarith
  obtain ⟨pr,hoff⟩ := profiles_off_patch ha ha2
  obtain ⟨ε,η,Dstar,he,he1,heta,heta1,hDs,hnegative⟩ := negative_scale_parameters ha pr hoff
  let D := max Dstar (2*Real.sqrt (2*pr.R)+1)
  have hDstar : Dstar ≤ D := le_max_left _ _
  have hD : 1 ≤ D := hDs.trans hDstar
  have hDR : 2*Real.sqrt (2*pr.R) < D := by
    have := le_max_right Dstar (2*Real.sqrt (2*pr.R)+1)
    dsimp [D]; linarith
  obtain ⟨kmin,d,hd,hneg⟩ := hnegative D hDstar
  obtain ⟨M,θ,hθ,hθ1,herr,hθb⟩ := logarithmicTest_later_threshold ha0.le he.ne' (by positivity : 0 < d/2)
  obtain ⟨c,K,hc,hK,hden⟩ := uniform_representing_densities pr
  obtain ⟨Q₀,hQ₀⟩ := hden D hDR kmin
  obtain ⟨nD,hnD⟩ := exists_nat_ge (D^2)
  let Q := max Q₀ (max nD (M+3))
  obtain ⟨hQ,hQk,hQT⟩ := hQ₀ Q (le_max_left _ _)
  have hQM : M+2 < Q := by
    have := (le_max_right nD (M+3)).trans (le_max_right Q₀ (max nD (M+3)))
    dsimp [Q]; omega
  have hQD : D^2 ≤ Q := hnD.trans (by exact_mod_cast (le_max_left nD (M+3)).trans (le_max_right Q₀ (max nD (M+3))))
  have hex (k : ℕ) : ∃ P : Finset Sphere,
      D^2 ≤ k → ProjectivelySeparated (D/Real.sqrt k) P ∧ ProjectiveCover (D/Real.sqrt k) P := by
    by_cases hk : D^2 ≤ k
    · have hk0 : 0 < (k:ℝ) := by nlinarith
      have hs : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.2 hk0
      have hρ1 : D/Real.sqrt k ≤ 1 := (div_le_one hs).2 ((Real.le_sqrt (by linarith) hk0.le).2 hk)
      obtain ⟨P,hP⟩ := exists_separated_cover (div_pos (by linarith) hs) hρ1
      exact ⟨P,fun _ => hP⟩
    · exact ⟨∅,fun hh => False.elim (hk hh)⟩
  choose P hP using hex
  have hdegree (j : ℕ) : Q ≤ Q^(j+1) := by
    calc Q = Q^1 := (pow_one Q).symm
         _ ≤ Q^(j+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hsets (j : ℕ) := hP (Q^(j+1)) (hQD.trans (by exact_mod_cast hdegree j))
  have hsep := fun j => (hsets j).1
  have ht := hQT P hsep
  have hpositive : ∀ N (ξ : Sphere), 0 ≤ density Q pr.R pr.f pr.b P N ξ :=
    fun N ξ => ((ht N).2.1.positive ξ).le
  have hprob := fun N => (ht N).2.2.2.2.1
  have hrep := fun N => (ht N).2.2.2.2.2
  refine ⟨⟨a,ε,η,d/2,D,Q,P,pr,ha0,he,heta,heta1,by positivity,hD,hQ,hsep,hpositive,hprob,hrep,?_⟩⟩
  intro N j hjN r hr hnear
  let := hprob N
  let := hprob (j+1)
  have hlow : (∫ ξ : Sphere, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ((r:ℂ) • (ξ:Base))
      ∂densityMeasure (density Q pr.R pr.f pr.b P (j+1))) ≤ -d := by
    rw [densityMeasure_integral (ht (j+1)).1.continuous (hpositive (j+1))]
    simp only [smul_eq_mul]
    simp_rw [mul_comm (density Q pr.R pr.f pr.b P (j+1) _)]
    rw [logarithmicTests_exact_averaging pr he.ne' hQ P j r]
    have hh := hneg (Q^(j+1)) (hQk.trans (hdegree j)) (P (Q^(j+1))) (hsets j).1 (hsets j).2
      (r^(Q^(j+1))) ⟨hnear,pow_le_one₀ hr.1 hr.2⟩
    simpa only [logarithmicTest,peakPolynomial_homogeneous,Complex.ofReal_pow] using hh
  have hcomp := logarithmicTest_later_comparison ha0.le pr hQ hQM (by omega : 1 ≤ j+1) hjN P hD
    (hsep j) he.ne' hθ.le hθ1 hr.1 hr.2 hθb (hpositive (j+1)) (hpositive N)
  have hb := (le_abs_self _).trans (hcomp.trans herr)
  linarith

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseSeriesBounds
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
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma logarithmicTest_value_bound (a : ℝ) {ε D : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, 1 ≤ k → ∀ P : Finset Sphere,
      ProjectivelySeparated (D/Real.sqrt k) P → ∀ z : Base, ‖z‖ ≤ 1 →
      ‖logarithmicTest a ε P k z‖ ≤ B*‖z‖^k := by
  obtain ⟨C,hC,hCb⟩ := regularizedLog_lipschitz_bound a he gaussianConstant_pos.le
  refine ⟨C*gaussianConstant,mul_nonneg hC gaussianConstant_pos.le,?_⟩
  intro k hk P hP z hz
  have hp := peak_global_bound hD hk hP z
  have hpG : ‖peakPolynomial P k z‖ ≤ gaussianConstant :=
    hp.trans (mul_le_of_le_one_right gaussianConstant_pos.le (pow_le_one₀ (norm_nonneg _) hz))
  exact (hCb _ hpG).trans ((mul_le_mul_of_nonneg_left hp hC).trans_eq (by ring))

lemma logarithmicTest_sphere_bound (a : ℝ) {ε D : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, 1 ≤ k → ∀ P : Finset Sphere,
      ProjectivelySeparated (D/Real.sqrt k) P → ∀ r ∈ Icc (0:ℝ) 1, ∀ ξ : Sphere,
      ‖logarithmicTest a ε P k ((r:ℂ) • (ξ:Base))‖ ≤ B*r^k := by
  obtain ⟨B,hB,hBb⟩ := logarithmicTest_value_bound a he hD
  refine ⟨B,hB,?_⟩
  intro k hk P hP r hr ξ
  have hn : ‖(r:ℂ) • (ξ:Base)‖=r := by simp [norm_smul,abs_of_nonneg hr.1]
  simpa only [hn] using hBb k hk P hP ((r:ℂ) • (ξ:Base)) (by simpa only [hn] using hr.2)

lemma logarithmicTest_integral_series (a : ℝ) {ε D : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D)
    {Q : ℕ} (hQ : 2 ≤ Q) (P : ℕ → Finset Sphere)
    (hP : ∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1))))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (μ : Measure Sphere) [IsProbabilityMeasure μ] :
    Summable (fun j => ∫ ξ : Sphere,
      logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ((r:ℂ) • (ξ:Base)) ∂μ) ∧
    (∫ ξ : Sphere, (∑' j, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ((r:ℂ) • (ξ:Base))) ∂μ) =
      ∑' j, ∫ ξ : Sphere, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ((r:ℂ) • (ξ:Base)) ∂μ := by
  let f := fun j (ξ : Sphere) => logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ((r:ℂ) • (ξ:Base))
  have hi (j : ℕ) : Integrable (f j) μ := continuous_integrable
    ((logarithmicTest_contDiff a he _ _).continuous.comp ((continuous_subtype_val : Continuous (fun ξ : Sphere => (ξ:Base))).const_smul (r:ℂ)))
  obtain ⟨B,hB,hBb⟩ := logarithmicTest_sphere_bound a he hD
  have hb (j : ℕ) (ξ : Sphere) : ‖f j ξ‖ ≤ B*r^(Q^(j+1)) :=
    hBb _ (Nat.one_le_pow _ _ (by omega)) _ (hP j) r ⟨hr,hr1.le⟩ ξ
  have hn (j : ℕ) : (∫ ξ, ‖f j ξ‖ ∂μ) ≤ B*r^(Q^(j+1)) := by
    have hh := integral_mono (hi j).norm
      (integrable_const (B*r^(Q^(j+1)))) (fun ξ => hb j ξ)
    simpa using hh
  have hs : Summable (fun j => ∫ ξ, ‖f j ξ‖ ∂μ) := Summable.of_nonneg_of_le
    (fun j => integral_nonneg (fun ξ => norm_nonneg _)) hn ((summable_lacunary hr hr1 hQ).mul_left B)
  exact ⟨Summable.of_norm_bounded hs (fun j => norm_integral_le_integral_norm _),
    (integral_tsum_of_summable_integral_norm hi hs).symm⟩

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseRadii
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
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma testRadius_mem {Q : ℕ} (hQ : 2 ≤ Q) {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (N : ℕ) : 0 < testRadius Q η N ∧ testRadius Q η N < 1 := by
  have hQ1 : 1 ≤ (Q:ℝ) := by exact_mod_cast (show 1 ≤ Q by omega)
  have hp : 1 ≤ (Q:ℝ)^N := one_le_pow₀ hQ1
  have hd : 0 < η/(Q:ℝ)^N := div_pos hη (by positivity)
  have hd1 : η/(Q:ℝ)^N < 1 := (div_lt_one (by positivity)).2 (hη1.trans_le hp)
  dsimp [testRadius]
  constructor <;> linarith

lemma testRadius_near {Q : ℕ} (hQ : 2 ≤ Q) {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    {N j : ℕ} (hj : j+1 ≤ N) : 1-η ≤ (testRadius Q η N)^(Q^(j+1)) := by
  have hp : 0 < (Q:ℝ)^N := by positivity
  have hp1 : 1 ≤ (Q:ℝ)^N := one_le_pow₀ (by exact_mod_cast (show 1 ≤ Q by omega))
  have hd : η/(Q:ℝ)^N ≤ 1 := (div_le_one hp).2 (hη1.le.trans hp1)
  have hbern := one_add_mul_le_pow (a := -η/(Q:ℝ)^N) (by rw [neg_div]; linarith : -2 ≤ -η/(Q:ℝ)^N) (Q^(j+1))
  have hk : (Q:ℝ)^(j+1) ≤ (Q:ℝ)^N := pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ Q by omega)) hj
  have hm : (Q:ℝ)^(j+1)*(η/(Q:ℝ)^N) ≤ η := by
    calc _ ≤ (Q:ℝ)^N*(η/(Q:ℝ)^N) := mul_le_mul_of_nonneg_right hk (div_nonneg hη.le hp.le)
         _ = η := mul_div_cancel₀ η hp.ne'
  simp only [Nat.cast_pow,neg_div,mul_neg,← sub_eq_add_neg] at hbern
  exact (by linarith : 1-η ≤ 1-(Q:ℝ)^(j+1)*(η/(Q:ℝ)^N)).trans hbern

lemma testRadius_tail {Q : ℕ} (hQ : 2 ≤ Q) {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (N m : ℕ) : (testRadius Q η N)^(Q^(m+N+1)) ≤ (Real.exp (-η))^(m+1) := by
  have hp : 0 < (Q:ℝ)^N := by positivity
  have hbase : testRadius Q η N ≤ Real.exp (-η/(Q:ℝ)^N) := by
    simpa only [testRadius,neg_div] using Real.one_sub_le_exp_neg (η/(Q:ℝ)^N)
  have hpow := pow_le_pow_left₀ (testRadius_mem hQ hη hη1 N).1.le hbase (Q^(m+N+1))
  rw [← Real.exp_nat_mul] at hpow
  have heq : ((Q^(m+N+1):ℕ):ℝ)*(-η/(Q:ℝ)^N) = -η*(Q:ℝ)^(m+1) := by
    rw [Nat.cast_pow,show m+N+1=N+(m+1) by omega,pow_add]
    field_simp
  rw [heq] at hpow
  have hdeg : (m+1:ℝ) ≤ (Q:ℝ)^(m+1) := by exact_mod_cast lacunary_degree_ge hQ m
  calc _ ≤ Real.exp (-η*(Q:ℝ)^(m+1)) := hpow
       _ ≤ Real.exp ((m+1)*(-η)) := Real.exp_le_exp.mpr (by nlinarith)
       _ = (Real.exp (-η))^(m+1) := by simpa using Real.exp_nat_mul (-η) (m+1)

lemma testRadius_log {Q : ℕ} (hQ : 2 ≤ Q) {η : ℝ} (hη : 0 < η) (N : ℕ) :
    Real.log (1/(1-testRadius Q η N)) = (N:ℝ)*Real.log Q-Real.log η := by
  have hp : (Q:ℝ)^N ≠ 0 := by positivity
  rw [testRadius]
  have heq : 1/(1-(1-η/(Q:ℝ)^N)) = (Q:ℝ)^N/η := by field_simp [hη.ne']; ring
  rw [heq,Real.log_div hp hη.ne',Real.log_pow]

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseMinorant
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
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma TestSystem.series_mean_bound (S : TestSystem) :
    ∃ T : ℝ, ∀ N : ℕ,
      (∫ ξ : Sphere, (∑' j, logarithmicTest S.a S.ε (S.P (S.Q^(j+1))) (S.Q^(j+1))
        ((testRadius S.Q S.η N:ℂ) • (ξ:Base)))
        ∂densityMeasure (density S.Q S.pr.R S.pr.f S.pr.b S.P N)) ≤ -(S.d)*(N:ℝ)+T := by
  obtain ⟨B,hB,hBb⟩ := logarithmicTest_sphere_bound S.a S.eps_pos.ne' S.D_ge
  let t := Real.exp (-S.η)
  have ht : 0 ≤ t := (Real.exp_pos _).le
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by linarith [S.eta_pos])
  have hsum : Summable (fun m : ℕ => B*t^(m+1)) := by
    simpa only [pow_succ,mul_assoc,mul_left_comm,mul_comm] using
      ((summable_geometric_of_lt_one ht ht1).mul_left B).mul_right t
  refine ⟨∑' m : ℕ, B*t^(m+1),?_⟩
  intro N
  let μ := densityMeasure (density S.Q S.pr.R S.pr.f S.pr.b S.P N)
  let : IsProbabilityMeasure μ := S.probability N
  let r := testRadius S.Q S.η N
  have hr := testRadius_mem S.Q_ge S.eta_pos (by linarith [S.eta_lt] : S.η < 1) N
  obtain ⟨hs,he⟩ := logarithmicTest_integral_series S.a S.eps_pos.ne' S.D_ge S.Q_ge S.P S.separated hr.1.le hr.2 μ
  rw [he,← hs.sum_add_tsum_nat_add N]
  have hlo : (∑ j ∈ Finset.range N, ∫ ξ : Sphere,
      logarithmicTest S.a S.ε (S.P (S.Q^(j+1))) (S.Q^(j+1)) ((r:ℂ) • (ξ:Base)) ∂μ) ≤ -(S.d)*(N:ℝ) := by
    have hh := Finset.sum_le_sum (s := Finset.range N) (g := fun _ => -S.d) (fun j hj =>
      S.negative N j (by simp only [Finset.mem_range] at hj; omega) r ⟨hr.1.le,hr.2.le⟩
        (testRadius_near S.Q_ge S.eta_pos (by linarith [S.eta_lt]) (by simp only [Finset.mem_range] at hj; omega)))
    simpa [mul_comm] using hh
  have htail : (∑' m, ∫ ξ : Sphere,
      logarithmicTest S.a S.ε (S.P (S.Q^(m+N+1))) (S.Q^(m+N+1)) ((r:ℂ) • (ξ:Base)) ∂μ) ≤ ∑' m : ℕ, B*t^(m+1) := by
    apply (hs.comp_injective (fun m n h => Nat.add_right_cancel h)).tsum_le_tsum _ hsum
    intro m
    have hb (ξ : Sphere) : ‖logarithmicTest S.a S.ε (S.P (S.Q^(m+N+1))) (S.Q^(m+N+1)) ((r:ℂ) • (ξ:Base))‖ ≤ B*t^(m+1) :=
      (hBb _ (Nat.one_le_pow _ _ (by have := S.Q_ge; omega)) _ (S.separated (m+N)) r ⟨hr.1.le,hr.2.le⟩ ξ).trans
        (mul_le_mul_of_nonneg_left (testRadius_tail S.Q_ge S.eta_pos (by linarith [S.eta_lt]) N m) hB)
    have hh := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hb)
    exact (le_abs_self _).trans (by simpa [r,Function.comp_def] using hh)
  exact add_le_add hlo htail

lemma psi_radial_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (ξ : Sphere) :
    psi ((r:ℂ) • (ξ:Base)) ≤ Real.log (1/(1-r)) := by
  have hn : ‖(r:ℂ) • (ξ:Base)‖=r := by simp [norm_smul,abs_of_nonneg hr]
  rw [psi,hn,one_div,Real.log_inv]
  have h1 : 0 < 1-r := by linarith
  have hle : 1-r ≤ 1-r^2 := by nlinarith
  exact neg_le_neg (Real.log_le_log h1 hle)

lemma TestSystem.noMinorant (S : TestSystem) {L : ℝ} (hL : 0 < L)
    (hamp : 5*Real.log S.Q < L*S.d) : noMinorant (basePotential S.P S.a S.ε L S.Q) := by
  obtain ⟨T,hT⟩ := S.series_mean_bound
  rintro ⟨H,C,hH,hminor⟩
  have hbound (N : ℕ) : (N:ℝ)*(L*S.d-5*Real.log S.Q) ≤ C-5*Real.log S.η+L*T-(H 0).re := by
    let μ := densityMeasure (density S.Q S.pr.R S.pr.f S.pr.b S.P N)
    let : IsProbabilityMeasure μ := S.probability N
    let r := testRadius S.Q S.η N
    have hr := testRadius_mem S.Q_ge S.eta_pos (by linarith [S.eta_lt] : S.η < 1) N
    change 0 < r ∧ r < 1 at hr
    have hrc : ‖(r:ℂ)‖ < 1 := by simpa [abs_of_pos hr.1] using hr.2
    have hmap := radial_mem_ball hrc
    have hiH := continuous_integrable (μ := μ) (radial_continuous hH.continuousOn hrc)
    have hseries := testSeries_contDiffOn S.a S.eps_pos.ne' S.D_ge S.Q_ge S.P S.separated
    have his := continuous_integrable (μ := μ) (hseries.continuousOn.comp_continuous ((continuous_subtype_val : Continuous (fun ξ : Sphere => (ξ:Base))).const_smul (r:ℂ)) hmap)
    change Integrable (fun ξ : Sphere => ∑' j, logarithmicTest S.a S.ε (S.P (S.Q^(j+1))) (S.Q^(j+1)) ((r:ℂ) • (ξ:Base))) μ at his
    have hpoint (ξ : Sphere) : (H ((r:ℂ) • (ξ:Base))).re ≤
        C+5*Real.log (1/(1-r))+L*(∑' j, logarithmicTest S.a S.ε (S.P (S.Q^(j+1))) (S.Q^(j+1)) ((r:ℂ) • (ξ:Base))) := by
      have hh := hminor _ (hmap ξ)
      have hp := psi_radial_le hr.1.le hr.2 ξ
      have hn : ‖(r:ℂ) • (ξ:Base)‖=r := by simp [norm_smul,abs_of_pos hr.1]
      rw [hn,basePotential] at hh
      linarith
    have hi := integral_mono hiH.re ((integrable_const _).add (his.const_mul L)) hpoint
    simp only [Pi.add_apply] at hi his
    rw [integral_add (integrable_const _) (his.const_mul L),integral_const_mul] at hi
    have hre := Complex.reCLM.integral_comp_comm hiH
    have hm := (S.representing N).analytic_mean hH hrc
    change (∫ ξ : Sphere, (H ((r:ℂ) • (ξ:Base))).re ∂μ) = _ at hre
    change (∫ ξ : Sphere, (H ((r:ℂ) • (ξ:Base))).re ∂μ) ≤ _ at hi
    change (∫ ξ : Sphere, H ((r:ℂ) • (ξ:Base)) ∂μ) = H 0 at hm
    rw [hre,hm] at hi
    simp only [integral_const] at hi
    simp at hi
    have ht := mul_le_mul_of_nonneg_left (hT N) hL.le
    simp at ht
    have hl := testRadius_log S.Q_ge S.eta_pos N
    change Real.log (1/(1-r))=_ at hl
    simp only [one_div,Real.log_inv] at hl
    linarith
  have hd : 0 < L*S.d-5*Real.log S.Q := by linarith
  obtain ⟨N,hN⟩ := exists_nat_gt ((C-5*Real.log S.η+L*T-(H 0).re)/(L*S.d-5*Real.log S.Q))
  have hh := (div_lt_iff₀ hd).mp hN
  have := hbound N
  linarith

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open Set Filter Topology Metric
open scoped ContDiff NNReal
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs
open BaseConstruction

theorem controlled_potential_oai : ControlledPotential := by
  obtain ⟨S⟩ := exists_testSystem
  let L := (5*Real.log (S.Q:ℝ))/S.d+1
  have hlog : 0 < Real.log (S.Q:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < S.Q by have := S.Q_ge; omega))
  have hd := S.d_pos
  have hL : 0 < L := by dsimp [L]; positivity
  have hamp : 5*Real.log (S.Q:ℝ) < L*S.d := by
    dsimp [L]
    rw [add_mul,div_mul_cancel₀ _ S.d_pos.ne']
    linarith [S.d_pos]
  obtain ⟨C,hcontrol,hjets⟩ := basePotential_chart_control S.a S.eps_pos.ne' S.D_ge hL.le S.Q_ge S.P S.separated
  exact ⟨basePotential S.P S.a S.ε L S.Q,C,
    basePotential_contDiffOn S.a L S.eps_pos.ne' S.D_ge S.Q_ge S.P S.separated,
    hcontrol,hjets,S.noMinorant hL hamp⟩

end PinchedHartogs

end

end OAI
end

theorem solution : type_of% @OAI.PinchedHartogs.controlled_potential_oai := @OAI.PinchedHartogs.controlled_potential_oai
