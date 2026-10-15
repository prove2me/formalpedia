-- Prove2me | solution 1 for OAI.TriangularCovering.uniform_scalar_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:04:33.765664+00:00
-- url     : https://prove2.me/submissions/77a666fd-fa28-4c2a-b407-1e6b9b8f2f2b

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/Asymptotics.lean:L301-L321
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularCovering.uniform_scalar_sum. Inline helpers are the
-- source spans of proof-only lemmas this proof needs; the node is hoisted out of its namespace
-- as a top-level `theorem solution` with the namespace re-opened.
import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover
import Definitions.Def_OAI_Geometry_TriangularCovering_TriangleArea
import Definitions.Def_OAI_Geometry_TriangularCovering_Projection
import Definitions.Def_OAI_Geometry_TriangularCovering_CylinderFamily
import Definitions.Def_OAI_Geometry_TriangularCovering_Tetrahedron
import Definitions.Def_OAI_Geometry_TriangularCovering_Shadows
import Definitions.Def_OAI_Geometry_TriangularCovering_Asymptotics
import Theorems.Thm_OAI_TriangularCovering_alpha_error
import Theorems.Thm_OAI_TriangularCovering_coeff_bounds
import Theorems.Thm_OAI_TriangularCovering_d_le_max_endpoints
import Theorems.Thm_OAI_TriangularCovering_inv_sqrt_remainder
import Theorems.Thm_OAI_TriangularCovering_mesh_abs_le

-- ---- inline helpers from OAI.Geometry.TriangularCovering.CoordinateCover ----
namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

theorem beta_error {a b q : ℝ} (ha : a ≤ q) (hb : q ≤ b) :
    |beta a b - q / 2| ≤ (b - a) / 4 := by
  rw [abs_le]
  dsimp [beta]
  constructor <;> linarith

end TriangularCovering

namespace TriangularCovering

end TriangularCovering

end

end OAI

-- ---- inline helpers from OAI.Geometry.TriangularCovering.Asymptotics ----
namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

lemma bounded_product_remainder {z M D : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hM0 : 0 ≤ M) (hM1 : M ≤ 1)
    (hD0 : 0 ≤ D) (hD1 : D ≤ 1) :
    |(1/2+z*M)^2 / Real.sqrt (1+z*D) - (1/4+z*(M-D/8))| ≤ 5*z^2 := by
  let A : ℝ := (1/2+z*M)^2
  let R : ℝ := 1/Real.sqrt (1+z*D) - (1-z*D/2)
  have hzM0 : 0 ≤ z*M := mul_nonneg hz0 hM0
  have hzM1 : z*M ≤ 1 := (mul_le_mul hz1 hM1 hM0 (by norm_num)).trans_eq (by norm_num)
  have hA0 : 0 ≤ A := sq_nonneg _
  have hA1 : A ≤ 9/4 := by dsimp [A]; nlinarith only [hzM0,hzM1]
  have hR : |R| ≤ z^2 := by
    have h := inv_sqrt_remainder (mul_nonneg hz0 hD0)
    have hD2 : D^2 ≤ 1 := by nlinarith only [hD0,hD1]
    have hb := mul_le_of_le_one_right (sq_nonneg z) hD2
    dsimp [R]
    exact h.trans (by nlinarith only [hb])
  have hAR : |A*R| ≤ 9/4*z^2 := by
    rw [abs_mul,abs_of_nonneg hA0]
    exact mul_le_mul hA1 hR (abs_nonneg _) (by norm_num)
  have hM2 : M^2 ≤ 1 := by nlinarith only [hM0,hM1]
  have hMD0 : 0 ≤ M*D := mul_nonneg hM0 hD0
  have hMD1 : M*D ≤ 1 := by nlinarith only [mul_le_mul hM1 hD1 hD0 (by norm_num : (0:ℝ) ≤ 1)]
  have hZM0 : 0 ≤ z*M^2*D := by positivity
  have hZM1 : z*M^2*D ≤ 1 := by
    calc
      z*M^2*D ≤ 1*1*1 := mul_le_mul
        (mul_le_mul hz1 hM2 (sq_nonneg _) (by norm_num)) hD1 hD0 (by norm_num)
      _ = 1 := by ring
  have hG : |M^2-M*D/2-z*M^2*D/2| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith only [hM2,sq_nonneg M,hMD0,hMD1,hZM0,hZM1]
  have hZG : |z^2*(M^2-M*D/2-z*M^2*D/2)| ≤ z^2*2 := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left hG (sq_nonneg _)
  have hid : (1/2+z*M)^2 / Real.sqrt (1+z*D) - (1/4+z*(M-D/8)) =
      A*R+z^2*(M^2-M*D/2-z*M^2*D/2) := by dsimp [A,R]; ring
  rw [hid]
  have hab := abs_add_le (A*R) (z^2*(M^2-M*D/2-z*M^2*D/2))
  nlinarith only [hab,hZG,hAR,sq_nonneg z]

lemma term_remainder {ε a b : ℝ} (he : |ε| ≤ 1)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hab : a ≤ b) :
    |normalizedTerm ε a b - (b-a)*(1/4+ε^2*(cutoffCoeff a b-speedSq a b/8))|
      ≤ (b-a)*5*ε^4 := by
  have hc := coeff_bounds ha hb
  have hM0 : 0 ≤ cutoffCoeff a b := by have := hc.2.2.2.1; dsimp [η] at this; linarith
  have hM1 : cutoffCoeff a b ≤ 1 := by have := hc.2.2.2.2; dsimp [η] at this; linarith
  have hD0 : 0 ≤ speedSq a b := by unfold speedSq; positivity
  have hD1 : speedSq a b ≤ 1 := by
    have ha2 : (alpha a b)^2 ≤ 1/4 := by nlinarith only [hc.1,hc.2.1]
    have hb2 : (beta a b)^2 ≤ 1/4 := by nlinarith only [(abs_le.mp hc.2.2.1).1,(abs_le.mp hc.2.2.1).2]
    dsimp [speedSq]
    linarith only [ha2,hb2]
  have he2 : ε^2 ≤ 1 := by nlinarith only [(abs_le.mp he).1,(abs_le.mp he).2]
  have hh := bounded_product_remainder (sq_nonneg ε) he2 hM0 hM1 hD0 hD1
  have hid : normalizedTerm ε a b - (b-a)*(1/4+ε^2*(cutoffCoeff a b-speedSq a b/8)) =
      (b-a)*((1/2+ε^2*cutoffCoeff a b)^2 / Real.sqrt (1+ε^2*speedSq a b) -
        (1/4+ε^2*(cutoffCoeff a b-speedSq a b/8))) := by
    dsimp [normalizedTerm,cutoff]; ring
  rw [hid,abs_mul,abs_of_nonneg (sub_nonneg.mpr hab)]
  have h := mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr hab)
  calc
    _ ≤ (b-a)*(5*(ε^2)^2) := h
    _ = (b-a)*5*ε^4 := by ring

end TriangularCovering

namespace TriangularCovering

lemma d_lipschitz {a q : ℝ} (ha : |a| ≤ 1) (hq : |q| ≤ 1) :
    |d a-d q| ≤ |a-q| := by
  have ha2 : a^2 ≤ 1 := by nlinarith only [(abs_le.mp ha).1,(abs_le.mp ha).2]
  have hq2 : q^2 ≤ 1 := by nlinarith only [(abs_le.mp hq).1,(abs_le.mp hq).2]
  have has : |a+q| ≤ 2 := (abs_add_le _ _).trans (by linarith only [ha,hq])
  have hs0 : 0 ≤ 1+a^2+q^2 := by positivity
  have hs1 : 1+a^2+q^2 ≤ 3 := by linarith only [ha2,hq2]
  have hid : d a-d q = (a-q)*((a+q)*(1+a^2+q^2)/16) := by dsimp [d]; ring
  rw [hid,abs_mul]
  apply mul_le_of_le_one_right (abs_nonneg _)
  rw [abs_div,abs_mul,abs_of_nonneg hs0]
  norm_num
  have hp := mul_le_mul has hs1 hs0 (by norm_num : (0:ℝ) ≤ 2)
  linarith only [hp]

lemma cutoffCoeff_error {a b q : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hq : a ≤ q ∧ q ≤ b) : |cutoffCoeff a b-(η+d q)| ≤ b-a := by
  have hqab : |q| ≤ 1 := abs_le.mpr ⟨(abs_le.mp ha).1.trans hq.1,hq.2.trans (abs_le.mp hb).2⟩
  have h1 := d_lipschitz ha hqab
  have h2 := d_lipschitz hb hqab
  rw [abs_of_nonpos (sub_nonpos.mpr hq.1)] at h1
  rw [abs_of_nonneg (sub_nonneg.mpr hq.2)] at h2
  have hlo := d_le_max_endpoints hq.1 hq.2
  have hhi : max (d a) (d b) ≤ d q+(b-a) := by
    apply max_le <;> linarith only [(abs_le.mp h1).2,(abs_le.mp h2).2,hq.1,hq.2]
  dsimp [cutoffCoeff]
  rw [abs_le]
  constructor <;> linarith only [hlo,hhi,hq.1,hq.2]

lemma sq_error {x y e : ℝ} (hx : |x| ≤ 1/2) (hy : |y| ≤ 1/2)
    (he : |x-y| ≤ e) : |x^2-y^2| ≤ e := by
  have hs : |x+y| ≤ 1 := (abs_add_le _ _).trans (by linarith only [hx,hy])
  rw [sq_sub_sq,abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg (x-y)) hs).trans he

lemma areaDensity_eq (q : ℝ) :
    areaDensity q = η-1/128-q^2/64+7*q^4/128 := by
  dsimp [areaDensity,d]; ring

lemma continuous_areaDensity : Continuous areaDensity := by
  unfold areaDensity d
  fun_prop

lemma density_error {a b q : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hq : a ≤ q ∧ q ≤ b) :
    |cutoffCoeff a b-speedSq a b/8-areaDensity q| ≤ 2*(b-a) := by
  have hqab : |q| ≤ 1 := abs_le.mpr ⟨(abs_le.mp ha).1.trans hq.1,hq.2.trans (abs_le.mp hb).2⟩
  have hc := coeff_bounds ha hb
  have hal : |alpha a b| ≤ 1/2 := by rw [abs_of_nonneg hc.1]; exact hc.2.1
  have hq2 : q^2 ≤ 1 := by nlinarith only [(abs_le.mp hqab).1,(abs_le.mp hqab).2]
  have hql : |(1+q^2)/4| ≤ 1/2 := by rw [abs_of_nonneg (by positivity)]; linarith only [hq2]
  have haq := sq_error hal hql (alpha_error ha hqab hq.1 hq.2)
  have hqr : |q/2| ≤ 1/2 := by rw [abs_div]; norm_num; linarith only [hqab]
  have hbq := sq_error hc.2.2.1 hqr (beta_error hq.1 hq.2)
  have hspeed : |speedSq a b-(((1+q^2)/4)^2+2*(q/2)^2)| ≤ b-a := by
    have hid : speedSq a b-(((1+q^2)/4)^2+2*(q/2)^2) =
        ((alpha a b)^2-((1+q^2)/4)^2)+2*((beta a b)^2-(q/2)^2) := by
      dsimp [speedSq]; ring
    rw [hid]
    have h := abs_add_le ((alpha a b)^2-((1+q^2)/4)^2) (2*((beta a b)^2-(q/2)^2))
    rw [abs_mul] at h
    norm_num at h
    linarith only [h,haq,hbq]
  have hM := cutoffCoeff_error ha hb hq
  have hid : cutoffCoeff a b-speedSq a b/8-areaDensity q =
      (cutoffCoeff a b-(η+d q))-(speedSq a b-(((1+q^2)/4)^2+2*(q/2)^2))/8 := by
    dsimp [areaDensity]; ring
  rw [hid]
  have hr := abs_add_le (cutoffCoeff a b-(η+d q))
    (-((speedSq a b-(((1+q^2)/4)^2+2*(q/2)^2))/8))
  rw [← sub_eq_add_neg,abs_neg] at hr
  rw [abs_div] at hr
  norm_num at hr
  linarith only [hr,hM,hspeed,hq.1,hq.2]

lemma areaDensity_integral : (∫ q in (-1:ℝ)..1, areaDensity q) = -13/6000 := by
  simp_rw [areaDensity_eq]
  have hf : IntervalIntegrable (fun q : ℝ => η-1/128-q^2/64) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hg : IntervalIntegrable (fun q : ℝ => 7*q^4/128) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hh : IntervalIntegrable (fun q : ℝ => q^2/64) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_add hf hg,
    intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _) hh]
  rw [intervalIntegral.integral_div,intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul,integral_pow,integral_pow,intervalIntegral.integral_const]
  norm_num [η]

lemma interval_density_error {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hab : a ≤ b) :
    |(b-a)*(cutoffCoeff a b-speedSq a b/8) - (∫ q in a..b, areaDensity q)| ≤
      2*(b-a)^2 := by
  have hu : ∀ q ∈ Ι a b, ‖cutoffCoeff a b-speedSq a b/8-areaDensity q‖ ≤ 2*(b-a) := by
    intro q hq
    rw [Set.uIoc_of_le hab] at hq
    simpa only [Real.norm_eq_abs] using density_error ha hb ⟨hq.1.le,hq.2⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hu
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => cutoffCoeff a b-speedSq a b/8)
    (g := areaDensity) (continuous_const.intervalIntegrable _ _)
    (continuous_areaDensity.intervalIntegrable _ _),intervalIntegral.integral_const,
    Real.norm_eq_abs,smul_eq_mul,abs_of_nonneg (sub_nonneg.mpr hab)] at h
  nlinarith only [h]

end TriangularCovering

namespace TriangularCovering

lemma count_step {N : ℕ} (hN : 0 < N) : (N : ℝ)*step N = 2 := by
  have h := mesh_last hN
  dsimp [mesh] at h
  linarith only [h]

lemma integral_mesh_sum {N : ℕ} (hN : 0 < N) :
    (∑ j : Fin N, ∫ q in mesh N j..mesh N (j+1), areaDensity q) = -13/6000 := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ∫ q in mesh N j..mesh N (j+1), areaDensity q) N]
  rw [intervalIntegral.sum_integral_adjacent_intervals
    (fun _ _ => continuous_areaDensity.intervalIntegrable _ _)]
  rw [mesh_zero,mesh_last hN,areaDensity_integral]

lemma coefficientSum_error {N : ℕ} (hN : 0 < N) :
    |coefficientSum N + 13/6000| ≤ 4*step N := by
  have hi := integral_mesh_sum hN
  have hid : coefficientSum N+13/6000 =
      ∑ j : Fin N, (step N*(cutoffCoeff (mesh N j) (mesh N (j+1))-
        speedSq (mesh N j) (mesh N (j+1))/8) -
        ∫ q in mesh N j..mesh N (j+1), areaDensity q) := by
    rw [Finset.sum_sub_distrib,hi]
    dsimp [coefficientSum]
    ring
  rw [hid]
  calc
    _ ≤ ∑ j : Fin N, |step N*(cutoffCoeff (mesh N j) (mesh N (j+1))-
        speedSq (mesh N j) (mesh N (j+1))/8) -
        ∫ q in mesh N j..mesh N (j+1), areaDensity q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin N, 2*(step N)^2 := by
      apply Finset.sum_le_sum
      intro j _
      have h := interval_density_error (mesh_abs_le hN j.isLt.le)
        (mesh_abs_le hN j.isLt) (le_of_lt (by have := mesh_succ N j; have := step_pos hN; linarith))
      simpa only [mesh_succ] using h
    _ = 4*step N := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      calc
        (N : ℝ)*(2*(step N)^2) = 2*((N : ℝ)*step N)*step N := by ring
        _ = 4*step N := by rw [count_step hN]; ring

lemma mesh_term_remainder {ε : ℝ} {N : ℕ} (he : |ε| ≤ 1) (hN : 0 < N) :
    |(∑ j : Fin N, normalizedTerm ε (mesh N j) (mesh N (j+1))) -
      (1/2+ε^2 * coefficientSum N)| ≤ 10*ε^4 := by
  let f : Fin N → ℝ := fun j => step N*(1/4+ε^2*
    (cutoffCoeff (mesh N j) (mesh N (j+1))-speedSq (mesh N j) (mesh N (j+1))/8))
  have hsum : (∑ j : Fin N, f j) = 1/2+ε^2*coefficientSum N := by
    dsimp [f,coefficientSum]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib,Finset.mul_sum]
    have heq : (∑ j : Fin N, step N * (ε^2 *
        (cutoffCoeff (mesh N j) (mesh N (j+1))-speedSq (mesh N j) (mesh N (j+1))/8))) =
        ∑ j : Fin N, ε^2 * (step N *
        (cutoffCoeff (mesh N j) (mesh N (j+1))-speedSq (mesh N j) (mesh N (j+1))/8)) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq]
    congr 1
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have := count_step hN
    linarith only [this]
  rw [← hsum,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin N, |normalizedTerm ε (mesh N j) (mesh N (j+1))-f j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin N, step N*5*ε^4 := by
      apply Finset.sum_le_sum
      intro j _
      have hab : mesh N j ≤ mesh N (j+1) := by
        have := mesh_succ N j
        have := step_pos hN
        linarith only [this,mesh_succ N j]
      have h := term_remainder he (mesh_abs_le hN j.isLt.le) (mesh_abs_le hN j.isLt) hab
      simpa only [mesh_succ,f] using h
    _ = 10*ε^4 := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      calc
        (N : ℝ)*(step N*5*ε^4) = ((N : ℝ)*step N)*5*ε^4 := by ring
        _ = 10*ε^4 := by rw [count_step hN]; ring

end TriangularCovering

end

end OAI

-- ---- hoisted node ----
open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem solution {ε : ℝ} {N : ℕ} (he : |ε| ≤ 1) (hN : 0 < N)
    (hstep : step N ≤ ε^2) :
    |(∑ j : Fin N, normalizedTerm ε (mesh N j) (mesh N (j+1))) -
      (1/2-(13/6000:ℝ)*ε^2)| ≤ 14*ε^4 := by
  have hR := mesh_term_remainder he hN
  have hC := coefficientSum_error hN
  have hc : |ε^2*(coefficientSum N+13/6000)| ≤ 4*ε^4 := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
    calc
      ε^2*|coefficientSum N+13/6000| ≤ ε^2*(4*step N) :=
        mul_le_mul_of_nonneg_left hC (sq_nonneg _)
      _ ≤ ε^2*(4*ε^2) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hstep (by norm_num)) (sq_nonneg _)
      _ = 4*ε^4 := by ring
  have hid : (∑ j : Fin N, normalizedTerm ε (mesh N j) (mesh N (j+1))) -
      (1/2-(13/6000:ℝ)*ε^2) =
      ((∑ j : Fin N, normalizedTerm ε (mesh N j) (mesh N (j+1))) -
        (1/2+ε^2*coefficientSum N)) + ε^2*(coefficientSum N+13/6000) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans (by linarith only [hR,hc])
