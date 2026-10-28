-- Prove2me | solution 1 for OAI.ElasticityBoundaryCutoffLayer.correction_order_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:47:00.053161+00:00
-- url     : https://prove2.me/submissions/322ec05d-70ef-4df0-800e-0b984626e76e

import Mathlib
import Definitions.Def_OAIQ6El001

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Literal smooth polynomial amplitudes in boundary coordinates, including
actual Frechet derivatives and polynomial growth. -/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace ElasticityBoundaryMVCalculus

/-- Every fixed amplitude is bounded by a uniform polynomial moment, so the
Gaussian/exponential majorants used for its remainder are honest integrable functions. -/
theorem polynomialGrowth (p : MP) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ y : Y, ‖value p y‖ ≤ C*(1+‖y‖)^d := by
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨‖c‖, norm_nonneg _, 0, fun y => by simp⟩
  | add p q hp hq =>
      obtain ⟨A,hA,a,ha⟩ := hp
      obtain ⟨B,hB,b,hb⟩ := hq
      refine ⟨A+B,add_nonneg hA hB,max a b,fun y => ?_⟩
      have hbase : 1 ≤ 1+‖y‖ := by linarith [norm_nonneg y]
      calc
        _ ≤ ‖value p y‖+‖value q y‖ := by rw [value_add]; exact norm_add_le _ _
        _ ≤ A*(1+‖y‖)^a+B*(1+‖y‖)^b := add_le_add (ha y) (hb y)
        _ ≤ A*(1+‖y‖)^(max a b)+B*(1+‖y‖)^(max a b) :=
          add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (le_max_left _ _)) hA)
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (le_max_right _ _)) hB)
        _ = _ := by ring
  | mul_X p i hp =>
      obtain ⟨A,hA,a,ha⟩ := hp
      refine ⟨A,hA,a+1,fun y => ?_⟩
      have hcoord : ‖(y i : ℂ)‖ ≤ 1+‖y‖ := by
        rw [Complex.norm_real]
        exact (norm_le_pi_norm y i).trans (by linarith)
      calc
        _ = ‖value p y‖*‖(y i : ℂ)‖ := by rw [value_mul, value_X, norm_mul]
        _ ≤ (A*(1+‖y‖)^a)*(1+‖y‖) :=
          mul_le_mul (ha y) hcoord (norm_nonneg _) (by positivity)
        _ = _ := by rw [pow_succ]; ring

end ElasticityBoundaryMVCalculus

end
end
section
/-! Exact anisotropic boundary scaling, retaining the physical dimension-three
Jacobian δ⁴. No asymptotic change-of-variable formula is postulated. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryScaling

lemma scale_norm_le {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (y : Y) :
    ‖scale δ y‖ ≤ δ*‖y‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hδ (norm_nonneg y))).mpr
  intro i
  have hc : |scaleFactor δ i| ≤ δ := by
    unfold scaleFactor
    split_ifs
    · rw [abs_of_nonneg (sq_nonneg δ)]
      nlinarith
    · rw [abs_of_nonneg hδ]
  simpa only [scale_apply, Real.norm_eq_abs, abs_mul] using
    mul_le_mul hc (norm_le_pi_norm y i) (abs_nonneg (y i)) hδ

end ElasticityBoundaryScaling

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryLayers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Uniform true L2/H1 estimates for finite corrected boundary amplitudes. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryParameterBounds
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryProfile
  ElasticityBoundaryProfileBounds ElasticityBoundaryWeights ElasticityBoundaryParameter

lemma atParameter_add (q r : Polynomial MP) (δ : ℝ) :
    atParameter (q+r) δ=atParameter q δ+atParameter r δ := Polynomial.eval_add

lemma value_parameter_monomial (n : ℕ) (p : MP) (δ : ℝ) (y : Y) :
    value (atParameter (Polynomial.monomial n p) δ) y=value p y*(δ:ℂ)^n := by
  simp [atParameter,value]

lemma parameterGrowth (q : Polynomial MP) :
    ∃ A : ℝ, 0≤A ∧ ∃ n : ℕ, ∀ δ : ℝ, 0≤δ → δ≤1 → ∀ y : Y,
      ‖value (atParameter q δ) y‖ ≤ A*(1+‖y‖)^n := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨A,hA,a,ha⟩ := hp
      obtain ⟨B,hB,b,hb⟩ := hq
      refine ⟨A+B,add_nonneg hA hB,max a b,fun δ hδ hδ1 y => ?_⟩
      have hr : 1≤1+‖y‖ := by linarith [norm_nonneg y]
      calc
        _ ≤ ‖value (atParameter p δ) y‖+‖value (atParameter q δ) y‖ := by
          rw [atParameter_add,value_add]; exact norm_add_le _ _
        _ ≤ A*(1+‖y‖)^a+B*(1+‖y‖)^b := add_le_add (ha δ hδ hδ1 y) (hb δ hδ hδ1 y)
        _ ≤ A*(1+‖y‖)^(max a b)+B*(1+‖y‖)^(max a b) :=
          add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (le_max_left _ _)) hA)
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (le_max_right _ _)) hB)
        _ = _ := by ring
  | monomial k p =>
      obtain ⟨A,hA,a,ha⟩ := polynomialGrowth p
      refine ⟨A,hA,a,fun δ hδ hδ1 y => ?_⟩
      rw [value_parameter_monomial, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hδ]
      exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hδ hδ1)).trans (ha y)

end ElasticityBoundaryParameterBounds

end
end
section
/-! Uniform polynomial-growth estimates for the actual smooth coefficient
Taylor errors, multiplied by a finite amplitude family. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryOrderBound
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryParameterBounds
  ElasticityBoundaryTaylorPolynomial ElasticityBoundaryTaylor ElasticityBoundaryScaling
  ElasticityBoundaryProfileBounds ElasticityBoundaryWeights

lemma OrderBound.zero (k : ℕ) : OrderBound (fun _ _ => 0) k := by
  exact ⟨0,le_rfl,0,fun _ _ _ _ => by simp⟩

lemma OrderBound.add {f g : ℝ → Y → ℂ} {k : ℕ}
    (hf : OrderBound f k) (hg : OrderBound g k) : OrderBound (fun δ y => f δ y+g δ y) k := by
  obtain ⟨A,hA,a,ha⟩ := hf
  obtain ⟨B,hB,b,hb⟩ := hg
  refine ⟨A+B,add_nonneg hA hB,max a b,fun δ hδ hδ1 y => ?_⟩
  have hr : 1≤1+‖y‖ := by linarith [norm_nonneg y]
  calc
    _ ≤ ‖f δ y‖+‖g δ y‖ := norm_add_le _ _
    _ ≤ A*δ^k*(1+‖y‖)^a+B*δ^k*(1+‖y‖)^b :=
      add_le_add (ha δ hδ hδ1 y) (hb δ hδ hδ1 y)
    _ ≤ A*δ^k*(1+‖y‖)^(max a b)+B*δ^k*(1+‖y‖)^(max a b) :=
      add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (le_max_left _ _))
        (mul_nonneg hA (pow_nonneg hδ.le _)))
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (le_max_right _ _))
        (mul_nonneg hB (pow_nonneg hδ.le _)))
    _ = _ := by ring

lemma OrderBound.sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → Y → ℂ) {k : ℕ}
    (h : ∀ i∈s, OrderBound (f i) k) : OrderBound (fun δ y => ∑ i∈s, f i δ y) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using OrderBound.zero k
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using (h i (Finset.mem_insert_self _ _)).add
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

lemma OrderBound.mul {f g : ℝ → Y → ℂ} {k l : ℕ}
    (hf : OrderBound f k) (hg : OrderBound g l) : OrderBound (fun δ y => f δ y*g δ y) (k+l) := by
  obtain ⟨A,hA,a,ha⟩ := hf
  obtain ⟨B,hB,b,hb⟩ := hg
  refine ⟨A*B,mul_nonneg hA hB,a+b,fun δ hδ hδ1 y => ?_⟩
  rw [norm_mul]
  calc
    _ ≤ (A*δ^k*(1+‖y‖)^a)*(B*δ^l*(1+‖y‖)^b) :=
      mul_le_mul (ha δ hδ hδ1 y) (hb δ hδ hδ1 y) (norm_nonneg _)
        (by positivity)
    _ = _ := by rw [pow_add, pow_add]; ring

lemma OrderBound.weaken {f : ℝ → Y → ℂ} {k l : ℕ} (hf : OrderBound f k) (hl : l≤k) :
    OrderBound f l := by
  obtain ⟨A,hA,n,h⟩ := hf
  refine ⟨A,hA,n,fun δ hδ hδ1 y => ?_⟩
  exact (h δ hδ hδ1 y).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hδ.le hδ1 hl) hA) (by positivity))

lemma parameter_bound (p : Polynomial MP) :
    OrderBound (fun δ y => value (atParameter p δ) y) 0 := by
  obtain ⟨A,hA,n,h⟩ := parameterGrowth p
  exact ⟨A,hA,n,fun δ hδ hδ1 y => by simpa using h δ hδ.le hδ1 y⟩

lemma power_bound (k : ℕ) : OrderBound (fun δ _ => (δ:ℂ)^k) k := by
  refine ⟨1,by norm_num,0,fun δ hδ _ _ => ?_⟩
  simp [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]

end ElasticityBoundaryOrderBound

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryParametrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Pointwise all-order cutoff bounds. These bounds feed exactly the same
weighted-mass estimate used for the smooth coefficient Taylor error. -/
noncomputable section
open Set
namespace ElasticityBoundaryCutoffBound
open ElasticityBoundaryOrderBound ElasticityBoundaryScaling

lemma bounded_scaled {f : Y → ℂ} {M : ℝ} (hM : 0≤M) (hf : ∀ y, ‖f y‖≤M) :
    OrderBound (fun δ y => f (scale δ y)) 0 := by
  exact ⟨M,hM,0,fun δ _ _ y => by simpa using hf (scale δ y)⟩

lemma compact_scaled {f : Y → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    OrderBound (fun δ y => f (scale δ y)) 0 := by
  obtain ⟨M,hM⟩ := hf.bounded_above_of_compact_support hc
  exact bounded_scaled (le_trans (norm_nonneg (f 0)) (hM 0))
    hM

/-- A bounded coefficient vanishing on a fixed neighborhood of the base
point yields every power of the true concentration parameter. -/
theorem flat_scaled {f : Y → ℂ} {M r : ℝ} (hM : 0≤M) (hr : 0 < r)
    (hf : ∀ y, ‖f y‖≤M) (hz : ∀ y, ‖y‖ < r → f y=0) (N : ℕ) :
    OrderBound (fun δ y => f (scale δ y)) N := by
  refine ⟨M/r^N,by positivity,N,fun δ hδ hδ1 y => ?_⟩
  change ‖f (scale δ y)‖ ≤ _
  by_cases hy : ‖scale δ y‖ < r
  · rw [hz _ hy, norm_zero]
    positivity
  · have hy' : r≤δ*‖y‖ := (le_of_not_gt hy).trans (scale_norm_le hδ.le hδ1 y)
    calc
      _ ≤ M := hf _
      _ = (M/r^N)*r^N := (div_mul_cancel₀ M (pow_pos hr N).ne').symm
      _ ≤ (M/r^N)*(δ*‖y‖)^N := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hr.le hy' N) (by positivity)
      _ = (M/r^N)*δ^N*‖y‖^N := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg y) (by linarith) N) (by positivity)

lemma compact_flat_scaled {f : Y → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hz : f =ᶠ[nhds (0:Y)] 0) (N : ℕ) :
    OrderBound (fun δ y => f (scale δ y)) N := by
  obtain ⟨M,hM⟩ := hf.bounded_above_of_compact_support hc
  obtain ⟨r,hr,hrf⟩ := Metric.mem_nhds_iff.mp hz
  apply flat_scaled (le_trans (norm_nonneg (f 0)) (hM 0)) hr
    hM
  intro y hy
  exact hrf (by simpa only [Metric.mem_ball, dist_zero_right] using hy)

end ElasticityBoundaryCutoffBound

end
end
section
/-! Cut off actual boundary fields. The complete product-rule residual is
retained; its derivatives are flat at the concentration point. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace ElasticityBoundaryCutoffLayer
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundarySmoothOperator ElasticityBoundaryProfile
  ElasticityBoundaryProfileBounds ElasticityBoundaryScaling ElasticityBoundaryLayerOperator
  ElasticityBoundaryWeights ElasticityBoundaryStrongLayer ElasticityBoundaryOrderBound
  ElasticityBoundaryCutoffBound

lemma smooth_dpart {f : Y → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (dpart f j) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma compact_dpart {f : Y → ℂ} (hf : HasCompactSupport f) (j : Fin 3) :
    HasCompactSupport (dpart f j) := HasCompactSupport.fderiv_apply ℝ hf _

lemma dpart_eventually_zero {f : Y → ℂ} {c : ℂ} (hf : f =ᶠ[𝓝 (0:Y)] fun _ => c)
    (j : Fin 3) : dpart f j =ᶠ[𝓝 (0:Y)] 0 := by
  filter_upwards [hf.fderiv (𝕜 := ℝ)] with y hy
  simp only [dpart, hy, fderiv_const_apply, zero_apply, Pi.zero_apply]

lemma correction_order_bound_oai (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, Continuous (a i α j β) ∧ HasCompactSupport (a i α j β))
    (hb : ∀ i j β, Continuous (b i j β) ∧ HasCompactSupport (b i j β))
    {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχ0 : χ =ᶠ[𝓝 (0:Y)] fun _ => 1) (q : Polynomial W) (N : ℕ) (i : Fin 3) :
    OrderBound (fun δ y => cutoffCorrection a b χ q δ i y) N := by
  have hd (α : Fin 3) := compact_flat_scaled (smooth_dpart hχ α).continuous
    (compact_dpart hc α) (dpart_eventually_zero hχ0 α) N
  have hdd (α β : Fin 3) := compact_flat_scaled (smooth_dpart (smooth_dpart hχ β) α).continuous
    (compact_dpart (compact_dpart hc β) α)
    (dpart_eventually_zero (dpart_eventually_zero hχ0 β) α) N
  have hA : OrderBound (fun δ y => ∑ α, ∑ j, ∑ β, a i α j β (scale δ y) *
      (dpart χ β (scale δ y)*value (atParameter (PD α (unpack j q)) δ) y+
       dpart χ α (scale δ y)*value (atParameter (PD β (unpack j q)) δ) y)) N := by
    apply OrderBound.sum
    intro α _
    apply OrderBound.sum
    intro j _
    apply OrderBound.sum
    intro β _
    simpa only [Nat.add_zero, Nat.zero_add] using
      (compact_scaled (ha i α j β).1 (ha i α j β).2).mul
        (((hd β).mul (parameter_bound (PD α (unpack j q)))).add
         ((hd α).mul (parameter_bound (PD β (unpack j q)))))
  have hB : OrderBound (fun δ y => ∑ α, ∑ j, ∑ β, a i α j β (scale δ y) *
      dpart (dpart χ β) α (scale δ y)*value (atParameter (unpack j q) δ) y) N := by
    apply OrderBound.sum
    intro α _
    apply OrderBound.sum
    intro j _
    apply OrderBound.sum
    intro β _
    simpa only [Nat.add_zero, Nat.zero_add] using
      ((compact_scaled (ha i α j β).1 (ha i α j β).2).mul (hdd α β)).mul
        (parameter_bound (unpack j q))
  have hC : OrderBound (fun δ y => ∑ j, ∑ β, b i j β (scale δ y)*dpart χ β (scale δ y)*
      value (atParameter (unpack j q) δ) y) N := by
    apply OrderBound.sum
    intro j _
    apply OrderBound.sum
    intro β _
    simpa only [Nat.add_zero, Nat.zero_add] using
      ((compact_scaled (hb i j β).1 (hb i j β).2).mul (hd β)).mul
        (parameter_bound (unpack j q))
  exact (((power_bound 2).mul hA).weaken (by omega)).add
    (((power_bound 4).mul (hB.add hC)).weaken (by omega))

end ElasticityBoundaryCutoffLayer

end
end

end OAI
end

theorem solution : type_of% @OAI.ElasticityBoundaryCutoffLayer.correction_order_bound_oai := @OAI.ElasticityBoundaryCutoffLayer.correction_order_bound_oai
