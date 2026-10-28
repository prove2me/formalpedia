-- Prove2me | solution 1 for OAI.ElasticityBoundarySmoothOperator.scaledOperator_order_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:12:43.384823+00:00
-- url     : https://prove2.me/submissions/197b0382-755c-4deb-bbfd-b7f9490d665e

import Mathlib
import Definitions.Def_OAIQ6El004

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryCalculus
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
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
-- module Solutions.OAIQ6_Elast.Elasticity_BoundarySymbols
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Coefficientwise linear differential operators in a genuine finite
parameter polynomial. Used to construct, not postulate, Taylor transport
coefficients of the physical boundary layer. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryParameter
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryProfile

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

lemma coeffMap_X_mul (T : A →ₗ[ℂ] B) (q : Polynomial A) :
    coeffMap T (Polynomial.X*q)=Polynomial.X*coeffMap T q := by
  apply Polynomial.ext
  intro n
  cases n <;> simp [coeffMap_coeff, Polynomial.coeff_X_mul]

lemma coeffMap_monomial_one_mul (T : A →ₗ[ℂ] B) (n : ℕ) (q : Polynomial A) :
    coeffMap T (Polynomial.monomial n 1*q)=Polynomial.monomial n 1*coeffMap T q := by
  rw [Polynomial.monomial_one_right_eq_X_pow, Polynomial.monomial_one_right_eq_X_pow]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_assoc, coeffMap_X_mul, ih, ← mul_assoc, ← pow_succ']

end ElasticityBoundaryParameter

end
end
section
/-! The finite-parameter differential operator of the actual Taylor-expanded
divergence tensor. No leading normal operator is stipulated. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryTensorSeries
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryProfile ElasticityBoundaryParameter ElasticityBoundaryLayerOperator

lemma pack_coeff (q : Fin 3 → Polynomial MP) (n : ℕ) (i : Fin 3) :
    (pack q).coeff n i = (q i).coeff n := by
  simp [pack, LinearMap.sum_apply, Polynomial.finsetSum_coeff, coeffMap_coeff,
    Pi.single_apply]

lemma unpack_pack (q : Fin 3 → Polynomial MP) (i : Fin 3) : unpack i (pack q)=q i := by
  apply Polynomial.ext
  intro n
  exact pack_coeff q n i

lemma unpack_operator (a : Tensor) (b : Lower) (q : Polynomial W) (i : Fin 3) :
    unpack i (operator a b q) =
      (∑ α, ∑ j, ∑ β, a i α j β * PD α (PD β (unpack j q))) +
      Polynomial.X^2 * (∑ j, ∑ β, b i j β * PD β (unpack j q)) := by
  simp only [operator, LinearMap.comp_apply, unpack_pack, LinearMap.pi_apply,
    LinearMap.add_apply, LinearMap.sum_apply, LinearMap.mulLeft_apply]

lemma unpack_monomial_mul (i : Fin 3) (n : ℕ) (q : Polynomial W) :
    unpack i (Polynomial.monomial n 1*q)=Polynomial.monomial n 1*unpack i q := by
  unfold unpack
  exact coeffMap_monomial_one_mul (A := W) (B := MP) (LinearMap.proj i) n q

end ElasticityBoundaryTensorSeries

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryLayers
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Uniform multivariable Taylor estimates for anisotropically rescaled boundary
layers. The constants are proved for actual smooth compactly supported physical
coefficient extensions; no symbol/asymptotic identification is assumed. -/
noncomputable section
open Set
open scoped BigOperators
namespace ElasticityBoundaryTaylor
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma iteratedDeriv_line {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k : ℕ) (z : E) (t : ℝ) :
    iteratedDeriv k (fun t : ℝ => f (t • z)) t =
      iteratedFDeriv ℝ k f (t • z) (fun _ => z) := by
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ k (f ∘ line z) t (fun _ => 1) = _
  rw [(line z).iteratedFDeriv_comp_right hf t (mod_cast le_top),
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [line_apply, one_smul]

lemma radialTaylor_eq_line {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (n : ℕ) (z : E) :
    radialTaylor f n z = taylorWithinEval (fun t : ℝ => f (t • z)) n (Icc 0 1) 0 1 := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => f (t • z)) :=
    hf.comp (contDiff_id.smul contDiff_const)
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
    (hg.of_le (mod_cast le_top)).contDiffAt (by simp), iteratedDeriv_line hf]
  simp

lemma radialTaylor_remainder {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (n : ℕ) {C : ℝ} (hC : ∀ x, ‖iteratedFDeriv ℝ (n+1) f x‖ ≤ C) (z : E) :
    ‖f z - radialTaylor f n z‖ ≤ C * ‖z‖^(n+1) / (n.factorial : ℝ) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => f (t • z)) :=
    hf.comp (contDiff_id.smul contDiff_const)
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖iteratedDerivWithin (n+1) (fun t : ℝ => f (t • z)) (Icc 0 1) t‖ ≤
        C * ‖z‖^(n+1) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
      (hg.of_le (mod_cast le_top)).contDiffAt ht, iteratedDeriv_line hf]
    exact (ContinuousMultilinearMap.le_opNorm _ _).trans (by
      simpa using mul_le_mul_of_nonneg_right (hC (t • z)) (pow_nonneg (norm_nonneg z) (n+1)))
  have h := taylor_mean_remainder_bound (f := fun t : ℝ => f (t • z))
    (a := 0) (b := 1) (n := n) (x := 1) (by norm_num)
    (hg.of_le (mod_cast le_top)).contDiffOn (by simp) hbound
  simpa only [radialTaylor_eq_line hf, one_smul, sub_zero, one_pow, mul_one] using h

lemma compact_iteratedFDeriv_bound {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := ((hf.of_le (show (n : WithTop ℕ∞) ≤ (⊤ : ℕ∞) from by
    exact_mod_cast le_top)).continuous_iteratedFDeriv').bounded_above_of_compact_support
      (hc.iteratedFDeriv n)
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

/-- Every smooth compactly supported coefficient has a global polynomially
weighted Taylor remainder estimate, at every finite order. -/
theorem compact_radialTaylor_remainder {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z,
      ‖f z - radialTaylor f n z‖ ≤ C * ‖z‖^(n+1) := by
  obtain ⟨C, hC, hbound⟩ := compact_iteratedFDeriv_bound hf hc (n+1)
  refine ⟨C/(n.factorial : ℝ), div_nonneg hC (Nat.cast_nonneg _), fun z => ?_⟩
  simpa only [div_mul_eq_mul_div] using radialTaylor_remainder hf n hbound z

end ElasticityBoundaryTaylor

end
end
section
/-! Literal polynomial representations of the actual Frechet Taylor jets and
of their anisotropic parameter dependence. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryTaylorPolynomial
open MvPolynomial ElasticityBoundaryTaylor ElasticityBoundaryMVCalculus ElasticityBoundaryScaling

lemma value_diagonal {n : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Y) ℂ)
    (y : Y) : value (diagonal T) y = T (fun _ => y) := by
  classical
  have hy : (fun _ : Fin n => y) = (fun _ : Fin n => ∑ i : Fin 3, y i • Pi.single i (1:ℝ)) := by
    funext k i
    simp [Pi.single_apply]
  rw [hy]
  change _ = T.toMultilinearMap (fun _ => ∑ i : Fin 3, y i • Pi.single i (1:ℝ))
  rw [T.toMultilinearMap.map_sum]
  simp only [diagonal, value, eval_sum, eval_mul, eval_C, eval_prod, eval_X]
  apply Finset.sum_congr rfl
  intro j _
  rw [T.toMultilinearMap.map_smul_univ]
  simp only [Complex.real_smul, Complex.ofReal_prod]
  change T (fun k => Pi.single (j k) 1) * _ = _ * T (fun k => Pi.single (j k) 1)
  exact mul_comm _ _

lemma value_taylor (f : Y → ℂ) (n : ℕ) (y : Y) :
    value (taylor f n) y = radialTaylor f n y := by
  simp only [taylor, value, eval_sum, radialTaylor]
  apply Finset.sum_congr rfl
  intro k _
  change value (((k.factorial : ℂ)⁻¹) • diagonal (iteratedFDeriv ℝ k f 0)) y = _
  rw [value_smul, value_diagonal]
  simp [Complex.real_smul]

lemma eval_parameterize (p : MP) (δ : ℝ) :
    (parameterize p).eval (C (δ:ℂ)) =
      MvPolynomial.aeval (fun i => C ((scaleFactor δ i : ℝ):ℂ)*X i) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [parameterize]
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, Polynomial.eval_mul, hp]
      congr 1
      simp only [parameterize, aeval_X, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      unfold weightOrder scaleFactor
      split_ifs <;> simp only [Complex.ofReal_pow, map_pow, pow_one] <;> ring

lemma value_parameterize (p : MP) (δ : ℝ) (y : Y) :
    value ((parameterize p).eval (C (δ:ℂ))) y = value p (scale δ y) := by
  rw [eval_parameterize]
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, value_add, hp, hq]
  | mul_X p i hp =>
      rw [map_mul, aeval_X, value_mul, hp, value_mul, value_C, value_X, value_mul, value_X]
      simp only [scale_apply, Complex.ofReal_mul]

lemma value_parameterized_taylor (f : Y → ℂ) (n : ℕ) (δ : ℝ) (y : Y) :
    value ((parameterize (taylor f n)).eval (C (δ:ℂ))) y =
      radialTaylor f n (scale δ y) := by rw [value_parameterize, value_taylor]

end ElasticityBoundaryTaylorPolynomial

end
end
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

lemma parameter_factor_bound (p : Polynomial MP) (k : ℕ) :
    OrderBound (fun δ y => value (atParameter (Polynomial.X^k*p) δ) y) k := by
  have h := (power_bound k).mul (parameter_bound p)
  simpa [atParameter,value] using h

/-- The actual smooth coefficient minus its literal Taylor polynomial carries
the prescribed power of delta uniformly, not only at each fixed spatial point. -/
lemma taylor_error_bound {f : Y → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (N : ℕ) :
    OrderBound (fun δ y => f (scale δ y)-
      value (atParameter (parameterize (taylor f N)) δ) y) (N+1) := by
  obtain ⟨A,hA,h⟩ := compact_radialTaylor_remainder hf hc N
  refine ⟨A,hA,N+1,fun δ hδ hδ1 y => ?_⟩
  change ‖f (scale δ y)-value ((parameterize (taylor f N)).eval (C (δ:ℂ))) y‖ ≤ _
  rw [value_parameterized_taylor]
  calc
    _ ≤ A*‖scale δ y‖^(N+1) := h _
    _ ≤ A*(δ*‖y‖)^(N+1) := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (scale_norm_le hδ.le hδ1 y) _) hA
    _ = A*δ^(N+1)*‖y‖^(N+1) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg y)
      (by linarith : ‖y‖≤1+‖y‖) _) (by positivity)

end ElasticityBoundaryOrderBound

end
end
section
/-! The genuine smooth variable-coefficient operator applied to constructed
finite boundary amplitudes. The remaining error is estimated, not discarded. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundarySmoothOperator
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundaryTaylorPolynomial ElasticityBoundaryOrderBound
  ElasticityBoundaryScaling ElasticityBoundaryLayerOperator ElasticityBoundaryWeights

lemma polynomial_operator_value (a : Tensor) (b : Lower) (q : Polynomial W)
    (δ : ℝ) (i : Fin 3) (y : Y) :
    value (atParameter (unpack i (operator a b q)) δ) y =
    (∑ α, ∑ j, ∑ β, value (atParameter (a i α j β) δ) y *
      value (atParameter (PD α (PD β (unpack j q))) δ) y) +
    (δ:ℂ)^2 * ∑ j, ∑ β, value (atParameter (b i j β) δ) y *
      value (atParameter (PD β (unpack j q)) δ) y := by
  rw [unpack_operator]
  simp [atParameter, value, Polynomial.eval_finsetSum]

lemma scaledOperator_decomposition (a : SmoothTensor) (b : SmoothLower) (q : Polynomial W)
    (N : ℕ) (δ : ℝ) (i : Fin 3) (y : Y) :
    scaledOperator a b q δ i y =
      value (atParameter (unpack i (operator (tensorTaylor a N) (lowerTaylor b N) q)) δ) y +
      scaledError a b q N δ i y := by
  rw [polynomial_operator_value]
  simp only [scaledOperator, scaledError, sub_mul, Finset.sum_sub_distrib, mul_sub]
  ring

lemma error_order_bound (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, ContDiff ℝ (⊤ : ℕ∞) (a i α j β) ∧ HasCompactSupport (a i α j β))
    (hb : ∀ i j β, ContDiff ℝ (⊤ : ℕ∞) (b i j β) ∧ HasCompactSupport (b i j β))
    (q : Polynomial W) (N : ℕ) (i : Fin 3) :
    OrderBound (fun δ y => scaledError a b q N δ i y) (N+1) := by
  have hA : OrderBound (fun δ y => ∑ α, ∑ j, ∑ β, (a i α j β (scale δ y)-
      value (atParameter (tensorTaylor a N i α j β) δ) y) *
      value (atParameter (PD α (PD β (unpack j q))) δ) y) (N+1) := by
    apply OrderBound.sum
    intro α _
    apply OrderBound.sum
    intro j _
    apply OrderBound.sum
    intro β _
    simpa only [Nat.add_zero, tensorTaylor] using
      (taylor_error_bound (ha i α j β).1 (ha i α j β).2 N).mul
        (parameter_bound (PD α (PD β (unpack j q))))
  have hB : OrderBound (fun δ y => ∑ j, ∑ β, (b i j β (scale δ y)-
      value (atParameter (lowerTaylor b N i j β) δ) y) *
      value (atParameter (PD β (unpack j q)) δ) y) (N+1) := by
    apply OrderBound.sum
    intro j _
    apply OrderBound.sum
    intro β _
    simpa only [Nat.add_zero, lowerTaylor] using
      (taylor_error_bound (hb i j β).1 (hb i j β).2 N).mul
        (parameter_bound (PD β (unpack j q)))
  exact hA.add (((power_bound 2).mul hB).weaken (by omega))

lemma unpack_X_pow_mul (i : Fin 3) (k : ℕ) (q : Polynomial W) :
    unpack i (Polynomial.X^k*q)=Polynomial.X^k*unpack i q := by
  simpa only [Polynomial.monomial_one_right_eq_X_pow] using unpack_monomial_mul i k q

lemma scaledOperator_order_bound_oai (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, ContDiff ℝ (⊤ : ℕ∞) (a i α j β) ∧ HasCompactSupport (a i α j β))
    (hb : ∀ i j β, ContDiff ℝ (⊤ : ℕ∞) (b i j β) ∧ HasCompactSupport (b i j β))
    (q R : Polynomial W) (N : ℕ)
    (hR : operator (tensorTaylor a N) (lowerTaylor b N) q=Polynomial.X^(N+1)*R)
    (i : Fin 3) : OrderBound (fun δ y => scaledOperator a b q δ i y) (N+1) := by
  simp_rw [scaledOperator_decomposition a b q N, hR, unpack_X_pow_mul]
  exact (parameter_factor_bound (unpack i R) (N+1)).add (error_order_bound a b ha hb q N i)

end ElasticityBoundarySmoothOperator

end
end

end OAI
end

theorem solution : type_of% @OAI.ElasticityBoundarySmoothOperator.scaledOperator_order_bound_oai := @OAI.ElasticityBoundarySmoothOperator.scaledOperator_order_bound_oai
