-- Prove2me | solution 1 for OAI.ElasticityBoundaryPacket.pair_separates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:52:50.696882+00:00
-- url     : https://prove2.me/submissions/69e42513-f97b-4b3b-825d-e9b3faf08698

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
/-! Integrable polynomial majorants for the physical anisotropic boundary-layer
profiles. The decay and all moments are proved, not assumed symbol bounds. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryWeights

lemma factor_nonneg (b : ℝ) (i : Fin 3) (t : ℝ) : 0 ≤ factor b i t := by
  unfold factor
  split_ifs
  · exact indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
  · exact (Real.exp_pos _).le

lemma weight_nonneg (b : ℝ) (y : Y) : 0 ≤ weight b y :=
  Finset.prod_nonneg (fun i _ => factor_nonneg b i (y i))

lemma measurable_factor (b : ℝ) (i : Fin 3) : Measurable (factor b i) := by
  unfold factor
  by_cases hi : i = 2
  · simp only [hi, ite_true]
    exact (by fun_prop : Measurable (fun s : ℝ => Real.exp (-b*s))).indicator measurableSet_Ioi
  · simp only [hi, ite_false]
    fun_prop

lemma measurable_weight (b : ℝ) : Measurable (weight b) := by
  unfold weight
  exact Finset.measurable_prod _ (fun i _ => (measurable_factor b i).comp (measurable_pi_apply i))

lemma integrable_factor_pow {b : ℝ} (hb : 0 < b) (i : Fin 3) (n : ℕ) :
    Integrable (fun t : ℝ => |t|^n * factor b i t) := by
  by_cases hi : i = 2
  · have h : IntegrableOn (fun t : ℝ => t^n * Real.exp (-b*t)) (Ioi 0) := by
      simpa only [Real.rpow_natCast, Real.rpow_one] using
        (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1)
          (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) hb)
    have h' : (fun t : ℝ => |t|^n * factor b i t) =
        (Ioi (0 : ℝ)).indicator (fun t => t^n * Real.exp (-b*t)) := by
      funext t
      by_cases ht : t ∈ Ioi (0 : ℝ)
      · simp [factor, hi, ht, abs_of_pos (mem_Ioi.mp ht)]
      · simp [factor, hi, ht]
    rw [h']
    exact h.integrable_indicator measurableSet_Ioi
  · have h : Integrable (fun t : ℝ => t^n * Real.exp (-b*t^2)) := by
      simpa only [Real.rpow_natCast] using
        (integrable_rpow_mul_exp_neg_mul_sq (s := (n : ℝ)) hb (by have := Nat.cast_nonneg (α := ℝ) n; linarith))
    simpa only [factor, hi, ite_false, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_pos (Real.exp_pos _)] using h.norm

lemma integrable_factor {b : ℝ} (hb : 0 < b) (i : Fin 3) : Integrable (factor b i) := by
  simpa using integrable_factor_pow hb i 0

lemma integrable_weight {b : ℝ} (hb : 0 < b) : Integrable (weight b) :=
  Integrable.fintype_prod (fun i => integrable_factor hb i)

lemma integrable_coordinate_moment {b : ℝ} (hb : 0 < b) (i : Fin 3) (n : ℕ) :
    Integrable (fun y : Y => |y i|^n * weight b y) := by
  let g : Fin 3 → ℝ → ℝ := fun j t => (if i=j then |t|^n else 1) * factor b j t
  have hg (j : Fin 3) : Integrable (g j) := by
    by_cases hij : i=j
    · simpa [g, hij] using integrable_factor_pow hb j n
    · simpa [g, hij] using integrable_factor hb j
  have h := Integrable.fintype_prod hg
  simp only [g, Finset.prod_mul_distrib, Finset.prod_ite_eq, Finset.mem_univ, ite_true] at h
  exact h

lemma norm_pow_le_sum (y : Y) (n : ℕ) : ‖y‖^n ≤ ∑ i, |y i|^n := by
  obtain ⟨⟨i, hi⟩, _⟩ := IsGreatest.pi_norm y
  rw [← hi]
  exact Finset.single_le_sum (fun j _ => pow_nonneg (abs_nonneg (y j)) n) (Finset.mem_univ i)

/-- Every finite radial moment of the Gaussian-tangential, exponential-normal
profile is integrable over the full coordinate space (zero for t≤0). -/
theorem integrable_norm_moment {b : ℝ} (hb : 0 < b) (n : ℕ) :
    Integrable (fun y : Y => ‖y‖^n * weight b y) := by
  have h := integrable_finsetSum Finset.univ (fun i _ => integrable_coordinate_moment hb i n)
  apply h.mono' ((continuous_norm.measurable.pow_const n).mul (measurable_weight b)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y => by
    change ‖‖y‖^n * weight b y‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg y) n) (weight_nonneg b y)),
      ← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (norm_pow_le_sum y n) (weight_nonneg b y))

end ElasticityBoundaryWeights

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
/-!
Polynomial-amplitude inversion for the frozen physical half-space operator.
This is the arbitrary-order normal ODE used in a boundary-layer construction:
every exp(-t)-polynomial forcing has an exp(-t)-polynomial solution with
zero boundary value. No pseudodifferential solvability is assumed.
-/
noncomputable section
open Polynomial
namespace ElasticityBoundarySymbol

lemma laplaceAmplitude_apply (p : P) :
    laplaceAmplitude p=derivative (derivative p)-(2 : ℂ) • derivative p := by
  simp [laplaceAmplitude, shiftedDerivative]

end ElasticityBoundarySymbol

end
end
section
/-! Zero-Dirichlet inversion, with a literal exponential-polynomial ODE
interpretation. This is the normal component of the boundary quasimode
recursion, not a replacement for variable-coefficient boundary localization. -/
noncomputable section
open Polynomial
namespace ElasticityBoundarySymbol

lemma homogeneousPolynomial_physical (l m : ℂ) (hp : l+3*m≠0) (f : F) :
    polynomialPhysical l m (homogeneousPolynomial l m f) = 0 := by
  have hp' : m*3+l≠0 := by convert hp using 1; ring
  have hp'' : l+m*3≠0 := by simpa only [mul_comm] using hp
  funext i
  apply Polynomial.funext
  intro z
  fin_cases i <;>
    simp [polynomialPhysical, homogeneousPolynomial, laplaceAmplitude_apply,
      shiftedDerivative_apply, slope, smul_eq_C_mul]
  all_goals field_simp [hp, hp']
  all_goals ring_nf
  all_goals simp only [Complex.I_sq]
  all_goals field_simp [hp'']
  all_goals ring

end ElasticityBoundarySymbol

end
end
section
/-! The normal inverse on literal multivariable polynomial amplitudes.  No
identification of formal symbols with physical derivatives is assumed: the
normal operator here consists of the actual formal partial derivatives, whose
evaluations agree with the corresponding Fréchet derivatives. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryMVNormal
open MvPolynomial ElasticityBoundarySymbol ElasticityBoundaryMVCalculus

lemma normal_apply (l m : ℂ) (p : W) : normal l m p =
    ![m • lap (p 0) - (l+m) • p 0 + (Complex.I*(l+m)) • shift (p 2),
      m • lap (p 1), (Complex.I*(l+m)) • shift (p 0) +
        (l+2*m) • lap (p 2) + (l+m) • p 2] := by funext i; fin_cases i <;> rfl

lemma d_lift (p : P) : d (lift p)=lift (Polynomial.derivative p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n c =>
      simp only [d_apply, lift, Polynomial.aeval_monomial, algebraMap_eq,
        Polynomial.derivative_monomial, pderiv_C_mul, pderiv_pow, pderiv_X_self, mul_one,
        map_mul, map_natCast]
      ring

lemma pderiv_lift (p : P) : pderiv 2 (lift p)=lift (Polynomial.derivative p) := d_lift p

lemma lap_lift (p : P) : lap (lift p)=lift (laplaceAmplitude p) := by
  change d (d (lift p)-(2:ℂ) • lift p)=_
  rw [map_sub, map_smul, d_lift, d_lift, laplaceAmplitude_apply, map_sub, map_smul]

lemma normal_lift (l m : ℂ) (p : Fin 3 → P) :
    normal l m (fun i => lift (p i)) = fun i => lift (polynomialPhysical l m p i) := by
  funext i
  fin_cases i <;>
    simp [normal_apply, polynomialPhysical, lap_lift, pderiv_lift]

end ElasticityBoundaryMVNormal

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
/-! Honest L2 bounds and exact change of variables for physical boundary layers. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryProfileBounds
open ElasticityBoundaryMVCalculus ElasticityBoundaryScaling ElasticityBoundaryWeights
  ElasticityBoundaryProfile

lemma one_add_pow_le {r : ℝ} (hr : 0 ≤ r) (n : ℕ) : (1+r)^n ≤ 2^n*(1+r^n) := by
  by_cases h : r≤1
  · calc
      _ ≤ (2:ℝ)^n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ ≤ _ := by nlinarith [pow_nonneg hr n, pow_nonneg (show (0:ℝ)≤2 by norm_num) n]
  · have h1 : 1 ≤ r := le_of_not_ge h
    calc
      _ ≤ (2*r)^n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = (2:ℝ)^n*r^n := mul_pow _ _ _
      _ ≤ _ := by nlinarith [pow_nonneg (show (0:ℝ)≤2 by norm_num) n]

end ElasticityBoundaryProfileBounds

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

end ElasticityBoundaryOrderBound

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryEnergy
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Elasticity
/-! The complex physical variational density is exactly the Hermitian
contraction of the literal isotropic elasticity tensor. -/
open scoped BigOperators
open ElasticityBoundaryLayerOperator

lemma tensorDensity_isotropic (l m : ℂ) (P Q : CMatrix) :
    tensorDensity (elasticityTensor l m) P Q=sesquiDensity l m P Q := by
  unfold tensorDensity elasticityTensor
  simp only [add_mul,mul_add,Finset.sum_add_distrib,mul_ite,ite_mul,mul_one,mul_zero,
    zero_mul,Finset.sum_ite_irrel,Fintype.sum_ite_eq,Finset.sum_const_zero]
  simp only [sesquiDensity,Fin.sum_univ_three,star_add]
  ring

end Elasticity
namespace ElasticityBoundaryLimit
/-! Genuine Gaussian boundary scaling limits for the finite corrected
amplitudes. Dominated convergence is proved from the uniform polynomial
majorants and the actual half-space weight. -/
open Set Filter MeasureTheory
open scoped Topology BigOperators
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryScaling ElasticityBoundaryWeights ElasticityBoundaryOrderBound
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundaryCutoffParametrix
  ElasticityBoundaryProfileBounds ElasticityBoundaryCutoffLayer

lemma OrderBound.conj {F : ℝ → Y → ℂ} {k : ℕ} (hF : OrderBound F k) :
    OrderBound (fun δ y => star (F δ y)) k := by
  obtain ⟨A,hA,n,h⟩ := hF
  exact ⟨A,hA,n,fun δ hδ h1 y => by simpa only [norm_star] using h δ hδ h1 y⟩

end ElasticityBoundaryLimit
namespace ElasticityBoundaryEnergyLimit
/-! Actual normalized mixed energy limits of the corrected, cut-off boundary
layers. The coefficient has its genuine normal factor and arbitrary compact
smooth remainder; all Jacobian and physical-derivative powers are exact. -/
open Set Filter MeasureTheory
open scoped Topology BigOperators
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryScaling ElasticityBoundaryWeights ElasticityBoundaryOrderBound
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundaryCutoffParametrix ElasticityBoundaryLimit
  ElasticityBoundaryProfileBounds ElasticityBoundaryCutoffLayer ElasticityBoundaryProfile
  ElasticityBoundaryCutoffBound

lemma normal_power_bound (n : ℕ) : OrderBound (fun (_ : ℝ) (y : Y) => (y 2:ℂ)^n) 0 := by
  refine ⟨1,by norm_num,n,fun δ _ _ y => ?_⟩
  simp only [pow_zero,mul_one,one_mul,norm_pow,Complex.norm_real]
  exact pow_le_pow_left₀ (norm_nonneg _) ((norm_le_pi_norm y 2).trans (by linarith [norm_nonneg y])) n

end ElasticityBoundaryEnergyLimit

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryValues
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Strictly positive Gaussian-normal moments, without relying on a numerical
constant or an unproved nondegeneracy of the boundary limit. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryWeights

lemma weight_zero_of_nonpos (b : ℝ) {y : Y} (hy : y 2≤0) : weight b y=0 := by
  simp [weight,Fin.prod_univ_three,factor,not_lt.mpr hy]

lemma weight_pos (b : ℝ) {y : Y} (hy : 0<y 2) : 0<weight b y := by
  simp [weight,Fin.prod_univ_three,factor,hy,Real.exp_pos]

lemma normal_moment_integrable (n : ℕ) : Integrable (fun y : Y => (y 2)^n*weight 2 y) := by
  apply (integrable_coordinate_moment (by norm_num : (0:ℝ)<2) 2 n).congr
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only
    by_cases hy : 0<y 2
    · rw [abs_of_pos hy]
    · rw [weight_zero_of_nonpos 2 (le_of_not_gt hy),mul_zero,mul_zero])

lemma normalMoment_pos (n : ℕ) : 0<normalMoment n := by
  have hn (y : Y) : 0≤(y 2)^n*weight 2 y := by
    by_cases hy : 0<y 2
    · exact mul_nonneg (pow_nonneg hy.le n) (weight_nonneg 2 y)
    · rw [weight_zero_of_nonpos 2 (le_of_not_gt hy),mul_zero]
  apply (integral_pos_iff_support_of_nonneg hn (normal_moment_integrable n)).mpr
  have ho : IsOpen ({y : Y | 0<y 2}) := isOpen_lt continuous_const (continuous_apply 2)
  have hne : ({y : Y | 0<y 2}).Nonempty := ⟨fun _ => 1,by norm_num⟩
  exact (ho.measure_pos volume hne).trans_le (measure_mono (fun y hy =>
    (mul_pos (pow_pos hy _) (weight_pos 2 hy)).ne'))

lemma normalMoment_complex (n : ℕ) :
    (∫ y : Y, weight 2 y • (y 2:ℂ)^n)=(normalMoment n:ℂ) := by
  simp only [Complex.real_smul,← Complex.ofReal_pow,← Complex.ofReal_mul]
  rw [integral_complex_ofReal]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => mul_comm _ _)

end ElasticityBoundaryWeights

end
end
section
/-! The finite leading packet pairing is precisely the integrated Hermitian
isotropic density, against a strictly positive normal Gaussian moment. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundaryMVNormal ElasticityBoundaryMVCalculus
  ElasticityBoundaryWeights ElasticityBoundaryOrderBound ElasticityBoundaryProfileBounds
  ElasticityBoundaryLimit ElasticityBoundaryParameter ElasticityBoundaryEnergyLimit
  ElasticityBoundaryCutoffBound

lemma polynomial_bound (p : MP) : OrderBound (fun _ y => value p y) 0 := by
  obtain ⟨A,hA,n,h⟩ := polynomialGrowth p
  exact ⟨A,hA,n,fun _ _ _ y => by simpa using h y⟩

lemma weighted_integrable {f : Y → ℂ} (hf : Continuous f)
    (hF : OrderBound (fun _ => f) 0) {b : ℝ} (hb : 0<b) :
    Integrable (fun y => weight b y • f y) := by
  obtain ⟨A,hA,n,hB⟩ := hF
  let g : Y → ℝ := fun y => (A*2^n)*(weight b y+‖y‖^n*weight b y)
  have hg : Integrable g := ((integrable_weight hb).add (integrable_norm_moment hb n)).const_mul _
  apply hg.mono' ((measurable_weight b).aestronglyMeasurable.smul hf.aestronglyMeasurable)
  exact Eventually.of_forall (fun y => by
    change ‖weight b y • f y‖≤g y
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (weight_nonneg b y)]
    have h := hB 1 (by norm_num) le_rfl y
    simp only [pow_zero,mul_one] at h
    calc
      _ ≤ weight b y*(A*(1+‖y‖)^n) := mul_le_mul_of_nonneg_left h (weight_nonneg b y)
      _ ≤ weight b y*(A*(2^n*(1+‖y‖^n))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (one_add_pow_le (norm_nonneg y) n) hA)
          (weight_nonneg b y)
      _ = g y := by dsimp [g]; ring)

lemma frozen_integrable (n : ℕ) (c : ℂ) (p q : MP) :
    Integrable (fun y : Y => weight 2 y • ((y 2:ℂ)^n*c*value p y*star (value q y))) := by
  apply weighted_integrable
  · exact ((((Complex.continuous_ofReal.comp (continuous_apply 2)).pow n).mul continuous_const).mul
      (smooth_value p).continuous).mul (smooth_value q).continuous.star
  · have hc : OrderBound (fun (_ : ℝ) (_ : Y) => c) 0 := by
      exact ⟨‖c‖,norm_nonneg _,0,fun _ _ _ _ => by simp⟩
    exact (((normal_power_bound n).mul hc).mul (polynomial_bound p)).mul (OrderBound.conj (polynomial_bound q))
  · norm_num

lemma frozenPair_integral (n : ℕ) (a : I → I → I → I → ℂ) (p q : W) :
    frozenPair n a p q=∫ y : Y, weight 2 y • ((y 2:ℂ)^n*
      tensorDensity a (fun i α => value (E₀ α (p i)) y) (fun j β => value (E₀ β (q j)) y)) := by
  have hi (i α j β : I) := frozen_integrable n (a i α j β) (E₀ α (p i)) (E₀ β (q j))
  have hfun (y : Y) : weight 2 y • ((y 2:ℂ)^n*
      tensorDensity a (fun i α => value (E₀ α (p i)) y) (fun j β => value (E₀ β (q j)) y))=
      ∑ i, ∑ α, ∑ j, ∑ β, weight 2 y • ((y 2:ℂ)^n*a i α j β*
        value (E₀ α (p i)) y*star (value (E₀ β (q j)) y)) := by
    simp only [tensorDensity,Finset.mul_sum,Finset.smul_sum,mul_assoc]
  simp_rw [hfun]
  unfold frozenPair
  symm
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun α _ =>
    integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun β _ => hi i α j β))))]
  apply Finset.sum_congr rfl; intro i _
  rw [integral_finsetSum _ (fun α _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun β _ => hi i α j β)))]
  apply Finset.sum_congr rfl; intro α _
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun β _ => hi i α j β))]
  apply Finset.sum_congr rfl; intro j _
  exact integral_finsetSum _ (fun β _ => hi i α j β)

lemma frozenPair_constant (n : ℕ) (a : I → I → I → I → ℂ) (p q : W) (c : ℂ)
    (h : ∀ y : Y, tensorDensity a (fun i α => value (E₀ α (p i)) y)
      (fun j β => value (E₀ β (q j)) y)=c) :
    frozenPair n a p q=(normalMoment n:ℂ)*c := by
  rw [frozenPair_integral]
  simp only [h,Complex.real_smul,← mul_assoc]
  rw [integral_mul_const]
  congr 1
  exact normalMoment_complex n

end ElasticityBoundaryPacket

end
end
section
/-! Exact transverse and longitudinal frozen physical tests. Both are genuine
solutions of the normal isotropic elasticity equation. -/
noncomputable section
open scoped BigOperators Matrix
namespace ElasticityBoundaryLeading
open Elasticity ElasticityBoundarySymbol ElasticityBoundaryMVNormal
  ElasticityBoundaryMVCalculus ElasticityBoundaryParameter ElasticityBoundaryLayerOperator

lemma leading_normal (l m : ℂ) (hp : l+3*m≠0) (f : F) : normal l m (leading l m f)=0 := by
  change normal l m (fun i => lift (homogeneousPolynomial l m f i))=0
  rw [normal_lift,homogeneousPolynomial_physical l m hp]
  ext i
  simp

lemma leading_apply (l m : ℂ) (f : F) (i : I) :
    leading l m f i=MvPolynomial.C (f i)+MvPolynomial.X 2*MvPolynomial.C (ElasticityBoundarySymbol.slope l m f i) := by
  simp only [leading,homogeneousPolynomial,map_add,map_mul,lift_C,lift_X]

lemma grad_leading (l m : ℂ) (f : F) (y : Y) (i α : I) :
    grad (leading l m f) y i α=
      if α=0 then Complex.I*(f i+(y 2:ℂ)*ElasticityBoundarySymbol.slope l m f i)
      else if α=1 then 0 else ElasticityBoundarySymbol.slope l m f i-f i-(y 2:ℂ)*ElasticityBoundarySymbol.slope l m f i := by
  rw [grad,leading_apply]
  fin_cases α <;> simp [E₀,value_smul] <;> ring

lemma tensorDensity_factor (D : ℂ) (a : I → I → I → I → ℂ) (P Q : CMatrix) :
    tensorDensity (fun i α j β => D*a i α j β) P Q=D*tensorDensity a P Q := by
  simp only [tensorDensity,Finset.mul_sum,mul_assoc]

lemma transverse_density (l₁ m₁ l₂ m₂ L M : ℂ) (y : Y) :
    tensorDensity (elasticityTensor L M)
      (grad (leading l₁ m₁ ![0,1,0]) y) (grad (leading l₂ m₂ ![0,1,0]) y)=2*M := by
  rw [tensorDensity_isotropic]
  simp only [sesquiDensity,Fin.sum_univ_three,grad_leading]
  simp [ElasticityBoundarySymbol.slope]
  ring

lemma longitudinal_trace (l m : ℂ) (hp : l+3*m≠0) (y : Y) :
    (∑ i, grad (leading l m ![1,0,0]) y i i)=Complex.I*(2*m/(l+3*m)) := by
  simp [Fin.sum_univ_three,grad_leading,ElasticityBoundarySymbol.slope]
  have hp' : l+m*3≠0 := by simpa only [mul_comm] using hp
  field_simp [hp,hp']
  ring

lemma longitudinal_density (l₁ m₁ l₂ m₂ : ℂ) (hp₁ : l₁+3*m₁≠0) (hp₂ : l₂+3*m₂≠0)
    (L : ℂ) (y : Y) :
    tensorDensity (elasticityTensor L 0)
      (grad (leading l₁ m₁ ![1,0,0]) y) (grad (leading l₂ m₂ ![1,0,0]) y)=
      L*(Complex.I*(2*m₁/(l₁+3*m₁)))*star (Complex.I*(2*m₂/(l₂+3*m₂))) := by
  rw [tensorDensity_isotropic]
  simp only [sesquiDensity,zero_div,zero_mul,add_zero,longitudinal_trace l₁ m₁ hp₁,
    longitudinal_trace l₂ m₂ hp₂]

lemma longitudinal_trace_ne (l m : ℂ) (hm : m≠0) (hp : l+3*m≠0) :
    Complex.I*(2*m/(l+3*m))≠0 :=
  mul_ne_zero Complex.I_ne_zero (div_ne_zero (mul_ne_zero (by norm_num) hm) hp)

end ElasticityBoundaryLeading

end
end
section
/-! Nondegenerate extraction of the two genuine isotropic scalar coefficients.
Tests are the actual frozen normal solutions, not arbitrary symbol data. -/
noncomputable section
open scoped Matrix BigOperators
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundaryLeading ElasticityBoundaryWeights
  ElasticityBoundarySymbol ElasticityBoundaryMVNormal ElasticityBoundaryParameter ElasticityBoundaryLayerOperator

lemma pair_separates_oai (n : ℕ) (l₁ m₁ l₂ m₂ D L M : ℂ)
    (hm₁ : m₁≠0) (hm₂ : m₂≠0) (hp₁ : l₁+3*m₁≠0) (hp₂ : l₂+3*m₂≠0)
    (hD : D≠0)
    (h : ∀ p q : W, normal l₁ m₁ p=0 → normal l₂ m₂ q=0 →
      frozenPair n (fun i α j β => D*elasticityTensor L M i α j β) p q=0) : L=0 ∧ M=0 := by
  have hmoment : (normalMoment n:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (normalMoment_pos n).ne'
  have hM : M=0 := by
    have hh := h (leading l₁ m₁ ![0,1,0]) (leading l₂ m₂ ![0,1,0])
      (leading_normal l₁ m₁ hp₁ _) (leading_normal l₂ m₂ hp₂ _)
    have he := frozenPair_constant n (fun i α j β => D*elasticityTensor L M i α j β)
      (leading l₁ m₁ ![0,1,0]) (leading l₂ m₂ ![0,1,0]) (D*(2*M)) (fun y => by
        change tensorDensity _ (grad _ y) (grad _ y)=_
        rw [tensorDensity_factor,transverse_density])
    rw [he] at hh
    exact (mul_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hmoment)).resolve_left hD)).resolve_left
      (by norm_num)
  refine ⟨?_,hM⟩
  have hh := h (leading l₁ m₁ ![1,0,0]) (leading l₂ m₂ ![1,0,0])
    (leading_normal l₁ m₁ hp₁ _) (leading_normal l₂ m₂ hp₂ _)
  have he := frozenPair_constant n (fun i α j β => D*elasticityTensor L M i α j β)
    (leading l₁ m₁ ![1,0,0]) (leading l₂ m₂ ![1,0,0])
    (D*(L*(Complex.I*(2*m₁/(l₁+3*m₁)))*star (Complex.I*(2*m₂/(l₂+3*m₂))))) (fun y => by
      change tensorDensity _ (grad _ y) (grad _ y)=_
      rw [hM,tensorDensity_factor,longitudinal_density l₁ m₁ l₂ m₂ hp₁ hp₂])
  rw [he] at hh
  have ht₁ := longitudinal_trace_ne l₁ m₁ hm₁ hp₁
  have ht₂ : star (Complex.I*(2*m₂/(l₂+3*m₂)))≠0 := star_ne_zero.mpr
    (longitudinal_trace_ne l₂ m₂ hm₂ hp₂)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp
    ((mul_eq_zero.mp hh).resolve_left hmoment)).resolve_left hD)).resolve_right ht₂)).resolve_right ht₁

end ElasticityBoundaryPacket

end
end

end OAI
end

theorem solution : type_of% @OAI.ElasticityBoundaryPacket.pair_separates_oai := @OAI.ElasticityBoundaryPacket.pair_separates_oai
