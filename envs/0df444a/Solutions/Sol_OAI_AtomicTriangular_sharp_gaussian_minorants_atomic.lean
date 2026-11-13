-- Prove2me | solution 1 for OAI.AtomicTriangular.sharp_gaussian_minorants_atomic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:15:06.217108+00:00
-- url     : https://prove2.me/submissions/6dbe927d-d98f-4717-84cb-1d0c799a86b4

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X010
import Definitions.Def_OAIQ257X029
import Theorems.Thm_OAI_AtomicTriangular_Construction_actualFiniteError_norm_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_actualTail_norm_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_minusResidualTable_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_plusResidualTable_mem_x

section
-- module Solutions.OAIQ250_TR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Auxiliary_MatrixNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.MatrixBounds

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

lemma matNorm_le [Nonempty n] {A : Matrix m n ℝ} {c : ℝ}
    (h : ∀ j, colNorm A j ≤ c) : matNorm A ≤ c := by
  classical
  exact (Finset.sup'_le_iff _ _).mpr (fun j _ => h j)

end AtomicTriangular.MatrixBounds

namespace AtomicTriangular.MatrixBounds
open Matrix
variable {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
omit [Nonempty n] [DecidableEq n] in
lemma vecNorm_nonneg (v : n → ℝ) : 0 ≤ vecNorm v := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
omit [Nonempty n] [DecidableEq n] in
lemma vecNorm_zero_iff (v : n → ℝ) : vecNorm v = 0 ↔ v = 0 := by
  constructor
  · intro h
    ext i
    have hi : |v i| ≤ vecNorm v := (Finset.single_le_sum (f := fun j => |v j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
    rw [h] at hi
    exact abs_eq_zero.mp (le_antisymm hi (abs_nonneg _))
  · rintro rfl; simp [vecNorm]
omit [DecidableEq n] in
lemma matrix_vecNorm (A : Matrix n n ℝ) (v : n → ℝ) :
    vecNorm (A.mulVec v) ≤ matNorm A * vecNorm v := by
  calc
    _ ≤ ∑ i, ∑ j, |A i j * v j| := Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ j, colNorm A j * |v j| := by
      rw [Finset.sum_comm]
      simp only [abs_mul,Finset.sum_mul,colNorm]
    _ ≤ ∑ j, matNorm A * |v j| := Finset.sum_le_sum
      (fun j _ => mul_le_mul_of_nonneg_right (colNorm_le_matNorm A j) (abs_nonneg _))
    _ = _ := by simp only [vecNorm,Finset.mul_sum]
lemma isUnit_of_residual (A C : Matrix n n ℝ) (he : matNorm (C*A-1) < 1) : IsUnit A := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hh
  have hzero : A.mulVec (v-w) = 0 := by rw [mulVec_sub,hh,sub_self]
  have hres : (C*A-1).mulVec (v-w) = -(v-w) := by
    rw [Matrix.sub_mulVec,← Matrix.mulVec_mulVec, hzero,Matrix.mulVec_zero,Matrix.one_mulVec,zero_sub]
  have hb := matrix_vecNorm (C*A-1) (v-w)
  rw [hres] at hb
  have hneg : vecNorm (-(v-w)) = vecNorm (v-w) := by simp only [vecNorm, Pi.neg_apply, abs_neg]
  rw [hneg] at hb
  have hz := vecNorm_nonneg (v-w)
  have hv : vecNorm (v-w) = 0 := by nlinarith
  exact sub_eq_zero.mp ((vecNorm_zero_iff _).mp hv)
end AtomicTriangular.MatrixBounds
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_WaveIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex Polynomial

lemma hasDerivAt_P (s : ℂ) : HasDerivAt P (waveDerivative 1 s) s := by
  simpa only [waveDerivative_zero] using hasDerivAt_waveDerivative 0 s

lemma fourier_node_cancel (n : Node) : waveDerivative 0 n.val = 0 := by
  rw [waveDerivative_zero, P_node]

lemma fourier_node_deriv_cancel (n : Node) : waveDerivative 1 n.val = 0 := by
  rw [← (hasDerivAt_P n.val).deriv, deriv_P_node]

end AtomicTriangular.Construction

namespace AtomicTriangular.Interval

noncomputable section
open scoped BigOperators

lemma RI.mem_abs {a : RI} {x : ℝ} (hx : a.Mem x) : a.abs.Mem |x| := by
  rcases hx with ⟨hl,hu⟩
  change (↑(max 0 (max a.lo (-a.hi))) : ℝ) ≤ (scale:ℝ)*|x| ∧
    (scale:ℝ)*|x| ≤ ↑(max a.hi (-a.lo))
  push_cast
  rw [← abs_of_pos scale_pos, ← abs_mul]
  constructor
  · exact max_le (abs_nonneg _) (max_le (hl.trans (le_abs_self _)) (by simpa using (neg_le_neg hu).trans (neg_le_abs _)))
  · exact (abs_le.mpr ⟨by linarith [le_max_right (a.hi:ℝ) (-(a.lo:ℝ))], hu.trans (le_max_left _ _)⟩)

end
end AtomicTriangular.Interval

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators Topology
open Finset Filter

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators FourierTransform
namespace AtomicTriangular.Construction
open Complex

lemma spectralParameter_pos {k : ℝ} (hk : 0 < k) (t : ℝ) : 0 < (spectralParameter k t).re := by
  simpa [spectralParameter] using mul_pos b_pos hk
lemma spectralParameter_inv {k : ℝ} (hk : 0 < k) (t : ℝ) :
    (spectralParameter k t)⁻¹ = lambda k t := by
  have hb : (b:ℂ) ≠ 0 := by exact_mod_cast b_pos.ne'
  have hd : (waveDen k t:ℂ) ≠ 0 := by exact_mod_cast (waveDen_pos hk t).ne'
  apply inv_eq_of_mul_eq_one_right
  unfold lambda spectralParameter
  push_cast
  field_simp
  simp only [waveDen]
  push_cast
  ring_nf
  simp [I_sq]

lemma spectral_exponent {k : ℝ} (hk : 0 < k) (v t : ℝ) (x : Plane) :
    -(Real.pi:ℂ)*(‖x‖:ℂ)^2/spectralParameter k t =
      -(Real.pi:ℂ)*v*(radial x:ℂ)+I*Real.pi*zeta k v t*(radial x:ℂ) := by
  have hb : (b:ℂ) ≠ 0 := by exact_mod_cast b_pos.ne'
  have hd : (waveDen k t:ℂ) ≠ 0 := by exact_mod_cast (waveDen_pos hk t).ne'
  have hbs := congrArg (fun r : ℝ => (r:ℂ)) b_sq
  push_cast at hbs
  rw [div_eq_mul_inv,spectralParameter_inv hk]
  unfold lambda zeta Xwave radial
  push_cast
  field_simp
  ring_nf
  simp only [I_sq]
  rw [hbs]
  ring

lemma transformed_spectral_wave {k : ℝ} (hk : 0 < k) (v t : ℝ) (w : Plane) :
    𝓕 (fun x : Plane => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*
      exp (I*Real.pi*t*(radial x:ℂ))) w =
      exp (-(Real.pi:ℂ)*v*(radial w:ℂ))*transformedWave k v t (radial w) := by
  have hfun : (fun x : Plane => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*
      exp (I*Real.pi*t*(radial x:ℂ))) =
      (fun x : Plane => exp (-(Real.pi:ℂ)*spectralParameter k t*‖x‖^2)) := by
    funext x
    rw [← exp_add]
    congr 1
    unfold spectralParameter radial
    push_cast
    ring
  rw [hfun,complex_gaussian_transform _ (spectralParameter_pos hk t),
    spectralParameter_inv hk,spectral_exponent hk,exp_add]
  unfold transformedWave
  ring

end AtomicTriangular.Construction

end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_MatrixInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Interval
open Matrix AtomicTriangular.MatrixBounds

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
lemma matrixNorm_bound [Nonempty n] {a : m → n → RI} {A : Matrix m n ℝ} {b : ℤ}
    (ha : ∀ i j, (a i j).Mem (A i j)) (hb : ∀ j, matrixColBound a j ≤ b) :
    matNorm A ≤ (b:ℝ)/(scale:ℝ) := by
  apply matNorm_le
  intro j
  have hh := (RI.mem_sum (fun i => RI.mem_abs (ha i j))).2
  apply (le_div_iff₀ scale_pos).mpr
  change colNorm A j * (scale:ℝ) ≤ (b:ℝ)
  rw [mul_comm]
  apply hh.trans
  exact_mod_cast hb j

end AtomicTriangular.Interval
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_Inverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval AtomicTriangular.MatrixBounds Matrix
lemma minusResidual_bound : matNorm (minusApprox*(1 - Construction.R)-1) ≤ (1:ℝ)/10^26 := by
  have hh := matrixNorm_bound (b := 10000000000000000000000000000000000) minusResidualTable_mem_x (by
    intro j
    revert j
    decide +kernel)
  norm_num [scale] at hh ⊢
  exact hh
lemma minusBlock_isUnit : IsUnit (1 - Construction.R) :=
  isUnit_of_residual _ minusApprox (minusResidual_bound.trans_lt (by norm_num))
lemma plusResidual_bound : matNorm (plusApprox*(1 + Construction.R)-1) ≤ (1:ℝ)/10^26 := by
  have hh := matrixNorm_bound (b := 10000000000000000000000000000000000) plusResidualTable_mem_x (by
    intro j
    revert j
    decide +kernel)
  norm_num [scale] at hh ⊢
  exact hh
lemma plusBlock_isUnit : IsUnit (1 + Construction.R) :=
  isUnit_of_residual _ plusApprox (plusResidual_bound.trans_lt (by norm_num))

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_TailSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set
namespace AtomicTriangular.Construction
open MeasureTheory

lemma continuous_intervalIntegral_complex {f : ℂ → ℝ → ℂ}
    (hf : Continuous f.uncurry) (a b : ℝ) :
    Continuous (fun s => ∫ t in a..b, f s t) := by
  have h₁ := continuous_parametric_integral_of_continuous (μ := volume) hf (isCompact_Icc (a := a) (b := b))
  have h₂ := continuous_parametric_integral_of_continuous (μ := volume) hf (isCompact_Icc (a := b) (b := a))
  simpa only [intervalIntegral, integral_Icc_eq_integral_Ioc] using! h₁.sub h₂

lemma exponential_first_integral (u : ℂ) (hu : u ≠ 0) (t : ℝ) :
    I*Real.pi * (∫ r in (0:ℝ)..t, exp (I*Real.pi*(r:ℂ)*u)) =
      (exp (I*Real.pi*(t:ℂ)*u)-1)/u := by
  have hc : I*(Real.pi:ℂ)*u ≠ 0 := mul_ne_zero (mul_ne_zero I_ne_zero
    (by exact_mod_cast Real.pi_ne_zero)) hu
  have hi := integral_exp_mul_complex (a := 0) (b := t) hc
  simp only [Complex.ofReal_zero, mul_zero, exp_zero] at hi
  simp_rw [show ∀ r : ℝ, I*(Real.pi:ℂ)*(r:ℂ)*u = (I*Real.pi*u)*(r:ℂ) by intro r; ring]
  rw [hi]
  field_simp

lemma exponential_second_integral (u : ℂ) (hu : u ≠ 0) (t : ℝ) :
    -(Real.pi:ℂ)^2 * (∫ r in (0:ℝ)..t, ((t:ℂ)-r)*exp (I*Real.pi*(r:ℂ)*u)) =
      (exp (I*Real.pi*(t:ℂ)*u)-1-I*Real.pi*(t:ℂ)*u)/u^2 := by
  let c : ℂ := I*Real.pi*u
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero I_ne_zero
    (by exact_mod_cast Real.pi_ne_zero)) hu
  let F : ℝ → ℂ := fun r => (((t:ℂ)-(r:ℂ))/c+1/c^2)*exp (c*(r:ℂ))
  have hd (x : ℝ) : HasDerivAt F (((t:ℂ)-(x:ℂ))*exp (c*(x:ℂ))) x := by
    have hx : HasDerivAt (fun x : ℝ => (x:ℂ)) 1 x := by
      simpa using! (Complex.ofRealCLM.hasDerivAt (x := x))
    have hf := ((hx.const_sub (t:ℂ)).div_const c).add_const (1/c^2)
    have hh := hf.mul ((hx.const_mul c).cexp)
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (show IntervalIntegrable (fun x : ℝ => ((t:ℂ)-(x:ℂ))*exp (c*(x:ℂ))) volume 0 t from
      (by fun_prop : Continuous (fun x : ℝ => ((t:ℂ)-(x:ℂ))*exp (c*(x:ℂ)))).intervalIntegrable 0 t)
  have he : ∀ r : ℝ, I*(Real.pi:ℂ)*(r:ℂ)*u = c*(r:ℂ) := by intro r; dsimp [c] <;> ring
  simp_rw [he]
  rw [hi]
  dsimp [F]
  simp only [sub_self, zero_div, zero_add, mul_zero, exp_zero,
    mul_one, sub_zero]
  dsimp [c]
  field_simp
  simp [Complex.I_sq]
  ring

lemma continuous_integralDBasis (n : Node) : Continuous (integralDBasis n) := by
  unfold integralDBasis
  refine continuous_finsetSum _ fun l _ => ?_
  exact continuous_const.mul <| continuous_const.mul
    (continuous_intervalIntegral_complex (by fun_prop) 0 (frequency l))

lemma continuous_integralCBasis (n : Node) : Continuous (integralCBasis n) := by
  unfold integralCBasis
  refine continuous_finsetSum _ fun l _ => ?_
  exact continuous_const.mul <| continuous_const.mul
    (continuous_intervalIntegral_complex (by fun_prop) 0 (frequency l))

lemma exp_frequency_sub (s n : ℂ) (l : Fin 31) :
    exp (I*Real.pi*frequency l*n) * exp (I*Real.pi*frequency l*(s-n)) =
      exp (I*Real.pi*frequency l*s) := by
  rw [← exp_add]
  congr 1
  ring

lemma integralDBasis_eq (n : Node) : integralDBasis n = dBasis n := by
  apply (continuous_integralDBasis n).ext_on (dense_compl_singleton (n.val:ℂ))
    (differentiable_dBasis n).continuous
  intro s hs
  have hsn : s ≠ (n.val:ℂ) := hs
  rw [dBasis_eq n hsn]
  unfold integralDBasis
  simp_rw [exponential_first_integral (s-n.val) (sub_ne_zero.mpr hsn), ← mul_div_assoc,
    ← Finset.sum_div]
  congr 1
  calc
    _ = (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*s)) -
        ∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      rw [mul_sub, mul_one, mul_assoc, exp_frequency_sub]
    _ = P s := by
      have hz : (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val)) = 0 := by
        simpa [waveDerivative] using fourier_node_cancel n
      rw [hz, sub_zero, P_fourier]

lemma integralCBasis_eq (n : Node) : integralCBasis n = cBasis n := by
  apply (continuous_integralCBasis n).ext_on (dense_compl_singleton (n.val:ℂ))
    (differentiable_cBasis n).continuous
  intro s hs
  have hsn : s ≠ (n.val:ℂ) := hs
  rw [cBasis_eq n hsn]
  unfold integralCBasis
  simp_rw [exponential_second_integral (s-n.val) (sub_ne_zero.mpr hsn), ← mul_div_assoc,
    ← Finset.sum_div]
  congr 1
  calc
    _ = (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*s)) -
        (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val)) -
        (∑ l : Fin 31, fourierCoeff l * (I*Real.pi*frequency l) *
          exp (I*Real.pi*frequency l*n.val)) * (s-n.val) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      rw [mul_sub, mul_sub, mul_one, mul_assoc, exp_frequency_sub]
      ring
    _ = P s := by
      have hd : (∑ l : Fin 31, fourierCoeff l * (I*Real.pi*frequency l) *
          exp (I*Real.pi*frequency l*n.val)) = 0 := by
        simpa [waveDerivative] using fourier_node_deriv_cancel n
      have hz : (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val)) = 0 := by
        simpa [waveDerivative] using fourier_node_cancel n
      rw [hd, hz, zero_mul, sub_zero, sub_zero, P_fourier]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_SpectralCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set MeasureTheory
namespace AtomicTriangular.Construction

lemma spectralCCLM_apply (n : Node) (f : C(Spectrum,ℂ)) : spectralCCLM n f = spectralC n f :=
  spectralCLinear_apply n f
lemma spectralDCLM_apply (n : Node) (f : C(Spectrum,ℂ)) : spectralDCLM n f = spectralD n f :=
  spectralDLinear_apply n f
lemma spectralPCLM_apply (f : C(Spectrum,ℂ)) : spectralPCLM f = spectralP f := by
  simp [spectralPCLM,spectralP]

lemma spectralCCLM_norm (n : Node) : ‖spectralCCLM n‖ ≤ cVariation :=
  LinearMap.mkContinuous_norm_le _ (by simp only [cVariation, coeffAbs] <;> positivity) _
lemma spectralDCLM_norm (n : Node) : ‖spectralDCLM n‖ ≤ dVariation :=
  LinearMap.mkContinuous_norm_le _ (by simp only [dVariation, coeffAbs] <;> positivity) _

lemma extend_on (f : C(Spectrum,ℂ)) (t : ℝ) (ht : t ∈ Spectrum) :
    extend f t = f ⟨t,ht⟩ := by
  simp only [extend,Set.projIcc_of_mem _ ht]

lemma interval_frequency_subset (l : Fin 31) : Set.uIcc 0 (frequency l) ⊆ Spectrum := by
  have h := Set.uIcc_subset_uIcc (show (0:ℝ) ∈ Set.uIcc (-(5/6)) (5/6) by norm_num)
    (show frequency l ∈ Set.uIcc (-(5/6)) (5/6) by simpa [Set.uIcc_of_le (by norm_num : (-(5/6):ℝ) ≤ 5/6)] using frequency_mem l)
  simpa [Set.uIcc_of_le (by norm_num : (-(5/6):ℝ) ≤ 5/6)] using h

lemma spectralD_phase (n : Node) (s : ℂ) : spectralD n (phaseFunction s) = dBasis n s := by
  rw [← integralDBasis_eq]
  unfold spectralD integralDBasis
  apply Finset.sum_congr rfl
  intro l hl
  congr 2
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [extend_on _ t (interval_frequency_subset l ht)]
  change exp (-I*Real.pi*(t:ℂ)*n.val)*exp (I*Real.pi*(t:ℂ)*s) = _
  rw [← exp_add]
  congr 1
  ring

lemma spectralC_phase (n : Node) (s : ℂ) : spectralC n (phaseFunction s) = cBasis n s := by
  rw [← integralCBasis_eq]
  unfold spectralC integralCBasis
  apply Finset.sum_congr rfl
  intro l hl
  congr 2
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [extend_on _ t (interval_frequency_subset l ht)]
  change ((frequency l:ℂ)-t)*exp (-I*Real.pi*(t:ℂ)*n.val)*exp (I*Real.pi*(t:ℂ)*s) = _
  rw [mul_assoc,← exp_add]
  congr 2
  ring

lemma spectralP_phase (s : ℂ) : spectralP (phaseFunction s) = P s := by
  exact (P_fourier s).symm

lemma exponential_apply (f : C(Spectrum,ℂ)) (t : Spectrum) :
    (NormedSpace.exp f) t = exp (f t) := by
  have h := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ t)
    (ContinuousMap.evalCLM ℂ t).continuous f
  simpa only [ContinuousMap.evalAlgHom_apply,Complex.exp_eq_exp_ℂ] using h

lemma phaseFunction_exp (s : ℂ) : phaseFunction s = NormedSpace.exp (s • frequencyFunction) := by
  ext t
  rw [exponential_apply]
  change exp (I*Real.pi*(t.val:ℂ)*s) = exp (s*(I*Real.pi*(t.val:ℂ)))
  congr 1
  ring

lemma differentiable_phaseFunction : Differentiable ℂ phaseFunction := by
  have he : phaseFunction = fun s => NormedSpace.exp (s • frequencyFunction) := funext phaseFunction_exp
  rw [he]
  exact differentiable_exp_smul_const ℂ frequencyFunction

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_ActualInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds

lemma tail_pairs_norm (w : TailCoefficients) :
    (∑' n, (|w (n,0)| + |w (n,1)|))=‖w‖ := by
  rw [l1_norm]
  symm
  calc
    (∑' p, |w p|) = ∑' n : TailNode, ∑' d : Fin 2, |w (n,d)| := (l1_summable w).tsum_prod
    _ = _ := by simp only [tsum_fintype,Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
                rfl

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_FourierCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform RealInnerProductSpace
open Complex Filter Set MeasureTheory GaussianFourier
namespace AtomicTriangular.Construction

lemma transformedFunction_apply (k v : ℝ) (hk : 0 < k) (s : ℂ) (t : Spectrum) :
    transformedFunction k v hk s t = transformedWave k v t.val s := by
  simp only [transformedFunction,ContinuousMap.mul_apply,exponential_apply]
  change lambda k t.val * exp (s*(I*Real.pi*zeta k v t.val)) = _
  unfold transformedWave
  congr 2
  ring
lemma atomFunction_apply (k : ℝ) (x : Plane) (t : Spectrum) :
    atomFunction k x t = exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*
      exp (I*Real.pi*(t.val:ℂ)*(radial x:ℂ)) := rfl
lemma continuous_atomFunction (k : ℝ) : Continuous (atomFunction k) := by
  have hs : Continuous (fun x : Plane => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))) := by
    unfold radial; fun_prop
  have ht : Continuous (fun x : Plane => phaseFunction (radial x:ℂ)) := by
    apply differentiable_phaseFunction.continuous.comp
    unfold radial; fun_prop
  simpa only [atomFunction] using! hs.smul ht
lemma atomFunction_bound (k : ℝ) (x : Plane) : ‖atomFunction k x‖ ≤ gaussian k x := by
  apply (ContinuousMap.norm_le _ (by unfold gaussian; positivity)).mpr
  intro t
  rw [atomFunction_apply,norm_mul]
  have hp : ‖exp (I*Real.pi*(t.val:ℂ)*(radial x:ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hp,mul_one,Complex.norm_exp]
  simp [gaussian]
lemma integrable_gaussian {k : ℝ} (hk : 0 < k) : Integrable (gaussian k) := by
  have hc : 0 < ((Real.pi*k*b:ℝ):ℂ).re := by
    simpa only [Complex.ofReal_re] using mul_pos (mul_pos Real.pi_pos hk) b_pos
  have hi := (integrable_cexp_neg_mul_sq_norm_add hc 0 (0:Plane)).norm
  convert! hi using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp [gaussian,radial,Complex.norm_exp,mul_assoc,pow_two]
lemma integrable_atomFunction {k : ℝ} (hk : 0 < k) : Integrable (atomFunction k) :=
  (integrable_gaussian hk).mono' (continuous_atomFunction k).aestronglyMeasurable
    (ae_of_all _ (atomFunction_bound k))
lemma clm_fourier {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
    (L : E →L[ℂ] F) (f : Plane → E) (hf : Integrable f) (w : Plane) :
    𝓕 (fun x => L (f x)) w = L (𝓕 f w) := by
  simp only [Real.fourier_eq]
  have hh := L.integral_comp_comm ((Real.fourierIntegral_convergent_iff w).mpr hf)
  simpa only [Circle.smul_def,map_smul] using hh
lemma fourier_atomFunction {k : ℝ} (hk : 0 < k) (v : ℝ) (w : Plane) :
    𝓕 (atomFunction k) w = exp (-(Real.pi:ℂ)*v*(radial w:ℂ)) •
      transformedFunction k v hk (radial w:ℂ) := by
  ext t
  have hh := clm_fourier (ContinuousMap.evalCLM ℂ t) (atomFunction k) (integrable_atomFunction hk) w
  have ha := transformed_spectral_wave hk v t.val w
  change 𝓕 (fun x => atomFunction k x t) w = (𝓕 (atomFunction k) w) t at hh
  rw [← hh]
  change 𝓕 (fun x => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*
    exp (I*Real.pi*(t.val:ℂ)*(radial x:ℂ))) w =
    exp (-(Real.pi:ℂ)*v*(radial w:ℂ))*transformedFunction k v hk (radial w:ℂ) t
  rw [transformedFunction_apply]
  exact ha
lemma fourier_spectral (S : C(Spectrum,ℂ) →L[ℂ] ℂ) {k : ℝ} (hk : 0 < k) (v : ℝ) (w : Plane) :
    𝓕 (fun x => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*S (phaseFunction (radial x:ℂ))) w =
      exp (-(Real.pi:ℂ)*v*(radial w:ℂ))*S (transformedFunction k v hk (radial w:ℂ)) := by
  have hh := clm_fourier S (atomFunction k) (integrable_atomFunction hk) w
  have he : (fun x => S (atomFunction k x)) =
      (fun x => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*S (phaseFunction (radial x:ℂ))) := by
    ext x
    simp only [atomFunction,map_smul,smul_eq_mul]
  rw [he,fourier_atomFunction hk v,map_smul] at hh
  exact hh
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_InputCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set MeasureTheory
namespace AtomicTriangular.Construction

lemma tailSpectral_term_bound (a : InputCoefficients) (n : TailNode) :
    ‖(a.tailC n:ℂ) • spectralCCLM n.val + (a.tailD n:ℂ) • spectralDCLM n.val‖ ≤
      (|a.tailC n|+|a.tailD n|)*tailVariation := by
  have hc : cVariation ≤ tailVariation := by
    exact le_add_of_nonneg_right (by unfold dVariation coeffAbs; positivity)
  have hd : dVariation ≤ tailVariation := by
    exact le_add_of_nonneg_left (by unfold cVariation coeffAbs; positivity)
  calc
    _ ≤ ‖(a.tailC n:ℂ) • spectralCCLM n.val‖ + ‖(a.tailD n:ℂ) • spectralDCLM n.val‖ := by
      convert! norm_add_le ((a.tailC n:ℂ) • spectralCCLM n.val) ((a.tailD n:ℂ) • spectralDCLM n.val) using 1
      all_goals try with_reducible_and_instances rfl
    _ ≤ |a.tailC n| * ‖spectralCCLM n.val‖ + |a.tailD n| * ‖spectralDCLM n.val‖ := by
      have hn (r : ℝ) (T : C(Spectrum,ℂ) →L[ℂ] ℂ) : ‖(r:ℂ) • T‖ ≤ |r| * ‖T‖ := by
        apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (abs_nonneg r) (norm_nonneg T))
        intro f
        change ‖(r:ℂ) * T f‖ ≤ _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
        exact mul_le_mul_of_nonneg_left (T.le_opNorm f) (abs_nonneg r)
      exact add_le_add (hn _ _) (hn _ _)
    _ ≤ |a.tailC n| *tailVariation+|a.tailD n| *tailVariation :=
      add_le_add (mul_le_mul_of_nonneg_left ((spectralCCLM_norm n.val).trans hc) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left ((spectralDCLM_norm n.val).trans hd) (abs_nonneg _))
    _ = _ := by ring

lemma summable_tailSpectral (a : InputCoefficients) :
    Summable (fun n => (a.tailC n:ℂ) • spectralCCLM n.val + (a.tailD n:ℂ) • spectralDCLM n.val) :=
  Summable.of_norm_bounded (E := C(Spectrum,ℂ) →L[ℂ] ℂ)
    (f := fun n => (a.tailC n:ℂ) • spectralCCLM n.val + (a.tailD n:ℂ) • spectralDCLM n.val)
    (a.summable.mul_right tailVariation) (tailSpectral_term_bound a)

lemma tailSpectral_apply (a : InputCoefficients) (f : C(Spectrum,ℂ)) :
    tailSpectral a f = (a.C:ℂ)*spectralP f +
      ∑' n : TailNode, ((a.tailC n:ℂ)*spectralC n.val f + (a.tailD n:ℂ)*spectralD n.val f) := by
  have ht := (ContinuousLinearMap.apply ℂ ℂ f).map_tsum (summable_tailSpectral a)
  simpa only [tailSpectral,add_apply, smul_apply,
    ContinuousLinearMap.apply_apply,smul_eq_mul,spectralPCLM_apply,
    spectralCCLM_apply,spectralDCLM_apply] using congrArg (fun x => (a.C:ℂ)*spectralP f+x) ht

lemma tailSpectral_phase (a : InputCoefficients) (s : ℂ) :
    tailSpectral a (phaseFunction s) = tailInput a s := by
  simp only [tailSpectral_apply,spectralP_phase,spectralC_phase,spectralD_phase,tailInput]

lemma atomSpectral_apply (S : Fin 31 → ℂ) (f : C(Spectrum,ℂ)) :
    atomSpectral S f = ∑ j : Fin 31, S j*f ⟨frequency j,frequency_mem j⟩ := by
  simp [atomSpectral]

lemma atomSpectral_finiteC_phase (j : Fin 15) (s : ℂ) :
    atomSpectral (FiniteCertificate.cCoefficient j) (phaseFunction s) = finiteC j s := by
  rw [atomSpectral_apply,FiniteCertificate.finiteC_fourier]
  rfl
lemma atomSpectral_finiteD_phase (j : Fin 15) (s : ℂ) :
    atomSpectral (FiniteCertificate.dCoefficient j) (phaseFunction s) = finiteD j s := by
  rw [atomSpectral_apply,FiniteCertificate.finiteD_fourier]
  rfl

lemma finiteSpectral_phase (a : InputCoefficients) (s : ℂ) :
    finiteSpectral a (phaseFunction s) = finiteInput a s := by
  simp only [finiteSpectral,sum_apply,add_apply,
    smul_apply,smul_eq_mul,atomSpectral_finiteC_phase,atomSpectral_finiteD_phase,finiteInput]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_FiniteAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds
lemma finiteApprox_fixed (side : Fin 2) (e : Fin 8 → ℝ) (i : Fin 2) :
    finiteApprox side e ⟨i.val,by omega⟩=(gamma side *ᵥ e) ⟨i.val,by omega⟩ := by
  change (∑ j : Fin 8,Acoefficient side ⟨i.val,by omega⟩ j*e j)=_
  simp only [Acoefficient,show i.val<2 from i.isLt,↓reduceDIte]
  rfl
lemma gamma_actual (side : Fin 2) (z : ℝ) :
    (gamma side *ᵥ actualParameter z)= ![11/25,0,if side.val=0 then -(3/500) else 3/500] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,gamma,Fin.sum_univ_succ,actualParameter]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_FiniteSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Matrix

lemma Uplus_equation : (1-R)*Uplus = Yf+R0*(gamma 1+gamma 0) := by
  unfold Uplus
  apply Matrix.mul_nonsing_inv_cancel_left
  exact (Matrix.isUnit_iff_isUnit_det _).mp FiniteCertificate.minusBlock_isUnit
lemma Uminus_equation : (1+R)*Uminus = Yf+R0*(gamma 1-gamma 0) := by
  unfold Uminus
  apply Matrix.mul_nonsing_inv_cancel_left
  exact (Matrix.isUnit_iff_isUnit_det _).mp FiniteCertificate.plusBlock_isUnit
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_FiniteInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel
lemma extendFiniteError_fixed (u : FiniteCoefficients) (i : Fin 2) :
    extendFiniteError u ⟨i.val,by omega⟩=0 := by
  change (if hi : i.val<2 then _ else _)=_
  simp only [i.isLt,↓reduceDIte]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Energy_Mixtures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open Classical Filter
namespace TriangularUniversal

lemma triangularPoint_coord_zero (j k : ℤ) :
    triangularPoint (j, k) 0 = Real.sqrt (2 / Real.sqrt 3) * ((j : ℝ) + (k : ℝ) / 2) := by
  simp [triangularPoint]

lemma triangularPoint_coord_one (j k : ℤ) :
    triangularPoint (j, k) 1 = Real.sqrt (2 / Real.sqrt 3) * ((k : ℝ) * Real.sqrt 3 / 2) := by
  simp [triangularPoint]

lemma triangularPoint_norm_sq (j k : ℤ) :
    b * ‖triangularPoint (j, k)‖ ^ 2 = (j : ℝ) ^ 2 + (j : ℝ) * (k : ℝ) + (k : ℝ) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp only [triangularPoint_coord_zero, triangularPoint_coord_one, Real.norm_eq_abs,
    sq_abs, mul_pow]
  have hs : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc : (Real.sqrt (2 / Real.sqrt (3 : ℝ))) ^ 2 = 2 / Real.sqrt 3 :=
    Real.sq_sqrt (by positivity)
  rw [hc]
  dsimp [b]
  field_simp
  nlinarith [hs]

end TriangularUniversal

open scoped BigOperators Topology NNReal ENNReal Polynomial
open Filter Finset MeasureTheory
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Lattice_LatticeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace AtomicTriangular
lemma triangular_scale_eq : (Real.sqrt b)⁻¹=Real.sqrt (2/Real.sqrt 3) := by
  rw [←Real.sqrt_inv]
  congr 1
  simp [b,inv_div]
lemma triangularPoint_eq_support (v : ℤ × ℤ) : triangularPoint v=TriangularUniversal.triangularPoint v := by
  unfold triangularPoint TriangularUniversal.triangularPoint
  rw [triangular_scale_eq]
  congr 2
  unfold b
  ring_nf
lemma b_pos : 0 < b := by unfold b; positivity
lemma b_sq : b^2=3/4 := by
  unfold b
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num
lemma triangularPoint_norm_sq (j k : ℤ) :
    b*‖triangularPoint (j,k)‖^2=(j:ℝ)^2+(j:ℝ)*k+(k:ℝ)^2 := by
  rw [triangularPoint_eq_support]
  exact TriangularUniversal.triangularPoint_norm_sq j k
lemma eisenstein_mod36_finite : ∀ j k : Fin 36,
    ((j.val:ℤ)^2+(j.val:ℤ)*k.val+(k.val:ℤ)^2)%36∈Construction.residues := by decide +kernel
lemma eisenstein_mod36 (j k : ℤ) :
    (j^2+j*k+k^2)%36∈Construction.residues := by
  let j' : Fin 36 := ⟨(j%36).toNat,by have := Int.emod_nonneg j (by norm_num : (36:ℤ)≠0); have := Int.emod_lt_of_pos j (by norm_num : (0:ℤ)<36); omega⟩
  let k' : Fin 36 := ⟨(k%36).toNat,by have := Int.emod_nonneg k (by norm_num : (36:ℤ)≠0); have := Int.emod_lt_of_pos k (by norm_num : (0:ℤ)<36); omega⟩
  have hj : (j'.val:ℤ)=j%36 := Int.toNat_of_nonneg (Int.emod_nonneg j (by norm_num))
  have hk : (k'.val:ℤ)=k%36 := Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))
  have hh := eisenstein_mod36_finite j' k'
  rw [hj,hk] at hh
  simpa [Int.add_emod,Int.mul_emod,pow_two,Int.emod_emod] using hh
lemma A_radial_node {x : Plane} (hx : x∈A) (hx0 : x≠0) :
    ∃ n : Construction.Node,Construction.radial x=n.val := by
  obtain ⟨⟨j,k⟩,rfl⟩ := hx
  let n : ℤ := j^2+j*k+k^2
  have he : Construction.radial (triangularPoint (j,k))=(n:ℝ) := by
    change b*‖triangularPoint (j,k)‖^2=_
    rw [triangularPoint_norm_sq]
    dsimp [n]
    push_cast
    rfl
  have hn : 0 < n := by
    have hp : 0 < Construction.radial (triangularPoint (j,k)) :=
      mul_pos b_pos (sq_pos_of_pos (norm_pos_iff.mpr hx0))
    rw [he] at hp
    exact_mod_cast hp
  exact ⟨⟨n,hn,eisenstein_mod36 j k⟩,he⟩
lemma dualA_integer_coordinates {w : Plane} (hw : w∈dualA) :
    ∃ j k : ℤ,w 0=(Real.sqrt b)*(j:ℝ) ∧ (Real.sqrt b)*w 1=(k:ℝ)-(j:ℝ)/2 := by
  obtain ⟨j,hj⟩ := hw (triangularPoint (1,0)) ⟨(1,0),rfl⟩
  obtain ⟨k,hk⟩ := hw (triangularPoint (0,1)) ⟨(0,1),rfl⟩
  have hr : (Real.sqrt b)^2=b := Real.sq_sqrt b_pos.le
  have hp : 0 < Real.sqrt b := Real.sqrt_pos.mpr b_pos
  simp [triangularPoint,inner_smul_left,inner_add_left,EuclideanSpace.inner_single_left] at hj hk
  refine ⟨j,k,?_,?_⟩
  · field_simp at hj
    nlinarith
  · field_simp at hj hk
    apply (mul_left_cancel₀ hp.ne')
    nlinarith [congrArg (fun t : ℝ => t*w 1) hr]
lemma dualA_radial_node {w : Plane} (hw : w∈dualA) (hw0 : w≠0) :
    ∃ n : Construction.Node,Construction.radial w=n.val := by
  obtain ⟨j,k,hj,hk⟩ := dualA_integer_coordinates hw
  let n : ℤ := j^2-j*k+k^2
  have he : Construction.radial w=(n:ℝ) := by
    change b*‖w‖^2=_
    rw [EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
    simp only [Real.norm_eq_abs,sq_abs]
    have hr : (Real.sqrt b)^2=b := Real.sq_sqrt b_pos.le
    have hb := b_sq
    have hk' := congrArg (fun t : ℝ => t^2) hk
    rw [mul_pow,hr] at hk'
    rw [hj,mul_pow,hr]
    dsimp [n]
    push_cast
    nlinarith
  have hn : 0 < n := by
    have hpos : 0 < Construction.radial w := mul_pos b_pos (sq_pos_of_pos (norm_pos_iff.mpr hw0))
    rw [he] at hpos
    exact_mod_cast hpos
  have hm : n%36∈Construction.residues := by
    convert eisenstein_mod36 j (-k) using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [n]
    congr 1
    ring
  exact ⟨⟨n,hn,hm⟩,he⟩
end AtomicTriangular
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_Gaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped SchwartzMap
namespace AtomicTriangular.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma iteratedDeriv_real_of_complex {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => (f x).re) = fun x : ℝ => (iteratedDeriv n f x).re := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext x
    exact ((hf.contDiff (n := ⊤)).differentiable_iteratedDeriv n (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (x : ℂ)).hasDerivAt.real_of_complex.deriv

lemma entire_real_temperate {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hstrip : ∃ M : ℝ, ∀ z : ℂ, |z.im| ≤ 1 → ‖f z‖ ≤ M) :
    Function.HasTemperateGrowth (fun x : ℝ => (f x).re) := by
  obtain ⟨M,hM⟩ := hstrip
  refine ⟨hf.contDiff.real_of_complex, fun n => ⟨0,(n.factorial:ℝ)*M,?_⟩⟩
  intro x
  rw [pow_zero,mul_one,norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_real_of_complex hf]
  apply (Complex.abs_re_le_norm _).trans
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (f := f) n
    (by norm_num : (0:ℝ)<1) hf.diffContOnCl (c := (x:ℂ)) (C := M) (fun z hz => hM z (by
      have hi := Complex.abs_im_le_norm (z-(x:ℂ))
      have he := Metric.mem_sphere.mp hz
      simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero,← dist_eq_norm,he] using hi))
  simpa using hh

lemma dampedEntireSchwartz_apply (c : ℝ) (hc : 0 < c) (b : ℝ) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hstrip : ∃ M : ℝ, ∀ z : ℂ, |z.im| ≤ 1 → ‖f z‖ ≤ M) (x : E) :
    dampedEntireSchwartz c hc b f hf hstrip x = Real.exp (-c*‖x‖^2)*(f (b*‖x‖^2)).re := by
  have ht := entire_real_temperate hf hstrip
  have hg : Function.HasTemperateGrowth (fun x : E => (f (b*‖x‖^2)).re) := by
    convert ht.comp (by fun_prop : Function.HasTemperateGrowth (fun x : E => b*‖x‖^2)) using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp
  rw [dampedEntireSchwartz,SchwartzMap.smulLeftCLM_apply_apply hg,gaussianSchwartz_apply]
  simp [mul_comm]

end AtomicTriangular.Analysis
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_Regularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology SchwartzMap
open Complex Filter Set
namespace AtomicTriangular.Construction

lemma inputSchwartz_apply (a : InputCoefficients) (x : Plane) :
    inputSchwartz a x = Real.exp (-Real.pi*h*radial x)*(tailInput a (radial x)).re +
      Real.exp (-Real.pi*H*radial x)*(finiteInput a (radial x)).re := by
  simp only [inputSchwartz,add_apply,Analysis.dampedEntireSchwartz_apply,radial]
  push_cast
  congr 3 <;> ring

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_Realness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform ComplexConjugate SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular.Construction

lemma P_conj (s : ℂ) : conj (P s) = P (conj s) := by
  simp only [P,sineFactor,map_prod,map_pow,map_mul,← Complex.sin_conj,map_sub,
    Complex.conj_ofReal,map_ofNat,map_intCast]

lemma dslope_conj_real {f : ℂ → ℂ} (hf : ∀ s, conj (f s) = f (conj s))
    (r : ℝ) (s : ℂ) : conj (dslope f (r:ℂ) s) = dslope f (r:ℂ) (conj s) := by
  have he : conj ∘ f ∘ conj = f := by
    ext z
    simp only [Function.comp_apply,hf,RCLike.conj_conj]
  have hd := congrFun (deriv_conj_conj (f := f)) (r:ℂ)
  rw [he] at hd
  simp only [Function.comp_apply,Complex.conj_ofReal] at hd
  by_cases hs : s = (r:ℂ)
  · subst s
    simpa only [Complex.conj_ofReal,dslope_same] using hd.symm
  · have hc : conj s ≠ (r:ℂ) := by
      intro h; apply hs
      have hh := congrArg conj h
      simpa using hh
    rw [dslope_of_ne _ hs,dslope_of_ne _ hc]
    simp only [slope_def_field,map_div₀,map_sub,hf,Complex.conj_ofReal]

lemma dBasis_conj (n : Node) (s : ℂ) : conj (dBasis n s) = dBasis n (conj s) := by
  simpa only [dBasis,Complex.ofReal_intCast] using dslope_conj_real P_conj (n.val:ℝ) s
lemma cBasis_conj (n : Node) (s : ℂ) : conj (cBasis n s) = cBasis n (conj s) := by
  simpa only [cBasis,Complex.ofReal_intCast] using dslope_conj_real (dBasis_conj n) (n.val:ℝ) s
lemma finiteC_conj (j : Fin 15) (s : ℂ) : conj (finiteC j s) = finiteC j (conj s) := by
  simp only [finiteC,sineFactor,map_prod,map_pow,map_mul,← Complex.sin_conj,map_sub,
    Complex.conj_ofReal,map_ofNat,map_intCast]
lemma finiteD_conj (j : Fin 15) (s : ℂ) : conj (finiteD j s) = finiteD j (conj s) := by
  simp only [finiteD,sineFactor,map_prod,map_pow,map_mul,← Complex.sin_conj,← Complex.cos_conj,map_sub,
    Complex.conj_ofReal,map_ofNat,map_intCast]
lemma tailInput_conj (a : InputCoefficients) (s : ℂ) : conj (tailInput a s) = tailInput a (conj s) := by
  simp only [tailInput,map_add,map_mul,Complex.conj_ofReal,P_conj,Complex.conj_tsum,cBasis_conj,dBasis_conj]
lemma finiteInput_conj (a : InputCoefficients) (s : ℂ) : conj (finiteInput a s) = finiteInput a (conj s) := by
  simp only [finiteInput,map_sum,map_add,map_mul,Complex.conj_ofReal,finiteC_conj,finiteD_conj]

lemma inputComplex_real (a : InputCoefficients) (x : Plane) : conj (inputComplex a x) = inputComplex a x := by
  simp only [inputComplex,map_add,map_mul,← Complex.exp_conj,map_neg,Complex.conj_ofReal,tailInput_conj,finiteInput_conj]
lemma inputComplex_re (a : InputCoefficients) (x : Plane) : (inputComplex a x).re = inputSchwartz a x := by
  rw [inputSchwartz_apply]
  simp [inputComplex,Complex.mul_re,← Complex.ofReal_mul,← Complex.ofReal_neg,Complex.exp_ofReal_re]
lemma inputComplex_eq (a : InputCoefficients) (x : Plane) : inputComplex a x = (inputSchwartz a x:ℂ) := by
  rw [← inputComplex_re]
  exact (Complex.conj_eq_iff_re.mp (inputComplex_real a x)).symm

lemma complexInputSchwartz_apply (a : InputCoefficients) (x : Plane) :
    complexInputSchwartz a x = inputComplex a x := by
  exact (inputComplex_eq a x).symm

lemma radial_neg (x : Plane) : radial (-x) = radial x := by simp [radial]
lemma inputComplex_even (a : InputCoefficients) (x : Plane) : inputComplex a (-x) = inputComplex a x := by
  simp only [inputComplex,radial_neg]
lemma fourier_conj_even (f : Plane → ℂ) (hre : ∀ x, conj (f x) = f x)
    (hev : ∀ x, f (-x) = f x) (w : Plane) : conj (𝓕 f w) = 𝓕 f w := by
  have he : (fun x => f (-x)) = f := funext hev
  have hi : conj (𝓕 f w) = 𝓕⁻ f w := by
    simp only [Real.fourier_eq',Real.fourierInv_eq',smul_eq_mul,← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with x
    simp [← Complex.exp_conj,hre,map_ofNat]
  rw [hi,Real.fourierInv_eq_fourier_comp_neg,he]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_FourierPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform ComplexConjugate SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular.Construction

lemma integrable_spectral (S : C(Spectrum,ℂ) →L[ℂ] ℂ) {k : ℝ} (hk : 0 < k) :
    Integrable (fun x : Plane => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*S (phaseFunction (radial x:ℂ))) := by
  have hh := S.integrable_comp (integrable_atomFunction hk)
  simpa only [atomFunction,map_smul,smul_eq_mul,Function.comp_def] using hh
lemma inputComplex_spectral (a : InputCoefficients) (x : Plane) : inputComplex a x =
    exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*tailSpectral a (phaseFunction (radial x:ℂ)) +
    exp (-(Real.pi:ℂ)*H*(radial x:ℂ))*finiteSpectral a (phaseFunction (radial x:ℂ)) := by
  rw [tailSpectral_phase,finiteSpectral_phase]
  rfl
lemma fourier_inputComplex (a : InputCoefficients) : 𝓕 (inputComplex a) = outputComplex a := by
  ext w
  simp only [Real.fourier_eq,inputComplex_spectral,smul_add]
  rw [integral_add ((Real.fourierIntegral_convergent_iff w).mpr (integrable_spectral (tailSpectral a) h_pos))
    ((Real.fourierIntegral_convergent_iff w).mpr (integrable_spectral (finiteSpectral a) H_pos))]
  change 𝓕 (fun x => exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*tailSpectral a (phaseFunction (radial x:ℂ))) w +
    𝓕 (fun x => exp (-(Real.pi:ℂ)*H*(radial x:ℂ))*finiteSpectral a (phaseFunction (radial x:ℂ))) w = _
  rw [fourier_spectral _ h_pos h,fourier_spectral _ H_pos h]
  simp only [outputComplex,transformedInput,mul_add]

lemma coe_complexInputSchwartz (a : InputCoefficients) :
    (complexInputSchwartz a : Plane → ℂ) = inputComplex a := funext (complexInputSchwartz_apply a)
lemma coe_fourier_input (a : InputCoefficients) :
    ((𝓕 (complexInputSchwartz a) : 𝓢(Plane,ℂ)) : Plane → ℂ) = outputComplex a := by
  rw [SchwartzMap.fourier_coe,coe_complexInputSchwartz,fourier_inputComplex]
lemma outputComplex_real (a : InputCoefficients) (x : Plane) : conj (outputComplex a x) = outputComplex a x := by
  rw [← fourier_inputComplex]
  exact fourier_conj_even _ (inputComplex_real a) (inputComplex_even a) x
lemma pairSchwartz_apply (a₁ a₂ : InputCoefficients) (x : Plane) :
    pairSchwartz a₁ a₂ x = (pairComplex a₁ a₂ x).re := by
  simp only [pairSchwartz,SchwartzMap.postcompCLM_apply,Complex.reCLM_apply,add_apply,
    coe_fourier_input,complexInputSchwartz_apply,pairComplex,Pi.add_apply]
lemma pairComplex_real (a₁ a₂ : InputCoefficients) (x : Plane) : conj (pairComplex a₁ a₂ x) = pairComplex a₁ a₂ x := by
  simp only [pairComplex,Pi.add_apply,map_add,inputComplex_real,outputComplex_real]
lemma pairComplex_eq (a₁ a₂ : InputCoefficients) (x : Plane) :
    pairComplex a₁ a₂ x = (pairSchwartz a₁ a₂ x:ℂ) := by
  rw [pairSchwartz_apply]
  exact (Complex.conj_eq_iff_re.mp (pairComplex_real a₁ a₂ x)).symm
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap lp
open Complex Matrix

namespace AtomicTriangular.Construction

lemma finiteCoordinates_coefficientInput (C : ℝ) (a : TrigonometricCoefficients)
    (w : TailCoefficients) (i : Fin 22) :
    finiteCoordinates (coefficientInput C a w) i = a i := by
  unfold finiteCoordinates coefficientInput
  split_ifs with hi
  · exact congrArg (fun j : Fin 22 => a j) (Fin.ext (by dsimp; omega))
  · exact congrArg (fun j : Fin 22 => a j) (Fin.ext (by dsimp; omega))

lemma actualInput_fixed_zero (side : Fin 2) {z : ℝ} (hz : 0 < z) (hzB : z ≤ Z) :
    (actualInput side z hz hzB).finiteC 0 = 11/25 ∧
    (actualInput side z hz hzB).finiteD 0 = 0 := by
  constructor
  · change finiteApprox side (actualParameter z) 0 +
      extendFiniteError (actualFiniteError side z hz hzB) 0 = 11/25
    erw [finiteApprox_fixed side (actualParameter z) 0,
      extendFiniteError_fixed (actualFiniteError side z hz hzB) 0,
      add_zero, gamma_actual]
    rfl
  · change finiteApprox side (actualParameter z) 1 +
      extendFiniteError (actualFiniteError side z hz hzB) 1 = 0
    erw [finiteApprox_fixed side (actualParameter z) 1,
      extendFiniteError_fixed (actualFiniteError side z hz hzB) 1,
      add_zero, gamma_actual]
    rfl

lemma largeGaussian_hasAtomicConstruction {α : ℝ} (hα : 1 ≤ α) :
    HasAtomicConstruction α (largeGaussianPair hα).first := by
  let z := gaussianZ α
  have hz : 0 < z := (gaussianZ_bounds hα).1
  have hzB : z ≤ Z := (gaussianZ_bounds hα).2.le
  refine ⟨FiniteCertificate.minusBlock_isUnit, FiniteCertificate.plusBlock_isUnit,
    Uplus_equation, Uminus_equation,
    (fun side => actualInput side z hz hzB),
    (fun side i => actualFiniteError side z hz hzB i), ?_, ?_, ?_⟩
  · intro side
    obtain ⟨hc, hd⟩ := actualInput_fixed_zero side hz hzB
    refine ⟨rfl, hc, hd, ?_⟩
    intro i
    dsimp only
    rw [actualInput, finiteCoordinates_coefficientInput]
    rfl
  · intro side
    refine ⟨?_, (actualInput side z hz hzB).summable, ?_⟩
    · simpa only [AtomicTriangular.L1Kernel.l1_norm, tsum_fintype] using
        actualFiniteError_norm_x side hz hzB
    · change (∑' n : TailNode,
        (|actualTail side z hz hzB (n,0)| + |actualTail side z hz hzB (n,1)|)) < _
      rw [tail_pairs_norm]
      exact actualTail_norm_x side hz hzB
  · intro x
    change ((((normalizingDen z)⁻¹ *
        pairSchwartz (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) x : ℝ) : ℂ)) = _
    rw [Complex.ofReal_mul, Complex.ofReal_inv, ← pairComplex_eq, fourier_inputComplex]
    simp only [pairComplex, Pi.add_apply]
    ring

end AtomicTriangular.Construction

namespace AtomicTriangular

theorem sharp_gaussian_minorants_atomic_oai (α : ℝ) (hα : 0 < α) :
    ∃ f : SchwartzMap Plane ℝ,
      Radial f ∧ (∀ x, f x ≤ gaussian α x) ∧
      (∀ w, (realFourier f w).im = 0 ∧ 0 ≤ (realFourier f w).re) ∧
      (∀ a ∈ A, a ≠ 0 → f a = gaussian α a) ∧
      (∀ w ∈ dualA, w ≠ 0 → realFourier f w = 0) ∧
      (1 ≤ α → Construction.HasAtomicConstruction α f) := by
  let p := gaussianPair α hα
  refine ⟨p.first, p.first_radial, p.minorant, ?_, ?_, ?_, ?_⟩
  · intro w
    rw [p.fourier_first]
    exact ⟨rfl, p.positive w⟩
  · intro a ha ha0
    obtain ⟨n, hn⟩ := A_radial_node ha ha0
    exact p.contact a n hn
  · intro w hw hw0
    obtain ⟨n, hn⟩ := dualA_radial_node hw hw0
    rw [p.fourier_first, p.zeros w n hn, ofReal_zero]
  · intro hlarge
    change Construction.HasAtomicConstruction α (gaussianPair α hα).first
    rw [gaussianPair, dite_eq_left hlarge]
    exact Construction.largeGaussian_hasAtomicConstruction hlarge

end AtomicTriangular

end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.sharp_gaussian_minorants_atomic_oai := @OAI.AtomicTriangular.sharp_gaussian_minorants_atomic_oai
