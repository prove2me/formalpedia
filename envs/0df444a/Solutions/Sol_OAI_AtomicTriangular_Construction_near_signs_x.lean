-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.near_signs_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:18:23.421429+00:00
-- url     : https://prove2.me/submissions/d7c836b0-ce53-4236-9f9e-17832e720405

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X011
import Definitions.Def_OAIQ257X020
import Theorems.Thm_OAI_AtomicTriangular_Construction_actualFiniteError_norm_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_actualTail_norm_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_actual_interpolation_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_exceptional_rational_comparison_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_finiteTaylor_error_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_near_negative_polynomial_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_near_positive_polynomial_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_pairJ_curvature_x

section
-- module Solutions.OAIQ250_TR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

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

namespace AtomicTriangular.Interval

lemma RI.mem_invPos {a : RI} {x : ℝ} (hx : a.Mem x) (ha : 0 < a.lo) :
    a.invPos.Mem x⁻¹ := by
  have halo : (0:ℝ) < a.lo := by exact_mod_cast ha
  have hsx : 0 < (scale:ℝ)*x := halo.trans_le hx.1
  have hahi : (0:ℝ) < a.hi := hsx.trans_le hx.2
  have hahi' : (0:ℤ) < a.hi := by exact_mod_cast hahi
  have hl := (div_floor_bounds (scale^2) a.hi hahi').1
  have hu := (div_floor_bounds (scale^2) a.lo ha).2
  push_cast at hl hu
  have hlow : (((scale^2/a.hi:ℤ):ℝ)) ≤ (scale:ℝ)^2/((scale:ℝ)*x) := by
    exact ((le_div_iff₀ hahi).mpr hl).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) hsx hx.2)
  have hupp : (scale:ℝ)^2/((scale:ℝ)*x) ≤ (((scale^2/a.lo+1:ℤ):ℝ)) := by
    exact (div_le_div_of_nonneg_left (sq_nonneg _) halo hx.1).trans
      ((div_le_iff₀ halo).mpr (by simpa only [Int.cast_add,Int.cast_one] using hu))
  have heq : (scale:ℝ)^2/((scale:ℝ)*x) = (scale:ℝ)*x⁻¹ := by
    field_simp [ne_of_gt scale_pos]
  simpa only [heq,RI.Mem,RI.invPos] using And.intro hlow hupp

end AtomicTriangular.Interval

end
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

lemma exponential_apply (f : C(Spectrum,ℂ)) (t : Spectrum) :
    (NormedSpace.exp f) t = exp (f t) := by
  have h := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ t)
    (ContinuousMap.evalCLM ℂ t).continuous f
  simpa only [ContinuousMap.evalAlgHom_apply,Complex.exp_eq_exp_ℂ] using h

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_KernelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma finiteNode_node (i : Fin 10) : 0<finiteNode i ∧ (finiteNode i)%36 ∈ residues := by
  revert i; decide +kernel
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_PolytopeInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma ZBox_mem : ZBox.Mem Z := RI.mem_divNat (RI.mem_point 391) (by norm_num)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma parameterExpBox2_calc :
    (CI.ofReal ((RI.point (-2)).mul ZBox.invPos)).exp.re = parameterExpBox2 := by decide +kernel
lemma parameterExp2_bound : Real.exp (-2/Z) < Wstar := by
  have hx : ((RI.point (-2)).mul ZBox.invPos).Mem (-2/Z) := by
    rw [div_eq_mul_inv]
    exact RI.mem_mul (by simpa using RI.mem_point (-2)) (RI.mem_invPos ZBox_mem (by decide +kernel))
  have hh := (CI.mem_exp_checked (CI.mem_ofReal hx) (by decide +kernel)).1
  rw [parameterExpBox2_calc] at hh
  simp only [Complex.exp_ofReal_re] at hh
  norm_num [RI.Mem,parameterExpBox2,scale,Wstar] at *
  linarith
lemma parameterExpBox3_calc :
    (CI.ofReal ((RI.point (-3)).mul ZBox.invPos)).exp.re = parameterExpBox3 := by decide +kernel
lemma parameterExp3_bound : Real.exp (-3/Z) < Ustar := by
  have hx : ((RI.point (-3)).mul ZBox.invPos).Mem (-3/Z) := by
    rw [div_eq_mul_inv]
    exact RI.mem_mul (by simpa using RI.mem_point (-3)) (RI.mem_invPos ZBox_mem (by decide +kernel))
  have hh := (CI.mem_exp_checked (CI.mem_ofReal hx) (by decide +kernel)).1
  rw [parameterExpBox3_calc] at hh
  simp only [Complex.exp_ofReal_re] at hh
  norm_num [RI.Mem,parameterExpBox3,scale,Ustar] at *
  linarith
lemma parameterExpBox6_calc :
    (CI.ofReal ((RI.point (-6)).mul ZBox.invPos)).exp.re = parameterExpBox6 := by decide +kernel
lemma parameterExp6_bound : Real.exp (-6/Z) < Pstar := by
  have hx : ((RI.point (-6)).mul ZBox.invPos).Mem (-6/Z) := by
    rw [div_eq_mul_inv]
    exact RI.mem_mul (by simpa using RI.mem_point (-6)) (RI.mem_invPos ZBox_mem (by decide +kernel))
  have hh := (CI.mem_exp_checked (CI.mem_ofReal hx) (by decide +kernel)).1
  rw [parameterExpBox6_calc] at hh
  simp only [Complex.exp_ofReal_re] at hh
  norm_num [RI.Mem,parameterExpBox6,scale,Pstar] at *
  linarith
lemma exp_neg_one_bound : Real.exp (-1) < 369/1000 := by
  have he := Real.exp_one_gt_d9
  rw [Real.exp_neg,inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
  linarith
end AtomicTriangular.FiniteCertificate
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

lemma exp_parameter_mono {z : ℝ} (hz : 0<z) (hzB : z≤Z) {k : ℝ} (hk : 0≤k) :
    Real.exp (-k/z) ≤ Real.exp (-k/Z) := by
  apply Real.exp_le_exp.mpr
  rw [neg_div,neg_div,neg_le_neg_iff]
  exact div_le_div_of_nonneg_left hk hz hzB

lemma delta_parameter_bound {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    (Z-z)*Real.exp (-2/z) < DeltaStar := by
  let t : ℝ := 1/z-1/Z
  have ht : 0≤t := sub_nonneg.mpr (one_div_le_one_div_of_le hz hzB)
  have hid : Z-z = Z*z*t := by
    have hZ : Z ≠ 0 := by norm_num [Z]
    dsimp [t]
    field_simp
  have he : Real.exp (-2/z) = Real.exp (-2/Z)*Real.exp (-(2*t)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [t]
    ring
  have h1 : (Z-z)*Real.exp (-2/z) ≤ Z^2*Real.exp (-2/Z)*(t*Real.exp (-(2*t))) := by
    rw [hid,he]
    have hh := mul_le_mul_of_nonneg_left hzB
      (show 0≤Z*t*Real.exp (-2/Z)*Real.exp (-(2*t)) by
        have hZ : 0 < Z := by norm_num [Z]
        positivity)
    nlinarith
  have h2 := Real.mul_exp_neg_le_exp_neg_one (2*t)
  have h3 := mul_le_mul_of_nonneg_left h2
    (show 0≤Z^2*Real.exp (-2/Z) by positivity)
  have h4 := mul_le_mul_of_nonneg_left parameterExp2_bound.le
    (show 0≤Z^2*(369/1000:ℝ) by positivity)
  have h5 := mul_le_mul_of_nonneg_left exp_neg_one_bound.le
    (show 0≤Z^2*Real.exp (-2/Z) by positivity)
  norm_num [Z,Wstar,DeltaStar] at *
  nlinarith
lemma actualParameter_mem {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    ParameterPolytope (actualParameter z) := by
  have hw := (exp_parameter_mono hz hzB (by norm_num : (0:ℝ)≤2)).trans parameterExp2_bound.le
  have hu := (exp_parameter_mono hz hzB (by norm_num : (0:ℝ)≤3)).trans parameterExp3_bound.le
  have hp := (exp_parameter_mono hz hzB (by norm_num : (0:ℝ)≤6)).trans parameterExp6_bound.le
  have hzp : z*Real.exp (-6/z) ≤ Pstar :=
    (mul_le_of_le_one_left (Real.exp_pos _).le (hzB.trans (by norm_num [Z]))).trans hp
  refine ⟨z,Real.exp (-2/z),(Z-z)*Real.exp (-2/z),Real.exp (-3/z),
    z*Real.exp (-3/z),z*Real.exp (-6/z),Real.exp (-6/z),hz.le,hzB,
    (Real.exp_pos _).le,hw,mul_nonneg (sub_nonneg.mpr hzB) (Real.exp_pos _).le,
    (delta_parameter_bound hz hzB).le,(Real.exp_pos _).le,hu,
    mul_nonneg hz.le (Real.exp_pos _).le,mul_le_mul_of_nonneg_right hzB (Real.exp_pos _).le,
    mul_nonneg hz.le (Real.exp_pos _).le,hzp,(Real.exp_pos _).le,hp,?_⟩
  unfold actualParameter
  congr 1
  ring_nf
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

lemma extendFiniteError_norm (u : FiniteCoefficients) : ‖extendFiniteError u‖=‖u‖ := by
  rw [l1_norm,l1_norm,tsum_fintype,tsum_fintype]
  change (∑ i : Fin 22, |if hi : i.val<2 then 0 else u ⟨i.val-2,by omega⟩|)=_
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [Fin.val_zero,Fin.val_succ,show 0<2 by omega,show 0+1<2 by omega,↓reduceDIte,abs_zero,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  simp only [show ¬(i.val+1+1<2) by omega,↓reduceDIte]
  congr 2

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

lemma atomSpectral_apply (S : Fin 31 → ℂ) (f : C(Spectrum,ℂ)) :
    atomSpectral S f = ∑ j : Fin 31, S j*f ⟨frequency j,frequency_mem j⟩ := by
  simp [atomSpectral]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_WaveFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma wavePhaseFunction_apply (q br : Fin 2) (t : Spectrum) :
    wavePhaseFunction q br t=taylorPhase q br t.val := by
  fin_cases br <;> rfl
lemma waveAmplitudeFunction_apply (q br : Fin 2) (t : Spectrum) :
    waveAmplitudeFunction q br t=taylorAmplitude q br t.val := by
  fin_cases br <;> rfl

lemma waveFunctionJet_apply (q br : Fin 2) (k : ℕ) (s : ℂ) (t : Spectrum) :
    waveFunctionJet q br k s t=finiteWaveJet q br t.val k s := by
  simp only [waveFunctionJet,ContinuousMap.mul_apply,ContinuousMap.pow_apply,
    exponential_apply,ContinuousMap.smul_apply,smul_eq_mul,wavePhaseFunction_apply,
    waveAmplitudeFunction_apply,finiteWaveJet,mul_comm s]
lemma hasDerivAt_waveFunctionJet (q br : Fin 2) (k : ℕ) (s : ℂ) :
    HasDerivAt (waveFunctionJet q br k) (waveFunctionJet q br (k+1) s) s := by
  have hh := ((hasDerivAt_exp_smul_const (wavePhaseFunction q br) s).const_mul
    (waveAmplitudeFunction q br)).mul_const ((wavePhaseFunction q br)^k)
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (try simp only [waveFunctionJet,pow_succ])
  all_goals first | rfl | (ext t; simp [ContinuousMap.mul_apply,ContinuousMap.pow_apply]; ring)
lemma hasDerivAt_inputJJet (a : InputCoefficients) (br : Fin 2) (k : ℕ) (s : ℂ) :
    HasDerivAt (inputJJet a br k) (inputJJet a br (k+1) s) s := by
  exact ((tailSpectral a).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_waveFunctionJet 0 br k s)).add
    ((finiteSpectral a).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_waveFunctionJet 1 br k s))
lemma hasDerivAt_pairJJet (a₁ a₂ : InputCoefficients) (k : ℕ) (s : ℂ) :
    HasDerivAt (pairJJet a₁ a₂ k) (pairJJet a₁ a₂ (k+1) s) s :=
  (hasDerivAt_inputJJet a₁ 0 k s).add (hasDerivAt_inputJJet a₂ 1 k s)
lemma pairJ_contDiff (a₁ a₂ : InputCoefficients) : ContDiff ℝ ⊤ (pairJ a₁ a₂) := by
  have hh : Differentiable ℂ (pairJJet a₁ a₂ 0) := fun s => (hasDerivAt_pairJJet a₁ a₂ 0 s).differentiableAt
  exact hh.contDiff.real_of_complex
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_CoefficientSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open Complex AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate
lemma finiteColumn_even (j : Fin 11) (l : Fin 31) :
    finiteColumn ⟨2*j.val,by omega⟩ l=cCoefficient ⟨j.val,by omega⟩ l := by
  simp only [finiteColumn,show 2*j.val<22 by omega,↓reduceDIte,
    show 2*j.val%2=0 by omega,↓reduceIte]
  congr 2
  omega
lemma finiteColumn_odd (j : Fin 11) (l : Fin 31) :
    finiteColumn ⟨2*j.val+1,by omega⟩ l=dCoefficient ⟨j.val,by omega⟩ l := by
  simp only [finiteColumn,show 2*j.val+1<22 by omega,↓reduceDIte,
    show ¬((2*j.val+1)%2=0) by omega,↓reduceIte]
  congr 2
  omega
lemma sum_fin22_pairs {M : Type*} [AddCommMonoid M] (g : Fin 22 → M) :
    (∑ c : Fin 22, g c)=∑ j : Fin 11, (g ⟨2*j.val,by omega⟩+g ⟨2*j.val+1,by omega⟩) := by
  have hh := (finProdFinEquiv (m:=11) (n:=2)).sum_comp g
  rw [Fintype.sum_prod_type] at hh
  simp only [Fin.sum_univ_two] at hh
  convert hh.symm using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro i _
  congr 2 <;> apply Fin.ext <;> simp [finProdFinEquiv, mul_comm, add_comm]
lemma finiteSpectral_coefficient (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients) :
    finiteSpectral (coefficientInput C a w)=∑ c : Fin 22,
      (a c:ℂ) • atomSpectral (finiteColumn ⟨c.val,by omega⟩) := by
  rw [sum_fin22_pairs]
  simp only [finiteSpectral,coefficientInput]
  apply Finset.sum_congr rfl
  intro j _
  congr 2 <;> congr 1 <;> funext l
  · exact (finiteColumn_even j l).symm
  · exact (finiteColumn_odd j l).symm
lemma finiteSpectral_coefficient_apply (C : ℝ) (a : TrigonometricCoefficients)
    (w : TailCoefficients) (f : C(Spectrum,ℂ)) :
    finiteSpectral (coefficientInput C a w) f=∑ c : Fin 22,
      (a c:ℂ)*(∑ j : Fin 31, finiteColumn ⟨c.val,by omega⟩ j*f ⟨frequency j,frequency_mem j⟩) := by
  rw [finiteSpectral_coefficient]
  simp only [sum_apply,smul_apply,smul_eq_mul,atomSpectral_apply]
lemma tailSpectral_coefficient (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients) :
    tailSpectral (coefficientInput C a w)= (C:ℂ) • spectralPCLM+
      ∑' n : TailNode, ((w (n,0):ℂ) • spectralCCLM n.val+(w (n,1):ℂ) • spectralDCLM n.val) := rfl
lemma tailSpectral_zero_coeff (C : ℝ) (a : TrigonometricCoefficients) :
    tailSpectral (coefficientInput C a 0)=(C:ℂ) • spectralPCLM := by
  ext f
  simp [tailSpectral_apply,coefficientInput,spectralPCLM_apply]
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
lemma gamma_actual (side : Fin 2) (z : ℝ) :
    (gamma side *ᵥ actualParameter z)= ![11/25,0,if side.val=0 then -(3/500) else 3/500] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,gamma,Fin.sum_univ_succ,actualParameter]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_ActualInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
lemma gaussianG_deriv {z : ℝ} (hz : 0<z) (s : ℝ) :
    HasDerivAt (gaussianG z) (-Q 1*Real.exp ((1-s)/z)) s := by
  have hh := ((((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).div_const z).exp.const_mul (Q 1*z))
  convert hh using 1 <;> first | rfl | (simp only [Pi.sub_apply,id_eq]; field_simp; ring)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_FinitePairBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
lemma Acoefficient_constant (side : Fin 2) (r : Fin 8) : Acoefficient side 22 r=gamma side 2 r := by
  simp [Acoefficient]
lemma finiteSpectrum_dot (side q : Fin 2) (j : Fin 31) (e : Fin 8 → ℝ) :
    (∑ r : Fin 8,(e r:ℂ)*finiteSpectrum side q j r)=
      if q.val=0 then ((gamma side *ᵥ e) 2:ℂ)*fourierCoeff j
      else ∑ c : Fin 22,(finiteApprox side e c:ℂ)*finiteColumn ⟨c.val,by omega⟩ j := by
  by_cases hq : q.val=0
  · simp only [finiteSpectrum,hq,↓reduceIte,Acoefficient_constant,Matrix.mulVec,dotProduct,
      ofReal_sum,ofReal_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    ring
  · simp only [finiteSpectrum,hq,↓reduceIte,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    change (∑ r : Fin 8,(e r:ℂ)*(finiteColumn ⟨c.val,by omega⟩ j*(Acoefficient side ⟨c.val,by omega⟩ r:ℂ)))=
      ((∑ r : Fin 8,Acoefficient side ⟨c.val,by omega⟩ r*e r:ℝ):ℂ)*finiteColumn ⟨c.val,by omega⟩ j
    simp only [ofReal_sum,ofReal_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    ring
lemma finiteSpectrum_input (side : Fin 2) (e : Fin 8 → ℝ) (br : Fin 2) (k : ℕ) (s : ℂ) :
    (∑ q : Fin 2,∑ j : Fin 31,(∑ r : Fin 8,(e r:ℂ)*finiteSpectrum side q j r)*finiteWaveJet q br (frequency j) k s)=
      inputJJet (coefficientInput ((gamma side *ᵥ e) 2) (finiteApprox side e) 0) br k s := by
  simp only [finiteSpectrum_dot,Fin.sum_univ_two,Fin.val_zero,Fin.val_one,Nat.one_ne_zero,↓reduceIte]
  rw [inputJJet,tailSpectral_zero_coeff,finiteSpectral_coefficient_apply]
  simp only [_root_.smul_apply,smul_eq_mul,spectralPCLM_apply,spectralP,
    waveFunctionJet_apply,Finset.mul_sum,Finset.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro j _
    ring
lemma finiteJJet_pair (side : Fin 2) (e : Fin 8 → ℝ) (k : ℕ) (s : ℂ) :
    finiteJJet side e k s=
      pairJJet (coefficientInput ((gamma side *ᵥ e) 2) (finiteApprox side e) 0)
        (coefficientInput ((gamma (otherSide side) *ᵥ e) 2) (finiteApprox (otherSide side) e) 0) k s := by
  unfold finiteJJet
  simp only [Finset.mul_sum,mul_add,Finset.sum_add_distrib,←mul_assoc]
  rw [Finset.sum_comm (f:=fun r q => ∑ j : Fin 31,(e r:ℂ)*finiteSpectrum side q j r*finiteWaveJet q 0 (frequency j) k s)]
  rw [Finset.sum_comm (f:=fun r q => ∑ j : Fin 31,(e r:ℂ)*finiteSpectrum (otherSide side) q j r*finiteWaveJet q 1 (frequency j) k s)]
  simp_rw [Finset.sum_comm (f:=fun r j => (e r:ℂ)*finiteSpectrum side _ j r*finiteWaveJet _ 0 (frequency j) k s),←Finset.sum_mul]
  simp_rw [Finset.sum_comm (f:=fun r j => (e r:ℂ)*finiteSpectrum (otherSide side) _ j r*finiteWaveJet _ 1 (frequency j) k s),←Finset.sum_mul]
  rw [finiteSpectrum_input,finiteSpectrum_input]
  rfl
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_CoefficientAddition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
lemma inputJJet_split (C : ℝ) (a da : TrigonometricCoefficients) (w : TailCoefficients) (br : Fin 2) (k : ℕ) (s : ℂ) :
    inputJJet (coefficientInput C (a+da) w) br k s=
      inputJJet (coefficientInput C a 0) br k s+inputJJet (coefficientInput 0 da w) br k s := by
  have hzero (T : C(Spectrum,ℂ) →L[ℂ] ℂ) : (0:ℂ) • T=0 := by
    ext f
    exact zero_mul _
  simp only [hzero,inputJJet,tailSpectral_coefficient,finiteSpectral_coefficient_apply,
    lp.coeFn_add,lp.coeFn_zero,Pi.zero_apply,add_zero,tsum_zero,Pi.add_apply,ofReal_add,ofReal_zero,zero_add,_root_.add_apply,
    _root_.smul_apply,smul_eq_mul,add_mul,Finset.sum_add_distrib]
  ring
lemma gamma_actual_constant (side : Fin 2) (z : ℝ) :
    (gamma side *ᵥ actualParameter z) 2=if side.val=0 then -(3/500:ℝ) else 3/500 := by
  rw [gamma_actual]
  rfl
lemma actualJ_split (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    actualJ side z hz hzB = finiteJ side (actualParameter z)+
      pairJ (coefficientInput 0 (extendFiniteError (actualFiniteError side z hz hzB)) (actualTail side z hz hzB))
        (coefficientInput 0 (extendFiniteError (actualFiniteError (otherSide side) z hz hzB)) (actualTail (otherSide side) z hz hzB)) := by
  funext s
  simp only [Pi.add_apply,actualJ,actualInput,actualTrigonometric,finiteJ,finiteJJet_pair,pairJ,pairJJet,inputJJet_split,gamma_actual_constant]
  simp only [add_re]
  ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_DeletedQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction

lemma taylor_one_eval {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {m s : ℝ} (hms : m≠s) :
    taylorWithinEval f 1 (uIcc m s) m s=f m+deriv f m*(s-m) := by
  have he : iteratedDerivWithin 1 f (uIcc m s) m=iteratedDeriv 1 f m :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hms)
      (hf.of_le (by norm_num)).contDiffAt (left_mem_uIcc)
  rw [show (1:ℕ)=0+1 from rfl,taylorWithinEval_succ,he]
  simp [mul_comm]

lemma deletedSecond_eq_at_mean {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {m s : ℝ} (hms : m≠s) :
    ∃ c∈uIoo m s,deletedSecond f m s=iteratedDeriv 2 f c/2 := by
  obtain ⟨c,hc,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n:=1) hms hf.contDiffOn
  refine ⟨c,hc,?_⟩
  rw [taylor_one_eval hf hms] at he
  have hn : s-m≠0 := sub_ne_zero.mpr hms.symm
  rw [deletedSecond,ite_eq_right hms.symm]
  norm_num at he
  apply (div_eq_iff (pow_ne_zero 2 hn)).mpr
  linarith

lemma deletedSecond_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {m s C : ℝ}
    (hb : ∀ t∈uIcc m s,|iteratedDeriv 2 f t|≤C) : |deletedSecond f m s|≤C/2 := by
  by_cases h : m=s
  · subst s
    rw [deletedSecond,ite_eq_left rfl,abs_div,show |(2:ℝ)|=2 by norm_num]
    exact div_le_div_of_nonneg_right (hb m (left_mem_uIcc)) (by norm_num)
  · obtain ⟨c,hc,he⟩ := deletedSecond_eq_at_mean hf h
    rw [he,abs_div,show |(2:ℝ)|=2 by norm_num]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact hb c (Ioo_subset_Icc_self hc)

lemma deletedSecond_of_jets {f : ℝ → ℝ} {m s : ℝ} (hfm : f m=0) (hdfm : deriv f m=0)
    (hsm : s≠m) : deletedSecond f m s=f s/(s-m)^2 := by
  simp [deletedSecond,hsm,hfm,hdfm]

lemma real_function_nonneg_of_deleted {f : ℝ → ℝ} {m s : ℝ} (hfm : f m=0)
    (hdfm : deriv f m=0) (hb : 0≤deletedSecond f m s) : 0≤f s := by
  by_cases hsm : s=m
  · simp [hsm,hfm]
  · rw [deletedSecond_of_jets hfm hdfm hsm] at hb
    simpa only [zero_mul] using (le_div_iff₀ (sq_pos_of_ne_zero (sub_ne_zero.mpr hsm))).mp hb
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_DeletedAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma deletedSecond_add {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (m s : ℝ) :
    deletedSecond (f+g) m s=deletedSecond f m s+deletedSecond g m s := by
  unfold deletedSecond
  split_ifs with hs
  · rw [iteratedDeriv_add hf.contDiffAt hg.contDiffAt]
    ring
  · rw [deriv_add (hf.differentiable (by norm_num) m) (hg.differentiable (by norm_num) m)]
    simp only [Pi.add_apply]
    ring
lemma finiteJ_contDiff (side : Fin 2) (e : Fin 8 → ℝ) : ContDiff ℝ ⊤ (finiteJ side e) := by
  have he : finiteJ side e=pairJ (coefficientInput ((gamma side *ᵥ e) 2) (finiteApprox side e) 0)
      (coefficientInput ((gamma (otherSide side) *ᵥ e) 2) (finiteApprox (otherSide side) e) 0) := by
    funext s; exact congrArg Complex.re (finiteJJet_pair side e 0 s)
  rw [he]
  exact pairJ_contDiff _ _
lemma nearDisplacement_radius (n : Fin 7) (y : Fin 2) : |nearDisplacement n y| ≤ nearRadius n := by
  fin_cases n <;> fin_cases y <;> (first | (simp [nearDisplacement,nearDisplacementNum,nearRadius,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]; all_goals first | (norm_num [nearDisplacement,nearDisplacementNum,nearRadius,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]; done) | rfl | decide) | (norm_num [nearDisplacement,nearDisplacementNum,nearRadius,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]; done) | norm_num [nearDisplacement,nearDisplacementNum,nearRadius,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail])
lemma nearDisplacement_mul_radius (n : Fin 7) (y : Fin 2) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    |nearDisplacement n y*τ| ≤ nearRadius n := by
  rw [abs_mul,abs_of_nonneg hτ.1]
  exact (mul_le_of_le_one_right (abs_nonneg _) hτ.2).trans (nearDisplacement_radius n y)
lemma nearBase_le_node (n : Fin 7) (y : Fin 2) : curvaturePoint (nearBase n y) ≤ (nearNode n:ℝ) := by
  fin_cases n <;> fin_cases y <;> (first | (simp [nearBase,curvaturePoint,nearNode,finiteNode,residue,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]; all_goals first | (norm_num [nearBase,curvaturePoint,nearNode,finiteNode,residue,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]; done) | rfl | decide) | (norm_num [nearBase,curvaturePoint,nearNode,finiteNode,residue,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]; done) | norm_num [nearBase,curvaturePoint,nearNode,finiteNode,residue,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail])
lemma nearBase_le_cell (n : Fin 7) (y : Fin 2) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    curvaturePoint (nearBase n y) ≤ (nearNode n:ℝ)+nearDisplacement n y*τ := by
  obtain ⟨ht0,ht1⟩ := hτ
  fin_cases n <;> fin_cases y <;> norm_num [nearBase,curvaturePoint,nearNode,finiteNode,residue,nearDisplacement,nearDisplacementNum,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail] <;> linarith
lemma near_error_arithmetic (n : Fin 7) (y : Fin 2) :
    (1/100000:ℝ)*finiteCurvatureEnvelope (nearBase n y)+(3/1000000000)*tailCurvatureEnvelope (nearBase n y)+
      (if n.val=0 then (161/100000:ℝ) else 75/10000000)<nearError n y := by
  fin_cases n <;> fin_cases y <;> (first | (simp [nearBase,nearError,finiteCurvatureEnvelope,tailCurvatureEnvelope,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]; all_goals first | (norm_num [nearBase,nearError,finiteCurvatureEnvelope,tailCurvatureEnvelope,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]; done) | rfl | decide) | (norm_num [nearBase,nearError,finiteCurvatureEnvelope,tailCurvatureEnvelope,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]; done) | norm_num [nearBase,nearError,finiteCurvatureEnvelope,tailCurvatureEnvelope,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail])
lemma deleted_accuracy (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) (n : Fin 7) (y : Fin 2) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    |deletedSecond (actualJ side z hz hzB) (nearNode n) (nearNode n+nearDisplacement n y*τ)-
      finiteTaylor side (nearNode n) (nearDisplacement n y) (actualParameter z) τ|<nearError n y := by
  let corr := pairJ (coefficientInput 0 (extendFiniteError (actualFiniteError side z hz hzB)) (actualTail side z hz hzB))
      (coefficientInput 0 (extendFiniteError (actualFiniteError (otherSide side) z hz hzB)) (actualTail (otherSide side) z hz hzB))
  let K : ℝ := (1/100000)*finiteCurvatureEnvelope (nearBase n y)+(3/1000000000)*tailCurvatureEnvelope (nearBase n y)
  have hb : |deletedSecond corr (nearNode n) (nearNode n+nearDisplacement n y*τ)| ≤ K := by
    have hh := deletedSecond_bound (f:=corr) ((pairJ_contDiff _ _).of_le (by norm_num))
      (m:=(nearNode n:ℝ)) (s:=(nearNode n:ℝ)+nearDisplacement n y*τ) (C:=2*K) ?_
    · linarith
    · intro t ht
      have htB : curvaturePoint (nearBase n y) ≤ t := (le_min (nearBase_le_node n y) (nearBase_le_cell n y hτ)).trans ht.1
      have ha (side : Fin 2) : ‖extendFiniteError (actualFiniteError side z hz hzB)‖ ≤ (1/100000:ℝ) := by
        rw [extendFiniteError_norm]
        simpa only [show (10:ℝ)^5=100000 by norm_num] using (actualFiniteError_norm_x side hz hzB).le
      have hh := pairJ_curvature_x _ _ _ _ (nearBase n y) htB (ha side) (ha (otherSide side))
        (actualTail_norm_x side hz hzB).le (actualTail_norm_x (otherSide side) hz hzB).le
      norm_num at hh
      change |iteratedDeriv 2 corr t|/2 ≤ K at hh
      linarith
  rw [actualJ_split,deletedSecond_add ((finiteJ_contDiff _ _).of_le (by norm_num)) ((pairJ_contDiff _ _).of_le (by norm_num))]
  have he := finiteTaylor_error_x side hz hzB n (nearDisplacement_mul_radius n y hτ)
  have hh := abs_add_le (deletedSecond (finiteJ side (actualParameter z)) (nearNode n) (nearNode n+nearDisplacement n y*τ)-finiteTaylor side (nearNode n) (nearDisplacement n y) (actualParameter z) τ)
    (deletedSecond corr (nearNode n) (nearNode n+nearDisplacement n y*τ))
  have htab := near_error_arithmetic n y
  dsimp only [K] at hb
  convert lt_of_le_of_lt hh (by linarith) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_GaussianDeleted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace AtomicTriangular.Construction
lemma gaussianG_contDiff (z : ℝ) : ContDiff ℝ ⊤ (gaussianG z) := by unfold gaussianG; fun_prop
lemma gaussianG_second {z : ℝ} (hz : 0<z) (s : ℝ) :
    iteratedDeriv 2 (gaussianG z) s=Q 1/z*Real.exp ((1-s)/z) := by
  rw [show 2=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one]
  have he : deriv (gaussianG z)=fun t => -Q 1*Real.exp ((1-t)/z) := funext fun t => (gaussianG_deriv hz t).deriv
  rw [he]
  have hh := ((((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).div_const z).exp.const_mul (-Q 1))
  convert hh.deriv using 1 <;> first | rfl | (simp only [Pi.sub_apply,id_eq]; ring)
lemma deletedSecond_lower {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (m s L : ℝ)
    (hb : ∀ t∈uIcc m s,L ≤ iteratedDeriv 2 f t/2) : L ≤ deletedSecond f m s := by
  by_cases hms : m=s
  · subst s
    simpa [deletedSecond] using hb m (left_mem_uIcc)
  · obtain ⟨c,hc,he⟩ := deletedSecond_eq_at_mean hf hms
    rw [he]
    exact hb c (Ioo_subset_Icc_self hc)
lemma gaussian_deleted_nonneg {z : ℝ} (hz : 0<z) (m v : ℝ) :
    0 ≤ deletedSecond (gaussianG z) m (m+v) := by
  apply deletedSecond_lower ((gaussianG_contDiff z).of_le (by norm_num))
  intro t _
  rw [gaussianG_second hz]
  exact div_nonneg (mul_nonneg (div_nonneg Q_one_pos.le hz.le) (Real.exp_pos _).le) (by norm_num)
lemma gaussian_deleted_left {z m v : ℝ} (hz : 0<z) (hv : v ≤ 0) :
    Q 1*Real.exp ((1-m)/z)/(2*z) ≤ deletedSecond (gaussianG z) m (m+v) := by
  apply deletedSecond_lower ((gaussianG_contDiff z).of_le (by norm_num))
  intro t ht
  have htm : t ≤ m := by
    have hh := ht.2
    rw [max_eq_left (by linarith : m+v ≤ m)] at hh
    exact hh
  rw [gaussianG_second hz]
  have he : Real.exp ((1-m)/z) ≤ Real.exp ((1-t)/z) := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hz.le)
  have hh := mul_le_mul_of_nonneg_left he (div_nonneg Q_one_pos.le hz.le)
  convert div_le_div_of_nonneg_right hh (by norm_num : (0:ℝ) ≤ 2) using 1 <;> first | rfl | ring

lemma pade0_deriv (x : ℝ) : HasDerivAt pade0 (pade1 x) x := by
  have he := ((hasDerivAt_id x).neg).exp
  have hp := (((hasDerivAt_const x (6:ℝ)).add ((hasDerivAt_id x).const_mul 4)).add ((hasDerivAt_id x).pow 2))
  have hh := ((he.mul hp).sub_const 6).add ((hasDerivAt_id x).const_mul 2)
  convert hh using 1 <;> first | rfl | (dsimp [pade1]; ring)
lemma pade1_deriv (x : ℝ) : HasDerivAt pade1 (x^2*Real.exp (-x)) x := by
  have he := ((hasDerivAt_id x).neg).exp
  have hp := (((hasDerivAt_const x (2:ℝ)).add ((hasDerivAt_id x).const_mul 2)).add ((hasDerivAt_id x).pow 2))
  have hh := (he.mul hp).const_sub 2
  convert hh using 1 <;> first | rfl | (dsimp; ring)
lemma pade1_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ pade1 x := by
  have hm := monotone_of_hasDerivAt_nonneg pade1_deriv (fun t => mul_nonneg (sq_nonneg t) (Real.exp_pos _).le)
  have hh := hm hx
  simpa [pade1] using hh
lemma pade0_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ pade0 x := by
  have hm : MonotoneOn pade0 (Ici 0) := monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (by unfold pade0; fun_prop) (fun s _ => (pade0_deriv s).differentiableAt.differentiableWithinAt)
    (fun s hs => by rw [(pade0_deriv s).deriv]; exact pade1_nonneg (interior_subset hs))
  have hh := hm (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
  simpa [pade0] using hh
lemma pade_rational {x : ℝ} (hx : 0<x) :
    (3+x)/(6+4*x+x^2) ≤ (Real.exp (-x)-1+x)/x^2 := by
  have hd : 0<6+4*x+x^2 := by positivity
  rw [div_le_div_iff₀ hd (sq_pos_of_pos hx)]
  have hh := pade0_nonneg hx.le
  dsimp [pade0] at hh
  nlinarith
lemma gaussian_deleted_formula {z m v : ℝ} (hz : 0<z) (hv : v≠0) :
    deletedSecond (gaussianG z) m (m+v)=
      Q 1*z*Real.exp ((1-m)/z)*(Real.exp (-v/z)-1+v/z)/v^2 := by
  rw [deletedSecond,ite_eq_right (by intro hh; apply hv; linarith : m+v≠m),(gaussianG_deriv hz m).deriv]
  simp only [gaussianG]
  rw [show (1-(m+v))/z=(1-m)/z+(-v/z) by ring,Real.exp_add]
  field_simp [hz.ne',hv]
  ring
lemma gaussian_deleted_right {z m v : ℝ} (hz : 0<z) (hv : 0 ≤ v) :
    Q 1*Real.exp ((1-m)/z)*((3*z+v)/(6*z^2+4*z*v+v^2)) ≤
      deletedSecond (gaussianG z) m (m+v) := by
  rcases hv.eq_or_lt with hv|hv
  · subst v
    simp only [add_zero,deletedSecond,ite_true, if_true]
    rw [gaussianG_second hz]
    apply le_of_eq
    field_simp [hz.ne']
    ring
  · rw [gaussian_deleted_formula hz hv.ne']
    have hQ := Q_one_pos
    have hh := mul_le_mul_of_nonneg_left (pade_rational (div_pos hv hz))
      (show 0 ≤ Q 1*Real.exp ((1-m)/z)/z by positivity)
    have hz0 := hz.ne'
    have hv0 := hv.ne'
    have hd : 6*z^2+4*z*v+v^2≠0 := ne_of_gt (by positivity)
    convert hh using 1 <;> first | rfl | field_simp [hz0,hv0,hd]
lemma gaussian_deleted_three {z v : ℝ} (hz : 0<z) (hzB : z ≤ Z) (hv : v ≤ 1/2) :
    (4/5)*Q 1*Real.exp (-2/z) ≤ deletedSecond (gaussianG z) 3 (3+v) := by
  have hzBound : z ≤ 391/1000 := hzB
  have hq : 0 ≤ Q 1*Real.exp (-2/z) := mul_nonneg Q_one_pos.le (Real.exp_pos _).le
  by_cases hv0 : v ≤ 0
  · have hh := gaussian_deleted_left (m:=3) hz hv0
    norm_num at hh
    have hr : (4/5:ℝ) ≤ 1/(2*z) := (le_div_iff₀ (by positivity)).mpr (by linarith)
    have hl := mul_le_mul_of_nonneg_left hr hq
    have he : Q 1*Real.exp (-2/z)*(1/(2*z))=Q 1*Real.exp (-2/z)/(2*z) := by ring
    rw [he] at hl
    convert hl.trans hh using 1 <;> first | rfl | ring
  · have hv0 : 0<v := lt_of_not_ge hv0
    have hd : 0<6*z^2+4*z*v+v^2 := by positivity
    have hz2 : z^2 ≤ (391/1000)*z := by nlinarith
    have hv2 : v^2 ≤ (1/2)*v := by nlinarith
    have hzv : z*v ≤ (1/2)*z := by nlinarith
    have hzv' : z*v ≤ (391/1000)*v := by nlinarith
    have hr : (4/5:ℝ) ≤ (3*z+v)/(6*z^2+4*z*v+v^2) := by
      rw [le_div_iff₀ hd]
      nlinarith
    have hh := gaussian_deleted_right (m:=3) hz hv0.le
    norm_num at hh
    convert (mul_le_mul_of_nonneg_left hr hq).trans hh using 1 <;> first | rfl | ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_OrdinaryComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma ordinaryOffset_actual (n : Fin 7) (z : ℝ) :
    (∑ r : Fin 8,ordinaryOffset n r*actualParameter z r)=
      if n.val=0 then Q 1/(2*Z) else if n.val=1 then (4/5)*Q 1*Real.exp (-2/z) else 0 := by
  fin_cases n <;> (first | (simp [ordinaryOffset,actualParameter,Fin.sum_univ_succ]; all_goals first | (norm_num [ordinaryOffset,actualParameter,Fin.sum_univ_succ]; done) | rfl | decide) | (norm_num [ordinaryOffset,actualParameter,Fin.sum_univ_succ]; done) | norm_num [ordinaryOffset,actualParameter,Fin.sum_univ_succ])
lemma gaussian_ordinary_lower {z : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Fin 7) (y : Fin 2) (hne : ¬(n=0 ∧ y=1)) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    (∑ r : Fin 8,ordinaryOffset n r*actualParameter z r) ≤
      deletedSecond (gaussianG z) (nearNode n) (nearNode n+nearDisplacement n y*τ) := by
  rw [ordinaryOffset_actual]
  by_cases hn0 : n=0
  · subst n
    have hy : y=0 := by fin_cases y <;> simp_all
    subst y
    norm_num [nearNode,finiteNode,residue,nearDisplacement,nearDisplacementNum]
    have hh := gaussian_deleted_left (m:=1) hz (neg_nonpos.mpr hτ.1)
    norm_num at hh
    have hd := div_le_div_of_nonneg_left Q_one_pos.le (show 0<2*z by positivity) (show 2*z ≤ 2*Z by linarith)
    exact hd.trans hh
  · have hnval : n.val≠0 := by exact fun hh => hn0 (Fin.ext hh)
    simp only [hnval,ite_false, if_false]
    by_cases hn1 : n=1
    · subst n
      simp only [Fin.val_one,ite_true, if_true]
      have hv : nearDisplacement 1 y*τ ≤ 1/2 := by
        fin_cases y <;> norm_num[nearDisplacement,nearDisplacementNum] <;> nlinarith [hτ.1,hτ.2]
      have hh := gaussian_deleted_three hz hzB hv
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      norm_num [nearNode,finiteNode,residue]
    · have hnval1 : n.val≠1 := by exact fun hh => hn1 (Fin.ext hh)
      simp only [hnval1,ite_false, if_false]
      exact gaussian_deleted_nonneg hz _ _
lemma near_positive_deleted {z : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Fin 7) (y : Fin 2) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    0 ≤ deletedSecond (actualJ 1 z hz hzB) (nearNode n) (nearNode n+nearDisplacement n y*τ) := by
  have hh := near_positive_polynomial_x (actualParameter z) (actualParameter_mem hz hzB) n y hτ
  have he := (abs_lt.mp (deleted_accuracy 1 hz hzB n y hτ)).1
  linarith
lemma near_ordinary_deleted {z : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Fin 7) (y : Fin 2) (hne : ¬(n=0 ∧ y=1)) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    deletedSecond (actualJ 0 z hz hzB) (nearNode n) (nearNode n+nearDisplacement n y*τ) ≤
      deletedSecond (gaussianG z) (nearNode n) (nearNode n+nearDisplacement n y*τ) := by
  have hh := near_negative_polynomial_x (actualParameter z) (actualParameter_mem hz hzB) n y hne hτ
  have he := (abs_lt.mp (deleted_accuracy 0 hz hzB n y hτ)).2
  have hg := gaussian_ordinary_lower hz hzB n y hne hτ
  linarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_NearSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma real_function_le_of_deleted {f g : ℝ → ℝ} {m s : ℝ}
    (hv : f m=g m) (hd : deriv f m=deriv g m)
    (hb : deletedSecond f m s ≤ deletedSecond g m s) : f s ≤ g s := by
  by_cases hsm : s=m
  · simpa [hsm] using hv.le
  · simp only [deletedSecond,hsm,ite_false, if_false] at hb
    have hh := (div_le_div_iff_of_pos_right (sq_pos_of_ne_zero (sub_ne_zero.mpr hsm))).mp hb
    rw [hv,hd] at hh
    linarith
lemma near_exceptional_deleted {z : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    {τ : ℝ} (hτ : τ∈Icc 0 1) :
    deletedSecond (actualJ 0 z hz hzB) 1 (1+τ) ≤ deletedSecond (gaussianG z) 1 (1+τ) := by
  have he := (abs_lt.mp (deleted_accuracy 0 hz hzB 0 1 hτ)).2
  have hg := gaussian_deleted_right (m:=1) hz hτ.1
  have ht := exceptional_rational_comparison_x (actualParameter z) (actualParameter_mem hz hzB) hτ hz hzB
  change finiteTaylor 0 1 1 (actualParameter z) τ+3/1000 ≤ _ at ht
  norm_num [nearNode,finiteNode,residue,nearDisplacement,nearDisplacementNum,nearError] at he
  norm_num at hg
  change _ ≤ Q 1*((3*z+τ)/(6*z^2+4*z*τ+τ^2)) at ht
  linarith
lemma near_deleted {z : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Fin 7) (y : Fin 2) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    deletedSecond (actualJ 0 z hz hzB) (nearNode n) (nearNode n+nearDisplacement n y*τ) ≤
      deletedSecond (gaussianG z) (nearNode n) (nearNode n+nearDisplacement n y*τ) := by
  by_cases he : n=0 ∧ y=1
  · rcases he with ⟨rfl,rfl⟩
    simpa [nearNode,finiteNode,residue,nearDisplacement,nearDisplacementNum] using near_exceptional_deleted hz hzB hτ
  · exact near_ordinary_deleted hz hzB n y he hτ
lemma nearCell_signs {z : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Fin 7) (y : Fin 2) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    actualJ 0 z hz hzB (nearNode n+nearDisplacement n y*τ) ≤ gaussianG z (nearNode n+nearDisplacement n y*τ) ∧
      0 ≤ actualJ 1 z hz hzB (nearNode n+nearDisplacement n y*τ) := by
  have hn : 0<nearNode n ∧ nearNode n%36∈residues := finiteNode_node ⟨n.val,by omega⟩
  have hj := actual_interpolation_x hz hzB ⟨nearNode n,hn⟩
  exact ⟨real_function_le_of_deleted hj.1 hj.2.1 (near_deleted hz hzB n y hτ),
    real_function_nonneg_of_deleted hj.2.2.1 hj.2.2.2 (near_positive_deleted hz hzB n y hτ)⟩
lemma near_cell_cover {s : ℝ} (hs : s∈Icc 0 (29/2)) :
    ∃ (n : Fin 7) (y : Fin 2) (τ : ℝ),τ∈Icc 0 1 ∧ s=nearNode n+nearDisplacement n y*τ := by
  by_cases h0 : s ≤ 1
  · refine ⟨0,0,(s-1)/(-1),?_,?_⟩
    · constructor <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (0:Fin 7)=(1:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (0:Fin 7) (0:Fin 2)=(-2:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h1 : s ≤ 2
  · refine ⟨0,1,(s-1)/1,?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (0:Fin 7)=(1:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (0:Fin 7) (1:Fin 2)=(2:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h2 : s ≤ 3
  · refine ⟨1,0,(s-3)/(-1),?_,?_⟩
    · constructor <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (1:Fin 7)=(3:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (1:Fin 7) (0:Fin 2)=(-2:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h3 : s ≤ (7/2)
  · refine ⟨1,1,(s-3)/(1/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (1:Fin 7)=(3:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (1:Fin 7) (1:Fin 2)=(1:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h4 : s ≤ 4
  · refine ⟨2,0,(s-4)/(-1/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (2:Fin 7)=(4:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (2:Fin 7) (0:Fin 2)=(-1:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h5 : s ≤ (11/2)
  · refine ⟨2,1,(s-4)/(3/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (2:Fin 7)=(4:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (2:Fin 7) (1:Fin 2)=(3:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h6 : s ≤ 7
  · refine ⟨3,0,(s-7)/(-3/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (3:Fin 7)=(7:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (3:Fin 7) (0:Fin 2)=(-3:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h7 : s ≤ 8
  · refine ⟨3,1,(s-7)/1,?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (3:Fin 7)=(7:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (3:Fin 7) (1:Fin 2)=(2:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h8 : s ≤ 9
  · refine ⟨4,0,(s-9)/(-1),?_,?_⟩
    · constructor <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (4:Fin 7)=(9:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (4:Fin 7) (0:Fin 2)=(-2:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h9 : s ≤ (21/2)
  · refine ⟨4,1,(s-9)/(3/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (4:Fin 7)=(9:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (4:Fin 7) (1:Fin 2)=(3:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h10 : s ≤ 12
  · refine ⟨5,0,(s-12)/(-3/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (5:Fin 7)=(12:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (5:Fin 7) (0:Fin 2)=(-3:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h11 : s ≤ (25/2)
  · refine ⟨5,1,(s-12)/(1/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (5:Fin 7)=(12:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (5:Fin 7) (1:Fin 2)=(1:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h12 : s ≤ 13
  · refine ⟨6,0,(s-13)/(-1/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (6:Fin 7)=(13:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (6:Fin 7) (0:Fin 2)=(-1:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  refine ⟨6,1,(s-13)/(3/2),?_,?_⟩
  · constructor <;> norm_num <;> linarith [hs.1,hs.2]
  · norm_num only [show nearNode (6:Fin 7)=(13:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (6:Fin 7) (1:Fin 2)=(3:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
    ring
lemma near_signs_x_oai {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z) (hs : s∈Icc 0 (29/2)) :
    actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s := by
  obtain ⟨n,y,τ,hτ,rfl⟩ := near_cell_cover hs
  exact nearCell_signs hz hzB n y hτ
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.near_signs_x_oai := @OAI.AtomicTriangular.Construction.near_signs_x_oai
