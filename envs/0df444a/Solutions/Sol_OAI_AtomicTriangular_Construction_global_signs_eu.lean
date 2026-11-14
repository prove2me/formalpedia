-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.global_signs_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:12:51.146365+00:00
-- url     : https://prove2.me/submissions/3a7bfc94-5876-4c3f-8f9a-1b6d76f925e7

import Mathlib
import Definitions.Def_OAIQ334E011
import Definitions.Def_OAIQ334E020
import Theorems.Thm_OAI_AtomicTriangular_Construction_actualJ0_curvature_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_actual_interpolation_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cell_factors_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cell_geometry_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_deleted_accuracy_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_exceptional_rational_comparison_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_near_negative_polynomial_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_near_positive_polynomial_eu

section
-- module Solutions.OAIQ334_EU.Compat
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
-- module Solutions.OAIQ334_EU.Triangular_Certificate_WaveIntervals
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
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_SpectralCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set MeasureTheory
namespace AtomicTriangular.Construction
lemma spectralPCLM_apply (f : C(Spectrum,ℂ)) : spectralPCLM f = spectralP f := by
  simp [spectralPCLM,spectralP]

lemma spectralP_phase (s : ℂ) : spectralP (phaseFunction s) = P s := by
  exact (P_fourier s).symm

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
-- module Solutions.OAIQ334_EU.Triangular_Envelope_KernelBounds
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
-- module Solutions.OAIQ334_EU.Triangular_Certificate_PolytopeInterval
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
-- module Solutions.OAIQ334_EU.Triangular_Certificate_ParamActual
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
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_InputCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set MeasureTheory
namespace AtomicTriangular.Construction

lemma atomSpectral_apply (S : Fin 31 → ℂ) (f : C(Spectrum,ℂ)) :
    atomSpectral S f = ∑ j : Fin 31, S j*f ⟨frequency j,frequency_mem j⟩ := by
  simp [atomSpectral]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_WaveFunction
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
-- module Solutions.OAIQ334_EU.Triangular_Construction_DirectWaveJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
lemma waveFunctionJet_direct_zero (q : Fin 2) (s : ℂ) :
    waveFunctionJet q 0 0 s=exp (-(Real.pi:ℂ)*(damping q-h)*s) • phaseFunction s := by
  ext t
  rw [waveFunctionJet_apply]
  simp only [finiteWaveJet,taylorAmplitude,taylorPhase,Fin.val_zero,↓reduceIte,pow_zero,mul_one,one_mul,
    ContinuousMap.smul_apply,smul_eq_mul,phaseFunction]
  simp only [ofReal_mul,ofReal_sub,ContinuousMap.coe_mk]
  rw [show (I*Real.pi*(t.val:ℂ)-(Real.pi:ℂ)*(damping q-h))*s=
    -(Real.pi:ℂ)*(damping q-h)*s+I*Real.pi*(t.val:ℂ)*s by ring,exp_add]
lemma waveFunctionJet_zero_phase (s : ℂ) : waveFunctionJet 0 0 0 s=phaseFunction s := by
  rw [waveFunctionJet_direct_zero]
  simp only [damping,Fin.val_zero,↓reduceIte,sub_self,mul_zero,zero_mul,exp_zero,one_smul]
lemma hasDerivAt_phaseFunction (s : ℂ) : HasDerivAt phaseFunction (waveFunctionJet 0 0 1 s) s := by
  have he : phaseFunction=waveFunctionJet 0 0 0 := (funext waveFunctionJet_zero_phase).symm
  rw [he]
  exact hasDerivAt_waveFunctionJet 0 0 0 s
lemma spectralP_direct (s : ℂ) :
    spectralPCLM (waveFunctionJet 0 0 0 s)=P s ∧
    spectralPCLM (waveFunctionJet 0 0 1 s)=deriv P s := by
  constructor
  · rw [waveFunctionJet_zero_phase,spectralPCLM_apply,spectralP_phase]
  · have he : (fun s => spectralPCLM (phaseFunction s))=P := funext fun s => by rw [spectralPCLM_apply,spectralP_phase]
    have hh := (spectralPCLM.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_phaseFunction s)).deriv
    simp only [Function.comp_def] at hh
    rw [he] at hh
    exact hh.symm
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_CoefficientSpectral
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
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_ActualInterpolation
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
-- module Solutions.OAIQ334_EU.Triangular_Signs_SineBarrierBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset Set Filter
namespace AtomicTriangular.Construction

lemma sinePolynomial_lower {x : ℝ} (hx : 0≤x) (hx2 : x≤2) : sinePolynomial x≤Real.sin x := by
  have ha : Antitone (fun j : ℕ => x^(2*j+1)/((2*j+1).factorial:ℝ)) := by
    apply antitone_nat_of_succ_le
    intro j
    have hf : (0:ℝ)<((2*j+1).factorial:ℝ) := by positivity
    have hn : (0:ℝ)<(2*j+2:ℕ)*(2*j+3:ℕ) := by positivity
    have hd : (((2*(j+1)+1).factorial:ℕ):ℝ) = ((2*j+3:ℕ):ℝ)*((2*j+2:ℕ):ℝ)*((2*j+1).factorial:ℝ) := by
      rw [show 2*(j+1)+1=(2*j+1)+1+1 by omega,Nat.factorial_succ,Nat.factorial_succ]
      push_cast
      ring
    rw [hd,show 2*(j+1)+1=2*j+1+2 by omega,pow_add]
    apply (div_le_div_iff₀ (by positivity) hf).mpr
    have hb : x^2≤((2*j+3:ℕ):ℝ)*((2*j+2:ℕ):ℝ) := by
      have hj : (0:ℝ)≤j := Nat.cast_nonneg j
      push_cast
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hb (mul_nonneg (pow_nonneg hx (2*j+1)) hf.le)
    nlinarith
  have ht : Tendsto (fun n : ℕ => ∑ j ∈ range n, (-1:ℝ)^j*(x^(2*j+1)/((2*j+1).factorial:ℝ))) atTop (nhds (Real.sin x)) := by
    simpa only [mul_div_assoc] using (Real.hasSum_sin x).tendsto_sum_nat
  have hh := ha.alternating_series_le_tendsto ht 3
  norm_num [sum_range_succ,sinePolynomial] at hh ⊢
  linarith

lemma sine_pi_bounds : (piLow:ℝ)≤Real.pi ∧ Real.pi≤(piHigh:ℝ) := by
  rcases AtomicTriangular.Constants.pStar_bracket with ⟨h1,h2⟩
  constructor
  · have hh : (piLow:ℝ)≤AtomicTriangular.Constants.pStar := by norm_num [piLow,AtomicTriangular.Constants.pStar]
    exact hh.trans h1.le
  · have hh : AtomicTriangular.Constants.pStar+AtomicTriangular.Constants.eps≤(piHigh:ℝ) := by norm_num [piHigh,AtomicTriangular.Constants.pStar,AtomicTriangular.Constants.eps]
    exact h2.le.trans hh

lemma sine_lower {d : ℚ} (hd : 0≤d) (hd18 : d≤18) :
    (sineLower d:ℝ)≤2*Real.sin (Real.pi*d/36) := by
  have hd0 : (0:ℝ)≤d := by exact_mod_cast hd
  have hd18' : (d:ℝ)≤18 := by exact_mod_cast hd18
  have hl : 0≤(piLow:ℝ)*d/36 := by
    have : (0:ℝ)≤piLow := by norm_num [piLow]
    positivity
  have hlay : (piLow:ℝ)*d/36≤Real.pi*d/36 := by nlinarith [sine_pi_bounds.1]
  have huay : Real.pi*d/36≤(piHigh:ℝ)*d/36 := by nlinarith [sine_pi_bounds.2]
  have hx : 0≤Real.pi*d/36 := by positivity
  have hx2 : Real.pi*d/36≤2 := by nlinarith [Real.pi_lt_four]
  have hs := sinePolynomial_lower hx hx2
  have h3 := pow_le_pow_left₀ hx huay 3
  have h5 := pow_le_pow_left₀ hl hlay 5
  have h7 := pow_le_pow_left₀ hx huay 7
  have h9 := pow_le_pow_left₀ hl hlay 9
  have h11 := pow_le_pow_left₀ hx huay 11
  unfold sineLower
  push_cast
  unfold sinePolynomial at hs
  linarith
lemma sine_arc_lower {d : ℚ} {t : ℝ} (hd : 0≤d) (hd18 : d≤18)
    (ht : t∈Icc (d:ℝ) (36-d)) : (sineLower d:ℝ)≤2*|Real.sin (Real.pi*t/36)| := by
  have hd0 : (0:ℝ)≤d := by exact_mod_cast hd
  have hx0 : 0≤Real.pi*d/36 := by positivity
  have hleft : -(Real.pi/2)≤Real.pi*d/36 := (neg_nonpos.mpr (by positivity)).trans hx0
  have hmon : Real.sin (Real.pi*d/36)≤Real.sin (Real.pi*t/36) := by
    by_cases h : t≤18
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two hleft (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos,ht.1])
    · rw [show Real.pi*t/36=Real.pi-(Real.pi*(36-t)/36) by ring,Real.sin_pi_sub]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two hleft (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos,ht.2])
  linarith [sine_lower hd hd18,le_abs_self (Real.sin (Real.pi*t/36))]

lemma sine_vanishing_lower {v : ℚ} {u : ℝ} (hv : 0≤v) (hv3 : v≤3) (hu : |u|≤v) :
    (vanishingLower v:ℝ)*|u|≤2*|Real.sin (Real.pi*u/36)| := by
  have hv0 : (0:ℝ)≤v := by exact_mod_cast hv
  have hv3' : (v:ℝ)≤3 := by exact_mod_cast hv3
  have hp0 : (0:ℝ)≤piHigh := by norm_num [piHigh]
  have hx : 0≤Real.pi*|u|/36 := by positivity
  have hl : (piLow:ℝ)/36*|u|≤Real.pi*|u|/36 := by nlinarith [sine_pi_bounds.1,abs_nonneg u]
  have hq : (Real.pi/36)^3≤((piHigh:ℝ)/36)^3 := pow_le_pow_left₀ (by positivity) (by linarith [sine_pi_bounds.2]) 3
  have hu2 : |u|^2≤(v:ℝ)^2 := (sq_le_sq₀ (abs_nonneg u) hv0).mpr hu
  have hc : (Real.pi*|u|/36)^3≤((piHigh:ℝ)/36)^3*(v:ℝ)^2*|u| := by
    have h1 := mul_le_mul_of_nonneg_right hq (pow_nonneg (abs_nonneg u) 3)
    have h2 := mul_le_mul_of_nonneg_left hu2 (mul_nonneg (pow_nonneg (by positivity : 0≤(piHigh:ℝ)/36) 3) (abs_nonneg u))
    nlinarith
  have hs := Real.sin_ge_sub_cube hx
  have he : |Real.sin (Real.pi*u/36)|=Real.sin (Real.pi*|u|/36) := by
    have hb : |Real.pi*u/36|≤Real.pi := by
      rw [abs_div,abs_mul,abs_of_pos Real.pi_pos,abs_of_pos (by norm_num : (0:ℝ)<36)]
      nlinarith [Real.pi_pos]
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hb,abs_div,abs_mul,abs_of_pos Real.pi_pos,abs_of_pos (by norm_num : (0:ℝ)<36)]
  rw [he]
  unfold vanishingLower
  push_cast
  linarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_SineGridDefs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

lemma local_geometry (u : Fin 30) :
    |localHalf u|≤5/2 ∧ localPhase u (localPivot u)=0 ∧
    ∀ j : Fin 15,localCenter u-residue j=localPhase u j+36*localShift u j := by
  exact (show ∀ u : Fin 30, |localHalf u|≤5/2 ∧ localPhase u (localPivot u)=0 ∧
    ∀ j : Fin 15,localCenter u-residue j=localPhase u j+36*localShift u j by decide +kernel) u
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_SineGridAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction

lemma P_ofReal (s : ℝ) : P (s:ℂ)=(realP s:ℂ) := by
  unfold P realP sineFactor kappa
  push_cast
  congr 1
  funext a
  ring_nf
lemma realP_nonneg (s : ℝ) : 0 ≤ realP s := Finset.prod_nonneg (fun _ _ => sq_nonneg _)
lemma realP_periodic : Function.Periodic realP 36 := by
  intro s
  unfold realP
  apply Finset.prod_congr rfl
  intro a _
  rw [show Real.pi*(s+36-residue a)/36=Real.pi*(s-residue a)/36+Real.pi by ring,Real.sin_add_pi]
  ring
lemma sin_abs_local (u : Fin 30) (j : Fin 15) (y : ℝ) :
    |Real.sin (Real.pi*((localCenter u:ℝ)+y-residue j)/36)|=
      |Real.sin (Real.pi*((localPhase u j:ℝ)+y)/36)| := by
  have he : (localCenter u:ℝ)-residue j=localPhase u j+36*(localShift u j:ℝ) := by
    exact_mod_cast (local_geometry u).2.2 j
  rw [show (localCenter u:ℝ)+y-residue j=(localPhase u j:ℝ)+y+36*(localShift u j:ℝ) by linarith,
    show Real.pi*((localPhase u j:ℝ)+y+36*(localShift u j:ℝ))/36=
      Real.pi*((localPhase u j:ℝ)+y)/36+(localShift u j:ℝ)*Real.pi by ring,
    Real.sin_add_int_mul_pi,abs_mul,abs_zpow]
  norm_num
lemma abs_cell_le (u : Fin 30) (k : Fin 100) {y : ℝ}
    (hy : y∈Icc (cellLo u k:ℝ) (cellHi u k:ℝ)) : |y|≤(cellMagnitude u k:ℝ) := by
  unfold cellMagnitude
  push_cast
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (cellLo u k:ℝ),le_max_left |(cellLo u k:ℝ)| |(cellHi u k:ℝ)|,hy.1]
  · exact hy.2.trans ((le_abs_self _).trans (le_max_right _ _))
lemma cell_factor_lower (u : Fin 30) (k : Fin 100)
    (hg : 0 ≤ cellMagnitude u k ∧ cellMagnitude u k≤3 ∧
      (∀ j : Fin 15,j≠localPivot u → 0 ≤ cellSeparation u k j ∧ cellSeparation u k j≤18))
    (j : Fin 15) {y : ℝ} (hy : y∈Icc (cellLo u k:ℝ) (cellHi u k:ℝ)) :
    (cellFactor u k j:ℝ)*(if j=localPivot u then |y| else 1)≤
      2*|Real.sin (Real.pi*((localCenter u:ℝ)+y-residue j)/36)| := by
  rw [sin_abs_local]
  by_cases hj : j=localPivot u
  · subst j
    simpa only [cellFactor,ite_true, if_true,(local_geometry u).2.1,Int.cast_zero,zero_add] using
      sine_vanishing_lower hg.1 hg.2.1 (abs_cell_le u k hy)
  · have hsep : (cellSeparation u k j:ℝ)=
        min ((localPhase u j:ℝ)+(cellLo u k:ℝ)) (36-((localPhase u j:ℝ)+(cellHi u k:ℝ))) := by
      unfold cellSeparation
      push_cast
      rfl
    have ht : (localPhase u j:ℝ)+y∈Icc (cellSeparation u k j:ℝ) (36-cellSeparation u k j) := by
      rw [hsep]
      constructor <;> linarith [min_le_left ((localPhase u j:ℝ)+(cellLo u k:ℝ))
        (36-((localPhase u j:ℝ)+(cellHi u k:ℝ))),
        min_le_right ((localPhase u j:ℝ)+(cellLo u k:ℝ))
        (36-((localPhase u j:ℝ)+(cellHi u k:ℝ))),hy.1,hy.2]
    simpa only [cellFactor,ite_eq_right hj,mul_one] using sine_arc_lower (hg.2.2 j hj).1 (hg.2.2 j hj).2 ht
lemma realP_cell_lower (u : Fin 30) (k : Fin 100)
    (hg : 0 ≤ cellMagnitude u k ∧ cellMagnitude u k≤3 ∧
      (∀ j : Fin 15,j≠localPivot u → 0 ≤ cellSeparation u k j ∧ cellSeparation u k j≤18))
    (hn : ∀ j : Fin 15,0 ≤ cellFactor u k j)
    (hp : cellBarrier u < ∏ j : Fin 15,(cellFactor u k j)^2)
    {y : ℝ} (hy : y∈Icc (cellLo u k:ℝ) (cellHi u k:ℝ)) (hy0 : y≠0) :
    (cellBarrier u:ℝ)*y^2 < realP ((localCenter u:ℝ)+y) := by
  have hc : (cellBarrier u:ℝ)<∏ j : Fin 15,(cellFactor u k j:ℝ)^2 := by
    exact_mod_cast hp
  calc
    _ < (∏ j : Fin 15,(cellFactor u k j:ℝ)^2)*y^2 := mul_lt_mul_of_pos_right hc (sq_pos_of_ne_zero hy0)
    _ = ∏ j : Fin 15,((cellFactor u k j:ℝ)*(if j=localPivot u then |y| else 1))^2 := by
      simp only [mul_pow]
      rw [Finset.prod_mul_distrib]
      simp only [ite_pow,one_pow,sq_abs]
      rw [Fintype.prod_ite_eq']
    _ ≤ ∏ j : Fin 15,(2*|Real.sin (Real.pi*((localCenter u:ℝ)+y-residue j)/36)|)^2 := by
      apply Finset.prod_le_prod (fun _ _ => sq_nonneg _)
      intro j _
      have hnon : 0≤(cellFactor u k j:ℝ) := by exact_mod_cast hn j
      apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
      exact cell_factor_lower u k hg j hy
    _ = _ := by simp [realP,mul_pow,sq_abs]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_FarCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

lemma hasDerivAt_spectralP_wave (br : Fin 2) (k : ℕ) (s : ℂ) :
    HasDerivAt (fun t => spectralPCLM (waveFunctionJet 0 br k t))
      (spectralPCLM (waveFunctionJet 0 br (k+1) s)) s :=
  spectralPCLM.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_waveFunctionJet 0 br k s)
lemma transformedP_contDiff : ContDiff ℝ ⊤ transformedP := by
  exact (show Differentiable ℂ (fun s => spectralPCLM (waveFunctionJet 0 1 0 s)) from
    fun s => (hasDerivAt_spectralP_wave 1 0 s).differentiableAt).contDiff.real_of_complex
lemma realP_contDiff : ContDiff ℝ ⊤ realP := by unfold realP; fun_prop
lemma realP_jet_zero (n : Node) : realP n.val=0 ∧ deriv realP n.val=0 := by
  have he (s : ℝ) : (spectralPCLM (waveFunctionJet 0 0 0 s)).re=realP s := by
    rw [(spectralP_direct _).1,P_ofReal,ofReal_re]
  constructor
  · rw [←he,(spectralP_direct _).1]
    norm_cast
    rw [P_node,zero_re]
  · have hh := ((hasDerivAt_spectralP_wave 0 0 (n.val:ℂ)).real_of_complex).deriv
    simp only [he] at hh
    rw [hh,(spectralP_direct _).2]
    norm_cast
    rw [deriv_P_node,zero_re]
lemma inputJJet_constant (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (br : Fin 2) (k : ℕ) (s : ℂ) :
    inputJJet (coefficientInput C a w) br k s=
      (C:ℂ)*spectralPCLM (waveFunctionJet 0 br k s)+inputJJet (coefficientInput 0 a w) br k s := by
  simp only [inputJJet,tailSpectral_coefficient,finiteSpectral_coefficient_apply,
    add_apply,smul_apply,smul_eq_mul,ofReal_zero,zero_mul,zero_add]
  ring

lemma actualJ0_contDiff (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) :
    ContDiff ℝ ⊤ (actualJ0 side z hz hzB) :=
  by
    change ContDiff ℝ ⊤ (fun s => _+sideConstant (otherSide side)*transformedP s)
    exact (pairJ_contDiff _ _).add (by simpa only [smul_eq_mul] using transformedP_contDiff.const_smul (sideConstant (otherSide side)))
lemma actualJ_decompose (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) :
    actualJ side z hz hzB=sideConstant side • realP+actualJ0 side z hz hzB := by
  funext s
  simp only [actualJ,actualInput,pairJ,pairJJet,actualJ0,Pi.add_apply,
    Pi.smul_apply,smul_eq_mul]
  rw [inputJJet_constant (if side.val=0 then -(3/500) else 3/500) _ _ 0,
    inputJJet_constant (if (otherSide side).val=0 then -(3/500) else 3/500) _ _ 1]
  simp only [add_re]
  rw [(spectralP_direct _).1,P_ofReal]
  simp only [ofReal_re,mul_re,ofReal_im,zero_mul,sub_zero,transformedP,sideConstant]
  ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_DeletedQuotient
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
-- module Solutions.OAIQ334_EU.Triangular_Signs_GaussianDeleted
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
-- module Solutions.OAIQ334_EU.Triangular_Signs_OrdinaryComparison
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
  have hh := near_positive_polynomial_eu (actualParameter z) (actualParameter_mem hz hzB) n y hτ
  have he := (abs_lt.mp (deleted_accuracy_eu 1 hz hzB n y hτ)).1
  linarith
lemma near_ordinary_deleted {z : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Fin 7) (y : Fin 2) (hne : ¬(n=0 ∧ y=1)) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    deletedSecond (actualJ 0 z hz hzB) (nearNode n) (nearNode n+nearDisplacement n y*τ) ≤
      deletedSecond (gaussianG z) (nearNode n) (nearNode n+nearDisplacement n y*τ) := by
  have hh := near_negative_polynomial_eu (actualParameter z) (actualParameter_mem hz hzB) n y hne hτ
  have he := (abs_lt.mp (deleted_accuracy_eu 0 hz hzB n y hτ)).2
  have hg := gaussian_ordinary_lower hz hzB n y hne hτ
  linarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_NearSigns
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
  have he := (abs_lt.mp (deleted_accuracy_eu 0 hz hzB 0 1 hτ)).2
  have hg := gaussian_deleted_right (m:=1) hz hτ.1
  have ht := exceptional_rational_comparison_eu (actualParameter z) (actualParameter_mem hz hzB) hτ hz hzB
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
  have hj := actual_interpolation_eu hz hzB ⟨nearNode n,hn⟩
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
lemma near_signs {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z) (hs : s∈Icc 0 (29/2)) :
    actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s := by
  obtain ⟨n,y,τ,hτ,rfl⟩ := near_cell_cover hs
  exact nearCell_signs hz hzB n y hτ
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_SineGridCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
lemma unit_grid_cover {x : ℝ} (hx : x∈Icc 0 1) :
    ∃ k : Fin 100, (k.val:ℝ)/100≤x ∧ x≤(k.val+1:ℝ)/100 := by
  by_cases he : x=1
  · subst x
    exact ⟨99,by norm_num,by norm_num⟩
  · have hx1 : x<1 := lt_of_le_of_ne hx.2 he
    let n : ℕ := ⌊100*x⌋₊
    have hn1 : (n:ℝ)≤100*x := Nat.floor_le (by nlinarith [hx.1])
    have hn2 : 100*x<(n:ℝ)+1 := Nat.lt_floor_add_one _
    have hn : n<100 := by
      by_contra! hh
      have : (100:ℝ)≤n := by exact_mod_cast hh
      nlinarith
    exact ⟨⟨n,hn⟩,by dsimp <;> linarith,by dsimp <;> linarith⟩
lemma cell_displacement (u : Fin 30) (k : Fin 100) {x : ℝ}
    (hx : (k.val:ℝ)/100≤x ∧ x≤(k.val+1:ℝ)/100) :
    (localHalf u:ℝ)*x∈Icc (cellLo u k:ℝ) (cellHi u k:ℝ) := by
  have hlo : (cellLo u k:ℝ)=min ((localHalf u:ℝ)*k.val/100) ((localHalf u:ℝ)*(k.val+1)/100) := by
    unfold cellLo; push_cast; rfl
  have hhi : (cellHi u k:ℝ)=max ((localHalf u:ℝ)*k.val/100) ((localHalf u:ℝ)*(k.val+1)/100) := by
    unfold cellHi; push_cast; rfl
  rw [hlo,hhi]
  by_cases h : 0≤(localHalf u:ℝ)
  · have hab : (localHalf u:ℝ)*k.val/100≤(localHalf u:ℝ)*(k.val+1)/100 := by nlinarith
    rw [min_eq_left hab,max_eq_right hab]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hx.1 h,mul_le_mul_of_nonneg_left hx.2 h]
  · have h := le_of_not_ge h
    have hab : (localHalf u:ℝ)*(k.val+1)/100≤(localHalf u:ℝ)*k.val/100 := by nlinarith
    rw [min_eq_right hab,max_eq_left hab]
    constructor <;> nlinarith [mul_le_mul_of_nonpos_left hx.1 h,mul_le_mul_of_nonpos_left hx.2 h]
lemma local_boundary_end : localBoundary 0= -5/2 ∧ localBoundary 30=67/2 := by decide +kernel
lemma local_boundary_geometry (u : Fin 30) :
    min (localCenter u:ℚ) ((localCenter u:ℚ)+localHalf u)=localBoundary u.val ∧
    max (localCenter u:ℚ) ((localCenter u:ℚ)+localHalf u)=localBoundary (u.val+1) ∧
    localHalf u≠0 ∧ 0≤localCenter u ∧ localCenter u%36∈residues ∧
    (localCenter u<25 → localBoundary (u.val+1)≤23) ∧
    (u.val<16 → localBoundary (u.val+1)≤29/2) ∧
    (21<u.val → 23≤localBoundary u.val) := by
  exact (show ∀ u : Fin 30,
    min (localCenter u:ℚ) ((localCenter u:ℚ)+localHalf u)=localBoundary u.val ∧
    max (localCenter u:ℚ) ((localCenter u:ℚ)+localHalf u)=localBoundary (u.val+1) ∧
    localHalf u≠0 ∧ 0≤localCenter u ∧ localCenter u%36∈residues ∧
    (localCenter u<25 → localBoundary (u.val+1)≤23) ∧
    (u.val<16 → localBoundary (u.val+1)≤29/2) ∧
    (21<u.val → 23≤localBoundary u.val) by decide +kernel) u
lemma local_halfGap_cover {t : ℝ} (ht : t∈Ico (-(5/2)) (67/2)) :
    ∃ u : Fin 30,∃ x∈Icc (0:ℝ) 1,t=(localCenter u:ℝ)+(localHalf u:ℝ)*x ∧
      t∈Ico (localBoundary u.val:ℝ) (localBoundary (u.val+1):ℝ) := by
  have hex : ∃ n : ℕ,1≤n ∧ n≤30 ∧ t<(localBoundary n:ℝ) := by
    refine ⟨30,by omega,le_rfl,?_⟩
    simpa only [local_boundary_end.2,Rat.cast_div,Rat.cast_ofNat] using ht.2
  let n := Nat.find hex
  have hn := Nat.find_spec hex
  change 1≤n ∧ n≤30 ∧ t<(localBoundary n:ℝ) at hn
  have hl : (localBoundary (n-1):ℝ)≤t := by
    by_cases h : n=1
    · simp only [h,Nat.sub_self,local_boundary_end.1,Rat.cast_neg,Rat.cast_div,Rat.cast_ofNat]
      linarith [ht.1]
    · have hmin := Nat.find_min hex (show n-1<n by omega)
      by_contra! hh
      exact hmin ⟨by omega,by omega,hh⟩
  let u : Fin 30 := ⟨n-1,by omega⟩
  have hg := local_boundary_geometry u
  have hg₁ : min (localCenter u:ℝ) ((localCenter u:ℝ)+(localHalf u:ℝ))=(localBoundary u.val:ℝ) := by
    simpa only [Rat.cast_min,Rat.cast_add,Rat.cast_intCast] using congrArg (fun q : ℚ => (q:ℝ)) hg.1
  have hg₂ : max (localCenter u:ℝ) ((localCenter u:ℝ)+(localHalf u:ℝ))=(localBoundary (u.val+1):ℝ) := by
    simpa only [Rat.cast_max,Rat.cast_add,Rat.cast_intCast] using congrArg (fun q : ℚ => (q:ℝ)) hg.2.1
  have hu : t<(localBoundary (u.val+1):ℝ) := by simpa only [u,show n-1+1=n by omega] using hn.2.2
  have hb : t∈uIcc (localCenter u:ℝ) ((localCenter u:ℝ)+(localHalf u:ℝ)) := by
    rw [uIcc,mem_Icc,hg₁,hg₂]
    exact ⟨hl,hu.le⟩
  have hne : (localHalf u:ℝ)≠0 := by exact_mod_cast hg.2.2.1
  refine ⟨u,(t-localCenter u)/(localHalf u:ℝ),?_,?_,hl,hu⟩
  · by_cases hp : 0<(localHalf u:ℝ)
    · rw [uIcc_of_le (by linarith)] at hb
      exact ⟨div_nonneg (sub_nonneg.mpr hb.1) hp.le,(div_le_one hp).mpr (by linarith [hb.2])⟩
    · have hp : (localHalf u:ℝ)<0 := lt_of_le_of_ne (le_of_not_gt hp) hne
      rw [uIcc_of_ge (by linarith)] at hb
      exact ⟨div_nonneg_of_nonpos (sub_nonpos.mpr hb.2) hp.le,(div_le_one_of_neg hp).mpr (by linarith [hb.1])⟩
  · field_simp
    ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_SineGlobal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
lemma realP_local_strict (u : Fin 30) {x : ℝ} (hx : x∈Icc 0 1)
    (hy : (localHalf u:ℝ)*x≠0) :
    (cellBarrier u:ℝ)*((localHalf u:ℝ)*x)^2 < realP ((localCenter u:ℝ)+(localHalf u:ℝ)*x) := by
  obtain ⟨k,hk⟩ := unit_grid_cover hx
  exact realP_cell_lower u k (cell_geometry_eu u k) (cell_factors_eu u k).1 (cell_factors_eu u k).2
    (cell_displacement u k hk) hy
lemma realP_local_lower (u : Fin 30) {x : ℝ} (hx : x∈Icc 0 1) :
    (cellBarrier u:ℝ)*((localHalf u:ℝ)*x)^2 ≤ realP ((localCenter u:ℝ)+(localHalf u:ℝ)*x) := by
  by_cases hy : (localHalf u:ℝ)*x=0
  · simpa only [hy,zero_pow (by norm_num : 2≠0),mul_zero,add_zero] using realP_nonneg (localCenter u)
  · exact (realP_local_strict u hx hy).le
lemma cellBarrier_lower (u : Fin 30) : (27/500:ℝ) ≤ cellBarrier u := by
  unfold cellBarrier
  split_ifs <;> norm_num
lemma realP_far_lower {s : ℝ} (hs : (23:ℝ)  ≤  s) :
    ∃ m : Node, 25 ≤ m.val ∧ (27/500:ℝ)*(s-m.val)^2 ≤ realP s := by
  let q : ℕ := ⌊(s+5/2)/36⌋₊
  let t : ℝ := s-36*q
  have hq0 : (q:ℝ) ≤ (s+5/2)/36 := Nat.floor_le (by linarith)
  have hq1 : (s+5/2)/36<(q:ℝ)+1 := Nat.lt_floor_add_one _
  have ht : t∈Ico (-(5/2)) (67/2) := by dsimp [t]; constructor <;> linarith
  obtain ⟨u,x,hx,htu,hcell⟩ := local_halfGap_cover ht
  let m : ℤ := 36*(q:ℤ)+localCenter u
  have hm : 25 ≤ m := by
    by_cases hq : q=0
    · have ht0 : t=s := by simp [t,hq]
      have hg := (local_boundary_geometry u).2.2.2.2.2.1
      by_contra! hh
      have hu : localCenter u<25 := by simpa [m,hq] using hh
      have hhB : (localBoundary (u.val+1):ℝ) ≤ 23 := by exact_mod_cast hg hu
      linarith [hcell.2]
    · have hqc : (1:ℤ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
      have huc := (local_boundary_geometry u).2.2.2.1
      dsimp [m]
      omega
  have hmres : m%36∈residues := by
    simpa only [m,Int.add_emod,Int.mul_emod_right,zero_add,Int.emod_emod] using
      (local_boundary_geometry u).2.2.2.2.1
  refine ⟨⟨m,by omega,hmres⟩,hm,?_⟩
  have hp := realP_local_lower u hx
  have hp' := mul_le_mul_of_nonneg_right (cellBarrier_lower u) (sq_nonneg ((localHalf u:ℝ)*x))
  have hP : realP t=realP s := by
    convert realP_periodic.sub_nat_mul_eq q using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [t]
    ring_nf
  have hsm : s-(m:ℝ)=(localHalf u:ℝ)*x := by
    dsimp [m,t] at *
    push_cast
    linarith
  change (27/500:ℝ)*(s-(m:ℝ))^2 ≤ realP s
  rw [hsm,←hP,htu]
  exact hp'.trans hp
lemma strong_local_geometry (u : Fin 30) (hu : 16 ≤ u.val ∧ u.val ≤ 21) :
    localCenter u∈({16,19,21}:Finset ℤ) ∧ cellBarrier u=3 := by
  have hh : ∀ u : Fin 30,16 ≤ u.val ∧ u.val ≤ 21 → localCenter u∈({16,19,21}:Finset ℤ) := by decide +kernel
  exact ⟨hh u hu,by simp [cellBarrier,hu]⟩
lemma realP_middle_lower {s : ℝ} (hs : s∈Icc (29/2) 23) :
    ∃ m : ℤ,m∈({16,19,21}:Finset ℤ) ∧ (3:ℝ)*(s-m)^2 ≤ realP s := by
  by_cases he : s=23
  · subst s
    refine ⟨21,by simp,?_⟩
    have hh := realP_local_lower (21:Fin 30) (x:=1) (by simp)
    have hc : localCenter (21:Fin 30)=21 ∧ localHalf (21:Fin 30)=2 ∧ cellBarrier (21:Fin 30)=3 := by decide +kernel
    rw [hc.1,hc.2.1,hc.2.2] at hh
    norm_num at hh ⊢
    exact hh
  · obtain ⟨u,x,hx,htu,hcell⟩ := local_halfGap_cover (t:=s) (by constructor <;> linarith [hs.1,hs.2])
    have hu : 16 ≤ u.val ∧ u.val ≤ 21 := by
      have hg := local_boundary_geometry u
      constructor
      · by_contra! h
        have hh : (localBoundary (u.val+1):ℝ) ≤ 29/2 := by
          have ht := Rat.cast_le (K:=ℝ) |>.mpr (hg.2.2.2.2.2.2.1 h)
          norm_num at ht ⊢
          exact ht
        linarith [hcell.2,hs.1,hs.2]
      · by_contra! h
        have hh : (23:ℝ) ≤ localBoundary u.val := by exact_mod_cast hg.2.2.2.2.2.2.2 h
        have hss : s<23 := lt_of_le_of_ne hs.2 he
        linarith [hcell.1,hss]
    refine ⟨localCenter u,(strong_local_geometry u hu).1,?_⟩
    have hh := realP_local_lower u hx
    rw [(strong_local_geometry u hu).2] at hh
    norm_num only [Rat.cast_ofNat] at hh
    rw [htu]
    simpa only [add_sub_cancel_left] using hh
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_FarSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma deletedSecond_identity (f : ℝ → ℝ) (m s : ℝ) :
    f s=f m+deriv f m*(s-m)+(s-m)^2*deletedSecond f m s := by
  by_cases hsm : s=m
  · simp [hsm]
  · rw [deletedSecond,ite_eq_right hsm]
    field_simp [sub_ne_zero.mpr hsm]
    ring
lemma actualJ0_jets (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) (n : Node) :
    actualJ0 side z hz hzB n.val=actualJ side z hz hzB n.val ∧
      deriv (actualJ0 side z hz hzB) n.val=deriv (actualJ side z hz hzB) n.val := by
  have hp := realP_jet_zero n
  have hv := congrFun (actualJ_decompose side hz hzB) (n.val:ℝ)
  have hd := ((realP_contDiff.differentiable (by norm_num) (n.val:ℝ)).hasDerivAt.const_mul (sideConstant side)).add
    ((actualJ0_contDiff side hz hzB).differentiable (by norm_num) (n.val:ℝ)).hasDerivAt
  change HasDerivAt (sideConstant side • realP+actualJ0 side z hz hzB) _ _ at hd
  rw [←actualJ_decompose side hz hzB] at hd
  constructor
  · simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hp.1,mul_zero,zero_add] using hv.symm
  · simpa only [hp.2,mul_zero,zero_add] using hd.deriv.symm
lemma actualJ0_deleted (side : Fin 2) {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Node) (i : Fin 5) (hs : curvaturePoint i ≤ s) (hm : curvaturePoint i ≤ (n.val:ℝ))
    (hs14 : 29/2 ≤ s) (hm14 : 29/2 ≤ (n.val:ℝ)) :
    |deletedSecond (actualJ0 side z hz hzB) n.val s| ≤ farK i := by
  have hh := deletedSecond_bound ((actualJ0_contDiff side hz hzB).of_le (by norm_num))
    (m:=(n.val:ℝ)) (s:=s) (C:=2*farK i) (by
      intro t ht
      have hi : curvaturePoint i ≤ t := (le_min hm hs).trans ht.1
      have h14 : 29/2 ≤ t := (le_min hm14 hs14).trans ht.1
      have hc := actualJ0_curvature_eu side hz hzB i hi h14
      change |iteratedDeriv 2 (actualJ0 side z hz hzB) t|/2 ≤ farK i at hc
      linarith)
  simpa using hh
lemma far_signs_of_barrier {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Node) (i : Fin 5) (hs : curvaturePoint i ≤ s) (hm : curvaturePoint i ≤ (n.val:ℝ))
    (hs14 : 29/2 ≤ s) (hm14 : 29/2 ≤ (n.val:ℝ))
    (hb : farK i*(s-n.val)^2 ≤ (3/500)*realP s) :
    actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s := by
  have hj := actual_interpolation_eu hz hzB n
  have hj0 := actualJ0_jets 0 hz hzB n
  have hj1 := actualJ0_jets 1 hz hzB n
  have h0 := mul_le_mul_of_nonneg_left (abs_le.mp (actualJ0_deleted 0 hz hzB n i hs hm hs14 hm14)).2 (sq_nonneg (s-n.val))
  have h1 := mul_le_mul_of_nonneg_left (abs_le.mp (actualJ0_deleted 1 hz hzB n i hs hm hs14 hm14)).1 (sq_nonneg (s-n.val))
  have hg := mul_nonneg (sq_nonneg (s-n.val)) (gaussian_deleted_nonneg hz n.val (s-n.val))
  simp only [add_sub_cancel] at hg
  have he0 := deletedSecond_identity (actualJ0 0 z hz hzB) n.val s
  rw [hj0.1,hj0.2,hj.1,hj.2.1] at he0
  have he1 := deletedSecond_identity (actualJ0 1 z hz hzB) n.val s
  rw [hj1.1,hj1.2,hj.2.2.1,hj.2.2.2] at he1
  have heG := deletedSecond_identity (gaussianG z) n.val s
  have hd0 := congrFun (actualJ_decompose 0 hz hzB) s
  have hd1 := congrFun (actualJ_decompose 1 hz hzB) s
  norm_num [Pi.add_apply,Pi.smul_apply,smul_eq_mul,sideConstant] at hd0 hd1
  constructor <;> nlinarith
lemma middle_signs {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z) (hs : s∈Icc (29/2) 23) :
    actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s := by
  obtain ⟨m,hm,hP⟩ := realP_middle_lower hs
  have hn : 0 < m ∧ m%36∈residues := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl|rfl|rfl <;> norm_num [residues]
  have hm14 : 29/2 ≤ (m:ℝ) := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl|rfl|rfl <;> norm_num
  apply far_signs_of_barrier hz hzB ⟨m,hn⟩ 3 hs.1 hm14 hs.1 hm14
  have hK : farK 3=(140109/10000000:ℝ) := by
    change (301/100:ℝ)*(465/100000)+(3/1000000000)*800+(3/500)*(2/1000)=_
    norm_num
  change farK 3*(s-m)^2 ≤ (3/500)*realP s
  rw [hK]
  nlinarith [sq_nonneg (s-m)]
lemma later_signs {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z) (hs : 23 ≤ s) :
    actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s := by
  obtain ⟨n,hn,hP⟩ := realP_far_lower hs
  have hm : (23:ℝ) ≤ n.val := by exact_mod_cast (show (23:ℤ) ≤ n.val by omega)
  apply far_signs_of_barrier hz hzB n 4 hs hm (by linarith) (by linarith)
  have hK : farK 4=(8363/100000000:ℝ) := by
    change (301/100:ℝ)*(23/1000000)+(3/1000000000)*800+(3/500)*(2/1000)=_
    norm_num
  rw [hK]
  nlinarith [sq_nonneg (s-n.val)]
theorem global_signs_eu_oai {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z) (hs : 0 ≤ s) :
    actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s := by
  by_cases h14 : s ≤ 29/2
  · exact near_signs hz hzB ⟨hs,h14⟩
  by_cases h23 : s ≤ 23
  · exact middle_signs hz hzB ⟨by linarith,h23⟩
  exact later_signs hz hzB (by linarith)
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.global_signs_eu_oai := @OAI.AtomicTriangular.Construction.global_signs_eu_oai
