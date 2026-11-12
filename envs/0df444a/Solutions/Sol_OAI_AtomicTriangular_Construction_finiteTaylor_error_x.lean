-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.finiteTaylor_error_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:24:14.014859+00:00
-- url     : https://prove2.me/submissions/8db26d95-7164-4332-ae10-9af06c2a7e99

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X021
import Theorems.Thm_OAI_AtomicTriangular_Construction_finiteApprox_norm_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainder_table_x

section
-- module Solutions.OAIQ250_TR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
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

lemma RI.mem_pow {a : RI} {x : ℝ} (hx : a.Mem x) (n : ℕ) : (a.pow n).Mem (x^n) := by
  induction n with
  | zero => simpa [RI.pow] using RI.mem_point 1
  | succ n ih => simpa [RI.pow,pow_succ] using RI.mem_mul ih hx

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

noncomputable section
open scoped BigOperators

lemma RI.mem_sqrt {a r : RI} {x : ℝ} (hx : a.Mem x) (h₀ : 0 ≤ x)
    (hr₀ : 0 ≤ r.lo) (hr₁ : r.lo * r.lo ≤ scale * max 0 a.lo)
    (hr₂ : scale * a.hi ≤ r.hi * r.hi) (hr₃ : 0 ≤ r.hi) :
    r.Mem (Real.sqrt x) := by
  have hs := Real.sq_sqrt h₀
  have hp := Real.sqrt_nonneg x
  have hrl : (0:ℝ) ≤ r.lo := by exact_mod_cast hr₀
  have hrh : (0:ℝ) ≤ r.hi := by exact_mod_cast hr₃
  have hrls : (r.lo:ℝ) * r.lo ≤ (scale:ℝ) * max (0:ℝ) (a.lo:ℝ) := by exact_mod_cast hr₁
  have hrhs : (scale:ℝ) * a.hi ≤ (r.hi:ℝ) * r.hi := by exact_mod_cast hr₂
  have hsl := mul_le_mul_of_nonneg_left (max_le (mul_nonneg scale_pos.le h₀) hx.1) scale_pos.le
  have hsh := mul_le_mul_of_nonneg_left hx.2 scale_pos.le
  have he : ((scale:ℝ) * Real.sqrt x)^2 = (scale:ℝ) * ((scale:ℝ)*x) := by
    rw [mul_pow, hs]
    ring
  constructor <;> nlinarith [mul_nonneg scale_pos.le hp]

lemma CI.mem_norm {a : CI} {r : RI} {x : ℂ} (hx : a.Mem x)
    (hr₀ : 0 ≤ r.lo) (hr₁ : r.lo * r.lo ≤ scale * max 0 a.normSq.lo)
    (hr₂ : scale * a.normSq.hi ≤ r.hi * r.hi) (hr₃ : 0 ≤ r.hi) :
    r.Mem ‖x‖ := by
  have hh := RI.mem_sqrt (CI.mem_normSq hx) (Complex.normSq_nonneg x) hr₀ hr₁ hr₂ hr₃
  simpa [Complex.normSq_eq_norm_sq] using hh

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

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex

lemma dampingBox_mem (q : Fin 2) : (dampingBox q).Mem (damping q) := by
  unfold dampingBox damping h H
  split_ifs
  · simpa using RI.mem_divNat (RI.mem_point 17) (by norm_num : 0<(50:ℕ))
  · simpa using RI.mem_divNat (RI.mem_point 27) (by norm_num : 0<(50:ℕ))
lemma realFrequencyBox_mem (j : Fin 31) : (realFrequencyBox j).Mem (frequency j) := by
  have hh := RI.mem_divNat (RI.mem_point ((j.val:ℤ)-15)) (by norm_num : 0<(18:ℕ))
  simpa only [realFrequencyBox, frequency, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat,
    Nat.cast_ofNat] using hh

lemma denBox_mem (q : Fin 2) (j : Fin 31) :
    (denBox q j).Mem (waveDen (damping q) (frequency j)) := by
  exact RI.mem_add (RI.mem_pow (dampingBox_mem q) 2) (RI.mem_pow (realFrequencyBox_mem j) 2)
lemma denBox_pos (q : Fin 2) (j : Fin 31) : 0 < (denBox q j).lo := by
  revert q j
  decide +kernel
lemma xwaveBox_mem (q : Fin 2) (j : Fin 31) :
    (xwaveBox q j).Mem (Xwave (damping q) (frequency j)) := by
  unfold Xwave
  rw [div_eq_mul_inv]
  exact RI.mem_mul (by simpa using RI.mem_divNat (RI.mem_point 4) (by norm_num : 0<(3:ℕ)))
    (RI.mem_invPos (denBox_mem q j) (denBox_pos q j))

lemma zetaBox_mem (q v : Fin 2) (j : Fin 31) :
    (zetaBox q v j).Mem (zeta (damping q) (damping v) (frequency j)) := by
  have hh := CI.mem_add (CI.mem_ofReal (RI.mem_neg
    (RI.mem_mul (realFrequencyBox_mem j) (xwaveBox_mem q j))))
    (CI.mem_mul CI.mem_imag (CI.mem_ofReal
      (RI.mem_sub (RI.mem_mul (dampingBox_mem q) (xwaveBox_mem q j)) (dampingBox_mem v))))
  simpa only [zetaBox,zeta,Complex.ofReal_neg,Complex.ofReal_mul,neg_mul] using hh

lemma wavePhaseBox_mem (q v : Fin 2) (j : Fin 31) :
    (wavePhaseBox q v j).Mem (I*Real.pi*zeta (damping q) (damping v) (frequency j)) :=
  CI.mem_mul (CI.mem_mul CI.mem_imag (CI.mem_ofReal piBox_mem)) (zetaBox_mem q v j)
end AtomicTriangular.FiniteCertificate
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
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Auxiliary_ExponentialTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Envelope

lemma factorial_term_step {d r : ℝ} {k : ℕ} (hd : 0 ≤ d) (hdr : d ≤ r*(k+1)) :
    d^(k+1)/(k+1).factorial  ≤  r*(d^k/k.factorial) := by
  have hk : (0:ℝ)<k+1 := by positivity
  have hf : (0:ℝ)<k.factorial := by positivity
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
  apply (div_le_iff₀ (mul_pos hk hf)).mpr
  have hh := mul_le_mul_of_nonneg_left hdr (pow_nonneg hd k)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  field_simp
lemma factorial_tail_geometric {d r : ℝ} (N : ℕ) (hd : 0 ≤ d) (hr : 0 ≤ r)
    (hdr : d ≤ r*(N+1)) (i : ℕ) :
    d^(i+N)/(i+N).factorial  ≤  (d^N/N.factorial)*r^i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hni : (N:ℝ)+1 ≤ (i+N:ℕ)+1 := by exact_mod_cast (show N+1 ≤ i+N+1 by omega)
    have hs := factorial_term_step (k:=i+N) hd (hdr.trans (mul_le_mul_of_nonneg_left hni hr))
    calc
      d^(i+1+N)/(i+1+N).factorial = d^(i+N+1)/(i+N+1).factorial := by rw [show i+1+N=i+N+1 by omega]
      _  ≤  r*(d^(i+N)/(i+N).factorial) := hs
      _  ≤  r*((d^N/N.factorial)*r^i) := mul_le_mul_of_nonneg_left ih hr
      _ = _ := by rw [pow_succ]; ring
lemma exp_tail_bound {d r : ℝ} (N : ℕ) (hd : 0 ≤ d) (hr : 0 ≤ r) (hr1 : r<1)
    (hdr : d ≤ r*(N+1)) :
    Real.exp d-(∑ i ∈ Finset.range N, d^i/i.factorial)  ≤  (d^N/N.factorial)/(1-r) := by
  have hf := NormedSpace.expSeries_div_summable d
  have ht : ∑' i : ℕ, d^i/i.factorial = Real.exp d := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp d).tsum_eq
  have he := hf.sum_add_tsum_nat_add N
  rw [ht] at he
  have hh := Summable.tsum_le_tsum (factorial_tail_geometric N hd hr hdr)
    ((summable_nat_add_iff N).mpr hf) ((summable_geometric_of_lt_one hr hr1).mul_left (d^N/N.factorial))
  rw [tsum_mul_left,tsum_geometric_of_lt_one hr hr1] at hh
  rw [div_eq_mul_inv]
  linarith
lemma complex_exp_tail_bound (z : ℂ) (N : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1)
    (hz : ‖z‖ ≤ r*(N+1)) :
    ‖Complex.exp z-∑ i ∈ Finset.range N, z^i/i.factorial‖  ≤ 
      (‖z‖^N/N.factorial)/(1-r) :=
  (Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z N).trans
    (exp_tail_bound N (norm_nonneg z) hr hr1 hz)
end AtomicTriangular.Envelope
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma ri1_mem : (RI.point 1).Mem (1:ℝ) := by simpa using RI.mem_point 1
end AtomicTriangular.FiniteCertificate
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
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorPhaseBox_mem (q branch : Fin 2) (j : Fin 31) :
    (taylorPhaseBox q branch j).Mem (taylorPhase q branch (frequency j)) := by
  unfold taylorPhaseBox taylorPhase
  split_ifs
  · exact CI.mem_sub (CI.mem_mul (CI.mem_mul CI.mem_imag (CI.mem_ofReal piBox_mem)) (CI.mem_ofReal (realFrequencyBox_mem j)))
      (CI.mem_ofReal (RI.mem_mul piBox_mem (RI.mem_sub (dampingBox_mem q) (dampingBox_mem 0))))
  · exact wavePhaseBox_mem q 0 j

lemma taylorPhase0_0_calc (j : Fin 31) : taylorPhaseBox 0 0 j = taylorPhase0_0 j := by
  revert j
  decide +kernel
lemma taylorPhase0_0_mem (j : Fin 31) : (taylorPhase0_0 j).Mem (taylorPhase 0 0 (frequency j)) := by
  rw [← taylorPhase0_0_calc]
  exact taylorPhaseBox_mem 0 0 j
lemma taylorPhase0_1_calc (j : Fin 31) : taylorPhaseBox 0 1 j = taylorPhase0_1 j := by
  revert j
  decide +kernel
lemma taylorPhase0_1_mem (j : Fin 31) : (taylorPhase0_1 j).Mem (taylorPhase 0 1 (frequency j)) := by
  rw [← taylorPhase0_1_calc]
  exact taylorPhaseBox_mem 0 1 j
lemma taylorPhase1_0_calc (j : Fin 31) : taylorPhaseBox 1 0 j = taylorPhase1_0 j := by
  revert j
  decide +kernel
lemma taylorPhase1_0_mem (j : Fin 31) : (taylorPhase1_0 j).Mem (taylorPhase 1 0 (frequency j)) := by
  rw [← taylorPhase1_0_calc]
  exact taylorPhaseBox_mem 1 0 j
lemma taylorPhase1_1_calc (j : Fin 31) : taylorPhaseBox 1 1 j = taylorPhase1_1 j := by
  revert j
  decide +kernel
lemma taylorPhase1_1_mem (j : Fin 31) : (taylorPhase1_1 j).Mem (taylorPhase 1 1 (frequency j)) := by
  rw [← taylorPhase1_1_calc]
  exact taylorPhaseBox_mem 1 1 j
lemma taylorPhaseTable_mem (q br : Fin 2) (j : Fin 31) :
    (taylorPhaseTable q br j).Mem (taylorPhase q br (frequency j)) := by
  fin_cases q <;> fin_cases br
  · exact taylorPhase0_0_mem j
  · exact taylorPhase0_1_mem j
  · exact taylorPhase1_0_mem j
  · exact taylorPhase1_1_mem j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_CurvatureAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma curvatureWave_nonneg (q br : Fin 2) (s t : ℝ) : 0 ≤ curvatureWave q br s t := by
  unfold curvatureWave; positivity
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
-- module Solutions.OAIQ250_TR.Triangular_Taylor_FiniteTaylorIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma hasDerivAt_finiteWaveJet (q br : Fin 2) (t : ℝ) (k : ℕ) (s : ℂ) :
    HasDerivAt (finiteWaveJet q br t k) (finiteWaveJet q br t (k+1) s) s := by
  unfold finiteWaveJet
  have hh := (((hasDerivAt_id s).const_mul (taylorPhase q br t)).cexp.const_mul
    (taylorAmplitude q br t)).mul_const ((taylorPhase q br t)^k)
  simpa only [finiteWaveJet,mul_one,one_mul,pow_succ,mul_assoc,mul_comm,mul_left_comm,
    id_eq] using hh

lemma hasDerivAt_finiteJJet (side : Fin 2) (e : Fin 8 → ℝ) (k : ℕ) (s : ℂ) :
    HasDerivAt (finiteJJet side e k) (finiteJJet side e (k+1) s) s := by
  have hj (r : Fin 8) (q : Fin 2) (j : Fin 31) :=
    ((hasDerivAt_finiteWaveJet q 0 (frequency j) k s).const_mul (finiteSpectrum side q j r)).add
    ((hasDerivAt_finiteWaveJet q 1 (frequency j) k s).const_mul (finiteSpectrum (otherSide side) q j r))
  have hq (r : Fin 8) (q : Fin 2) := HasDerivAt.sum (u := Finset.univ) (fun j _ => hj r q j)
  have hr (r : Fin 8) := (HasDerivAt.sum (u := Finset.univ) (fun q _ => hq r q)).const_mul (e r:ℂ)
  simpa only [finiteJJet,Finset.sum_apply,Pi.add_apply] using!
    HasDerivAt.sum (u := Finset.univ) (fun r _ => hr r)
lemma finiteJJet_re_iterated (side : Fin 2) (e : Fin 8 → ℝ) (k : ℕ) :
    (fun s : ℝ => (finiteJJet side e k s).re) = iteratedDeriv k (finiteJ side e) := by
  induction k with
  | zero => rfl
  | succ k hk =>
    rw [iteratedDeriv_succ,← hk]
    exact funext fun s => ((hasDerivAt_finiteJJet side e k s).real_of_complex).deriv.symm
lemma taylorWave_eq (q br : Fin 2) (m : ℤ) (l : ℕ) (t : ℝ) :
    taylorWave q br m l t = finiteWaveJet q br t (l+2) m / ((l+2).factorial:ℂ) := rfl
lemma taylorRow_dot (side : Fin 2) (m : ℤ) (y : ℝ) (l : ℕ) (e : Fin 8 → ℝ) :
    (∑ r : Fin 8, taylorRow side m y l r*e r) =
      (iteratedDeriv (l+2) (finiteJ side e) m) * y^l / ((l+2).factorial:ℝ) := by
  rw [← finiteJJet_re_iterated]
  simp only [taylorRow,taylorWave_eq,finiteJJet,Complex.ofReal_intCast,
    ← mul_div_assoc,← add_div,← Finset.sum_div]
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  simp only [Finset.sum_mul,Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Complex.re_sum,← Complex.ofReal_natCast,Complex.div_ofReal_re,
    Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Complex.add_re]
  ring
lemma finiteTaylor_exact (side : Fin 2) (m : ℤ) (y : ℝ) (e : Fin 8 → ℝ) (τ : ℝ) :
    finiteTaylor side m y e τ = ∑ l ∈ Finset.range 21,
      (iteratedDeriv (l+2) (finiteJ side e) m) * y^l / ((l+2).factorial:ℝ) * τ^l := by
  unfold finiteTaylor
  apply Finset.sum_congr rfl
  intro l hl
  rw [taylorRow_dot]
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
-- module Solutions.OAIQ250_TR.Triangular_Signs_DeletedExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Envelope
open Complex

lemma exp_sum_split (z : ℂ) :
    (∑ i ∈ Finset.range 23, z^i/(i.factorial:ℂ)) =
      1+z+z^2*∑ j ∈ Finset.range 21, z^j/((j+2).factorial:ℂ) := by
  rw [show (23:ℕ)=2+21 by norm_num,Finset.sum_range_add]
  rw [show (∑ i ∈ Finset.range 2, z^i/(i.factorial:ℂ))=1+z by
    simp [Finset.sum_range_succ]]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  simp only [Nat.add_comm 2 j]
  ring
lemma expDeleted_remainder_eq (w : ℂ) (m v : ℝ) (hv : v≠0) :
    expDeleted w m v-expDeletedTaylor w m v =
      exp (w*(m:ℂ))/(v:ℂ)^2 *
        (exp (w*(v:ℂ))-∑ i ∈ Finset.range 23, (w*(v:ℂ))^i/(i.factorial:ℂ)) := by
  have hv' : (v:ℂ)≠0 := by exact_mod_cast hv
  simp only [expDeleted,ite_eq_right hv,expDeletedTaylor,ofReal_add,mul_add,exp_add,exp_sum_split]
  field_simp
  ring
lemma expDeleted_zero (w : ℂ) (m : ℝ) : expDeleted w m 0=expDeletedTaylor w m 0 := by
  simp [expDeleted,expDeletedTaylor,Finset.sum_range_succ]
  ring
lemma expDeleted_error (w : ℂ) (m v Y : ℝ) (hY : 0≤Y) (hv : |v|≤Y)
    (hr : Y*‖w‖/24<1) :
    ‖expDeleted w m v-expDeletedTaylor w m v‖ ≤
      ‖exp (w*(m:ℂ))‖*‖w‖^2*(Y*‖w‖)^21/(23).factorial/(1-Y*‖w‖/24) := by
  by_cases hv0 : v=0
  · subst v
    rw [expDeleted_zero,sub_self,norm_zero]
    positivity
  have hp : 0<1-Y*‖w‖/24 := sub_pos.mpr hr
  have hcoef : 0≤Y*‖w‖/24 := by positivity
  have hnorm : ‖w*(v:ℂ)‖≤(Y*‖w‖/24)*((23:ℝ)+1) := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    nlinarith [mul_le_mul_of_nonneg_left hv (norm_nonneg w)]
  have hb := complex_exp_tail_bound (w*(v:ℂ)) 23 hcoef hr hnorm
  rw [expDeleted_remainder_eq w m v hv0,norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  have hpos : 0 < |v| ^ 2 := sq_pos_of_pos (abs_pos.mpr hv0)
  calc
    _ ≤ (‖exp (w*(m:ℂ))‖/ |v|^2)*((‖w*(v:ℂ)‖^23/(23).factorial)/(1-Y*‖w‖/24)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ‖exp (w*(m:ℂ))‖*‖w‖^2*(|v| * ‖w‖)^21/(23).factorial/(1-Y*‖w‖/24) := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow]
      field_simp
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hp.le
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hv (norm_nonneg w)) 21
end AtomicTriangular.Envelope
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_DeletedJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Complex
namespace AtomicTriangular.Construction

lemma complexDeleted_re (F : ℕ → ℝ → ℂ) (f : ℝ → ℝ) (m v : ℝ)
    (h0 : ∀ s,(F 0 s).re=f s) (h1 : (F 1 m).re=deriv f m) (h2 : (F 2 m).re=iteratedDeriv 2 f m) :
    (complexDeleted F m v).re=deletedSecond f m (m+v) := by
  by_cases hv : v=0
  · subst v
    simp [complexDeleted,deletedSecond,h2]
  · have hs : m+v≠m := by intro hh; apply hv; linarith
    simp only [complexDeleted,ite_eq_right hv,deletedSecond,ite_eq_right hs,show m+v-m=v by ring,
      ←Complex.ofReal_pow,Complex.div_ofReal_re,sub_re,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero,h0,h1]
    ring
lemma complexDeleted_add (F G : ℕ → ℝ → ℂ) (m v : ℝ) :
    complexDeleted (fun k s => F k s+G k s) m v=complexDeleted F m v+complexDeleted G m v := by
  unfold complexDeleted
  split_ifs <;> ring
lemma complexDeleted_mul (a : ℂ) (F : ℕ → ℝ → ℂ) (m v : ℝ) :
    complexDeleted (fun k s => a*F k s) m v=a*complexDeleted F m v := by
  unfold complexDeleted
  split_ifs <;> ring
lemma complexDeleted_sum {ι : Type*} (S : Finset ι) (F : ι → ℕ → ℝ → ℂ) (m v : ℝ) :
    complexDeleted (fun k s => ∑ i∈S,F i k s) m v=∑ i∈S,complexDeleted (F i) m v := by
  unfold complexDeleted
  by_cases hv : v=0
  · simp only [hv,↓reduceIte,Finset.sum_div]
  · simp only [ite_eq_right hv,sub_div,Finset.sum_div,Finset.sum_sub_distrib,Finset.mul_sum]
lemma complexTaylor_add (F G : ℕ → ℝ → ℂ) (m v : ℝ) :
    complexTaylor (fun k s => F k s+G k s) m v=complexTaylor F m v+complexTaylor G m v := by
  simp [complexTaylor,add_mul,add_div,Finset.sum_add_distrib]
lemma complexTaylor_mul (a : ℂ) (F : ℕ → ℝ → ℂ) (m v : ℝ) :
    complexTaylor (fun k s => a*F k s) m v=a*complexTaylor F m v := by
  simp [complexTaylor,Finset.mul_sum,mul_assoc,mul_div_assoc]
lemma complexTaylor_sum {ι : Type*} (S : Finset ι) (F : ι → ℕ → ℝ → ℂ) (m v : ℝ) :
    complexTaylor (fun k s => ∑ i∈S,F i k s) m v=∑ i∈S,complexTaylor (F i) m v := by
  simp only [complexTaylor,Finset.sum_mul,Finset.sum_div]
  exact Finset.sum_comm
lemma complexDeleted_exp (w : ℂ) (m v : ℝ) :
    complexDeleted (fun k s => exp (w*(s:ℂ))*w^k) m v=Envelope.expDeleted w m v := by
  unfold complexDeleted Envelope.expDeleted
  split_ifs <;> simp only [pow_zero,pow_one,mul_one]
  ring
lemma complexTaylor_exp (w : ℂ) (m v : ℝ) :
    complexTaylor (fun k s => exp (w*(s:ℂ))*w^k) m v=Envelope.expDeletedTaylor w m v := by
  simp only [complexTaylor,Envelope.expDeletedTaylor,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add,mul_pow]
  ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open AtomicTriangular.FiniteCertificate
namespace AtomicTriangular.Construction

lemma nearRadius_nonneg (n : Fin 7) : 0≤nearRadius n := by
  fin_cases n <;> (first | (simp [nearRadius]; all_goals first | (norm_num [nearRadius]; done) | rfl | decide) | (norm_num [nearRadius]; done) | norm_num [nearRadius])
end AtomicTriangular.Construction
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma nearRadiusBox_mem (n : Fin 7) : (nearRadiusBox n).Mem (nearRadius n) := by
  fin_cases n <;> (first | (simp [nearRadiusBox,nearRadius,RI.Mem,RI.point,RI.divNat,scale]; all_goals first | (norm_num [nearRadiusBox,nearRadius,RI.Mem,RI.point,RI.divNat,scale]; done) | rfl | decide) | (norm_num [nearRadiusBox,nearRadius,RI.Mem,RI.point,RI.divNat,scale]; done) | norm_num [nearRadiusBox,nearRadius,RI.Mem,RI.point,RI.divNat,scale])
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorNorm00_check (j : Fin 31) : 0≤(taylorNorm00 j).lo ∧ (taylorNorm00 j).lo*(taylorNorm00 j).lo ≤ scale*max 0 (taylorPhaseTable 0 0 j).normSq.lo ∧ scale*(taylorPhaseTable 0 0 j).normSq.hi ≤ (taylorNorm00 j).hi*(taylorNorm00 j).hi ∧ 0≤(taylorNorm00 j).hi := by
  revert j
  decide +kernel
lemma taylorNorm00_mem (j : Fin 31) : (taylorNorm00 j).Mem ‖taylorPhase 0 0 (frequency j)‖ := by
  have hh := taylorNorm00_check j
  exact CI.mem_norm (taylorPhaseTable_mem 0 0 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma taylorNorm01_check (j : Fin 31) : 0≤(taylorNorm01 j).lo ∧ (taylorNorm01 j).lo*(taylorNorm01 j).lo ≤ scale*max 0 (taylorPhaseTable 0 1 j).normSq.lo ∧ scale*(taylorPhaseTable 0 1 j).normSq.hi ≤ (taylorNorm01 j).hi*(taylorNorm01 j).hi ∧ 0≤(taylorNorm01 j).hi := by
  revert j
  decide +kernel
lemma taylorNorm01_mem (j : Fin 31) : (taylorNorm01 j).Mem ‖taylorPhase 0 1 (frequency j)‖ := by
  have hh := taylorNorm01_check j
  exact CI.mem_norm (taylorPhaseTable_mem 0 1 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma taylorNorm10_check (j : Fin 31) : 0≤(taylorNorm10 j).lo ∧ (taylorNorm10 j).lo*(taylorNorm10 j).lo ≤ scale*max 0 (taylorPhaseTable 1 0 j).normSq.lo ∧ scale*(taylorPhaseTable 1 0 j).normSq.hi ≤ (taylorNorm10 j).hi*(taylorNorm10 j).hi ∧ 0≤(taylorNorm10 j).hi := by
  revert j
  decide +kernel
lemma taylorNorm10_mem (j : Fin 31) : (taylorNorm10 j).Mem ‖taylorPhase 1 0 (frequency j)‖ := by
  have hh := taylorNorm10_check j
  exact CI.mem_norm (taylorPhaseTable_mem 1 0 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma taylorNorm11_check (j : Fin 31) : 0≤(taylorNorm11 j).lo ∧ (taylorNorm11 j).lo*(taylorNorm11 j).lo ≤ scale*max 0 (taylorPhaseTable 1 1 j).normSq.lo ∧ scale*(taylorPhaseTable 1 1 j).normSq.hi ≤ (taylorNorm11 j).hi*(taylorNorm11 j).hi ∧ 0≤(taylorNorm11 j).hi := by
  revert j
  decide +kernel
lemma taylorNorm11_mem (j : Fin 31) : (taylorNorm11 j).Mem ‖taylorPhase 1 1 (frequency j)‖ := by
  have hh := taylorNorm11_check j
  exact CI.mem_norm (taylorPhaseTable_mem 1 1 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma taylorNormTable_mem (q br : Fin 2) (j : Fin 31) : (taylorNormTable q br j).Mem ‖taylorPhase q br (frequency j)‖ := by
  fin_cases q <;> fin_cases br
  · exact taylorNorm00_mem j
  · exact taylorNorm01_mem j
  · exact taylorNorm10_mem j
  · exact taylorNorm11_mem j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderData0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData0_00_pre (j : Fin 31) : (remainderExpInput 0 0 0 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 0).mul (taylorNormTable 0 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData0_01_pre (j : Fin 31) : (remainderExpInput 0 1 0 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 0).mul (taylorNormTable 0 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData0_10_pre (j : Fin 31) : (remainderExpInput 1 0 0 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 0).mul (taylorNormTable 1 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData0_11_pre (j : Fin 31) : (remainderExpInput 1 1 0 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 0).mul (taylorNormTable 1 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderData1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData1_00_pre (j : Fin 31) : (remainderExpInput 0 0 1 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 1).mul (taylorNormTable 0 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData1_01_pre (j : Fin 31) : (remainderExpInput 0 1 1 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 1).mul (taylorNormTable 0 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData1_10_pre (j : Fin 31) : (remainderExpInput 1 0 1 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 1).mul (taylorNormTable 1 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData1_11_pre (j : Fin 31) : (remainderExpInput 1 1 1 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 1).mul (taylorNormTable 1 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderData2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData2_00_pre (j : Fin 31) : (remainderExpInput 0 0 2 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 2).mul (taylorNormTable 0 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData2_01_pre (j : Fin 31) : (remainderExpInput 0 1 2 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 2).mul (taylorNormTable 0 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData2_10_pre (j : Fin 31) : (remainderExpInput 1 0 2 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 2).mul (taylorNormTable 1 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData2_11_pre (j : Fin 31) : (remainderExpInput 1 1 2 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 2).mul (taylorNormTable 1 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderData3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData3_00_pre (j : Fin 31) : (remainderExpInput 0 0 3 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 3).mul (taylorNormTable 0 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData3_01_pre (j : Fin 31) : (remainderExpInput 0 1 3 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 3).mul (taylorNormTable 0 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData3_10_pre (j : Fin 31) : (remainderExpInput 1 0 3 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 3).mul (taylorNormTable 1 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData3_11_pre (j : Fin 31) : (remainderExpInput 1 1 3 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 3).mul (taylorNormTable 1 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderData4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData4_00_pre (j : Fin 31) : (remainderExpInput 0 0 4 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 4).mul (taylorNormTable 0 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData4_01_pre (j : Fin 31) : (remainderExpInput 0 1 4 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 4).mul (taylorNormTable 0 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData4_10_pre (j : Fin 31) : (remainderExpInput 1 0 4 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 4).mul (taylorNormTable 1 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData4_11_pre (j : Fin 31) : (remainderExpInput 1 1 4 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 4).mul (taylorNormTable 1 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderData5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData5_00_pre (j : Fin 31) : (remainderExpInput 0 0 5 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 5).mul (taylorNormTable 0 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData5_01_pre (j : Fin 31) : (remainderExpInput 0 1 5 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 5).mul (taylorNormTable 0 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData5_10_pre (j : Fin 31) : (remainderExpInput 1 0 5 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 5).mul (taylorNormTable 1 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData5_11_pre (j : Fin 31) : (remainderExpInput 1 1 5 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 5).mul (taylorNormTable 1 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderData6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData6_00_pre (j : Fin 31) : (remainderExpInput 0 0 6 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 6).mul (taylorNormTable 0 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData6_01_pre (j : Fin 31) : (remainderExpInput 0 1 6 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 6).mul (taylorNormTable 0 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData6_10_pre (j : Fin 31) : (remainderExpInput 1 0 6 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 6).mul (taylorNormTable 1 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData6_11_pre (j : Fin 31) : (remainderExpInput 1 1 6 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 6).mul (taylorNormTable 1 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderPre
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainder_all_pre (q br : Fin 2) (n : Fin 7) (j : Fin 31) :
    0<((RI.point 1).sub (((nearRadiusBox n).mul (taylorNormTable q br j)).divNat 24)).lo := by
  fin_cases n <;> fin_cases q <;> fin_cases br
  · exact (remainderData0_00_pre j).2
  · exact (remainderData0_01_pre j).2
  · exact (remainderData0_10_pre j).2
  · exact (remainderData0_11_pre j).2
  · exact (remainderData1_00_pre j).2
  · exact (remainderData1_01_pre j).2
  · exact (remainderData1_10_pre j).2
  · exact (remainderData1_11_pre j).2
  · exact (remainderData2_00_pre j).2
  · exact (remainderData2_01_pre j).2
  · exact (remainderData2_10_pre j).2
  · exact (remainderData2_11_pre j).2
  · exact (remainderData3_00_pre j).2
  · exact (remainderData3_01_pre j).2
  · exact (remainderData3_10_pre j).2
  · exact (remainderData3_11_pre j).2
  · exact (remainderData4_00_pre j).2
  · exact (remainderData4_01_pre j).2
  · exact (remainderData4_10_pre j).2
  · exact (remainderData4_11_pre j).2
  · exact (remainderData5_00_pre j).2
  · exact (remainderData5_01_pre j).2
  · exact (remainderData5_10_pre j).2
  · exact (remainderData5_11_pre j).2
  · exact (remainderData6_00_pre j).2
  · exact (remainderData6_01_pre j).2
  · exact (remainderData6_10_pre j).2
  · exact (remainderData6_11_pre j).2
lemma remainder_ratio_lt_one (q br : Fin 2) (n : Fin 7) (j : Fin 31) :
    nearRadius n*‖taylorPhase q br (frequency j)‖/24<1 := by
  have hh := (RI.mem_sub ri1_mem (RI.mem_divNat
    (RI.mem_mul (nearRadiusBox_mem n) (taylorNormTable_mem q br j)) (by norm_num : 0<24))).1
  have hp : (0:ℝ)<((RI.point 1).sub (((nearRadiusBox n).mul (taylorNormTable q br j)).divNat 24)).lo :=
    by exact_mod_cast remainder_all_pre q br n j
  have hs := AtomicTriangular.Interval.scale_pos
  nlinarith
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_FiniteRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

lemma complexError_add (F G : ℕ → ℝ → ℂ) (m v : ℝ) :
    complexError (fun k s => F k s+G k s) m v=complexError F m v+complexError G m v := by
  simp only [complexError,complexDeleted_add,complexTaylor_add]
  ring
lemma complexError_mul (a : ℂ) (F : ℕ → ℝ → ℂ) (m v : ℝ) :
    complexError (fun k s => a*F k s) m v=a*complexError F m v := by
  simp only [complexError,complexDeleted_mul,complexTaylor_mul]
  ring
lemma complexError_sum {ι : Type*} (S : Finset ι) (F : ι → ℕ → ℝ → ℂ) (m v : ℝ) :
    complexError (fun k s => ∑ i∈S,F i k s) m v=∑ i∈S,complexError (F i) m v := by
  simp only [complexError,complexDeleted_sum,complexTaylor_sum,Finset.sum_sub_distrib]
lemma finiteWave_error (q br : Fin 2) (n : Fin 7) (j : Fin 31) {v : ℝ} (hv : |v|≤nearRadius n) :
    ‖complexError (fun k s => finiteWaveJet q br (frequency j) k s) (nearNode n) v‖≤
      remainderWave q br (nearNode n) (nearRadius n) (frequency j) := by
  have he : (fun (k : ℕ) (s : ℝ) => finiteWaveJet q br (frequency j) k s)=
      (fun (k : ℕ) (s : ℝ) => taylorAmplitude q br (frequency j)*(Complex.exp (taylorPhase q br (frequency j)*(s:ℂ))*(taylorPhase q br (frequency j))^k)) := by
    funext k s; simp only [finiteWaveJet,mul_assoc]
  rw [he,complexError_mul,complexError,complexDeleted_exp,complexTaylor_exp,norm_mul]
  have hb := Envelope.expDeleted_error (taylorPhase q br (frequency j)) (nearNode n) v (nearRadius n)
    (nearRadius_nonneg n) hv (remainder_ratio_lt_one q br n j)
  have hh := mul_le_mul_of_nonneg_left hb (norm_nonneg (taylorAmplitude q br (frequency j)))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | (simp only [remainderWave,curvatureWave,Complex.norm_exp,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]; ring)
lemma remainderWave_nonneg (q br : Fin 2) (n : Fin 7) (j : Fin 31) :
    0 ≤ remainderWave q br (nearNode n) (nearRadius n) (frequency j) := by
  unfold remainderWave
  have hp := sub_pos.mpr (remainder_ratio_lt_one q br n j)
  have hy := nearRadius_nonneg n
  have hc := curvatureWave_nonneg q br (nearNode n) (frequency j)
  positivity
lemma rawRemainderColumn_nonneg (br : Fin 2) (n : Fin 7) (c : Fin 22) :
    0 ≤ rawRemainderColumn br n c := Finset.sum_nonneg fun j _ => mul_nonneg (remainderWave_nonneg 1 br n j) (norm_nonneg _)
lemma inputJJet_zero_tail (C : ℝ) (a : TrigonometricCoefficients) (br : Fin 2) (k : ℕ) (s : ℂ) :
    inputJJet (coefficientInput C a 0) br k s=
      (C:ℂ)*(∑ j : Fin 31,fourierCoeff j*finiteWaveJet 0 br (frequency j) k s)+
      ∑ c : Fin 22,(a c:ℂ)*(∑ j : Fin 31,finiteColumn ⟨c.val,by omega⟩ j*finiteWaveJet 1 br (frequency j) k s) := by
  rw [inputJJet,tailSpectral_zero_coeff,finiteSpectral_coefficient_apply]
  simp only [_root_.smul_apply,smul_eq_mul,spectralPCLM_apply,spectralP,waveFunctionJet_apply]
lemma atom_remainder_bound (S : Fin 31 → ℂ) (q br : Fin 2) (n : Fin 7) {v : ℝ} (hv : |v|≤nearRadius n) :
    ‖complexError (fun k s => ∑ j : Fin 31,S j*finiteWaveJet q br (frequency j) k s) (nearNode n) v‖≤
      ∑ j : Fin 31,remainderWave q br (nearNode n) (nearRadius n) (frequency j)*‖S j‖ := by
  rw [complexError_sum]
  simp only [complexError_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul,mul_comm]
  exact mul_le_mul_of_nonneg_right (finiteWave_error q br n j hv) (norm_nonneg _)
lemma finite_input_error (C : ℝ) (a : TrigonometricCoefficients) (br : Fin 2) (n : Fin 7) {v M : ℝ}
    (hv : |v|≤nearRadius n) (hM : ∀ c : Fin 22,rawRemainderColumn br n c≤M) :
    ‖complexError (fun k s => inputJJet (coefficientInput C a 0) br k s) (nearNode n) v‖≤
      |C| *rawRemainderConstant br n+‖a‖*M := by
  simp only [inputJJet_zero_tail]
  rw [complexError_add,complexError_mul]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (atom_remainder_bound fourierCoeff 0 br n hv) (abs_nonneg _)
  · rw [complexError_sum]
    simp only [complexError_mul]
    calc
      _ ≤ ∑ c : Fin 22,‖(a c:ℂ)*complexError (fun k s => ∑ j : Fin 31,finiteColumn ⟨c.val,by omega⟩ j*finiteWaveJet 1 br (frequency j) k s) (nearNode n) v‖ := norm_sum_le _ _
      _ ≤ ∑ c : Fin 22,|a c| *M := by
        apply Finset.sum_le_sum
        intro c _
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left ((atom_remainder_bound _ 1 br n hv).trans (hM c)) (abs_nonneg _)
      _ = ‖a‖*M := by rw [←Finset.sum_mul,AtomicTriangular.L1Kernel.l1_norm,tsum_fintype]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_FiniteTaylorError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma finiteJ_remainder (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) (n : Fin 7) {v : ℝ}
    (hv : |v|≤nearRadius n) :
    ‖complexError (fun k s => finiteJJet side (actualParameter z) k s) (nearNode n) v‖ <
      (if n.val=0 then (161/100000:ℝ) else 75/10000000) := by
  obtain ⟨c,_,hc⟩ := Finset.exists_max_image Finset.univ (rawRemainderColumn 0 n) Finset.univ_nonempty
  obtain ⟨d,_,hd⟩ := Finset.exists_max_image Finset.univ (rawRemainderColumn 1 n) Finset.univ_nonempty
  have h0 := finite_input_error ((gamma side *ᵥ actualParameter z) 2) (finiteApprox side (actualParameter z)) 0 n hv (fun i => hc i (Finset.mem_univ i))
  have h1 := finite_input_error ((gamma (otherSide side) *ᵥ actualParameter z) 2) (finiteApprox (otherSide side) (actualParameter z)) 1 n hv (fun i => hd i (Finset.mem_univ i))
  have hg (side : Fin 2) : |(gamma side *ᵥ actualParameter z) 2|=6/1000 := by
    rw [gamma_actual]
    change |(if side.val=0 then -(3/500:ℝ) else 3/500)|=6/1000
    fin_cases side <;> (first | (simp; all_goals first | (norm_num; done) | rfl | decide) | (norm_num; done) | norm_num)
  rw [hg] at h0 h1
  have ha := mul_le_mul_of_nonneg_right (finiteApprox_norm_x side (actualParameter z) (actualParameter_mem hz hzB)).le (rawRemainderColumn_nonneg 0 n c)
  have hb := mul_le_mul_of_nonneg_right (finiteApprox_norm_x (otherSide side) (actualParameter z) (actualParameter_mem hz hzB)).le (rawRemainderColumn_nonneg 1 n d)
  simp only [finiteJJet_pair,pairJJet]
  rw [complexError_add]
  have hh := norm_add_le
    (complexError (fun k s => inputJJet (coefficientInput ((gamma side *ᵥ actualParameter z) 2) (finiteApprox side (actualParameter z)) 0) 0 k s) (nearNode n) v)
    (complexError (fun k s => inputJJet (coefficientInput ((gamma (otherSide side) *ᵥ actualParameter z) 2) (finiteApprox (otherSide side) (actualParameter z)) 0) 1 k s) (nearNode n) v)
  have htab := remainder_table_x n c d
  linarith
lemma complexDeleted_finiteJ (side : Fin 2) (e : Fin 8 → ℝ) (m v : ℝ) :
    (complexDeleted (fun k s => finiteJJet side e k s) m v).re=deletedSecond (finiteJ side e) m (m+v) := by
  apply complexDeleted_re
  · intro s; rfl
  · simpa only [iteratedDeriv_one] using congrFun (finiteJJet_re_iterated side e 1) m
  · exact congrFun (finiteJJet_re_iterated side e 2) m
lemma complexTaylor_finiteJ (side : Fin 2) (e : Fin 8 → ℝ) (m : ℤ) (y τ : ℝ) :
    (complexTaylor (fun k s => finiteJJet side e k s) m (y*τ)).re=finiteTaylor side m y e τ := by
  rw [finiteTaylor_exact]
  simp only [complexTaylor,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [←Complex.ofReal_natCast,Complex.div_ofReal_re,←Complex.ofReal_pow,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  rw [congrFun (finiteJJet_re_iterated side e (j+2)) m,mul_pow]
  ring
lemma finiteTaylor_error_x_oai (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) (n : Fin 7) {y τ : ℝ}
    (hv : |y*τ|≤nearRadius n) :
    |deletedSecond (finiteJ side (actualParameter z)) (nearNode n) (nearNode n+y*τ)-finiteTaylor side (nearNode n) y (actualParameter z) τ| <
      (if n.val=0 then (161/100000:ℝ) else 75/10000000) := by
  rw [←complexDeleted_finiteJ,←complexTaylor_finiteJ,←Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans_lt (finiteJ_remainder side hz hzB n hv)
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.finiteTaylor_error_x_oai := @OAI.AtomicTriangular.Construction.finiteTaylor_error_x_oai
