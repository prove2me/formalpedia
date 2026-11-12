-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.finiteSpectral_curvature_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:17:59.381026+00:00
-- url     : https://prove2.me/submissions/461e808e-dfaf-4f3d-9b79-8226687ba901

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X011
import Theorems.Thm_OAI_AtomicTriangular_Construction_finiteCurvatureCap_bound_x

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_Analytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma wavePhase_re (k v t : ℝ) : (I*Real.pi*zeta k v t).re = -Real.pi*(k*Xwave k t-v) := by
  simp [zeta,mul_re,mul_im]

lemma Xwave_antitone {k s t : ℝ} (hk : 0<k) (hs : 0 ≤ s) (hst : s ≤ t) :
    Xwave k t≤Xwave k s := by
  unfold Xwave
  apply div_le_div_of_nonneg_left (by norm_num) (waveDen_pos hk s)
  unfold waveDen
  nlinarith
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
-- module Solutions.OAIQ250_TR.Triangular_Envelope_TailEnvelopeSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma frequencyDecay_pos (q v : Fin 2) {t : ℝ} (ht : |t|≤5/6) :
    0 < frequencyDecay (damping q) (damping v) t := by
  have hx := Xwave_antitone (damping_pos q) (abs_nonneg t) ht
  have he : Xwave (damping q) |t|=Xwave (damping q) t := by simp [Xwave,waveDen,sq_abs]
  rw [he] at hx
  have hb : damping v < damping q * Xwave (damping q) (5/6) := by
    fin_cases q <;> fin_cases v <;> (first | (simp [damping,h,H,Xwave,waveDen]; all_goals first | (norm_num [damping,h,H,Xwave,waveDen]; done) | rfl | decide) | (norm_num [damping,h,H,Xwave,waveDen]; done) | norm_num [damping,h,H,Xwave,waveDen])
  unfold frequencyDecay
  exact mul_pos Real.pi_pos (sub_pos.mpr (hb.trans_le (mul_le_mul_of_nonneg_left hx (damping_pos q).le)))
end AtomicTriangular.Construction
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

lemma taylorPhase_re_nonpos (q br : Fin 2) {t : ℝ} (ht : |t|≤5/6) :
    (taylorPhase q br t).re≤0 := by
  fin_cases br
  · simp only [taylorPhase,↓reduceIte,sub_re,mul_re,mul_im,I_re,I_im,
      ofReal_re,ofReal_im,mul_zero,zero_mul,sub_zero,zero_sub]
    have hh : h≤damping q := by fin_cases q <;> (first | (simp [damping,h,H]; all_goals first | (norm_num [damping,h,H]; done) | rfl | decide) | (norm_num [damping,h,H]; done) | norm_num [damping,h,H])
    exact neg_nonpos.mpr (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hh))
  · change (I*Real.pi*zeta (damping q) h t).re≤0
    rw [wavePhase_re]
    have hh := (frequencyDecay_pos q 0 ht).le
    change 0≤Real.pi*(damping q*Xwave (damping q) t-h) at hh
    nlinarith

lemma curvatureWave_antitone (q br : Fin 2) {s u t : ℝ} (ht : |t|≤5/6) (hsu : s≤ u) :
    curvatureWave q br u t ≤ curvatureWave q br s t := by
  unfold curvatureWave
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hsu (taylorPhase_re_nonpos q br ht))
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

lemma norm_finiteWaveJet_two (q br : Fin 2) (s t : ℝ) :
    ‖finiteWaveJet q br t 2 s‖=curvatureWave q br s t := by
  simp only [finiteWaveJet,norm_mul,norm_pow,Complex.norm_exp,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero,curvatureWave]
  ring
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
lemma finiteSpectral_wave_bound (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (br : Fin 2) (s : ℝ) {M : ℝ} (hb : ∀ c : Fin 22, rawCurvatureColumn br s c ≤ M) :
    ‖finiteSpectral (coefficientInput C a w) (waveFunctionJet 1 br 2 s)‖ ≤ ‖a‖*M := by
  rw [finiteSpectral_coefficient_apply]
  calc
    _ ≤ ∑ c : Fin 22, ‖(a c:ℂ)*(∑ j : Fin 31, finiteColumn ⟨c.val,by omega⟩ j * waveFunctionJet 1 br 2 s ⟨frequency j,frequency_mem j⟩)‖ := norm_sum_le _ _
    _ ≤ ∑ c : Fin 22, |a c| * rawCurvatureColumn br s c := by
      apply Finset.sum_le_sum
      intro c _
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul,waveFunctionJet_apply,norm_finiteWaveJet_two]
      exact le_of_eq (mul_comm _ _)
    _ ≤ ∑ c : Fin 22, |a c| * M := Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hb c) (abs_nonneg _)
    _ = _ := by rw [←Finset.sum_mul,l1_norm,tsum_fintype]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_CurvatureEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open Complex AtomicTriangular.FiniteCertificate

lemma rawCurvatureColumn_antitone (br : Fin 2) (c : Fin 22) {u s : ℝ} (hus : u≤ s) :
    rawCurvatureColumn br s c ≤ rawCurvatureColumn br u c := by
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (curvatureWave_antitone 1 br (abs_le.mpr (frequency_mem j)) hus) (norm_nonneg _)
lemma finiteSpectral_curvature_x_oai (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (br : Fin 2) (i : Fin 5) {s : ℝ} (hs : curvaturePoint i≤ s) :
    ‖finiteSpectral (coefficientInput C a w) (waveFunctionJet 1 br 2 s)‖≤‖a‖*finiteCurvatureCap br i := by
  apply finiteSpectral_wave_bound
  intro c
  exact (rawCurvatureColumn_antitone br c hs).trans (finiteCurvatureCap_bound_x br i c)
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.finiteSpectral_curvature_x_oai := @OAI.AtomicTriangular.Construction.finiteSpectral_curvature_x_oai
