-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.psiC25_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:38:57.489095+00:00
-- url     : https://prove2.me/submissions/1cba7548-e82b-4951-b037-a49025f0adcd

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X004
import Definitions.Def_OAIQ257X005

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

lemma RI.mem_abs {a : RI} {x : ℝ} (hx : a.Mem x) : a.abs.Mem |x| := by
  rcases hx with ⟨hl,hu⟩
  change (↑(max 0 (max a.lo (-a.hi))) : ℝ) ≤ (scale:ℝ)*|x| ∧
    (scale:ℝ)*|x| ≤ ↑(max a.hi (-a.lo))
  push_cast
  rw [← abs_of_pos scale_pos, ← abs_mul]
  constructor
  · exact max_le (abs_nonneg _) (max_le (hl.trans (le_abs_self _)) (by simpa using (neg_le_neg hu).trans (neg_le_abs _)))
  · exact (abs_le.mpr ⟨by linarith [le_max_right (a.hi:ℝ) (-(a.lo:ℝ))], hu.trans (le_max_left _ _)⟩)

lemma RI.mem_inv {a : RI} {x : ℝ} (hx : a.Mem x) (ha : 0 < a.lo ∨ a.hi < 0) :
    a.inv.Mem x⁻¹ := by
  unfold RI.inv
  split_ifs with hh
  · have hp : 0 < a.neg.lo := by simpa [RI.neg] using neg_pos.mpr hh
    simpa using RI.mem_neg (RI.mem_invPos (RI.mem_neg hx) hp)
  · exact RI.mem_invPos hx (ha.resolve_right hh)

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
namespace AtomicTriangular.Constants

lemma bStar_bracket : bStar < Real.sqrt 3 / 2 ∧ Real.sqrt 3 / 2 < bStar + eps := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3:ℝ)
  have hp : 0 < bStar := by norm_num [bStar]
  have he : 0 < eps := by norm_num [eps]
  have h₁ : bStar^2 < (3:ℝ)/4 := by norm_num [bStar]
  have h₂ : (3:ℝ)/4 < (bStar+eps)^2 := by norm_num [bStar, eps]
  constructor <;> nlinarith

end AtomicTriangular.Constants

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma jetBox3_25_calc : waveDerivativeBox 3 25 = jetBox3_25 := by decide +kernel
lemma jetBox3_25_mem : jetBox3_25.Mem (waveDerivative 3 ((25:ℤ):ℂ)) := by
  rw [← jetBox3_25_calc]
  exact waveDerivativeBox_mem 3 25
lemma DBox25_calc : jetBox3_25.re.mul ((RI.point 6).mul QBox25).inv = DBox25 := by decide +kernel
lemma DBox25_mem : DBox25.Mem (D 25) := by
  rw [← DBox25_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_25_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox25_mem
  · left; decide +kernel
end AtomicTriangular.FiniteCertificate

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators FourierTransform

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex

lemma bBox_mem : bBox.Mem b := by
  obtain ⟨hl,hu⟩ := Constants.bStar_bracket
  constructor <;> dsimp [RI.Mem, bBox]
  · have hr : (bBox.lo:ℝ)/(scale:ℝ) ≤ Constants.bStar := by norm_num [bBox,scale,Constants.bStar]
    simpa only [b, mul_comm, bBox] using (div_le_iff₀ scale_pos).mp (hr.trans hl.le)
  · have hr : Constants.bStar+Constants.eps ≤ (bBox.hi:ℝ)/(scale:ℝ) := by
      norm_num [bBox,scale,Constants.bStar,Constants.eps]
    simpa only [b,mul_comm,bBox] using (le_div_iff₀ scale_pos).mp (hu.le.trans hr)

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
lemma bdenBox_pos (q : Fin 2) (j : Fin 31) : 0 < (bBox.mul (denBox q j)).lo := by
  revert q j
  decide +kernel

lemma xwaveBox_mem (q : Fin 2) (j : Fin 31) :
    (xwaveBox q j).Mem (Xwave (damping q) (frequency j)) := by
  unfold Xwave
  rw [div_eq_mul_inv]
  exact RI.mem_mul (by simpa using RI.mem_divNat (RI.mem_point 4) (by norm_num : 0<(3:ℕ)))
    (RI.mem_invPos (denBox_mem q j) (denBox_pos q j))

lemma lambdaBox_mem (q : Fin 2) (j : Fin 31) :
    (lambdaBox q j).Mem (lambda (damping q) (frequency j)) := by
  unfold lambda
  rw [div_eq_mul_inv,← Complex.ofReal_inv]
  exact CI.mem_mul (CI.mem_add (CI.mem_ofReal (dampingBox_mem q))
    (CI.mem_mul CI.mem_imag (CI.mem_ofReal (realFrequencyBox_mem j))))
    (CI.mem_ofReal (RI.mem_invPos (RI.mem_mul bBox_mem (denBox_mem q j)) (bdenBox_pos q j)))

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
-- module Solutions.OAIQ250_TR.Triangular_Certificate_WaveExpData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma lambdaTable0_calc (j : Fin 31) : lambdaBox 0 j = lambdaTable0 j := by
  revert j
  decide +kernel
lemma lambdaTable0_mem (j : Fin 31) : (lambdaTable0 j).Mem (lambda (damping 0) (frequency j)) := by
  rw [← lambdaTable0_calc]
  exact lambdaBox_mem 0 j
lemma lambdaTable1_calc (j : Fin 31) : lambdaBox 1 j = lambdaTable1 j := by
  revert j
  decide +kernel
lemma lambdaTable1_mem (j : Fin 31) : (lambdaTable1 j).Mem (lambda (damping 1) (frequency j)) := by
  rw [← lambdaTable1_calc]
  exact lambdaBox_mem 1 j
lemma lambdaTable_mem (q : Fin 2) (j : Fin 31) : (lambdaTable q j).Mem (lambda (damping q) (frequency j)) := by
  fin_cases q
  · exact lambdaTable0_mem j
  · exact lambdaTable1_mem j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

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
end AtomicTriangular.Construction
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
lemma ri_exp_mem {a : RI} {x : ℝ} (hx : a.Mem x)
    (h : (CI.ofReal a).normSq.hi ≤ scale*1024^2) :
    (CI.ofReal a).exp.re.Mem (Real.exp x) := by
  have hh := (CI.mem_exp_checked (CI.mem_ofReal hx) h).1
  simpa only [← Complex.ofReal_exp,Complex.ofReal_re] using hh

lemma decayBox_mem (q v : Fin 2) (j : Fin 31) :
    (decayBox q v j).Mem (frequencyDecay (damping q) (damping v) (frequency j)) := by
  have hh := RI.mem_neg (wavePhaseBox_mem q v j).1
  convert hh using 1
  · rfl
  · rw [wavePhase_re]
    unfold frequencyDecay
    ring

lemma decayExpBox_mem (q v : Fin 2) (n : ℤ) (j : Fin 31)
    (hh : (CI.ofReal ((decayBox q v j).neg.mul (RI.point n))).normSq.hi ≤ scale*1024^2) :
    (decayExpBox q v n j).Mem (Real.exp (-frequencyDecay (damping q) (damping v) (frequency j)*n)) :=
  ri_exp_mem (RI.mem_mul (RI.mem_neg (decayBox_mem q v j)) (RI.mem_point n)) hh

lemma psiBox_mem (q v : Fin 2) (n : ℤ) (j : Fin 31) {qb db lell dnorm ex : RI}
    (hq : qb.Mem (Q n)) (hd : db.Mem (D n))
    (hl : lell.Mem ‖lambda (damping q) (frequency j)‖)
    (hn : dnorm.Mem ‖I*Real.pi*zeta (damping q) (damping v) (frequency j)‖)
    (he : ex.Mem (Real.exp (-frequencyDecay (damping q) (damping v) (frequency j)*n)))
    (hqp : 0<qb.lo) :
    (psiBox q v n j qb db lell dnorm ex).Mem (normJetEnvelope (damping q) (damping v) n (frequency j)) := by
  exact RI.mem_mul (RI.mem_mul (RI.mem_mul (RI.mem_add (RI.mem_add ri1_mem (RI.mem_abs hd)) hn) hl)
    (RI.mem_invPos hq hqp)) he
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeWaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma lambdaNorm1_check (j : Fin 31) : 0≤(lambdaNorm1 j).lo ∧ (lambdaNorm1 j).lo*(lambdaNorm1 j).lo ≤ scale*max 0 (lambdaTable 1 j).normSq.lo ∧ scale*(lambdaTable 1 j).normSq.hi ≤ (lambdaNorm1 j).hi*(lambdaNorm1 j).hi ∧ 0≤(lambdaNorm1 j).hi := by
  revert j
  decide +kernel
lemma lambdaNorm1_mem (j : Fin 31) : (lambdaNorm1 j).Mem ‖lambda (damping 1) (frequency j)‖ := by
  have hh := lambdaNorm1_check j
  exact CI.mem_norm (lambdaTable_mem 1 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma envelopePhase10_calc (j : Fin 31) : wavePhaseBox 1 0 j=envelopePhase10 j := by
  revert j
  decide +kernel
lemma envelopePhase10_mem (j : Fin 31) : (envelopePhase10 j).Mem (I*Real.pi*zeta (damping 1) (damping 0) (frequency j)) := by
  rw [← envelopePhase10_calc]
  exact wavePhaseBox_mem 1 0 j
lemma phaseNorm10_check (j : Fin 31) : 0≤(phaseNorm10 j).lo ∧ (phaseNorm10 j).lo*(phaseNorm10 j).lo ≤ scale*max 0 (envelopePhase10 j).normSq.lo ∧ scale*(envelopePhase10 j).normSq.hi ≤ (phaseNorm10 j).hi*(phaseNorm10 j).hi ∧ 0≤(phaseNorm10 j).hi := by
  revert j
  decide +kernel
lemma phaseNorm10_mem (j : Fin 31) : (phaseNorm10 j).Mem ‖I*Real.pi*zeta (damping 1) (damping 0) (frequency j)‖ := by
  have hh := phaseNorm10_check j
  exact CI.mem_norm (envelopePhase10_mem j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopePsiC
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma envelopeExpC25_calc (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 25))).exp.re=envelopeExpC25 j := by
  revert j
  decide +kernel
lemma envelopeExpC25_pre (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 25))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpC25_mem (j : Fin 31) : (envelopeExpC25 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*25)) := by
  rw [← envelopeExpC25_calc]
  have hh := decayExpBox_mem 1 0 25 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC25_pre j)
lemma psiC25_calc (j : Fin 31) : psiBox 1 0 25 j QBox25 DBox25 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC25 j)=psiC25 j := by
  revert j
  decide +kernel
lemma psiC25_mem_x_oai (j : Fin 31) : (psiC25 j).Mem (normJetEnvelope (damping 1) (damping 0) 25 (frequency j)) := by
  rw [← psiC25_calc]
  apply psiBox_mem
  · exact QBox25_mem
  · exact DBox25_mem
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC25_mem j
  · decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.psiC25_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.psiC25_mem_x_oai
