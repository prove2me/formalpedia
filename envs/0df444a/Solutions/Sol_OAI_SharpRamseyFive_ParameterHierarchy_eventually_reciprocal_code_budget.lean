-- Prove2me | solution 1 for OAI.SharpRamseyFive.ParameterHierarchy.eventually_reciprocal_code_budget
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:08:55.501165+00:00
-- url     : https://prove2.me/submissions/589b63ae-9a74-41cb-8230-341cba08bb89

import Mathlib
import Definitions.Def_OAIQ060R001

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Beta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ParameterHierarchy
open Filter Asymptotics
open scoped Topology

lemma beta_pos {η : ℝ} (h : 0 < η) : 0 < beta η := by unfold beta; positivity

end SharpRamseyFive.ParameterHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OrientedTreeCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module ReverseCap ScoreGeometry PivotTree BinaryTree Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

lemma nodeChargeConstant_nonneg : 0≤nodeChargeConstant := by
  have h1 : Real.log ((9:ℝ)/100000)≤0 := Real.log_nonpos (by norm_num) (by norm_num)
  have h2 : Real.log ((9:ℝ)/10)≤0 := Real.log_nonpos (by norm_num) (by norm_num)
  unfold nodeChargeConstant
  linarith only [h1,h2]

end

open Module ReverseCap ScoreGeometry PivotTree BinaryTree Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology BigOperators

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_StageNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Asymptotics Real
open scoped Topology
noncomputable section

lemma stage_cost_monomial {σ D P H w Cw b η : ℝ} (hσ : 1≤σ)
    (hD : 0≤D) (hP : 0≤P) (hH : 0≤H) (hw : 0≤w) (_hC : 0≤Cw)
    (hb : 0≤b) (hη : 0≤η)
    (hP' : P≤4*D*σ^(9*b)) (hH' : H≤σ^b)
    (hw' : D*w≤Cw*σ^(1+η/2)) :
    P*H*(σ+w*P)≤(4+16*Cw)*D*σ^(1+η/2+19*b) := by
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hPH : P*H≤4*D*σ^(10*b) := by
    calc
      _ ≤ (4*D*σ^(9*b))*σ^b := mul_le_mul hP' hH' hH (by positivity)
      _ = _ := by rw [mul_assoc,←Real.rpow_add hs];congr 2;ring
  have hwP : w*P≤4*Cw*σ^(1+η/2+9*b) := by
    calc
      w*P≤w*(4*D*σ^(9*b)) := mul_le_mul_of_nonneg_left hP' hw
      _ =4*(D*w)*σ^(9*b) := by ring
      _ ≤4*(Cw*σ^(1+η/2))*σ^(9*b) := by gcongr
      _ = _ := by rw [Real.rpow_add hs (1+η/2) (9*b)];ring
  have hfirst : (4*D*σ^(10*b))*σ≤4*D*σ^(1+η/2+19*b) := by
    calc
      _ =4*D*σ^(1+10*b) := by rw [Real.rpow_add hs,Real.rpow_one];ring
      _ ≤_ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hσ (by linarith)) (by positivity)
  have hsecond : (4*D*σ^(10*b))*(4*Cw*σ^(1+η/2+9*b))=
      16*Cw*D*σ^(1+η/2+19*b) := by
    calc
      _ =16*Cw*D*(σ^(10*b)*σ^(1+η/2+9*b)) := by ring
      _ =_ := by rw [←Real.rpow_add hs];congr 2;ring
  calc
    P*H*(σ+w*P)≤(4*D*σ^(10*b))*(σ+4*Cw*σ^(1+η/2+9*b)) :=
      mul_le_mul hPH (add_le_add le_rfl hwP) (by positivity) (by positivity)
    _ = (4*D*σ^(10*b))*σ+(4*D*σ^(10*b))*(4*Cw*σ^(1+η/2+9*b)) := by ring
    _ ≤4*D*σ^(1+η/2+19*b)+16*Cw*D*σ^(1+η/2+19*b) := by rw [hsecond];exact add_le_add hfirst le_rfl
    _ =_ := by ring

theorem eventually_stage_entropy_bound {η : ℝ} (hη : 0<η)
    (C Cw : ℝ) (hC : 0≤C) (hCw : 0≤Cw) :
    ∀ᶠ σ : ℝ in atTop,∀ (q D P H w k Λ : ℝ),0<q→0≤D→0≤P→0≤H→0≤w→
      P≤4*D*σ^(9*beta η)→H≤σ^beta η→D*w≤Cw*σ^(1+η/2)→
      q*σ^(1+η)≤2*k→Λ≤C*q*(P*H*(σ+w*P))→Λ/k≤D*σ^(-η/3) := by
  have he : 0<η/6-19*beta η := by unfold beta;linarith
  have ht : Tendsto (fun σ : ℝ=>2*C*(4+16*Cw)*σ^(-(η/6-19*beta η))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop he).const_mul (2*C*(4+16*Cw))
  filter_upwards [eventually_ge_atTop (1:ℝ),
    ht.eventually_lt_const (by norm_num : (0:ℝ)<1)] with σ hσ hsmall
  intro q D P H w k Λ hq hD hP hH hw hP' hH' hw' hk hΛ
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hkp : 0<k := by have := mul_pos hq (Real.rpow_pos_of_pos hs (1+η));linarith
  have hmono:=stage_cost_monomial hσ hD hP hH hw hCw (beta_pos hη).le hη.le hP' hH' hw'
  have h1 : Λ≤C*q*((4+16*Cw)*D*σ^(1+η/2+19*beta η)) :=
    hΛ.trans (mul_le_mul_of_nonneg_left hmono (by positivity))
  have hpow : σ^(1+η/2+19*beta η)=σ^(-(η/6-19*beta η))*σ^(-η/3)*σ^(1+η) := by
    rw [←Real.rpow_add hs,←Real.rpow_add hs]
    congr 1
    ring
  have hsmall' : 2*C*(4+16*Cw)*σ^(-(η/6-19*beta η))≤1 := hsmall.le
  have h2 : C*q*((4+16*Cw)*D*σ^(1+η/2+19*beta η))≤D*σ^(-η/3)*k := by
    rw [hpow]
    calc
      _ = (2*C*(4+16*Cw)*σ^(-(η/6-19*beta η)))*(D*σ^(-η/3))*(q*σ^(1+η)/2) := by ring
      _ ≤ 1*(D*σ^(-η/3))*(2*k/2) := by gcongr
      _ = _ := by ring
  exact (div_le_iff₀ hkp).mpr (h1.trans h2)

end
end SharpRamseyFive.ParameterHierarchy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_WindowBudgetNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Real
noncomputable section

lemma windowCodeBudget_coarse {σ q P b Cℓ : ℝ} {w H l : ℕ}
    (hσ : 1≤σ) (hq : σ≤q) (hP : 1≤P) (hH : 1≤H)
    (hb : b≤P) (hmeta : 2*Real.log (320/((9:ℝ)/100000)+320)≤P)
    (hlog4 : Real.log 4≤σ) (hC : 0≤Cℓ) (hl : Real.log (l+1)≤Cℓ*σ) :
    windowCodeBudget σ q P b w H+(w+1)*Real.log (l+1)≤
      (5+7*nodeChargeConstant+Cℓ)*q*(P*H*(σ+w*P)) := by
  have hs : 0≤σ := by linarith
  have hp : 0≤P := by linarith
  have hq0 : 0≤q := by linarith
  have hh : (1:ℝ)≤H := by exact_mod_cast hH
  have hh0 : (0:ℝ)≤H := by positivity
  have hn := nodeChargeConstant_nonneg
  have hl2 : Real.log 2≤1 := by convert Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2) using 1; norm_num
  have hx : (w:ℝ)+1≤σ+w*P := by nlinarith [mul_le_mul_of_nonneg_left hP (show (0:ℝ)≤w by positivity)]
  have hmul : 1≤q*P*H := by
    have hq1 : 1≤q := hσ.trans hq
    calc
      1 = (1:ℝ)*1*1 := by norm_num
      _ ≤ q*P*H := by gcongr
  have hmulσ : σ≤q*P*H := by
    calc
      σ≤q := hq
      _ =q*1*1 := by ring
      _ ≤q*P*H := by gcongr
  let A:=q*P*H*(σ+w*P)
  have ha0 : 0≤A := by dsimp [A];positivity
  have ha : σ+w*P≤A := by
    dsimp [A]
    exact le_mul_of_one_le_left (by positivity) hmul
  have hwA : (w:ℝ)≤A := by linarith
  have hhA : Real.log (w+1)≤A := by
    have hh' := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ)<(w:ℝ)+1)
    exact (show Real.log (w+1)≤(w:ℝ) by linarith).trans hwA
  have hfirst : nodeChargeConstant*q*P*H*
      (3*σ+Real.log 4+(b+1+2*Real.log (320/((9:ℝ)/100000)+320))*w)≤4*nodeChargeConstant*A := by
    calc
      _ ≤ nodeChargeConstant*q*P*H*(4*σ+3*P*w) := by gcongr <;> nlinarith
      _ ≤ nodeChargeConstant*q*P*H*(4*(σ+w*P)) := by gcongr; nlinarith
      _ = _ := by dsimp [A];ring
  have hsecond : (Real.log 2+nodeChargeConstant*q*P*(b+1+P))*w≤
      (1+3*nodeChargeConstant)*A := by
    have hw : nodeChargeConstant*q*P*(3*P)*w≤3*nodeChargeConstant*A := by
      calc
        _ =3*nodeChargeConstant*(q*P*(w*P)) := by ring
        _ =3*nodeChargeConstant*(q*P*(1:ℝ)*(w*P)) := by ring
        _ ≤3*nodeChargeConstant*(q*P*H*(σ+w*P)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_left hh (by positivity))
            (by linarith) (by positivity) (by positivity)
    calc
      _ ≤ (1+nodeChargeConstant*q*P*(3*P))*w := by gcongr; linarith
      _ = w+nodeChargeConstant*q*P*(3*P)*w := by ring
      _ ≤ A+3*nodeChargeConstant*A := add_le_add hwA hw
      _ = _ := by ring
  have hstatus : (2*(w:ℝ)+1)*Real.log 2≤3*A := by
    calc
      _ ≤2*(w:ℝ)+1 := mul_le_of_le_one_right (by positivity) hl2
      _ ≤3*((w:ℝ)+1) := by linarith
      _ ≤3*A := by linarith
  have hassign : ((w:ℝ)+1)*Real.log (l+1)≤Cℓ*A := by
    calc
      _ ≤((w:ℝ)+1)*(Cℓ*σ) := mul_le_mul_of_nonneg_left hl (by positivity)
      _ =Cℓ*(σ*((w:ℝ)+1)) := by ring
      _ ≤Cℓ*(q*P*H*(σ+w*P)) := by gcongr
  have ht:=add_le_add (add_le_add (add_le_add hhA (add_le_add hfirst hsecond)) hstatus) hassign
  exact ht.trans_eq (by dsimp [A];ring)
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ReciprocalCodeNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real Marking ProjectiveIncidence
open scoped Topology
noncomputable section
lemma log_length_three {σ q η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (hσ : 6≤σ) (hq : Real.exp σ=q) (l : ℕ) (hl : (l:ℝ)≤q*σ^(1+η)) :
    Real.log (l+1)≤3*σ := by
  have hp : 0<σ := by linarith
  have hσ1 : 1≤σ := by linarith
  have hpow : σ^(1+η)≤σ^2 := by
    rw [←Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hσ1 (by linarith)
  have hexp : σ^2≤Real.exp σ := by
    have hh:=Real.pow_div_factorial_le_exp σ hp.le 3
    norm_num only [Nat.factorial] at hh
    have hs3 : σ^2≤σ^3/6 := by nlinarith [mul_nonneg (sq_nonneg σ) (show 0≤σ-6 by linarith)]
    exact hs3.trans hh
  have hlen : (l:ℝ)≤q*q := hl.trans (mul_le_mul_of_nonneg_left (hpow.trans (hexp.trans_eq hq)) (by rw [←hq];positivity))
  have hq1 : 1≤q := by rw [←hq];exact Real.one_le_exp hp.le
  have hsum : (l:ℝ)+1≤2*(q*q) := by nlinarith
  have hh:=Real.log_le_log (by positivity : (0:ℝ)<(l:ℝ)+1) hsum
  have hqp : 0<q := by rw [←hq];positivity
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (mul_pos hqp hqp).ne',Real.log_mul hqp.ne' hqp.ne',←hq,Real.log_exp] at hh
  have hlog2 : Real.log 2≤1 := by
    have hh:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  linarith

lemma prescribed_P_bounds {η σ D R : ℝ} (hη : 0<η) (hσ : 1≤σ) (hR : Range η σ D R) :
    D*σ^(9*beta η)≤P η σ D R ∧ P η σ D R≤4*D*σ^(9*beta η) := by
  have hp : 0<σ := zero_lt_one.trans_le hσ
  have hb:=beta_pos hη
  have hx : 1≤σ^beta η := Real.one_le_rpow hσ hb.le
  have hD : 0≤D := (Real.rpow_nonneg hp.le _).trans hR.dlo
  have hRh : R≤4*σ^beta η := hR.rhi.trans (by linarith)
  have heq : D*σ^(8*beta η)*σ^beta η=D*σ^(9*beta η) := by
    rw [mul_assoc,←Real.rpow_add hp];congr 2;ring
  constructor
  · rw [←heq]
    exact mul_le_mul_of_nonneg_left hR.rlo (by positivity)
  · calc
      _ ≤D*σ^(8*beta η)*(4*σ^beta η) := mul_le_mul_of_nonneg_left hRh (by positivity)
      _ =4*(D*σ^(8*beta η)*σ^beta η) := by ring
      _ =_ := by rw [heq];ring

theorem eventually_reciprocal_code_budget_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (q D R k : ℝ) (w H l : ℕ),
      Real.exp σ=q→Range η σ D R→1≤H→(H:ℝ)≤σ^beta η→
      (w:ℝ)*D≤σ^(1+η/2)→q*σ^(1+η)≤2*k→(l:ℝ)≤q*σ^(1+η)→
      windowCodeBudget σ q (P η σ D R) (D*σ^(6*beta η)+2*(D*σ^(2*beta η))+Real.log 4) w H+
          (w+1)*Real.log (l+1)≤k*D*σ^(-η/3) := by
  have hb:=beta_pos hη
  have h3 : 0<3*beta η := by positivity
  have hm : 0≤8+7*nodeChargeConstant := by have:=nodeChargeConstant_nonneg;positivity
  filter_upwards [eventually_ge_atTop (6:ℝ),
    (tendsto_rpow_atTop hb).eventually (eventually_ge_atTop (max 1 (2*Real.log (320/(9/100000)+320)))),
    (tendsto_rpow_atTop h3).eventually (eventually_ge_atTop (3+Real.log 4)),
    eventually_stage_entropy_bound hη (8+7*nodeChargeConstant) 1 hm (by norm_num)] with σ hσ hg hg3 hbudget
  intro q D R k w H l hq hr hH hHhi hw hk hl
  have hσ1 : 1≤σ := by linarith
  have hp : 0<σ := by linarith
  have hqp : 0<q := by rw [←hq];positivity
  have hD : 0<D := (Real.rpow_pos_of_pos hp _).trans_le hr.dlo
  obtain ⟨hPlo,hPhi⟩:=prescribed_P_bounds hη hσ1 hr
  have hD1 : 1≤D := (Real.one_le_rpow hσ1 hb.le).trans hr.dlo
  have hP1 : 1≤P η σ D R := by
    have hh:=Real.one_le_rpow hσ1 (show 0≤9*beta η by positivity)
    nlinarith
  have hPmeta : 2*Real.log (320/(9/100000)+320)≤P η σ D R := by
    have hh : σ^beta η≤σ^(9*beta η) := Real.rpow_le_rpow_of_exponent_le hσ1 (by linarith)
    have hh' : σ^(9*beta η)≤D*σ^(9*beta η) := le_mul_of_one_le_left (by positivity) hD1
    exact (le_max_right _ _).trans (hg.trans (hh.trans (hh'.trans hPlo)))
  have hbP : D*σ^(6*beta η)+2*(D*σ^(2*beta η))+Real.log 4≤P η σ D R := by
    have h26 : σ^(2*beta η)≤σ^(6*beta η) := Real.rpow_le_rpow_of_exponent_le hσ1 (by linarith)
    have hk1 : 1≤D*σ^(6*beta η) := by
      have hh:=Real.one_le_rpow hσ1 (show 0≤6*beta η by positivity)
      nlinarith
    have hld : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
    calc
      _ ≤(3+Real.log 4)*(D*σ^(6*beta η)) := by nlinarith [mul_le_mul_of_nonneg_left h26 hD.le]
      _ ≤σ^(3*beta η)*(D*σ^(6*beta η)) := mul_le_mul_of_nonneg_right hg3 (by positivity)
      _ =D*σ^(9*beta η) := by
        rw [mul_left_comm,←Real.rpow_add hp];congr 2;ring
      _ ≤_ := hPlo
  have hlog:=log_length_three hη hη' hσ hq l hl
  have hlog4 : Real.log 4≤σ := by
    have hh:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
    linarith
  have hσq : σ≤q := by
    rw [←hq]
    linarith [Real.add_one_le_exp σ]
  have hcoarse:=windowCodeBudget_coarse (w:=w) hσ1 hσq hP1 hH hbP hPmeta hlog4 (by norm_num : (0:ℝ)≤3) hlog
  have hh:=hbudget q D (P η σ D R) H w k _ hqp hD.le (by linarith) (by positivity) (by positivity)
    hPhi hHhi (by simpa only [mul_comm,one_mul] using hw) hk (by simpa only [show (5:ℝ)+7*nodeChargeConstant+3=8+7*nodeChargeConstant by ring] using hcoarse)
  have hkp : 0<k := by have := mul_pos hqp (Real.rpow_pos_of_pos hp (1+η));linarith
  exact (div_le_iff₀ hkp).mp hh |>.trans_eq (by ring)
end
end SharpRamseyFive.ParameterHierarchy

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ParameterHierarchy.eventually_reciprocal_code_budget_oai := @OAI.SharpRamseyFive.ParameterHierarchy.eventually_reciprocal_code_budget_oai
