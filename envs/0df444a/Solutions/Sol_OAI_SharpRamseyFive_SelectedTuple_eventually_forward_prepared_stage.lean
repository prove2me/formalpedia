-- Prove2me | solution 1 for OAI.SharpRamseyFive.SelectedTuple.eventually_forward_prepared_stage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:26:11.323372+00:00
-- url     : https://prove2.me/submissions/5ec577a8-d03b-4f36-834d-da6ad80ba85b

import Mathlib
import Definitions.Def_OAIQ060R004
import Theorems.Thm_OAI_SharpRamseyFive_ParameterHierarchy_eventually_reciprocal_code_budget
import Theorems.Thm_OAI_SharpRamseyFive_ParameterHierarchy_eventually_reciprocal_packing
import Theorems.Thm_OAI_SharpRamseyFive_SelectedTuple_eventually_reciprocal_coded_stage

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
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_HighNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

open Filter Real ParameterHierarchy FiniteEntropy
open scoped Topology
noncomputable section

lemma eventually_stage_scale {η : ℝ} (_ : 0<η) (a δ : ℝ)
    (ha : a*beta η<η/2) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀D : ℝ,D≤σ^(1-η/2)→D*σ^(a*beta η)≤δ*σ := by
  have he : 0<η/2-a*beta η := sub_pos.mpr ha
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_neg_atTop he).eventually_lt_const hδ] with σ hσ ht
  intro D hD
  have hs : 0<σ := zero_lt_one.trans_le hσ
  calc
    _ ≤ σ^(1-η/2)*σ^(a*beta η) := mul_le_mul_of_nonneg_right hD (by positivity)
    _ = σ^(-(η/2-a*beta η))*σ := by
      rw [←Real.rpow_add hs,show 1-η/2+a*beta η= -(η/2-a*beta η)+1 by ring,
        Real.rpow_add hs,Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right ht.le hs.le

end

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalDropNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real Marking
open scoped Topology
noncomputable section

lemma reciprocal_drop_ratio {σ D η w G C : ℝ} (hη : 0<η) (hσ : 1≤σ)
    (hD : σ^beta η≤D) (hw : 0≤w) (hC : 0≤C)
    (hG : G≤C*w*D*σ^(3*beta η)) :
    (G+2*w*(2*(D*σ^(2*beta η))+Real.log 64))/(D*σ^(6*beta η))≤
      w*((C+4+2*Real.log 64)*σ^(-3*beta η)) := by
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hb:=beta_pos hη
  have hD1 : 1≤D := (Real.one_le_rpow hσ hb.le).trans hD
  have hDp : 0<D := by linarith
  have hp3 : 1≤σ^(3*beta η) := Real.one_le_rpow hσ (by positivity)
  have hp23 : σ^(2*beta η)≤σ^(3*beta η) := Real.rpow_le_rpow_of_exponent_le hσ (by linarith)
  have hl : 0≤Real.log 64 := Real.log_nonneg (by norm_num)
  have hbig : 1≤D*σ^(3*beta η) := (by nlinarith : 1≤D*σ^(3*beta η))
  have hlog : Real.log 64≤D*σ^(3*beta η)*Real.log 64 := by nlinarith
  calc
    _ ≤ ((C+4+2*Real.log 64)*w*D*σ^(3*beta η))/(D*σ^(6*beta η)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hp23 (show 0≤4*w*D by positivity),
        mul_le_mul_of_nonneg_left hlog (show 0≤2*w by positivity)]
    _ =w*((C+4+2*Real.log 64)*(σ^(3*beta η)/σ^(6*beta η))) := by field_simp
    _ =_ := by rw [←Real.rpow_sub hs];congr 3;ring

lemma eventually_reciprocal_drop_fraction {η : ℝ} (hη : 0<η) (C δ : ℝ)
    (hC : 0≤C) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀ D w G : ℝ,σ^beta η≤D→0≤w→
      G≤C*w*D*σ^(3*beta η)→
      (G+2*w*(2*(D*σ^(2*beta η))+Real.log 64))/(D*σ^(6*beta η))≤w*δ := by
  have hb : 0<3*beta η := by have:=beta_pos hη;positivity
  have ht : Tendsto (fun σ : ℝ=>(C+4+2*Real.log 64)*σ^(-3*beta η)) atTop (𝓝 0) := by
    simpa only [neg_mul,mul_zero] using (tendsto_rpow_neg_atTop hb).const_mul (C+4+2*Real.log 64)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually_lt_const hδ] with σ hσ ht
  intro D w G hD hw hG
  exact (reciprocal_drop_ratio hη hσ hD hw hC hG).trans (mul_le_mul_of_nonneg_left ht.le hw)

lemma open_gap_scale {σ D η c w : ℝ} (hη : 0<η) (hσ : 1≤σ) (hc : 0 < c)
    (hw : 0≤w) (hD : 0≤D) (hlo : c*σ^(1+η/2)≤w*D) :
    3*σ≤(3/c)*w*D*σ^(3*beta η) := by
  have hb:=beta_pos hη
  have hp : σ≤σ^(1+η/2) := by
    nth_rw 1 [←Real.rpow_one σ]
    exact Real.rpow_le_rpow_of_exponent_le hσ (by linarith)
  have hh := mul_le_mul_of_nonneg_left hlo (by positivity : 0≤3/c)
  have hcancel : (3/c)*(c*σ^(1+η/2))=3*σ^(1+η/2) := by field_simp
  rw [hcancel] at hh
  calc
    3*σ≤3*σ^(1+η/2) := by linarith
    _ ≤(3/c)*(w*D) := hh
    _ ≤(3/c)*(w*D)*σ^(3*beta η) := le_mul_of_one_le_right (by positivity)
        (Real.one_le_rpow hσ (by positivity))
    _ =_ := by ring

end
end SharpRamseyFive.ParameterHierarchy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalRoundNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real
open scoped Topology
noncomputable section

lemma reciprocal_round_ratio {σ q D η c C Cₘ w n B T rem M : ℝ}
    (_hη : 0<η) (hσ : 1≤σ) (hq : 0<q) (hc : 0 < c) (hC : 0≤C) (hCm : 0≤Cₘ)
    (hD : σ^beta η≤D) (hw : 0≤w) (hn : 0<n) (_hB : 0≤B)
    (hBhi : B≤C*(4*w*n)*D*σ^(-beta η))
    (hT : q*D*σ^(3000*beta η)/2≤T)
    (hr : n/2 ≤ rem) (_hM : 0≤M) (hMhi : M≤Cₘ*σ)
    (closed : Bool) (hlen : closed=true→c*q*σ^(1+η)≤n) :
    B/(D*σ^beta η)+(2*B/T+(if closed then 16*w*n*M/rem else 0))/(σ^(-2000*beta η)/q)≤
      (w*n)*(4*C*σ^(-2*beta η)+16*C*σ^(-1001*beta η)+
        (32*Cₘ/c)*σ^(2000*beta η-η)) := by
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hDp : 0<D := (Real.rpow_pos_of_pos hs _).trans_le hD
  have hTp : 0<T := (by positivity : 0<q*D*σ^(3000*beta η)/2).trans_le hT
  have hrp : 0 < rem := (by positivity : 0<n/2).trans_le hr
  have hp (a : ℝ) : 0<σ^a := Real.rpow_pos_of_pos hs a
  have hfirst : B/(D*σ^beta η)≤w*n*(4*C*σ^(-2*beta η)) := by
    calc
      _ ≤(C*(4*w*n)*D*σ^(-beta η))/(D*σ^beta η) := div_le_div_of_nonneg_right hBhi (by positivity)
      _ =w*n*(4*C*(σ^(-beta η)/σ^beta η)) := by field_simp
      _ =_ := by rw [←Real.rpow_sub hs];congr 3;ring
  have hsecond : (2*B/T)/(σ^(-2000*beta η)/q)≤w*n*(16*C*σ^(-1001*beta η)) := by
    calc
      _ ≤(2*(C*(4*w*n)*D*σ^(-beta η))/(q*D*σ^(3000*beta η)/2))/(σ^(-2000*beta η)/q) := by gcongr
      _ =w*n*(16*C*(σ^(-beta η)/(σ^(3000*beta η)*σ^(-2000*beta η)))) := by field_simp; ring
      _ =_ := by rw [←Real.rpow_add hs,←Real.rpow_sub hs];congr 3;ring
  have hthird : (if closed then 16*w*n*M/rem else 0)/(σ^(-2000*beta η)/q)≤
      w*n*((32*Cₘ/c)*σ^(2000*beta η-η)) := by
    cases closed with
    | false => simp only [Bool.false_eq_true,ite_false,zero_div];positivity
    | true =>
      simp only [ite_true]
      have hlen':=hlen rfl
      have hh : (16*w*n*M/rem)/(σ^(-2000*beta η)/q)≤32*w*Cₘ*q*σ/σ^(-2000*beta η) := by
        calc
          _ ≤(16*w*n*(Cₘ*σ)/(n/2))/(σ^(-2000*beta η)/q) := by gcongr
          _ =_ := by field_simp; ring
      apply hh.trans
      have he : 32*w*Cₘ*q*σ/σ^(-2000*beta η)=
          (32*Cₘ/c)*w*(c*q*σ^(1+η))*σ^(2000*beta η-η) := by
        rw [mul_assoc ((32*Cₘ/c)*w),mul_assoc (c*q),←Real.rpow_add hs]
        have he : 1+η+(2000*beta η-η)=1-(-2000*beta η) := by ring
        rw [he,Real.rpow_sub hs,Real.rpow_one]
        field_simp
      rw [he]
      calc
        _ ≤(32*Cₘ/c)*w*n*σ^(2000*beta η-η) := by gcongr
        _ =_ := by ring
  rw [add_div]
  nlinarith [hfirst,hsecond,hthird]

lemma eventually_reciprocal_round_fraction {η : ℝ} (hη : 0<η)
    (c C Cₘ δ : ℝ) (hc : 0 < c) (hC : 0≤C) (hCm : 0≤Cₘ) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀ q D w n B T rem M : ℝ,
      0<q→σ^beta η≤D→0≤w→0<n→0≤B→B≤C*(4*w*n)*D*σ^(-beta η)→
      q*D*σ^(3000*beta η)/2≤T→n/2 ≤ rem→0≤M→M≤Cₘ*σ→
      ∀closed : Bool,(closed=true→c*q*σ^(1+η)≤n)→
      B/(D*σ^beta η)+(2*B/T+(if closed then 16*w*n*M/rem else 0))/(σ^(-2000*beta η)/q)≤w*n*δ := by
  have h2 : 0<2*beta η := by have:=beta_pos hη;positivity
  have h1001 : 0<1001*beta η := by have:=beta_pos hη;positivity
  have h2000 : 0<η-2000*beta η := by unfold beta;linarith
  have ht : Tendsto (fun σ : ℝ=>4*C*σ^(-2*beta η)+16*C*σ^(-1001*beta η)+
      (32*Cₘ/c)*σ^(2000*beta η-η)) atTop (𝓝 0) := by
    have he : 2000*beta η-η= -(η-2000*beta η) := by ring
    simpa only [neg_mul,he,mul_zero,add_zero] using
      (((tendsto_rpow_neg_atTop h2).const_mul (4*C)).add
        ((tendsto_rpow_neg_atTop h1001).const_mul (16*C))).add
          ((tendsto_rpow_neg_atTop h2000).const_mul (32*Cₘ/c))
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually_lt_const hδ] with σ hσ ht
  intro q D w n B T rem M hq hD hw hn hB hBhi hT hr hM hMhi closed hlen
  exact (reciprocal_round_ratio hη hσ hq hc hC hCm hD hw hn hB hBhi hT hr hM hMhi closed hlen).trans
    (mul_le_mul_of_nonneg_left ht.le (mul_nonneg hw hn.le))
end
end SharpRamseyFive.ParameterHierarchy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ReciprocalLossBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real Marking
open scoped Topology
noncomputable section

lemma reciprocal_total_fraction {w n l bad drop : ℝ}
    (hw : 0≤w) (hn : 0≤n) (hl : l≤w*n)
    (hbad : bad≤w*n/10000) (hdrop : drop≤w/10000) :
    5*bad+(2*n)*drop+(w*(2*n))*(1/10000)≤(w*(2*n)-l)/10 := by
  have := mul_le_mul_of_nonneg_left hdrop (show 0≤2*n by positivity)
  nlinarith [mul_nonneg hw hn]

theorem eventually_reciprocal_loss_budget {η : ℝ} (hη : 0<η)
    (c C Cm : ℝ) (hc : 0 < c) (hC : 0≤C) (hCm : 0≤Cm) :
    ∀ᶠ σ : ℝ in atTop,∀ (q D m w n B T rem M G l : ℝ),
      0<q→σ^beta η≤D→1≤w→0<n→m≤8*w*n→0≤B→B≤C*m*D*σ^(-beta η)→
      q*D*σ^(3000*beta η)/2≤T→n/2 ≤ rem→0≤M→M≤Cm*σ→l≤w*n→
      ∀closed : Bool,(closed=true→(c/8)*q*σ^(1+η)≤n)→
        (closed=false→(c/8)*σ^(1+η/2)≤w*D)→
        (closed=true→G≤2*D*σ^(3*beta η))→(closed=false→G≤3*σ)→
      5*(B/(D*σ^beta η)+(2*B/T+(if closed then 16*w*n*M/rem else 0))/(σ^(-2000*beta η)/q))+
        (2*n)*((G+2*w*(2*(D*σ^(2*beta η))+Real.log 64))/(D*σ^(6*beta η)))+
        (w*(2*n))*(1/10000)≤(w*(2*n)-l)/10 := by
  have hcd : 0≤2+24/c := by positivity
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_reciprocal_round_fraction hη (c/8) (2*C) Cm (1/10000) (by positivity) (by positivity) hCm (by norm_num),
    eventually_reciprocal_drop_fraction hη (2+24/c) (1/10000) hcd (by norm_num)] with σ hσ hround hdrop
  intro q D m w n B T rem M G l hq hD hw hn hm hB hBhi hT hr hM hMhi hl closed hclosed hopen hGc hGo
  have hw0 : 0≤w := by linarith
  have hp : 0<σ := zero_lt_one.trans_le hσ
  have hDp : 0<D := (Real.rpow_pos_of_pos hp _).trans_le hD
  have hB' : B≤(2*C)*(4*w*n)*D*σ^(-beta η) := by
    apply hBhi.trans
    calc
      _ ≤C*(8*w*n)*D*σ^(-beta η) := by gcongr
      _ =_ := by ring
  have hG : G≤(2+24/c)*w*D*σ^(3*beta η) := by
    cases closed with
    | true =>
      calc
        G≤2*D*σ^(3*beta η) := hGc rfl
        _ ≤2*w*D*σ^(3*beta η) := by gcongr;linarith
        _ ≤_ := by
          have hh : (2:ℝ)≤2+24/c := le_add_of_nonneg_right (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hh hw0) hDp.le) (by positivity)
    | false =>
      calc
        G≤3*σ := hGo rfl
        _ ≤(3/(c/8))*w*D*σ^(3*beta η) :=
          open_gap_scale hη hσ (by positivity) hw0 hDp.le (hopen rfl)
        _ = (24/c)*w*D*σ^(3*beta η) := by ring
        _ ≤_ := by gcongr; linarith
  have hh:=hround q D w n B T rem M hq hD hw0 hn hB hB' hT hr hM hMhi closed hclosed
  have hh':=hdrop D w G hD hw0 hG
  apply reciprocal_total_fraction hw0 hn.le hl
  · simpa only [mul_one_div] using hh
  · simpa only [mul_one_div] using hh'
end
end SharpRamseyFive.ParameterHierarchy

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
noncomputable section
variable {Ω β κ : Type} [Fintype Ω] [Fintype β] [Fintype κ]
  {n : ℕ} {p : Law Ω} {x : Ω→Fin n→β} {Λ J Λ' J' : ℝ}
lemma card_le_of_log_le {a b : ℝ} (ha : 0≤a) (hb : 0<b)
    (h : Real.log a≤Real.log b) : a≤b := by
  rcases eq_or_lt_of_le ha with he|he
  · linarith
  · exact (Real.log_le_log_iff he hb).mp h
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_BandEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Filter Real
noncomputable section
lemma band_endpoints {σ width u : ℝ} {b : Fin 7}
    (_hσ : 0≤σ) (_hw : 0≤width) (hu : σ≤u ∧ u≤4*σ)
    (hb : BandCondition σ width u b) :
    bandLo σ width b≤u ∧ u≤bandHi σ width b := by
  unfold bandLo bandHi BandCondition at *
  split_ifs at * with he
  · have hh:=abs_le.mp hb
    constructor <;> linarith
  · exact hu
lemma band_lo_le_hi {σ width : ℝ} {b : Fin 7} (hσ : 0≤σ) (hw : 0≤width) :
    bandLo σ width b≤bandHi σ width b := by
  unfold bandLo bandHi
  split_ifs <;> linarith
lemma band_gap_closed {σ width : ℝ} {b : Fin 7} (hb : b.val%2=0) :
    bandHi σ width b-bandLo σ width b=2*width := by simp [bandHi,bandLo,hb];ring
lemma band_gap_open {σ width : ℝ} {b : Fin 7} (hb : b.val%2≠0) :
    bandHi σ width b-bandLo σ width b=3*σ := by simp [bandHi,bandLo,hb];ring
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Filter Asymptotics Real
open scoped Topology
noncomputable section

lemma reciprocal_bad_uniform {σ D b C : ℝ} (hσ : 1≤σ) (_hb : 0<b)
    (hD : σ^b≤D) (hC : 0≤C) :
    reciprocalBadMass (D*σ^(2*b)) (D*σ^b) C≤
      Real.exp (-σ^(3*b))+50*(σ^(-b)+C/σ^(3*b)) := by
  have hσp : 0<σ := zero_lt_one.trans_le hσ
  have hDp : 0<D := (Real.rpow_pos_of_pos hσp b).trans_le hD
  have hs : σ^(3*b)≤D*σ^(2*b) := by
    calc
      _ = σ^b*σ^(2*b) := by rw [←Real.rpow_add hσp];congr 1;ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD (Real.rpow_nonneg hσp.le _)
  have he : (D*σ^b)/(D*σ^(2*b))=σ^(-b) := by
    rw [mul_div_mul_left _ _ hDp.ne']
    rw [←Real.rpow_sub hσp]
    congr 1
    ring
  have hc := div_le_div_of_nonneg_left hC (Real.rpow_pos_of_pos hσp _) hs
  unfold reciprocalBadMass
  rw [mul_div_assoc,add_div,he]
  exact add_le_add (Real.exp_le_exp.mpr (neg_le_neg hs))
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hc) (by norm_num))

lemma reciprocal_core_uniform {σ D b C : ℝ} (hσ : 1≤σ) (hb : 0<b)
    (hD : σ^b≤D) (hC : 0≤C) :
    2*(D*σ^b+Real.log 32+Real.log 33+2*(Real.log (5*σ+1)+1))/(D*σ^(2*b))+
      2*Real.exp 1*reciprocalBadMass (D*σ^(2*b)) (D*σ^b) C≤
    2*(σ^(-b)+(Real.log 32+Real.log 33+2*(Real.log 6+1))/σ^(3*b)+
      2*(Real.log σ/σ^(3*b)))+
      2*Real.exp 1*(Real.exp (-σ^(3*b))+50*(σ^(-b)+C/σ^(3*b))) := by
  have hσp : 0<σ := zero_lt_one.trans_le hσ
  have hDp : 0<D := (Real.rpow_pos_of_pos hσp b).trans_le hD
  have hs : σ^(3*b)≤D*σ^(2*b) := by
    calc
      _ = σ^b*σ^(2*b) := by rw [←Real.rpow_add hσp];congr 1;ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD (Real.rpow_nonneg hσp.le _)
  have he : (D*σ^b)/(D*σ^(2*b))=σ^(-b) := by
    rw [mul_div_mul_left _ _ hDp.ne',←Real.rpow_sub hσp]
    congr 1
    ring
  have hl : Real.log (5*σ+1)≤Real.log 6+Real.log σ := by
    rw [←Real.log_mul (by norm_num : (6:ℝ)≠0) hσp.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have hn : 0≤Real.log 32+Real.log 33+2*(Real.log 6+Real.log σ+1) := by
    have := Real.log_nonneg hσ
    positivity
  have hd := div_le_div_of_nonneg_left hn (Real.rpow_pos_of_pos hσp _) hs
  have hl' : (Real.log 32+Real.log 33+2*(Real.log (5*σ+1)+1))/(D*σ^(2*b))≤
      (Real.log 32+Real.log 33+2*(Real.log 6+1))/σ^(3*b)+2*(Real.log σ/σ^(3*b)) := by
    calc
      _ ≤ (Real.log 32+Real.log 33+2*(Real.log 6+Real.log σ+1))/(D*σ^(2*b)) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (Real.log 32+Real.log 33+2*(Real.log 6+Real.log σ+1))/σ^(3*b) := hd
      _ = _ := by ring
  have hf : 2*(D*σ^b+Real.log 32+Real.log 33+2*(Real.log (5*σ+1)+1))/(D*σ^(2*b))≤
      2*(σ^(-b)+(Real.log 32+Real.log 33+2*(Real.log 6+1))/σ^(3*b)+2*(Real.log σ/σ^(3*b))) := by
    calc
      _ = 2*((D*σ^b)/(D*σ^(2*b))+
        (Real.log 32+Real.log 33+2*(Real.log (5*σ+1)+1))/(D*σ^(2*b))) := by ring
      _ ≤ _ := by rw [he];linarith
  exact add_le_add hf (mul_le_mul_of_nonneg_left (reciprocal_bad_uniform hσ hb hD hC) (by positivity))

theorem eventually_reciprocal_endpoints {b : ℝ} (hb : 0<b) (C ε : ℝ)
    (hC : 0≤C) (hε : 0<ε) :
    ∀ᶠ σ : ℝ in atTop,∀ D : ℝ,σ^b≤D→
      reciprocalBadMass (D*σ^(2*b)) (D*σ^b) C≤ε ∧
      2*(D*σ^b+Real.log 32+Real.log 33+2*(Real.log (5*σ+1)+1))/(D*σ^(2*b))+
        2*Real.exp 1*reciprocalBadMass (D*σ^(2*b)) (D*σ^b) C≤1/2 := by
  have ht := tendsto_rpow_neg_atTop hb
  have h3 : 0<3*b := by positivity
  have hn := tendsto_rpow_neg_atTop h3
  have hc : Tendsto (fun σ : ℝ=>C/σ^(3*b)) atTop (𝓝 0) :=
    (tendsto_rpow_atTop h3).const_div_atTop C
  have he : Tendsto (fun σ : ℝ=>Real.exp (-σ^(3*b))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_rpow_atTop h3)
  have hbad : Tendsto (fun σ : ℝ=>Real.exp (-σ^(3*b))+50*(σ^(-b)+C/σ^(3*b))) atTop (𝓝 0) := by
    simpa using he.add ((ht.add hc).const_mul 50)
  have hc' : Tendsto (fun σ : ℝ=>(Real.log 32+Real.log 33+2*(Real.log 6+1))/σ^(3*b))
      atTop (𝓝 0) :=
    (tendsto_rpow_atTop h3).const_div_atTop (Real.log 32+Real.log 33+2*(Real.log 6+1))
  have hl := (isLittleO_log_rpow_atTop h3).tendsto_div_nhds_zero
  have hcore := (((ht.add hc').add (hl.const_mul 2)).const_mul 2).add (hbad.const_mul (2*Real.exp 1))
  simp only [add_zero,mul_zero] at hcore
  filter_upwards [eventually_ge_atTop (1:ℝ),hbad.eventually_lt_const hε,
    hcore.eventually_lt_const (by norm_num : (0:ℝ)<1/2)] with σ hσ he hc
  intro D hD
  exact ⟨(reciprocal_bad_uniform hσ hb hD hC).trans he.le,
    (reciprocal_core_uniform hσ hb hD hC).trans hc.le⟩

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalStageArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real Marking ProjectiveIncidence SelectedTuple
open scoped Topology NNReal
noncomputable section

lemma reciprocal_domain_slack_bound {σ η D : ℝ} (hη : 0<η) (hσ : 1≤σ)
    (hD : σ^beta η≤D) :
    codeDomainSlack (D*σ^(6*beta η)) (D*σ^(2*beta η))≤domainSlackConstant*D*σ^(6*beta η) := by
  have hb:=beta_pos hη
  have h1 : 1≤D := (Real.one_le_rpow hσ hb.le).trans hD
  have hpow : σ^(2*beta η)≤σ^(6*beta η) := Real.rpow_le_rpow_of_exponent_le hσ (by linarith)
  have hpow1 : 1≤σ^(6*beta η) := Real.one_le_rpow hσ (by positivity)
  have hk : 1≤D*σ^(6*beta η) := by nlinarith
  have hl : 0≤Real.log 4+1+Real.log (2*(320/(9/100000)+320)^2) := by
    have h1 : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
    have h2 : 0≤Real.log (2*(320/(9/100000)+320)^2) := Real.log_nonneg (by norm_num)
    linarith
  have hh:=mul_le_mul_of_nonneg_left hpow (show 0≤2*D by linarith)
  have hh':=mul_le_mul_of_nonneg_left hk hl
  dsimp only [codeDomainSlack,domainSlackConstant]
  nlinarith

lemma eventually_reciprocal_local_numbers {η : ℝ} (hη : 0<η) :
    ∀ᶠ σ : ℝ in atTop,∀D : ℝ,σ^beta η≤D→D≤σ^(1-η/2)→
      2≤D*σ^(2*beta η) ∧
      Real.log 32+D*σ^(3*beta η)+3*(D*σ^(2*beta η))<σ ∧
      Real.log 32+3*(D*σ^(2*beta η))<D*σ^(3*beta η) ∧
      0≤D*σ^(6*beta η)+2*(D*σ^(2*beta η))+Real.log 4 ∧
      D*σ^(6*beta η)+2*(D*σ^(2*beta η))+Real.log 4≤(3+Real.log 4)*D*σ^(6*beta η) ∧
      ((4*Real.exp 1)^2*80004)*(σ^(-2000*beta η)/Real.exp σ)≤1/(4*Real.exp σ) := by
  have hb:=beta_pos hη
  have he : 0<2000*beta η := by positivity
  have ht : Tendsto (fun σ : ℝ=>4*((4*Real.exp 1)^2*80004)*σ^(-2000*beta η)) atTop (𝓝 0) := by
    simpa only [neg_mul,mul_zero] using (tendsto_rpow_neg_atTop he).const_mul (4*((4*Real.exp 1)^2*80004))
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop (4*Real.log 32+1),
    (tendsto_rpow_atTop hb).eventually (eventually_ge_atTop (4+Real.log 32)),
    eventually_stage_scale hη 3 (1/16) (by unfold beta;linarith) (by norm_num),
    ht.eventually_lt_const (by norm_num : (0:ℝ)<1)] with σ hσ hs hg hscale hε
  intro D hD hDhi
  have hp : 0<σ := zero_lt_one.trans_le hσ
  have hl : 0≤Real.log 32 := Real.log_nonneg (by norm_num)
  have hl4 : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have h1 : 1≤D := (Real.one_le_rpow hσ hb.le).trans hD
  have hs1 : 1≤D*σ^(2*beta η) := by
    have := Real.one_le_rpow hσ (show 0≤2*beta η by positivity)
    nlinarith
  have h2 : 2≤D*σ^(2*beta η) := by
    have hh : σ^beta η≤σ^(2*beta η) := Real.rpow_le_rpow_of_exponent_le hσ (by linarith)
    nlinarith
  have h23 : D*σ^(2*beta η)≤D*σ^(3*beta η) := by
    apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hσ (by linarith)) (by linarith)
  have h6 : D*σ^(2*beta η)≤D*σ^(6*beta η) := by
    apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hσ (by linarith)) (by linarith)
  have hwide : Real.log 32+3*(D*σ^(2*beta η))<D*σ^(3*beta η) := by
    have heq : D*σ^(3*beta η)=(D*σ^(2*beta η))*σ^beta η := by
      rw [mul_assoc,←Real.rpow_add hp];congr 2;ring
    rw [heq]
    nlinarith
  refine ⟨h2,by have := hscale D hDhi;linarith,hwide,by positivity,?_,?_⟩
  · nlinarith
  · apply (le_div_iff₀ (by positivity : 0<4*Real.exp σ)).mpr
    have hh : ((4*Real.exp 1)^2*80004)*(σ^(-2000*beta η)/Real.exp σ)*(4*Real.exp σ)=
        4*((4*Real.exp 1)^2*80004)*σ^(-2000*beta η) := by field_simp
    rw [hh]
    exact hε.le

lemma eventually_public_integers {b : ℝ} (hb : 0<b) :
    ∀ᶠ σ : ℝ in atTop,∀w : ℕ,(w:ℝ)≤σ^2→
      let H:=⌈σ^(b/2)⌉₊
      let R:=⌈σ^b⌉₊
      1≤H ∧ w<2^H ∧ (H:ℝ)≤σ^b ∧ σ^b≤R ∧ (R:ℝ)≤2*σ^b+2 := by
  have hb2 : 0<b/2 := by linarith
  have ht := (isLittleO_log_rpow_atTop hb2).tendsto_div_nhds_zero
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop hb2).eventually (eventually_ge_atTop (2:ℝ)),
    ht.eventually_lt_const (show (0:ℝ)<Real.log 2/3 by positivity)] with σ hσ hg hlog
  intro w hw
  dsimp only
  have hp : 0<σ := by linarith
  have hs : 0<σ^(b/2) := Real.rpow_pos_of_pos hp _
  have hceil:=Nat.le_ceil (σ^(b/2))
  have hceilhi:=Nat.ceil_lt_add_one hs.le
  have hpow : σ^(b/2)*σ^(b/2)=σ^b := by rw [←Real.rpow_add hp];congr 1;ring
  have hdepth : (3:ℝ)*Real.log σ≤(⌈σ^(b/2)⌉₊:ℝ)*Real.log 2 := by
    have hl : Real.log σ<(Real.log 2/3)*σ^(b/2) := (div_lt_iff₀ hs).mp hlog
    have hh:=mul_le_mul_of_nonneg_right hceil (show 0≤Real.log 2 by positivity)
    linarith
  have hpow3 : σ^3≤(2:ℝ)^⌈σ^(b/2)⌉₊ := by
    calc
      σ^3 = Real.exp (3*Real.log σ) := by simpa only [Nat.cast_ofNat,Real.exp_log hp] using (Real.exp_nat_mul (Real.log σ) 3).symm
      _ ≤ Real.exp ((⌈σ^(b/2)⌉₊:ℝ)*Real.log 2) := Real.exp_le_exp.mpr hdepth
      _ = _ := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  have hwlt : (w:ℝ)<(2:ℝ)^⌈σ^(b/2)⌉₊ := by
    apply (hw.trans_lt _).trans_le hpow3
    have := mul_pos (sq_pos_of_pos hp) (show 0<σ-1 by linarith)
    nlinarith
  refine ⟨?_,by exact_mod_cast hwlt,?_,Nat.le_ceil _,?_⟩
  · have hh : (1:ℝ)≤⌈σ^(b/2)⌉₊ := by linarith
    exact_mod_cast hh
  · rw [←hpow]
    nlinarith
  · have hh:=Nat.ceil_lt_add_one (Real.rpow_nonneg hp.le b)
    have hh':=Real.rpow_nonneg hp.le b
    linarith
end
end SharpRamseyFive.ParameterHierarchy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_ForwardPreparedStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal
noncomputable section

theorem eventually_forward_prepared_stage_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (c C Cm : ℝ) (hc : 0 < c) (hC : 0≤C) (hCm : 0≤Cm) :
    ∀ᶠ σ : ℝ in atTop,∀ (q₀ : ℕ) (K V Ω κ α : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α],
    ∀ (N m l : ℕ) (admissible : (Fin N→α)→Prop)
      (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N m admissible)
      (ctx : Ω→κ) (D B M k₀ : ℝ)
      (PS : Prepared S ctx (Real.log (153*(Nat.card K:ℝ)^4)) B M) (b : Fin 7),
      finrank K V=5→3≤Nat.card K→Nat.card K=q₀→1≤σ→Real.exp σ=Nat.card K→
      σ^beta η≤D→D≤σ^(1-η/2)→c*(Nat.card K:ℝ)*σ^(1+η)≤ m→
      (m:ℝ)≤(Nat.card K:ℝ)*σ^(1+η)→(l:ℝ)≤ m/100→
      (Nat.card K:ℝ)*σ^(1+η)≤2*k₀→0≤B→B≤C*m*D*σ^(-beta η)→0≤M→M≤Cm*σ→
      (∀a,0 < map S.law ctx a→∀i,DomainClass (D*σ^(3*beta η)) (PS.domain a i) (.inl b))→
      Nonempty (CodedStream (K:=K) (V:=V) N l admissible ((10/9)*S.density)
        (k₀*D*σ^(-η/3)) (Real.log (153*(Nat.card K:ℝ)^4)+domainSlackConstant*D*σ^(6*beta η)) M) := by
  have hCb : 0≤3+Real.log 4 := by have:=Real.log_nonneg (show (1:ℝ)≤4 by norm_num);linarith
  filter_upwards [eventually_reciprocal_coded_stage hη hη' (3+Real.log 4) 153 (1/10000) hCb (by norm_num) (by norm_num),
    eventually_reciprocal_packing hη hη' c hc,eventually_reciprocal_local_numbers hη,
    eventually_public_integers (beta_pos hη),eventually_reciprocal_code_budget hη hη',
    eventually_reciprocal_loss_budget hη c C Cm hc hC hCm,
    eventually_reciprocal_endpoints (beta_pos hη) 153 (1/2) (by norm_num) (by norm_num)]
    with σ hstage hpack hlocal hpublic hcode hloss hend
  intro q₀ K V Ω κ α _ _ _ _ _ _ _ _ _ _ _ _ N m l adm S ctx D B M k₀ PS b
    hd hq3 hcard hσ hq hD hDhi hlen hm hl hk₀ hB hBhi hM hMhi hcl
  have hp : 0<σ := zero_lt_one.trans_le hσ
  have hqp : (0:ℝ)<Nat.card K := by rw [←hq];positivity
  have hqr : (2:ℝ)≤Nat.card K := by exact_mod_cast (show 2≤Nat.card K by omega)
  have hDp : 0<D := (Real.rpow_pos_of_pos hp _).trans_le hD
  have hσeq : Real.log (Nat.card K)=σ := by rw [←hq,Real.log_exp]
  have hJ : Real.log (153*(Nat.card K:ℝ)^4)=Real.log 153+4*σ := by
    rw [Real.log_mul (by norm_num) (pow_pos hqp _).ne',Real.log_pow,hσeq];norm_num
  have hlog153 : 0≤Real.log 153 := Real.log_nonneg (by norm_num)
  let closed : Bool:=decide (b.val%2=0)
  obtain ⟨w,n,T,rem,hw,hn,hpacking,hml,hwD,hw2,hclosed,hopen,hT,hr,hnr,hroom,hTlo,hrlo⟩:=
    hpack (Nat.card K) D m hqr hD hDhi hlen hm closed
  let : Nonempty (Fin n):=⟨⟨0,hn⟩⟩
  let R:=⌈σ^beta η⌉₊
  let H:=⌈σ^(beta η/2)⌉₊
  obtain ⟨hHpos,hwH,hHhi,hRlo,hRhi⟩:=hpublic w hw2
  have hRange : Range η σ D R := ⟨hD,hDhi,hRlo,hRhi⟩
  let L₀ : ℝ≥0:=⟨L η σ D,by unfold L;positivity⟩
  let e:=Fin.castLEOrderEmb hpacking
  let S':=S.reindex e
  let PS':=PS.reindex e
  let u : κ→Slots w n→ℝ:=fun c i=>if h : 0 < map S.law ctx c then
    (hcl c h (e (slotEmbedding i))).choose else 0
  have hu : ∀c,0 < map S'.law ctx c→∀i,
      σ≤u c i ∧ u c i≤4*σ ∧ ForwardCaps (PS'.domain c (slotEmbedding i)) (u c i) ∧
        BandCondition σ (D*σ^(3*beta η)) (u c i) b := by
    intro c hc i
    change 0 < map S.law ctx c at hc
    have hh:=(hcl c hc (e (slotEmbedding i))).choose_spec
    simpa only [u,dite_eq_left hc,hσeq,PS',Prepared.reindex] using hh
  have hflag : ∀c,0 < map S'.law ctx c→∀i,
      ((PS'.domain c (slotEmbedding i)).card:ℝ)≤153*(Nat.card K:ℝ)^4 := by
    intro c hc i
    exact card_le_of_log_le (by positivity) (by positivity) (PS'.cap c (slotEmbedding i))
  have hlwn : (l:ℝ)≤(w:ℝ)*n := by nlinarith
  have hlmid : l<w*(2*n) := by
    have hpos : (0:ℝ)<(w:ℝ)*n := by positivity
    exact_mod_cast (show (l:ℝ)<(w:ℝ)*(2*n) by nlinarith)
  have hll : (l:ℝ)≤(Nat.card K:ℝ)*σ^(1+η) := by
    have hm0 : (0:ℝ)≤ m := by positivity
    linarith
  obtain ⟨hs,hsmall,hwide,hkb0,hkbhi,hε⟩:=hlocal D hD hDhi
  obtain ⟨hmass,hcore⟩:=hend D hD
  have hnum:=hloss (Nat.card K) D m w n B T rem M
    (bandHi σ (D*σ^(3*beta η)) b-bandLo σ (D*σ^(3*beta η)) b) l
    hqp hD (by exact_mod_cast hw) (by exact_mod_cast hn) hml hB hBhi hTlo hrlo hM hMhi hlwn
    closed hclosed hopen (by
      intro hh
      have hb : b.val%2=0 := by simpa only [closed,decide_eq_true_eq] using hh
      rw [band_gap_closed hb];ring_nf;exact le_rfl)
    (by
      intro hh
      have hb : b.val%2≠0 := by simpa only [closed,decide_eq_false_iff_not] using hh
      rw [band_gap_open hb])
  obtain ⟨out⟩:=hstage D (D*σ^(6*beta η)) (Real.log (153*(Nat.card K:ℝ)^4))
    (bandLo σ (D*σ^(3*beta η)) b) (bandHi σ (D*σ^(3*beta η)) b) B M (D*σ^(3*beta η)) R L₀
    q₀ K V Ω κ α hd hq3 N w n H T rem l adm S' ctx PS' u b
    (fun c hc i=>(hu c hc i).2.2.1) hflag
    (fun c hc i=>band_endpoints hp.le (by positivity) ⟨(hu c hc i).1,(hu c hc i).2.1⟩ (hu c hc i).2.2.2)
    (by simpa only [hσeq] using (fun c hc i=>(hu c hc i).2.2.2))
    (band_lo_le_hi hp.le (by positivity)) (by positivity) (by rw [hσeq,hJ];linarith)
    hσ hq hcard hRange rfl hT hr hnr hroom hlmid hM hs
    (by simpa only [hσeq] using hsmall) hwide hkb0 hkbhi hwH hHhi hmass
    (by simpa only [hσeq] using hcore) (by simpa only [hq] using hε) (by
      simpa only [closed,decide_eq_true_eq,Nat.cast_mul,Nat.cast_ofNat,hq,show (4:ℝ)*(w*(4*n))=16*w*n by ring] using hnum)
  refine ⟨out.mono le_rfl (hcode (Nat.card K) D R k₀ w H l hq hRange hHpos hHhi hwD hk₀ hll) ?_⟩
  have hh:=reciprocal_domain_slack_bound hη hσ hD
  rw [hJ]
  linarith
end
end SharpRamseyFive.SelectedTuple

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.SelectedTuple.eventually_forward_prepared_stage_oai := @OAI.SharpRamseyFive.SelectedTuple.eventually_forward_prepared_stage_oai
