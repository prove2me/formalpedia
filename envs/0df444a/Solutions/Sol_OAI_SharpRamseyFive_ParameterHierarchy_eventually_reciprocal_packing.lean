-- Prove2me | solution 1 for OAI.SharpRamseyFive.ParameterHierarchy.eventually_reciprocal_packing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:09:43.967168+00:00
-- url     : https://prove2.me/submissions/dd306a90-2d00-4958-bb97-8ac1651228cf

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
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_HighNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

open Filter Real ParameterHierarchy
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
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_IntegerWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real
open scoped Topology
noncomputable section
lemma integral_floor_half {x : ℝ} (hx : 2≤x) :
    0<⌊x⌋₊ ∧ x/2≤(⌊x⌋₊:ℝ) ∧ (⌊x⌋₊:ℝ)≤x := by
  have hh:=Nat.lt_floor_add_one x
  exact ⟨Nat.floor_pos.mpr (by linarith),by linarith,Nat.floor_le (by linarith)⟩
lemma integral_window_packing (m n : ℕ) (hn : 0<n) (hm : 4*n≤ m) :
    let w:= m/(4*n)
    0<w ∧ w*(4*n)≤ m ∧ (m:ℝ)/8≤w*n ∧ (w:ℝ)*n≤ m/4 := by
  dsimp only
  have hw : 1≤ m/(4*n) := (Nat.one_le_div_iff (by omega)).mpr hm
  have hh:=Nat.div_mul_le_self m (4*n)
  have hh' : m<(m/(4*n)+1)*(4*n) := by simpa only [mul_comm] using Nat.lt_mul_div_succ m (show 0<4*n by omega)
  have hw' : (1:ℝ)≤((m/(4*n):ℕ):ℝ) := by exact_mod_cast hw
  have hhR : ((m/(4*n):ℕ):ℝ)*(4*n)≤ m := by exact_mod_cast hh
  have hhR' : (m:ℝ)<(((m/(4*n):ℕ):ℝ)+1)*(4*n) := by exact_mod_cast hh'
  have hnR : (0:ℝ)≤n := by positivity
  have hh2 : ((m/(4*n):ℕ):ℝ)+1≤2*((m/(4*n):ℕ):ℝ) := by linarith
  have hh3:= mul_le_mul_of_nonneg_right hh2 (by positivity : (0:ℝ)≤4*n)
  refine ⟨by omega,hh,?_,?_⟩ <;> nlinarith
lemma integral_round_packing {x : ℝ} (hx : 2≤x) (n : ℕ) (hxhi : 2*x≤n) :
    let T:=⌊x⌋₊
    let rem:=n-T
    0<T ∧ 0 < rem ∧ n≤2*rem ∧ rem+T≤n ∧ (n:ℝ)/2 ≤ rem ∧ x/2≤T := by
  obtain ⟨hT,hlo,hhi⟩:=integral_floor_half hx
  have h2T : 2*⌊x⌋₊≤n := by exact_mod_cast (show (2:ℝ)*⌊x⌋₊≤n by linarith)
  have ht : ⌊x⌋₊≤n := by omega
  dsimp only
  refine ⟨hT,by omega,by omega,by omega,?_,hlo⟩
  rw [Nat.cast_sub ht]
  exact (by linarith [show (2:ℝ)*⌊x⌋₊≤n by exact_mod_cast h2T])
lemma integer_window_length {q D a m : ℝ} (hq : 0<q) (_hD : 0<D) (ha : 0<a)
    (hx : 2≤q*D*a) (mn : ℕ) (hm : (mn:ℝ)= m) (hfit : 8*(q*D*a)≤ m) :
    let n:=⌊q*D*a⌋₊
    let w:= mn/(4*n)
    0<n ∧ 0<w ∧ w*(4*n)≤ mn ∧ m/8≤(w:ℝ)*n ∧
      m/(8*q*a)≤(w:ℝ)*D ∧ (w:ℝ)*D≤ m/(2*q*a) := by
  dsimp only
  obtain ⟨hn,hnlo,hnhi⟩:=integral_floor_half hx
  have hfit' : 4*⌊q*D*a⌋₊≤ mn := by
    exact_mod_cast (show (4:ℝ)*⌊q*D*a⌋₊≤ mn by rw [hm];linarith)
  obtain ⟨hw,hpack,hlo,hhi⟩:=integral_window_packing mn ⌊q*D*a⌋₊ hn hfit'
  rw [hm] at hlo hhi
  refine ⟨hn,hw,hpack,hlo,?_,?_⟩
  · apply (div_le_iff₀ (by positivity : 0<8*q*a)).mpr
    have := mul_le_mul_of_nonneg_left hnhi (show (0:ℝ)≤ mn/(4*⌊q*D*a⌋₊) by positivity)
    nlinarith
  · apply (le_div_iff₀ (by positivity : 0<2*q*a)).mpr
    have := mul_le_mul_of_nonneg_left hnlo (show (0:ℝ)≤ mn/(4*⌊q*D*a⌋₊) by positivity)
    nlinarith
end
end SharpRamseyFive.ParameterHierarchy

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

lemma reciprocal_integer_pack {η c σ q D : ℝ} {m : ℕ}
    (hη : 0<η) (hc : 0 < c) (hσ : 1≤σ) (hqp : 0<q) (hq : 2≤q)
    (hD1 : 1≤D) (hDhi : D≤σ^(1-η/2))
    (hlen : c*q*σ^(1+η)≤ m) (hm : (m:ℝ)≤q*σ^(1+η)) (hm4 : 4≤ m)
    (hfit : 8/c≤σ^η) (hTopen : σ^(-(η/2-3000*beta η))<1/4)
    (hTclosed : ∀D : ℝ,D≤σ^(1-η/2)→D*σ^(3000*beta η)≤(c/16)*σ)
    (hwbig : σ^(1+η/2)≤σ^2) (closed : Bool) :
    ∃w n : ℕ, 0<w ∧ 0<n ∧ w*(4*n)≤ m ∧ (m:ℝ)≤8*(w:ℝ)*n ∧
      (w:ℝ)*D≤σ^(1+η/2) ∧ (w:ℝ)≤σ^2 ∧
      (closed=true→(c/8)*q*σ^(1+η)≤n) ∧
      (closed=false→(c/8)*σ^(1+η/2)≤(w:ℝ)*D) ∧
      2*(q*D*σ^(3000*beta η))≤n := by
  have hp : 0<σ := zero_lt_one.trans_le hσ
  have hDp : 0<D := by linarith
  have hsig : σ≤σ^(1+η) := by
    nth_rw 1 [←Real.rpow_one σ]
    exact Real.rpow_le_rpow_of_exponent_le hσ (by linarith)
  have powadd (a b : ℝ) : σ^a*σ^b=σ^(a+b) := (Real.rpow_add hp _ _).symm

  cases closed with
  | true =>
      obtain ⟨hn,hpack,hlo,hhi⟩:=integral_window_packing m 1 (by norm_num) (by simpa using hm4)
      simp only [mul_one] at hn hpack hlo hhi
      refine ⟨1,m/4,by norm_num,hn,?_,?_,?_,?_,?_,?_,?_⟩
      · simpa only [Nat.one_mul,Nat.mul_comm] using hpack
      · simpa only [Nat.cast_one,one_mul,mul_one] using (show (m:ℝ)≤8*(m/4:ℕ) by linarith)
      · simp only [Nat.cast_one,one_mul]
        exact hDhi.trans (Real.rpow_le_rpow_of_exponent_le hσ (by linarith))
      · simp only [Nat.cast_one]
        nlinarith
      · intro _
        nlinarith
      · intro hh
        contradiction
      · have hx:=mul_le_mul_of_nonneg_left (hTclosed D hDhi) hqp.le
        have hh:=mul_le_mul_of_nonneg_left hsig (show 0 ≤ c*q/16 by positivity)
        nlinarith
  | false =>
      have ha1 : 1≤σ^(η/2) := Real.one_le_rpow hσ (by positivity)
      have hx : 2≤q*D*σ^(η/2) := by
        have hqd : 2≤q*D := by nlinarith
        nlinarith
      have hfit' : 8*(q*D*σ^(η/2))≤(m:ℝ) := by
        have hd : D*σ^(η/2)≤σ := by
          calc
            _ ≤σ^(1-η/2)*σ^(η/2) := mul_le_mul_of_nonneg_right hDhi (by positivity)
            _ =σ := by rw [powadd];rw [show 1-η/2+η/2=(1:ℝ) by ring,Real.rpow_one]
        have hcσ : 8 ≤ c*σ^η := by simpa only [mul_comm] using (div_le_iff₀ hc).mp hfit
        have hmlo : 8*q*σ ≤ c*q*σ^(1+η) := by
          rw [Real.rpow_add hp,Real.rpow_one]
          nlinarith [mul_le_mul_of_nonneg_right hcσ (show 0≤q*σ by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hd hqp.le]
      obtain ⟨hn,hw,hpack,hlo,hwlo,hwhi⟩:=integer_window_length hqp hDp
        (Real.rpow_pos_of_pos hp (η/2)) hx m rfl hfit'
      let n:=⌊q*D*σ^(η/2)⌋₊
      let w:=m/(4*n)
      have hlo' : (c/8)*σ^(1+η/2)≤(w:ℝ)*D := by
        apply le_trans _ hwlo
        apply (le_div_iff₀ (by positivity : 0<8*q*σ^(η/2))).mpr
        have heq : (c/8)*σ^(1+η/2)*(8*q*σ^(η/2))=c*q*σ^(1+η) := by
          calc
            _ =c*q*(σ^(1+η/2)*σ^(η/2)) := by ring
            _ =_ := by rw [powadd];congr 2;ring
        rwa [heq]
      have hhi' : (w:ℝ)*D≤σ^(1+η/2) := by
        apply hwhi.trans
        apply (div_le_iff₀ (by positivity : 0<2*q*σ^(η/2))).mpr
        have heq : σ^(1+η/2)*(2*q*σ^(η/2))=2*q*σ^(1+η) := by
          calc
            _ =2*q*(σ^(1+η/2)*σ^(η/2)) := by ring
            _ =_ := by rw [powadd];congr 2;ring
        rw [heq]
        nlinarith
      refine ⟨w,n,hw,hn,hpack,by linarith,hhi',?_,?_,fun _=>hlo',?_⟩
      · have hh:(w:ℝ)≤(w:ℝ)*D := le_mul_of_one_le_right (by positivity) hD1
        exact hh.trans (hhi'.trans hwbig)
      · intro hh
        contradiction
      · have hnlo:=(integral_floor_half hx).2.1
        have hexp : σ^(3000*beta η)=σ^(-(η/2-3000*beta η))*σ^(η/2) := by
          rw [powadd];congr 1;ring
        have ht : 4*σ^(3000*beta η)≤σ^(η/2) := by
          rw [hexp]
          nlinarith [mul_le_mul_of_nonneg_right hTopen.le (Real.rpow_nonneg hp.le (η/2))]
        have hh:=mul_le_mul_of_nonneg_left ht (show 0≤q*D by positivity)
        dsimp only [n]
        nlinarith

theorem eventually_reciprocal_packing_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop,∀ (q D : ℝ) (m : ℕ),2≤q→σ^beta η≤D→D≤σ^(1-η/2)→
      c*q*σ^(1+η)≤ m→(m:ℝ)≤q*σ^(1+η)→∀closed : Bool,
      ∃ (w n rounds rem : ℕ),
        0<w ∧ 0<n ∧ w*(4*n)≤ m ∧ (m:ℝ)≤8*(w:ℝ)*n ∧
        (w:ℝ)*D≤σ^(1+η/2) ∧ (w:ℝ)≤σ^2 ∧
        (closed=true→(c/8)*q*σ^(1+η)≤n) ∧
        (closed=false→(c/8)*σ^(1+η/2)≤(w:ℝ)*D) ∧
        0 < rounds ∧ 0 < rem ∧ n≤2*rem ∧ rem+rounds≤n ∧
        q*D*σ^(3000*beta η)/2 ≤ rounds ∧ (n:ℝ)/2 ≤ rem := by
  have hb:=beta_pos hη
  have he : 0<η/2-3000*beta η := by unfold beta;linarith
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop (2/c),
    (tendsto_rpow_atTop hη).eventually (eventually_ge_atTop (8/c)),
    (tendsto_rpow_neg_atTop he).eventually_lt_const (by norm_num : (0:ℝ)<1/4),
    eventually_stage_scale hη 3000 (c/16) (by unfold beta;linarith) (by positivity)]
    with σ hσ hσc hfit hTopen hTclosed
  intro q D m hq hD hDhi hlen hm closed
  have hp : 0<σ := zero_lt_one.trans_le hσ
  have hqp : 0<q := by linarith
  have hD1 : 1≤D := (Real.one_le_rpow hσ hb.le).trans hD
  have hDp : 0<D := by linarith
  have hpow1 : 1≤σ^(1+η) := Real.one_le_rpow hσ (by linarith)
  have hsig : σ≤σ^(1+η) := by
    nth_rw 1 [←Real.rpow_one σ]
    exact Real.rpow_le_rpow_of_exponent_le hσ (by linarith)
  have hm4 : 4≤ m := by
    have hsc : 2 ≤ c*σ := by simpa only [mul_comm] using (div_le_iff₀ hc).mp hσc
    have : (4:ℝ)≤ m := by nlinarith [mul_le_mul_of_nonneg_left hsig (mul_nonneg hc.le hqp.le)]
    exact_mod_cast this
  have hlarge : 2≤q*D*σ^(3000*beta η) := by
    have hx : 1≤σ^(3000*beta η) := Real.one_le_rpow hσ (by positivity)
    have hqd : 2≤q*D := by nlinarith
    nlinarith
  have powadd (a b : ℝ) : σ^a*σ^b=σ^(a+b) := (Real.rpow_add hp _ _).symm
  have hwbig : σ^(1+η/2)≤σ^2 := by
    rw [←Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hσ (by linarith)
  have hpack:=reciprocal_integer_pack hη hc hσ hqp hq hD1 hDhi hlen hm hm4
    hfit hTopen hTclosed hwbig closed
  obtain ⟨w,n,hw,hn,hpack,hlo,hhi,hw2,hclosed,hopen,hTn⟩:=hpack
  obtain ⟨hT,hr,h2r,hroom,hrem,hTlo⟩:=integral_round_packing hlarge n hTn
  exact ⟨w,n,⌊q*D*σ^(3000*beta η)⌋₊,n-⌊q*D*σ^(3000*beta η)⌋₊,
    hw,hn,hpack,hlo,hhi,hw2,hclosed,hopen,hT,hr,h2r,hroom,hTlo,hrem⟩
end
end SharpRamseyFive.ParameterHierarchy

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ParameterHierarchy.eventually_reciprocal_packing_oai := @OAI.SharpRamseyFive.ParameterHierarchy.eventually_reciprocal_packing_oai
