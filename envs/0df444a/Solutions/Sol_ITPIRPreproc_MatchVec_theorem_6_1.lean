-- Prove2me | solution 1 for ITPIRPreproc.MatchVec.theorem_6_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jesko
-- created : 2026-11-13T16:48:05.655394+00:00
-- url     : https://prove2.me/submissions/944b5e46-7802-4ee7-87cf-6f1f011a921f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
import Definitions.Def_ITPIRPreproc_MatchVec_Model
import Theorems.Thm_ITPIRPreproc_MatchVec_matching_vectors_eq7
import Theorems.Thm_ITPIRPreproc_MatchVec_lemma_6_2
import Theorems.Thm_ITPIRPreproc_MatchVec_lemma_4_2
import Theorems.Thm_ITPIRPreproc_MatchVec_power_four_padding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
open scoped ENNReal NNReal

namespace PIRParameters
lemma sqrt_ratio (x : ℝ) (hx : 0 < x) :
    Real.sqrt (x * Real.log x) = x * Real.sqrt (Real.log x / x) := by
  symm
  calc
    x * Real.sqrt (Real.log x / x) = Real.sqrt (x^2) * Real.sqrt (Real.log x / x) := by
      rw [Real.sqrt_sq hx.le]
    _ = Real.sqrt (x^2 * (Real.log x / x)) := (Real.sqrt_mul (sq_nonneg x) _).symm
    _ = Real.sqrt (x * Real.log x) := by congr 1; field_simp

lemma subpolynomial_envelope (dim : ℕ → ℕ) (C : ℝ) (k : ℕ)
    (hd : ∀ h : ℕ, 3 ≤ h → (dim h : ℝ) ≤ 2 ^ (C * Real.sqrt (h * Real.log h))) :
    ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧
      ∀ h : ℕ, 3 ≤ h → 0 ≤ η h ∧
        ((dim h : ℝ) + 1) * (h : ℝ)^k ≤ (((4^h : ℕ) : ℝ) ^ η h) := by
  let η : ℕ → ℝ := fun h =>
    (((|C| * Real.sqrt (Real.log h / h) + 1 / h) * Real.log 2) +
      k * (Real.log h / h)) / Real.log 4
  refine ⟨η, ?_, ?_⟩
  · have hlog : Tendsto (fun h : ℕ => Real.log h / h) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun h : ℕ => (1:ℝ) / h) atTop (𝓝 0) := by
      simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have hs := hlog.sqrt
    have ht := (((hs.const_mul |C|).add hinv).mul_const (Real.log 2)).add (hlog.const_mul (k:ℝ))
    simpa [η] using ht.div_const (Real.log 4)
  · intro h hh
    have hp : 0 < (h:ℝ) := by exact_mod_cast (show 0 < h by omega)
    have h1 : (1:ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
    have hlog : 0 ≤ Real.log h := Real.log_nonneg h1
    have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    constructor
    · dsimp [η]; positivity
    · have hd' : (dim h : ℝ) ≤ 2 ^ (|C| * Real.sqrt (h * Real.log h)) := by
        refine (hd h hh).trans ?_
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
      have hone : (1:ℝ) ≤ 2 ^ (|C| * Real.sqrt (h * Real.log h)) := by
        exact Real.one_le_rpow (by norm_num) (by positivity)
      have hdim : (dim h : ℝ) + 1 ≤ 2 ^ (|C| * Real.sqrt (h * Real.log h) + 1) := by
        rw [Real.rpow_add (by norm_num : (0:ℝ)<2), Real.rpow_one]
        linarith
      have he : Real.log (((4^h : ℕ) : ℝ)) * η h =
          (|C| * Real.sqrt (h * Real.log h) + 1) * Real.log 2 + (k:ℝ)*Real.log h := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, sqrt_ratio _ hp]
        dsimp [η]
        field_simp
        <;> ring
      apply (Real.log_le_log_iff (by positivity : 0 < ((dim h : ℝ)+1)* (h:ℝ)^k)
        (by positivity : 0 < (((4^h : ℕ) : ℝ)^η h))).mp
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
        Real.log_rpow (by positivity), mul_comm (η h), he]
      have hl := Real.log_le_log (by positivity : (0:ℝ)<(dim h:ℝ)+1) hdim
      rw [Real.log_rpow (by norm_num : (0:ℝ)<2)] at hl
      linarith

lemma error_amplification (lam T : ℕ) :
    (T : ℝ≥0∞) * (7 / 8 : ℝ≥0∞)^(8*(lam+1)) ≤
      (T : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞)^lam := by
  have hbase : (7 / 8 : ℝ≥0∞)^8 ≤ 2⁻¹ := by
    have hn : (7 / 8 : ℝ≥0)^8 ≤ 2⁻¹ := by
      change (((7 / 8 : ℝ≥0)^8 : ℝ≥0) : ℝ) ≤ ((2⁻¹ : ℝ≥0) : ℝ)
      norm_num
    have he := ENNReal.coe_le_coe.mpr hn
    simpa only [ENNReal.coe_pow, ENNReal.coe_div (by norm_num : (8:ℝ≥0) ≠ 0),
      ENNReal.coe_inv_two, ENNReal.coe_ofNat] using he
  have hp : (7 / 8 : ℝ≥0∞)^(8*(lam+1)) ≤ (2⁻¹ : ℝ≥0∞)^(lam+1) := by
    rw [pow_mul]
    exact pow_le_pow_left' hbase _
  have hhalf : (2⁻¹ : ℝ≥0∞)^(lam+1) ≤ (2⁻¹ : ℝ≥0∞)^lam := by
    rw [pow_succ]
    have hh : (2⁻¹ : ℝ≥0∞) ≤ 1 := ENNReal.inv_le_one.mpr (by norm_num)
    exact mul_le_of_le_one_right' hh
  exact mul_le_mul_of_nonneg_left (hp.trans hhalf) zero_le
end PIRParameters

namespace PIRParameters
lemma budget_arithmetic (A C L m M t r q ell : ℝ)
    (hL : 1 ≤ L) (hm : 1 ≤ m) (hM : 1 ≤ M)
    (ht : 0 ≤ t) (htM : t ≤ M) (hr : 0 ≤ r) (hrM : r ≤ M)
    (hq : 0 ≤ q) (hqM : q ≤ 4*M) (hell : 0 ≤ ell) (hellM : ell ≤ 4*M) :
    let K := 10*(|A|+1)*(|C|+1)
    A*(L*m*(C*t)+L*(m*m)*(C*r)) ≤ K*(m*m)*M*L ∧
    A*(C*t+L*m*(C*r)) ≤ K*m*M*L ∧
    A*(L*q+ell) ≤ K*M*L ∧
    A*m ≤ K*m ∧
    A*(L*m*(C*t+C*r)+L*(C*t+C*t)+m*ell) ≤ K*m*M*L ∧
    A*(L*(C*m*r)+m) ≤ K*m*M*L := by
  let J := (|A|+1)*(|C|+1)
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hA : A ≤ J := by
    have h1 := le_abs_self A
    dsimp [J]
    nlinarith [abs_nonneg A,abs_nonneg C,mul_nonneg (abs_nonneg A) (abs_nonneg C)]
  have hAC : A*C ≤ J := by
    have h1 := le_abs_self (A*C)
    rw [abs_mul] at h1
    dsimp [J]
    nlinarith [abs_nonneg A,abs_nonneg C]
  have hLM : 0 ≤ L*m := by positivity
  have hLmm : 0 ≤ L*(m*m) := by positivity
  have hT : A*C*t ≤ J*M :=
    (mul_le_mul_of_nonneg_right hAC ht).trans (mul_le_mul_of_nonneg_left htM hJ)
  have hR : A*C*r ≤ J*M :=
    (mul_le_mul_of_nonneg_right hAC hr).trans (mul_le_mul_of_nonneg_left hrM hJ)
  have hQ : A*q ≤ 4*(J*M) := by
    calc A*q ≤ J*q := mul_le_mul_of_nonneg_right hA hq
         _ ≤ J*(4*M) := mul_le_mul_of_nonneg_left hqM hJ
         _ = _ := by ring
  have hE : A*ell ≤ 4*(J*M) := by
    calc A*ell ≤ J*ell := mul_le_mul_of_nonneg_right hA hell
         _ ≤ J*(4*M) := mul_le_mul_of_nonneg_left hellM hJ
         _ = _ := by ring
  have hX : 0 ≤ J*M := mul_nonneg hJ (by linarith)
  have h1 : J*M ≤ L*m*(J*M) := by
    calc J*M = 1*(J*M) := by ring
         _ ≤ L*m*(J*M) := by gcongr; nlinarith
  have h2 : L*(J*M) ≤ L*m*(J*M) := by gcongr; nlinarith
  have h3 : m*(J*M) ≤ L*m*(J*M) := by gcongr; nlinarith
  have h4 : L*m*(J*M) ≤ L*(m*m)*(J*M) := by gcongr; nlinarith
  have h5 : J*M ≤ L*(J*M) := by
    calc J*M = 1*(J*M) := by ring
         _ ≤ L*(J*M) := by gcongr
  have h6 : J*m ≤ L*m*(J*M) := by
    calc J*m ≤ J*m*(L*M) := by
           calc J*m = J*m*1 := by ring
                _ ≤ _ := by gcongr; nlinarith
         _ = _ := by ring
  have hK : 10*(|A|+1)*(|C|+1) = 10*J := by dsimp [J]; ring
  dsimp only
  rw [hK]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · have b1 := mul_le_mul_of_nonneg_left hT hLM
    have b2 := mul_le_mul_of_nonneg_left hR hLmm
    nlinarith only [b1,b2,h4,h1,hX]
  · have b1 := mul_le_mul_of_nonneg_left hR hLM
    nlinarith only [hT,b1,h1,hX]
  · have b1 := mul_le_mul_of_nonneg_left hQ (by linarith : 0 ≤ L)
    nlinarith only [b1,hE,h5,hX]
  · have b1 := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ m)
    nlinarith only [b1,mul_nonneg hJ (show 0 ≤ m by linarith)]
  · have b1 := mul_le_mul_of_nonneg_left hT hLM
    have b2 := mul_le_mul_of_nonneg_left hR hLM
    have b3 := mul_le_mul_of_nonneg_left hT (by linarith : 0 ≤ L)
    have b4 := mul_le_mul_of_nonneg_left hE (by linarith : 0 ≤ m)
    nlinarith only [b1,b2,b3,b4,h2,h3,h1,hX]
  · have b1 := mul_le_mul_of_nonneg_left hR hLM
    have b2 := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ m)
    nlinarith only [b1,b2,h6,h1,hX]

lemma envelope_bounds (d h M : ℝ) (c : ℕ) (hd : 0 ≤ d) (hh : 1 ≤ h)
    (hbound : (d+1)*h^(c+3) ≤ M) :
    1 ≤ M ∧ h ≤ M ∧ h*d ≤ M ∧ d*h^c ≤ M ∧ (h+3)*d ≤ 4*M := by
  have hp : 1 ≤ h^(c+3) := one_le_pow₀ hh
  have hp1 : h ≤ h^(c+3) := by
    simpa using (pow_le_pow_right₀ hh (show 1 ≤ c+3 by omega))
  have hpc : h^c ≤ h^(c+3) := pow_le_pow_right₀ hh (by omega)
  have hpos : 0 ≤ h := by linarith
  have hb1 : h^(c+3) ≤ (d+1)*h^(c+3) := by nlinarith
  have hb2 : d*h^(c+3) ≤ (d+1)*h^(c+3) := by nlinarith
  have hhd : h*d ≤ M := by
    calc h*d ≤ h^(c+3)*d := mul_le_mul_of_nonneg_right hp1 hd
         _ ≤ M := by nlinarith
  have hdc : d*h^c ≤ M :=
    (mul_le_mul_of_nonneg_left hpc hd).trans (hb2.trans hbound)
  have hdM : d ≤ M := by nlinarith
  exact ⟨hp.trans (hb1.trans hbound),hp1.trans (hb1.trans hbound),hhd,hdc,by nlinarith⟩
end PIRParameters

namespace PIRParameters
open ITPIRPreproc.MatchVec
lemma budget_mono {S : Scheme} {n lam : ℕ} {B B' : Budget}
    (hb : MeetsBudget S n lam B)
    (hpre : B.preWork ≤ B'.preWork) (hps : B.preSpace ≤ B'.preSpace)
    (hon : B.online ≤ B'.online) (hoff : B.offline ≤ B'.offline)
    (hcw : B.clientWork ≤ B'.clientWork) (hcs : B.clientSpace ≤ B'.clientSpace)
    (hsw : B.serverWork ≤ B'.serverWork) : MeetsBudget S n lam B' := by
  intro D
  obtain ⟨hp,hr⟩ := hb D
  constructor
  · intro τ
    obtain ⟨hh,hw,hs⟩ := hp τ
    exact ⟨hh,hw.trans hpre,hs.trans hps⟩
  · intro st hst i τ
    obtain ⟨hh,hon',hoff',hw,hs1,hs2,hs3,hsw'⟩ := hr st hst i τ
    exact ⟨hh,hon'.trans hon,hoff'.trans hoff,hw.trans hcw,
      hs1.trans hcs,hs2.trans hcs,hs3.trans hcs,hsw'.trans hsw⟩
end PIRParameters
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ENNReal
open Filter Topology ITPIRPreproc.MatchVec PIRParameters

lemma PIRParameters.square_scheme :
    ∃ S : Scheme, S.WellFormed ∧
      ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧
        ∃ (K : ℝ) (c : ℕ), ∀ h lam : ℕ, 3 ≤ h → 1 ≤ lam →
          PerfectlyPrivate S (4^h) lam ∧
          Correct S (4^h) lam (fun T => (T : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞)^lam) ∧
          MeetsBudget S (4^h) lam
            { preWork := K * ((4^h : ℕ) : ℝ)^(1+η h) * (lam:ℝ)^c
              preSpace := K * ((4^h : ℕ) : ℝ)^((1:ℝ)/2+η h) * (lam:ℝ)^c
              online := K * lam * ((4^h : ℕ) : ℝ)^(η h)
              offline := K * Real.sqrt (4^h : ℕ)
              clientWork := K * ((4^h : ℕ) : ℝ)^((1:ℝ)/2+η h) * (lam:ℝ)^c
              clientSpace := K * ((4^h : ℕ) : ℝ)^((1:ℝ)/2+η h) * (lam:ℝ)^c
              serverWork := K * ((4^h : ℕ) : ℝ)^((1:ℝ)/2+η h) * (lam:ℝ)^c } := by
  obtain ⟨dim,u,v,Cmv,C₀,c₀,vecProg,tableProg,hmv,hcomp⟩ := matching_vectors_eq7
  obtain ⟨C,c,hprim⟩ := lemma_6_2 C₀ c₀
  obtain ⟨hprob,I,hintProg,hdet,heff⟩ := hprim dim u v vecProg tableProg
    (fun h hh => (hmv h hh).1) hcomp
  obtain ⟨A,hcompiler⟩ := lemma_4_2
  obtain ⟨S,hS,hcost⟩ := hcompiler (actFamily dim u v) I
  obtain ⟨η,hη,hbound⟩ := subpolynomial_envelope dim Cmv (c+3) (fun h hh => (hmv h hh).2)
  let K := 10*(|A|+1)*(|C|+1)
  refine ⟨S,hS,η,hη,K,1,?_⟩
  intro h lam hh hlam
  have hm8 : 8 ≤ 2^h := by
    calc 8 = 2^3 := by norm_num
         _ ≤ 2^h := Nat.pow_le_pow_right (by omega) hh
  have hn : 2^h * 2^h = 4^h := by rw [← mul_pow]; norm_num
  have hall := hcost (2^h) (C*h*dim h) (C*dim h*(h:ℝ)^c) (C*h*dim h)
    (C*h*dim h) (C*2^h*dim h*(h:ℝ)^c) ((h+1)*dim h) (2*dim h)
    hm8 (hprob h hh).1 (heff h hh).2.2.2.1 lam hlam
  rw [hn] at hall
  refine ⟨hall.1,?_,?_⟩
  · intro D adv hadv T
    exact (hall.2.1 D adv hadv T).trans (error_amplification lam T)
  · let m : ℝ := (2^h : ℕ)
    let M : ℝ := ((4^h : ℕ) : ℝ)^η h
    have hmn : m*m = ((4^h : ℕ) : ℝ) := by dsimp [m]; norm_cast
    have hm : 1 ≤ m := by dsimp [m]; exact_mod_cast (show 1 ≤ 2^h by omega)
    have hmpos : 0 < m := by linarith
    have hh1 : (1:ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
    have hL : (1:ℝ) ≤ lam := by exact_mod_cast hlam
    have hd : (0:ℝ) ≤ dim h := Nat.cast_nonneg _
    have hb := envelope_bounds (dim h) h M c hd hh1 (hbound h hh).2
    have hM : 1 ≤ M := hb.1
    have hlog : Real.log (m*m) ≤ 4*M := by
      have he : Real.log (m*m) = 2*(h:ℝ)*Real.log 2 := by
        dsimp [m]
        rw [Real.log_mul (by positivity) (by positivity)]
        simp only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
        ring
      rw [he]
      have hl2 : Real.log 2 ≤ 2 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
      have hh0 : (0:ℝ) ≤ h := Nat.cast_nonneg _
      have hs := mul_le_mul_of_nonneg_left hl2 hh0
      linarith [hb.2.1]
    have har := budget_arithmetic A C lam m M ((h:ℝ)*dim h) ((dim h:ℝ)*(h:ℝ)^c)
      (((h:ℝ)+3)*dim h) (Real.log (m*m)) hL hm hM (by positivity) hb.2.2.1
      (by positivity) hb.2.2.2.1 (by positivity) hb.2.2.2.2
      (Real.log_nonneg (by nlinarith)) hlog
    change _ ≤ K*(m*m)*M*lam ∧ _ ≤ K*m*M*lam ∧ _ ≤ K*M*lam ∧
      _ ≤ K*m ∧ _ ≤ K*m*M*lam ∧ _ ≤ K*m*M*lam at har
    have hpre : (((4^h : ℕ):ℝ)^(1+η h)) = m*m*M := by
      rw [Real.rpow_add (by positivity),Real.rpow_one]
      change ((4^h : ℕ):ℝ)*M = m*m*M
      rw [hmn]
    have hsqrt : Real.sqrt ((4^h : ℕ):ℝ) = m := by rw [← hmn,Real.sqrt_mul_self hmpos.le]
    have hhalf : (((4^h : ℕ):ℝ)^((1:ℝ)/2+η h)) = m*M := by
      rw [Real.rpow_add (by positivity), ← Real.sqrt_eq_rpow, hsqrt]
    apply budget_mono hall.2.2
    · dsimp only
      rw [hpre,pow_one]
      convert har.1 using 1 <;> dsimp [m] <;> push_cast <;> ring
    · dsimp only
      rw [hhalf,pow_one]
      convert har.2.1 using 1 <;> dsimp [m] <;> push_cast <;> ring
    · dsimp only
      convert har.2.2.1 using 1 <;> dsimp [m,M] <;> push_cast <;> ring
    · dsimp only
      rw [hsqrt]
      exact har.2.2.2.1
    · dsimp only
      rw [hhalf,pow_one]
      convert har.2.2.2.2.1 using 1 <;> dsimp [m] <;> push_cast <;> ring
    · dsimp only
      rw [hhalf,pow_one]
      convert har.2.2.2.2.1 using 1 <;> dsimp [m] <;> push_cast <;> ring
    · dsimp only
      rw [hhalf,pow_one]
      convert har.2.2.2.2.2 using 1 <;> dsimp [m] <;> push_cast <;> ring

theorem solution :
    ∃ S : Scheme, S.WellFormed ∧
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        ∃ (C : ℝ) (c : ℕ), ∀ n lam : ℕ, 1 ≤ n → 1 ≤ lam →
          PerfectlyPrivate S n lam ∧
          Correct S n lam (fun T => (T : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ lam) ∧
          MeetsBudget S n lam
            { preWork := C * (n : ℝ) ^ (1 + ε n) * (lam : ℝ) ^ c
              preSpace := C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c
              online := C * lam * (n : ℝ) ^ (ε n)
              offline := C * Real.sqrt n
              clientWork := C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c
              clientSpace := C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c
              serverWork := C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c } := by
  exact power_four_padding PIRParameters.square_scheme

