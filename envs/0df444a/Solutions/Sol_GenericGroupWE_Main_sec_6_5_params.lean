-- Prove2me | solution 1 for GenericGroupWE.Main.sec_6_5_params
-- status  : ACCEPTED   (prove)
-- author  : @vigyan
-- created : 2026-11-15T13:56:06.241965+00:00
-- url     : https://prove2.me/submissions/2de76531-b134-452c-93f4-f796494b2941

import Definitions.Def_GenericGroupWE_Main_Tables

-- Local proof module: WitnessEncryption.ParameterBasic
namespace GenericGroupWE.Main
open scoped BigOperators

namespace ParameterProof

lemma weight_pos (N : ℕ) : 1 ≤ weightDegree N := le_max_left _ _

lemma rank_pos (N d : ℕ) : 0 < rankTarget N d := by
  apply Nat.choose_pos
  omega

lemma choose_scale (d r : ℕ) (hr : 1 ≤ r) :
    (1 / (d.factorial : ℝ)) * (r : ℝ)^d ≤ (Nat.choose (r + 2*d) d : ℝ) ∧
      (Nat.choose (r + 2*d) d : ℝ) ≤ ((1 + 2*d : ℕ) : ℝ)^d * (r : ℝ)^d := by
  constructor
  · have h := Nat.pow_le_choose (α := ℝ) d (r + 2*d)
    have hs : r ≤ r + 2*d + 1 - d := by omega
    have hp : (r : ℝ)^d ≤ ((r + 2*d + 1 - d : ℕ) : ℝ)^d := by
      gcongr
    have hf : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
    calc
      (1 / (d.factorial : ℝ)) * (r : ℝ)^d = (r : ℝ)^d / d.factorial := by ring
      _ ≤ ((r + 2*d + 1 - d : ℕ) : ℝ)^d / d.factorial := by gcongr
      _ ≤ (Nat.choose (r + 2*d) d : ℝ) := h
  · have h := Nat.choose_le_pow (r + 2*d) d
    have hs : r + 2*d ≤ (1+2*d)*r := by nlinarith
    calc
      (Nat.choose (r + 2*d) d : ℝ) ≤ ((r + 2*d : ℕ) : ℝ)^d := by exact_mod_cast h
      _ ≤ (((1 + 2*d)*r : ℕ) : ℝ)^d := by gcongr
      _ = ((1+2*d : ℕ) : ℝ)^d * (r : ℝ)^d := by rw [Nat.cast_mul, mul_pow]

lemma matrixOrder_lower (N d : ℕ) (hd : 1 ≤ d) (hN : 2 ≤ N) :
    N ≤ matrixOrder N d := by
  have hsum : N ≤ ∑ j ∈ Finset.range (min d N + 1), Nat.choose N j := by
    simpa using (Finset.single_le_sum (fun j _ => Nat.zero_le (Nat.choose N j))
      (show 1 ∈ Finset.range (min d N + 1) by simp only [Finset.mem_range]; omega))
  have hchoose : 1 ≤ Nat.choose ((rankTarget N d)^2 + weightDegree N) (weightDegree N) :=
    Nat.choose_pos (by omega)
  unfold matrixOrder
  calc
    N ≤ ∑ j ∈ Finset.range (min d N + 1), Nat.choose N j := hsum
    _ ≤ (∑ j ∈ Finset.range (min d N + 1), Nat.choose N j) *
        (N * ((rankTarget N d)^2 + weightDegree N) + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    _ ≤ _ := Nat.le_mul_of_pos_right _ hchoose

lemma label_log_bound (N d : ℕ) :
    Real.logb 2 (Nat.choose ((rankTarget N d)^2 + weightDegree N) (weightDegree N) : ℝ) ≤
      (weightDegree N : ℝ) * Real.logb 2 ((rankTarget N d)^2 + weightDegree N : ℝ) := by
  have hr := weight_pos N
  have hc : 0 < Nat.choose ((rankTarget N d)^2 + weightDegree N) (weightDegree N) :=
    Nat.choose_pos (by omega)
  have hp := Nat.choose_le_pow ((rankTarget N d)^2 + weightDegree N) (weightDegree N)
  calc
    Real.logb 2 (Nat.choose ((rankTarget N d)^2 + weightDegree N) (weightDegree N) : ℝ) ≤
        Real.logb 2 ((((rankTarget N d)^2 + weightDegree N : ℕ) : ℝ)^(weightDegree N)) := by
      apply Real.logb_le_logb_of_le (by norm_num)
      · exact_mod_cast hc
      · exact_mod_cast hp
    _ = _ := by simp only [Real.logb_pow, Nat.cast_add, Nat.cast_pow]

lemma weight_log_bounds (N : ℕ) (hN : 2 ≤ N) :
    Real.logb 2 (N : ℝ) ≤ 4*(weightDegree N : ℝ)^2 ∧
      (weightDegree N : ℝ)^2 ≤ 3*Real.logb 2 (N : ℝ) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 1 ≤ Real.logb 2 (N : ℝ) := by
    calc
      1 = Real.logb 2 (2 : ℝ) := by norm_num [Real.logb]
      _ ≤ Real.logb 2 (N : ℝ) :=
        Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast hN)
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog0 : 0 ≤ Real.logb 2 ((N + 2 : ℕ) : ℝ) := by
    apply Real.logb_nonneg (by norm_num)
    exact_mod_cast (by omega : 1 ≤ N+2)
  have hk : (Nat.log 2 (N+2) : ℝ) ≤ Real.logb 2 ((N+2 : ℕ) : ℝ) := by
    rw [← Real.natFloor_logb_natCast]
    exact Nat.floor_le hlog0
  have hk' : Real.logb 2 ((N+2 : ℕ) : ℝ) < (Nat.log 2 (N+2) : ℝ) + 1 := by
    rw [← Real.natFloor_logb_natCast]
    exact Nat.lt_floor_add_one _
  have hshift : Real.logb 2 ((N+2 : ℕ) : ℝ) ≤ Real.logb 2 (N : ℝ) + 1 := by
    calc
      _ ≤ Real.logb 2 (2 * (N : ℝ)) := by
        apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
        push_cast
        nlinarith
      _ = _ := by
        rw [Real.logb_mul (by norm_num) (ne_of_gt hn0)]
        norm_num [Real.logb]
        ring
  have hmono : Real.logb 2 (N : ℝ) ≤ Real.logb 2 ((N+2 : ℕ) : ℝ) := by
    apply Real.logb_le_logb_of_le (by norm_num) hn0
    push_cast
    linarith
  have hr : (1 : ℝ) ≤ weightDegree N := by exact_mod_cast weight_pos N
  have hs : (Nat.sqrt (Nat.log 2 (N+2)) : ℝ) ≤ weightDegree N := by
    exact_mod_cast (le_max_right 1 (Nat.sqrt (Nat.log 2 (N+2))))
  have hsq : (Nat.log 2 (N+2) : ℝ)+1 ≤
      ((Nat.sqrt (Nat.log 2 (N+2)) : ℝ)+1)^2 := by
    exact_mod_cast Nat.succ_le_succ_sqrt' (Nat.log 2 (N+2))
  have hrsq : (weightDegree N : ℝ)^2 ≤ (Nat.log 2 (N+2) : ℝ)+1 := by
    have hx : (weightDegree N)^2 ≤ Nat.log 2 (N+2) + 1 := by
      unfold weightDegree
      rcases le_total 1 (Nat.sqrt (Nat.log 2 (N+2))) with h | h
      · rw [max_eq_right h]
        exact (Nat.sqrt_le' _).trans (Nat.le_succ _)
      · rw [max_eq_left h]
        simp
    exact_mod_cast hx
  constructor <;> nlinarith [sq_nonneg ((weightDegree N : ℝ) - 1)]

end ParameterProof
end GenericGroupWE.Main

-- Local proof module: WitnessEncryption.ParameterScales
namespace GenericGroupWE.Main
namespace ParameterProof

lemma weight_sqrt_bounds (N : ℕ) (hN : 2 ≤ N) :
    (1/2 : ℝ) * Real.sqrt (Real.logb 2 (N : ℝ)) ≤ (weightDegree N : ℝ) ∧
      (weightDegree N : ℝ) ≤ 2 * Real.sqrt (Real.logb 2 (N : ℝ)) := by
  obtain ⟨hl, hu⟩ := weight_log_bounds N hN
  have hL : 0 ≤ Real.logb 2 (N : ℝ) := by
    apply Real.logb_nonneg (by norm_num)
    exact_mod_cast (by omega : 1 ≤ N)
  have hr : 0 ≤ (weightDegree N : ℝ) := Nat.cast_nonneg _
  have hs := Real.sq_sqrt hL
  have hx := Real.sqrt_nonneg (Real.logb 2 (N : ℝ))
  have hlo : Real.sqrt (Real.logb 2 (N : ℝ)) ≤ 2 * (weightDegree N : ℝ) := by
    apply (sq_le_sq₀ hx (by positivity)).mp
    nlinarith
  have hhi : (weightDegree N : ℝ) ≤ 2 * Real.sqrt (Real.logb 2 (N : ℝ)) := by
    apply (sq_le_sq₀ hr (by positivity)).mp
    nlinarith
  constructor
  · linarith
  · exact hhi

end ParameterProof

theorem parameter_rank_scale_bounds :
    ∀ d : ℕ, 1 ≤ d → ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ N : ℕ, 2 ≤ N →
        a * (weightDegree N : ℝ)^d ≤ (rankTarget N d : ℝ) ∧
        (rankTarget N d : ℝ) ≤ b * (weightDegree N : ℝ)^d ∧
        a * (Real.logb 2 (N : ℝ))^((d : ℝ)/2) ≤ (rankTarget N d : ℝ) ∧
        (rankTarget N d : ℝ) ≤ b * (Real.logb 2 (N : ℝ))^((d : ℝ)/2) := by
  intro d hd
  let A : ℝ := 1 / (d.factorial : ℝ)
  let B : ℝ := ((1+2*d : ℕ) : ℝ)^d
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨min A (A * (1/2 : ℝ)^d), max B (B * (2:ℝ)^d),
    lt_min hA (by positivity), lt_of_lt_of_le hB (le_max_left _ _), ?_⟩
  intro N hN
  have hscale := ParameterProof.choose_scale d (weightDegree N) (ParameterProof.weight_pos N)
  change A * (weightDegree N : ℝ)^d ≤ (rankTarget N d : ℝ) ∧
    (rankTarget N d : ℝ) ≤ B * (weightDegree N : ℝ)^d at hscale
  obtain ⟨hl, hu⟩ := ParameterProof.weight_sqrt_bounds N hN
  have hL : 0 ≤ Real.logb 2 (N : ℝ) := by
    apply Real.logb_nonneg (by norm_num)
    exact_mod_cast (by omega : 1 ≤ N)
  have hroot : (Real.sqrt (Real.logb 2 (N : ℝ)))^d =
      (Real.logb 2 (N : ℝ))^((d : ℝ)/2) := by
    rw [Real.rpow_div_two_eq_sqrt (d : ℝ) hL, Real.rpow_natCast]
  have hlo : ((1/2 : ℝ) * Real.sqrt (Real.logb 2 (N : ℝ)))^d ≤
      (weightDegree N : ℝ)^d := pow_le_pow_left₀ (by positivity) hl d
  have hhi : (weightDegree N : ℝ)^d ≤
      (2 * Real.sqrt (Real.logb 2 (N : ℝ)))^d :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hu d
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans hscale.1
  · exact hscale.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · calc
      min A (A * (1/2 : ℝ)^d) * (Real.logb 2 (N : ℝ))^((d : ℝ)/2) ≤
          (A * (1/2 : ℝ)^d) * (Real.logb 2 (N : ℝ))^((d : ℝ)/2) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg hL _)
      _ = A * ((1/2 : ℝ) * Real.sqrt (Real.logb 2 (N : ℝ)))^d := by
        rw [mul_pow, hroot]
        ring
      _ ≤ A * (weightDegree N : ℝ)^d := mul_le_mul_of_nonneg_left hlo hA.le
      _ ≤ _ := hscale.1
  · calc
      (rankTarget N d : ℝ) ≤ B * (weightDegree N : ℝ)^d := hscale.2
      _ ≤ B * (2 * Real.sqrt (Real.logb 2 (N : ℝ)))^d :=
        mul_le_mul_of_nonneg_left hhi hB.le
      _ = (B * (2:ℝ)^d) * (Real.logb 2 (N : ℝ))^((d : ℝ)/2) := by
        rw [mul_pow, hroot]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hL _)

end GenericGroupWE.Main

-- Local proof module: WitnessEncryption.ParameterEntropy
namespace GenericGroupWE.Main.ParameterProof
open Filter

lemma sqrt_log_sublinear (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ threshold : ℕ, 4 ≤ threshold ∧ ∀ N : ℕ, threshold ≤ N →
      C * Real.sqrt (Real.logb 2 (N : ℝ)) * Real.logb 2 (Real.logb 2 (N : ℝ)) ≤
        ε * Real.logb 2 (N : ℝ) := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hη : 0 < ε * Real.log 2 / C := by positivity
  have hs := (isLittleO_log_rpow_atTop (r := (1/2 : ℝ)) (by norm_num)).bound hη
  have hlim : Tendsto (fun N : ℕ => Real.logb 2 (N : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hevent := hlim.eventually hs
  obtain ⟨T, hT⟩ := hevent.exists_forall_of_atTop
  refine ⟨max T 4, le_max_right _ _, ?_⟩
  intro N hN
  have hbound := hT N ((le_max_left _ _).trans hN)
  have hN' : (4 : ℝ) ≤ N := by exact_mod_cast ((le_max_right T 4).trans hN)
  have hL : 1 ≤ Real.logb 2 (N : ℝ) := by
    calc
      1 = Real.logb 2 (2 : ℝ) := by norm_num [Real.logb]
      _ ≤ _ := Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by linarith)
  have hlog : 0 ≤ Real.log (Real.logb 2 (N : ℝ)) := Real.log_nonneg hL
  have hroot := Real.sqrt_nonneg (Real.logb 2 (N : ℝ))
  have hsq := Real.sq_sqrt (by linarith : 0 ≤ Real.logb 2 (N : ℝ))
  simp only [Real.norm_eq_abs, abs_of_nonneg hlog, ← Real.sqrt_eq_rpow,
    abs_of_nonneg hroot] at hbound
  calc
    C * Real.sqrt (Real.logb 2 (N : ℝ)) * Real.logb 2 (Real.logb 2 (N : ℝ)) =
        (C * Real.sqrt (Real.logb 2 (N : ℝ)) / Real.log 2) *
          Real.log (Real.logb 2 (N : ℝ)) := by simp only [Real.logb]; ring
    _ ≤ (C * Real.sqrt (Real.logb 2 (N : ℝ)) / Real.log 2) *
        ((ε * Real.log 2 / C) * Real.sqrt (Real.logb 2 (N : ℝ))) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = ε * Real.logb 2 (N : ℝ) := by
      field_simp [ne_of_gt hC, ne_of_gt htwo]
      nlinarith [hsq]

end GenericGroupWE.Main.ParameterProof

namespace GenericGroupWE.Main.ParameterProof
open Filter

lemma power_gap (K a c e : ℝ) (hK : 0 ≤ K) (ha : 0 < a) (hce : c < e) :
    ∀ᶠ x : ℝ in atTop, (K*x)^c ≤ a*x^e := by
  have hlim := tendsto_rpow_atTop (sub_pos.mpr hce)
  have hev := hlim.eventually (eventually_ge_atTop (K^c/a))
  filter_upwards [hev, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hk : K^c ≤ a*x^(e-c) := by simpa only [mul_comm] using (div_le_iff₀ ha).mp hx
  calc
    (K*x)^c = K^c*x^c := Real.mul_rpow hK hx0.le
    _ ≤ (a*x^(e-c))*x^c := mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hx0.le _)
    _ = a*x^e := by rw [mul_assoc, ← Real.rpow_add hx0]; congr 1; ring

lemma matrix_log_comparison (d : ℕ) (C : ℝ) (hC : 0 < C)
    (horder : ∀ N : ℕ, 2 ≤ N → N ≤ matrixOrder N d ∧
      (matrixOrder N d : ℝ) ≤ C*(N : ℝ)^C) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ N : ℕ, 2 ≤ N →
      1 ≤ Real.logb 2 (N : ℝ) ∧
      Real.logb 2 (N : ℝ) ≤ Real.logb 2 (matrixOrder N d : ℝ) ∧
      Real.logb 2 (matrixOrder N d : ℝ) ≤ K*Real.logb 2 (N : ℝ) := by
  refine ⟨|Real.logb 2 C|+C+1, by linarith [abs_nonneg (Real.logb 2 C)], ?_⟩
  intro N hN
  obtain ⟨hl, hu⟩ := horder N hN
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hm0 : (0 : ℝ) < matrixOrder N d := by exact_mod_cast (by omega : 0 < matrixOrder N d)
  have hL : 1 ≤ Real.logb 2 (N : ℝ) := by
    calc
      1 = Real.logb 2 (2 : ℝ) := by norm_num [Real.logb]
      _ ≤ _ := Real.logb_le_logb_of_le (by norm_num) (by norm_num) hN'
  refine ⟨hL, Real.logb_le_logb_of_le (by norm_num) hN0 (by exact_mod_cast hl), ?_⟩
  calc
    Real.logb 2 (matrixOrder N d : ℝ) ≤ Real.logb 2 (C*(N : ℝ)^C) :=
      Real.logb_le_logb_of_le (by norm_num) hm0 hu
    _ = Real.logb 2 C + C*Real.logb 2 (N : ℝ) := by
      rw [Real.logb_mul (ne_of_gt hC) (by positivity), Real.logb_rpow_eq_mul_logb_of_pos hN0]
    _ ≤ (|Real.logb 2 C|+C+1)*Real.logb 2 (N : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hL (abs_nonneg (Real.logb 2 C)),
        le_abs_self (Real.logb 2 C)]

end GenericGroupWE.Main.ParameterProof


namespace GenericGroupWE.Main

theorem parameter_weight_entropy_bound :
    ∀ d : ℕ, 1 ≤ d → ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 4 ≤ N →
        (weightDegree N : ℝ) * Real.logb 2 ((rankTarget N d)^2 + weightDegree N : ℝ) ≤
          C * Real.sqrt (Real.logb 2 (N : ℝ)) * Real.logb 2 (Real.logb 2 (N : ℝ)) := by
  intro d hd
  let B : ℝ := ((1+2*d : ℕ) : ℝ)^d
  have hB : 0 < B := by dsimp [B]; positivity
  have hlogB : 0 ≤ Real.logb 2 (B^2+1) :=
    Real.logb_nonneg (by norm_num) (by nlinarith [sq_nonneg B])
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨2*(Real.logb 2 (B^2+1)+3*d), by positivity, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := by omega
  have hN' : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hr : (1 : ℝ) ≤ weightDegree N := by exact_mod_cast ParameterProof.weight_pos N
  have hr0 : (0 : ℝ) < weightDegree N := by linarith
  have hL : 2 ≤ Real.logb 2 (N : ℝ) := by
    calc
      2 = Real.logb 2 (4 : ℝ) := by
        rw [show (4 : ℝ) = 2^2 by norm_num, Real.logb_pow]
        norm_num [Real.logb]
      _ ≤ _ := Real.logb_le_logb_of_le (by norm_num) (by norm_num) hN'
  have hL0 : 0 < Real.logb 2 (N : ℝ) := by linarith
  have hll : 1 ≤ Real.logb 2 (Real.logb 2 (N : ℝ)) := by
    calc
      1 = Real.logb 2 (2 : ℝ) := by norm_num [Real.logb]
      _ ≤ _ := Real.logb_le_logb_of_le (by norm_num) (by norm_num) hL
  have hscale := (ParameterProof.choose_scale d (weightDegree N) (ParameterProof.weight_pos N)).2
  change (rankTarget N d : ℝ) ≤ B * (weightDegree N : ℝ)^d at hscale
  have hsquare : (rankTarget N d : ℝ)^2 ≤ B^2 * (weightDegree N : ℝ)^(2*d) := by
    calc
      _ ≤ (B * (weightDegree N : ℝ)^d)^2 := by gcongr
      _ = _ := by rw [mul_pow, ← pow_mul (weightDegree N : ℝ) d 2, Nat.mul_comm d 2]
  have hrpow : (weightDegree N : ℝ) ≤ (weightDegree N : ℝ)^(2*d) := by
    simpa using (pow_le_pow_right₀ hr (show 1 ≤ 2*d by omega))
  have hbase : (rankTarget N d : ℝ)^2 + (weightDegree N : ℝ) ≤
      (B^2+1) * (weightDegree N : ℝ)^(2*d) := by nlinarith
  have hlogbase : Real.logb 2 ((rankTarget N d)^2 + weightDegree N : ℝ) ≤
      Real.logb 2 (B^2+1) + ((2*d : ℕ) : ℝ) * Real.logb 2 (weightDegree N : ℝ) := by
    calc
      _ ≤ Real.logb 2 ((B^2+1) * (weightDegree N : ℝ)^(2*d)) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) hbase
      _ = _ := by rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow]
  have hroot : 0 < Real.sqrt (Real.logb 2 (N : ℝ)) := Real.sqrt_pos.2 hL0
  have hsqrt := (ParameterProof.weight_sqrt_bounds N hN2).2
  have hlogr : Real.logb 2 (weightDegree N : ℝ) ≤
      1 + (1/2 : ℝ) * Real.logb 2 (Real.logb 2 (N : ℝ)) := by
    calc
      _ ≤ Real.logb 2 (2 * Real.sqrt (Real.logb 2 (N : ℝ))) :=
        Real.logb_le_logb_of_le (by norm_num) hr0 hsqrt
      _ = _ := by
        rw [Real.logb_mul (by norm_num) (ne_of_gt hroot), Real.sqrt_eq_rpow,
          Real.logb_rpow_eq_mul_logb_of_pos hL0]
        norm_num [Real.logb]
  have hmulLog := mul_le_mul_of_nonneg_left hlogr (show (0 : ℝ) ≤ 2*d by positivity)
  have hlog : Real.logb 2 ((rankTarget N d)^2 + weightDegree N : ℝ) ≤
      (Real.logb 2 (B^2+1)+3*d) * Real.logb 2 (Real.logb 2 (N : ℝ)) := by
    push_cast at hlogbase
    nlinarith [mul_le_mul_of_nonneg_left hll hlogB]
  calc
    (weightDegree N : ℝ) * Real.logb 2 ((rankTarget N d)^2 + weightDegree N : ℝ) ≤
        (weightDegree N : ℝ) *
          ((Real.logb 2 (B^2+1)+3*d) * Real.logb 2 (Real.logb 2 (N : ℝ))) :=
      mul_le_mul_of_nonneg_left hlog (le_of_lt hr0)
    _ ≤ (2 * Real.sqrt (Real.logb 2 (N : ℝ))) *
        ((Real.logb 2 (B^2+1)+3*d) * Real.logb 2 (Real.logb 2 (N : ℝ))) :=
      mul_le_mul_of_nonneg_right hsqrt (by positivity)
    _ = _ := by ring

end GenericGroupWE.Main

-- Local proof module: WitnessEncryption.ParameterOrder
namespace GenericGroupWE.Main.ParameterProof
open scoped BigOperators

lemma weight_le_twice (N : ℕ) (hN : 2 ≤ N) : weightDegree N ≤ 2*N := by
  unfold weightDegree
  apply max_le (by omega)
  exact ((Nat.sqrt_le_self _).trans (Nat.log_le_self 2 (N+2))).trans (by omega)

lemma matrixOrder_poly_of_labels (N d : ℕ) (hd : 1 ≤ d) (hN : 2 ≤ N)
    (hlabels : Nat.choose ((rankTarget N d)^2 + weightDegree N) (weightDegree N) ≤ N) :
    matrixOrder N d ≤ (d+1)*(((d+2)^d)^2+3)*N^(3*d+2) := by
  let D := (d+2)^d
  let B := D^2+2
  have hN1 : 1 ≤ N := by omega
  have hr := weight_le_twice N hN
  have hR : rankTarget N d ≤ D*N^d := by
    calc
      rankTarget N d ≤ (weightDegree N+2*d)^d := Nat.choose_le_pow _ _
      _ ≤ ((d+2)*N)^d := by gcongr; nlinarith
      _ = D*N^d := by rw [mul_pow]
  have hp : N ≤ N^(2*d) := by
    simpa using Nat.pow_le_pow_right hN1 (show 1 ≤ 2*d by omega)
  have hbase : (rankTarget N d)^2 + weightDegree N ≤ B*N^(2*d) := by
    have hR2 : (rankTarget N d)^2 ≤ D^2*N^(2*d) := by
      calc
        _ ≤ (D*N^d)^2 := by gcongr
        _ = _ := by rw [mul_pow, ← pow_mul N d 2, Nat.mul_comm d 2]
    dsimp [B]
    nlinarith
  have hsample : N*((rankTarget N d)^2+weightDegree N)+1 ≤ (B+1)*N^(2*d+1) := by
    have hx := Nat.mul_le_mul_left N hbase
    have hp1 : 1 ≤ N^(2*d+1) := Nat.one_le_pow _ _ hN1
    calc
      _ ≤ N*(B*N^(2*d)) + N^(2*d+1) := Nat.add_le_add hx hp1
      _ = _ := by rw [pow_succ N (2*d)]; ring
  have hcolumns : (∑ j ∈ Finset.range (min d N+1), Nat.choose N j) ≤ (d+1)*N^d := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (min d N+1), N^d := by
        apply Finset.sum_le_sum
        intro j hj
        have hjd : j ≤ d := by simp only [Finset.mem_range] at hj; omega
        exact (Nat.choose_le_pow N j).trans (Nat.pow_le_pow_right hN1 hjd)
      _ = (min d N+1)*N^d := by simp
      _ ≤ (d+1)*N^d := Nat.mul_le_mul_right _ (by omega)
  calc
    matrixOrder N d ≤ ((d+1)*N^d) * ((B+1)*N^(2*d+1)) * N :=
      Nat.mul_le_mul (Nat.mul_le_mul hcolumns hsample) hlabels
    _ = (d+1)*(((d+2)^d)^2+3)*N^(3*d+2) := by
      rw [show 3*d+2 = d+(2*d+1)+1 by omega,
        pow_succ N (d+(2*d+1)), pow_add N d (2*d+1)]
      dsimp [B, D]
      ring

end GenericGroupWE.Main.ParameterProof


namespace GenericGroupWE.Main.ParameterProof
open scoped BigOperators

lemma polynomial_envelope (f : ℕ → ℕ) (e K T : ℕ)
    (hf : ∀ N : ℕ, 2 ≤ N → T ≤ N → f N ≤ K*N^e) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → (f N : ℝ) ≤ C*(N : ℝ)^C := by
  let K' := K + ∑ n ∈ Finset.range T, f n
  let E := max K' e + 1
  have hE : 0 < E := by dsimp [E]; omega
  have hEK : K' ≤ E := by dsimp [E]; omega
  have hEe : e ≤ E := by dsimp [E]; omega
  have hglobal : ∀ N : ℕ, 2 ≤ N → f N ≤ K'*N^e := by
    intro N hN
    by_cases hT : T ≤ N
    · exact (hf N hN hT).trans (Nat.mul_le_mul_right _ (by dsimp [K']; omega))
    · have hsum : f N ≤ ∑ n ∈ Finset.range T, f n :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp only [Finset.mem_range]; omega)
      have hp : 1 ≤ N^e := Nat.one_le_pow e N (by omega)
      calc
        f N ≤ ∑ n ∈ Finset.range T, f n := hsum
        _ ≤ K' := by dsimp [K']; omega
        _ ≤ K'*N^e := Nat.le_mul_of_pos_right _ hp
  refine ⟨(E : ℝ), by exact_mod_cast hE, ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  calc
    (f N : ℝ) ≤ (K' : ℝ)*(N : ℝ)^e := by exact_mod_cast hglobal N hN
    _ ≤ (E : ℝ)*(N : ℝ)^e := by gcongr
    _ = (E : ℝ)*(N : ℝ)^(e : ℝ) := by rw [Real.rpow_natCast]
    _ ≤ (E : ℝ)*(N : ℝ)^(E : ℝ) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.rpow_le_rpow_of_exponent_le hN1 (by exact_mod_cast hEe)
      · positivity

end GenericGroupWE.Main.ParameterProof

namespace GenericGroupWE.Main

theorem parameter_matrix_order_bound :
    ∀ d : ℕ, 1 ≤ d → ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → N ≤ matrixOrder N d ∧
        (matrixOrder N d : ℝ) ≤ C * (N : ℝ)^C := by
  intro d hd
  obtain ⟨B, hB, hentropy⟩ := parameter_weight_entropy_bound d hd
  obtain ⟨T, hT, hslow⟩ := ParameterProof.sqrt_log_sublinear B 1 hB (by norm_num)
  have hlabels : ∀ N : ℕ, T ≤ N →
      Nat.choose ((rankTarget N d)^2 + weightDegree N) (weightDegree N) ≤ N := by
    intro N hN
    have hN4 : 4 ≤ N := hT.trans hN
    have hlog := (ParameterProof.label_log_bound N d).trans
      ((hentropy N hN4).trans (hslow N hN))
    rw [one_mul] at hlog
    have hc : 0 < Nat.choose ((rankTarget N d)^2+weightDegree N) (weightDegree N) :=
      Nat.choose_pos (by omega)
    have hreal := (Real.logb_le_logb (by norm_num)
      (by exact_mod_cast hc) (by exact_mod_cast (by omega : 0 < N))).mp hlog
    exact_mod_cast hreal
  obtain ⟨C, hC, hbound⟩ := ParameterProof.polynomial_envelope
    (fun N => matrixOrder N d) (3*d+2) ((d+1)*(((d+2)^d)^2+3)) T
    (fun N hN hTN => ParameterProof.matrixOrder_poly_of_labels N d hd hN (hlabels N hTN))
  exact ⟨C, hC, fun N hN => ⟨ParameterProof.matrixOrder_lower N d hd hN, hbound N hN⟩⟩

end GenericGroupWE.Main

-- Local proof module: WitnessEncryption.Parameters
namespace GenericGroupWE.Main
open scoped BigOperators

theorem sec_6_5_params :
    ∀ d : ℕ, 1 ≤ d →
    ∃ C : ℝ, 0 < C ∧
      (∀ N : ℕ, 2 ≤ N → N ≤ matrixOrder N d ∧
        (matrixOrder N d : ℝ) ≤ C * (N : ℝ)^C) ∧
      (∀ c : ℝ, 0 < c → 2*c < (d : ℝ) →
        ∃ threshold : ℕ, 2 ≤ threshold ∧ ∀ N : ℕ, threshold ≤ N →
          (Real.logb 2 (matrixOrder N d : ℝ))^c ≤ (rankTarget N d : ℝ)) ∧
      (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ threshold : ℕ, 2 ≤ threshold ∧
        ∀ N : ℕ, threshold ≤ N →
          a * (weightDegree N : ℝ)^d ≤ (rankTarget N d : ℝ) ∧
          (rankTarget N d : ℝ) ≤ b * (weightDegree N : ℝ)^d ∧
          a * (Real.logb 2 (N : ℝ))^((d : ℝ)/2) ≤ (rankTarget N d : ℝ) ∧
          (rankTarget N d : ℝ) ≤ b * (Real.logb 2 (N : ℝ))^((d : ℝ)/2) ∧
          a * (Real.logb 2 (matrixOrder N d : ℝ))^((d : ℝ)/2) ≤ (rankTarget N d : ℝ) ∧
          (rankTarget N d : ℝ) ≤ b * (Real.logb 2 (matrixOrder N d : ℝ))^((d : ℝ)/2)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ threshold : ℕ, 2 ≤ threshold ∧
        ∀ N : ℕ, threshold ≤ N →
          Real.logb 2 (Nat.choose ((rankTarget N d)^2 + weightDegree N) (weightDegree N) : ℝ) ≤
            ε * Real.logb 2 (N : ℝ)) ∧
      (∀ N : ℕ, 2 ≤ N →
        Real.logb 2 (Nat.choose ((rankTarget N d)^2 + weightDegree N) (weightDegree N) : ℝ) ≤
          (weightDegree N : ℝ) * Real.logb 2 ((rankTarget N d)^2 + weightDegree N : ℝ)) ∧
      (∃ threshold : ℕ, 4 ≤ threshold ∧ ∀ N : ℕ, threshold ≤ N →
        (weightDegree N : ℝ) * Real.logb 2 ((rankTarget N d)^2 + weightDegree N : ℝ) ≤
          C * Real.sqrt (Real.logb 2 (N : ℝ)) * Real.logb 2 (Real.logb 2 (N : ℝ))) := by
  intro d hd
  obtain ⟨C₀, hC₀, horder⟩ := parameter_matrix_order_bound d hd
  obtain ⟨D, hD, hentropy⟩ := parameter_weight_entropy_bound d hd
  obtain ⟨a, b, ha, hb, hscale⟩ := parameter_rank_scale_bounds d hd
  obtain ⟨K, hK, hlog⟩ := ParameterProof.matrix_log_comparison d C₀ hC₀ horder
  let C := max C₀ D + 1
  have hC₀C : C₀ ≤ C := by dsimp [C]; linarith [le_max_left C₀ D]
  have hDC : D ≤ C := by dsimp [C]; linarith [le_max_right C₀ D]
  have hC : 0 < C := lt_of_lt_of_le hC₀ hC₀C
  let e : ℝ := (d : ℝ)/2
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  refine ⟨C, hC, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N hN
    refine ⟨(horder N hN).1, ?_⟩
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    exact (horder N hN).2.trans (mul_le_mul hC₀C
      (Real.rpow_le_rpow_of_exponent_le hN1 hC₀C) (by positivity) hC.le)
  · intro c hc hcd
    have hgap : c < e := by dsimp [e]; linarith
    have hp := ParameterProof.power_gap K a c e hK0.le ha hgap
    have hlim : Filter.Tendsto (fun N : ℕ => Real.logb 2 (N : ℝ)) Filter.atTop Filter.atTop :=
      (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    obtain ⟨T, hT⟩ := (hlim.eventually hp).exists_forall_of_atTop
    refine ⟨max T 2, le_max_right _ _, ?_⟩
    intro N hN
    have hN2 : 2 ≤ N := (le_max_right T 2).trans hN
    obtain ⟨hL, hLM, hMK⟩ := hlog N hN2
    calc
      (Real.logb 2 (matrixOrder N d : ℝ))^c ≤ (K*Real.logb 2 (N : ℝ))^c :=
        Real.rpow_le_rpow (by linarith) hMK hc.le
      _ ≤ a*(Real.logb 2 (N : ℝ))^e := hT N ((le_max_left T 2).trans hN)
      _ ≤ (rankTarget N d : ℝ) := (hscale N hN2).2.2.1
  · have hKpow : 0 < K^e := Real.rpow_pos_of_pos hK0 _
    let A := min a (a/K^e)
    have hA : 0 < A := lt_min ha (by positivity)
    refine ⟨A, b, hA, hb, 2, le_rfl, ?_⟩
    intro N hN
    obtain ⟨hL, hLM, hMK⟩ := hlog N hN
    have hL0 : 0 ≤ Real.logb 2 (N : ℝ) := by linarith
    have hM0 : 0 ≤ Real.logb 2 (matrixOrder N d : ℝ) := by linarith
    obtain ⟨hlr, hur, hll, hul⟩ := hscale N hN
    have hAa : A ≤ a := min_le_left _ _
    have hAK : A ≤ a/K^e := min_le_right _ _
    refine ⟨?_, hur, ?_, hul, ?_, ?_⟩
    · exact (mul_le_mul_of_nonneg_right hAa (by positivity)).trans hlr
    · exact (mul_le_mul_of_nonneg_right hAa (Real.rpow_nonneg hL0 _)).trans hll
    · calc
        A*(Real.logb 2 (matrixOrder N d : ℝ))^e ≤
            (a/K^e)*(Real.logb 2 (matrixOrder N d : ℝ))^e :=
          mul_le_mul_of_nonneg_right hAK (Real.rpow_nonneg hM0 _)
        _ ≤ (a/K^e)*(K*Real.logb 2 (N : ℝ))^e :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hM0 hMK he) (by positivity)
        _ = a*(Real.logb 2 (N : ℝ))^e := by
          rw [Real.mul_rpow hK0.le hL0]
          field_simp [ne_of_gt hKpow]
        _ ≤ _ := hll
    · exact hul.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hL0 hLM he) hb.le)
  · intro ε hε
    obtain ⟨T, hT, hslow⟩ := ParameterProof.sqrt_log_sublinear D ε hD hε
    refine ⟨T, by omega, ?_⟩
    intro N hN
    exact (ParameterProof.label_log_bound N d).trans
      ((hentropy N (hT.trans hN)).trans (hslow N hN))
  · intro N hN
    exact ParameterProof.label_log_bound N d
  · refine ⟨4, le_rfl, ?_⟩
    intro N hN
    have hN2 : 2 ≤ N := by omega
    have hL := (hlog N hN2).1
    have hll : 0 ≤ Real.logb 2 (Real.logb 2 (N : ℝ)) := Real.logb_nonneg (by norm_num) hL
    exact (hentropy N hN).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hDC (Real.sqrt_nonneg _)) hll)

end GenericGroupWE.Main

open scoped BigOperators
open GenericGroupWE.Main

theorem solution :
∀ d : ℕ, 1 ≤ d →
    ∃ C : ℝ, 0 < C ∧
      (∀ N : ℕ, 2 ≤ N → N ≤ matrixOrder N d ∧
        (matrixOrder N d : ℝ) ≤ C * (N : ℝ)^C) ∧
      (∀ c : ℝ, 0 < c → 2*c < (d : ℝ) →
        ∃ threshold : ℕ, 2 ≤ threshold ∧ ∀ N : ℕ, threshold ≤ N →
          (Real.logb 2 (matrixOrder N d : ℝ))^c ≤ (rankTarget N d : ℝ)) ∧
      (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ threshold : ℕ, 2 ≤ threshold ∧
        ∀ N : ℕ, threshold ≤ N →
          a * (weightDegree N : ℝ)^d ≤ (rankTarget N d : ℝ) ∧
          (rankTarget N d : ℝ) ≤ b * (weightDegree N : ℝ)^d ∧
          a * (Real.logb 2 (N : ℝ))^((d : ℝ)/2) ≤ (rankTarget N d : ℝ) ∧
          (rankTarget N d : ℝ) ≤ b * (Real.logb 2 (N : ℝ))^((d : ℝ)/2) ∧
          a * (Real.logb 2 (matrixOrder N d : ℝ))^((d : ℝ)/2) ≤ (rankTarget N d : ℝ) ∧
          (rankTarget N d : ℝ) ≤ b * (Real.logb 2 (matrixOrder N d : ℝ))^((d : ℝ)/2)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ threshold : ℕ, 2 ≤ threshold ∧
        ∀ N : ℕ, threshold ≤ N →
          Real.logb 2 (Nat.choose ((rankTarget N d)^2 + weightDegree N) (weightDegree N) : ℝ) ≤
            ε * Real.logb 2 (N : ℝ)) ∧
      (∀ N : ℕ, 2 ≤ N →
        Real.logb 2 (Nat.choose ((rankTarget N d)^2 + weightDegree N) (weightDegree N) : ℝ) ≤
          (weightDegree N : ℝ) * Real.logb 2 ((rankTarget N d)^2 + weightDegree N : ℝ)) ∧
      (∃ threshold : ℕ, 4 ≤ threshold ∧ ∀ N : ℕ, threshold ≤ N →
        (weightDegree N : ℝ) * Real.logb 2 ((rankTarget N d)^2 + weightDegree N : ℝ) ≤
          C * Real.sqrt (Real.logb 2 (N : ℝ)) * Real.logb 2 (Real.logb 2 (N : ℝ))) :=
  @GenericGroupWE.Main.sec_6_5_params
