-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.dyadic_initial_schedule
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T09:26:47.747892+00:00
-- url     : https://prove2.me/submissions/435912a6-470d-496d-a6a8-e9abe2dbb899

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

/-- A finite public cap on dyadic halving gives a first crossing of the
    terminal width. The terminal source lies in the interval [w/2,w]. -/
private theorem first_halving_crossing (W w : ℝ) (K : ℕ)
    (hW : 0 < W) (hw : 0 < w) (hstart : w ≤ W)
    (hcap : W ≤ (2 : ℝ)^K * w) :
    ∃ k : ℕ, k ≤ K ∧
      w / 2 ≤ W / (2 : ℝ)^k ∧ W / (2 : ℝ)^k ≤ w ∧
      ∀ j < k, w < W / (2 : ℝ)^j := by
  have hex : ∃ k : ℕ, W / (2 : ℝ)^k ≤ w := by
    refine ⟨K, (div_le_iff₀ (by positivity)).2 ?_⟩
    simpa [mul_comm] using hcap
  let k := Nat.find hex
  have hupper : W / (2 : ℝ)^k ≤ w := Nat.find_spec hex
  have hkle : k ≤ K := Nat.find_min' hex ((div_le_iff₀ (by positivity)).2 (by simpa [mul_comm] using hcap))
  have hbefore : ∀ j < k, w < W / (2 : ℝ)^j := by
    intro j hj
    exact lt_of_not_ge (Nat.find_min hex hj)
  have hlower : w / 2 ≤ W / (2 : ℝ)^k := by
    by_cases hk : k = 0
    · rw [hk]
      norm_num
      linarith
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk
      have hprev := hbefore j (by omega)
      rw [hj, pow_succ]
      have hpos : (0 : ℝ) < (2 : ℝ)^j := by positivity
      have hsplit : W / ((2 : ℝ)^j * 2) = (W / (2 : ℝ)^j) / 2 := by ring
      rw [hsplit]
      linarith
  exact ⟨k, hkle, hlower, hupper, hbefore⟩

/-- If the desired target has the fixed-family threshold and the initial
width starts above its terminal scale, dyadic halving stays strictly above the
source smoothing threshold. At the first crossing the target's amplitude
fits the BDD radius, despite the source width being rational and the terminal
scale possibly irrational. -/
private theorem initial_to_terminal_schedule
    (n : ℕ) (q sigma eta target W : ℝ) (K : ℕ)
    (hn : 0 < n) (hq : 0 < q) (hsigma : 0 < sigma)
    (heta : 0 < eta) (htarget : 0 < target) (hW : 0 < W)
    (hthreshold : (16*q*Real.sqrt n/sigma)*eta ≤ target)
    (hstart : target*sigma/(Real.sqrt 2*Real.sqrt n) ≤ W)
    (hcap : W ≤ (2 : ℝ)^K*(target*sigma/(Real.sqrt 2*Real.sqrt n))) :
    ∃ k : ℕ, k ≤ K ∧
      (∀ j < k, Real.sqrt 2*q*eta < W/(2 : ℝ)^j) ∧
      Real.sqrt 2*q*eta < W/(2 : ℝ)^k ∧
      Real.sqrt n/(Real.sqrt 2*target) ≤ sigma/(2*(W/(2 : ℝ)^k)) ∧
      1/(Real.sqrt 2*(1/(Real.sqrt 2*target))) = target ∧
      (target*sigma/(Real.sqrt 2*Real.sqrt n))^2 = target^2*sigma^2/(2*(n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have htwo : 0 < Real.sqrt (2 : ℝ) := by positivity
  have htwoSq : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  let w := target*sigma/(Real.sqrt 2*Real.sqrt n)
  have hw : 0 < w := by dsimp [w]; positivity
  have hbound : 16*q*Real.sqrt n*eta ≤ target*sigma := by
    apply (div_le_iff₀ hsigma).mp
    calc
      (16*q*Real.sqrt n*eta)/sigma = (16*q*Real.sqrt n/sigma)*eta := by ring
      _ ≤ target := hthreshold
  have hslack : 8*Real.sqrt 2*q*eta ≤ w := by
    dsimp [w]
    apply (le_div_iff₀ (mul_pos htwo hnroot)).mpr
    calc
      8*Real.sqrt 2*q*eta*(Real.sqrt 2*Real.sqrt n) =
          (8*(Real.sqrt (2 : ℝ))^2)*q*Real.sqrt n*eta := by ring
      _ = 16*q*Real.sqrt n*eta := by rw [htwoSq]; norm_num
      _ ≤ target*sigma := hbound
  obtain ⟨k,hkle,hlow,hup,hbefore⟩ := first_halving_crossing W w K hW hw hstart hcap
  have hqe : 0 < Real.sqrt 2*q*eta := by positivity
  have hsmall : Real.sqrt 2*q*eta < w/2 := by nlinarith
  have hu : 0 < W/(2 : ℝ)^k := by positivity
  refine ⟨k,hkle,?_,hsmall.trans_le hlow,?_,?_,?_⟩
  · intro j hj
    exact (by nlinarith : Real.sqrt 2*q*eta < w).trans (hbefore j hj)
  · have hup' : (W/(2 : ℝ)^k)*(Real.sqrt 2*Real.sqrt n) ≤ target*sigma := by
      apply (le_div_iff₀ (mul_pos htwo hnroot)).mp
      simpa [w] using hup
    apply (div_le_div_iff₀ (mul_pos htwo htarget) (by positivity : 0 < 2*(W/(2 : ℝ)^k))).mpr
    calc
      Real.sqrt n*(2*(W/(2 : ℝ)^k)) =
          Real.sqrt 2*((W/(2 : ℝ)^k)*(Real.sqrt 2*Real.sqrt n)) := by
            calc
              _ = (2 : ℝ)*(W/(2 : ℝ)^k)*Real.sqrt n := by ring
              _ = (Real.sqrt (2 : ℝ))^2*(W/(2 : ℝ)^k)*Real.sqrt n := by rw [htwoSq]
              _ = _ := by ring
      _ ≤ Real.sqrt 2*(target*sigma) := mul_le_mul_of_nonneg_left hup' htwo.le
      _ = sigma*(Real.sqrt 2*target) := by ring
  · field_simp
  · simp only [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sq_sqrt hnR.le]


/-- A bit-length cap for a positive rational width ratio. The dependence is
on numerator and denominator bit lengths, not on their magnitudes. -/
private theorem rational_width_cap (start target : ℚ) (hstart : 0 < start) (htarget : 0 < target) :
    let K := Nat.size start.num.natAbs + Nat.size target.den
    (start : ℝ) ≤ (2 : ℝ)^K*(target : ℝ) := by
  have hstartNum : 0 < start.num := Rat.num_pos.mpr hstart
  have htargetNum : 0 < target.num := Rat.num_pos.mpr htarget
  have hstartDen : (0 : ℝ) < start.den := by exact_mod_cast start.den_pos
  have htargetDen : (0 : ℝ) < target.den := by exact_mod_cast target.den_pos
  have hstartNumR : (0 : ℝ) < start.num := by exact_mod_cast hstartNum
  have htargetNumR : (1 : ℝ) ≤ target.num := by exact_mod_cast htargetNum
  have hstartDenR : (1 : ℝ) ≤ start.den := by exact_mod_cast start.den_pos
  have hstartId : (start : ℝ) = (start.num : ℝ)/(start.den : ℝ) := by
    exact_mod_cast start.num_div_den.symm
  have htargetId : (target : ℝ) = (target.num : ℝ)/(target.den : ℝ) := by
    exact_mod_cast target.num_div_den.symm
  have hstartBound : (start : ℝ) ≤ (start.num.natAbs : ℝ) := by
    rw [hstartId]
    have hcast : (start.num.natAbs : ℝ) = (start.num : ℝ) := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, abs_of_nonneg hstartNumR.le]
    rw [hcast]
    exact (div_le_self hstartNumR.le hstartDenR)
  have htargetBound : 1 ≤ (target : ℝ)*(target.den : ℝ) := by
    rw [htargetId]
    field_simp
    exact htargetNumR
  have hsize1 : (start.num.natAbs : ℝ) ≤ (2 : ℝ)^Nat.size start.num.natAbs := by
    exact_mod_cast (Nat.lt_size_self start.num.natAbs).le
  have hsize2 : (target.den : ℝ) ≤ (2 : ℝ)^Nat.size target.den := by
    exact_mod_cast (Nat.lt_size_self target.den).le
  have ht : (0 : ℝ) < target := by exact_mod_cast htarget
  have hNatPos : (0 : ℝ) ≤ start.num.natAbs := by positivity
  dsimp only
  rw [pow_add]
  have hm := mul_le_mul hsize1 hsize2 (by positivity : 0 ≤ (target.den : ℝ))
    (by positivity : 0 ≤ (2 : ℝ)^Nat.size start.num.natAbs)
  nlinarith [mul_nonneg hNatPos (sub_nonneg.mpr htargetBound),
    mul_nonneg ht.le (sub_nonneg.mpr hm)]

/-- The fixed Gaussian width sigma=n+2 makes the terminal input scale at
least the positive requested output width. -/
private theorem fixed_terminal_ge_requested (n : ℕ) (target : ℝ)
    (hn : 0 < n) (htarget : 0 < target) :
    target ≤ target*((n : ℝ)+2)/(Real.sqrt 2*Real.sqrt n) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs2 : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hs2Sq : (Real.sqrt (2 : ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hsnSq : (Real.sqrt (n : ℝ))^2=n := Real.sq_sqrt (by positivity)
  have hsum : Real.sqrt 2*Real.sqrt n ≤ (n : ℝ)+2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,hs2Sq,hsnSq]
    nlinarith [sq_nonneg ((n : ℝ)+1)]
  apply (le_div_iff₀ (mul_pos hs2 hsn)).mpr
  exact mul_le_mul_of_nonneg_left hsum htarget.le


theorem solution (n : ℕ) (q eta : ℝ) (start target : ℚ)
    (hn : 0 < n) (hq : 0 < q) (heta : 0 < eta)
    (hstart : 0 < start) (htarget : 0 < target)
    (hthreshold : (16*q*Real.sqrt n/((n : ℝ)+2))*eta ≤ (target : ℝ))
    (hinit : (target : ℝ)*((n : ℝ)+2)/(Real.sqrt 2*Real.sqrt n) ≤ (start : ℝ)) :
    let K := Nat.size start.num.natAbs + Nat.size target.den
    ∃ k : ℕ, k ≤ K ∧
      (∀ j < k, Real.sqrt 2*q*eta < (start : ℝ)/(2 : ℝ)^j) ∧
      Real.sqrt 2*q*eta < (start : ℝ)/(2 : ℝ)^k ∧
      Real.sqrt n/(Real.sqrt 2*(target : ℝ)) ≤ ((n : ℝ)+2)/(2*((start : ℝ)/(2 : ℝ)^k)) ∧
      1/(Real.sqrt 2*(1/(Real.sqrt 2*(target : ℝ)))) = (target : ℝ) ∧
      ((target : ℝ)*((n : ℝ)+2)/(Real.sqrt 2*Real.sqrt n))^2 =
        (target : ℝ)^2*((n : ℝ)+2)^2/(2*(n : ℝ)) := by
  have ht : (0 : ℝ) < target := by exact_mod_cast htarget
  have hs : (0 : ℝ) < start := by exact_mod_cast hstart
  have hsig : (0 : ℝ) < (n : ℝ)+2 := by positivity
  have hrange := fixed_terminal_ge_requested n (target : ℝ) hn ht
  have hcap := rational_width_cap start target hstart htarget
  have hcap' : (start : ℝ) ≤ (2 : ℝ)^(Nat.size start.num.natAbs + Nat.size target.den)*
      ((target : ℝ)*((n : ℝ)+2)/(Real.sqrt 2*Real.sqrt n)) :=
    hcap.trans (mul_le_mul_of_nonneg_left hrange (by positivity))
  exact initial_to_terminal_schedule n q ((n : ℝ)+2) eta target start
    (Nat.size start.num.natAbs + Nat.size target.den)
    hn hq hsig heta ht hs hthreshold hinit hcap'

#print axioms solution
end
