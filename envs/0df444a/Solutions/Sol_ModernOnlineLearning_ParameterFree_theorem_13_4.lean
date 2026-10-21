-- Prove2me | solution 1 for ModernOnlineLearning.ParameterFree.theorem_13_4
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T05:43:33.517879+00:00
-- url     : https://prove2.me/submissions/e755829e-632c-4e61-879e-fe1f76312939

import Theorems.Thm_ModernOnlineLearning_ParameterFree_wealth_dominates_potential
open Filter Topology ModernOnlineLearning.ParameterFree


private lemma inv_midpoint_sum_bound (x : ℝ) (hx : 0 < x) (n : ℕ) :
    (∑ k ∈ Finset.range n, (x + (k : ℝ) + 1 / 2)⁻¹ ^ 2) ≤ x⁻¹ - (x + n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have ha : 0 < x + (n : ℝ) := by positivity
    have hb : 0 < x + (n : ℝ) + 1 := by positivity
    have hm : 0 < x + (n : ℝ) + 1 / 2 := by positivity
    have ht : (x + (n : ℝ) + 1 / 2)⁻¹ ^ 2 ≤
        (x + (n : ℝ))⁻¹ - (x + (n : ℝ) + 1)⁻¹ := by
      field_simp
      nlinarith
    push_cast
    rw [← add_assoc]
    linarith

private lemma convex_gamma_approx (n : ℕ) :
    ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x * Real.log x - Real.BohrMollerup.logGammaSeq (x + 1/2) n) := by
  let f' : ℝ → ℝ := fun x => Real.log x + 1 - Real.log n +
    ∑ k ∈ Finset.range (n + 1), (x + 1/2 + k)⁻¹
  let f'' : ℝ → ℝ := fun x => x⁻¹ -
    ∑ k ∈ Finset.range (n + 1), (x + 1/2 + k)⁻¹ ^ 2
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := f') (f'' := f'') (convex_Ici 0)
  · apply Real.continuous_mul_log.continuousOn.sub
    unfold Real.BohrMollerup.logGammaSeq
    apply ContinuousOn.sub
    · fun_prop
    · apply continuousOn_finsetSum
      intro k hk
      apply ContinuousOn.log
      · fun_prop
      · intro x hx
        have hx0 : 0 ≤ x := hx
        positivity
  · intro x hx
    have hx0 : 0 < x := by simpa using hx
    have hsum : HasDerivAt (fun x : ℝ => ∑ k ∈ Finset.range (n + 1), Real.log (x + 1/2 + k))
        (∑ k ∈ Finset.range (n + 1), (x + 1/2 + k)⁻¹) x := by
      apply HasDerivAt.fun_sum
      intro k hk
      convert! (((hasDerivAt_id x).add_const (1/2)).add_const (k : ℝ)).log (by positivity) using 1 <;> try simp
    have hd : HasDerivAt (fun x : ℝ => Real.BohrMollerup.logGammaSeq (x + 1/2) n)
        (Real.log n - ∑ k ∈ Finset.range (n + 1), (x + 1/2 + k)⁻¹) x := by
      unfold Real.BohrMollerup.logGammaSeq
      convert! ((((hasDerivAt_id x).add_const (1/2)).mul_const (Real.log n)).add_const
          (Real.log (Nat.factorial n))).sub hsum using 1 <;> try simp
    convert! ((Real.hasDerivAt_mul_log hx0.ne').sub hd).hasDerivWithinAt using 1
    try dsimp [f']
    ring
  · intro x hx
    have hx0 : 0 < x := by simpa using hx
    have hs : HasDerivAt (fun x : ℝ => ∑ k ∈ Finset.range (n + 1), (x + 1/2 + k)⁻¹)
        (∑ k ∈ Finset.range (n + 1), -(x + 1/2 + k)⁻¹ ^ 2) x := by
      apply HasDerivAt.fun_sum
      intro k hk
      convert! (((hasDerivAt_id x).add_const (1/2)).add_const (k : ℝ)).inv (by positivity) using 1 <;> try simp [div_eq_mul_inv, inv_pow]
    convert! (((Real.hasDerivAt_log hx0.ne').add_const 1).sub_const (Real.log n)).add hs |>.hasDerivWithinAt using 1
    all_goals try simp [f', f'', Finset.sum_neg_distrib, sub_eq_add_neg]
  · intro x hx
    have hx0 : 0 < x := by simpa using hx
    have h := inv_midpoint_sum_bound x hx0 (n + 1)
    have hn : 0 ≤ (x + ((n + 1 : ℕ) : ℝ))⁻¹ := by positivity
    dsimp [f'']
    have he : (∑ k ∈ Finset.range (n + 1), (x + 1/2 + k)⁻¹ ^ 2) =
        ∑ k ∈ Finset.range (n + 1), (x + (k : ℝ) + 1/2)⁻¹ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      congr 2 <;> ring
    rw [he]
    linarith

private lemma gamma_shift_entropy_convex : ConvexOn ℝ (Set.Ici 0)
    (fun x : ℝ => x * Real.log x - Real.log (Real.Gamma (x + 1/2))) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz : 0 ≤ a * x + b * y := add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  have ht (z : ℝ) (hz : 0 ≤ z) :
      Tendsto (fun n => z * Real.log z - Real.BohrMollerup.logGammaSeq (z + 1/2) n)
        atTop (𝓝 (z * Real.log z - Real.log (Real.Gamma (z + 1/2)))) :=
    tendsto_const_nhds.sub (Real.BohrMollerup.tendsto_log_gamma (by linarith))
  exact le_of_tendsto_of_tendsto' (ht _ hz) ((ht x hx).const_mul a |>.add ((ht y hy).const_mul b))
    (fun n => (convex_gamma_approx n).2 hx hy ha hb hab)


private lemma binary_entropy_quadratic (T A : ℝ) (hT : 0 < T) (hA : 0 ≤ A) (hAT : A ≤ T) :
    T * Real.log (T / 2) + (2 / T) * (A - T / 2) ^ 2 ≤
      A * Real.log A + (T - A) * Real.log (T - A) := by
  let f : ℝ → ℝ := fun x => x * Real.log x + (T - x) * Real.log (T - x) -
    (2 / T) * (x - T / 2) ^ 2
  let f' : ℝ → ℝ := fun x => Real.log x - Real.log (T - x) - (4 / T) * (x - T/2)
  let f'' : ℝ → ℝ := fun x => x⁻¹ + (T - x)⁻¹ - 4 / T
  have hconv : ConvexOn ℝ (Set.Icc 0 T) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (f' := f') (f'' := f'') (convex_Icc 0 T)
    · exact ((Real.continuous_mul_log.add (Real.continuous_mul_log.comp
        (continuous_const.sub continuous_id))).sub (by fun_prop)).continuousOn
    · intro x hx
      have hx0 : 0 < x ∧ x < T := by simpa using hx
      have hdx := Real.hasDerivAt_mul_log hx0.1.ne'
      have hdtx := (Real.hasDerivAt_mul_log (by linarith : T - x ≠ 0)).comp x
        ((hasDerivAt_id x).const_sub T)
      have hdsq := (((hasDerivAt_id x).sub_const (T/2)).pow 2).const_mul (2/T)
      convert! (hdx.add hdtx |>.sub hdsq).hasDerivWithinAt using 1 <;> try { dsimp [f, f']; ring }
    · intro x hx
      have hx0 : 0 < x ∧ x < T := by simpa using hx
      have hdlog := (Real.hasDerivAt_log (by linarith : T - x ≠ 0)).comp x
        ((hasDerivAt_id x).const_sub T)
      convert! (((Real.hasDerivAt_log hx0.1.ne').sub hdlog).sub
        (((hasDerivAt_id x).sub_const (T/2)).const_mul (4/T))).hasDerivWithinAt using 1 <;>
        try { dsimp [f', f'']; ring }
    · intro x hx
      have hx0 : 0 < x ∧ x < T := by simpa using hx
      have hxT : 0 < T - x := by linarith
      have hxpos := hx0.1
      dsimp [f'']
      field_simp
      nlinarith [sq_nonneg (T - 2*x)]
  have hi := hconv.2 (x := A) (y := T - A) 
    ⟨hA, hAT⟩ (by constructor <;> linarith) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at hi
  have hmid : (1/2 : ℝ)*A+(1/2 : ℝ)*(T-A)=T/2 := by ring
  rw [hmid] at hi
  dsimp [f] at hi
  rw [show T-T/2=T/2 by ring, show T-(T-A)=A by ring] at hi
  nlinarith [show (T-A-T/2)^2=(A-T/2)^2 by ring]


private lemma gamma_normalization_lower (T : ℝ) (hT : 1 ≤ T) :
    -Real.log T / 2 - 1 ≤ Real.log (Real.Gamma (T + 1/2)) +
      Real.log (Real.Gamma (1/2)) - Real.log Real.pi - Real.log (Real.Gamma (T+1)) := by
  have hT0 : 0 < T := by linarith
  have hhalf : 0 < T + 1/2 := by linarith
  have hone : 0 < T + 1 := by linarith
  have hthree : 0 < T + 1/2 + 1 := by linarith
  have hc := Real.convexOn_log_Gamma.2 (x := T+1/2) (y := T+1/2+1)
     hhalf hthree (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [Function.comp_apply, smul_eq_mul] at hc
  rw [show (1/2 : ℝ)*(T+1/2)+(1/2 : ℝ)*(T+1/2+1)=T+1 by ring] at hc
  rw [Real.Gamma_add_one hhalf.ne', Real.log_mul hhalf.ne' (Real.Gamma_pos_of_pos hhalf).ne'] at hc
  have hpi := Real.pi_lt_four
  have he : (5/2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hE : 6 < Real.exp (2 : ℝ) := by
    rw [show (2 : ℝ)=1+1 by norm_num, Real.exp_add]
    nlinarith
  have hp : Real.pi * (T+1/2) ≤ Real.exp 2 * T := by
    have hm := mul_le_mul_of_nonneg_right hpi.le hhalf.le
    nlinarith
  have hl := Real.log_le_log (by positivity : 0 < Real.pi*(T+1/2)) hp
  rw [Real.log_mul Real.pi_pos.ne' hhalf.ne',
    Real.log_mul (Real.exp_pos 2).ne' hT0.ne', Real.log_exp] at hl
  rw [Real.Gamma_one_half_eq, Real.log_sqrt Real.pi_pos.le]
  linarith

private lemma gamma_entropy_product (T A B : ℝ) (hT : 0 < T)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hab : A+B=T) :
    A * Real.log A + B * Real.log B - T * Real.log T +
      Real.log (Real.Gamma (T+1/2)) + Real.log (Real.Gamma (1/2)) ≤
      Real.log (Real.Gamma (A+1/2)) + Real.log (Real.Gamma (B+1/2)) := by
  have hwA : 0 ≤ A/T := div_nonneg hA hT.le
  have hwB : 0 ≤ B/T := div_nonneg hB hT.le
  have hw : A/T+B/T=1 := by rw [← add_div, hab, div_self hT.ne']
  have ha := gamma_shift_entropy_convex.2 (x := T) (y := 0) hT.le (by simp) hwA hwB hw
  have hb := gamma_shift_entropy_convex.2 (x := T) (y := 0) hT.le (by simp) hwB hwA (by linarith)
  simp only [smul_eq_mul, mul_zero, add_zero, div_mul_cancel₀ _ hT.ne', zero_mul] at ha hb
  have hadd := add_le_add ha hb
  have he (r s : ℝ) : (A/T*r+B/T*s)+(B/T*r+A/T*s)=r+s := by
    calc
      _ = (A/T+B/T)*r+(A/T+B/T)*s := by ring
      _ = _ := by rw [hw]; ring
  rw [he] at hadd
  linarith

private lemma potential_exponential_lower (ε : ℝ) (hε : 0 < ε) (T : ℕ) (hT : 1 ≤ T)
    (z : ℝ) (hz : -(T : ℝ) ≤ z ∧ z ≤ (T : ℝ)) :
    ε * Real.exp (z^2/(2*(T:ℝ)) - Real.log (T:ℝ)/2 - 1) ≤ ktPotential ε T z := by
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : 0 < (T : ℝ) := by linarith
  let A : ℝ := ((T : ℝ)+z)/2
  let B : ℝ := ((T : ℝ)-z)/2
  have hA : 0 ≤ A := by dsimp [A]; linarith [hz.1]
  have hB : 0 ≤ B := by dsimp [B]; linarith [hz.2]
  have hab : A+B=(T:ℝ) := by dsimp [A,B]; ring
  have hAhalf : 0 < A+1/2 := by linarith
  have hBhalf : 0 < B+1/2 := by linarith
  have hTone : 0 < (T:ℝ)+1 := by positivity
  have hent := binary_entropy_quadratic (T:ℝ) A hT0 hA (by linarith)
  rw [show (T:ℝ)-A=B by linarith] at hent
  have hsq : (2/(T:ℝ))*(A-(T:ℝ)/2)^2=z^2/(2*(T:ℝ)) := by
    dsimp [A]
    ring
  rw [hsq, Real.log_div hT0.ne' (by norm_num : (2:ℝ)≠0)] at hent
  have hprod := gamma_entropy_product (T:ℝ) A B hT0 hA hB hab
  have hnorm := gamma_normalization_lower (T:ℝ) hT1
  let K : ℝ := 2^T * Real.Gamma (A+1/2) * Real.Gamma (B+1/2) /
    (Real.pi * Real.Gamma ((T:ℝ)+1))
  have hga := Real.Gamma_pos_of_pos hAhalf
  have hgb := Real.Gamma_pos_of_pos hBhalf
  have hgt := Real.Gamma_pos_of_pos hTone
  have hK : 0 < K := by dsimp [K]; positivity
  have hlogK : Real.log K = (T:ℝ)*Real.log 2 + Real.log (Real.Gamma (A+1/2)) +
      Real.log (Real.Gamma (B+1/2)) - Real.log Real.pi - Real.log (Real.Gamma ((T:ℝ)+1)) := by
    dsimp [K]
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) hgb.ne', Real.log_mul (by positivity) hga.ne',
      Real.log_mul Real.pi_pos.ne' hgt.ne', Real.log_pow]
    ring
  have hlower : z^2/(2*(T:ℝ)) - Real.log (T:ℝ)/2 - 1 ≤ Real.log K := by
    rw [hlogK]
    nlinarith
  have he := Real.exp_le_exp.mpr hlower
  rw [Real.exp_log hK] at he
  have hεK : ε*K=ktPotential ε T z := by
    unfold ktPotential
    dsimp [K,A,B]
    rw [show ((T:ℝ)+z)/2+1/2=((T:ℝ)+1+z)/2 by ring,
      show ((T:ℝ)-z)/2+1/2=((T:ℝ)+1-z)/2 by ring]
    ring
  rw [← hεK]
  exact mul_le_mul_of_nonneg_left he hε.le



theorem solution (ε : ℝ) (hε : 0 < ε) (T : ℕ) (hT : 1 ≤ T)
    (c : ℕ → ℝ)
    (hc : ∀ t ∈ Finset.Icc 1 T, -1 ≤ c t ∧ c t ≤ 1) :
    let C : ℝ := ∑ t ∈ Finset.Icc 1 T, c t
    ktPotential ε T C ≤ ktWealth ε c T ∧
      ε * Real.exp (C ^ 2 / (2 * (T : ℝ)) - Real.log (T : ℝ) / 2 - 1) ≤
        ktPotential ε T C := by
  dsimp only
  refine ⟨wealth_dominates_potential ε hε T c hc, potential_exponential_lower ε hε T hT _ ?_⟩
  constructor
  · calc
      _ = ∑ _t ∈ Finset.Icc 1 T, (-1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun t ht => (hc t ht).1)
  · calc
      _ ≤ ∑ _t ∈ Finset.Icc 1 T, (1 : ℝ) := Finset.sum_le_sum (fun t ht => (hc t ht).2)
      _ = _ := by simp

