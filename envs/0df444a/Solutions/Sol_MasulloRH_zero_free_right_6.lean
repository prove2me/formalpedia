-- Prove2me | solution 6 for MasulloRH.zero_free_right
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:59:44.636287+00:00
-- url     : https://prove2.me/submissions/539de12e-eb9b-4747-9695-23b1ef9c9ba7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NymanBeurling_localized_zero_obstruction
import Theorems.Thm_NymanBeurling_subpower_remainder_certificates

open Filter Topology

private theorem cost_root {x y : ℝ} (hx : 0≤x) {n : ℕ} (hn : 0<n) (h : x^n≤y) :
    x≤y^(1/(n:ℝ)) := by
  have h' := Real.rpow_le_rpow (pow_nonneg hx n) h (by positivity : 0≤1/(n:ℝ))
  simpa only [one_div,Real.pow_rpow_inv_natCast hx hn.ne'] using h'

theorem solution (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs_one : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  let b := 2*s.re-1
  let V := ‖s‖^2
  have hb : 0<b := by dsimp [b];linarith
  have hV : 0≤V := sq_nonneg _
  let p := min (b/2) (b/(4*(V+1)))
  have hp : 0<p := lt_min (by positivity) (by positivity)
  obtain ⟨J,hJ⟩ := exists_nat_gt (1/p)
  let d := 1/(J+1:ℝ)
  have hd : 0<d := by dsimp [d];positivity
  have hdp : d<p := by
    apply (div_lt_iff₀' (by positivity : 0<(J+1:ℝ))).mpr
    have hJ' := (div_lt_iff₀ hp).mp hJ
    nlinarith
  have hdb : d<b := by linarith [hdp.trans_le (min_le_left _ _)]
  have hVd : 4*V*d<b := by
    have h := (lt_div_iff₀ (by positivity : 0<4*(V+1))).mp (hdp.trans_le (min_le_right _ _))
    nlinarith
  have hlim : Tendsto (fun n : ℕ => (n+1:ℝ)^(-(b-d))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (sub_pos.mpr hdb)).comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  obtain ⟨L,hL⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hd))
  obtain ⟨H,K,c,hH,hP,hC⟩ := NymanBeurling.subpower_remainder_certificates J L
  let R := fun n : ℕ => 1-∑ k∈c.support,c k*((((n+1)%(k+2):ℕ):ℚ)/(k+2:ℚ))
  let E := fun n : ℕ => ((R n)^2/((n+1:ℚ)*(n+2:ℚ)):ℚ)
  let P : ℚ := ∑ n∈Finset.range H,E n
  let C : ℚ := (∑ n∈Finset.range K,E n)+(1+∑ k∈c.support,|c k|)^2/(K+1:ℚ)
  change P≤1/(J+1:ℚ) at hP
  change C^(J+1)≤(H+1:ℚ) at hC
  have hp' : (P:ℝ)≤d := by simpa only [d,Rat.cast_div,Rat.cast_add,Rat.cast_one,Rat.cast_natCast] using (Rat.cast_le (K:=ℝ)).mpr hP
  have epos (n : ℕ) : 0≤E n := by dsimp [E];positivity
  have ppos : 0≤(P:ℝ) := by exact_mod_cast (Finset.sum_nonneg (s:=Finset.range H) fun i _ => epos i)
  have cpos : 0≤(C:ℝ) := by
    have hsum := Finset.sum_nonneg (s:=Finset.range K) fun i _ => epos i
    have : 0≤C := by dsimp only [C];positivity
    exact_mod_cast this
  let x := (H+1:ℝ)
  have hx : 0<x := by dsimp [x];positivity
  have hc : (C:ℝ)≤x^d := by
    have h := cost_root cpos (n:=J+1) (by omega) (y:=x) (by simpa only [x,Rat.cast_pow,Rat.cast_add,Rat.cast_one,Rat.cast_natCast] using (Rat.cast_le (K:=ℝ)).mpr hC)
    simpa only [Nat.cast_add,Nat.cast_one] using h
  have htail : x^(-b)*((C:ℝ)-(P:ℝ))≤d := by
    calc _ ≤ x^(-b)*x^d := mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hx.le _)
         _ = x^(-(b-d)) := by rw [←Real.rpow_add hx];congr 1;ring
         _ ≤ d := (hL H hH).le
  have h := (NymanBeurling.localized_zero_obstruction s hs hs_one hz c H K).2.2
  change b ≤ 2*V*((∑ n∈Finset.range H,(E n:ℝ))+x^(1-2*s.re)*((C:ℝ)-(∑ n∈Finset.range H,(E n:ℝ)))) at h
  have pcast : (∑ n∈Finset.range H,(E n:ℝ))=(P:ℝ) := by simp [P]
  rw [pcast,show 1-2*s.re= -b by dsimp [b];ring] at h
  have hh := mul_le_mul_of_nonneg_left (add_le_add hp' htail) (by linarith : 0≤2*V)
  linarith
