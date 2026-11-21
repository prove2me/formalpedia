-- Prove2me | solution 1 for MasulloRH.endpoint_riesz_pairing_and_prime_power_tail
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T03:29:30.309619+00:00
-- url     : https://prove2.me/submissions/699a5321-31af-4340-b1c1-194aa9418365

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.Positivity

namespace MasulloRH

/-- The one-sided half-density sum along positive prime powers starts at exponent one. -/
theorem shifted_half_density_geometric (p s m : ℝ) (hp : 1 < p) :
    HasSum (fun j : ℕ => Real.exp ((s - ((j:ℝ)+1)*Real.log p)/2)*m)
      (Real.exp (s/2)*m/(Real.sqrt p-1)) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hsqrt : 1 < Real.sqrt p := by simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt zero_le_one hp
  let q := (Real.sqrt p)⁻¹
  have hq : 0 < q := inv_pos.mpr (Real.sqrt_pos.mpr hp0)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ hsqrt
  have hbase : Real.exp (-(Real.log p / 2)) = q := by
    rw [Real.exp_neg, Real.exp_half, Real.exp_log hp0]
  let A := Real.exp (s/2)*m
  have H := (hasSum_geometric_of_lt_one hq.le hq1).mul_left (A*q)
  convert! H using 1
  · funext j
    rw [show (s-((j:ℝ)+1)*Real.log p)/2 = s/2 + (-(Real.log p/2)) + (j:ℝ)*(-(Real.log p/2)) by ring,
      Real.exp_add, Real.exp_add, Real.exp_nat_mul, hbase]
    dsimp only [A]; ring
  · dsimp only [A,q]
    field_simp [(ne_of_gt (Real.sqrt_pos.mpr hp0)),(sub_pos.mpr hsqrt).ne']

end MasulloRH
open MeasureTheory
namespace MasulloRH

private theorem a_endpoint_pairing :
    let w (u : ℝ) := Real.exp |u| * (1 + u^2)
    let k (u : ℝ) := Real.exp (u/2) / w u
    let h (u : ℝ) := Real.exp (u - |u|) / (1 + u^2)
    let z := ∫ u : ℝ, h u
    Integrable h ∧ 0 < z ∧ ∀ b : ℝ,
      Integrable (fun u : ℝ => k (u-b)*k u*w u) ∧
      (∫ u : ℝ, k (u-b)*k u*w u) = Real.exp (b/2)*z := by
  dsimp only
  let h (u : ℝ) := Real.exp (u - |u|) / (1 + u^2)
  have hc : Continuous h := by
    dsimp [h]
    exact (Real.continuous_exp.comp (continuous_id.sub continuous_abs)).div
      (continuous_const.add (continuous_id.pow 2)) (fun x => by positivity)
  have hpos (u : ℝ) : 0 < h u := by dsimp [h]; positivity
  have hint : Integrable h := by
    apply integrable_inv_one_add_sq.mono' hc.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (hpos x)]
    dsimp [h]
    rw [← one_div]
    exact div_le_div_of_nonneg_right (Real.exp_le_one_iff.mpr (sub_nonpos.mpr (le_abs_self x))) (by positivity)
  refine ⟨hint,integral_pos_of_integrable_nonneg_nonzero hc hint (fun u => (hpos u).le) (hpos 0).ne',?_⟩
  intro b
  have hstep (u : ℝ) :
      Real.exp ((u-b)/2) / (Real.exp |u-b| * (1+(u-b)^2)) *
        (Real.exp (u/2) / (Real.exp |u| *(1+u^2))) * (Real.exp |u| *(1+u^2))
        = Real.exp (b/2) * h (u-b) := by
    dsimp [h]
    rw [Real.exp_sub]
    field_simp [Real.exp_ne_zero,show (1+u^2:ℝ) ≠ 0 by positivity,
      show (1+(u-b)^2:ℝ) ≠ 0 by positivity]
    repeat rw [← Real.exp_add]
    congr 1
    ring
  simp only [hstep]
  exact ⟨(hint.comp_sub_right b).const_mul _,by rw [integral_const_mul,integral_sub_right_eq_self]⟩

end MasulloRH
open MeasureTheory

theorem solution :
    let w (u : ℝ) := Real.exp |u| * (1 + u^2)
    let k (u : ℝ) := Real.exp (u/2) / w u
    let h (u : ℝ) := Real.exp (u - |u|) / (1 + u^2)
    let z := ∫ u : ℝ, h u
    let a (b u : ℝ) := k (u-b)*k u*w u
    Integrable h ∧ 0 < z ∧
    (∀ b : ℝ, Integrable (a b) ∧ (∫ u : ℝ, a b u) = Real.exp (b/2)*z) ∧
    (∀ p s : ℝ, 1<p →
      HasSum (fun j : ℕ => ∫ u : ℝ, a (s-((j:ℝ)+1)*Real.log p) u)
        (Real.exp (s/2)*z/(Real.sqrt p-1)) ∧
      ∀ (V : Set ℝ) (J : ℕ),
        let t (j : ℕ) := ∫ u in V, a ((s-(J:ℝ)*Real.log p)-((j:ℝ)+1)*Real.log p) u
        Summable t ∧ (∑' j : ℕ, t j) ≤ Real.exp ((s-(J:ℝ)*Real.log p)/2)*z/(Real.sqrt p-1)) := by
  let w (u : ℝ) := Real.exp |u| * (1 + u^2)
  let k (u : ℝ) := Real.exp (u/2) / w u
  let h (u : ℝ) := Real.exp (u - |u|) / (1 + u^2)
  let z := ∫ u : ℝ, h u
  let a (b u : ℝ) := k (u-b)*k u*w u
  change Integrable h ∧ 0 < z ∧ (∀ b : ℝ, Integrable (a b) ∧ _ ) ∧ _
  obtain ⟨hint, hz, hpair⟩ := MasulloRH.a_endpoint_pairing
  refine ⟨hint,hz,hpair,?_⟩
  intro p s hp
  have hfull (t : ℝ) : HasSum (fun j : ℕ => ∫ u : ℝ, a (t-((j:ℝ)+1)*Real.log p) u)
        (Real.exp (t/2)*z/(Real.sqrt p-1)) := by
    simpa only [(show ∀ b:ℝ, (∫ u : ℝ, a b u) = Real.exp (b/2)*z from fun b => (hpair b).2)] using
      MasulloRH.shifted_half_density_geometric p t z hp
  refine ⟨hfull s,?_⟩
  intro V J
  let t := s-(J:ℝ)*Real.log p
  let g (j : ℕ) := ∫ u in V, a (t-((j:ℝ)+1)*Real.log p) u
  let G (j : ℕ) := ∫ u : ℝ, a (t-((j:ℝ)+1)*Real.log p) u
  change Summable g ∧ (∑' j : ℕ, g j) ≤ _
  have hpos (b u : ℝ) : 0 ≤ a b u := by dsimp [a,k,w]; positivity
  have hg (j : ℕ) : 0 ≤ g j := integral_nonneg fun _ => hpos _ _
  have hG (j : ℕ) : g j ≤ G j :=
    setIntegral_le_integral (hpair _).1 (Filter.Eventually.of_forall (hpos _))
  have hsG : Summable G := (hfull t).summable
  have hsg : Summable g := Summable.of_nonneg_of_le hg hG hsG
  exact ⟨hsg, (hsg.tsum_le_tsum hG hsG).trans_eq (hfull t).tsum_eq⟩
