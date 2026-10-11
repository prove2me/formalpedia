-- Prove2me | solution 1 for GravityNonRenorm.gravity_not_renormalizable
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-10T13:18:25.782779+00:00
-- url     : https://prove2.me/submissions/a73703c1-a5ac-4f86-9743-f010fc2104e8

import Definitions.Def_GravityNonRenorm_Defs
import Mathlib

open GravityNonRenorm Filter Asymptotics

namespace GravityNonRenorm

theorem gnr_sphereArea_pos (k : ℕ) : 0 < sphereArea k := by
  unfold sphereArea
  have : 0 < Real.Gamma (((k : ℝ) + 1) / 2) := Real.Gamma_pos_of_pos (by positivity)
  positivity

theorem gnr_main (d : ℕ) (hd : 4 ≤ d) (G M : ℝ) (hG : 0 < G) (hM : 0 < M) :
    flatBHEntropy d G M =
      sphereArea (d - 2) / (4 * G) *
        (omega (d - 2) * G * M) ^ (((d : ℝ) - 2) / ((d : ℝ) - 3)) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 4 := ⟨d - 4, by omega⟩
  have e2 : n + 4 - 2 = n + 2 := by omega
  have e3 : n + 4 - 3 = n + 1 := by omega
  have hω : 0 < omega (n + 2) := by
    unfold omega
    have := gnr_sphereArea_pos (n + 2)
    have : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
    positivity
  set c := omega (n + 2) * G * M with hc
  have hc0 : 0 < c := by positivity
  set r0 : ℝ := c ^ (((n + 1 : ℕ) : ℝ)⁻¹) with hr0
  have hr0pos : 0 < r0 := by positivity
  have hr0pow : r0 ^ (n + 1) = c := Real.rpow_inv_natCast_pow hc0.le (by omega)
  have hset : {r : ℝ | 0 < r ∧ schwarzschildF (n + 4) G M r = 0} = {r0} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, schwarzschildF, e2, e3]
    constructor
    · rintro ⟨hr, hf⟩
      have hp : r ^ (n + 1) ≠ 0 := by positivity
      have h1 : c / r ^ (n + 1) = 1 := by rw [hc]; linarith
      have h2 : r ^ (n + 1) = c := ((div_eq_one_iff_eq hp).1 h1).symm
      rw [hr0, ← h2, Real.pow_rpow_inv_natCast hr.le (by omega)]
    · rintro rfl
      refine ⟨hr0pos, ?_⟩
      rw [← hc, hr0pow, div_self hc0.ne']
      ring
  unfold flatBHEntropy bekensteinHawkingEntropy flatHorizonRadius
  rw [hset, csSup_singleton, e2, ← hc]
  have hexp : r0 ^ (n + 2) = c ^ ((((n + 4 : ℕ) : ℝ) - 2) / (((n + 4 : ℕ) : ℝ) - 3)) := by
    rw [hr0, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
    congr 1
    push_cast
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    rw [show (n : ℝ) + 4 - 2 = n + 2 by ring, show (n : ℝ) + 4 - 3 = n + 1 by ring]
    field_simp
  rw [hexp]
  ring


open GravityNonRenorm in
theorem gnr_cft (d : ℕ) (hd : 2 ≤ d) (a b R : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hR : 0 < R) :
    (fun E : ℝ => cftEntropyOfEnergy d a b R E) =Θ[atTop]
      (fun E : ℝ => E ^ (((d : ℝ) - 1) / d)) := by
  set c : ℝ := b * R ^ (d - 1) with hc_def
  have hc : 0 < c := by positivity
  set x : ℝ := ((d : ℝ) - 1) / d with hx_def
  set K : ℝ := a * R ^ (d - 1) / c ^ x with hK_def
  have hK : K ≠ 0 := by
    have : 0 < c ^ x := Real.rpow_pos_of_pos hc x
    positivity
  have hexp : (1 / (d : ℝ)) * ((d - 1 : ℕ) : ℝ) = x := by
    rw [hx_def, Nat.cast_sub (by omega : 1 ≤ d)]
    push_cast
    ring
  have heq : (fun E : ℝ => cftEntropyOfEnergy d a b R E) =ᶠ[atTop]
      (fun E : ℝ => K * E ^ x) := by
    filter_upwards [eventually_gt_atTop 0] with E hE
    unfold cftEntropyOfEnergy
    rw [← hc_def, mul_pow, ← Real.rpow_mul_natCast (div_nonneg hE.le hc.le), hexp,
      Real.div_rpow hE.le hc.le, hK_def]
    field_simp
  exact heq.trans_isTheta ((isTheta_const_mul_left hK).2 (isTheta_refl _ _))



theorem gnr_flat (d : ℕ) (hd : 4 ≤ d) (G : ℝ) (hG : 0 < G) :
    (fun M : ℝ => flatBHEntropy d G M) =Θ[atTop]
      (fun M : ℝ => M ^ (((d : ℝ) - 2) / ((d : ℝ) - 3))) := by
  set p : ℝ := ((d : ℝ) - 2) / ((d : ℝ) - 3)
  have hω : 0 < omega (d - 2) := by
    unfold omega
    have := gnr_sphereArea_pos (d - 2)
    have : (0 : ℝ) < ((d - 2 : ℕ) : ℝ) := by
      have : 0 < d - 2 := by omega
      exact_mod_cast this
    positivity
  have hA := gnr_sphereArea_pos (d - 2)
  set K : ℝ := sphereArea (d - 2) / (4 * G) * (omega (d - 2) * G) ^ p
  have hK : K ≠ 0 := by
    have : 0 < (omega (d - 2) * G) ^ p := Real.rpow_pos_of_pos (by positivity) p
    positivity
  have heq : (fun M : ℝ => flatBHEntropy d G M) =ᶠ[atTop] (fun M : ℝ => K * M ^ p) := by
    filter_upwards [eventually_gt_atTop 0] with M hM
    rw [gnr_main d hd G M hG hM, Real.mul_rpow (by positivity) hM.le]
    ring
  exact heq.trans_isTheta ((isTheta_const_mul_left hK).2 (isTheta_refl _ _))

theorem gnr_exp_lt (d : ℕ) (hd : 4 ≤ d) :
    ((d : ℝ) - 1) / d < ((d : ℝ) - 2) / ((d : ℝ) - 3) := by
  have h4 : (4 : ℝ) ≤ d := by exact_mod_cast hd
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem gnr_thm (d : ℕ) (hd : 4 ≤ d) (G a b R : ℝ) (hG : 0 < G)
    (ha : 0 < a) (hb : 0 < b) (hR : 0 < R) :
    ¬ (fun M : ℝ => flatBHEntropy d G M) =Θ[atTop]
      (fun E : ℝ => cftEntropyOfEnergy d a b R E) := by
  intro h
  have h1 := gnr_flat d hd G hG
  have h2 := gnr_cft d (by omega) a b R ha hb hR
  have h3 := (h1.symm.trans h).trans h2
  have hlt := gnr_exp_lt d hd
  set p : ℝ := ((d : ℝ) - 2) / ((d : ℝ) - 3)
  set q : ℝ := ((d : ℝ) - 1) / d
  obtain ⟨C, hC⟩ := h3.1.bound
  have hT : Tendsto (fun x : ℝ => x ^ (p - q)) atTop atTop :=
    tendsto_rpow_atTop (sub_pos.2 hlt)
  obtain ⟨x, ⟨hx0, hxC⟩, hxb⟩ := (((eventually_gt_atTop 0).and
    (hT.eventually_gt_atTop C)).and hC).exists
  have hxp : 0 < x ^ p := Real.rpow_pos_of_pos hx0 _
  have hxq : 0 < x ^ q := Real.rpow_pos_of_pos hx0 _
  rw [Real.norm_of_nonneg hxq.le, Real.norm_of_nonneg hxp.le] at hxb
  have hsplit : x ^ p = x ^ (p - q) * x ^ q := by
    rw [← Real.rpow_add hx0]; ring_nf
  rw [hsplit] at hxb
  have : x ^ (p - q) ≤ C := le_of_mul_le_mul_right hxb hxq
  linarith

end GravityNonRenorm

theorem solution (d : ℕ) (hd : 4 ≤ d) (G a b R : ℝ) (hG : 0 < G)
    (ha : 0 < a) (hb : 0 < b) (hR : 0 < R) :
    ¬ (fun M : ℝ => GravityNonRenorm.flatBHEntropy d G M) =Θ[atTop]
      (fun E : ℝ => GravityNonRenorm.cftEntropyOfEnergy d a b R E) :=
  GravityNonRenorm.gnr_thm d hd G a b R hG ha hb hR
