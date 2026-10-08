-- Prove2me | solution 1 for MazurReduction.rational_residue_field_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T10:18:17.899051+00:00
-- url     : https://prove2.me/submissions/b04143e8-f72f-4370-bed4-09abd06db968

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Mathlib
open WithZero IsLocalRing

theorem solution (p : ℕ) [Fact p.Prime] :
    Nonempty (IsLocalRing.ResidueField (Rat.padicValuation p).valuationSubring ≃+* ZMod p) := by
  let v := Rat.padicValuation p
  let A := v.valuationSubring
  let F := ResidueField A
  have hpzero : (p : F) = 0 := by
    have hm : (p : A) ∈ maximalIdeal A := by
      apply v.mem_maximalIdeal_iff.mpr
      change Rat.padicValuation p (p : ℚ) < 1
      rw [Rat.padicValuation_self, ← exp_zero, exp_lt_exp]
      norm_num
    have hz := (residue_eq_zero_iff (p : A)).mpr hm
    simpa only [map_natCast] using hz
  letI : CharP F p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpzero
  let f : ZMod p →+* F := ZMod.castHom (dvd_refl p) F
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨a, rfl⟩ := residue_surjective (R := A) z
    have hden : ¬ p ∣ (a : ℚ).den := (Rat.padicValuation_le_one_iff).mp a.property
    have hd : ((a : ℚ).den : F) ≠ 0 := by
      exact fun hz => hden ((CharP.cast_eq_zero_iff F p _).mp hz)
    have hmul : a * ((a : ℚ).den : A) = ((a : ℚ).num : A) := by
      apply Subtype.ext
      change (a : ℚ) * ((a : ℚ).den : ℚ) = ((a : ℚ).num : ℚ)
      have hdq : ((a : ℚ).den : ℚ) ≠ 0 := by exact_mod_cast (a : ℚ).den_ne_zero
      exact (eq_div_iff hdq).mp (a : ℚ).num_div_den.symm
    have hr : residue A a = ((a : ℚ).num : F) / ((a : ℚ).den : F) := by
      apply (eq_div_iff hd).mpr
      simpa only [map_mul, map_natCast, map_intCast] using congrArg (residue A) hmul
    refine ⟨((a : ℚ).num : ZMod p) / ((a : ℚ).den : ZMod p), ?_⟩
    rw [map_div₀, map_intCast, map_natCast]
    exact hr.symm
  exact ⟨(RingEquiv.ofBijective f ⟨f.injective, hsurj⟩).symm⟩
