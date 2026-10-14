-- Prove2me | solution 1 for MTT.character_integral_of_disk_moments
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T04:50:48.644693+00:00
-- url     : https://prove2.me/submissions/b7ef57c2-a49a-497c-9279-da50a137452e

import Definitions.Def_MTT_Measures
import Mathlib.RingTheory.Coprime.Lemmas

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MTT

theorem solution {p N k : ℕ} [Fact p.Prime]
    {ι : Qbar →+* ℂ} (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (s : Bool) (μ : UnitMeasure p)
    (hμ : RealizesMoments f ιp P α s μ)
    (n : ℕ) (hn : 0 < n) (χ : DirichletCharacter Qbar (p ^ n))
    (j : ℕ) (hj : j ≤ k - 2) :
    ∃ g : C((ℤ_[p])ˣ, ℂ_[p]),
      (∀ x, g x = specialFunction ιp n χ j x) ∧
      μ g = ∑ a : (ZMod (p ^ n))ˣ,
        ιp (χ a) * diskMoment f ιp P α s j n ((a : ZMod (p ^ n)).val : ℤ) := by
  classical
  have coprime (a : (ZMod (p ^ n))ˣ) :
      IsCoprime (((a : ZMod (p ^ n)).val : ℕ) : ℤ) (p : ℤ) :=
    ((Nat.coprime_pow_right_iff hn _ _).mp (ZMod.val_coe_unit_coprime a)).isCoprime
  choose g hg hmg using fun a : (ZMod (p ^ n))ˣ =>
    hμ n hn ((a : ZMod (p ^ n)).val : ℤ) (coprime a) j hj
  refine ⟨∑ a : (ZMod (p ^ n))ˣ, ιp (χ a) • g a, ?_, ?_⟩
  · intro x
    let b : (ZMod (p ^ n))ˣ := Units.map (PadicInt.toZModPow n).toMonoidHom x
    simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul, hg,
      diskFunction, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [Finset.sum_eq_single b]
    · simp [b, specialFunction]
    · intro a _ hab
      have hne : PadicInt.toZModPow n x.val ≠ (a : ZMod (p ^ n)) := by
        intro h
        apply hab
        apply Units.ext
        exact h.symm
      simp [hne]
    · simp
  · simp only [map_sum, map_smul, smul_eq_mul, hmg]
