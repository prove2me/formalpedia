-- Prove2me | solution 1 for HorizontalPadicL.even_algebraicSymbol_sum_ne_zero_iff_modularSymbol_sum_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T14:30:09.586337+00:00
-- url     : https://prove2.me/submissions/5d4bd299-de41-49e2-9fcb-e3815c9baddb

import Definitions.Def_KN_SeededInverseThetaSystemV2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

private theorem modularSymbol_add_modulus
    {N k : ℕ} (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (j : ℕ) (a m : ℚ) (hm : m ≠ 0) :
    MTT.modularSymbol f j (a + m) m = MTT.modularSymbol f j a m := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hp := SlashInvariantFormClass.periodic_comp_ofComplex f
    (show (1 : ℝ) ∈ (MTT.GammaOne N).strictPeriods by
      simp [MTT.GammaOne, CongruenceSubgroup.strictPeriods_Gamma1])
  unfold MTT.modularSymbol MTT.modularIntegral
  apply congrArg (fun z : ℂ => (2 * Real.pi : ℂ) * z)
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t _
  have harg : (-(a + m) / m : ℂ) + Complex.I * t + 1 =
      (-a / m : ℂ) + Complex.I * t := by
    field_simp [hmC]
    ring
  have hf :
      f (UpperHalfPlane.ofComplex ((-(a + m) / m : ℚ) + Complex.I * t)) =
      f (UpperHalfPlane.ofComplex ((-a / m : ℚ) + Complex.I * t)) := by
    have h := hp ((-(a + m) / m : ℂ) + Complex.I * t)
    change f (UpperHalfPlane.ofComplex
      ((-(a + m) / m : ℂ) + Complex.I * t + 1)) =
      f (UpperHalfPlane.ofComplex ((-(a + m) / m : ℂ) + Complex.I * t)) at h
    rw [harg] at h
    push_cast at h ⊢
    exact h.symm
  dsimp only
  rw [hf]
  congr 1
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_smul,
    Polynomial.eval_X, Polynomial.eval_C]
  push_cast
  congr 1
  linear_combination (m : ℂ) * harg

private theorem modularSymbol_neg_val
    {N k n : ℕ} [NeZero n]
    (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (j : ℕ) (a : ZMod n) :
    MTT.modularSymbol f j (-(a.val : ℚ)) n =
      MTT.modularSymbol f j (-a).val n := by
  by_cases ha : a = 0
  · subst a
    simp
  · let _ : NeZero a := ⟨ha⟩
    have hperiod := (modularSymbol_add_modulus f j (-(a.val : ℚ)) n
      (by exact_mod_cast NeZero.ne n)).symm
    rw [ZMod.val_neg_of_ne_zero]
    calc
      MTT.modularSymbol f j (-(a.val : ℚ)) n =
          MTT.modularSymbol f j (-(a.val : ℚ) + n) n := hperiod
      _ = MTT.modularSymbol f j (n - a.val : ℕ) n := by
        congr 2
        rw [Nat.cast_sub (Nat.le_of_lt (ZMod.val_lt a))]
        ring

private theorem even_character_apply_neg
    {n : ℕ} [NeZero n] (θ : DirichletCharacter MTT.Qbar n)
    (hθeven : θ (-1) = 1) (a : ZMod n) :
    θ (-a) = θ a := by
  rw [show -a = (-1) * a by ring, map_mul, hθeven, one_mul]

private theorem even_character_reflected_sum
    {n : ℕ} [NeZero n] (ι : MTT.Qbar →+* ℂ)
    (θ : DirichletCharacter MTT.Qbar n) (hθeven : θ (-1) = 1)
    (F : ZMod n → ℂ) :
    (∑ a : ZMod n, ι (θ a) * F (-a)) =
      ∑ a : ZMod n, ι (θ a) * F a := by
  calc
    (∑ a : ZMod n, ι (θ a) * F (-a)) =
        ∑ a : ZMod n, ι (θ (-a)) * F (-a) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [even_character_apply_neg θ hθeven]
    _ = ∑ a : ZMod n, ι (θ a) * F a :=
      Equiv.sum_comp (Equiv.neg (ZMod n)) (fun a => ι (θ a) * F a)

theorem _root_.solution
    {N k : ℕ} {ι : MTT.Qbar →+* ℂ}
    (hk : 2 ≤ k) (f : MTT.Eigenform N k ι)
    (P : MTT.Periods k ι f.form)
    (θ : DirichletCharacterWithLevel) (hθeven : θ.2 (-1) = 1)
    (s : Bool) (hs : (MTT.sign s : ℤ) = (-1 : ℤ) ^ (k / 2 - 1))
    (hcomparison : ∀ s j a m, j ≤ k - 2 → m ≠ 0 →
      ι (MTT.algebraicSymbol P s j a m) * P.omega s =
        signedModularSymbol f.form s j a m) :
    letI : NeZero θ.1.1 := ⟨Nat.ne_of_gt θ.1.2⟩
    ((∑ a : ZMod θ.1.1,
        θ.2 a * MTT.algebraicSymbol P s (k / 2 - 1) a.val θ.1.1) ≠ 0 ↔
      (∑ a : ZMod θ.1.1,
        ι (θ.2 a) * MTT.modularSymbol f.form
          (k / 2 - 1) a.val θ.1.1) ≠ 0) := by
  let _ : NeZero θ.1.1 := ⟨Nat.ne_of_gt θ.1.2⟩
  let j := k / 2 - 1
  have hj : j ≤ k - 2 := by omega
  have hn : (θ.1.1 : ℚ) ≠ 0 := by exact_mod_cast θ.1.2.ne'
  let A : MTT.Qbar := ∑ a : ZMod θ.1.1,
    θ.2 a * MTT.algebraicSymbol P s j a.val θ.1.1
  let S : ℂ := ∑ a : ZMod θ.1.1,
    ι (θ.2 a) * MTT.modularSymbol f.form j a.val θ.1.1
  let Ssigned : ℂ := ∑ a : ZMod θ.1.1,
    ι (θ.2 a) * signedModularSymbol f.form s j a.val θ.1.1
  have hperiod : ι A * P.omega s = Ssigned := by
    dsimp only [A, Ssigned]
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [map_mul]
    rw [mul_assoc, hcomparison s j a.val θ.1.1 hj hn]
  have hsC : (MTT.sign s : ℂ) = (-1 : ℂ) ^ j := by
    exact_mod_cast hs
  have hsign : (MTT.sign s : ℂ) * (-1 : ℂ) ^ j = 1 := by
    rw [hsC, ← pow_add]
    exact Even.neg_one_pow ⟨j, by omega⟩
  have hreflect :
      (∑ a : ZMod θ.1.1,
        ι (θ.2 a) * MTT.modularSymbol f.form j (-a).val θ.1.1) = S := by
    simpa only [S] using even_character_reflected_sum ι θ.2 hθeven
      (fun a => MTT.modularSymbol f.form j a.val θ.1.1)
  have hnegative :
      (∑ a : ZMod θ.1.1,
        ι (θ.2 a) * MTT.modularSymbol f.form j (-(a.val : ℚ)) θ.1.1) = S := by
    calc
      _ = ∑ a : ZMod θ.1.1,
          ι (θ.2 a) * MTT.modularSymbol f.form j (-a).val θ.1.1 := by
        apply Finset.sum_congr rfl
        intro a _
        rw [modularSymbol_neg_val]
      _ = S := hreflect
  have hsigned : Ssigned = S := by
    let T : ℂ := ∑ a : ZMod θ.1.1,
      ι (θ.2 a) * MTT.modularSymbol f.form j (-(a.val : ℚ)) θ.1.1
    have hexpand : Ssigned = (S +
        ((MTT.sign s : ℂ) * (-1 : ℂ) ^ j) * T) / 2 := by
      dsimp only [Ssigned, S, T]
      calc
        (∑ a : ZMod θ.1.1,
          ι (θ.2 a) * signedModularSymbol f.form s j a.val θ.1.1) =
            ∑ a : ZMod θ.1.1,
              (ι (θ.2 a) * MTT.modularSymbol f.form j a.val θ.1.1 +
                ((MTT.sign s : ℂ) * (-1 : ℂ) ^ j) *
                  (ι (θ.2 a) * MTT.modularSymbol f.form j
                    (-(a.val : ℚ)) θ.1.1)) / 2 := by
          apply Finset.sum_congr rfl
          intro a _
          unfold signedModularSymbol
          ring
        _ = (∑ a : ZMod θ.1.1,
              (ι (θ.2 a) * MTT.modularSymbol f.form j a.val θ.1.1 +
                ((MTT.sign s : ℂ) * (-1 : ℂ) ^ j) *
                  (ι (θ.2 a) * MTT.modularSymbol f.form j
                    (-(a.val : ℚ)) θ.1.1))) / 2 := by
          rw [Finset.sum_div]
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [hexpand, show T = S by exact hnegative, hsign, one_mul]
    ring
  change A ≠ 0 ↔ S ≠ 0
  rw [← hsigned, ← hperiod]
  constructor
  · intro hA
    exact mul_ne_zero ((map_ne_zero_iff ι ι.injective).2 hA) (P.omega_ne s)
  · intro hprod hA
    apply hprod
    rw [hA, map_zero, zero_mul]

end HorizontalPadicL
