-- Prove2me | solution 1 for NoSignalPA.secure_of_long_key
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T21:50:50.835434+00:00
-- url     : https://prove2.me/submissions/5d000ab2-431d-4524-9013-47eead76880c

import Mathlib
import Definitions.Def_NoSignalPA_IsSecure
import Theorems.Thm_NoSignalPA_chsh_tensor_entry

open scoped ENNReal

namespace NoSignalPALongKeyAux

/-- `ofReal |s - c t| ≤ s + c t` for finite `s, t` and `c ≥ 0`. -/
lemma ofReal_abs_sub_le (s t : ℝ≥0∞) (hs : s ≠ ∞) (ht : t ≠ ∞) (c : ℝ) (hc : 0 ≤ c) :
    ENNReal.ofReal |s.toReal - c * t.toReal| ≤ s + ENNReal.ofReal c * t := by
  have h1 : |s.toReal - c * t.toReal| ≤ s.toReal + c * t.toReal := by
    have := ENNReal.toReal_nonneg (a := s)
    have := ENNReal.toReal_nonneg (a := t)
    rw [abs_le]
    constructor <;> nlinarith
  calc ENNReal.ofReal |s.toReal - c * t.toReal| ≤ ENNReal.ofReal (s.toReal + c * t.toReal) :=
        ENNReal.ofReal_le_ofReal h1
    _ = s + ENNReal.ofReal c * t := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (mul_nonneg hc ENNReal.toReal_nonneg),
          ENNReal.ofReal_toReal hs, ENNReal.ofReal_mul hc, ENNReal.ofReal_toReal ht]

/-- The total mass of a box at fixed inputs, summed in the order `a, b, e`. -/
lemma total_mass.{u} {Nr : ℕ} {Z E : Type u} (P : NoSignalPA.Box Nr Z E) (x y : NoSignalPA.Str Nr)
    (z : Z) : ∑ a, ∑ b, ∑' e, P x y z (a, b, e) = 1 := by
  have h := PMF.tsum_coe (P x y z)
  rw [ENNReal.tsum_prod (f := fun a be => P x y z (a, be)), tsum_fintype] at h
  rw [← h]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ENNReal.tsum_prod (f := fun b e => P x y z (a, b, e)), tsum_fintype]

lemma tsum_finset_sum {α ι : Type*} (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    ∑' e, ∑ i ∈ s, f i e = ∑ i ∈ s, ∑' e, f i e :=
  Summable.tsum_finsetSum fun _ _ => ENNReal.summable

lemma tsum_e_ne_top.{u} {Nr : ℕ} {Z E : Type u} (P : NoSignalPA.Box Nr Z E)
    (x y : NoSignalPA.Str Nr) (z : Z) (a b : NoSignalPA.Str Nr) :
    ∑' e, P x y z (a, b, e) ≠ ∞ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  rw [← PMF.tsum_coe (P x y z)]
  exact ENNReal.tsum_comp_le_tsum_of_injective (f := fun e : E => (a, b, e))
    (fun e e' h => by simpa using h) _

end NoSignalPALongKeyAux

open NoSignalPALongKeyAux in
theorem solution.{u} {Nr Ns : ℕ} (hN : (Nr : ℝ) + 2 ≤ Ns + Real.sqrt Nr)
    (h : NoSignalPA.Str Nr → NoSignalPA.Str Ns) : NoSignalPA.IsSecure.{u} h := by
  intro Z E P hNS y z₀
  classical
  set x0 : NoSignalPA.Str Nr := fun _ => false with hx0
  set c : ℝ := ((2 : ℝ) ^ Ns)⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  -- Eve's no-signalling: the `(a, b)`-marginal does not depend on `z`
  have hindep : ∀ z a b, ∑' e, P x0 y z (a, b, e) = ∑' e, P x0 y z₀ (a, b, e) :=
    fun z a b => hNS.2.2 x0 y z z₀ a b
  have hfin : ∀ z a b e, P x0 y z (a, b, e) ≠ ∞ := fun z a b e => PMF.apply_ne_top _ _
  ------------------------------------------------------------------
  -- Step A: the distance is at most `2`
  ------------------------------------------------------------------
  set q : NoSignalPA.Str Ns → ℝ≥0∞ := fun k =>
    ∑ a ∈ Finset.univ.filter (fun a => h a = k), ∑ b, ∑' e, P x0 y z₀ (a, b, e) with hq
  have hstep : ∀ k, (⨆ z : Z, ∑' e : E,
      ENNReal.ofReal |(NoSignalPA.keyEveMarg h P x0 y z k e).toReal
        - c * (NoSignalPA.eveMarg P x0 y z e).toReal|) ≤ q k + ENNReal.ofReal c := by
    intro k
    refine iSup_le fun z => ?_
    calc ∑' e : E, ENNReal.ofReal |(NoSignalPA.keyEveMarg h P x0 y z k e).toReal
          - c * (NoSignalPA.eveMarg P x0 y z e).toReal|
        ≤ ∑' e : E, (NoSignalPA.keyEveMarg h P x0 y z k e
            + ENNReal.ofReal c * NoSignalPA.eveMarg P x0 y z e) := by
          refine ENNReal.tsum_le_tsum fun e => ofReal_abs_sub_le _ _ ?_ ?_ c hc0
          · exact ENNReal.sum_ne_top.mpr fun a _ => ENNReal.sum_ne_top.mpr fun b _ => hfin z a b e
          · exact ENNReal.sum_ne_top.mpr fun a _ => ENNReal.sum_ne_top.mpr fun b _ => hfin z a b e
      _ = q k + ENNReal.ofReal c := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
          have hK : ∑' e, NoSignalPA.keyEveMarg h P x0 y z k e = q k := by
            simp only [NoSignalPA.keyEveMarg, hq]
            rw [tsum_finset_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [tsum_finset_sum]
            exact Finset.sum_congr rfl fun b _ => hindep z a b
          have hEv : ∑' e, NoSignalPA.eveMarg P x0 y z e = 1 := by
            simp only [NoSignalPA.eveMarg]
            rw [tsum_finset_sum]
            simp only [tsum_finset_sum]
            exact total_mass P x0 y z
          rw [hK, hEv, mul_one]
  have hLHS : ∑ k : NoSignalPA.Str Ns, (⨆ z : Z, ∑' e : E,
      ENNReal.ofReal |(NoSignalPA.keyEveMarg h P x0 y z k e).toReal
        - c * (NoSignalPA.eveMarg P x0 y z e).toReal|) ≤ 2 := by
    calc _ ≤ ∑ k : NoSignalPA.Str Ns, (q k + ENNReal.ofReal c) := Finset.sum_le_sum fun k _ => hstep k
      _ = 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
        have hq1 : ∑ k, q k = 1 := by
          simp only [hq]
          rw [Finset.sum_fiberwise Finset.univ h (fun a => ∑ b, ∑' e, P x0 y z₀ (a, b, e))]
          exact total_mass P x0 y z₀
        have hcard : (Fintype.card (NoSignalPA.Str Ns) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ Ns) := by
          rw [ENNReal.ofReal_pow (by norm_num)]
          simp [NoSignalPA.Str, Fintype.card_bool, Fintype.card_fin]
        rw [hq1, nsmul_eq_mul, hcard, ← ENNReal.ofReal_mul (by positivity), hc,
          mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one]
        norm_num
  ------------------------------------------------------------------
  -- Step B: the bound is at least `2`
  ------------------------------------------------------------------
  have hpair : (2 : ℝ) ^ (-(Nr : ℝ) / 2) ≤ NoSignalPA.pairing NoSignalPA.chshPow (NoSignalPA.abMarg P z₀) := by
    have hQnn : ∀ a b x y', 0 ≤ NoSignalPA.abMarg P z₀ a b x y' := fun _ _ _ _ => ENNReal.toReal_nonneg
    have hentry : ∀ a b x y' : NoSignalPA.Str Nr,
        (2 : ℝ) ^ (-(5 * (Nr : ℝ)) / 2) ≤ NoSignalPA.chshPow a b x y' := by
      intro a b x y'
      rw [NoSignalPA.chsh_tensor_entry]
      have : (1 : ℝ) ≤ 5 ^ NoSignalPA.ones (fun i => xor (xor (a i) (b i)) (x i && y' i)) :=
        one_le_pow₀ (by norm_num)
      have hp : (0 : ℝ) < (2 : ℝ) ^ (-(5 * (Nr : ℝ)) / 2) := by positivity
      nlinarith
    have hmass : ∀ x y' : NoSignalPA.Str Nr, ∑ a, ∑ b, NoSignalPA.abMarg P z₀ a b x y' = 1 := by
      intro x y'
      simp only [NoSignalPA.abMarg]
      have h1 : ∀ a, ∑ b, (∑' e, P x y' z₀ (a, b, e)).toReal =
          (∑ b, ∑' e, P x y' z₀ (a, b, e)).toReal := fun a =>
        (ENNReal.toReal_sum fun b _ => tsum_e_ne_top P x y' z₀ a b).symm
      simp only [h1]
      rw [← ENNReal.toReal_sum fun a _ => ENNReal.sum_ne_top.mpr fun b _ =>
        tsum_e_ne_top P x y' z₀ a b, total_mass P x y' z₀, ENNReal.toReal_one]
    have hcardStr : ((Fintype.card (NoSignalPA.Str Nr) : ℕ) : ℝ) = (2 : ℝ) ^ Nr := by
      simp [NoSignalPA.Str, Fintype.card_bool, Fintype.card_fin]
    have hre : ∑ a, ∑ b, ∑ x, ∑ y', NoSignalPA.abMarg P z₀ a b x y' =
        (2 : ℝ) ^ Nr * (2 : ℝ) ^ Nr := by
      calc ∑ a, ∑ b, ∑ x, ∑ y', NoSignalPA.abMarg P z₀ a b x y'
          = ∑ a, ∑ x, ∑ b, ∑ y', NoSignalPA.abMarg P z₀ a b x y' :=
            Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = ∑ a, ∑ x, ∑ y', ∑ b, NoSignalPA.abMarg P z₀ a b x y' :=
            Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = ∑ x, ∑ a, ∑ y', ∑ b, NoSignalPA.abMarg P z₀ a b x y' := Finset.sum_comm
        _ = ∑ x, ∑ y', ∑ a, ∑ b, NoSignalPA.abMarg P z₀ a b x y' :=
            Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = ∑ x : NoSignalPA.Str Nr, ∑ y' : NoSignalPA.Str Nr, (1 : ℝ) := by simp only [hmass]
        _ = (2 : ℝ) ^ Nr * (2 : ℝ) ^ Nr := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcardStr]
    calc (2 : ℝ) ^ (-(Nr : ℝ) / 2)
        = (2 : ℝ) ^ (-(5 * (Nr : ℝ)) / 2) * ((2 : ℝ) ^ Nr * (2 : ℝ) ^ Nr) := by
          rw [← pow_add, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1
          push_cast
          ring
      _ = ∑ a, ∑ b, ∑ x, ∑ y', (2 : ℝ) ^ (-(5 * (Nr : ℝ)) / 2) * NoSignalPA.abMarg P z₀ a b x y' := by
          simp only [← Finset.mul_sum]
          rw [hre]
      _ ≤ NoSignalPA.pairing NoSignalPA.chshPow (NoSignalPA.abMarg P z₀) := by
          unfold NoSignalPA.pairing
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
            Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y' _ => ?_
          exact mul_le_mul_of_nonneg_right (hentry a b x y') (hQnn a b x y')
  -- the factor `√(2^{Ns + √Nr}) ≥ 2^{(Nr + 2)/2}`
  have hsqrt : (2 : ℝ) ^ (((Nr : ℝ) + 2) / 2) ≤ Real.sqrt ((2 : ℝ) ^ ((Ns : ℝ) + Real.sqrt Nr)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hRHS : (2 : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ ((Ns : ℝ) + Real.sqrt Nr)) *
      NoSignalPA.pairing NoSignalPA.chshPow (NoSignalPA.abMarg P z₀) := by
    have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (-(Nr : ℝ) / 2) := by positivity
    have hs0 : (0 : ℝ) ≤ (2 : ℝ) ^ (((Nr : ℝ) + 2) / 2) := by positivity
    calc (2 : ℝ) = (2 : ℝ) ^ (((Nr : ℝ) + 2) / 2) * (2 : ℝ) ^ (-(Nr : ℝ) / 2) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          rw [show ((Nr : ℝ) + 2) / 2 + -(Nr : ℝ) / 2 = 1 by ring, Real.rpow_one]
      _ ≤ _ := mul_le_mul hsqrt hpair hp (Real.sqrt_nonneg _)
  calc _ ≤ (2 : ℝ≥0∞) := hLHS
    _ = ENNReal.ofReal 2 := by norm_num
    _ ≤ _ := ENNReal.ofReal_le_ofReal hRHS
