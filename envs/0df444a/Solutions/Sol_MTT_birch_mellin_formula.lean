-- Prove2me | solution 1 for MTT.birch_mellin_formula
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-05T22:43:51.209348+00:00
-- url     : https://prove2.me/submissions/c299c88e-54ce-422f-83a0-af34e766a04f

import Definitions.Def_MTT_Arithmetic
import Mathlib.NumberTheory.ModularForms.LFunction
import Mathlib.NumberTheory.ModularForms.Identities
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option maxRecDepth 2000
noncomputable section
open scoped BigOperators ModularForm
open MeasureTheory MatrixGroups Complex UpperHalfPlane
open MTT ModularForm
open ConjAct Pointwise

private lemma rational_translate_integrable
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (f : CuspForm (GammaOne N) (k : ℤ)) (r : ℚ) (j : ℕ) :
    IntegrableOn (fun t : ℝ =>
      f (ofComplex ((r : ℂ) + Complex.I * t)) * (t : ℂ)^j) (Set.Ioi 0) := by
  let : NeZero N := ⟨by omega⟩
  let g : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.upperRightHom r
  let gr : GL (Fin 2) ℝ := g.map (Rat.castHom ℝ)
  have hr : gr = Matrix.GeneralLinearGroup.upperRightHom (r : ℝ) := by
    ext i l
    fin_cases i <;> fin_cases l <;> simp [gr, g]
  let : (GammaOne N).IsArithmetic := by dsimp [GammaOne]; infer_instance
  let : (toConjAct gr⁻¹ • GammaOne N).IsArithmetic := by
    have hh := Subgroup.IsArithmetic.conj (GammaOne N) g⁻¹
    simpa [gr] using hh
  let F := CuspForm.translate f gr
  have hconv := ((CuspForm.isStrongFEPair (by omega : (0 : ℤ) < k) F).hasMellin
    ((j : ℂ)+1)).1
  unfold MellinConvergent at hconv
  have hval (t : ℝ) (ht : 0 < t) :
      F (ofComplex (Complex.I * t)) = f (ofComplex ((r : ℂ) + Complex.I * t)) := by
    change (⇑f ∣[(k : ℤ)] gr) _ = _
    rw [slash_def, hr]
    simp only [Matrix.GeneralLinearGroup.val_det_apply]
    simp [σ, denom, Matrix.GeneralLinearGroup.upperRightHom]
    congr 1
    ext
    simp [coe_smul, σ, num, denom, ofComplex_apply_of_im_pos, ht]
    ring
  apply hconv.congr_fun _ measurableSet_Ioi
  intro t ht
  simp only [ModularForm.weakFEPair, add_sub_cancel_right, Complex.cpow_natCast,
    smul_eq_mul, hval t ht]
  ring

private def verticalMoment (f : UpperHalfPlane → ℂ) (r : ℚ) (j : ℕ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), f (ofComplex ((r : ℂ) + Complex.I*t)) * (t : ℂ)^j

private lemma symbol_vertical (f : UpperHalfPlane → ℂ) (a m : ℚ) (hm : m ≠ 0) (j : ℕ) :
    modularSymbol f j a m = (2*Real.pi : ℂ) * ((m : ℂ)*Complex.I)^j *
      verticalMoment f (-a/m) j := by
  unfold modularSymbol modularIntegral verticalMoment
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have heq (t : ℝ) :
      ((((m : ℂ) • Polynomial.X + Polynomial.C (a : ℂ))^j).eval
        (((-a/m : ℚ) : ℂ) + Complex.I*t)) =
      ((m : ℂ)*Complex.I)^j * (t : ℂ)^j := by
    simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_smul,
      Polynomial.eval_X, Polynomial.eval_C, smul_eq_mul, Rat.cast_div, Rat.cast_neg]
    rw [← mul_pow]
    congr 1
    field_simp
    ring
  simp_rw [heq]
  rw [show (fun t : ℝ => f (ofComplex (((-a/m : ℚ) : ℂ) + Complex.I*t)) *
      (((m : ℂ)*Complex.I)^j * (t : ℂ)^j)) =
    (fun t : ℝ => ((m : ℂ)*Complex.I)^j *
      (f (ofComplex (((-a/m : ℚ) : ℂ) + Complex.I*t)) * (t : ℂ)^j)) by
        funext t; ring, integral_const_mul]
  ring

private lemma critical_vertical {N k m : ℕ} [NeZero m] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (f : CuspForm (GammaOne N) (k : ℤ))
    (χ : DirichletCharacter Qbar m) (j : ℕ) :
    criticalLValue ι f m χ j =
      (2*Real.pi : ℂ)^(j+1) / (j.factorial : ℂ) * (MTT.gaussSum ι m χ)⁻¹ *
      ∑ a : ZMod m, ι (χ a) * verticalMoment f ((a.val : ℚ)/m) j := by
  unfold criticalLValue inverseTwist
  have heq (t : ℝ) (ht : t ∈ Set.Ioi (0 : ℝ)) :
      (MTT.gaussSum ι m χ)⁻¹ * (∑ a : ZMod m, ι (χ a) *
        f (ofComplex (↑(ofComplex (Complex.I*t)) + (a.val : ℂ)/m))) * (t : ℂ)^j =
      (MTT.gaussSum ι m χ)⁻¹ * ∑ a : ZMod m, ι (χ a) *
        (f (ofComplex ((((a.val : ℚ)/m : ℚ) : ℂ) + Complex.I*t)) * (t : ℂ)^j) := by
    simp only [ofComplex_apply_of_im_pos (show 0 < (Complex.I*(t : ℂ)).im by simpa using ht), Rat.cast_div, Rat.cast_natCast,
      Finset.sum_mul, mul_assoc]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [add_comm (Complex.I * (t : ℂ))]
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul]
  rw [integral_finsetSum _ (fun a _ => (rational_translate_integrable hN hk f
    ((a.val : ℚ)/m) j).const_mul (ι (χ a)))]
  simp only [integral_const_mul, verticalMoment]
  ring

private lemma moment_periodic {N k : ℕ} (f : CuspForm (GammaOne N) (k : ℤ))
    (r : ℚ) (j : ℕ) : verticalMoment f (r+1) j = verticalMoment f r j := by
  have hp := SlashInvariantFormClass.periodic_comp_ofComplex f
    (show (1 : ℝ) ∈ (GammaOne N).strictPeriods by
      simp [GammaOne, CongruenceSubgroup.strictPeriods_Gamma1])
  unfold verticalMoment
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  apply congrArg (fun z : ℂ => z * (t : ℂ)^j)
  simpa [Function.comp_def, add_assoc, add_comm, add_left_comm] using
    hp ((r : ℂ) + Complex.I*t)

private lemma weighted_moment_neg {N k m : ℕ} [NeZero m]
    (ι : Qbar →+* ℂ) (f : CuspForm (GammaOne N) (k : ℤ))
    (χ : DirichletCharacter Qbar m) (j : ℕ) :
    (∑ a : ZMod m, ι (χ a) * verticalMoment f (-(a.val : ℚ)/m) j) =
      ι (χ (-1)) * ∑ a : ZMod m, ι (χ a) * verticalMoment f ((a.val : ℚ)/m) j := by
  have hn (a : ZMod m) : verticalMoment f (-((-a).val : ℚ)/m) j =
      verticalMoment f ((a.val : ℚ)/m) j := by
    by_cases ha : a = 0
    · simp [ha]
    · rw [ZMod.neg_val, if_neg ha]
      have hval : a.val ≤ m := (ZMod.val_lt a).le
      push_cast [Nat.cast_sub hval]
      have hm : (m : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne m
      have he : -((m : ℚ)-a.val)/m = (a.val : ℚ)/m - 1 := by field_simp; ring
      rw [he]
      simpa using (moment_periodic f ((a.val : ℚ)/m-1) j).symm
  calc
    _ = ∑ a : ZMod m, ι (χ (-a)) * verticalMoment f (-((-a).val : ℚ)/m) j :=
      (Equiv.sum_comp (Equiv.neg (ZMod m)) _).symm
    _ = ∑ a : ZMod m, ι (χ (-1)) *
        (ι (χ a) * verticalMoment f ((a.val : ℚ)/m) j) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hn, show -a = (-1 : ZMod m)*a by ring, map_mul, map_mul]
      ring
    _ = _ := (Finset.mul_sum ..).symm

private lemma primitive_comp {m : ℕ} [NeZero m] (ι : Qbar →+* ℂ)
    (χ : DirichletCharacter Qbar m) (hχ : χ.IsPrimitive) :
    DirichletCharacter.IsPrimitive (χ.ringHomComp ι) := by
  let ψ : DirichletCharacter ℂ m := χ.ringHomComp ι
  have hc := ψ.factorsThrough_conductor
  have hh : χ.FactorsThrough ψ.conductor := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hc.dvd]
    intro u hu
    have h := (DirichletCharacter.factorsThrough_iff_ker_unitsMap hc.dvd).mp hc hu
    rw [MonoidHom.mem_ker, Units.ext_iff] at h
    change ι (χ u) = 1 at h
    rw [MonoidHom.mem_ker, Units.ext_iff]
    change χ u = 1
    apply ι.injective
    simpa using h
  change ψ.conductor = m
  apply Nat.le_antisymm (Nat.le_of_dvd (NeZero.pos m) ψ.conductor_dvd_level)
  calc
    m = χ.conductor := hχ.symm
    _ ≤ ψ.conductor := Nat.sInf_le hh

private lemma gauss_bridge {m : ℕ} [NeZero m] (ι : Qbar →+* ℂ)
    (χ : DirichletCharacter Qbar m) :
    MTT.gaussSum ι m χ = _root_.gaussSum (χ.ringHomComp ι) ZMod.stdAddChar := by
  unfold MTT.gaussSum _root_.gaussSum
  apply Finset.sum_congr rfl
  intro a _
  simp [ZMod.stdAddChar_apply, ZMod.toCircle_apply]

private lemma gauss_product {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m)
    (hχ : χ.IsPrimitive) :
    _root_.gaussSum χ ZMod.stdAddChar * _root_.gaussSum χ⁻¹ ZMod.stdAddChar =
      χ (-1) * (m : ℂ) := by
  have heq : ZMod.dft (⇑χ) = _root_.gaussSum χ ZMod.stdAddChar •
      (fun a => χ⁻¹ (-a)) := by
    ext a
    simpa [mul_comm] using hχ.fourierTransform_eq_inv_mul_gaussSum a
  have h := congrFun (ZMod.dft_dft (⇑χ)) (1 : ZMod m)
  rw [heq, map_smul, ZMod.dft_comp_neg] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h
  have ht : ZMod.dft (⇑χ⁻¹) (-1) = _root_.gaussSum χ⁻¹ ZMod.stdAddChar := by
    simp [ZMod.dft_apply, _root_.gaussSum, mul_comm]
  rw [ht] at h
  simpa [mul_comm] using h

open MTT in
theorem solution
    {N k m : ℕ} [NeZero m] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (f : Eigenform N k ι)
    (χ : DirichletCharacter Qbar m) (hχ : χ.IsPrimitive)
    (j : ℕ) (_hj : j ≤ k - 2) :
    criticalLValue ι f.form m χ j =
      ((-2 * Real.pi * Complex.I) ^ j * MTT.gaussSum ι m χ⁻¹ /
        ((j.factorial : ℂ) * (m : ℂ) ^ (j + 1))) *
        ∑ a : ZMod m, ι (χ a) * modularSymbol f.form j a.val m := by
  have hm : (m : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hc : ι (χ (-1))^2 = 1 := by
    rw [← map_pow, ← map_pow]
    norm_num
  have hcne : ι (χ (-1)) ≠ 0 := by intro h; simp [h] at hc
  have hg : MTT.gaussSum ι m χ * MTT.gaussSum ι m χ⁻¹ = ι (χ (-1)) * m := by
    have h := gauss_product (χ.ringHomComp ι) (primitive_comp ι χ hχ)
    simpa [gauss_bridge, MulChar.ringHomComp_inv] using h
  have hg0 : MTT.gaussSum ι m χ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hg
    exact (mul_ne_zero hcne hm') hg.symm
  have hfac : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  rw [critical_vertical hN hk]
  simp_rw [symbol_vertical _ _ _ hm, Rat.cast_natCast]
  have hsum : (∑ a : ZMod m, ι (χ a) *
      ((2*Real.pi : ℂ) * ((m : ℂ)*Complex.I)^j *
        verticalMoment f.form (-(a.val : ℚ)/m) j)) =
      ((2*Real.pi : ℂ) * ((m : ℂ)*Complex.I)^j) *
        (ι (χ (-1)) * ∑ a : ZMod m, ι (χ a) *
          verticalMoment f.form ((a.val : ℚ)/m) j) := by
    rw [← weighted_moment_neg ι f.form χ j, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hsum]
  have hi : (-2 * (Real.pi : ℂ) * Complex.I)^j * ((m : ℂ)*Complex.I)^j =
      (2*(Real.pi : ℂ))^j * (m : ℂ)^j := by
    rw [← mul_pow, ← mul_pow]
    congr 1
    linear_combination (-2*(Real.pi : ℂ)*(m : ℂ)) * Complex.I_sq
  field_simp
  have hgc : MTT.gaussSum ι m χ * MTT.gaussSum ι m χ⁻¹ * ι (χ (-1)) = m := by
    rw [hg]
    calc
      (ι (χ (-1)) * (m : ℂ)) * ι (χ (-1)) = ι (χ (-1))^2 * m := by ring
      _ = m := by rw [hc, one_mul]
  have hi' : (-(2 * (Real.pi : ℂ) * Complex.I))^j * (Complex.I * (m : ℂ))^j =
      (2*(Real.pi : ℂ))^j * (m : ℂ)^j := by
    convert hi using 1 <;> congr 1 <;> ring
  generalize (∑ x : ZMod m, ι (χ x) * verticalMoment f.form ((x.val : ℚ)/m) j) = S
  calc
    _ = (2*(Real.pi : ℂ))^j * (m : ℂ)^j * m * (2*Real.pi) * S := by
      rw [pow_succ, pow_succ]; ring
    _ = ((-(2 * (Real.pi : ℂ) * Complex.I))^j * (Complex.I * (m : ℂ))^j) *
        (MTT.gaussSum ι m χ * MTT.gaussSum ι m χ⁻¹ * ι (χ (-1))) * (2*Real.pi) * S := by
      rw [hi', hgc]
    _ = _ := by ring
