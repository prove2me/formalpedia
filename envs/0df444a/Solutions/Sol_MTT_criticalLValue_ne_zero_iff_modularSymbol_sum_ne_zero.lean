-- Prove2me | solution 1 for MTT.criticalLValue_ne_zero_iff_modularSymbol_sum_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-23T06:57:06.81326+00:00
-- url     : https://prove2.me/submissions/57bb9e71-e0d7-4bc4-869c-5a93b9f71c51

import Theorems.Thm_MTT_birch_mellin_formula
import Mathlib.Analysis.Fourier.ZMod

set_option autoImplicit false
noncomputable section
open scoped BigOperators

private lemma primitive_comp {m : ℕ} [NeZero m] (ι : MTT.Qbar →+* ℂ)
    (χ : DirichletCharacter MTT.Qbar m) (hχ : χ.IsPrimitive) :
    DirichletCharacter.IsPrimitive (χ.ringHomComp ι) := by
  let ψ : DirichletCharacter ℂ m := χ.ringHomComp ι
  have hc := ψ.factorsThrough_conductor
  have hh : χ.FactorsThrough ψ.conductor := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hc.dvd]
    intro u hu
    have h :=
      (DirichletCharacter.factorsThrough_iff_ker_unitsMap hc.dvd).mp hc hu
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

private lemma gauss_bridge {m : ℕ} [NeZero m] (ι : MTT.Qbar →+* ℂ)
    (χ : DirichletCharacter MTT.Qbar m) :
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
  have ht : ZMod.dft (⇑χ⁻¹) (-1) =
      _root_.gaussSum χ⁻¹ ZMod.stdAddChar := by
    simp [ZMod.dft_apply, _root_.gaussSum, mul_comm]
  rw [ht] at h
  simpa [mul_comm] using h

private lemma gauss_ne_zero {m : ℕ} [NeZero m] (ι : MTT.Qbar →+* ℂ)
    (χ : DirichletCharacter MTT.Qbar m) (hχ : χ.IsPrimitive) :
    MTT.gaussSum ι m χ⁻¹ ≠ 0 := by
  have hg := gauss_product (χ.ringHomComp ι)
    (by
      exact (primitive_comp ι χ hχ))
  have hc : ι (χ (-1)) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow]
    norm_num
  have hcne : ι (χ (-1)) ≠ 0 := by
    intro h
    simp [h] at hc
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  intro h
  have h' : _root_.gaussSum (χ.ringHomComp ι)⁻¹ ZMod.stdAddChar = 0 := by
    simpa [gauss_bridge, MulChar.ringHomComp_inv] using h
  rw [h', mul_zero] at hg
  exact (mul_ne_zero hcne hm) hg.symm

open MTT in
theorem _root_.solution
    {N k m : ℕ} [NeZero m] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (f : Eigenform N k ι)
    (χ : DirichletCharacter Qbar m) (hχ : χ.IsPrimitive)
    (j : ℕ) (hj : j ≤ k - 2) :
    criticalLValue ι f.form m χ j ≠ 0 ↔
      (∑ a : ZMod m, ι (χ a) * modularSymbol f.form j a.val m) ≠ 0 := by
  rw [MTT.birch_mellin_formula hN hk ι f χ hχ j hj]
  apply mul_ne_zero_iff_left
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hbase : (-2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr htwo) hpi) hI
  have hfac : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  exact div_ne_zero
    (mul_ne_zero (pow_ne_zero _ hbase) (gauss_ne_zero ι χ hχ))
    (mul_ne_zero hfac (pow_ne_zero _ hm))
