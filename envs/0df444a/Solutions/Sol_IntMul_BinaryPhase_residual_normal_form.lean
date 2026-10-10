-- Prove2me | solution 1 for IntMul.BinaryPhase.residual_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T17:38:16.68781+00:00
-- url     : https://prove2.me/submissions/73e73bc3-eae6-4435-97e6-ee3d9190feaa

import Definitions.Def_IntMul_BinaryQuadraticPhase
import Theorems.Thm_IntMul_BinaryPhase_residual_gauss_interface
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic
open scoped BigOperators
open IntMul.BinaryPhase

namespace IntMul.TensorNormal

open IntMul.BinaryPhase

open scoped BigOperators

theorem sign_add (a b : ZMod 2) : sign (a + b) = sign a * sign b := by
  fin_cases a <;> fin_cases b
  · change (1 : ℂ) = 1 * 1
    norm_num
  · change (-1 : ℂ) = 1 * (-1)
    norm_num
  · change (-1 : ℂ) = (-1) * 1
    norm_num
  · change (1 : ℂ) = (-1) * (-1)
    norm_num


/-- The one-bit identity `H₀ = b S C S`, evaluated entrywise. -/
theorem one_bit_walsh (a b : ZMod 2) :
    sign (a * b) / 2 = ((1 - Complex.I) / 2) *
      (phase (liftBit a) : ℂ) * cEntry a b * (phase (liftBit b) : ℂ) := by
  fin_cases a <;> fin_cases b <;>
    norm_num [sign, liftBit, phase, cEntry, ZMod.val,
      Zsqrtd.sqrtd, GaussianInt.toComplex_def', Zsqrtd.re_mul, Zsqrtd.im_mul]
  · change (1 : ℂ) / 2 = (1 - Complex.I) / 2 * Complex.I ^ 0 * ((1 + Complex.I) / 2) * Complex.I ^ 0
    norm_num
    ring_nf
    simp [Complex.I_sq, pow_succ]
    ring
  · change (1 : ℂ) / 2 = (1 - Complex.I) / 2 * Complex.I ^ 0 * ((1 - Complex.I) / 2) * Complex.I ^ 1
    norm_num
    ring_nf
    simp [Complex.I_sq, pow_succ]
    ring
  · change (1 : ℂ) / 2 = (1 - Complex.I) / 2 * Complex.I ^ 1 * ((1 - Complex.I) / 2) * Complex.I ^ 0
    norm_num
    ring_nf
    simp [Complex.I_sq, pow_succ]
    ring
  · change (-1 : ℂ) / 2 = (1 - Complex.I) / 2 * Complex.I ^ 1 * ((1 + Complex.I) / 2) * Complex.I ^ 1
    norm_num
    ring_nf
    simp [Complex.I_sq, pow_succ]
    ring

theorem sign_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    sign (∑ i ∈ s, f i) = ∏ i ∈ s, sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sign]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, sign_add, ih]

/-- Tensoring the one-bit identity produces the scaled Walsh kernel in arbitrary
dimension, with one complex child and two diagonal fourth-root phases. -/
theorem tensor_walsh {ι : Type*} [Fintype ι] (x y : ι → ZMod 2) :
    sign (∑ i, x i * y i) / (2 : ℂ) ^ Fintype.card ι =
      ((1 - Complex.I) / 2) ^ Fintype.card ι *
        coordinatePhase x * tensorKernel x y * coordinatePhase y := by
  classical
  calc
    _ = ∏ i, sign (x i * y i) / (2 : ℂ) := by
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
      rw [sign_sum]
    _ = ∏ i, ((1 - Complex.I) / 2) *
        (phase (liftBit (x i)) : ℂ) * cEntry (x i) (y i) *
          (phase (liftBit (y i)) : ℂ) := by
      apply Finset.prod_congr rfl
      intro i _
      exact one_bit_walsh _ _
    _ = _ := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        coordinatePhase, tensorKernel]

theorem phase_fourth_root (a : ZMod 4) : (phase a : ℂ) ^ 4 = 1 := by
  fin_cases a <;> norm_num [phase, ZMod.val, Zsqrtd.sqrtd, pow_succ,
    GaussianInt.toComplex_def', Zsqrtd.re_mul, Zsqrtd.im_mul, Complex.I_sq]

theorem coordinate_phase_fourth_root {ι : Type*} [Fintype ι] (x : ι → ZMod 2) :
    coordinatePhase x ^ 4 = 1 := by
  classical
  simp only [coordinatePhase, ← Finset.prod_pow, phase_fourth_root, Finset.prod_const_one]

end IntMul.TensorNormal


namespace IntMul.BinaryPhase

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- Independent input and output binary address changes put any nondegenerate
bilinear character kernel in dot-product form. No orthonormal basis is needed. -/
theorem bilinear_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (b : Module.Basis ι (ZMod 2) V) (x y : V) :
    B x y = ∑ i, (B.dualBasis hB b).equivFun x i * b.equivFun y i := by
  classical
  change B x y = ∑ i, (B.dualBasis hB b).repr x i * b.repr y i
  simp only [LinearMap.BilinForm.dualBasis_repr_apply]
  conv_lhs => rw [← b.sum_repr y]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Every nondegenerate binary quadratic residual uses one tensor complex child,
two binary address changes, two diagonal fourth-root phases, and a scalar fourth
root. In particular, alternating residuals do not require extra recursive children. -/
theorem residual_normal_form [DecidableEq V] {ι : Type*} [Fintype ι]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (q : V → ZMod 4) (hq0 : q 0 = 0)
    (hpolar : ∀ z w, q (z + w) = q z + q w + twice (B z w))
    (b : Module.Basis ι (ZMod 2) V) :
    ∃ (eL eR : V ≃ₗ[ZMod 2] (ι → ZMod 2)) (ε : ℂ) (dL dR : V → ℂ),
      ε ^ 4 = 1 ∧ (∀ x, dL x ^ 4 = 1) ∧ (∀ y, dR y ^ 4 = 1) ∧
      ∀ x y,
        (∑ z : V, (phase (q z) : ℂ) * sign (B z (x + y))) /
          (2 : ℂ) ^ Fintype.card ι =
        ε * dL x * tensorKernel (eL x) (eR y) * dR y := by
  classical
  let eL := (B.dualBasis hB b).equivFun
  let eR := b.equivFun
  let S : ℂ := ∑ z : V, (phase (q z) : ℂ)
  let β : ℂ := (1 - Complex.I) / 2
  let dL : V → ℂ := fun x => (phase (q x) : ℂ)⁻¹ * coordinatePhase (eL x)
  let dR : V → ℂ := fun y => coordinatePhase (eR y) * (phase (q y) : ℂ)⁻¹
  refine ⟨eL, eR, S * β ^ Fintype.card ι, dL, dR, ?_, ?_, ?_, ?_⟩
  · have hcard : Fintype.card V = 2 ^ Fintype.card ι := by
      rw [Module.card_fintype b, ZMod.card]
    have hs : ((∑ z : V, phase (q z) : GaussianInt) : ℂ) = S := by
      exact map_sum GaussianInt.toComplex _ _
    rw [← hs]
    have hg := (IntMul.BinaryPhase.residual_gauss_interface B hB q hq0 hpolar).2.1
    rw [Module.finrank_eq_card_basis b] at hg
    exact hg
  · intro x
    dsimp only [dL]
    rw [mul_pow, inv_pow, IntMul.TensorNormal.phase_fourth_root, IntMul.TensorNormal.coordinate_phase_fourth_root]
    simp
  · intro y
    dsimp only [dR]
    rw [mul_pow, inv_pow, IntMul.TensorNormal.phase_fourth_root, IntMul.TensorNormal.coordinate_phase_fourth_root]
    simp
  · intro x y
    have hw := IntMul.TensorNormal.tensor_walsh (eL x) (eR y)
    have hc : B x y = ∑ i, eL x i * eR y i := bilinear_coordinates B hB b x y
    rw [← hc] at hw
    rw [(IntMul.BinaryPhase.residual_gauss_interface B hB q hq0 hpolar).2.2 x y]
    dsimp only [dL, dR]
    calc
      _ = S * (phase (q x) : ℂ)⁻¹ *
          (sign (B x y) / (2 : ℂ) ^ Fintype.card ι) * (phase (q y) : ℂ)⁻¹ := by
        dsimp only [S]
        ring
      _ = _ := by
        rw [hw]
        dsimp only [β]
        ring

end IntMul.BinaryPhase

theorem solution
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V] {ι : Type*} [Fintype ι]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (q : V → ZMod 4) (hq0 : q 0 = 0)
    (hpolar : ∀ z w, q (z + w) = q z + q w + twice (B z w))
    (b : Module.Basis ι (ZMod 2) V) :
    ∃ (eL eR : V ≃ₗ[ZMod 2] (ι → ZMod 2)) (ε : ℂ) (dL dR : V → ℂ),
      ε ^ 4 = 1 ∧ (∀ x, dL x ^ 4 = 1) ∧ (∀ y, dR y ^ 4 = 1) ∧
      ∀ x y,
        (∑ z : V, (phase (q z) : ℂ) * sign (B z (x + y))) /
          (2 : ℂ) ^ Fintype.card ι =
        ε * dL x * tensorKernel (eL x) (eR y) * dR y := by
  exact IntMul.BinaryPhase.residual_normal_form B hB q hq0 hpolar b

#print axioms solution
