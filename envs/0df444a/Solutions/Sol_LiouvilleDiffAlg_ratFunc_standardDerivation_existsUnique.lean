-- Prove2me | solution 1 for LiouvilleDiffAlg.ratFunc_standardDerivation_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T12:31:11.410912+00:00
-- url     : https://prove2.me/submissions/39032994-a07d-4a59-8175-eb0e161e488a

import Mathlib
import Definitions.Def_LiouvilleDiffAlg_RatFunc

open scoped Differential
open LiouvilleDiffAlg

attribute [local instance 2000] Ring.toIntAlgebra

private noncomputable def dualHom :
    Polynomial ℂ →+* TrivSqZeroExt (RatFunc ℂ) (RatFunc ℂ) where
  toFun p := TrivSqZeroExt.inl (algebraMap _ (RatFunc ℂ) p) +
    TrivSqZeroExt.inr (algebraMap _ (RatFunc ℂ) (Polynomial.derivative p))
  map_one' := by
    apply TrivSqZeroExt.ext <;>
      simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_one,
        Polynomial.derivative_one, map_zero, TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one,
        add_zero, zero_add]
  map_zero' := by
    apply TrivSqZeroExt.ext <;>
      simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_zero,
        Polynomial.derivative_zero, TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_zero,
        add_zero, zero_add]
  map_add' p q := by
    apply TrivSqZeroExt.ext <;>
      simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_add,
        Polynomial.derivative_add] <;> ring
  map_mul' p q := by
    apply TrivSqZeroExt.ext
    · simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, map_mul, add_zero]
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr,
        TrivSqZeroExt.snd_inr, Polynomial.derivative_mul, map_add, map_mul, smul_eq_mul,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, add_zero, zero_add]
      ring

private lemma dualHom_fst (p : Polynomial ℂ) : (dualHom p).fst = algebraMap _ (RatFunc ℂ) p := by simp [dualHom]

private lemma dualHom_snd (p : Polynomial ℂ) :
    (dualHom p).snd = algebraMap _ (RatFunc ℂ) (Polynomial.derivative p) := by
  simp only [dualHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add,
    TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]

private lemma dualHom_unit (y : nonZeroDivisors (Polynomial ℂ)) : IsUnit (dualHom y) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, dualHom_fst]
  refine isUnit_iff_ne_zero.2 ?_
  rw [map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)]
  exact nonZeroDivisors.coe_ne_zero y

private noncomputable def dualLift : RatFunc ℂ →+* TrivSqZeroExt (RatFunc ℂ) (RatFunc ℂ) :=
  IsLocalization.lift (M := nonZeroDivisors (Polynomial ℂ)) dualHom_unit

private lemma dualLift_algebraMap (p : Polynomial ℂ) :
    dualLift (algebraMap _ (RatFunc ℂ) p) = dualHom p :=
  IsLocalization.lift_eq _ _

private lemma dualLift_fst (x : RatFunc ℂ) : (dualLift x).fst = x := by
  have : ((TrivSqZeroExt.fstHom ℂ (RatFunc ℂ) (RatFunc ℂ)).toRingHom.comp dualLift) =
      RingHom.id (RatFunc ℂ) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial ℂ))
    refine RingHom.ext fun p => ?_
    simp only [RingHom.comp_apply, dualLift_algebraMap]
    exact dualHom_fst p
  exact congrArg (fun f => f x) this

set_option warn.classDefReducibility false in
private noncomputable def stdDiff : Differential (RatFunc ℂ) where
  deriv := Derivation.mk'
    { toFun := fun x => (dualLift x).snd
      map_add' := fun x y => by simp only [map_add, TrivSqZeroExt.snd_add]
      map_smul' := fun n x => by
        simp only [map_zsmul, TrivSqZeroExt.snd_smul, RingHom.id_apply] }
    (fun a b => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, map_mul, TrivSqZeroExt.snd_mul,
        dualLift_fst, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      ring)

private lemma key (e : Differential (RatFunc ℂ)) (he : @IsStandardDerivation e)
    (x : RatFunc ℂ) :
    e.deriv x * algebraMap _ (RatFunc ℂ) x.denom =
      algebraMap _ (RatFunc ℂ) (Polynomial.derivative x.num) -
        x * algebraMap _ (RatFunc ℂ) (Polynomial.derivative x.denom) := by
  have hden : algebraMap _ (RatFunc ℂ) x.denom ≠ 0 := by
    rw [map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)]
    exact x.denom_ne_zero
  have h0 : x * algebraMap _ (RatFunc ℂ) x.denom = algebraMap _ (RatFunc ℂ) x.num := by
    have := RatFunc.num_div_denom x
    rw [div_eq_iff hden] at this
    exact this.symm
  have h1 := congrArg e.deriv h0
  rw [Derivation.leibniz] at h1
  have h2 : e.deriv (algebraMap _ (RatFunc ℂ) x.num) =
      algebraMap _ (RatFunc ℂ) (Polynomial.derivative x.num) := he x.num
  have h3 : e.deriv (algebraMap _ (RatFunc ℂ) x.denom) =
      algebraMap _ (RatFunc ℂ) (Polynomial.derivative x.denom) := he x.denom
  rw [h2, h3] at h1
  simp only [smul_eq_mul] at h1
  linear_combination h1

theorem solution : ∃! d : Differential (RatFunc ℂ), @IsStandardDerivation d := by
  refine ⟨stdDiff, ?_, ?_⟩
  · intro p
    show (dualLift (algebraMap _ (RatFunc ℂ) p)).snd = _
    rw [dualLift_algebraMap, dualHom_snd]
  · intro d hd
    have hstd : @IsStandardDerivation stdDiff := by
      intro p
      show (dualLift (algebraMap _ (RatFunc ℂ) p)).snd = _
      rw [dualLift_algebraMap, dualHom_snd]
    apply Differential.ext
    apply Derivation.ext
    intro x
    have hden : algebraMap _ (RatFunc ℂ) x.denom ≠ 0 := by
      rw [map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)]
      exact x.denom_ne_zero
    have h1 := key d hd x
    have h2 := key stdDiff hstd x
    exact mul_right_cancel₀ hden (h1.trans h2.symm)
