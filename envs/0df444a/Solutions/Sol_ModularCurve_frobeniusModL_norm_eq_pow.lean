-- Prove2me | solution 1 for ModularCurve.frobeniusModL_norm_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/7d4afdec-e19e-5194-8c8f-8ba9c8c9eff8

import Mathlib
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_finrankAlong_frobeniusModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_frobeniusModL_norm_eq_pow
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open Polynomial IntermediateField ModularCurve AlgebraicCurve

namespace P2MM2A

variable (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

abbrev FF : Type _ := modularFunctionFieldFullC K N

omit [IsAlgClosed K] [Fact ℓ.Prime] in
theorem charP_FF : CharP (FF K N) ℓ :=
  charP_of_injective_algebraMap (algebraMap K (modularFunctionFieldFullC K N)).injective ℓ

abbrev PP : IntermediateField K (FF K N) := (frobeniusModL K N ℓ).fieldRange

omit [IsAlgClosed K] in

theorem pow_mem_PP (f : FF K N) : f ^ ℓ ∈ PP K N ℓ := by
  obtain ⟨y, hy⟩ := exists_frobeniusModL_eq_pow K N ℓ f
  exact AlgHom.mem_fieldRange.mpr ⟨y, hy⟩

def isoPP : FF K N ≃+* PP K N ℓ :=
  RingEquiv.ofBijective
    ((frobeniusModL K N ℓ).toRingHom.codRestrict (PP K N ℓ).toSubring
      fun x => AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)
    ⟨fun x y h => frobeniusModL_injective K N ℓ (congrArg Subtype.val h),
     fun ⟨y, hy⟩ => by
       obtain ⟨x, rfl⟩ := AlgHom.mem_fieldRange.mp hy
       exact ⟨x, rfl⟩⟩

@[scoped simp] theorem coe_isoPP (x : FF K N) : (isoPP K N ℓ x : FF K N) = frobeniusModL K N ℓ x := rfl

theorem isoPP_compat :
    (algebraMap (PP K N ℓ) (FF K N)).comp (isoPP K N ℓ).toRingHom =
      (RingEquiv.refl (FF K N)).toRingHom.comp
        (@algebraMap (FF K N) (FF K N) _ _ (algebraAlong (frobeniusModL K N ℓ))) :=
  RingHom.ext fun _ => rfl

theorem finrank_PP : Module.finrank (PP K N ℓ) (FF K N) = ℓ := by
  have h := @Algebra.finrank_eq_of_equiv_equiv (FF K N) (FF K N) _ _ (algebraAlong (frobeniusModL K N ℓ))
    (PP K N ℓ) (FF K N) _ _ _ (isoPP K N ℓ) (RingEquiv.refl _) (isoPP_compat K N ℓ)

  have h2 : finrankAlong K (frobeniusModL K N ℓ) = ℓ := finrankAlong_frobeniusModL K N
  exact h.symm.trans h2

scoped instance finite_PP : Module.Finite (PP K N ℓ) (FF K N) :=
  Module.finite_of_finrank_pos (by rw [finrank_PP]; exact (Fact.out : ℓ.Prime).pos)

set_option maxHeartbeats 3200000 in

theorem minpoly_PP_of_not_mem {f : FF K N} (hf : f ∉ PP K N ℓ) :
    minpoly (PP K N ℓ) f = X ^ ℓ - Polynomial.C (⟨f ^ ℓ, pow_mem_PP K N ℓ f⟩ : PP K N ℓ) := by
  haveI := charP_FF K N ℓ
  have hℓ : ℓ.Prime := Fact.out
  symm
  refine minpoly.eq_of_irreducible_of_monic ?_ ?_ (monic_X_pow_sub_C _ hℓ.ne_zero)
  · refine X_pow_sub_C_irreducible_of_prime hℓ fun b hb => ?_
    apply hf
    have hb' : (b : FF K N) ^ ℓ = f ^ ℓ := by
      have h := congrArg Subtype.val hb
      simpa using h
    have : (b : FF K N) = f := by
      have h := sub_pow_char (b : FF K N) f (p := ℓ)
      rw [hb', sub_self] at h
      exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero h.symm.symm)
    rw [← this]; exact b.2
  · simp

set_option maxHeartbeats 6400000 in

theorem coe_norm_PP (f : FF K N) : ((Algebra.norm (PP K N ℓ) f : PP K N ℓ) : FF K N) = f ^ ℓ := by
  haveI := charP_FF K N ℓ
  haveI : CharP (PP K N ℓ) ℓ := IntermediateField.charP _ ℓ
  have hℓ : ℓ.Prime := Fact.out
  by_cases hf : f ∈ PP K N ℓ
  · have hfp : algebraMap (PP K N ℓ) (FF K N) ⟨f, hf⟩ = f := IntermediateField.algebraMap_apply _ _
    have h := Algebra.norm_algebraMap (S := FF K N) (⟨f, hf⟩ : PP K N ℓ)
    rw [hfp, finrank_PP] at h
    rw [h]
    exact SubmonoidClass.coe_pow _ _
  · have hint : IsIntegral (PP K N ℓ) f := IsIntegral.of_finite _ f
    have hdeg : (minpoly (PP K N ℓ) f).natDegree = ℓ := by
      rw [minpoly_PP_of_not_mem K N ℓ hf, natDegree_X_pow_sub_C]
    have h1 : Module.finrank (PP K N ℓ) (PP K N ℓ)⟮f⟯ = ℓ := by
      rw [adjoin.finrank hint, hdeg]
    have htop : (PP K N ℓ)⟮f⟯ = ⊤ :=
      IntermediateField.eq_of_le_of_finrank_eq le_top (by rw [h1, finrank_top', finrank_PP])
    have h2 : Module.finrank (PP K N ℓ)⟮f⟯ (FF K N) = 1 := finrank_eq_one_iff_eq_top.mpr htop
    rw [Algebra.norm_eq_norm_adjoin, h2, pow_one]
    have hpb := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (adjoin.powerBasis hint)
    have hgen : (adjoin.powerBasis hint).gen = AdjoinSimple.gen (PP K N ℓ) f := adjoin.powerBasis_gen hint
    have hdim : (adjoin.powerBasis hint).dim = ℓ := by rw [adjoin.powerBasis_dim, hdeg]
    have hmin : minpoly (PP K N ℓ) (AdjoinSimple.gen (PP K N ℓ) f) = minpoly (PP K N ℓ) f := minpoly_gen _ f
    rw [hgen, hdim, hmin, minpoly_PP_of_not_mem K N ℓ hf] at hpb
    rw [hpb, neg_one_pow_char, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C_zero,
      if_neg (Ne.symm hℓ.ne_zero), zero_sub, neg_mul_neg, one_mul]

set_option maxHeartbeats 3200000 in

theorem frobeniusModL_normAlong (f : FF K N) :
    frobeniusModL K N ℓ (@Algebra.norm (FF K N) (FF K N) _ _ (algebraAlong (frobeniusModL K N ℓ)) f) =
      f ^ ℓ := by
  have h := @Algebra.norm_eq_of_equiv_equiv (FF K N) (FF K N) (PP K N ℓ) (FF K N) _ _ _ _
    (algebraAlong (frobeniusModL K N ℓ)) _ (isoPP K N ℓ) (RingEquiv.refl _) (isoPP_compat K N ℓ) f
  rw [h]
  change ((isoPP K N ℓ) ((isoPP K N ℓ).symm _) : FF K N) = f ^ ℓ
  rw [RingEquiv.apply_symm_apply]
  exact coe_norm_PP K N ℓ f

end P2MM2A
p2m_reactivate "P2MW.S_ModularCurve_frobeniusModL_norm_eq_pow.P2MM2A"

end
p2m_reactivate "P2MW.S_ModularCurve_frobeniusModL_norm_eq_pow.P2MM2A"

open ModularCurve AlgebraicCurve in

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (N : ℕ) [NeZero N]
    (hfin : AlgebraicCurve.FiniteAlong K (frobeniusModL K N ℓ))
    (g : modularFunctionFieldFullC K N) :
    frobeniusModL K N ℓ
        (letI := AlgebraicCurve.algebraAlong (frobeniusModL K N ℓ)
         Algebra.norm (↥(modularFunctionFieldFullC K N)) g) = g ^ ℓ :=
  P2MM2A.frobeniusModL_normAlong K N ℓ g

end S_ModularCurve_frobeniusModL_norm_eq_pow
end P2MW
export P2MW.S_ModularCurve_frobeniusModL_norm_eq_pow (solution)
