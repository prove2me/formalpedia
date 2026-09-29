-- Prove2me | solution 1 for ModularCurve.isCurveOver_modularFunctionFieldBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/26e6e141-f721-5372-8792-f19f2cbb2ed1

import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull_unconditional
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin_pair
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Theorems.Thm_ModularCurve_deg_ne_zero_modularFunctionFieldC
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_isIntegral_jqNModC_all
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Theorems.Thm_KaehlerDifferential_span_D_eq_top_of_transcendental
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.CharP.Algebra
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isCurveOver_modularFunctionFieldBar
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

open IntermediateField

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place IsCurveOver"
p2m_open "AlgebraicCurve"

namespace R0

private theorem kaehler_free_rank_one (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x) [Algebra.IsSeparable K⟮x⟯ F] :
    Module.Free F (KaehlerDifferential K F) ∧ Module.finrank F (KaehlerDifferential K F) = 1 := by
  refine ⟨inferInstance, ?_⟩
  have h1 := finrank_span_singleton (K := F) (KaehlerDifferential.D_ne_zero_of_transcendental K x hx)
  rwa [KaehlerDifferential.span_D_eq_top_of_transcendental K x hx, finrank_top] at h1

section Adjoin

variable (K : Type*) [Field K] {LF : Type*} [Field LF] [Algebra K LF]

private theorem kaehler_free_rank_one_adjoin (x : LF) (hx : Transcendental K x) (T : Finset LF)
    (hT : ∀ t ∈ T, IsIntegral K⟮x⟯ t)
    (hsep : ∀ y : LF, IsIntegral K⟮x⟯ y → IsSeparable K⟮x⟯ y) :
    Module.Free (IntermediateField.adjoin K (insert x (T : Set LF)))
        (KaehlerDifferential K (IntermediateField.adjoin K (insert x (T : Set LF))))
      ∧ Module.finrank (IntermediateField.adjoin K (insert x (T : Set LF)))
        (KaehlerDifferential K (IntermediateField.adjoin K (insert x (T : Set LF)))) = 1 := by
  set F : IntermediateField K LF := IntermediateField.adjoin K (insert x (T : Set LF)) with hF
  have hxF : x ∈ F := subset_adjoin K _ (Set.mem_insert x _)
  have hTF : ∀ t ∈ T, t ∈ F := fun t ht => subset_adjoin K _ (Set.mem_insert_of_mem x ht)
  set x' : F := ⟨x, hxF⟩ with hx'

  have hx't : Transcendental K x' :=
    (transcendental_algebraMap_iff (R := K) (S := F) (A := LF) Subtype.val_injective).mp hx

  set A : IntermediateField K F := IntermediateField.adjoin K ({x'} : Set F) with hA
  have hliftA : lift A = K⟮x⟯ := by
    rw [hA, lift_adjoin_simple]
  let e : A ≃ₐ[K] K⟮x⟯ := (liftAlgEquiv A).trans (equivOfEq hliftA)
  have he : ∀ a : A, ((e a : K⟮x⟯) : LF) = ((a : F) : LF) := by
    intro a; rfl
  have hcomp : (algebraMap K⟮x⟯ LF).comp (e : A →+* K⟮x⟯) = (RingHom.id LF).comp (algebraMap A LF) :=
    RingHom.ext fun a => he a
  have hcomp' : (algebraMap A LF).comp (e.symm : K⟮x⟯ →+* A)
      = (RingHom.id LF).comp (algebraMap K⟮x⟯ LF) := by
    ext b
    change (((e.symm b : A) : F) : LF) = ((b : K⟮x⟯) : LF)
    rw [← he (e.symm b), AlgEquiv.apply_symm_apply]

  have hint : ∀ t (ht : t ∈ T), IsIntegral A (⟨t, hTF t ht⟩ : F) := by
    intro t ht
    have h1 : IsIntegral A (t : LF) :=
      (hT t ht).map_of_comp_eq (R := K⟮x⟯) (S := LF) (T := A) (U := LF)
        (e.symm : K⟮x⟯ →+* A) (RingHom.id LF) hcomp'
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom A F LF) Subtype.val_injective).mp h1

  haveI : FiniteDimensional A F := by
    set T' : Set F := (fun t : T => (⟨(t : LF), hTF t t.2⟩ : F)) '' Set.univ with hT'
    haveI : Finite T' := Set.Finite.to_subtype ((Set.finite_univ).image _)
    have hT'int : ∀ y ∈ T', IsIntegral A y := by
      rintro _ ⟨t, -, rfl⟩; exact hint t t.2
    haveI : FiniteDimensional A (IntermediateField.adjoin A T') := finiteDimensional_adjoin hT'int
    have htop : IntermediateField.adjoin A T' = ⊤ := by
      apply restrictScalars_injective K
      rw [restrictScalars_adjoin, restrictScalars_top]
      apply lift_injective
      rw [lift_top, lift_adjoin]
      apply le_antisymm (adjoin_le_iff.mpr ?_) ?_
      · rintro _ ⟨y, hy, rfl⟩; exact y.2
      · show IntermediateField.adjoin K (insert x (T : Set LF)) ≤ _
        apply adjoin.mono
        intro z hz
        rcases hz with rfl | hz
        · exact ⟨x', Or.inl (subset_adjoin K _ (Set.mem_singleton _)), rfl⟩
        · exact ⟨⟨z, hTF z hz⟩, Or.inr ⟨⟨z, hz⟩, Set.mem_univ _, rfl⟩, rfl⟩
    rw [htop] at this
    exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := A) (E := F)).toLinearEquiv

  haveI : Algebra.IsSeparable A F := ⟨fun z => by
    have hzLF : IsIntegral K⟮x⟯ ((z : F) : LF) :=
      ((IsIntegral.of_finite A z).map (IsScalarTower.toAlgHom A F LF)).map_of_comp_eq
        (R := A) (S := LF) (T := K⟮x⟯) (U := LF) (e : A →+* K⟮x⟯) (RingHom.id LF) hcomp
    have h2 : IsSeparable A ((z : F) : LF) :=
      IsSeparable.of_equiv_equiv (e.symm : K⟮x⟯ ≃+* A) (RingEquiv.refl LF) hcomp' (hsep _ hzLF)
    exact IsSeparable.of_algHom (IsScalarTower.toAlgHom A F LF) h2⟩
  exact kaehler_free_rank_one K x' hx't

end Adjoin

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
open ModularCurve in

private theorem isCurveOver_laurentBaseChange (L : Type*) [Field L] {instQL : Algebra ℚ L} (N : ℕ)
    [NeZero N] : IsCurveOver L (laurentBaseChange L (modularFunctionFieldFull N)) := by

  have hpair : laurentBaseChange L (modularFunctionFieldFull N)
      = IntermediateField.adjoin L {jqModC L, jqNModC L N} :=
    laurentBaseChange_adjoin_pair L N (functionFieldGeneration N)

  have hfin : ∀ E : IntermediateField L (LaurentSeries L), E = modularFunctionFieldC L N →
      ∀ w : Place L E, Module.Finite L w.ResidueField := by
    rintro E rfl w
    exact Module.finite_of_finrank_pos (Nat.pos_of_ne_zero (deg_ne_zero_modularFunctionFieldC L N w))

  have hkae : ∀ E : IntermediateField L (LaurentSeries L),
      E = IntermediateField.adjoin L
        (insert (jqModC L) ((({jqNModC L N} : Finset (LaurentSeries L)) : Set (LaurentSeries L)))) →
      Module.Free E (KaehlerDifferential L E) ∧ Module.finrank E (KaehlerDifferential L E) = 1 := by
    rintro E rfl
    haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
    refine kaehler_free_rank_one_adjoin L (jqModC L) (transcendental_jqModC L) {jqNModC L N} ?_ ?_
    · intro t ht
      rw [Finset.mem_singleton] at ht
      subst ht
      exact isIntegral_jqNModC_all L N
    · intro y hy
      haveI : CharZero L⟮jqModC L⟯ :=
        charZero_of_injective_algebraMap (algebraMap L L⟮jqModC L⟯).injective
      exact PerfectField.separable_of_irreducible (minpoly.irreducible hy)
  exact { hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull_unconditional L N with
    finiteResidue := hfin _ hpair
    kaehler_free_rank_one := hkae _ (by rw [Finset.coe_singleton]; exact hpair) }

end R0

end AlgebraicCurve

end

p2m_open "ModularCurve AlgebraicCurve P2MW.S_ModularCurve_isCurveOver_modularFunctionFieldBar.AlgebraicCurve"

theorem solution (N : ℕ) [NeZero N] :
    IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  AlgebraicCurve.R0.isCurveOver_laurentBaseChange (AlgebraicClosure ℚ) N

example : ∀ (N : ℕ) [NeZero N], IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := @solution

#print axioms solution

end S_ModularCurve_isCurveOver_modularFunctionFieldBar
end P2MW
export P2MW.S_ModularCurve_isCurveOver_modularFunctionFieldBar (solution)
