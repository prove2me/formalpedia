-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_ringHom_ringHom_placeMap_ord_eq_qExpFunctionFieldC_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/4b1f039c-eeae-576f-b381-d2f059818729

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_ModularCurve_exists_ringHom_qExpFunctionFieldC_coe_eq_coeffMap
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_ringHom_ringHom_placeMap_ord_eq_qExpFunctionFieldC_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "JHNeronObjectAtP.Fbar JHNeronObjectAtP coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single infSubgroup neZero_div translation_mem_GammaH Gamma1_le_GammaH intSeriesC intFormRatiosC qExpFunctionFieldC div_mem_qExpFunctionFieldC exists_ringHom_qExpFunctionFieldC_coe_eq_coeffMap exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed isCurveOver_qExpFunctionFieldC_of_isAlgClosed"
namespace PlaceLiftK
p2m_open "ModularCurve"

open Polynomial in

theorem isAlgebraic_residueField (p : ℕ) [Fact p.Prime] (Pl : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥Pl) p] :
    letI : Algebra (ZMod p) (IsLocalRing.ResidueField ↥Pl) := ZMod.algebra _ p
    Algebra.IsAlgebraic (ZMod p) (IsLocalRing.ResidueField ↥Pl) := by
  letI : Algebra (ZMod p) (IsLocalRing.ResidueField ↥Pl) := ZMod.algebra _ p
  refine ⟨fun y => ?_⟩
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  have hxQ : IsAlgebraic ℚ (x : AlgebraicClosure ℚ) := Algebra.IsAlgebraic.isAlgebraic _
  have hxZ : IsAlgebraic ℤ (x : AlgebraicClosure ℚ) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr hxQ
  obtain ⟨f, hf0, hfx⟩ := hxZ

  have hfx' : aeval (x : AlgebraicClosure ℚ) f.primPart = 0 := by
    have h := hfx
    rw [f.eq_C_content_mul_primPart, map_mul, aeval_C, mul_eq_zero] at h
    refine h.resolve_left ?_
    rw [eq_intCast, Int.cast_eq_zero]
    exact fun hc => hf0 (content_eq_zero_iff.mp hc)
  have hmap : f.primPart.map (algebraMap ℤ (ZMod p)) ≠ 0 := by
    intro h0
    have hdvd : C (p : ℤ) ∣ f.primPart := by
      rw [C_dvd_iff_dvd_coeff]
      intro n
      have hc : (algebraMap ℤ (ZMod p)) (f.primPart.coeff n) = 0 := by
        rw [← coeff_map, h0, coeff_zero]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hc
    have hu := f.isPrimitive_primPart (p : ℤ) hdvd
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hu
    exact (Fact.out : p.Prime).one_lt.ne' hu

  have hPl : aeval x f.primPart = 0 := by
    apply Subtype.val_injective
    show Pl.subtype (eval₂ (algebraMap ℤ ↥Pl) x f.primPart) = ((0 : ↥Pl) : AlgebraicClosure ℚ)
    rw [Polynomial.hom_eval₂, show Pl.subtype.comp (algebraMap ℤ ↥Pl) = algebraMap ℤ (AlgebraicClosure ℚ)
      from RingHom.ext_int _ _, ← aeval_def]
    exact hfx'
  have hres : aeval (IsLocalRing.residue ↥Pl x) (f.primPart.map (algebraMap ℤ (ZMod p))) = 0 := by
    rw [aeval_def, eval₂_map, show (algebraMap (ZMod p) (IsLocalRing.ResidueField ↥Pl)).comp (algebraMap ℤ (ZMod p)) =
      (IsLocalRing.residue ↥Pl).comp (algebraMap ℤ ↥Pl) from RingHom.ext_int _ _, ← Polynomial.hom_eval₂, ← aeval_def,
      hPl, map_zero]
  exact ⟨f.primPart.map (algebraMap ℤ (ZMod p)), hmap, hres⟩

theorem coeffMap_algebraMap' {k K : Type*} [Field k] [Field K] (ι : k →+* K) (c : k) :
    ModularCurve.coeffMap ι (algebraMap k (LaurentSeries k) c) = algebraMap K (LaurentSeries K) (ι c) := by
  rw [ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.algebraMap_laurentSeries_eq_single,
    ModularCurve.coeffMap_single]

theorem coeffMap_intSeriesC {k K : Type*} [Field k] [Field K] (ι : k →+* K) (q : PowerSeries ℤ) :
    ModularCurve.coeffMap ι (ModularCurve.intSeriesC k q) = ModularCurve.intSeriesC K q := by
  ext n
  simp only [ModularCurve.intSeriesC, ModularCurve.coeffMap_coeff, PowerSeries.coeff_coe,
    PowerSeries.coeff_map, apply_ite ι, map_zero, eq_intCast, map_intCast]

theorem intFormRatiosC_subset_image {k K : Type*} [Field k] [Field K] (ι : k →+* K) (Γ : Subgroup SL(2, ℤ)) :
    ModularCurve.intFormRatiosC K Γ ⊆ ModularCurve.coeffMap ι '' (ModularCurve.qExpFunctionFieldC k Γ : Set (LaurentSeries k)) := by
  rintro r ⟨w, f, g, pf, pg, hf, hg, hg0, rfl⟩
  have hg0k : ModularCurve.intSeriesC k pg ≠ 0 := by
    intro h
    apply hg0
    rw [← coeffMap_intSeriesC ι pg, h, map_zero]
  refine ⟨ModularCurve.intSeriesC k pf / ModularCurve.intSeriesC k pg,
    ModularCurve.div_mem_qExpFunctionFieldC f g hf hg hg0k, ?_⟩
  rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]

end ModularCurve.PlaceLiftK

open ModularCurve.PlaceLiftK in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] :
    ∃ (ι : IsLocalRing.ResidueField ↥Pl →+* K)
      (eK : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl) →+* ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
      (plK : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) → AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))),
      (∀ g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl), ((eK g : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) = ModularCurve.coeffMap ι (g : LaurentSeries (IsLocalRing.ResidueField ↥Pl))) ∧
      (∀ (g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) (v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))), (plK v).ord (eK g) = v.ord g) := by
  classical
  haveI hMp : NeZero (M / p) := ModularCurve.neZero_div p M hpM

  letI iκ : Algebra (ZMod p) (IsLocalRing.ResidueField ↥Pl) := ZMod.algebra _ p
  letI iK : Algebra (ZMod p) K := ZMod.algebra _ p
  haveI := isAlgebraic_residueField p Pl
  let ι : IsLocalRing.ResidueField ↥Pl →+* K :=
    (IsAlgClosed.lift : IsLocalRing.ResidueField ↥Pl →ₐ[ZMod p] K).toRingHom

  obtain ⟨eK, heK⟩ := ModularCurve.exists_ringHom_qExpFunctionFieldC_coe_eq_coeffMap ι
    (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))

  haveI : (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH _ _)
  have hT : ModularGroup.T ∈ CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) :=
    ModularCurve.translation_mem_GammaH _ _
  let iκF : Algebra (IsLocalRing.ResidueField ↥Pl)
      (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) := inferInstance
  haveI iCO : AlgebraicCurve.IsCurveOver (IsLocalRing.ResidueField ↥Pl)
      (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) :=
    ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed _ _ hT
  obtain ⟨xκ, -, hxκ, hfdκ⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
      (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) hT
  obtain ⟨xK, -, hxK, hfdK⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
      K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) hT

  letI a1 : Algebra (IsLocalRing.ResidueField ↥Pl) K := ι.toAlgebra
  letI a2 : Algebra (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))
      ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) := eK.toAlgebra
  letI a3 : Algebra (IsLocalRing.ResidueField ↥Pl)
      ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) :=
    ((algebraMap K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))).comp ι).toAlgebra
  haveI t1 : IsScalarTower (IsLocalRing.ResidueField ↥Pl) K
      ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) :=
    IsScalarTower.of_algebraMap_eq fun c => rfl
  haveI t2 : IsScalarTower (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))
      ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    apply Subtype.ext
    show ((algebraMap K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (ι c) :
        ↥(ModularCurve.qExpFunctionFieldC K _)) : LaurentSeries K) =
      ((eK (algebraMap (IsLocalRing.ResidueField ↥Pl) _ c) : ↥(ModularCurve.qExpFunctionFieldC K _)) : LaurentSeries K)
    rw [heK]
    change algebraMap K (LaurentSeries K) (ι c) =
      ModularCurve.coeffMap ι (algebraMap (IsLocalRing.ResidueField ↥Pl) (LaurentSeries (IsLocalRing.ResidueField ↥Pl)) c)
    rw [coeffMap_algebraMap']

  have hgen : IntermediateField.adjoin K (Set.range (algebraMap
      (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))
      ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))))) = ⊤ := by
    rw [eq_top_iff]
    intro y _

    have h2 : (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ≤ (IntermediateField.adjoin K (Set.range (algebraMap (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))))).map (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))).val := by
      change IntermediateField.adjoin K (ModularCurve.intFormRatiosC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ≤ _
      rw [IntermediateField.adjoin_le_iff]
      intro r hr
      obtain ⟨z, hz, rfl⟩ := intFormRatiosC_subset_image ι _ hr
      show ModularCurve.coeffMap ι z ∈ ((IntermediateField.adjoin K (Set.range (algebraMap (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))))).map (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))).val :
        IntermediateField K (LaurentSeries K))
      exact (IntermediateField.mem_map _).mpr ⟨eK ⟨z, hz⟩, IntermediateField.subset_adjoin K _ ⟨⟨z, hz⟩, rfl⟩, heK ⟨z, hz⟩⟩
    obtain ⟨a, ha, hay⟩ := (IntermediateField.mem_map _).mp (h2 y.2)
    have hay' : a = y := Subtype.ext hay
    exact hay' ▸ ha
  have key := fun P => @AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
    (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))
    K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
    _ _ _ _ iκF _ a1 a2 a3 t1 t2 _ ⟨xκ, hxκ, hfdκ⟩ ⟨xK, hxK, hfdK⟩ iCO hgen P
  choose plK _hcomap hord _huniq using key
  exact ⟨ι, eK, plK, heK, fun g v => hord v g⟩

end S_ModularCurve_JHNeronObjectAtP_exists_ringHom_ringHom_placeMap_ord_eq_qExpFunctionFieldC_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_ringHom_ringHom_placeMap_ord_eq_qExpFunctionFieldC_of_isAlgClosed (solution)
