-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/81f4bf36-d747-5bb9-b703-ff3c25b2fe2d

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_Localization_AtPrime_mem_range_of_forall_comap_eq_bot_and_valuation_dichotomy_tensorProduct_valuationSubring_of_liesOverPrime
import Theorems.Thm_ModularCurve_XHDRLevel_flat_chartAlgFin_and_flat_chartAlgInf
import Theorems.Thm_ModularCurve_finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens
import Theorems.Thm_ModularCurve_XHDRModelAtP_isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
import Theorems.Thm_ValuationSubring_eq_of_le_of_mem_nonunits_of_maximalIdeal_le_radical
import Theorems.Thm_AlgebraicCurve_RegularProlongation_krullDimLE_one_integers
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_of_liesOverPrime
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply"
p2m_attr_erase "simp" "CohCarrier.frickeH1_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
open scoped MatrixGroups TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open IsLocalRing AlgebraicCurve

namespace BranchReadE4

theorem exists_pow_mem_span_natCast_of_mem_maximalIdeal (p : ℕ) [hp : Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (m : ↥A) (hm : m ∈ maximalIdeal ↥A) :
    ∃ k : ℕ, m ^ k ∈ Ideal.span {((p : ℕ) : ↥A)} := by
  classical

  set L : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {(m : AlgebraicClosure ℚ)} with hL
  haveI hAlg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ
    all_goals first | rfl | skip
  haveI : FiniteDimensional ℚ ↥L :=
    IntermediateField.adjoin.finiteDimensional ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (m : AlgebraicClosure ℚ)).isIntegral)
  haveI hDVR : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥L (AlgebraicClosure ℚ))) :=
    ValuationSubring.isDiscreteValuationRing_comap_of_liesOverPrime L A hp.out hA
  set AL := A.comap (algebraMap ↥L (AlgebraicClosure ℚ)) with hAL

  have hmL : (m : AlgebraicClosure ℚ) ∈ L := IntermediateField.mem_adjoin_simple_self ℚ _
  set mL : ↥AL := ⟨⟨(m : AlgebraicClosure ℚ), hmL⟩, by show algebraMap ↥L (AlgebraicClosure ℚ) ⟨m, hmL⟩ ∈ A; exact m.2⟩ with hmLdef
  set pL : ↥AL := ⟨((p : ℕ) : ↥L), by show algebraMap ↥L (AlgebraicClosure ℚ) (p : ↥L) ∈ A; rw [map_natCast]; exact natCast_mem A p⟩ with hpLdef

  let ι : ↥AL →+* ↥A :=
    { toFun := fun x => ⟨algebraMap ↥L (AlgebraicClosure ℚ) x.1, x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have hιm : ι mL = m := Subtype.ext rfl
  have hιp : ι pL = ((p : ℕ) : ↥A) := by
    apply Subtype.ext
    show algebraMap ↥L (AlgebraicClosure ℚ) (p : ↥L) = ((p : ↥A) : AlgebraicClosure ℚ)
    rw [map_natCast]; rfl

  have hp0 : pL ≠ 0 := by
    intro h
    have := congrArg (fun x : ↥AL => ((x.1 : ↥L) : AlgebraicClosure ℚ)) h
    simp only [hpLdef] at this
    exact (Nat.cast_ne_zero.mpr hp.out.ne_zero : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0) (by simpa using this)
  have hpA : ((p : ℕ) : ↥A) ∈ maximalIdeal ↥A := by
    obtain ⟨h, hmem⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mp hA
    have hc : (⟨(p : AlgebraicClosure ℚ), h⟩ : ↥A) = ((p : ℕ) : ↥A) := Subtype.ext (by simp)
    rw [← hc]
    exact hmem
  have key : ∀ x : ↥AL, ι x ∈ maximalIdeal ↥A → x ∈ maximalIdeal ↥AL := fun x hx => by
    rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun hu => hx (hu.map ι)
  have hpnu : pL ∈ maximalIdeal ↥AL := key pL (by rw [hιp]; exact hpA)
  have hmnu : mL ∈ maximalIdeal ↥AL := key mL (by rw [hιm]; exact hm)

  have hrad : mL ∈ (Ideal.span {pL}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hJ, hJp⟩
    have hJne : J ≠ ⊥ := fun h => hp0 (by
      have : pL ∈ J := hJ (Ideal.subset_span rfl)
      rw [h] at this
      exact (Submodule.mem_bot _).mp this)
    have hJmax : J = maximalIdeal ↥AL := IsLocalRing.eq_maximalIdeal (hJp.isMaximal hJne)
    rw [hJmax]; exact hmnu
  obtain ⟨k, hk⟩ := hrad
  refine ⟨k, ?_⟩
  have := Ideal.mem_map_of_mem ι hk
  rw [Ideal.map_span, Set.image_singleton, hιp, map_pow, hιm] at this
  exact this

theorem natCast_mem_of_isPrime_of_ne_bot (p : ℕ) [hp : Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (P : Ideal ↥A) [hP : P.IsPrime] (hP0 : P ≠ ⊥) : ((p : ℕ) : ↥A) ∈ P := by
  classical
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  set L : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {(x : AlgebraicClosure ℚ)} with hL
  haveI hAlg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ
    all_goals first | rfl | skip
  haveI : FiniteDimensional ℚ ↥L :=
    IntermediateField.adjoin.finiteDimensional ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (x : AlgebraicClosure ℚ)).isIntegral)
  haveI hDVR : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥L (AlgebraicClosure ℚ))) :=
    ValuationSubring.isDiscreteValuationRing_comap_of_liesOverPrime L A hp.out hA
  set AL := A.comap (algebraMap ↥L (AlgebraicClosure ℚ)) with hAL
  have hxL : (x : AlgebraicClosure ℚ) ∈ L := IntermediateField.mem_adjoin_simple_self ℚ _
  set xL : ↥AL := ⟨⟨(x : AlgebraicClosure ℚ), hxL⟩, by show algebraMap ↥L (AlgebraicClosure ℚ) ⟨x, hxL⟩ ∈ A; exact x.2⟩ with hxLdef
  set pL : ↥AL := ⟨((p : ℕ) : ↥L), by show algebraMap ↥L (AlgebraicClosure ℚ) (p : ↥L) ∈ A; rw [map_natCast]; exact natCast_mem A p⟩ with hpLdef
  let ι : ↥AL →+* ↥A :=
    { toFun := fun y => ⟨algebraMap ↥L (AlgebraicClosure ℚ) y.1, y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun _ _ => Subtype.ext (by simp) }
  have hιx : ι xL = x := Subtype.ext rfl
  have hιp : ι pL = ((p : ℕ) : ↥A) := by
    apply Subtype.ext
    show algebraMap ↥L (AlgebraicClosure ℚ) (p : ↥L) = ((p : ↥A) : AlgebraicClosure ℚ)
    rw [map_natCast]; rfl
  have hpA : ((p : ℕ) : ↥A) ∈ maximalIdeal ↥A := by
    obtain ⟨h, hmem⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mp hA
    have hc : (⟨(p : AlgebraicClosure ℚ), h⟩ : ↥A) = ((p : ℕ) : ↥A) := Subtype.ext (by simp)
    rw [← hc]
    exact hmem
  have hpnu : pL ∈ maximalIdeal ↥AL := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map ι
    rw [hιp] at this
    exact (mem_maximalIdeal _ |>.mp hpA) this

  have hJ0 : P.comap ι ≠ ⊥ := fun h => by
    have : xL ∈ P.comap ι := by rw [Ideal.mem_comap, hιx]; exact hxP
    rw [h, Submodule.mem_bot] at this
    apply hx0
    rw [← hιx, this, map_zero]
  have hJmax : P.comap ι = maximalIdeal ↥AL := IsLocalRing.eq_maximalIdeal ((Ideal.comap_isPrime ι P).isMaximal hJ0)
  have : pL ∈ P.comap ι := hJmax ▸ hpnu
  rw [Ideal.mem_comap, hιp] at this
  exact this

theorem krullDimLE_one_of_liesOverPrime (p : ℕ) [hp : Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) : Ring.KrullDimLE 1 ↥A := by
  refine Ring.KrullDimLE.mk₁' (fun I hI0 hI => ?_)
  haveI := hI
  have hle : maximalIdeal ↥A ≤ I := fun m hm => by
    obtain ⟨k, hk⟩ := exists_pow_mem_span_natCast_of_mem_maximalIdeal p A hA m hm
    have hpI : Ideal.span {((p : ℕ) : ↥A)} ≤ I := (Ideal.span_singleton_le_iff_mem _).mpr (natCast_mem_of_isPrime_of_ne_bot p A hA I hI0)
    exact hI.mem_of_pow_mem k (hpI hk)
  have heq : I = maximalIdeal ↥A := le_antisymm (IsLocalRing.le_maximalIdeal hI.ne_top) hle
  rw [heq]
  exact IsLocalRing.maximalIdeal.isMaximal ↥A

theorem natCast_mem_nonunits_integers
    (p : ℕ) [Fact p.Prime] {F Fb : Type*} [Field F] [Algebra (AlgebraicClosure ℚ) F] [Field Fb]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [Algebra (ResidueField ↥A) Fb] [CharP (ResidueField ↥A) p]
    (Rg : RegularProlongation A F Fb) :
    (algebraMap (AlgebraicClosure ℚ) F (p : AlgebraicClosure ℚ)) ∈ Rg.integers.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  refine ⟨(Rg.algebraMap_mem_iff _).mpr (natCast_mem A p), ?_⟩
  rw [← Rg.ker_residue, RingHom.mem_ker]
  have : (⟨algebraMap (AlgebraicClosure ℚ) F (p : AlgebraicClosure ℚ), (Rg.algebraMap_mem_iff _).mpr (natCast_mem A p)⟩ : ↥Rg.integers) =
      ⟨algebraMap (AlgebraicClosure ℚ) F (((p : ℕ) : ↥A) : AlgebraicClosure ℚ), (Rg.algebraMap_mem_iff _).mpr ((p : ℕ) : ↥A).2⟩ :=
    Subtype.ext (by simp)
  rw [this, Rg.residue_algebraMap, map_natCast, CharP.cast_eq_zero (ResidueField ↥A) p, map_zero]

theorem eq_integers_and_rankOne_of_le_integers_of_maximalIdeal_le
    (p : ℕ) [Fact p.Prime]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p) [CharP (ResidueField ↥Pl) p]
    {F : Type*} [Field F] [Algebra (AlgebraicClosure ℚ) F] {Fbar : Type*} [Field Fbar] [Algebra (ResidueField ↥Pl) Fbar]
    (Rg : RegularProlongation Pl F Fbar)
    (V : ValuationSubring F) (hVRg : V ≤ Rg.integers)
    (ιV : ↥Pl →+* ↥V) (hιV : ∀ a : ↥Pl, ((ιV a : ↥V) : F) = algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ))
    (hV𝔪 : maximalIdeal ↥V ≤ (maximalIdeal ↥Pl).map ιV) :
    V = Rg.integers ∧ ∀ V' : ValuationSubring F, V ≤ V' → V' = V ∨ V' = ⊤ := by
  classical
  have hpW := natCast_mem_nonunits_integers p Pl Rg
  have hrad : maximalIdeal ↥V ≤ (Ideal.span {ιV ((p : ℕ) : ↥Pl)}).radical := by
    refine le_trans hV𝔪 ?_
    rw [Ideal.map_le_iff_le_comap]
    intro m hm
    obtain ⟨k, hk⟩ := exists_pow_mem_span_natCast_of_mem_maximalIdeal p Pl hPl m hm
    have := Ideal.mem_map_of_mem ιV hk
    rw [Ideal.map_span, Set.image_singleton, map_pow] at this
    exact ⟨k, this⟩
  have hxW : ((ιV ((p : ℕ) : ↥Pl) : ↥V) : F) ∈ Rg.integers.nonunits := by
    rw [hιV]
    have : (((p : ℕ) : ↥Pl) : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) := by simp
    rw [this]
    exact hpW
  have hV : V = Rg.integers :=
    ValuationSubring.eq_of_le_of_mem_nonunits_of_maximalIdeal_le_radical V Rg.integers hVRg (ιV ((p : ℕ) : ↥Pl)) hxW hrad
  refine ⟨hV, ?_⟩
  haveI : Ring.KrullDimLE 1 ↥Pl := krullDimLE_one_of_liesOverPrime p Pl hPl
  haveI : Ring.KrullDimLE 1 ↥Rg.integers := AlgebraicCurve.RegularProlongation.krullDimLE_one_integers Pl Rg
  intro V' hV'
  rw [hV] at hV' ⊢
  rcases ValuationSubring.eq_self_or_eq_top_of_le hV' with h | h
  · exact Or.inl h.symm
  · exact Or.inr h

end BranchReadE4

set_option synthInstance.maxHeartbeats 1600000

open scoped MatrixGroups TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

noncomputable section

namespace BranchReadSkel

open ModularCurve AlgebraicCurve
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section Generic

universe u

variable {R K B : Type u} [CommRing R] [CommRing K] [CommRing B] [Algebra R K] [Algebra R B]
  {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R))
  (ιB : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion ιB]
  (hιB : ιB ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R B)))

include hιB

omit hιB in
theorem appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y) (h : ⊤ ≤ f ⁻¹ᵁ ⊤) : f.appLE ⊤ ⊤ h = f.appTop :=
  Scheme.Hom.appLE_eq_app _

noncomputable def bcChart :
    Spec (CommRingCat.of (K ⊗[R] B)) ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  (pullbackSpecIso R K B).inv ≫
    pullback.map (Spec.map (CommRingCat.ofHom (algebraMap R K))) (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) c (𝟙 _) ιB (𝟙 _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) ((Category.comp_id _).trans hιB.symm) ≫
    (pullbackSymmetry _ _).hom

omit [IsOpenImmersion ιB] in
@[reassoc]
theorem bcChart_fst : bcChart c ιB hιB (K := K) ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom) ≫ ιB := by
  simp only [bcChart, Category.assoc, pullbackSymmetry_hom_comp_fst, pullback.lift_snd, pullbackSpecIso_inv_snd_assoc]
  rfl

omit [IsOpenImmersion ιB] in
@[reassoc]
theorem bcChart_snd : bcChart c ιB hιB (K := K) ≫ pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := K) (B := B))) := by
  simp only [bcChart, Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.lift_fst, Category.comp_id,
    pullbackSpecIso_inv_fst]

scoped instance bcChart_isOpenImmersion : IsOpenImmersion (bcChart c ιB hιB (K := K)) := by
  have : IsOpenImmersion (pullback.map (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) c (𝟙 _) ιB (𝟙 _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) ((Category.comp_id _).trans hιB.symm)) :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) (i₁ := 𝟙 _) (i₂ := ιB) inferInstance inferInstance
      (Category.id_comp _).symm hιB.symm
  unfold bcChart
  infer_instance

omit [IsOpenImmersion ιB] in
theorem range_bcChart : Set.range (bcChart c ιB hιB (K := K)) =
    (pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹' Set.range ιB := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    refine ⟨Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom) t, ?_⟩
    show _ = (bcChart c ιB hιB ≫ pullback.fst _ _) t
    rw [bcChart_fst]
    rfl
  · rintro z ⟨w, hw⟩
    set z' : ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap R K))) c) :=
      (pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap R K))) c).inv z with hz'def
    have hz' : z' ∈ Set.range (pullback.map (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) c (𝟙 _) ιB (𝟙 _)
        ((Category.comp_id _).trans (Category.id_comp _).symm) ((Category.comp_id _).trans hιB.symm)) := by
      rw [Scheme.Pullback.range_map]
      refine ⟨⟨pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K))) c z', rfl⟩, ⟨w, ?_⟩⟩
      show ιB w = ((pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap R K))) c).inv ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R K))) c) z
      rw [pullbackSymmetry_inv_comp_snd]
      exact hw
    obtain ⟨t, ht⟩ := hz'
    refine ⟨(pullbackSpecIso R K B).hom t, ?_⟩
    show ((pullbackSpecIso R K B).hom ≫ bcChart c ιB hιB) t = z
    simp only [bcChart, Iso.hom_inv_id_assoc, Scheme.Hom.comp_apply, ht, hz'def]
    show ((pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap R K))) c).inv ≫
      (pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap R K))) c).hom) z = z
    rw [Iso.inv_hom_id]
    rfl

variable {Y : Scheme.{u}} (e : Y ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) [IsIso e]

noncomputable def gChart : Spec (CommRingCat.of (K ⊗[R] B)) ⟶ Y := bcChart c ιB hιB ≫ inv e

scoped instance gChart_isOpenImmersion : IsOpenImmersion (gChart c ιB hιB e) := by
  unfold gChart; infer_instance

omit [IsOpenImmersion ιB] in
@[reassoc]
theorem gChart_comp_fst : gChart c ιB hιB e ≫ e ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom) ≫ ιB := by
  simp [gChart, bcChart_fst]

omit [IsOpenImmersion ιB] in
@[reassoc]
theorem gChart_comp_snd : gChart c ιB hιB e ≫ e ≫ pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := K) (B := B))) := by
  simp [gChart, bcChart_snd]

theorem opensRange_gChart :
    (gChart c ιB hιB e).opensRange = (e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ (ιB ''ᵁ ⊤) := by
  ext z
  simp only [Scheme.Hom.coe_opensRange, Set.mem_range, TopologicalSpace.Opens.map_coe, Set.mem_preimage,
    TopologicalSpace.Opens.coe_top, Scheme.Hom.coe_image, Set.image_univ]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom) t, ?_⟩
    show _ = (gChart c ιB hιB e ≫ e ≫ pullback.fst _ _) t
    rw [gChart_comp_fst]
    rfl
  · rintro ⟨w, hw⟩
    have : e z ∈ Set.range (bcChart c ιB hιB (K := K)) := by
      rw [range_bcChart]
      exact ⟨w, hw⟩
    obtain ⟨t, ht⟩ := this
    refine ⟨t, ?_⟩
    show (bcChart c ιB hιB ≫ inv e) t = z
    rw [Scheme.Hom.comp_apply, ht, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
    rfl

theorem isAffineOpen_U :
    IsAffineOpen ((e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ (ιB ''ᵁ ⊤)) := by
  rw [← opensRange_gChart c ιB hιB e]; exact isAffineOpen_opensRange _

theorem top_le_preimage_U :
    ⊤ ≤ (gChart c ιB hιB e) ⁻¹ᵁ ((e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ (ιB ''ᵁ ⊤)) := by
  rw [← opensRange_gChart c ιB hιB e, Scheme.Hom.preimage_opensRange]

noncomputable def φ : Γ(Y, (e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ (ιB ''ᵁ ⊤)) ⟶
    Γ(Spec (CommRingCat.of (K ⊗[R] B)), ⊤) :=
  (gChart c ιB hιB e).appLE _ ⊤ (top_le_preimage_U c ιB hιB e)

scoped instance φ_isIso : IsIso (φ c ιB hιB e) := by
  unfold φ
  rw [Scheme.Hom.appLE]
  have h1 : IsIso ((gChart c ιB hιB e).app
      ((e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ (ιB ''ᵁ ⊤))) :=
    Scheme.Hom.isIso_app _ _ (by rw [opensRange_gChart c ιB hιB e])
  have h2 : homOfLE (top_le_preimage_U c ιB hιB e) =
      eqToHom (by rw [← opensRange_gChart c ιB hιB e, Scheme.Hom.preimage_opensRange]) :=
    Subsingleton.elim _ _
  rw [h2, eqToHom_op]
  infer_instance

noncomputable def θ : Γ(Y, (e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ (ιB ''ᵁ ⊤)) ≅
    CommRingCat.of (K ⊗[R] B) :=
  asIso (φ c ιB hιB e) ≪≫ Scheme.ΓSpecIso (CommRingCat.of (K ⊗[R] B))

theorem φ_section (b : B) :
    φ c ιB hιB e (((e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app (ιB ''ᵁ ⊤))
      ((ιB.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b))) =
    (Scheme.ΓSpecIso (CommRingCat.of (K ⊗[R] B))).inv ((1 : K) ⊗ₜ[R] b) := by
  have key : ∀ {f₁ f₂ : Spec (CommRingCat.of (K ⊗[R] B)) ⟶ X} (_ : f₁ = f₂)
      (e₁ : ⊤ ≤ f₁ ⁻¹ᵁ (ιB ''ᵁ ⊤)) (e₂ : ⊤ ≤ f₂ ⁻¹ᵁ (ιB ''ᵁ ⊤)),
      f₁.appLE (ιB ''ᵁ ⊤) ⊤ e₁ = f₂.appLE (ιB ''ᵁ ⊤) ⊤ e₂ := by
    rintro _ _ rfl _ _; rfl
  have hle : ⊤ ≤ (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom)
      ≫ ιB) ⁻¹ᵁ (ιB ''ᵁ ⊤) := by
    rw [← gChart_comp_fst c ιB hιB e]
    exact (top_le_preimage_U c ιB hιB e)
  have h1 : (e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app (ιB ''ᵁ ⊤) ≫ φ c ιB hιB e =
      (ιB.appIso ⊤).hom ≫ (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom)).appTop := by
    unfold φ
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, key (gChart_comp_fst c ιB hιB e) _ hle,
      ← Scheme.Hom.appLE_comp_appLE _ _ _ ⊤ _ (ιB.preimage_image_eq ⊤).ge le_top,
      Scheme.Hom.appIso_hom', appLE_top_top]
  have h2 := congrArg (fun ψ => ψ.hom ((ιB.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b))) h1
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
  rw [h2, Iso.inv_hom_id_apply]
  have h3 := congrArg (fun ψ => ψ.hom b) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h3
  rw [← h3]
  rfl

theorem θ_section (b : B) :
    (θ c ιB hιB e).hom (((e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app (ιB ''ᵁ ⊤))
      ((ιB.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b))) = (1 : K) ⊗ₜ[R] b := by
  simp only [θ, Iso.trans_hom, asIso_hom]
  show (Scheme.ΓSpecIso (CommRingCat.of (K ⊗[R] B))).hom (φ c ιB hιB e _) = _
  rw [φ_section c ιB hιB e b, Iso.inv_hom_id_apply]

theorem φ_const (cK : Y ⟶ Spec (CommRingCat.of K))
    (hcK : gChart c ιB hιB e ≫ cK = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := K) (B := B))))
    (α : K) :
    φ c ιB hιB e (Y.presheaf.map (homOfLE le_top).op (cK.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv α))) =
    (Scheme.ΓSpecIso (CommRingCat.of (K ⊗[R] B))).inv (α ⊗ₜ[R] (1 : B)) := by
  have h1 : Y.presheaf.map (homOfLE (le_top :
      (e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ (ιB ''ᵁ ⊤) ≤ ⊤)).op ≫ φ c ιB hιB e =
      (gChart c ιB hιB e).appTop := by
    unfold φ
    rw [Scheme.Hom.map_appLE, appLE_top_top]
  have h2 := congrArg (fun ψ => ψ.hom (cK.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv α))) h1
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
  rw [h2, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hcK]
  have h3 := congrArg (fun ψ => ψ.hom α) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := K) (B := B))))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h3
  rw [← h3]
  rfl

theorem θ_const (cK : Y ⟶ Spec (CommRingCat.of K))
    (hcK : gChart c ιB hιB e ≫ cK = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := K) (B := B))))
    (α : K) :
    (θ c ιB hιB e).hom (Y.presheaf.map (homOfLE le_top).op (cK.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv α))) =
    α ⊗ₜ[R] (1 : B) := by
  simp only [θ, Iso.trans_hom, asIso_hom]
  show (Scheme.ΓSpecIso (CommRingCat.of (K ⊗[R] B))).hom (φ c ιB hιB e _) = _
  rw [φ_const c ιB hιB e cK hcK, Iso.inv_hom_id_apply]

theorem specθ_comp_fromSpec :
    Spec.map (θ c ιB hιB e).hom ≫ (isAffineOpen_U c ιB hιB e).fromSpec = gChart c ιB hιB e := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (gChart c ιB hιB e) (isAffineOpen_U c ιB hιB e)
    (isAffineOpen_top _) (top_le_preimage_U c ιB hιB e)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  simp only [θ, Iso.trans_hom, asIso_hom, Spec.map_comp, Category.assoc]
  erw [h]
  rw [← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem fromSpec_specθ (𝔮' : PrimeSpectrum (K ⊗[R] B)) :
    (isAffineOpen_U c ιB hιB e).fromSpec (Spec.map (θ c ιB hιB e).hom 𝔮') = gChart c ιB hιB e 𝔮' := by
  rw [← Scheme.Hom.comp_apply, specθ_comp_fromSpec]

theorem specθ_asIdeal (𝔮' : PrimeSpectrum (K ⊗[R] B)) :
    (Spec.map (θ c ιB hιB e).hom 𝔮').asIdeal = 𝔮'.asIdeal.comap (θ c ιB hιB e).hom.hom := rfl

end Generic

theorem base_inv_base_apply {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (y : Y) : f.base ((inv f).base y) = y := by
  show ((inv f) ≫ f).base y = y
  rw [IsIso.inv_hom_id]; rfl

end BranchReadSkel
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const.BranchReadSkel"

namespace EtaVal29

open ModularCurve AlgebraicCurve BranchReadSkel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section Topology

theorem closure_singleton_genericPoint_eq_range {C Y : Scheme.{0}} [IsIntegral C] (φ : C ⟶ Y) [IsClosedImmersion φ] :
    closure ({φ.base (genericPoint C)} : Set Y) = Set.range φ.base := by
  apply le_antisymm
  · exact closure_minimal (Set.singleton_subset_iff.mpr ⟨_, rfl⟩) φ.isClosedEmbedding.isClosed_range
  · rintro _ ⟨y, rfl⟩
    exact ((genericPoint_specializes y).map φ.continuous).mem_closure

theorem false_of_genericPoint_mem_range {C Y : Scheme.{0}} [IsIntegral C]
    (hC : ∀ y : C, y ≠ genericPoint C → IsClosed ({y} : Set C))
    (φ ψ : C ⟶ Y) [IsClosedImmersion φ] [IsClosedImmersion ψ]
    (hne : Set.range φ.base ≠ Set.range ψ.base) (hmem : ψ.base (genericPoint C) ∈ Set.range φ.base) : False := by
  have hclφ := closure_singleton_genericPoint_eq_range φ
  have hclψ := closure_singleton_genericPoint_eq_range ψ
  obtain ⟨y, hy⟩ := hmem
  by_cases hyη : y = genericPoint C
  · subst hyη
    apply hne
    rw [← hclφ, ← hclψ, hy]
  · have hcl : IsClosed ({ψ.base (genericPoint C)} : Set Y) := by
      rw [← hy, ← Set.image_singleton]
      exact φ.isClosedEmbedding.isClosedMap _ (hC y hyη)
    have hrange : Set.range ψ.base = {ψ.base (genericPoint C)} := by
      rw [← hclψ, hcl.closure_eq]
    have hψy : ψ.base y ∈ ({ψ.base (genericPoint C)} : Set Y) := hrange ▸ ⟨y, rfl⟩
    exact hyη (ψ.isClosedEmbedding.injective (Set.mem_singleton_iff.mp hψy))

end Topology
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const.BranchReadSkel"

section BC

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (A : ValuationSubring (AlgebraicClosure ℚ)) [Algebra (R p) ↥A]
  (bc : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))

include hbc₁ hbc₂ in
omit [Fact p.Prime] [NeZero M] in
theorem isPullback_bc : IsPullback bc (pullback.snd _ _) (pullback.snd _ _) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) := by
  have hig : Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)) =
      Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have s : IsPullback (bc ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A))))
      (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)))))
      (toBase p (ΓM M H) hj)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A))) := by
    rw [hbc₁, hig]
    exact IsPullback.of_hasPullback _ _
  exact IsPullback.of_right s hbc₂ (IsPullback.of_hasPullback _ _)

include hbc₁ hbc₂ in
omit [Fact p.Prime] [NeZero M] in
theorem isClosedImmersion_bc : IsClosedImmersion bc := by
  have hi : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion) (isPullback_bc p M H hj A bc hbc₁ hbc₂).flip hi

end BC
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const.BranchReadSkel"

section FibrePoint

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (A : ValuationSubring (AlgebraicClosure ℚ)) [Algebra (R p) ↥A]

set_option maxHeartbeats 3200000 in

theorem specMap_comp_bcChart_eq_bcChart_comp (bc : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) :
    Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) ≫ (bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ↥A)) = (@CategoryStruct.comp Scheme _ (Spec (CommRingCat.of (ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)))) (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) _ (bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ResidueField ↥A)) bc) := by

  have hKfst : (@CategoryStruct.comp Scheme _ (Spec (CommRingCat.of (ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)))) (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) _ (bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ResidueField ↥A)) (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)))))) = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ResidueField ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫ ιFin p (ΓM M H) hj :=
    bcChart_fst (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _)
  have hKsnd : ∀ {Z : Scheme} (h : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Z),
      (@CategoryStruct.comp Scheme _ (Spec (CommRingCat.of (ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)))) (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) _ (bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ResidueField ↥A)) ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))))) ≫ h)) = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ResidueField ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj)))) ≫ h := by
    intro Z h
    have h0 : (@CategoryStruct.comp Scheme _ (Spec (CommRingCat.of (ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)))) (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) _ (bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ResidueField ↥A)) (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A)))))) = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ResidueField ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj)))) :=
      bcChart_snd (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _)
    rw [← Category.assoc, h0]

  have hR : (((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))).comp (Algebra.TensorProduct.includeRight (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom = (Algebra.TensorProduct.includeRight (R := R p) (A := ResidueField ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom := by
    ext b
    show (Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) ((1 : ↥A) ⊗ₜ[R p] b) = (1 : ResidueField ↥A) ⊗ₜ[R p] b
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  have hL : (((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))).comp (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) = (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ResidueField ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).comp (IsLocalRing.residue ↥A) := by
    ext a
    show (Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) (a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓM M H) hj))) = (IsLocalRing.residue ↥A a) ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓM M H) hj))
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, hbc₁, hKfst, bcChart_fst, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hR]
  · rw [Category.assoc, Category.assoc, hbc₂, hKsnd, bcChart_snd, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hL]

set_option maxHeartbeats 3200000 in

theorem exists_fibre_point_bc_eq_bcChart (bc : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    (P : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) [hP : P.IsPrime]
    (hle : (IsLocalRing.maximalIdeal ↥A).map (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) ≤ P) :
    ∃ z : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))), bc.base z = (bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ↥A)).base ⟨P, hP⟩ := by
  classical

  have hsurj : Function.Surjective ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) :=
    Algebra.TensorProduct.map_surjective (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj)) IsLocalRing.residue_surjective Function.surjective_id
  have hkerA : RingHom.ker (Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) =
      (IsLocalRing.maximalIdeal ↥A).map (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) := by

    apply le_antisymm
    · rw [Algebra.TensorProduct.rTensor_ker (R := R p) (C := ↥(chartAlgFin p (ΓM M H) hj)) (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) IsLocalRing.residue_surjective]
      refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
      have ha' : a ∈ IsLocalRing.maximalIdeal ↥A := by
        rw [RingHom.mem_ker] at ha
        exact (IsLocalRing.residue_eq_zero_iff a).mp ha
      exact Ideal.mem_comap.mpr (Ideal.mem_map_of_mem _ ha')
    · refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul,
        map_one]
      have : (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) a = 0 := (IsLocalRing.residue_eq_zero_iff a).mpr ha
      rw [this, TensorProduct.zero_tmul]
  have hkerP : RingHom.ker ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) ≤ P := by rw [RingHom.ker_coe_toRingHom, hkerA]; exact hle

  haveI hP' : (P.map ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))).IsPrime := Ideal.map_isPrime_of_surjective hsurj hkerP
  have hcomap : (P.map ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))).comap ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) = P := by
    rw [Ideal.comap_map_of_surjective _ hsurj]
    exact sup_eq_left.mpr hkerP
  have h𝔮 : (Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)))).base (⟨P.map ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), hP'⟩ : PrimeSpectrum (ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) =
      (⟨P, hP⟩ : PrimeSpectrum (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) :=
    PrimeSpectrum.ext hcomap

  refine ⟨(bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ResidueField ↥A)).base ⟨P.map ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), hP'⟩, ?_⟩
  have h := congrArg (fun φ => φ.base (⟨P.map ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), hP'⟩ : PrimeSpectrum (ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))))
    (specMap_comp_bcChart_eq_bcChart_comp p M H hj A bc hbc₁ hbc₂)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
  rw [h𝔮] at h
  exact h.symm

end FibrePoint
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const.BranchReadSkel"

section Reduced

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (𝔛 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [Algebra (R p) ↥A]
  (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ))

include 𝔛 hA hρ in
set_option maxHeartbeats 1600000 in
theorem isRadical_map_maximalIdeal :
    ((IsLocalRing.maximalIdeal ↥A).map (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj)))).IsRadical := by

  haveI hfib : IsReduced (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A))))) := 𝔛.fibre_reduced A hA (algebraMap (R p) ↥A) hρ

  have θκ := BranchReadSkel.θ (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _)
    (𝟙 (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A)))))) (K := ResidueField ↥A)
  haveI hκB : IsReduced (ResidueField ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) :=
    isReduced_of_injective θκ.commRingCatIsoToRingEquiv.symm θκ.commRingCatIsoToRingEquiv.symm.injective

  have hsurj : Function.Surjective (Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) :=
    Algebra.TensorProduct.map_surjective (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj)) IsLocalRing.residue_surjective Function.surjective_id
  have hker : RingHom.ker (Algebra.TensorProduct.map (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) (AlgHom.id (R p) ↥(chartAlgFin p (ΓM M H) hj))) =
      (IsLocalRing.maximalIdeal ↥A).map (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) := by

    apply le_antisymm
    · rw [Algebra.TensorProduct.rTensor_ker (R := R p) (C := ↥(chartAlgFin p (ΓM M H) hj)) (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) IsLocalRing.residue_surjective]
      refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
      have ha' : a ∈ IsLocalRing.maximalIdeal ↥A := by
        rw [RingHom.mem_ker] at ha
        exact (IsLocalRing.residue_eq_zero_iff a).mp ha
      exact Ideal.mem_comap.mpr (Ideal.mem_map_of_mem _ ha')
    · refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul,
        map_one]
      have : (IsScalarTower.toAlgHom (R p) ↥A (ResidueField ↥A)) a = 0 := (IsLocalRing.residue_eq_zero_iff a).mpr ha
      rw [this, TensorProduct.zero_tmul]

  rw [← hker]
  exact (RingHom.ker_isRadical_iff_reduced_of_surjective hsurj).mpr hκB

end Reduced
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const.BranchReadSkel"

section Minimal

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (𝔛 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [Algebra (R p) ↥A]
  (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ))

set_option maxHeartbeats 1600000 in

theorem comap_includeLeftRingHom_eq_maximalIdeal (bc : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    (𝔯 : PrimeSpectrum (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (h𝔯 : (bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ↥A)).base 𝔯 = ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) ≫ bc).base (genericPoint (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C)) :
    𝔯.asIdeal.comap (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) = IsLocalRing.maximalIdeal ↥A := by

  have ha := congrArg (fun φ => φ.base 𝔯)
    (bcChart_snd (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ↥A))
  have hb := congrArg (fun φ => φ.base (((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).base (genericPoint (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C))) hbc₂
  have hc := h𝔯
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at ha hb hc
  have h1 : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))))).base 𝔯 =
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))).base
        ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))))).base ((𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0).base ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ).base (genericPoint (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C)))) := by
    rw [← ha, hc, hb]

  have h2 := congrArg PrimeSpectrum.asIdeal h1
  have h3 : ∀ x : ↥(Spec (CommRingCat.of (ResidueField ↥A))),
      ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))).base x).asIdeal = IsLocalRing.maximalIdeal ↥A := by
    intro x
    have hx : x.asIdeal = ⊥ := by
      haveI := x.isPrime
      exact Ideal.eq_bot_of_prime x.asIdeal
    show Ideal.comap (IsLocalRing.residue ↥A) x.asIdeal = _
    rw [hx, ← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]
  rw [h3] at h2
  exact h2

set_option maxHeartbeats 1600000 in

theorem eq_of_isPrime_of_le (bc : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    (𝔯 : PrimeSpectrum (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (h𝔯 : (bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ↥A)).base 𝔯 = ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) ≫ bc).base (genericPoint (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C))
    (P : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) [hP : P.IsPrime]
    (hle : (IsLocalRing.maximalIdeal ↥A).map (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) ≤ P) (hP𝔯 : P ≤ 𝔯.asIdeal) :
    P = 𝔯.asIdeal := by
  classical
  haveI := isClosedImmersion_bc p M H hj A bc hbc₁ hbc₂
  haveI := 𝔛.comp_isClosedImmersion A hA (algebraMap (R p) ↥A) hρ 0
  haveI := 𝔛.comp_isClosedImmersion A hA (algebraMap (R p) ↥A) hρ 1

  obtain ⟨z, hz⟩ := exists_fibre_point_bc_eq_bcChart p M H hj A bc hbc₁ hbc₂ P hle
  have hsp0 : (⟨P, hP⟩ : PrimeSpectrum (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) ⤳ 𝔯 := (PrimeSpectrum.le_iff_specializes _ _).mp hP𝔯
  have hsp1 := hsp0.map (bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ↥A)).continuous
  rw [← hz, h𝔯] at hsp1
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hsp1
  have hzη : z ⤳ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0).base ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ).base (genericPoint (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C)) := bc.isClosedEmbedding.isInducing.specializes_iff.mp hsp1
  rcases 𝔛.comp_jointly_surjective A hA (algebraMap (R p) ↥A) hρ z with ⟨y, hy⟩ | ⟨y, hy⟩
  ·
    rw [← hy] at hzη
    have hyη : y ⤳ (𝔛.efib A hA (algebraMap (R p) ↥A) hρ).base (genericPoint (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C) := ((𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).isClosedEmbedding.isInducing.specializes_iff.mp hzη
    have hym : y = (𝔛.efib A hA (algebraMap (R p) ↥A) hρ).base ((inv (𝔛.efib A hA (algebraMap (R p) ↥A) hρ)).base y) := (BranchReadSkel.base_inv_base_apply (𝔛.efib A hA (algebraMap (R p) ↥A) hρ) y).symm
    rw [hym] at hyη
    have hmη : (inv (𝔛.efib A hA (algebraMap (R p) ↥A) hρ)).base y ⤳ (genericPoint (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C) := ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ)).isOpenEmbedding.isInducing.specializes_iff.mp hyη
    have hmeq : (inv (𝔛.efib A hA (algebraMap (R p) ↥A) hρ)).base y = (genericPoint (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C) := (hmη.antisymm (genericPoint_specializes _)).eq
    have hzη' : bc.base z = ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) ≫ bc).base (genericPoint (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C) := by
      rw [← hy, hym, hmeq]
      simp only [Scheme.Hom.comp_base, TopCat.comp_app]
    rw [hz, ← h𝔯] at hzη'
    exact congrArg PrimeSpectrum.asIdeal ((bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ↥A)).isOpenEmbedding.injective hzη')
  ·
    exfalso
    have hmem : (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0).base ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ).base (genericPoint (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C)) ∈ Set.range (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1).base :=
      ((𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)).isClosedEmbedding.isClosed_range.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨y, hy⟩) hzη.mem_closure

    have hrange : ∀ i : Fin 2, Set.range ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ 𝔛.comp A hA (algebraMap (R p) ↥A) hρ i).base = Set.range (𝔛.comp A hA (algebraMap (R p) ↥A) hρ i).base := by
      intro i
      ext w
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.mem_range, Function.comp_apply]
      constructor
      · rintro ⟨u, rfl⟩; exact ⟨_, rfl⟩
      · rintro ⟨x, rfl⟩
        obtain ⟨u, rfl⟩ := ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ)).surjective x
        exact ⟨u, rfl⟩
    have hne : Set.range ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)).base ≠ Set.range ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)).base := by
      rw [hrange 0, hrange 1]
      exact (𝔛.range_comp_ne A hA (algebraMap (R p) ↥A) hρ).symm
    have hC : ∀ w : ↥(𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C, w ≠ genericPoint _ → IsClosed ({w} : Set _) := fun w hw =>
      AlgebraicCurve.isClosed_singleton_of_ne_genericPoint (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).toBase w hw
    refine false_of_genericPoint_mem_range hC ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 1)) ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0)) hne ?_
    rw [hrange 1]
    simpa only [Scheme.Hom.comp_base, TopCat.comp_app] using hmem

end Minimal
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const.BranchReadSkel"

section Maximal

theorem map_eq_maximalIdeal_of_isRadical_of_forall_eq {T : Type*} [CommRing T] (I 𝔯 : Ideal T) [𝔯.IsPrime]
    (hrad : I.IsRadical) (hI : I ≤ 𝔯) (hmin : ∀ P : Ideal T, P.IsPrime → I ≤ P → P ≤ 𝔯 → P = 𝔯) :
    I.map (algebraMap T (Localization.AtPrime 𝔯)) = IsLocalRing.maximalIdeal (Localization.AtPrime 𝔯) := by
  apply le_antisymm
  · rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hI
  · have hradS : (I.map (algebraMap T (Localization.AtPrime 𝔯))).IsRadical := by
      rw [← Ideal.radical_eq_iff, ← IsLocalization.map_radical 𝔯.primeCompl (Localization.AtPrime 𝔯), hrad.radical]
    rw [← hradS.radical, Ideal.radical_eq_sInf]
    refine le_sInf fun Q hQ => ?_
    obtain ⟨hQI, hQ⟩ := hQ
    haveI := hQ
    have h1 : I ≤ Q.comap (algebraMap T (Localization.AtPrime 𝔯)) := Ideal.map_le_iff_le_comap.mp hQI
    have h2 : Q.comap (algebraMap T (Localization.AtPrime 𝔯)) ≤ 𝔯 := by
      have h := Ideal.comap_mono (f := algebraMap T (Localization.AtPrime 𝔯)) (IsLocalRing.le_maximalIdeal hQ.ne_top)
      rwa [show (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔯)).comap (algebraMap T (Localization.AtPrime 𝔯)) = 𝔯
        from Localization.AtPrime.under_maximalIdeal] at h
    have h3 := hmin _ (Ideal.comap_isPrime _ Q) h1 h2
    have h4 : Ideal.map (algebraMap T (Localization.AtPrime 𝔯)) (Q.comap (algebraMap T (Localization.AtPrime 𝔯))) = Q :=
      IsLocalization.map_under 𝔯.primeCompl (Localization.AtPrime 𝔯) Q
    rw [h3, Localization.AtPrime.map_eq_maximalIdeal] at h4
    exact h4.le

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (𝔛 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [Algebra (R p) ↥A]
  (hρ : A.subtype.comp (algebraMap (R p) ↥A) = algebraMap (R p) (AlgebraicClosure ℚ))

set_option maxHeartbeats 1600000 in

theorem map_maximalIdeal_localization_eq (bc : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp (algebraMap (R p) ↥A))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
    (𝔯 : PrimeSpectrum (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (h𝔯 : (bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ↥A)).base 𝔯 = ((𝔛.efib A hA (algebraMap (R p) ↥A) hρ) ≫ (𝔛.comp A hA (algebraMap (R p) ↥A) hρ 0) ≫ bc).base (genericPoint (𝔛.Mfib A hA (algebraMap (R p) ↥A) hρ).C)) :
    ((IsLocalRing.maximalIdeal ↥A).map (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj)))).map (algebraMap (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) (Localization.AtPrime 𝔯.asIdeal)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime 𝔯.asIdeal) :=
  map_eq_maximalIdeal_of_isRadical_of_forall_eq _ 𝔯.asIdeal (isRadical_map_maximalIdeal p M H hpM hj 𝔛 A hA hρ)
    (Ideal.map_le_iff_le_comap.mpr (comap_includeLeftRingHom_eq_maximalIdeal p M H hpM hj 𝔛 A hA hρ bc hbc₁ hbc₂ 𝔯 h𝔯).ge)
    (fun P hP h1 h2 => by haveI := hP; exact eq_of_isPrime_of_le p M H hpM hj 𝔛 A hA hρ bc hbc₁ hbc₂ 𝔯 h𝔯 P h1 h2)

end Maximal
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const.BranchReadSkel"

section Export

set_option maxHeartbeats 3200000 in

theorem isMaximal_map_maximalIdeal_localization_genericPrime
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥Pl] (halg : algebraMap (R p) ↥Pl = ρ)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))
    (ιT : Spec (CommRingCat.of (↥Pl ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hιT₁ : ιT ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥Pl) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫
        ιFin p (ΓM M H) hj)
    (hιT₂ : ιT ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥Pl) (B := ↥(chartAlgFin p (ΓM M H) hj)))))
    (𝔯 : ↥(Spec (CommRingCat.of (↥Pl ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)))))
    (h𝔯 : ιT.base 𝔯 = (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) :
    ((IsLocalRing.maximalIdeal ↥Pl).map ((algebraMap (↥Pl ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) (Localization.AtPrime 𝔯.asIdeal)).comp
      (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥Pl) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom)).IsMaximal := by
  subst halg

  have hι : ιT = (bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ↥Pl)) :=
    pullback.hom_ext (hιT₁.trans (bcChart_fst _ _ _).symm) (hιT₂.trans (bcChart_snd _ _ _).symm)
  rw [hι] at h𝔯
  have hincl : (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥Pl) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom =
      Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥Pl) (B := ↥(chartAlgFin p (ΓM M H) hj)) := rfl
  rw [hincl, ← Ideal.map_map, map_maximalIdeal_localization_eq p M H hpM hj 𝔛 Pl hPl hρ bc hbc₁ hbc₂ 𝔯 h𝔯]
  exact IsLocalRing.maximalIdeal.isMaximal _

end Export
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const.BranchReadSkel"

end EtaVal29
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const.BranchReadSkel"

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const.BranchReadSkel"

namespace EtaValPieces
open ModularCurve

set_option maxHeartbeats 3200000 in

theorem etaEmb_injective

    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))

    (hsp : gA.base (genericPoint 𝔛.Meta.C) ⤳ (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) :
    Function.Injective
      (𝔛.Meta.ffEquiv.symm.toRingHom.comp
        ((gA.stalkMap (genericPoint 𝔛.Meta.C)).hom.comp
          ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes hsp).hom)) := by
  obtain ⟨hint, -, hopen⟩ :=
    ModularCurve.XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
      p M hpM H Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂
  haveI := hint
  haveI := hopen
  rw [RingHom.coe_comp, RingHom.coe_comp]
  refine 𝔛.Meta.ffEquiv.symm.injective.comp (Function.Injective.comp ?_ ?_)
  · exact (asIso (gA.stalkMap (genericPoint 𝔛.Meta.C))).commRingCatIsoToRingEquiv.injective
  · have hgen : genericPoint _ ⤳ gA.base (genericPoint 𝔛.Meta.C) :=
      (genericPoint_spec _).specializes trivial
    have hinj : Function.Injective ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes (hgen.trans hsp)).hom :=
      IsFractionRing.injective ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))) (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField
    rw [← TopCat.Presheaf.stalkSpecializes_comp _ hgen hsp, CommRingCat.hom_comp, RingHom.coe_comp] at hinj
    exact hinj.of_comp

set_option maxHeartbeats 3200000 in

theorem etaEmb_const

    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))

    (hsp : gA.base (genericPoint 𝔛.Meta.C) ⤳ (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))
    (a : ↥Pl) :
    𝔛.Meta.ffEquiv.symm ((gA.stalkMap (genericPoint 𝔛.Meta.C)).hom
      (((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes hsp).hom
        ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.germ ⊤ ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) trivial ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a))))) =
      algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) := by
  apply 𝔛.Meta.ffEquiv.injective
  rw [RingEquiv.apply_symm_apply, 𝔛.Meta.ffEquiv_algebraMap]

  have h1 : gA.appTop.hom ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a)) =
      𝔛.Meta.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).inv.hom (a : AlgebraicClosure ℚ)) := by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, hgA₂, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.comp_apply]
    congr 1
    change ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv ≫ (Spec.map (CommRingCat.ofHom Pl.subtype)).appTop).hom a = _
    rw [← Scheme.ΓSpecIso_inv_naturality]
    rfl
  have e1 := TopCat.Presheaf.germ_stalkSpecializes_apply (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf (U := ⊤) (trivial : ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) ∈ (⊤ : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)) hsp ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a))
  erw [e1]
  erw [Scheme.Hom.germ_stalkMap_apply gA ⊤ (genericPoint 𝔛.Meta.C) trivial]
  change (𝔛.Meta.C.presheaf.germ ⊤ (genericPoint 𝔛.Meta.C) trivial).hom (gA.appTop.hom _) = _
  rw [h1]
  rfl

set_option maxHeartbeats 3200000 in

theorem etaRes_const

    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))

    (hsp : gA.base (genericPoint 𝔛.Meta.C) ⤳ (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))
    (a : ↥Pl) :
    (𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)).hom
        ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.germ ⊤ ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) trivial ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a)))) =
      algebraMap (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))
        (IsLocalRing.residue ↥Pl a) := by
  apply (𝔛.Mfib Pl hPl ρ hρ).ffEquiv.injective
  rw [RingEquiv.apply_symm_apply, (𝔛.Mfib Pl hPl ρ hρ).ffEquiv_algebraMap]
  have ht : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ≫ pullback.snd _ _ = (𝔛.Mfib Pl hPl ρ hρ).toBase ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) := by
    rw [Category.assoc, Category.assoc, hbc₂, reassoc_of% (𝔛.comp_over Pl hPl ρ hρ 0), reassoc_of% (𝔛.hefib Pl hPl ρ hρ)]
  have h1 : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).appTop.hom ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a)) =
      (𝔛.Mfib Pl hPl ρ hρ).toBase.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField ↥Pl))).inv.hom (IsLocalRing.residue ↥Pl a)) := by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, ht, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.comp_apply]
    congr 1
    change ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl))).appTop).hom a = _
    rw [← Scheme.ΓSpecIso_inv_naturality]
    rfl
  erw [Scheme.Hom.germ_stalkMap_apply (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⊤ (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C) trivial]
  change ((𝔛.Mfib Pl hPl ρ hρ).C.presheaf.germ ⊤ (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C) trivial).hom ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).appTop.hom _) = _
  rw [h1]
  rfl

end EtaValPieces
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const.BranchReadSkel"

namespace GENERICPT

open ModularCurve

set_option maxHeartbeats 3200000 in

theorem exists_mem_integers_and_coe_res_eq_coe_residue

    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))

    (Rg : AlgebraicCurve.RegularProlongation Pl ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)))
    (hRg₁ : ∀ f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))), f ∈ Rg.integers ↔
        ∃ x y : LaurentSeries ↥Pl, ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 ∧
          (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap Pl.subtype y = ModularCurve.coeffMap Pl.subtype x)
    (hRg₂ : ∀ (y : LaurentSeries ↥Pl) (hy : ModularCurve.coeffMap Pl.subtype y ∈ ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))),
        ∃ hO : (⟨ModularCurve.coeffMap Pl.subtype y, hy⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers,
          ((Rg.residue ⟨_, hO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y)
    (hRg₃ : ∀ (f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) (hf : f ∈ Rg.integers) (x y : LaurentSeries ↥Pl),
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 →
        (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap Pl.subtype y = ModularCurve.coeffMap Pl.subtype x →
        ((Rg.residue ⟨f, hf⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) * ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y =
          ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) x)

    (hsp : gA.base (genericPoint 𝔛.Meta.C) ⤳ (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) :
    letI emb : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))) →+* ↥(ModularCurve.xHFunctionFieldBar M H) :=
      𝔛.Meta.ffEquiv.symm.toRingHom.comp
        ((gA.stalkMap (genericPoint 𝔛.Meta.C)).hom.comp
          ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes hsp).hom)
    letI res : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))) →+* ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM)) :=
      (𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)).hom
    ∀ g : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))),
      ∃ hO : (emb g : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers,
        ((res g : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
          ((Rg.residue ⟨emb g, hO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) := by
  intro g
  let emb : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))) →+* ↥(ModularCurve.xHFunctionFieldBar M H) :=
    𝔛.Meta.ffEquiv.symm.toRingHom.comp
      ((gA.stalkMap (genericPoint 𝔛.Meta.C)).hom.comp
        ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes hsp).hom)
  let res : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))) →+* ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM)) :=
    (𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)).hom

  obtain ⟨U, hηU, s, hs⟩ := (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.exists_germ_eq g

  haveI : JacobsonSpace ↥(𝔛.Mfib Pl hPl ρ hρ).C :=
    LocallyOfFiniteType.jacobsonSpace (𝔛.Mfib Pl hPl ρ hρ).toBase
  have hgenV : genericPoint (𝔛.Mfib Pl hPl ρ hρ).C ∈ (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U := hηU
  obtain ⟨P, hPV, hPcl⟩ := nonempty_inter_closedPoints (X := ↥(𝔛.Mfib Pl hPl ρ hρ).C)
    (Z := (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U : (𝔛.Mfib Pl hPl ρ hρ).C.Opens) : Set ↥(𝔛.Mfib Pl hPl ρ hρ).C)) ⟨_, hgenV⟩ ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U).2.isLocallyClosed
  have hzU : bc.base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base P) ∈ U := by
    have : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base P ∈ U := hPV
    simpa only [Scheme.Hom.comp_apply] using this

  have hne : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U)) := ⟨⟨genericPoint 𝔛.Meta.C, hsp.mem_open U.2 hηU⟩⟩
  obtain ⟨hneM, xs, ys, hys, hgen, hred, -⟩ :=
    ModularCurve.XHDRModelAtP.exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂ bc hbc₁ hbc₂ ⟨P, hPcl⟩ U hzU hne s

  have E1 : emb g = 𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom s)) := by
    show 𝔛.Meta.ffEquiv.symm ((gA.stalkMap (genericPoint 𝔛.Meta.C)).hom (((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes hsp).hom g)) = _
    rw [← hs, TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]

  haveI := hneM
  have E2 : res g = (𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm ((𝔛.Mfib Pl hPl ρ hρ).C.germToFunctionField ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U) (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).app U).hom s)) := by
    show (𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)).hom g) = _
    rw [← hs, Scheme.Hom.germ_stalkMap_apply]
  have hgen' : ((emb g : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) : LaurentSeries (AlgebraicClosure ℚ)) *
      ModularCurve.coeffMap Pl.subtype ys = ModularCurve.coeffMap Pl.subtype xs := by
    rw [E1]; exact hgen
  have hO : (emb g : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers :=
    (hRg₁ _).mpr ⟨xs, ys, hys, hgen'⟩
  refine ⟨hO, ?_⟩
  have h3 := hRg₃ _ hO xs ys hys hgen'
  rw [E2]
  apply mul_right_cancel₀ hys
  rw [h3]
  exact hred

end GENERICPT
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const.BranchReadSkel"

open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

namespace ETAGLUE

open ModularCurve

theorem injective_emb_and_isFractionRing
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (η : ↥(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hsp : gA.base (genericPoint 𝔛.Meta.C) ⤳ η) :
    letI emb : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk η) →+* ↥(ModularCurve.xHFunctionFieldBar M H) :=
      𝔛.Meta.ffEquiv.symm.toRingHom.comp
        ((gA.stalkMap (genericPoint 𝔛.Meta.C)).hom.comp
          ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes hsp).hom)
    Function.Injective emb ∧
    @IsFractionRing ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk η) _
      ↥(ModularCurve.xHFunctionFieldBar M H) _ emb.toAlgebra := by
  set emb : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk η) →+* ↥(ModularCurve.xHFunctionFieldBar M H) :=
      𝔛.Meta.ffEquiv.symm.toRingHom.comp
        ((gA.stalkMap (genericPoint 𝔛.Meta.C)).hom.comp
          ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes hsp).hom) with hembdef
  obtain ⟨hint, -, hopen⟩ := ModularCurve.XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
    p M hpM H Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂
  haveI := hint
  haveI := hopen
  haveI := 𝔛.Meta.isIntegral
  have hgen : gA.base (genericPoint 𝔛.Meta.C) = genericPoint ↥(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) := genericPoint_eq_of_isOpenImmersion gA

  let iso1 : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk (genericPoint ↥(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))) ≅ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk (gA.base (genericPoint 𝔛.Meta.C)) :=
    (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkCongr (Inseparable.of_eq hgen.symm)
  let iso2 : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk (gA.base (genericPoint 𝔛.Meta.C)) ≅ 𝔛.Meta.C.presheaf.stalk (genericPoint 𝔛.Meta.C) :=
    asIso (gA.stalkMap (genericPoint 𝔛.Meta.C))
  let E : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField ≃+* ↥(ModularCurve.xHFunctionFieldBar M H) := (iso1 ≪≫ iso2).commRingCatIsoToRingEquiv.trans 𝔛.Meta.ffEquiv.symm
  have hemb : emb = E.toRingHom.comp (algebraMap ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk η) (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField) := by
    have hsp0 : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes ((genericPoint_spec ↥(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))).specializes (Set.mem_univ η)) ≫ iso1.hom =
        (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes hsp := by
      simp only [iso1, TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_comp]
    rw [hembdef]
    change _ = (𝔛.Meta.ffEquiv.symm.toRingHom.comp ((iso1 ≪≫ iso2).hom.hom)).comp ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes _).hom
    rw [← hsp0]
    rfl
  have hinjE : Function.Injective (algebraMap ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk η) (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField) := IsFractionRing.injective _ _
  refine ⟨?_, ?_⟩
  · rw [hemb]; exact E.injective.comp hinjE
  · have := (IsLocalization.isLocalization_iff_of_ringEquiv (nonZeroDivisors ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk η)) E).mp
      (inferInstance : IsFractionRing ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk η) (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField)
    convert this using 2

end ETAGLUE
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const.BranchReadSkel"

namespace EtaValGL3
open ModularCurve

set_option maxHeartbeats 3200000 in
theorem isFractionRing_emb
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))
    (hsp : gA.base (genericPoint 𝔛.Meta.C) ⤳ (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) :
    @IsFractionRing ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))) _ ↥(ModularCurve.xHFunctionFieldBar M H) _
      (RingHom.toAlgebra (𝔛.Meta.ffEquiv.symm.toRingHom.comp
        ((gA.stalkMap (genericPoint 𝔛.Meta.C)).hom.comp
          ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes hsp).hom))) :=
  (ETAGLUE.injective_emb_and_isFractionRing p M hpM H Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂ ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) hsp).2

end EtaValGL3
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const.BranchReadSkel"

namespace EtaVal
open ModularCurve

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem core (p : ℕ) [Fact p.Prime]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥Pl] (halg : algebraMap (R p) ↥Pl = ρ)
    (A : Type) [CommRing A] [Algebra (R p) A] [Algebra.FiniteType (R p) A] [Module.Flat (R p) A]
    (𝔯 : Ideal (↥Pl ⊗[R p] A)) [𝔯.IsPrime]
    (O : Type) [CommRing O] [IsLocalRing O] [Algebra (↥Pl ⊗[R p] A) O] [IsLocalization.AtPrime O 𝔯]
    (h𝔭eq : (IsLocalRing.maximalIdeal ↥Pl).map ((algebraMap (↥Pl ⊗[R p] A) (Localization.AtPrime 𝔯)).comp
        (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥Pl) (B := A)).toRingHom) =
      IsLocalRing.maximalIdeal (Localization.AtPrime 𝔯))
    (K : Type) [Field K] (emb : O →+* K) (hinj : Function.Injective emb)
    (hfrac : @IsFractionRing O _ K _ emb.toAlgebra) :
    (∃ V : ValuationSubring K, emb.range = V.toSubring) ∧
      (IsLocalRing.maximalIdeal ↥Pl).map ((algebraMap (↥Pl ⊗[R p] A) O).comp
        (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥Pl) (B := A)).toRingHom) = IsLocalRing.maximalIdeal O := by
  classical

  let eA : Localization.AtPrime 𝔯 ≃ₐ[↥Pl ⊗[R p] A] O := IsLocalization.algEquiv 𝔯.primeCompl (Localization.AtPrime 𝔯) O
  set toS : ↥Pl →+* Localization.AtPrime 𝔯 := (algebraMap (↥Pl ⊗[R p] A) (Localization.AtPrime 𝔯)).comp
    (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥Pl) (B := A)).toRingHom with htoSdef
  set toO : ↥Pl →+* O := (algebraMap (↥Pl ⊗[R p] A) O).comp
    (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥Pl) (B := A)).toRingHom with htoOdef
  have heA : (eA : Localization.AtPrime 𝔯 →+* O).comp toS = toO := by
    ext o
    simp only [htoSdef, htoOdef, RingHom.comp_apply]
    exact eA.commutes _
  haveI h𝔭 : ((maximalIdeal ↥Pl).map toS).IsPrime := by rw [h𝔭eq]; infer_instance

  have htoO : ∀ o : ↥Pl, toO o = eA (toS o) := fun o => by rw [← heA]; rfl
  have hmax : (maximalIdeal ↥Pl).map toO = maximalIdeal O := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro o ho
      rw [Ideal.mem_comap, htoO]
      have hmem : toS o ∈ maximalIdeal (Localization.AtPrime 𝔯) := by
        rw [← h𝔭eq]; exact Ideal.mem_map_of_mem toS ho
      by_contra hcontra
      have hu : IsUnit (eA (toS o)) := IsLocalRing.notMem_maximalIdeal.mp hcontra
      have hu' : IsUnit (toS o) := by simpa using hu.map eA.symm
      exact IsLocalRing.notMem_maximalIdeal.mpr hu' hmem
    · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔯 O, Ideal.map_le_iff_le_comap]
      intro t ht
      rw [Ideal.mem_comap]
      have h1 : algebraMap _ (Localization.AtPrime 𝔯) t ∈ maximalIdeal (Localization.AtPrime 𝔯) :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔯) 𝔯 t).mpr ht
      rw [← h𝔭eq] at h1
      have h2 := Ideal.mem_map_of_mem (eA : Localization.AtPrime 𝔯 →+* O) h1
      rw [Ideal.map_map, heA] at h2
      have h3 : (eA : Localization.AtPrime 𝔯 →+* O) (algebraMap _ (Localization.AtPrime 𝔯) t) = algebraMap _ O t :=
        eA.commutes t
      rw [h3] at h2
      exact h2

  have h𝔔 : 𝔯.comap (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥Pl) (B := A)).toRingHom =
      maximalIdeal ↥Pl := by
    ext x
    rw [Ideal.mem_comap, ← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔯) 𝔯]
    show toS x ∈ maximalIdeal (Localization.AtPrime 𝔯) ↔ _
    constructor
    · intro h
      by_contra hx
      exact IsLocalRing.notMem_maximalIdeal.mpr ((IsLocalRing.notMem_maximalIdeal.mp hx).map toS) h
    · intro hx
      rw [← h𝔭eq]
      exact Ideal.mem_map_of_mem toS hx

  letI : Algebra O K := emb.toAlgebra
  haveI : IsFractionRing O K := hfrac
  let h : O ≃+* Localization.AtPrime 𝔯 := eA.toRingEquiv.symm
  letI algSK : Algebra (Localization.AtPrime 𝔯) K := ((algebraMap O K).comp h.symm.toRingHom).toAlgebra
  have halgSK : ∀ s, algebraMap (Localization.AtPrime 𝔯) K s = emb (eA s) := fun s => rfl
  haveI : IsDomain (Localization.AtPrime 𝔯) := by
    refine Function.Injective.isDomain (algebraMap (Localization.AtPrime 𝔯) K) (fun x y hxy => ?_)
    rw [halgSK, halgSK] at hxy
    exact eA.injective (hinj hxy)
  haveI : IsDomain O := Function.Injective.isDomain emb hinj
  haveI : IsFractionRing (Localization.AtPrime 𝔯) K := by
    have h1 := IsLocalization.isLocalization_of_base_ringEquiv (nonZeroDivisors O) K h
    have h2 : (nonZeroDivisors O).map h = nonZeroDivisors (Localization.AtPrime 𝔯) := by
      ext x
      simp only [Submonoid.mem_map, mem_nonZeroDivisors_iff_ne_zero]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (map_ne_zero_iff h h.injective).mpr hy
      · intro hx
        exact ⟨h.symm x, (map_ne_zero_iff h.symm h.symm.injective).mpr hx, h.apply_symm_apply x⟩
    rw [h2] at h1
    exact h1

  obtain ⟨-, hdich⟩ :=
    Localization.AtPrime.mem_range_of_forall_comap_eq_bot_and_valuation_dichotomy_tensorProduct_valuationSubring_of_liesOverPrime
      p Pl hPl ρ hρ halg A 𝔯 h𝔔 h𝔭 K

  have hrange : ∀ a c : Localization.AtPrime 𝔯, c ∉ (maximalIdeal ↥Pl).map toS → ∀ k : K,
      k * algebraMap _ K c = algebraMap _ K a → k ∈ emb.range := by
    intro a c hc k hk
    rw [h𝔭eq] at hc
    obtain ⟨u, rfl⟩ := IsLocalRing.notMem_maximalIdeal.mp hc
    have hk' : k = algebraMap _ K (a * ↑u⁻¹) := by
      rw [map_mul, ← hk, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
    rw [hk', halgSK]
    exact ⟨_, rfl⟩
  refine ⟨⟨⟨emb.range, fun k => ?_⟩, rfl⟩, hmax⟩
  rcases hdich k with ⟨a, c, hc, hk⟩ | ⟨a, c, hc, hk⟩
  · exact Or.inl (hrange a c hc k hk)
  · exact Or.inr (hrange a c hc k⁻¹ hk)

theorem finish (p : ℕ) [Fact p.Prime]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p) [CharP (ResidueField ↥Pl) p]
    {F : Type*} [Field F] [Algebra (AlgebraicClosure ℚ) F] {Fbar : Type*} [Field Fbar] [Algebra (ResidueField ↥Pl) Fbar]
    (Rg : RegularProlongation Pl F Fbar)
    (O : Type*) [CommRing O] [IsLocalRing O] (β : ↥Pl →+* O)
    (hmax : (IsLocalRing.maximalIdeal ↥Pl).map β = IsLocalRing.maximalIdeal O)
    (emb : O →+* F) (hinj : Function.Injective emb)
    (hconst : ∀ a : ↥Pl, emb (β a) = algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ))
    (V : ValuationSubring F) (hV : emb.range = V.toSubring) (hVRg : V ≤ Rg.integers) :
    V ≠ ⊤ ∧ ∀ V' : ValuationSubring F, V ≤ V' → V' = V ∨ V' = ⊤ := by
  classical
  have hmemV : ∀ g, emb g ∈ V := fun g => by
    have : emb g ∈ emb.range := ⟨g, rfl⟩
    rw [hV] at this; exact this
  let ε0 : O →+* ↥V := emb.codRestrict V.toSubring hmemV
  have hε0 : Function.Bijective ε0 := by
    refine ⟨fun x y h => hinj (congrArg Subtype.val h), fun v => ?_⟩
    have hv : (v : F) ∈ emb.range := by rw [hV]; exact v.2
    obtain ⟨g, hg⟩ := hv
    exact ⟨g, Subtype.ext hg⟩
  let ε : O ≃+* ↥V := RingEquiv.ofBijective ε0 hε0
  let ιV : ↥Pl →+* ↥V := (ε : O →+* ↥V).comp β
  have hιV : ∀ a : ↥Pl, ((ιV a : ↥V) : F) = algebraMap (AlgebraicClosure ℚ) F (a : AlgebraicClosure ℚ) :=
    fun a => hconst a
  have hεmax : (IsLocalRing.maximalIdeal O).map (ε : O →+* ↥V) = IsLocalRing.maximalIdeal ↥V :=
    IsLocalRing.map_maximalIdeal_of_surjective (ε : O →+* ↥V) (fun x => ⟨ε.symm x, ε.apply_symm_apply x⟩)
  have hV𝔪 : IsLocalRing.maximalIdeal ↥V ≤ (IsLocalRing.maximalIdeal ↥Pl).map ιV := by
    rw [← Ideal.map_map, hmax, hεmax]
  obtain ⟨hVeq, hrank⟩ :=
    BranchReadE4.eq_integers_and_rankOne_of_le_integers_of_maximalIdeal_le p Pl hPl Rg V hVRg ιV hιV hV𝔪
  refine ⟨?_, hrank⟩
  intro htop
  have hpn := BranchReadE4.natCast_mem_nonunits_integers p Pl Rg
  obtain ⟨hpmem, hpmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hpn
  have hp0 : algebraMap (AlgebraicClosure ℚ) F (p : AlgebraicClosure ℚ) ≠ 0 := by
    rw [map_ne_zero_iff _ (algebraMap (AlgebraicClosure ℚ) F).injective]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hinv : (algebraMap (AlgebraicClosure ℚ) F (p : AlgebraicClosure ℚ))⁻¹ ∈ Rg.integers := by
    rw [← hVeq, htop]; exact ValuationSubring.mem_top _
  exact IsLocalRing.notMem_maximalIdeal.mpr
    (IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hp0))) hpmax

end EtaVal
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const.BranchReadSkel"

namespace EtaValFin
open ModularCurve TopologicalSpace

universe u

theorem walkingSpan_hom_some_eq (a b : WalkingPair) (φ : @Quiver.Hom WalkingSpan _ (some a) (some b)) : a = b := by
  rcases φ with ⟨⟩
  rfl

theorem walkingSpan_hom_none_eq (b : WalkingPair) (φ : @Quiver.Hom WalkingSpan _ none (some b)) : φ = WidePushoutShape.Hom.init b := by
  rcases φ with ⟨⟩
  rfl

theorem exists_eq_of_inr_eq_inl {W Y Z : Scheme.{u}} (f : W ⟶ Y) (g : W ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
    (z : Z) (y : Y) (h : (pushout.inr f g).base z = (pushout.inl f g).base y) :
    ∃ m : W, g.base m = z := by
  have h' : (colimit.ι (span f g) WalkingSpan.right).base z = (colimit.ι (span f g) WalkingSpan.left).base y := h
  obtain ⟨k, fi, fj, x, hx, -⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (span f g)).mp h'
  rcases k with _ | _ | _
  · rw [walkingSpan_hom_none_eq _ fi] at hx
    exact ⟨x, by first | exact hx | simpa using hx | (simp at hx; exact hx) | (simp ; exact hx) | (simp at hx ⊢; exact hx)⟩
  · exact absurd (walkingSpan_hom_some_eq _ _ fi) (by decide : WalkingPair.left ≠ WalkingPair.right)
  · exact absurd (walkingSpan_hom_some_eq _ _ fj) (by decide : WalkingPair.right ≠ WalkingPair.left)

variable (p : ℕ) [Fact p.Prime] (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

set_option synthInstance.maxHeartbeats 1600000 in

theorem range_fInf_eq :
    Set.range (TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)).base =
      (PrimeSpectrum.basicOpen (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)) :
        Set (PrimeSpectrum ↥(chartAlgInf p Γ hj))) := by
  letI := (TwoChartIntegralModel.inclInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)).toRingHom.toAlgebra
  haveI := TwoChartIntegralModel.isLocalization_away_inclInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)
  rw [Spec.map_base]
  exact PrimeSpectrum.localization_away_comap_range _ (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj))

variable {p hj}
variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}

theorem iotaInf_jInvChartInf (𝔓 : XHDRModelAtP p M H hpM hj) :
    𝔓.iotaInf (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)) =
      TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [𝔓.iotaInf_spec]
  simp only [TwoChartIntegralModel.jInvChartInf]
  push_cast
  rw [coe_jAt, coe_jAt]

set_option synthInstance.maxHeartbeats 1600000 in

theorem mem_range_ιFin_of_pi_mem (𝔓 : XHDRModelAtP p M H hpM hj) (z : X p (ΓM M H) hj)
    (hz : 𝔓.π.1.base z ∈ Set.range (ιFin p (ΓN p M H hpM) hj).base) : z ∈ Set.range (ιFin p (ΓM M H) hj).base := by
  rcases TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) z with h | ⟨q, rfl⟩
  · exact h
  have hπ : 𝔓.π.1.base ((ιInf p (ΓM M H) hj).base q) =
      (ιInf p (ΓN p M H hpM) hj).base ((Spec.map (CommRingCat.ofHom 𝔓.iotaInf.toRingHom)).base q) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    exact congrArg (fun f => f.base q) 𝔓.pi_chartInf
  rw [hπ] at hz
  obtain ⟨a, ha⟩ := hz
  obtain ⟨m, hm⟩ := exists_eq_of_inr_eq_inl (TwoChartIntegralModel.fFin (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj))
    (TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)) _ a ha.symm
  have hqN : (Spec.map (CommRingCat.ofHom 𝔓.iotaInf.toRingHom)).base q ∈
      Set.range (TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)).base := ⟨m, hm⟩
  rw [range_fInf_eq] at hqN
  have hqN' := (PrimeSpectrum.mem_basicOpen _ _).mp hqN
  rw [Spec.map_apply, CommRingCat.hom_ofHom, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    iotaInf_jInvChartInf 𝔓] at hqN'
  have hqM : q ∈ Set.range (TwoChartIntegralModel.fInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)).base := by
    rw [range_fInf_eq]
    exact (PrimeSpectrum.mem_basicOpen _ _).mpr hqN'
  obtain ⟨m', hm'⟩ := hqM
  refine ⟨(TwoChartIntegralModel.fFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)).base m', ?_⟩
  rw [← hm', ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
  exact congrArg (fun f => f.base m') (TwoChartIntegralModel.glue_condition (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem eta_mem_chartFin
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))
    (hsp : gA.base (genericPoint 𝔛.Meta.C) ⤳ (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) :
    ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) ∈ (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤) := by
  show (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) ∈ (ιFin p (ΓM M H) hj) ''ᵁ ⊤
  rw [Scheme.Hom.image_top_eq_opensRange]
  show _ ∈ Set.range _
  apply mem_range_ιFin_of_pi_mem 𝔛
  have h1 : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) =
      ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0) ≫ pullback.fst (toBase p (ΓM M H) hj)
        (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ)))).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C) := by
    rw [← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, hbc₁, Category.assoc]
  have hf : fibreMap 𝔛.π ((IsLocalRing.residue ↥Pl).comp ρ) ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ))) =
      pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ))) ≫ 𝔛.π.1 :=
    pullback.lift_fst _ _ _
  have h2 : ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0) ≫ pullback.fst (toBase p (ΓM M H) hj)
        (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ)))) ≫ 𝔛.π.1 =
      𝔛.efib Pl hPl ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ))) := by
    rw [Category.assoc, Category.assoc, ← hf, ← Category.assoc (𝔛.comp Pl hPl ρ hρ 0), 𝔛.comp_pi Pl hPl ρ hρ, Category.id_comp]
  rw [h1, ← Scheme.Hom.comp_apply, h2]
  obtain ⟨⟨x, hx⟩⟩ := 𝔛.Mfib_chart_nonempty Pl hPl ρ hρ
  have h4 : genericPoint (𝔛.Mfib Pl hPl ρ hρ).C ∈ (𝔛.efib Pl hPl ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ)))) ⁻¹ᵁ ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤) :=
    ((genericPoint_spec (𝔛.Mfib Pl hPl ρ hρ).C).mem_open_set_iff (Opens.isOpen _)).mpr ⟨x, trivial, hx⟩
  have h5 : (𝔛.efib Pl hPl ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ)))).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C) ∈
      (ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤ := h4
  rw [Scheme.Hom.image_top_eq_opensRange] at h5
  exact h5

end EtaValFin
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const.BranchReadSkel"

namespace EtaValBridge
open ModularCurve BranchReadSkel

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem exists_prime_algebra
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))
    (hsp : gA.base (genericPoint 𝔛.Meta.C) ⤳ (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))
    [Algebra (R p) ↥Pl] (halg : algebraMap (R p) ↥Pl = ρ)
    (ιT : Spec (CommRingCat.of (↥Pl ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hιT₁ : ιT ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥Pl) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫
        ιFin p (ΓM M H) hj)
    (hιT₂ : ιT ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥Pl) (B := ↥(chartAlgFin p (ΓM M H) hj)))))
    (hη : ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) ∈ (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)) :
    ∃ (𝔯 : PrimeSpectrum (↥Pl ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (alg : Algebra (↥Pl ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)))),
      @IsLocalization.AtPrime (↥Pl ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) _ ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))) _ alg 𝔯.asIdeal _ ∧
      ιT.base 𝔯 = ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) ∧
      ∀ o : ↥Pl, (((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.germ ⊤ ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) trivial).hom.comp
        ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv.hom)) o = @algebraMap (↥Pl ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))) _ _ alg (o ⊗ₜ 1) := by
  subst halg
  have hι : ιT = (BranchReadSkel.bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ↥Pl)) :=
    pullback.hom_ext (hιT₁.trans (bcChart_fst _ _ _).symm) (hιT₂.trans (bcChart_snd _ _ _).symm)
  subst hι
  let e₁ : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥Pl)))) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥Pl)))) := 𝟙 _
  let U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥Pl)))).Opens := (e₁ ≫ pullback.fst _ _) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)
  have hU : IsAffineOpen U := isAffineOpen_U (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) e₁
  have hηU : ((𝔛.efib Pl hPl (algebraMap (R p) ↥Pl) hρ ≫ 𝔛.comp Pl hPl (algebraMap (R p) ↥Pl) hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl (algebraMap (R p) ↥Pl) hρ).C)) ∈ U := by
    show (𝟙 (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥Pl)))) ≫ pullback.fst _ _).base ((𝔛.efib Pl hPl (algebraMap (R p) ↥Pl) hρ ≫ 𝔛.comp Pl hPl (algebraMap (R p) ↥Pl) hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl (algebraMap (R p) ↥Pl) hρ).C)) ∈ (ιFin p (ΓM M H) hj) ''ᵁ ⊤
    rw [Category.id_comp]; exact hη

  let θr : ↥Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥Pl)))), U) ≃+* (↥Pl ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) := (θ (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) e₁).commRingCatIsoToRingEquiv

  letI algU := (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥Pl)))).presheaf.algebra_section_stalk (⟨((𝔛.efib Pl hPl (algebraMap (R p) ↥Pl) hρ ≫ 𝔛.comp Pl hPl (algebraMap (R p) ↥Pl) hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl (algebraMap (R p) ↥Pl) hρ).C)), hηU⟩ : U)
  have hloc : IsLocalization.AtPrime ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥Pl)))).presheaf.stalk ((𝔛.efib Pl hPl (algebraMap (R p) ↥Pl) hρ ≫ 𝔛.comp Pl hPl (algebraMap (R p) ↥Pl) hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl (algebraMap (R p) ↥Pl) hρ).C))) (hU.primeIdealOf ⟨((𝔛.efib Pl hPl (algebraMap (R p) ↥Pl) hρ ≫ 𝔛.comp Pl hPl (algebraMap (R p) ↥Pl) hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl (algebraMap (R p) ↥Pl) hρ).C)), hηU⟩).asIdeal := hU.isLocalization_stalk ⟨((𝔛.efib Pl hPl (algebraMap (R p) ↥Pl) hρ ≫ 𝔛.comp Pl hPl (algebraMap (R p) ↥Pl) hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl (algebraMap (R p) ↥Pl) hρ).C)), hηU⟩
  set P := hU.primeIdealOf ⟨((𝔛.efib Pl hPl (algebraMap (R p) ↥Pl) hρ ≫ 𝔛.comp Pl hPl (algebraMap (R p) ↥Pl) hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl (algebraMap (R p) ↥Pl) hρ).C)), hηU⟩ with hPdef

  let 𝔯 : PrimeSpectrum (↥Pl ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) := ⟨P.asIdeal.comap (θr.symm : (↥Pl ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ↥Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥Pl)))), U)), inferInstance⟩
  have hM : P.asIdeal.primeCompl.map θr = 𝔯.asIdeal.primeCompl := by
    ext x
    simp only [Submonoid.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      intro hx
      apply hy
      have : θr.symm (θr y) ∈ P.asIdeal := hx
      rwa [θr.symm_apply_apply] at this
    · intro hx
      exact ⟨θr.symm x, hx, θr.apply_symm_apply x⟩
  have hloc2 := IsLocalization.isLocalization_of_base_ringEquiv P.asIdeal.primeCompl ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥Pl)))).presheaf.stalk ((𝔛.efib Pl hPl (algebraMap (R p) ↥Pl) hρ ≫ 𝔛.comp Pl hPl (algebraMap (R p) ↥Pl) hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl (algebraMap (R p) ↥Pl) hρ).C))) θr
  rw [hM] at hloc2
  letI algT : Algebra (↥Pl ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥Pl)))).presheaf.stalk ((𝔛.efib Pl hPl (algebraMap (R p) ↥Pl) hρ ≫ 𝔛.comp Pl hPl (algebraMap (R p) ↥Pl) hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl (algebraMap (R p) ↥Pl) hρ).C))) := ((algebraMap ↥Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥Pl)))), U) ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥Pl)))).presheaf.stalk ((𝔛.efib Pl hPl (algebraMap (R p) ↥Pl) hρ ≫ 𝔛.comp Pl hPl (algebraMap (R p) ↥Pl) hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl (algebraMap (R p) ↥Pl) hρ).C)))).comp θr.symm.toRingHom).toAlgebra
  refine ⟨𝔯, algT, hloc2, ?_, fun o => ?_⟩
  ·
    have hg : gChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) e₁ =
        (BranchReadSkel.bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ↥Pl)) := by
      simp [gChart, e₁]
    have h1 := fromSpec_specθ (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) e₁
      ((Spec.map (θ (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) e₁).inv).base P)
    have h3 : (Spec.map (θ (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) e₁).hom).base ((Spec.map (θ (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) e₁).inv).base P) = P := by
      rw [← Scheme.Hom.comp_apply, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]; rfl
    rw [h3, hg] at h1
    have h2 : (Spec.map (θ (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) e₁).inv).base P = 𝔯 := rfl
    rw [← h2, ← h1]
    exact hU.fromSpec_primeIdealOf ⟨((𝔛.efib Pl hPl (algebraMap (R p) ↥Pl) hρ ≫ 𝔛.comp Pl hPl (algebraMap (R p) ↥Pl) hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl (algebraMap (R p) ↥Pl) hρ).C)), hηU⟩
  ·
    have hcK : gChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) e₁ ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥Pl) (B := ↥(chartAlgFin p (ΓM M H) hj)))) := by
      have := gChart_comp_snd (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) e₁
      simpa [e₁] using this
    have hθc := θ_const (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) e₁ (pullback.snd _ _) hcK o
    rw [← hθc]
    show _ = ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥Pl)))).presheaf.germ U ((𝔛.efib Pl hPl (algebraMap (R p) ↥Pl) hρ ≫ 𝔛.comp Pl hPl (algebraMap (R p) ↥Pl) hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl (algebraMap (R p) ↥Pl) hρ).C)) hηU).hom (θr.symm (θr _))
    rw [θr.symm_apply_apply]
    erw [TopCat.Presheaf.germ_res_apply]
    rfl

end EtaValBridge
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const.BranchReadSkel"

namespace EtaVal
open ModularCurve

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem E2
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))
    (hsp : gA.base (genericPoint 𝔛.Meta.C) ⤳ (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) :
    ∃ V : ValuationSubring ↥(ModularCurve.xHFunctionFieldBar M H), ((𝔛.Meta.ffEquiv.symm.toRingHom.comp
        ((gA.stalkMap (genericPoint 𝔛.Meta.C)).hom.comp
          ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes hsp).hom))).range = V.toSubring ∧ V ≠ ⊤ ∧
      ∀ V' : ValuationSubring ↥(ModularCurve.xHFunctionFieldBar M H), V ≤ V' → V' = V ∨ V' = ⊤ := by
  letI algPl : Algebra (R p) ↥Pl := ρ.toAlgebra
  have halg : algebraMap (R p) ↥Pl = ρ := rfl

  haveI : Module.Flat (R p) ↥(chartAlgFin p (ΓM M H) hj) := (ModularCurve.XHDRLevel.flat_chartAlgFin_and_flat_chartAlgInf p (ΓM M H) hj).1
  haveI : Algebra.FiniteType (R p) ↥(chartAlgFin p (ΓM M H) hj) :=
    (ModularCurve.finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC p (ΓM M H)
      (ModularCurve.translation_mem_GammaH M H) (jAt (ΓM M H) hj) (coe_jAt (ΓM M H) hj)).1

  have hη := EtaValFin.eta_mem_chartFin p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂ bc hbc₁ hbc₂ hsp
  obtain ⟨𝔯, alg, hloc, h𝔯, hβ⟩ := EtaValBridge.exists_prime_algebra p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂ bc hbc₁ hbc₂ hsp halg
    (BranchReadSkel.bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ↥Pl)) (BranchReadSkel.bcChart_fst _ _ _) (BranchReadSkel.bcChart_snd _ _ _) hη
  have hP := EtaVal29.isMaximal_map_maximalIdeal_localization_genericPrime p M hpM H Pl hPl hj 𝔛 ρ hρ halg bc hbc₁ hbc₂
    (BranchReadSkel.bcChart (toBase p (ΓM M H) hj) (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _) (K := ↥Pl)) (BranchReadSkel.bcChart_fst _ _ _) (BranchReadSkel.bcChart_snd _ _ _) 𝔯 h𝔯
  have h𝔭eq := IsLocalRing.eq_maximalIdeal hP

  have hinj : Function.Injective ((𝔛.Meta.ffEquiv.symm.toRingHom.comp
        ((gA.stalkMap (genericPoint 𝔛.Meta.C)).hom.comp
          ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes hsp).hom))) := EtaValPieces.etaEmb_injective p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂ bc hbc₁ hbc₂ hsp
  have hfrac := EtaValGL3.isFractionRing_emb p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂ bc hbc₁ hbc₂ hsp

  letI := alg
  haveI := hloc
  obtain ⟨⟨V, hV⟩, hmax⟩ := EtaVal.core p Pl hPl ρ hρ halg ↥(chartAlgFin p (ΓM M H) hj) 𝔯.asIdeal _ h𝔭eq _ _ hinj hfrac
  refine ⟨V, hV, ?_⟩

  have hβ' : ((algebraMap (↥Pl ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)))).comp
        (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥Pl) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) =
      (((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.germ ⊤ ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) trivial).hom.comp
        ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv.hom)) := by
    ext o
    exact (hβ o).symm
  rw [hβ'] at hmax
  have hconst : ∀ a : ↥Pl, ((𝔛.Meta.ffEquiv.symm.toRingHom.comp
        ((gA.stalkMap (genericPoint 𝔛.Meta.C)).hom.comp
          ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes hsp).hom))) ((((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.germ ⊤ ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) trivial).hom.comp
        ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv.hom)) a) = algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) :=
    fun a => EtaValPieces.etaEmb_const p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂ bc hbc₁ hbc₂ hsp a

  obtain ⟨Rg, hRg₁, hRg₂, hRg₃⟩ :=
    ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
      (AlgebraicClosure ℚ) Pl (ΓM M H) (ModularCurve.translation_mem_GammaH M H)
  have hVRg : V ≤ Rg.integers := by
    intro f hf
    have hf' : f ∈ ((𝔛.Meta.ffEquiv.symm.toRingHom.comp
        ((gA.stalkMap (genericPoint 𝔛.Meta.C)).hom.comp
          ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes hsp).hom))).range := by rw [hV]; exact hf
    obtain ⟨g, rfl⟩ := hf'
    exact (GENERICPT.exists_mem_integers_and_coe_res_eq_coe_residue p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂ bc hbc₁ hbc₂ Rg hRg₁ hRg₂ hRg₃ hsp g).1
  exact EtaVal.finish p Pl hPl Rg _ _ hmax _ hinj hconst V hV hVRg

end EtaVal
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const.BranchReadSkel"

set_option maxHeartbeats 3200000 in
open Classical in
open ModularCurve in
open Classical in
open ModularCurve in
theorem solution

    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))

    (hsp : gA.base (genericPoint 𝔛.Meta.C) ⤳ (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) :

    letI emb : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))) →+* ↥(ModularCurve.xHFunctionFieldBar M H) :=
      𝔛.Meta.ffEquiv.symm.toRingHom.comp
        ((gA.stalkMap (genericPoint 𝔛.Meta.C)).hom.comp
          ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes hsp).hom)
    letI res : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))) →+* ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM)) :=
      (𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)).hom
    Function.Injective emb ∧
    (∃ V : ValuationSubring ↥(ModularCurve.xHFunctionFieldBar M H), emb.range = V.toSubring ∧ V ≠ ⊤ ∧
      ∀ V' : ValuationSubring ↥(ModularCurve.xHFunctionFieldBar M H), V ≤ V' → V' = V ∨ V' = ⊤) ∧
    (∀ a : ↥Pl,
      emb ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.germ ⊤ ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) trivial
        ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a))) =
        algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) ∧
      res ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.germ ⊤ ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) trivial
        ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a))) =
        algebraMap (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM)) (IsLocalRing.residue ↥Pl a)) := by
  refine ⟨EtaValPieces.etaEmb_injective p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂ bc hbc₁ hbc₂ hsp, EtaVal.E2 p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂ bc hbc₁ hbc₂ hsp, fun a => ⟨EtaValPieces.etaEmb_const p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂ bc hbc₁ hbc₂ hsp a, EtaValPieces.etaRes_const p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂ bc hbc₁ hbc₂ hsp a⟩⟩

#print axioms solution

end S_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const (solution)
