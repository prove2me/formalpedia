-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_linearMap_finiteSubmodule_tateModule_jH_toPic0Pair_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/2d41386b-3120-52ea-8f7e-27901b16cc15

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0SliceOps
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_CharacterLatticePairings
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_isSeparated_of_valuationRing
import Theorems.Thm_AlgebraicCurve_GluedPic0_ker_toPic0Pair_eq_range_nodeUnit
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_addSubgroup_extendsToPlace_addMonoidHom_gluedPic0_eq_ptsSp_symm
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
import Theorems.Thm_AlgebraicCurve_GluedPic0_exists_zsmul_eq_zero_and_toPic0Pair_eq
import Theorems.Thm_AlgebraicCurve_GluedPic0_natCard_ker_toPic0Pair_inf_torsionBy
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_nodeUnit_eq_residue_toricLift_and_mul_and_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_linearMap_finiteSubmodule_tateModule_jH_toPic0Pair_of_ne
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice"

open scoped MatrixGroups TensorProduct
open ModularCurve.JHNeronObjectAtP (Fbar)

namespace A2MidBody

theorem convMul_single {A L G : Type*} [CommRing A] [CommRing L] [Algebra A L] [AddCommGroup G]
    (χ χ' : WithConv (AddMonoidAlgebra A G →ₐ[A] L)) (g : G) :
    (χ * χ') (AddMonoidAlgebra.single g 1) = χ (AddMonoidAlgebra.single g 1) * χ' (AddMonoidAlgebra.single g 1) := by
  simp [AlgHom.convMul_apply, AddMonoidAlgebra.comul_single]

theorem convOne_single {A L G : Type*} [CommRing A] [CommRing L] [Algebra A L] [AddCommGroup G] (g : G) :
    (1 : WithConv (AddMonoidAlgebra A G →ₐ[A] L)) (AddMonoidAlgebra.single g 1) = 1 := by
  simp [AlgHom.convOne_apply, AddMonoidAlgebra.counit_single]

theorem convPow_single {A L G : Type*} [CommRing A] [CommRing L] [Algebra A L] [AddCommGroup G]
    (χ : WithConv (AddMonoidAlgebra A G →ₐ[A] L)) (g : G) (n : ℕ) :
    (χ ^ n) (AddMonoidAlgebra.single g 1) = (χ (AddMonoidAlgebra.single g 1)) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, convOne_single]
  | succ n ih => rw [pow_succ, convMul_single, ih, pow_succ]

theorem single_add {A L G : Type*} [CommRing A] [CommRing L] [Algebra A L] [AddCommGroup G]
    (χ : AddMonoidAlgebra A G →ₐ[A] L) (g h : G) :
    χ (AddMonoidAlgebra.single (g + h) 1) = χ (AddMonoidAlgebra.single g 1) * χ (AddMonoidAlgebra.single h 1) := by
  rw [← map_mul, AddMonoidAlgebra.single_mul_single, one_mul]

theorem mem_of_pow_eq_one {K : Type*} [Field K] (B : ValuationSubring K) (x : K) (m : ℕ) (hm : 0 < m)
    (hx : x ^ m = 1) : x ∈ B := by
  rw [← B.valuation_le_one_iff]
  have h := congrArg B.valuation hx
  rw [map_pow, map_one] at h
  rcases lt_trichotomy (B.valuation x) 1 with hlt | heq | hgt
  · exact hlt.le
  · exact heq.le
  · exact absurd h (ne_of_gt (one_lt_pow₀ hgt hm.ne'))

theorem exists_algHom_comp_eq (A : ValuationSubring (AlgebraicClosure ℚ)) (t m : ℕ) (hm : 0 < m)
    (χ : muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ) :
    ∃ χA : muCoord ↥A t m →ₐ[↥A] ↥A, (Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA = χ := by
  classical
  have hval : ∀ v : Fin t → ZMod m, χ (AddMonoidAlgebra.single v 1) ∈ A := by
    intro v
    refine mem_of_pow_eq_one A _ m hm ?_
    rw [← map_pow, AddMonoidAlgebra.single_pow, one_pow]
    have : m • v = 0 := by
      funext i; simp [nsmul_eq_mul]
    rw [this]
    exact map_one χ
  let φ : Multiplicative (Fin t → ZMod m) →* ↥A :=
    { toFun := fun g => ⟨χ (AddMonoidAlgebra.single (Multiplicative.toAdd g) 1), hval _⟩
      map_one' := Subtype.ext (by
        show χ (AddMonoidAlgebra.single (0 : Fin t → ZMod m) 1) = 1
        exact map_one χ)
      map_mul' := fun g h => Subtype.ext (by
        show χ (AddMonoidAlgebra.single (Multiplicative.toAdd g + Multiplicative.toAdd h) 1) = _
        rw [single_add]; rfl) }
  refine ⟨AddMonoidAlgebra.lift ↥A ↥A (Fin t → ZMod m) φ, ?_⟩
  refine AddMonoidAlgebra.algHom_ext (fun v => ?_) (Subsingleton.elim _ _)
  rw [AlgHom.comp_apply, AddMonoidAlgebra.lift_single, one_smul]
  rfl

set_option maxHeartbeats 6400000 in

theorem gen_tor (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (m : ℕ) (hm : 0 < m) (χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) :
    ∃ s : SchemeHomOver Λ.σA O.g, (O.pts (O.toricPoint m hm χ)).1 = barPt A ≫ s.1 ∧
      O.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s) ∈ (GluedPic0.nodeUnit O.ssFinset).range ∧
      (m : ℤ) • O.toricPoint m hm χ = 0 := by
  classical
  obtain ⟨χA, hχA⟩ := exists_algHom_comp_eq A O.toricRank m hm χ

  have hunit : Spec.map (CommRingCat.ofHom χA.toRingHom) ≫ muStr ↥A O.toricRank m = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : χA.toRingHom.comp (algebraMap ↥A (muCoord ↥A O.toricRank m)) = RingHom.id _ := by
      rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]; rfl
    rw [h, CommRingCat.ofHom_id, Spec.map_id]
  let s : SchemeHomOver Λ.σA O.g :=
    ⟨Spec.map (CommRingCat.ofHom χA.toRingHom) ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA, by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (O.toricLift m hm).1,
        (O.toricLift m hm).2, ← Category.assoc, hunit, Category.id_comp]⟩
  have hχring : χ.toRingHom = (algebraMap ↥A (AlgebraicClosure ℚ)).comp χA.toRingHom := by
    rw [← hχA]; rfl
  refine ⟨s, ?_, ?_, ?_⟩
  ·
    have e : O.pts (O.toricPoint m hm χ) =
        genOfBaseChangePt Λ.hσA (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ) (O.toricLift m hm)) :=
      O.pts.apply_symm_apply _
    rw [e]
    simp only [JZeroNeronObjectAtP.genOfBaseChangePt, JZeroNeronObjectAtP.castOver,
      GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe,
      JZeroNeronObjectAtP.muPt, Category.assoc, s]
    rw [hχring, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    rfl
  ·
    obtain ⟨hnode, -, -⟩ :=
      ModularCurve.JHNeronObjectAtP.exists_nodeUnit_eq_residue_toricLift_and_mul_and_eq_one p M H hpM A hA Λ O m hm
    obtain ⟨wb, hwb⟩ := hnode χA
    refine ⟨wb, ?_⟩
    rw [Equiv.eq_symm_apply]
    apply Subtype.ext
    show (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb)).1 = resPt A ≫ Spec.map (CommRingCat.ofHom χA.toRingHom) ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA
    rw [← hwb, ← Category.assoc (resPt A), ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  ·
    obtain ⟨hconv, -, -, -⟩ :=
      ModularCurve.JHNeronObjectAtP.toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard p M H hpM A hA Λ O m hm
    have h1 : O.toricPoint m hm (1 : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)).ofConv = 0 := by
      have := hconv 1 1
      rw [mul_one] at this
      exact left_eq_add.mp this
    have hpow : ∀ k : ℕ, O.toricPoint m hm ((WithConv.toConv χ) ^ k).ofConv = (k : ℤ) • O.toricPoint m hm χ := by
      intro k
      induction k with
      | zero => rw [pow_zero, h1, Nat.cast_zero, zero_zsmul]
      | succ k ih => rw [pow_succ, hconv, ih, Nat.cast_succ, add_zsmul, one_zsmul]
    have hχm : (WithConv.toConv χ) ^ m = 1 := by
      apply WithConv.ext
      refine AddMonoidAlgebra.algHom_ext (fun v => ?_) (Subsingleton.elim _ _)
      show ((WithConv.toConv χ) ^ m) (AddMonoidAlgebra.single v 1) =
        (1 : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)) (AddMonoidAlgebra.single v 1)
      rw [convPow_single, convOne_single]
      show (χ (AddMonoidAlgebra.single v 1)) ^ m = 1
      rw [← map_pow, AddMonoidAlgebra.single_pow, one_pow]
      have : m • v = 0 := by
        funext i; simp [nsmul_eq_mul]
      rw [this]
      exact map_one χ
    rw [← hpow m, hχm, h1]

end A2MidBody

set_option maxHeartbeats 32000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]

    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))

    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (hσ : Λ.σA = Spec.map (CommRingCat.ofHom ρ))
    (S : Set ℕ) (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p)

    (Tt Tf : Submodule ℤ_[ℓ] (TateModule ℓ (JH M H)))
    (hTt : ∀ x : TateModule ℓ (JH M H), x ∈ Tt ↔ ∀ n : ℕ, TateModule.proj ℓ (JH M H) n x ∈ O.toricPts (ℓ ^ n))
    (hTf : ∀ x : TateModule ℓ (JH M H), x ∈ Tf ↔ ∀ n : ℕ, TateModule.proj ℓ (JH M H) n x ∈ O.finPts (ℓ ^ n))

    (F Finv Fstar : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)

    (hUPabq : ∀ ξ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset,
        GluedPic0.toPic0Pair O.ssFinset
            (O.ptsSp.symm (schemeHomOverComp (O.ptsSp ξ) (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM)))) =
          AlgebraicCurve.Pic0Pair.blockOp Fstar (((p : ℤ) - 1) • AddMonoidHom.id _) 0 (δ.comp F)
            (GluedPic0.toPic0Pair O.ssFinset ξ)) :
    ∃ red : ↥Tf →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))),

      (∀ (x : ↥Tf) (n : ℕ) (s : SchemeHomOver Λ.σA O.g),
        (O.pts (TateModule.proj ℓ (JH M H) n (x : TateModule ℓ (JH M H)))).1 = barPt A ≫ s.1 →
        TateModule.proj ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) n (red x) =
          GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s))) ∧

      (∀ x : ↥Tf, red x = 0 ↔ (x : TateModule ℓ (JH M H)) ∈ Tt) ∧

      Function.Surjective red ∧

      (∀ (x : ↥Tf) (hx : tateGenOpH M H S ℓ (CohCarrier.Gen.U p (Fact.out) hpM) (x : TateModule ℓ (JH M H)) ∈ Tf),
        red ⟨tateGenOpH M H S ℓ (CohCarrier.Gen.U p (Fact.out) hpM) (x : TateModule ℓ (JH M H)), hx⟩ =
          TateModule.rep ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) (AddMonoid.End (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
            (AlgebraicCurve.Pic0Pair.blockOp Fstar (((p : ℤ) - 1) • AddMonoidHom.id _) 0 (δ.comp F)) (red x)) := by
  classical

  let cmp : SchemeHomOver Λ.σA O.g → SchemeHomOver (genPt p) O.g :=
    fun s => GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA s
  have cmp_coe : ∀ s, (cmp s).1 = barPt A ≫ s.1 := fun s => rfl
  have cmp_mul : ∀ s t, cmp (O.L.mul Λ.σA s t) = O.L.mul (genPt p) (cmp s) (cmp t) :=
    fun s t => O.L.mul_natural Λ.σA (genPt p) (barPt A) Λ.hσA s t
  have cmp_one : cmp (O.L.one Λ.σA) = O.L.one (genPt p) := O.L.one_natural Λ.σA (genPt p) (barPt A) Λ.hσA

  have hpts0 : O.pts 0 = O.L.one (genPt p) := by
    have h := O.pts_add 0 0
    rw [add_zero] at h
    calc O.pts 0 = O.L.mul _ (O.L.inv _ (O.pts 0)) (O.L.mul _ (O.pts 0) (O.pts 0)) := by
            rw [← O.L.mul_assoc, O.L.inv_mul_cancel, O.L.one_mul]
      _ = O.L.mul _ (O.L.inv _ (O.pts 0)) (O.pts 0) := by rw [← h]
      _ = O.L.one _ := O.L.inv_mul_cancel _ _
  have hptsneg : ∀ y : JH M H, O.pts (-y) = O.L.inv (genPt p) (O.pts y) := by
    intro y
    have h := O.pts_add y (-y)
    rw [add_neg_cancel, hpts0] at h

    calc O.pts (-y) = O.L.mul _ (O.L.one _) (O.pts (-y)) := (O.L.one_mul _ _).symm
      _ = O.L.mul _ (O.L.mul _ (O.L.inv _ (O.pts y)) (O.pts y)) (O.pts (-y)) := by rw [O.L.inv_mul_cancel]
      _ = O.L.mul _ (O.L.inv _ (O.pts y)) (O.L.mul _ (O.pts y) (O.pts (-y))) := O.L.mul_assoc _ _ _ _
      _ = O.L.mul _ (O.L.inv _ (O.pts y)) (O.L.one _) := by rw [← h]
      _ = O.L.inv _ (O.pts y) := O.L.mul_one _ _

  have cmp_inv : ∀ s, cmp (O.L.inv Λ.σA s) = O.L.inv (genPt p) (cmp s) := by
    intro s
    have h1 : O.L.mul _ (cmp (O.L.inv Λ.σA s)) (cmp s) = O.L.one _ := by
      rw [← cmp_mul, O.L.inv_mul_cancel, cmp_one]
    calc cmp (O.L.inv Λ.σA s) = O.L.mul _ (cmp (O.L.inv Λ.σA s)) (O.L.one _) := (O.L.mul_one _ _).symm
      _ = O.L.mul _ (cmp (O.L.inv Λ.σA s)) (O.L.mul _ (cmp s) (O.L.inv _ (cmp s))) := by
            rw [GoodReductionJacobian.RelativeGroupLaw.mul_inv_cancel]
      _ = O.L.mul _ (O.L.mul _ (cmp (O.L.inv Λ.σA s)) (cmp s)) (O.L.inv _ (cmp s)) := (O.L.mul_assoc _ _ _ _).symm
      _ = O.L.inv _ (cmp s) := by rw [h1, O.L.one_mul]

  have iff_cmp : ∀ (y : JH M H) (s : SchemeHomOver Λ.σA O.g), (O.pts y).1 = barPt A ≫ s.1 ↔ cmp s = O.pts y :=
    fun y s => ⟨fun h => Subtype.ext ((cmp_coe s).trans h.symm), fun h => (congrArg (fun z => z.1) h).symm.trans (cmp_coe s)⟩
  have hext : ∀ (n : ℕ) (x : JH M H), x ∈ O.finPts (ℓ ^ n) → ExtendsToPlace A Λ.σA (O.pts x) := by
    intro n x hx
    refine AddSubgroup.closure_induction (fun y hy => hy.2) ?_ ?_ ?_ hx
    · exact ⟨O.L.one Λ.σA, (iff_cmp 0 _).2 (cmp_one.trans hpts0.symm)⟩
    · rintro y z - - ⟨s, hs⟩ ⟨t, ht⟩
      refine ⟨O.L.mul Λ.σA s t, (iff_cmp _ _).2 ?_⟩
      rw [cmp_mul, (iff_cmp y s).1 hs, (iff_cmp z t).1 ht, O.pts_add]
    · rintro y - ⟨s, hs⟩
      refine ⟨O.L.inv Λ.σA s, (iff_cmp _ _).2 ?_⟩
      rw [cmp_inv, (iff_cmp y s).1 hs, hptsneg]

  have huniq : ∀ (s s' : SchemeHomOver Λ.σA O.g), barPt A ≫ s.1 = barPt A ≫ s'.1 → s = s' := by
    intro s s' h
    letI instRA : Algebra (R p) ↥A := ρ.toAlgebra
    have hST : IsScalarTower (R p) ↥A (AlgebraicClosure ℚ) :=
      IsScalarTower.of_algebraMap_eq fun r => (RingHom.congr_fun hρ r).symm
    haveI : IsSeparated O.g := O.separated

    have hρ' : Λ.σA = Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥A)) := hσ
    have key := @AlgebraicGeometry.SchemeHomOver.ext_of_isSeparated_of_valuationRing (R p) _ O.G O.g O.separated
      ↥A _ _ _ instRA (AlgebraicClosure ℚ) _ _ _ _ hST ⟨s.1, s.2.trans hρ'⟩ ⟨s'.1, s'.2.trans hρ'⟩ h
    exact Subtype.ext (congrArg (fun z => z.1) key :)

  let rdS : SchemeHomOver Λ.σA O.g → Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) :=
    fun s => GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s))

  have hlev : ∀ (x : ↥Tf) (n : ℕ), ∃ s : SchemeHomOver Λ.σA O.g,
      (O.pts (TateModule.proj ℓ (JH M H) n (x : TateModule ℓ (JH M H)))).1 = barPt A ≫ s.1 :=
    fun x n => hext n _ (((hTf (x : TateModule ℓ (JH M H))).1 x.2) n)
  let sec : ↥Tf → ℕ → SchemeHomOver Λ.σA O.g := fun x n => Classical.choose (hlev x n)
  have hsec : ∀ (x : ↥Tf) (n : ℕ),
      (O.pts (TateModule.proj ℓ (JH M H) n (x : TateModule ℓ (JH M H)))).1 = barPt A ≫ (sec x n).1 :=
    fun x n => Classical.choose_spec (hlev x n)
  let redFun : ↥Tf → ℕ → Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) := fun x n => rdS (sec x n)

  have hind : ∀ (x : ↥Tf) (n : ℕ) (s : SchemeHomOver Λ.σA O.g),
      (O.pts (TateModule.proj ℓ (JH M H) n (x : TateModule ℓ (JH M H)))).1 = barPt A ≫ s.1 → rdS s = redFun x n := by
    intro x n s hs
    have : s = sec x n := huniq s (sec x n) (hs.symm.trans (hsec x n))
    simp only [redFun, this]

  have hsp_mul : ∀ u v : SchemeHomOver (resPt A ≫ Λ.σA) O.g,
      O.ptsSp.symm (O.L.mul _ u v) = O.ptsSp.symm u + O.ptsSp.symm v := by
    intro u v
    apply O.ptsSp.injective
    rw [Equiv.apply_symm_apply, O.ptsSp_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

    have hov : ∀ w : SchemeHomOver (resPt A ≫ Λ.σA) O.g,
        JZeroNeronObjectAtP.overId w = GoodReductionJacobian.schemeHomOverComp (𝟙 _) rfl w :=
      fun w => Subtype.ext (Category.id_comp _).symm
    apply Subtype.ext
    simp only [JZeroNeronObjectAtP.toFibrePt, JZeroNeronObjectAtP.ofFibrePt,
      GoodReductionJacobian.RelativeGroupLaw.baseChange_mul, GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase, hov]
    rw [← O.L.mul_natural (resPt A ≫ Λ.σA) _ (𝟙 _) rfl u v, GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp]

  have rdS_eq : ∀ s, rdS s = GluedPic0.toPic0Pair O.ssFinset
      (O.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) := fun s => rfl

  have rdS_mul : ∀ s t, rdS (O.L.mul Λ.σA s t) = rdS s + rdS t := by
    intro s t
    rw [rdS_eq, rdS_eq, rdS_eq, O.L.mul_natural Λ.σA (resPt A ≫ Λ.σA) (resPt A) rfl, hsp_mul, map_add]
  have rdS_one : rdS (O.L.one Λ.σA) = 0 := by
    have h := rdS_mul (O.L.one Λ.σA) (O.L.one Λ.σA)
    rw [O.L.one_mul] at h
    exact left_eq_add.mp h

  let nsec : ℕ → SchemeHomOver Λ.σA O.g → SchemeHomOver Λ.σA O.g :=
    fun k s => Nat.rec (O.L.one Λ.σA) (fun _ r => O.L.mul Λ.σA r s) k
  have nsec_zero : ∀ s, nsec 0 s = O.L.one Λ.σA := fun s => rfl
  have nsec_succ : ∀ k s, nsec (k + 1) s = O.L.mul Λ.σA (nsec k s) s := fun k s => rfl
  have cmp_nsec : ∀ (k : ℕ) (y : JH M H) (s : SchemeHomOver Λ.σA O.g), cmp s = O.pts y → cmp (nsec k s) = O.pts (k • y) := by
    intro k y s hs
    induction k with
    | zero => rw [nsec_zero, cmp_one, zero_nsmul, hpts0]
    | succ k ih => rw [nsec_succ, cmp_mul, ih, hs, ← O.pts_add, succ_nsmul]
  have rdS_nsec : ∀ (k : ℕ) (s : SchemeHomOver Λ.σA O.g), rdS (nsec k s) = (k : ℤ) • rdS s := by
    intro k s
    induction k with
    | zero => rw [nsec_zero, rdS_one, Nat.cast_zero, zero_zsmul]
    | succ k ih => rw [nsec_succ, rdS_mul, ih, Nat.cast_succ, add_zsmul, one_zsmul]

  have red_nsmul : ∀ (x : ↥Tf) (n k : ℕ) (s : SchemeHomOver Λ.σA O.g),
      (O.pts ((k : ℤ) • TateModule.proj ℓ (JH M H) n (x : TateModule ℓ (JH M H)))).1 = barPt A ≫ s.1 →
      rdS s = (k : ℤ) • redFun x n := by
    intro x n k s hs
    have h1 : cmp (nsec k (sec x n)) = O.pts ((k : ℤ) • TateModule.proj ℓ (JH M H) n (x : TateModule ℓ (JH M H))) := by
      rw [natCast_zsmul]; exact cmp_nsec k _ _ ((iff_cmp _ _).1 (hsec x n))
    have h2 : s = nsec k (sec x n) := huniq s _ (hs.symm.trans ((iff_cmp _ _).2 h1).symm.symm)
    rw [h2, rdS_nsec]

  obtain ⟨dom, sp, hdom, hspS, -, -, hinj, hsurjS⟩ :=
    ModularCurve.JHNeronObjectAtP.exists_addSubgroup_extendsToPlace_addMonoidHom_gluedPic0_eq_ptsSp_symm p M H hpM A hA Λ O
  have rdS_sp : ∀ (y : JH M H) (hy : y ∈ dom) (s : SchemeHomOver Λ.σA O.g), (O.pts y).1 = barPt A ≫ s.1 →
      rdS s = GluedPic0.toPic0Pair O.ssFinset (sp ⟨y, hy⟩) := by
    intro y hy s hs
    rw [rdS_eq, hspS ⟨y, hy⟩ s hs]
  have hfin_dom : ∀ (n : ℕ) (y : JH M H), y ∈ O.finPts (ℓ ^ n) → y ∈ dom := fun n y hy => (hdom y).2 (hext n y hy)
  have red_sp : ∀ (x : ↥Tf) (n : ℕ),
      redFun x n = GluedPic0.toPic0Pair O.ssFinset (sp ⟨_, hfin_dom n _ (((hTf (x : TateModule ℓ (JH M H))).1 x.2) n)⟩) :=
    fun x n => rdS_sp _ _ (sec x n) (hsec x n)

  obtain ⟨hPD, hCB, hratv⟩ :=
    ModularCurve.JHNeronObjectAtP.hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar p M H hpM hpM2 (ResidueField ↥A)
  have hrat : ∀ s ∈ O.ssFinset, Function.Surjective (algebraMap (ResidueField ↥A) s.1.ResidueField) ∧
      Function.Surjective (algebraMap (ResidueField ↥A) s.2.ResidueField) := fun s _ => ⟨hratv s.1, hratv s.2⟩
  have hℓn_pos : ∀ n : ℕ, 0 < ℓ ^ n := fun n => pow_pos (Fact.out : ℓ.Prime).pos n
  have hℓn_cop : ∀ n : ℕ, (ℓ ^ n).Coprime p := fun n =>
    (Nat.Coprime.pow_left n ((Nat.coprime_primes (Fact.out) (Fact.out)).2 hℓp))
  have hℓn_ne : ∀ n : ℕ, ((ℓ ^ n : ℕ) : ResidueField ↥A) ≠ 0 := by
    intro n
    rw [Nat.cast_pow]
    refine pow_ne_zero n fun h => hℓp ?_
    exact ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).1
      ((CharP.cast_eq_zero_iff (ResidueField ↥A) p ℓ).1 h)).symm

  have fin_tors : ∀ (n : ℕ) (y : JH M H), y ∈ O.finPts (ℓ ^ n) → (ℓ ^ n) • y = 0 := by
    intro n y hy
    have h : O.finPts (ℓ ^ n) ≤ Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) (ℓ ^ n) :=
      (AddSubgroup.closure_le _).2 fun z hz => hz.1
    have := (Pic0.mem_torsion (K := AlgebraicClosure ℚ) (F := xHFunctionFieldBar M H)).1 (h hy)
    rwa [natCast_zsmul] at this

  have gen_tor := A2MidBody.gen_tor p M H hpM A hA Λ O

  have tor_pts : ∀ (n : ℕ), O.toricPts (ℓ ^ n) = AddSubgroup.closure (Set.range (O.toricPoint (ℓ ^ n) (hℓn_pos n))) :=
    fun n => dif_pos (hℓn_pos n)
  have tor_dom : ∀ (n : ℕ) (y : JH M H), y ∈ O.toricPts (ℓ ^ n) → y ∈ dom := by
    intro n y hy
    rw [tor_pts] at hy
    refine (AddSubgroup.closure_le dom).2 ?_ hy
    rintro _ ⟨χ, rfl⟩
    obtain ⟨s, hs, -, -⟩ := gen_tor _ (hℓn_pos n) χ
    exact (hdom _).2 ⟨s, hs⟩
  have tor_fin : ∀ (n : ℕ) (y : JH M H), y ∈ O.toricPts (ℓ ^ n) → y ∈ O.finPts (ℓ ^ n) := by
    intro n y hy
    rw [tor_pts] at hy
    refine (AddSubgroup.closure_le _).2 ?_ hy
    rintro _ ⟨χ, rfl⟩
    obtain ⟨s, hs, -, htor⟩ := gen_tor _ (hℓn_pos n) χ
    exact AddSubgroup.subset_closure ⟨(Pic0.mem_torsion (K := AlgebraicClosure ℚ) (F := xHFunctionFieldBar M H)).2 htor, s, hs⟩
  have tor_ker : ∀ (n : ℕ) (y : JH M H) (hy : y ∈ O.toricPts (ℓ ^ n)),
      GluedPic0.toPic0Pair O.ssFinset (sp ⟨y, tor_dom n y hy⟩) = 0 := by
    intro n y hy

    suffices h : ∃ hy' : y ∈ dom, GluedPic0.toPic0Pair O.ssFinset (sp ⟨y, hy'⟩) = 0 by
      obtain ⟨hy', h⟩ := h; exact h
    rw [tor_pts] at hy
    refine AddSubgroup.closure_induction (p := fun y _ => ∃ hy' : y ∈ dom, GluedPic0.toPic0Pair O.ssFinset (sp ⟨y, hy'⟩) = 0)
      ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨χ, rfl⟩
      obtain ⟨s, hs, ⟨w, hw⟩, -⟩ := gen_tor _ (hℓn_pos n) χ
      refine ⟨(hdom _).2 ⟨s, hs⟩, ?_⟩
      rw [hspS _ s hs, ← hw, GluedPic0.toPic0Pair_nodeUnit]
    · exact ⟨zero_mem _, by rw [show (⟨0, zero_mem dom⟩ : ↥dom) = 0 from rfl, map_zero, map_zero]⟩
    · rintro y z - - ⟨hy', hy0⟩ ⟨hz', hz0⟩
      refine ⟨add_mem hy' hz', ?_⟩
      rw [show (⟨y + z, add_mem hy' hz'⟩ : ↥dom) = ⟨y, hy'⟩ + ⟨z, hz'⟩ from rfl, map_add, map_add, hy0, hz0, add_zero]
    · rintro y - ⟨hy', hy0⟩
      refine ⟨neg_mem hy', ?_⟩
      rw [show (⟨-y, neg_mem hy'⟩ : ↥dom) = -⟨y, hy'⟩ from rfl, map_neg, map_neg, hy0, neg_zero]

  have ker_tor : ∀ (n : ℕ) (y : JH M H) (hy : y ∈ O.finPts (ℓ ^ n)),
      GluedPic0.toPic0Pair O.ssFinset (sp ⟨y, hfin_dom n y hy⟩) = 0 → y ∈ O.toricPts (ℓ ^ n) := by
    intro n y hy h0

    set Km : AddSubgroup (GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset) :=
      (GluedPic0.toPic0Pair O.ssFinset).ker ⊓
        (Submodule.torsionBy ℤ (GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset) ((ℓ ^ n : ℕ) : ℤ)).toAddSubgroup
      with hKm
    have cardK : Nat.card ↥Km = (ℓ ^ n) ^ O.toricRank := by
      rw [hKm, AlgebraicCurve.GluedPic0.natCard_ker_toPic0Pair_inf_torsionBy hCB O.ssFinset hrat (ℓ ^ n) (hℓn_ne n),
        ← O.toricRank_succ_eq_card, Nat.add_sub_cancel]

    obtain ⟨-, -, -, cardT⟩ :=
      ModularCurve.JHNeronObjectAtP.toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard p M H hpM A hA Λ O (ℓ ^ n) (hℓn_pos n)

    have mem_tors : ∀ (z : JH M H) (hz : z ∈ dom), (ℓ ^ n) • z = 0 →
        sp ⟨z, hz⟩ ∈ (Submodule.torsionBy ℤ _ ((ℓ ^ n : ℕ) : ℤ)).toAddSubgroup := by
      intro z hz htz
      rw [Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff, natCast_zsmul, ← map_nsmul,
        show (ℓ ^ n) • (⟨z, hz⟩ : ↥dom) = ⟨(ℓ ^ n) • z, AddSubgroup.nsmul_mem _ hz _⟩ from rfl]
      simp only [htz]
      exact map_zero sp
    let Φ : ↥(O.toricPts (ℓ ^ n)) → ↥Km := fun z =>
      ⟨sp ⟨z, tor_dom n z z.2⟩, by
        rw [hKm]
        exact ⟨(AddMonoidHom.mem_ker).2 (tor_ker n z z.2), mem_tors z _ (fin_tors n z (tor_fin n z z.2))⟩⟩

    have inj_dom : ∀ (z : JH M H) (hz : z ∈ dom), (ℓ ^ n) • z = 0 → sp ⟨z, hz⟩ = 0 → z = 0 := by
      intro z hz htz hsz
      have := hinj ⟨z, hz⟩ ⟨ℓ ^ n, hℓn_pos n, fun hdvd => hℓp ?_, htz⟩ hsz
      · exact congrArg Subtype.val this
      · exact ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).1
          ((Fact.out : p.Prime).dvd_of_dvd_pow hdvd)).symm
    have Φinj : Function.Injective Φ := by
      intro z z' hzz'
      have hsub : sp ⟨(z : JH M H) - z', sub_mem (tor_dom n z z.2) (tor_dom n z' z'.2)⟩ = 0 := by
        rw [show (⟨(z : JH M H) - z', _⟩ : ↥dom) = ⟨z, tor_dom n z z.2⟩ - ⟨z', tor_dom n z' z'.2⟩ from rfl, map_sub, sub_eq_zero]
        exact congrArg Subtype.val hzz'
      have htz : (ℓ ^ n) • ((z : JH M H) - z') = 0 := by
        rw [nsmul_sub, fin_tors n _ (tor_fin n _ z.2), fin_tors n _ (tor_fin n _ z'.2), sub_zero]
      exact Subtype.ext (sub_eq_zero.1 (inj_dom _ _ htz hsub))

    haveI : Finite ↥Km := Nat.finite_of_card_ne_zero (by rw [cardK]; exact pow_ne_zero _ (hℓn_pos n).ne')
    have Φbij : Function.Bijective Φ :=
      Φinj.bijective_of_nat_card_le (by rw [cardK, cardT])

    have hyK : sp ⟨y, hfin_dom n y hy⟩ ∈ Km := by
      rw [hKm]; exact ⟨(AddMonoidHom.mem_ker).2 h0, mem_tors y _ (fin_tors n y hy)⟩
    obtain ⟨z, hz⟩ := Φbij.2 ⟨_, hyK⟩
    have hsub : sp ⟨y - z, sub_mem (hfin_dom n y hy) (tor_dom n z z.2)⟩ = 0 := by
      rw [show (⟨y - z, _⟩ : ↥dom) = ⟨y, hfin_dom n y hy⟩ - ⟨z, tor_dom n z z.2⟩ from rfl, map_sub, sub_eq_zero]
      exact (congrArg Subtype.val hz).symm
    have htz : (ℓ ^ n) • (y - (z : JH M H)) = 0 := by
      rw [nsmul_sub, fin_tors n y hy, fin_tors n _ (tor_fin n _ z.2), sub_zero]
    have : y = z := sub_eq_zero.1 (inj_dom _ _ htz hsub)
    rw [this]; exact z.2

  have hmem : ∀ x : ↥Tf, redFun x ∈ TateModule ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) := by
    intro x n
    refine ⟨?_, ?_⟩
    ·
      have h0 : (O.pts (((ℓ ^ n : ℕ) : ℤ) • TateModule.proj ℓ (JH M H) n (x : TateModule ℓ (JH M H)))).1 =
          barPt A ≫ (O.L.one Λ.σA).1 := by
        rw [TateModule.proj_apply, TateModule.torsion, hpts0]
        exact (congrArg (fun z => z.1) cmp_one).symm
      rw [← rdS_one, red_nsmul x n (ℓ ^ n) (O.L.one Λ.σA) h0]
    ·
      have h1 : (O.pts (((ℓ : ℕ) : ℤ) • TateModule.proj ℓ (JH M H) (n + 1) (x : TateModule ℓ (JH M H)))).1 =
          barPt A ≫ (sec x n).1 := by
        rw [TateModule.proj_apply, TateModule.compat, ← TateModule.proj_apply]; exact hsec x n
      exact (red_nsmul x (n + 1) ℓ (sec x n) h1).symm

  have hadd : ∀ x y : ↥Tf, redFun (x + y) = redFun x + redFun y := by
    intro x y
    funext n
    have hs : (O.pts (TateModule.proj ℓ (JH M H) n ((x + y : ↥Tf) : TateModule ℓ (JH M H)))).1 =
        barPt A ≫ (O.L.mul Λ.σA (sec x n) (sec y n)).1 := by
      refine ((iff_cmp _ _).2 ?_)
      rw [cmp_mul, (iff_cmp _ _).1 (hsec x n), (iff_cmp _ _).1 (hsec y n), ← O.pts_add, ← map_add]
      rfl
    rw [Pi.add_apply, ← hind (x + y) n _ hs, rdS_mul]
  have hsmul : ∀ (a : ℤ_[ℓ]) (x : ↥Tf) (n : ℕ), redFun (a • x) n = ((a.appr n : ℕ) : ℤ) • redFun x n := by
    intro a x n
    have hs : (O.pts (((a.appr n : ℕ) : ℤ) • TateModule.proj ℓ (JH M H) n (x : TateModule ℓ (JH M H)))).1 =
        barPt A ≫ (sec (a • x) n).1 := by
      have := hsec (a • x) n
      rwa [TateModule.proj_apply, Submodule.coe_smul, TateModule.smul_apply, ← TateModule.proj_apply] at this
    exact red_nsmul x n (a.appr n) (sec (a • x) n) hs
  let red : ↥Tf →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) :=
    { toFun := fun x => ⟨redFun x, hmem x⟩
      map_add' := fun x y => Subtype.ext (hadd x y)
      map_smul' := fun a x => Subtype.ext (funext fun n => by
        rw [RingHom.id_apply, TateModule.smul_apply]; exact hsmul a x n) }
  refine ⟨red, ?_, ?_, ?_, ?_⟩
  ·
    intro x n s hs
    show redFun x n = rdS s
    exact (hind x n s hs).symm
  ·
    intro x
    rw [hTt]
    constructor
    · intro h n
      have hn : redFun x n = 0 :=
        congrArg (fun z : ↥(TateModule ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))) => (z : ℕ → Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) n) h
      rw [red_sp] at hn
      exact ker_tor n _ (((hTf (x : TateModule ℓ (JH M H))).1 x.2) n) hn
    · intro h
      refine Subtype.ext (funext fun n => ?_)
      show redFun x n = 0
      rw [red_sp]
      have e : sp ⟨_, hfin_dom n _ (((hTf (x : TateModule ℓ (JH M H))).1 x.2) n)⟩ = sp ⟨_, tor_dom n _ (h n)⟩ := rfl
      rw [e]
      exact tor_ker n _ (h n)
  ·

    intro y

    let E : ℕ → Type := fun n =>
      {z : JH M H // ∃ h : z ∈ O.finPts (ℓ ^ n), GluedPic0.toPic0Pair O.ssFinset (sp ⟨z, hfin_dom n z h⟩) = (y : ℕ → Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) n}

    have spv : ∀ (z : JH M H) (h h' : z ∈ dom), sp ⟨z, h⟩ = sp ⟨z, h'⟩ := fun _ _ _ => rfl

    have hdown : ∀ (n k : ℕ) (z : JH M H) (h : z ∈ O.finPts (ℓ ^ (n + k))),
        GluedPic0.toPic0Pair O.ssFinset (sp ⟨z, hfin_dom _ z h⟩) = (y : ℕ → Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) (n + k) →
        ∃ h' : (ℓ ^ k) • z ∈ O.finPts (ℓ ^ n),
          GluedPic0.toPic0Pair O.ssFinset (sp ⟨(ℓ ^ k) • z, hfin_dom n _ h'⟩) = (y : ℕ → Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) n := by
      intro n k z h hz
      have hzdom := hfin_dom _ z h
      have h' : (ℓ ^ k) • z ∈ O.finPts (ℓ ^ n) := by
        refine AddSubgroup.subset_closure ⟨(Pic0.mem_torsion (K := AlgebraicClosure ℚ) (F := xHFunctionFieldBar M H)).2 ?_,
          (hdom _).1 (AddSubgroup.nsmul_mem _ hzdom _)⟩
        rw [natCast_zsmul, ← mul_nsmul', ← pow_add, fin_tors _ z h]
      refine ⟨h', ?_⟩
      rw [show (⟨(ℓ ^ k) • z, hfin_dom n _ h'⟩ : ↥dom) = (ℓ ^ k) • ⟨z, hzdom⟩ from rfl, map_nsmul, map_nsmul, hz,
        ← natCast_zsmul, ← TateModule.compat_pow y n k]
    have hdown' : ∀ (i j : ℕ) (hij : i ≤ j) (z : JH M H) (h : z ∈ O.finPts (ℓ ^ j)),
        GluedPic0.toPic0Pair O.ssFinset (sp ⟨z, hfin_dom _ z h⟩) = (y : ℕ → Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) j →
        ∃ h' : (ℓ ^ (j - i)) • z ∈ O.finPts (ℓ ^ i),
          GluedPic0.toPic0Pair O.ssFinset (sp ⟨(ℓ ^ (j - i)) • z, hfin_dom i _ h'⟩) = (y : ℕ → Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) i := by
      intro i j hij z h hz
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
      rw [Nat.add_sub_cancel_left]
      exact hdown i k z h hz
    let π : {i j : ℕ} → (hij : i ≤ j) → E j → E i := fun {i j} hij b =>
      ⟨(ℓ ^ (j - i)) • b.1, by obtain ⟨h, hb⟩ := b.2; exact hdown' i j hij b.1 h hb⟩
    have π_refl : ∀ ⦃i⦄ (a : E i), π rfl.le a = a := fun i a => Subtype.ext (by
      show (ℓ ^ (i - i)) • a.1 = a.1
      rw [Nat.sub_self, pow_zero, one_nsmul])
    have π_trans : ∀ ⦃i j k⦄ (hij : i ≤ j) (hjk : j ≤ k) (a : E k), π hij (π hjk a) = π (hij.trans hjk) a :=
      fun i j k hij hjk a => Subtype.ext (by
        show (ℓ ^ (j - i)) • (ℓ ^ (k - j)) • a.1 = (ℓ ^ (k - i)) • a.1
        rw [← mul_nsmul', ← pow_add, add_comm, Nat.sub_add_sub_cancel hjk hij])

    have hne : ∀ n, Nonempty (E n) := by
      intro n
      have hyn : ((ℓ ^ n : ℕ) : ℤ) • (y : ℕ → Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) n = 0 := TateModule.torsion y n
      haveI := hPD
      obtain ⟨ξ, hξt, hξ⟩ := AlgebraicCurve.GluedPic0.exists_zsmul_eq_zero_and_toPic0Pair_eq O.ssFinset hrat (ℓ ^ n) _ hyn
      have hprime : ¬ p ∣ ℓ ^ n := fun hdvd => hℓp
        ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).1 ((Fact.out : p.Prime).dvd_of_dvd_pow hdvd)).symm
      obtain ⟨x, ⟨k, hk, hpk, hkx⟩, hx⟩ := hsurjS ξ ⟨ℓ ^ n, hℓn_pos n, hprime, by rw [← natCast_zsmul]; exact hξt⟩

      have hxt : (ℓ ^ n) • (x : JH M H) = 0 := by
        have h1 : sp ((ℓ ^ n) • x) = 0 := by rw [map_nsmul, hx, ← natCast_zsmul]; exact hξt
        have h2 := hinj ((ℓ ^ n) • x) ⟨k, hk, hpk, by
          show k • (((ℓ ^ n) • x : ↥dom) : JH M H) = 0
          rw [AddSubgroup.coe_nsmul, smul_comm, hkx, smul_zero]⟩ h1
        exact congrArg Subtype.val h2
      refine ⟨⟨x, ⟨AddSubgroup.subset_closure ⟨(Pic0.mem_torsion (K := AlgebraicClosure ℚ) (F := xHFunctionFieldBar M H)).2
        (by rw [natCast_zsmul]; exact hxt), (hdom _).1 x.2⟩, ?_⟩⟩⟩
      rw [spv _ _ x.2]
      show GluedPic0.toPic0Pair O.ssFinset (sp x) = _
      rw [hx, hξ]

    have hfinE : ∀ n, Finite (E n) := by
      intro n
      obtain ⟨z₀⟩ := hne n
      obtain ⟨h₀, hz₀⟩ := z₀.2
      haveI : Finite ↥(O.toricPts (ℓ ^ n)) := by
        obtain ⟨-, -, -, cardT⟩ :=
          ModularCurve.JHNeronObjectAtP.toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard p M H hpM A hA Λ O (ℓ ^ n) (hℓn_pos n)
        exact Nat.finite_of_card_ne_zero (by rw [cardT]; exact pow_ne_zero _ (hℓn_pos n).ne')
      refine Finite.of_injective (fun b : E n => (⟨b.1 - z₀.1, ?_⟩ : ↥(O.toricPts (ℓ ^ n)))) ?_
      · obtain ⟨h, hb⟩ := b.2
        refine ker_tor n _ (sub_mem h h₀) ?_
        rw [show (⟨b.1 - z₀.1, hfin_dom n _ (sub_mem h h₀)⟩ : ↥dom) = ⟨b.1, hfin_dom n _ h⟩ - ⟨z₀.1, hfin_dom n _ h₀⟩ from rfl,
          map_sub, map_sub, hb, hz₀, sub_self]
      · intro b b' hbb'
        exact Subtype.ext (sub_left_inj.1 (congrArg Subtype.val hbb'))
    haveI : ∀ n, Nonempty (E n) := hne
    haveI : Finite (E 0) := hfinE 0
    obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite π π_refl π_trans (fun i a => Set.toFinite _)

    have hfcompat : ∀ n, ((ℓ : ℕ) : ℤ) • (f (n + 1)).1 = (f n).1 := by
      intro n
      have := congrArg Subtype.val (hf (Nat.le_succ n))
      rw [← this]
      show ((ℓ : ℕ) : ℤ) • (f (n + 1)).1 = (ℓ ^ (n + 1 - n)) • (f (n + 1)).1
      rw [Nat.add_sub_cancel_left, pow_one, natCast_zsmul]
    let X : TateModule ℓ (JH M H) := ⟨fun n => (f n).1, fun n => ⟨by
      obtain ⟨h, -⟩ := (f n).2
      rw [natCast_zsmul]; exact fin_tors n _ h, hfcompat n⟩⟩
    have hX : X ∈ Tf := (hTf X).2 fun n => by obtain ⟨h, -⟩ := (f n).2; exact h
    refine ⟨⟨X, hX⟩, Subtype.ext (funext fun n => ?_)⟩

    show redFun ⟨X, hX⟩ n = (y : ℕ → Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) n
    obtain ⟨h, hfn⟩ := (f n).2
    rw [red_sp]
    exact hfn
  ·
    intro x hx
    refine Subtype.ext (funext fun n => ?_)

    let s' : SchemeHomOver Λ.σA O.g :=
      NeronModelInfra.schemeHomOverComp (sec x n) (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))
    have hs' : (O.pts (TateModule.proj ℓ (JH M H) n
        (tateGenOpH M H S ℓ (CohCarrier.Gen.U p (Fact.out) hpM) (x : TateModule ℓ (JH M H))))).1 = barPt A ≫ s'.1 := by
      rw [TateModule.proj_apply, tateGenOpH_apply_coe, O.hecke_pts, ← TateModule.proj_apply, hsec x n]
      simp only [s', NeronModelInfra.schemeHomOverComp_coe, Category.assoc]
    have hL : redFun ⟨_, hx⟩ n = rdS s' := (hind ⟨_, hx⟩ n s' hs').symm

    show redFun ⟨_, hx⟩ n =
      (AlgebraicCurve.Pic0Pair.blockOp Fstar (((p : ℤ) - 1) • AddMonoidHom.id _) 0 (δ.comp F)) (redFun x n)
    rw [hL]
    have key := hUPabq (O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ (sec x n)))
    rw [Equiv.apply_symm_apply] at key
    have hassoc : NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ (sec x n))
        (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM)) = NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s' :=
      Subtype.ext (by simp only [s', NeronModelInfra.schemeHomOverComp_coe, Category.assoc])
    rw [hassoc] at key
    exact key

end S_ModularCurve_JHNeronObjectAtP_exists_linearMap_finiteSubmodule_tateModule_jH_toPic0Pair_of_ne
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_linearMap_finiteSubmodule_tateModule_jH_toPic0Pair_of_ne (solution)
