-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_mem_integers_algebraMap_mul_smul_norm_heckeBetaHBar_and_coe_residue_eq_C_mul_coeffMap_frobenius_coe_residue_of_mem_integers_of_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/189f6fc1-2776-525d-8020-c09be4af7111

import Mathlib
import Theorems.Thm_ModularCurve_exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist
import Theorems.Thm_ModularCurve_coeffMap_residue_eq_C_mul_coeffMap_frobenius_of_qExpand_eq_C_mul_prod_qTwist
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_mem_integers_algebraMap_mul_smul_norm_heckeBetaHBar_and_coe_residue_eq_C_mul_coeffMap_frobenius_coe_residue_of_mem_integers_of_algEquiv
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_jqNGen"

set_option autoImplicit false

namespace GEOMSmall

open ModularCurve

theorem exists_unit_isPrimitiveRoot (p : ℕ) [Fact p.Prime] (Pl : ValuationSubring (AlgebraicClosure ℚ)) :
    ∃ ζ : (↥Pl)ˣ, IsPrimitiveRoot (((ζ : ↥Pl) : (AlgebraicClosure ℚ))) p ∧ ζ ^ p = 1 ∧
      ∀ n : ℤ, ζ ^ n = 1 → (p : ℤ) ∣ n := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero ((p : ℕ) : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne p)⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p

  have hmem : ζ₀ ∈ Pl := by
    rw [← ValuationSubring.valuation_le_one_iff]
    have hp : (Pl.valuation ζ₀) ^ p = 1 := by rw [← map_pow, hζ₀.pow_eq_one, map_one]
    exact not_lt.mp fun h => (one_lt_pow₀ h (NeZero.ne p)).ne' hp
  have hζPl : IsPrimitiveRoot (⟨ζ₀, hmem⟩ : ↥Pl) p :=
    IsPrimitiveRoot.of_map_of_injective (f := Pl.subtype) (by exact hζ₀) Subtype.val_injective
  let u : (↥Pl)ˣ := (hζPl.isUnit (NeZero.ne p)).unit
  have hu : (u : ↥Pl) = ⟨ζ₀, hmem⟩ := IsUnit.unit_spec _
  have huprim : IsPrimitiveRoot u p := IsPrimitiveRoot.coe_units_iff.mp (hu ▸ hζPl)
  refine ⟨u, ?_, ?_, fun n hn => (huprim.zpow_eq_one_iff_dvd n).mp hn⟩
  · rw [hu]; exact hζ₀
  · exact huprim.pow_eq_one

theorem coe_algebraMap {M : ℕ} {H : Subgroup (ZMod M)ˣ} (a : AlgebraicClosure ℚ) :
    ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) a : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      HahnSeries.C a := by
  rw [show ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) a : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a from
    (IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (LaurentSeries (AlgebraicClosure ℚ)) a).symm,
    HahnSeries.algebraMap_apply', ← PowerSeries.C_eq_algebraMap, HahnSeries.ofPowerSeries_C]

theorem coe_algebraMap_mul {M : ℕ} {H : Subgroup (ZMod M)ˣ} (c : AlgebraicClosure ℚ) (x : ↥(xHFunctionFieldBar M H)) :
    ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c * x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      HahnSeries.C c * ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) := by
  rw [MulMemClass.coe_mul, coe_algebraMap]

end GEOMSmall

namespace GeomKit

open ModularCurve

variable {R S : Type} [CommRing R] [CommRing S]

theorem coeffMap_qTwist (f : R →+* S) (u : Rˣ) (x : LaurentSeries R) :
    coeffMap f (qTwist u x) = qTwist (Units.map (f : R →* S) u) (coeffMap f x) := by
  ext k
  rw [coeffMap_coeff, qTwist_coeff, qTwist_coeff, coeffMap_coeff, map_mul]
  congr 1
  rw [← map_zpow (Units.map (f : R →* S)) u k, Units.coe_map, MonoidHom.coe_coe]

theorem pow_eq_pow_mod_of_pow_eq_one {p : ℕ} (ζ : Rˣ) (hζp : ζ ^ p = 1) (m : ℕ) : ζ ^ m = ζ ^ (m % p) := by
  conv_lhs => rw [← Nat.mod_add_div m p, pow_add, pow_mul, hζp, one_pow, mul_one]

theorem exists_qExpand_eq_prod_qTwist [IsDomain R] (p : ℕ) [Fact p.Prime] (ζ : Rˣ) (hζp : ζ ^ p = 1)
    (hζ : ∀ n : ℤ, ζ ^ n = 1 → (p : ℤ) ∣ n) (Y : LaurentSeries R) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ Y₀ : LaurentSeries R, qExpand R p Y₀ = ∏ j ∈ Finset.range p, qTwist (ζ ^ j) Y := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  set P := ∏ j ∈ Finset.range p, qTwist (ζ ^ j) Y with hP

  have hinv : qTwist ζ P = P := by
    have hG : P = ∏ i : Fin p, qTwist (ζ ^ (i : ℕ)) Y := by
      rw [hP, ← Fin.prod_univ_eq_prod_range (fun j => qTwist (ζ ^ j) Y)]
    rw [hG, map_prod]
    simp_rw [qTwist_qTwist]
    have hstep : ∀ i : Fin p, ζ * ζ ^ (i : ℕ) = ζ ^ (((i + 1 : Fin p)) : ℕ) := by
      intro i
      rw [← pow_succ', pow_eq_pow_mod_of_pow_eq_one ζ hζp ((i : ℕ) + 1), Fin.val_add, Fin.val_one', Nat.add_mod_mod]
    simp_rw [hstep]
    exact Fintype.prod_equiv (Equiv.addRight (1 : Fin p)) _ _ (fun i => rfl)

  have hcoef : ∀ n : ℤ, ¬ (p : ℤ) ∣ n → P.coeff n = 0 := by
    intro n hn
    have h := congrArg (fun Q : LaurentSeries R => Q.coeff n) hinv
    simp only [qTwist_coeff] at h
    have hne : ((ζ ^ n : Rˣ) : R) ≠ 1 := by
      intro h1
      apply hn (hζ n _)
      exact Units.val_eq_one.mp h1
    have : (((ζ ^ n : Rˣ) : R) - 1) * P.coeff n = 0 := by rw [sub_mul, one_mul, h, sub_self]
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hne
    · exact h0

  by_cases hP0 : P = 0
  · exact ⟨0, by rw [map_zero, hP0]⟩
  have hbdd : BddBelow (Function.support fun k : ℤ => P.coeff ((p : ℤ) * k)) := by
    apply HahnSeries.forallLTEqZero_supp_BddBelow _ (min P.order 0)
    intro m hm
    apply HahnSeries.coeff_eq_zero_of_lt_order
    have hm0 : m < 0 := lt_of_lt_of_le hm (min_le_right _ _)
    have hmo : m < P.order := lt_of_lt_of_le hm (min_le_left _ _)
    have : (p : ℤ) * m ≤ m := by nlinarith
    exact lt_of_le_of_lt this hmo
  refine ⟨HahnSeries.ofSuppBddBelow (fun k : ℤ => P.coeff ((p : ℤ) * k)) hbdd, ?_⟩
  ext n
  by_cases hn : (p : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hn
    rw [qExpand_coeff_mul, HahnSeries.coeff_ofSuppBddBelow]
  · rw [qExpand_coeff_of_not_dvd _ _ hn, hcoef n hn]

end GeomKit

open scoped MatrixGroups
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

open ModularCurve in
set_option maxHeartbeats 1600000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (S : Set ℕ) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K]

    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)

    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
    (hsep : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ O.G)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L))
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection)
    (hajQ : (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
        ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
        ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
        (Category.comp_id t)))).idealModule)))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1)
    (hpts_law : (∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)))
    (hAJ : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (R : Type) [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    [Algebra R (AlgebraicClosure ℚ)] [FaithfulSMul R (AlgebraicClosure ℚ)]
    (hRA : ∀ x : R, algebraMap R (AlgebraicClosure ℚ) x ∈ Pl)
    (hRdvr : IsDiscreteValuationRing R) (hRirr : Irreducible ((p : ℕ) : R))
    (hRfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ Pl.inertiaSubgroupIn ℚ ↔ ∀ x : R, σ (algebraMap R (AlgebraicClosure ℚ) x) = algebraMap R (AlgebraicClosure ℚ) x)
    (hRmax : ∀ y ∈ Pl, (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, σ y = y) → ∃ x : R, algebraMap R (AlgebraicClosure ℚ) x = y)

    {h : ℕ} (𝒢 : PDivisibleGroup R p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (hΔinj : Function.Injective Δ)
    (hΔlev : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (hΔgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[R] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z)
    (hΔhecke : ∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[R] 𝒢.level v,
        (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
        ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
          Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[R] 𝒢.level v))))) =
            ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))

    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)

    (ιK : ↥Pl →+* K) (hιK : ∀ y : ↥Pl, ιK y = 0 ↔ Pl.valuation (y : AlgebraicClosure ℚ) < 1)

    [CharP K p]

    (Ψ : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p) → ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
    (hΨ : ∀ x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), ∃ (D : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))) (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (y : LaurentSeries ↥Pl),
        AlgebraicCurve.Pic0.mk D = ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) ∧ f ≠ 0 ∧
        (∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
          (p : ℤ) * (wgen • (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))) v = v.ord f) ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y ∧
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 ∧
        ((Ψ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) = ModularCurve.coeffMap ιK y)

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

    (d : (ZMod M)ˣ) (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (hdH : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM ∨
      -ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM)

    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwθ : wgen = SemilinearAut.ofAlgAut θ)
    :
    ∀ (f : ↥(ModularCurve.xHFunctionFieldBar M H))
      (hf : (f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers),
      ∃ (lam : AlgebraicClosure ℚ) (hlam : lam ≠ 0)
        (hfU : ((algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) lam *
            (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H p)
         wgen • (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H p (wgen⁻¹ • f)) : ↥(ModularCurve.xHFunctionFieldBar M H))) : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers)
        (c : (IsLocalRing.ResidueField ↥Pl)), c ≠ 0 ∧
        ((Rg.residue ⟨_, hfU⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
          HahnSeries.C c *
            ModularCurve.coeffMap (frobenius (IsLocalRing.ResidueField ↥Pl) p) ((Rg.residue ⟨(f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hf⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) := by
  intro f hf
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  set fU : ↥(ModularCurve.xHFunctionFieldBar M H) := (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H p)
         wgen • (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H p (wgen⁻¹ • f)) : ↥(ModularCurve.xHFunctionFieldBar M H))) with hfUdef

  obtain ⟨ζ, hζprim, hζp, hζdiv⟩ : ∃ ζ : (↥Pl)ˣ, IsPrimitiveRoot (((ζ : ↥Pl) : (AlgebraicClosure ℚ))) p ∧ ζ ^ p = 1 ∧
      ∀ n : ℤ, ζ ^ n = 1 → (p : ℤ) ∣ n :=
    GEOMSmall.exists_unit_isPrimitiveRoot p Pl
  set ζu : (AlgebraicClosure ℚ)ˣ := Units.map (Pl.subtype : ↥Pl →* (AlgebraicClosure ℚ)) ζ with hζu
  have hζu' : IsPrimitiveRoot ζu p := by
    have : (ζu : (AlgebraicClosure ℚ)) = ((ζ : ↥Pl) : (AlgebraicClosure ℚ)) := rfl
    exact (IsPrimitiveRoot.coe_units_iff).mp (this ▸ hζprim)

  obtain ⟨c₀, hc0, hlaw⟩ := ModularCurve.exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist p M hpM hpM2 H hHp hin wgen θ hθ hwθ ζu hζu' d hd hdH f
  rw [← hfUdef] at hlaw

  obtain ⟨Xs, Ys, hY0, hpres⟩ := (hRg₁ _).mp hf
  obtain ⟨Y₀, hY₀⟩ := GeomKit.exists_qExpand_eq_prod_qTwist p ζ hζp hζdiv Ys
  obtain ⟨X₀, hX₀⟩ := GeomKit.exists_qExpand_eq_prod_qTwist p ζ hζp hζdiv Xs
  have hread : ∀ (Z Z₀ : LaurentSeries ↥Pl), ModularCurve.qExpand ↥Pl p Z₀ = ∏ j ∈ Finset.range p, ModularCurve.qTwist (ζ ^ j) Z →
      ModularCurve.qExpand (AlgebraicClosure ℚ) p (ModularCurve.coeffMap Pl.subtype Z₀) =
        ∏ j ∈ Finset.range p, ModularCurve.qTwist (ζu ^ j) (ModularCurve.coeffMap Pl.subtype Z) := by
    intro Z Z₀ h
    rw [← ModularCurve.coeffMap_qExpand, h, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [GeomKit.coeffMap_qTwist, map_pow]
  have hY₀' := hread Ys Y₀ hY₀
  have hX₀' := hread Xs X₀ hX₀
  have hprod : (∏ j ∈ Finset.range p, ModularCurve.qTwist (ζu ^ j) ((f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))) *
      (∏ j ∈ Finset.range p, ModularCurve.qTwist (ζu ^ j) (ModularCurve.coeffMap Pl.subtype Ys)) =
      ∏ j ∈ Finset.range p, ModularCurve.qTwist (ζu ^ j) (ModularCurve.coeffMap Pl.subtype Xs) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← map_mul, hpres]

  have hGcoe : ((algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) c₀⁻¹ * fU : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.C c₀⁻¹ * ((fU : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) :=
    GEOMSmall.coe_algebraMap_mul c₀⁻¹ fU
  have hGlaw : ModularCurve.qExpand (AlgebraicClosure ℚ) p ((algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) c₀⁻¹ * fU : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      ∏ j ∈ Finset.range p, ModularCurve.qTwist (ζu ^ j) ((f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [hGcoe, map_mul, ModularCurve.qExpand_C, hlaw, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
  have hGpres : ((algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) c₀⁻¹ * fU : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap Pl.subtype Y₀ =
      ModularCurve.coeffMap Pl.subtype X₀ := by
    apply ModularCurve.qExpand_injective (R := AlgebraicClosure ℚ) p
    rw [map_mul, hGlaw, hY₀', hprod, hX₀']

  have hresY := ModularCurve.coeffMap_residue_eq_C_mul_coeffMap_frobenius_of_qExpand_eq_C_mul_prod_qTwist p ↥Pl ζ hζp 1 Ys Y₀
    (by rw [map_one, one_mul]; exact hY₀)
  have hresX := ModularCurve.coeffMap_residue_eq_C_mul_coeffMap_frobenius_of_qExpand_eq_C_mul_prod_qTwist p ↥Pl ζ hζp 1 Xs X₀
    (by rw [map_one, one_mul]; exact hX₀)
  rw [map_one, map_one, one_mul] at hresY hresX
  have hfrobinj : Function.Injective (ModularCurve.coeffMap (frobenius (IsLocalRing.ResidueField ↥Pl) p)) := by
    intro a b h
    ext k
    exact frobenius_inj (IsLocalRing.ResidueField ↥Pl) p (by simpa using congrArg (fun s : LaurentSeries (IsLocalRing.ResidueField ↥Pl) => s.coeff k) h)
  have hY₀0 : ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) Y₀ ≠ 0 := by
    rw [hresY, ← map_zero (ModularCurve.coeffMap (frobenius (IsLocalRing.ResidueField ↥Pl) p))]
    exact fun h0 => hY0 (hfrobinj h0)
  have hfU : ((algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) c₀⁻¹ * fU : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers :=
    (hRg₁ _).mpr ⟨X₀, Y₀, hY₀0, hGpres⟩
  refine ⟨c₀⁻¹, inv_ne_zero hc0, hfU, 1, one_ne_zero, ?_⟩
  have h3f := hRg₃ _ hf Xs Ys hY0 hpres
  have h3G := hRg₃ _ hfU X₀ Y₀ hY₀0 hGpres
  rw [hresY, hresX, ← h3f, map_mul] at h3G
  have hne : ModularCurve.coeffMap (frobenius (IsLocalRing.ResidueField ↥Pl) p) (ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) Ys) ≠ 0 := by
    rw [← hresY]; exact hY₀0
  rw [map_one, one_mul]
  exact mul_right_cancel₀ hne h3G

end S_ModularCurve_XHDRModelAtP_exists_mem_integers_algebraMap_mul_smul_norm_heckeBetaHBar_and_coe_residue_eq_C_mul_coeffMap_frobenius_coe_residue_of_mem_integers_of_algEquiv
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_mem_integers_algebraMap_mul_smul_norm_heckeBetaHBar_and_coe_residue_eq_C_mul_coeffMap_frobenius_coe_residue_of_mem_integers_of_algEquiv (solution)
