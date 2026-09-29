-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.forall_nsmul_eq_zero_of_over_of_eq_map_classify_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/ef7b72ee-94da-5f99-a02b-80ebef3ad664

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_modularPolynomial_kronecker
import Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_ssJSet_eq_image_algebraMap_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_forall_nsmul_eq_zero_of_over_of_eq_map_classify_rigidDataH1Pow
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups Classical

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

noncomputable section

namespace KroneckerRoadO

open Polynomial

theorem eval₂_modularPolynomial_eq {S : Type*} [CommRing S] (q : ℕ) [Fact q.Prime] [CharP S q]
    (D : ModularPolynomialData q) (a b : S) :
    D.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom S) a) b = (a ^ q - b) * (a - b ^ q) := by
  set π : ℤ →+* ZMod q := Int.castRingHom (ZMod q)
  set φ : ZMod q →+* S := ZMod.castHom (dvd_refl q) S
  have hint : Int.castRingHom S = φ.comp π := RingHom.ext_int _ _
  have hcomp : Polynomial.eval₂RingHom (Int.castRingHom S) a =
      (Polynomial.eval₂RingHom φ a).comp (Polynomial.mapRingHom π) := by
    refine Polynomial.ringHom_ext (fun r => ?_) ?_
    · simp [hint]
    · simp
  rw [hcomp, ← Polynomial.eval₂_map, ← Polynomial.coe_mapRingHom,
    show (Polynomial.mapRingHom (Polynomial.mapRingHom π)) D.Φ = D.Φ.map (Polynomial.mapRingHom π) from rfl,
    ModularCurve.modularPolynomial_kronecker q D]
  simp [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow]

theorem eq_pow_or_pow_eq_of_eval₂_eq_zero {S : Type*} [CommRing S] [IsDomain S] (q : ℕ) [Fact q.Prime] [CharP S q]
    (D : ModularPolynomialData q) (a b : S)
    (h : D.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom S) a) b = 0) :
    b = a ^ q ∨ b ^ q = a := by
  rw [eval₂_modularPolynomial_eq q D a b, mul_eq_zero, sub_eq_zero, sub_eq_zero] at h
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

theorem map_eval₂_eval₂RingHom {C S : Type*} [CommRing C] [CommRing S] (f : C →+* S)
    (Φ : Polynomial (Polynomial ℤ)) (a b : C) :
    f (Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom C) a) b) =
      Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom S) (f a)) (f b) := by
  rw [Polynomial.hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp

theorem eval₂_eq_zero_of_eq_jqNModC {k : Type*} [CommRing k] {C : Type*} [CommRing C]
    (ι : C →+* LaurentSeries k) (hι : Function.Injective ι) (a b : C) (d ℓ : ℕ) [NeZero d] [NeZero ℓ]
    (D : ModularPolynomialData ℓ) (ha : ι a = jqNModC k d) (hb : ι b = jqNModC k (d * ℓ)) :
    D.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom C) a) b = 0 := by
  apply hι
  rw [map_zero, Polynomial.hom_eval₂, hb]
  have hhom : ι.comp (Polynomial.eval₂RingHom (Int.castRingHom C) a) =
      (Polynomial.aeval (R := ℤ) (jqNModC k d)).toRingHom := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [ha]
  rw [hhom]
  exact D.eval_jqNModC_mul_eq_zero k d

theorem mem_ssJSet_of_frobeniusPair {K : Type} [Field K] [DecidableEq K] (q : ℕ) [Fact q.Prime] [CharP K q]
    [PerfectField K] {a b : K} (h : b = a ^ q ∨ b ^ q = a) (ha : a ∈ ssJSet q K) : b ∈ ssJSet q K := by
  rcases h with rfl | h
  · exact (ModularCurve.pow_mem_ssJSet_iff q a).2 ha
  · exact (ModularCurve.pow_mem_ssJSet_iff q b).1 (h ▸ ha)

section SmallConstants

variable {L : Type*} [Field L] (A : ValuationSubring L) (k₀ : Type*) [Field k₀] [Algebra k₀ L]

def inclComap : ↥(A.comap (algebraMap k₀ L)) →+* ↥A where
  toFun x := ⟨algebraMap k₀ L x, x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[scoped simp] theorem coe_inclComap_apply (x : ↥(A.comap (algebraMap k₀ L))) :
    ((inclComap A k₀ x : A) : L) = algebraMap k₀ L x := rfl

scoped instance isLocalHom_inclComap : IsLocalHom (inclComap A k₀) := by
  constructor
  intro x hx
  have hne : (x : k₀) ≠ 0 := by
    intro h0
    have hx' : IsUnit ((inclComap A k₀ x : A) : L) := hx.map A.subtype
    rw [coe_inclComap_apply, h0, map_zero] at hx'
    exact not_isUnit_zero hx'
  have hinvA : ((algebraMap k₀ L x)⁻¹ : L) ∈ A := by
    obtain ⟨u, hu⟩ := hx
    have h3 : (((u⁻¹ : (↥A)ˣ) : A) : L) * algebraMap k₀ L x = 1 := by
      have h2 : ((u⁻¹ : (↥A)ˣ) : A) * (inclComap A k₀ x) = 1 := by rw [← hu, Units.inv_mul]
      simpa using congrArg (fun z : A => (z : L)) h2
    rw [← eq_inv_of_mul_eq_one_left h3]
    exact ((u⁻¹ : (↥A)ˣ) : A).2
  have hinv : (x : k₀)⁻¹ ∈ A.comap (algebraMap k₀ L) := by
    rw [ValuationSubring.mem_comap, map_inv₀]; exact hinvA
  exact ⟨⟨x, ⟨(x : k₀)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hne), Subtype.ext (inv_mul_cancel₀ hne)⟩, rfl⟩

def resMap : ResidueField ↥(A.comap (algebraMap k₀ L)) →+* ResidueField ↥A :=
  ResidueField.map (inclComap A k₀)

theorem resMap_residue (x : ↥(A.comap (algebraMap k₀ L))) :
    resMap A k₀ (residue _ x) = residue A ⟨algebraMap k₀ L x, x.2⟩ :=
  ResidueField.map_residue _ _

end SmallConstants

theorem mem_ssJSet_of_resMap_mem (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    [DecidableEq (ResidueField ↥A)] [DecidableEq (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))]
    (c : ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hc : resMap A ↥k₀ c ∈ ssJSet q (ResidueField ↥A)) :
    c ∈ ssJSet q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := by
  haveI : CharP (ResidueField ↥A) q := A.residueField_charP_of_liesOverPrime (Fact.out) hA
  haveI : IsAlgClosed (ResidueField ↥A) := A.isAlgClosed_residueField_algebraicClosure_rat
  haveI := hres
  haveI : CharP (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) q :=
    ((resMap A ↥k₀).charP_iff_charP q).2 inferInstance
  letI : Algebra (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ResidueField ↥A) :=
    (resMap A ↥k₀).toAlgebra
  have h := ModularCurve.ssJSet_eq_image_algebraMap_of_isAlgClosed q
    (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ResidueField ↥A)
  have hc' : resMap A ↥k₀ c ∈ @ssJSet q (ResidueField ↥A) _ (Classical.decEq _) := by
    convert hc
  rw [h] at hc'
  obtain ⟨a, ha, hac⟩ := hc'
  have : a = c := (resMap A ↥k₀).injective hac
  subst this
  convert ha

theorem exists_const_residue_eq (A : ValuationSubring (AlgebraicClosure ℚ)) (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧
      ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)
    (r : ResidueField ↥A) : ∃ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A), residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ = r := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  obtain ⟨c, hcA, h, hm⟩ := hκ a a.2
  refine ⟨c, hcA, ?_⟩
  refine Ideal.Quotient.eq.2 ?_
  have : (⟨(c : AlgebraicClosure ℚ), hcA⟩ : ↥A) - a = -⟨_, h⟩ := Subtype.ext (by simp)
  rw [this]
  exact neg_mem hm

theorem coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L jq = jqModC L := by
  show (jqModC ℚ).map (algebraMap ℚ L) = jqModC L
  exact map_jqModC _

theorem coeffMap_jqModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    coeffMap f (jqModC R) = jqModC S := by
  show (jqModC R).map f = jqModC S
  exact map_jqModC _

theorem qExpand_coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] (d : ℕ) [NeZero d] :
    qExpand L d (coeffEmb L jq) = jqNModC L d := by
  rw [coeffEmb_jq]; rfl

theorem qExpand_coeffEmb_jq_mem_laurentBaseChange_xHFunctionField (L : Type*) [Field L] [Algebra ℚ L]
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (d : ℕ) [NeZero d] (hd : d ∣ N) :
    qExpand L d (coeffEmb L jq) ∈ laurentBaseChange L (xHFunctionField N H) := by
  have h1 : qExpand ℚ d jq ∈ xHFunctionField N H :=
    x0_le_xHFunctionFieldC ℚ N H
      (ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ N (jqd_mem_full N hd))
  have h2 := coeffEmb_mem_laurentBaseChange L h1
  rwa [coeffEmb, ModularCurve.coeffMap_qExpand] at h2

theorem isIntegral_of_eq_jqNModC {k : Type*} [CommRing k] {F : Type*} [CommRing F] {S : Type*} [CommRing S] [Algebra S F]
    (ι : F →+* LaurentSeries k) (hι : Function.Injective ι) (jS : S) (z : F) (d : ℕ) [NeZero d]
    (D : ModularPolynomialData d) (hj : ι (algebraMap S F jS) = jqModC k) (hz : ι z = jqNModC k d) :
    IsIntegral S z := by
  refine ⟨D.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom S) jS), D.monic.map _, ?_⟩
  apply hι
  rw [map_zero, Polynomial.eval₂_map, Polynomial.hom_eval₂, hz]
  have hhom : (ι.comp ((algebraMap S F).comp (Polynomial.eval₂RingHom (Int.castRingHom S) jS))) =
      (Polynomial.aeval (R := ℤ) (jqNModC k 1)).toRingHom := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [hj, jqNModC_one]
  rw [hhom]
  have h := D.eval_jqNModC_mul_eq_zero k 1
  have hd1 : jqNModC k (1 * d) = jqNModC k d := qExpand_congr (one_mul d) _
  rwa [hd1] at h

theorem exists_mem_integers_residue_eq_jGeomGen (A : ValuationSubring (AlgebraicClosure ℚ)) (M' : ℕ) [NeZero M']
    [Algebra (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')]
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (hmem : coeffEmb (AlgebraicClosure ℚ) jq ∈ modularFunctionFieldBar M') :
    ∃ hgi : (⟨coeffEmb (AlgebraicClosure ℚ) jq, hmem⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
      R₀.residue ⟨_, hgi⟩ = jGeomGen (ResidueField ↥A) M' := by
  suffices key : ∀ (z : LaurentSeries (AlgebraicClosure ℚ)) (hz : z ∈ modularFunctionFieldBar M'),
      z = coeffMap A.subtype (jqModC ↥A) →
        ∃ hgi : (⟨z, hz⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
          R₀.residue ⟨_, hgi⟩ = jGeomGen (ResidueField ↥A) M' from
    key _ hmem ((coeffEmb_jq _).trans (coeffMap_jqModC A.subtype).symm)
  rintro z hz rfl
  obtain ⟨h, hh⟩ := hR₀ (jqModC ↥A) hz
  exact ⟨h, Subtype.ext (hh.trans (coeffMap_jqModC _))⟩

section Moduli

universe u

variable {A : Type u} [CommRing A] (R : RigidWeierstrassData.{u} A)

theorem jOfUnit_curve_eq_of_mk_eq_map (P : LevelModuliPackageAbs A R.toLevelModuliDatum)
    {T : Type u} [CommRing T] [Algebra A T] (φ : P.B₀ →ₐ[A] T) (x : R.Raw T)
    (hx : (Quot.mk _ x : R.Pt T) = R.toLevelModuliDatum.map φ P.univ) :
    (R.curve x).jOfUnit (R.isUnit_Δ x) = φ (R.toLevelModuliDatum.jOf P.univ) := by
  rw [← R.jOf_mk, ← R.toLevelModuliDatum.jOf_map φ P.univ]
  exact congrArg R.jOf hx

theorem classify_jOf_univ (P : LevelModuliPackageAbs A R.toLevelModuliDatum)
    {T : Type u} [CommRing T] [Algebra A T] (x₀ : R.toLevelModuliDatum.Pt T) :
    P.classify x₀ (R.toLevelModuliDatum.jOf P.univ) = R.toLevelModuliDatum.jOf x₀ := by
  rw [← R.toLevelModuliDatum.jOf_map, P.map_classify]

end Moduli

end KroneckerRoadO
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_forall_nsmul_eq_zero_of_over_of_eq_map_classify_rigidDataH1Pow.KroneckerRoadO"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_forall_nsmul_eq_zero_of_over_of_eq_map_classify_rigidDataH1Pow.KroneckerRoadO"

set_option linter.unusedVariables false in

set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (hιξ : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hK : K = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] [CommRing T'] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T'] (f : T →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)

    (P₀ : LevelModuliPackageAbs ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)
    (x₀ : (WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.Pt ↥K)
    (hx₀ : (((WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf x₀ : ↥K) : LaurentSeries ↥k₀) = ModularCurve.jqNModC ↥k₀ q)
    (clC : P₀.B₀ →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j))
    (hclC : ∀ b : P₀.B₀, ((clC b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) : ↥K) = P₀.classify x₀ b) :

    ∀ (y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) (_ : y.IsMaximal)
        (ψ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) (_ : ∀ c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j), ψ c = 0 ↔ c ∈ y),
        (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
          (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
          (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
            0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
            0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
              ↥(modularFunctionFieldBar M'))) →
          (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∀ (hgK : (coeffEmb ↥k₀ g) ∈ K)
            (hgC : (⟨_, hgK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j),
          ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
            residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
            (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⟨c, hc⟩ ∈ y) →
        ∀ x : (WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓg M' q hℓ hM hL 𝒢 𝒯).Raw (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))), (Quot.mk _ x : (WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓg M' q hℓ hM hL 𝒢 𝒯).Pt (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) = (WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.map ((ψ).comp clC) P₀.univ →
          ∀ P : (x.curve).toAffine.Point, q • P = 0 → P = 0 := by
  intro y _hy ψ hψ hover x hx P hP
  have hqp : q.Prime := Fact.out
  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero _ hqp.ne_zero) (NeZero.ne M')⟩
  haveI hcharA : CharP (ResidueField ↥A) q := A.residueField_charP_of_liesOverPrime hqp hA
  haveI := hres
  haveI hchar0 : CharP (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) q :=
    ((KroneckerRoadO.resMap A ↥k₀).charP_iff_charP q).2 hcharA

  obtain ⟨hgi, hres_jq⟩ := KroneckerRoadO.exists_mem_integers_residue_eq_jGeomGen A M' R₀ hR₀
    (coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M')))
  obtain ⟨_hsrat, hsaff, hsj⟩ := (hW s).1 s.2
  obtain ⟨c, hc, hcres⟩ := KroneckerRoadO.exists_const_residue_eq A k₀ hκ
    ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jGeomGen (ResidueField ↥A) M'))

  have hgK : (coeffEmb ↥k₀ jq) ∈ K := hj ▸ j.2
  obtain ⟨Dq⟩ := ModularCurve.nonempty_modularPolynomialData q
  have hιK : Function.Injective (algebraMap ↥K (LaurentSeries ↥k₀)) := Subtype.val_injective
  have hjL : ((j : ↥K) : LaurentSeries ↥k₀) = jqModC ↥k₀ := hj.trans (KroneckerRoadO.coeffEmb_jq ↥k₀)
  have hgj : (⟨_, hgK⟩ : ↥K) = j := Subtype.ext hj.symm
  have hgC : (⟨_, hgK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin
      ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j := by
    rw [hgj]
    exact AlgebraicCurve.TwoChartIntegralModel.adjoin_le_chartAlg _ _ _ (Algebra.self_mem_adjoin_singleton _ j)

  have hmem := hover jq (modularFunctionField_le_full M' (jq_mem M')) hgi (fun _ h => h)
    (by rw [hres_jq]; exact hsaff.1) hgK hgC c hc (by rw [hres_jq]; exact hcres)
  have hψa : ψ ⟨⟨_, hgK⟩, hgC⟩ = residue _ (⟨c, hc⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := by
    have h0 := (hψ _).2 hmem
    rwa [map_sub, sub_eq_zero, AlgHom.commutes] at h0

  have hcbar : residue _ (⟨c, hc⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈
      ssJSet q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := by
    refine KroneckerRoadO.mem_ssJSet_of_resMap_mem q A hA k₀ hres _ ?_
    rw [KroneckerRoadO.resMap_residue]
    change residue A ⟨(c : AlgebraicClosure ℚ), hc⟩ ∈ _
    rw [hcres]
    exact hsj

  have hb : (((clC ((WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓg M' q
      hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf P₀.univ) : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin
        ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) : ↥K) : LaurentSeries ↥k₀) = jqNModC ↥k₀ (1 * q) := by
    rw [hclC, KroneckerRoadO.classify_jOf_univ, hx₀]
    exact qExpand_congr (one_mul q).symm _
  have hιC : Function.Injective ((algebraMap ↥K (LaurentSeries ↥k₀)).comp
      (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j).val.toRingHom) :=
    hιK.comp Subtype.val_injective
  have ha : ((algebraMap ↥K (LaurentSeries ↥k₀)).comp
      (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j).val.toRingHom)
      ⟨⟨_, hgK⟩, hgC⟩ = jqNModC ↥k₀ 1 := by
    show coeffEmb ↥k₀ jq = jqNModC ↥k₀ 1
    rw [KroneckerRoadO.coeffEmb_jq, jqNModC_one]
  have heqC := KroneckerRoadO.eval₂_eq_zero_of_eq_jqNModC _ hιC ⟨⟨_, hgK⟩, hgC⟩
    (clC ((WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓg M' q
      hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf P₀.univ)) 1 q Dq ha hb
  have heqκ := congrArg ψ heqC
  rw [map_zero, ← AlgHom.coe_toRingHom, KroneckerRoadO.map_eval₂_eval₂RingHom, AlgHom.coe_toRingHom, hψa] at heqκ

  have hjss := KroneckerRoadO.mem_ssJSet_of_frobeniusPair q
    (KroneckerRoadO.eq_pow_or_pow_eq_of_eval₂_eq_zero q Dq _ _ heqκ) hcbar

  have hjx := KroneckerRoadO.jOfUnit_curve_eq_of_mk_eq_map _ P₀ ((ψ).comp clC) x hx
  haveI : x.curve.IsElliptic := ⟨x.isUnit_Δ⟩
  exact hjss x.curve hjx P hP

end S_ModularCurve_FullLevel_Diamond_forall_nsmul_eq_zero_of_over_of_eq_map_classify_rigidDataH1Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_forall_nsmul_eq_zero_of_over_of_eq_map_classify_rigidDataH1Pow (solution)
