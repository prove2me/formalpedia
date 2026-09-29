-- Prove2me | solution 1 for ModularCurve.nonempty_ssLevelDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/55b878f1-5748-5612-8fef-776c9abb113b

import Mathlib
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_FibrePoly
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_mem_ssJSet_of_mem_roots_fibrePoly
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict
import Theorems.Thm_ModularCurve_isIntegral_jqNModC_all
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_one_lt
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_kroneckerCongruence
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_nonempty_ssLevelDatum
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm WeierstrassCurve.reducePoint_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open ModularCurve AlgebraicCurve Polynomial

namespace SSLevelSlot

section ModularEquations

variable (K : Type*) [Field K]

theorem laurentMap_jqInt_geom : laurentMap (Int.castRingHom K) jqInt = jqModC K := by
  have h := laurentMap_jqIntN_geom K 1
  rwa [jqIntN, qExpand_one_apply, jqNModC_one] at h

theorem evalModularPair_swap_eq_zero {n : ℕ} [NeZero n] (hn : 1 < n) (data : ModularPolynomialData n) :
    evalModularPair (jqNModC K n) (jqModC K) data.Φ = 0 := by

  have hQ : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqN n)).toRingHom jq = 0 := by
    rw [← ModularCurve.ModularPolynomialData.evalSymm_of_one_lt n hn data jq (jqN n)]
    exact data.eval_eq_zero

  have hZ : data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℤ)) (jqIntN n)) jqInt = 0 := by
    refine laurentMap_injective (f := Int.castRingHom ℚ) Int.cast_injective ?_
    rw [map_zero, Polynomial.hom_eval₂, laurentMap_jqInt]
    have hcomp : (laurentMap (Int.castRingHom ℚ)).comp
        (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℤ)) (jqIntN n)) =
        (Polynomial.aeval (R := ℤ) (jqN n)).toRingHom := by
      refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
      rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, laurentMap_jqIntN,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X]
    rw [hcomp]
    exact hQ

  have h := congrArg (laurentMap (Int.castRingHom K)) hZ
  rw [map_zero, Polynomial.hom_eval₂, laurentMap_jqInt_geom] at h
  have hcomp : (laurentMap (Int.castRingHom K)).comp
      (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℤ)) (jqIntN n)) =
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (jqNModC K n) := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, laurentMap_jqIntN_geom,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rw [hcomp] at h
  exact h

variable {K}

theorem evalModularPair_eq_zero_of_coe (F : IntermediateField K (LaurentSeries K)) (x y : F)
    (Φ : Polynomial (Polynomial ℤ)) (h : evalModularPair (x : LaurentSeries K) (y : LaurentSeries K) Φ = 0) :
    evalModularPair x y Φ = 0 := by
  have hval := map_evalModularPair F.val.toRingHom x y Φ
  refine (map_eq_zero_iff _ F.val.toRingHom.injective).mp ?_
  rw [hval]
  exact h

theorem evalModularPair_j_jn (F : IntermediateField K (LaurentSeries K)) {n : ℕ} [NeZero n]
    (data : ModularPolynomialData n) (hj : jqModC K ∈ F) (hjn : jqNModC K n ∈ F) :
    evalModularPair (⟨jqModC K, hj⟩ : F) ⟨jqNModC K n, hjn⟩ data.Φ = 0 :=
  evalModularPair_eq_zero_of_coe F _ _ _ (evalModularPair_jq_eq_zero K data)

end ModularEquations

section IntegralityFromRelation

theorem isIntegral_of_evalModularPair_eq_zero {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    (Φ : Polynomial (Polynomial ℤ)) (hΦ : Φ.Monic) (a : A) (y : R)
    (h : evalModularPair (algebraMap A R a) y Φ = 0) : IsIntegral A y := by
  refine ⟨Φ.map (Polynomial.eval₂RingHom (Int.castRingHom A) a), hΦ.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hcomp : (algebraMap A R).comp (Polynomial.eval₂RingHom (Int.castRingHom A) a) =
      Polynomial.eval₂RingHom (Int.castRingHom R) (algebraMap A R a) := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X]
  rw [hcomp]
  exact h

theorem mem_valuationSubring_of_isIntegral {F : Type*} [Field F] (O : ValuationSubring F) {x : F}
    (hx : IsIntegral O x) : x ∈ O := by
  have hv : O.valuation.Integers O :=
    { hom_inj := Subtype.val_injective
      map_le_one := fun a => O.valuation_le_one a
      exists_of_le_one := fun r hr => ⟨⟨r, O.mem_of_valuation_le_one r hr⟩, rfl⟩ }
  exact (O.valuation_le_one_iff x).mp (hv.mem_of_integral hx)

theorem mem_valuationSubring_of_evalModularPair_eq_zero {F : Type*} [Field F] (O : ValuationSubring F)
    (Φ : Polynomial (Polynomial ℤ)) (hΦ : Φ.Monic) {x y : F} (hx : x ∈ O)
    (h : evalModularPair x y Φ = 0) : y ∈ O :=
  mem_valuationSubring_of_isIntegral O
    (isIntegral_of_evalModularPair_eq_zero (A := O) Φ hΦ ⟨x, hx⟩ y h)

variable {K : Type*} [Field K]

theorem jn_mem_valuationSubring (F : IntermediateField K (LaurentSeries K)) (n : ℕ) [NeZero n]
    (hj : jqModC K ∈ F) (hjn : jqNModC K n ∈ F) (O : ValuationSubring F)
    (hjO : (⟨jqModC K, hj⟩ : F) ∈ O) : (⟨jqNModC K n, hjn⟩ : F) ∈ O := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData n
  exact mem_valuationSubring_of_evalModularPair_eq_zero O data.Φ data.monic hjO
    (evalModularPair_j_jn F data hj hjn)

end IntegralityFromRelation

section SupersingularStep

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
variable {F : Type*} [Field F] [Algebra K F]

theorem evalAt_mem_ssJSet_of_evalModularPair_eq_zero {s : ℕ} [Fact s.Prime] (hsp : s ≠ p)
    (data : ModularPolynomialData s) (W : Place K F) (hrat : W.IsRational) {x y : F}
    (hx : x ∈ W.toValuationSubring) (hy : y ∈ W.toValuationSubring)
    (h : evalModularPair x y data.Φ = 0) (hss : W.evalAt x ∈ ssJSet p K) : W.evalAt y ∈ ssJSet p K := by

  have hO : evalModularPair (⟨x, hx⟩ : W.toValuationSubring) ⟨y, hy⟩ data.Φ = 0 := by
    have hval := map_evalModularPair (SubringClass.subtype W.toValuationSubring)
      (⟨x, hx⟩ : W.toValuationSubring) ⟨y, hy⟩ data.Φ
    refine (map_eq_zero_iff (SubringClass.subtype W.toValuationSubring) Subtype.val_injective).mp ?_
    rw [hval]
    exact h

  have hK : evalModularPair (W.evalAt x) (W.evalAt y) data.Φ = 0 := by
    have hres := congrArg (IsLocalRing.residue W.toValuationSubring) hO
    rw [map_zero, map_evalModularPair, ← W.algebraMap_evalAt hrat hx, ← W.algebraMap_evalAt hrat hy,
      ← map_evalModularPair] at hres
    exact (map_eq_zero_iff _ (algebraMap K W.ResidueField).injective).mp hres

  have hroot : W.evalAt y ∈ (fibrePoly data.Φ (W.evalAt x)).roots := by
    unfold fibrePoly
    rw [Polynomial.mem_roots ((data.monic.map _).ne_zero), Polynomial.IsRoot.def, Polynomial.eval_map]
    exact hK
  exact ModularCurve.mem_ssJSet_of_mem_roots_fibrePoly p hsp data hss hroot

end SupersingularStep

section Places

theorem isRational_restrict {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (w : Place K F') (hw : w.IsRational) :
    (w.restrict F).IsRational := by
  intro y
  obtain ⟨a, ha⟩ := hw (Place.restrictResidueMap F w y)
  refine ⟨a, (Place.restrictResidueMap F w).injective ?_⟩
  rw [← ha]
  exact (IsScalarTower.algebraMap_apply K (w.restrict F).ResidueField w.ResidueField a).symm

theorem isRational_congrRingEquiv {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
    (v : Place K F) (hv : v.IsRational) : (Place.congrRingEquiv e he v).IsRational := by
  intro z
  obtain ⟨a, ha⟩ := hv ((Place.congrResidueAlgEquiv e he v).symm z)
  refine ⟨a, ?_⟩
  rw [← (Place.congrResidueAlgEquiv e he v).commutes a, ha, AlgEquiv.apply_symm_apply]

variable {K : Type*} [Field K]

theorem jn_sub_algebraMap_ne_zero (F : IntermediateField K (LaurentSeries K)) (n : ℕ) [NeZero n]
    (hjn : jqNModC K n ∈ F) (c : K) : (⟨jqNModC K n, hjn⟩ : F) - algebraMap K F c ≠ 0 := by
  intro h
  have hval : jqNModC K n = algebraMap K (LaurentSeries K) c := by
    have h' := congrArg (algebraMap F (LaurentSeries K)) h
    rw [map_sub, map_zero, sub_eq_zero, ← IsScalarTower.algebraMap_apply] at h'
    exact h'
  exact ModularCurve.transcendental_jqNModC K n (hval ▸ isAlgebraic_algebraMap c)

end Places

section Integrality

variable {K : Type*} [Field K]

theorem isIntegral_toRingHom_of_forall {L : Type*} [Field L] [Algebra K L] (E E' B : IntermediateField K L)
    (φ : E →ₐ[K] E') (hB : ∀ b ∈ B, ∃ a : E, ((φ a : E') : L) = b)
    (hint : ∀ y : E', IsIntegral B (y : L)) : φ.toRingHom.IsIntegral := by
  intro y
  obtain ⟨P, hPm, hPy⟩ := hint y
  set ψ : E →+* L := (algebraMap E' L).comp φ.toRingHom with hψ
  have hlifts : P.map (algebraMap B L) ∈ Polynomial.lifts ψ := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    rw [Polynomial.coeff_map]
    obtain ⟨a, ha⟩ := hB _ (P.coeff k).2
    exact ⟨a, ha⟩
  obtain ⟨Q, hQmap, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts (hPm.map _)
  refine ⟨Q, hQm, ?_⟩
  have hcoe : algebraMap E' L (Polynomial.eval₂ φ.toRingHom y Q) = 0 := by
    rw [Polynomial.hom_eval₂, ← hψ, ← Polynomial.eval_map, hQmap, Polynomial.eval_map]
    exact hPy
  exact (map_eq_zero_iff _ (algebraMap E' L).injective).mp hcoe

theorem forall_isIntegral_of_le_adjoin {L : Type*} [Field L] [Algebra K L] (B E' : IntermediateField K L)
    (T : Set L) (hT : T.Finite) (hint : ∀ t ∈ T, IsIntegral B t) (hE' : E' ≤ IntermediateField.adjoin K T) :
    ∀ y : E', IsIntegral B (y : L) := by
  haveI : Finite T := hT.to_subtype
  haveI : FiniteDimensional B (IntermediateField.adjoin B T) := IntermediateField.finiteDimensional_adjoin hint
  intro y
  have hle : IntermediateField.adjoin K T ≤ (IntermediateField.adjoin B T).restrictScalars K := by
    rw [IntermediateField.adjoin_le_iff]
    exact IntermediateField.subset_adjoin B T
  have hy : (y : L) ∈ IntermediateField.adjoin B T := hle (hE' y.2)
  have h1 : IsIntegral B (⟨(y : L), hy⟩ : IntermediateField.adjoin B T) := Algebra.IsIntegral.isIntegral _
  exact h1.map (IntermediateField.val _)

theorem isIntegral_of_forall_mem {L : Type*} [Field L] [Algebra K L] {B : Type*} [Field B] [Algebra B L]
    (E₁ : IntermediateField K L) (C : IntermediateField B L) (hle : ∀ a : E₁, (a : L) ∈ C) {x : L}
    (hx : IsIntegral E₁ x) : IsIntegral C x := by
  let ι : E₁ →+* C :=
    { toFun := fun a => ⟨(a : L), hle a⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  obtain ⟨P, hPm, hP⟩ := hx
  refine ⟨P.map ι, hPm.map ι, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hP

theorem isIntegral_j_adjoin_jn (n : ℕ) [NeZero n] :
    IsIntegral (IntermediateField.adjoin K ({jqNModC K n} : Set (LaurentSeries K))) (jqModC K) := by
  by_cases hn : n = 1
  · subst hn
    have hmem : jqModC K ∈ IntermediateField.adjoin K ({jqNModC K 1} : Set (LaurentSeries K)) := by
      rw [jqNModC_one]
      exact IntermediateField.mem_adjoin_simple_self K _
    exact isIntegral_algebraMap
      (x := (⟨jqModC K, hmem⟩ : IntermediateField.adjoin K ({jqNModC K 1} : Set (LaurentSeries K))))
  · have h1 : 1 < n := by
      have := NeZero.ne n
      omega
    obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData n
    exact isIntegral_of_evalModularPair_eq_zero data.Φ data.monic
      (⟨jqNModC K n, IntermediateField.mem_adjoin_simple_self K _⟩ :
        IntermediateField.adjoin K ({jqNModC K n} : Set (LaurentSeries K)))
      (jqModC K) (evalModularPair_swap_eq_zero K h1 data)

theorem isIntegral_jm_adjoin_jn (n m : ℕ) [NeZero n] [NeZero m] :
    IsIntegral (IntermediateField.adjoin K ({jqNModC K n} : Set (LaurentSeries K))) (jqNModC K m) := by
  set B := IntermediateField.adjoin K ({jqNModC K n} : Set (LaurentSeries K)) with hB
  have hj : IsIntegral B (jqModC K) := isIntegral_j_adjoin_jn n
  set C := IntermediateField.adjoin B ({jqModC K} : Set (LaurentSeries K)) with hC
  haveI : FiniteDimensional B C := IntermediateField.adjoin.finiteDimensional hj
  haveI : Algebra.IsIntegral B C := Algebra.IsIntegral.of_finite B C
  have h1 : IsIntegral (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K m) :=
    ModularCurve.isIntegral_jqNModC_all K m
  have hle : ∀ a : IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)), (a : LaurentSeries K) ∈ C := by
    intro a
    have h : IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) ≤ C.restrictScalars K := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact IntermediateField.mem_adjoin_simple_self B (jqModC K)
    exact h a.2
  have h2 : IsIntegral C (jqNModC K m) := isIntegral_of_forall_mem _ C hle h1
  exact isIntegral_trans (jqNModC K m) h2

theorem isIntegral_j_adjoin_jn' (n : ℕ) [NeZero n] :
    IsIntegral (IntermediateField.adjoin K ({jqNModC K n} : Set (LaurentSeries K))) (jqModC K) := by
  have h := isIntegral_jm_adjoin_jn (K := K) n 1
  rwa [jqNModC_one] at h

theorem isIntegral_of_generators (E E' : IntermediateField K (LaurentSeries K)) (φ : E →ₐ[K] E')
    (n : ℕ) [NeZero n] (T : Set (LaurentSeries K)) (hT : T.Finite)
    (hgen : ∀ t ∈ T, t = jqModC K ∨ ∃ (m : ℕ) (_ : NeZero m), t = jqNModC K m)
    (hE' : E' ≤ IntermediateField.adjoin K T)
    (hB : ∀ b ∈ IntermediateField.adjoin K ({jqNModC K n} : Set (LaurentSeries K)), ∃ a : E, ((φ a : E') : LaurentSeries K) = b) :
    φ.toRingHom.IsIntegral := by
  refine isIntegral_toRingHom_of_forall E E' _ φ hB (forall_isIntegral_of_le_adjoin _ E' T hT ?_ hE')
  intro t ht
  rcases hgen t ht with h | ⟨m, hm, h⟩
  · rw [h]; exact isIntegral_j_adjoin_jn' n
  · rw [h]; exact isIntegral_jm_adjoin_jn n m

theorem cover_alpha (M : ℕ) [NeZero M] (E' : IntermediateField K (LaurentSeries K))
    (φ : modularFunctionFieldC K M →ₐ[K] E') (hφ : ∀ x, ((φ x : E') : LaurentSeries K) = x) :
    ∀ b ∈ IntermediateField.adjoin K ({jqNModC K 1} : Set (LaurentSeries K)),
      ∃ a : modularFunctionFieldC K M, ((φ a : E') : LaurentSeries K) = b := by
  intro b hb
  have hle : IntermediateField.adjoin K ({jqNModC K 1} : Set (LaurentSeries K)) ≤ modularFunctionFieldC K M := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, jqNModC_one]
    exact jqModC_mem K M
  exact ⟨⟨b, hle hb⟩, hφ _⟩

theorem cover_beta (M ℓ : ℕ) [NeZero M] [NeZero ℓ] (E' : IntermediateField K (LaurentSeries K))
    (φ : modularFunctionFieldC K M →ₐ[K] E') (hφ : ∀ x, ((φ x : E') : LaurentSeries K) = qExpand K ℓ x) :
    ∀ b ∈ IntermediateField.adjoin K ({jqNModC K ℓ} : Set (LaurentSeries K)),
      ∃ a : modularFunctionFieldC K M, ((φ a : E') : LaurentSeries K) = b := by
  intro b hb
  have h : IntermediateField.adjoin K ({jqNModC K ℓ} : Set (LaurentSeries K)) =
      (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))).map (qExpandAlgC K ℓ) := by
    rw [IntermediateField.adjoin_map, Set.image_singleton, qExpandAlgC_apply]
    rfl
  rw [h, IntermediateField.mem_map] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  have hle : IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) ≤ modularFunctionFieldC K M := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact jqModC_mem K M
  exact ⟨⟨a, hle ha⟩, hφ _⟩

theorem levelAlphaC_isIntegral (M s : ℕ) [NeZero M] [NeZero s] (hM : jqNModC K M ∈ modularFunctionFieldC K (M * s)) :
    (levelAlphaC K M s hM).toRingHom.IsIntegral := by
  refine isIntegral_of_generators _ _ (levelAlphaC K M s hM) 1 {jqModC K, jqNModC K (M * s)}
    (Set.toFinite _) ?_ le_rfl (cover_alpha M _ _ (coe_levelAlphaC K M s hM))
  rintro t (rfl | rfl)
  · exact Or.inl rfl
  · exact Or.inr ⟨M * s, inferInstance, rfl⟩

theorem levelBetaC_isIntegral (M s : ℕ) [NeZero M] [NeZero s] (hS : jqNModC K s ∈ modularFunctionFieldC K (M * s)) :
    (levelBetaC K M s hS).toRingHom.IsIntegral := by
  refine isIntegral_of_generators _ _ (levelBetaC K M s hS) s {jqModC K, jqNModC K (M * s)}
    (Set.toFinite _) ?_ le_rfl (cover_beta M s _ _ (coe_levelBetaC K M s hS))
  rintro t (rfl | rfl)
  · exact Or.inl rfl
  · exact Or.inr ⟨M * s, inferInstance, rfl⟩

theorem legs_isIntegral (N ℓ : ℕ) [NeZero N] [NeZero ℓ] :
    (heckeAlphaC K N ℓ).toRingHom.IsIntegral ∧ (heckeBetaC K N ℓ).toRingHom.IsIntegral := by
  have hgen : ∀ t ∈ ({jqModC K, jqNModC K N, jqNModC K ℓ, jqNModC K (N * ℓ)} : Set (LaurentSeries K)),
      t = jqModC K ∨ ∃ (m : ℕ) (_ : NeZero m), t = jqNModC K m := by
    rintro t (rfl | rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr ⟨N, inferInstance, rfl⟩
    · exact Or.inr ⟨ℓ, inferInstance, rfl⟩
    · exact Or.inr ⟨N * ℓ, inferInstance, rfl⟩
  constructor
  · exact isIntegral_of_generators _ _ (heckeAlphaC K N ℓ) 1 _ (Set.toFinite _) hgen le_rfl
      (cover_alpha N _ _ (coe_heckeAlphaC K N ℓ))
  · exact isIntegral_of_generators _ _ (heckeBetaC K N ℓ) ℓ _ (Set.toFinite _) hgen le_rfl
      (cover_beta N ℓ _ _ (coe_heckeBetaC K N ℓ))

end Integrality

section Level

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] (M s : ℕ) [NeZero M] [Fact s.Prime]

theorem not_dvd_mul (hpM : ¬ p ∣ M) (hps : p ≠ s) : ¬ p ∣ M * s := by
  intro h
  rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).mp h with h | h
  · exact hpM h
  · exact hps ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : s.Prime)).mp h)

theorem mem_M (hpM : ¬ p ∣ M) (hps : p ≠ s) : jqNModC K M ∈ modularFunctionFieldC K (M * s) := by
  rw [ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC K p (M * s) (not_dvd_mul p M s hpM hps)]
  exact jqModCd_mem_full K (M * s) (Dvd.intro s rfl)

theorem mem_s (hpM : ¬ p ∣ M) (hps : p ≠ s) : jqNModC K s ∈ modularFunctionFieldC K (M * s) := by
  rw [ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC K p (M * s) (not_dvd_mul p M s hpM hps)]
  exact jqModCd_mem_full K (M * s) (Dvd.intro_left M rfl)

end Level

section Restrictions

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
variable (M s : ℕ) [NeZero M] [Fact s.Prime]

theorem restrictAlong_levelAlphaC_mem_ssPlaces (hM : jqNModC K M ∈ modularFunctionFieldC K (M * s))
    (hα : (levelAlphaC K M s hM).toRingHom.IsIntegral)
    (W : Place K (modularFunctionFieldC K (M * s))) (hW : W ∈ ssPlaces p (M * s) K) :
    Place.restrictAlong (levelAlphaC K M s hM) hα W ∈ ssPlaces p M K := by
  letI := algebraAlong (levelAlphaC K M s hM)
  haveI := isScalarTower_along (levelAlphaC K M s hM)
  haveI := isIntegral_along (levelAlphaC K M s hM) hα
  show W.restrict (modularFunctionFieldC K M) ∈ ssPlaces p M K
  obtain ⟨hrat, ⟨hj, hjN⟩, hss⟩ := hW
  have hφj : algebraMap (modularFunctionFieldC K M) (modularFunctionFieldC K (M * s)) (jGeomGen K M) =
      jGeomGen K (M * s) := Subtype.ext (coe_levelAlphaC K M s hM _)
  have hφjN : algebraMap (modularFunctionFieldC K M) (modularFunctionFieldC K (M * s)) (jNGeomGen K M) =
      ⟨jqNModC K M, hM⟩ := Subtype.ext (coe_levelAlphaC K M s hM _)
  have hrat' : (W.restrict (modularFunctionFieldC K M)).IsRational := isRational_restrict W hrat
  have hjM : (⟨jqNModC K M, hM⟩ : modularFunctionFieldC K (M * s)) ∈ W.toValuationSubring :=
    jn_mem_valuationSubring _ M (jqModC_mem K (M * s)) hM W.toValuationSubring hj
  have hj' : jGeomGen K M ∈ (W.restrict (modularFunctionFieldC K M)).toValuationSubring := by
    rw [Place.mem_restrict_iff, hφj]; exact hj
  have hjN' : jNGeomGen K M ∈ (W.restrict (modularFunctionFieldC K M)).toValuationSubring := by
    rw [Place.mem_restrict_iff, hφjN]; exact hjM
  refine ⟨hrat', ⟨hj', hjN'⟩, ?_⟩
  rw [← Place.evalAt_algebraMap_eq_evalAt_restrict W hrat' hj', hφj]
  exact hss

theorem restrictAlong_levelBetaC_mem_ssPlaces (hps : p ≠ s) (hS : jqNModC K s ∈ modularFunctionFieldC K (M * s))
    (hβ : (levelBetaC K M s hS).toRingHom.IsIntegral)
    (W : Place K (modularFunctionFieldC K (M * s))) (hW : W ∈ ssPlaces p (M * s) K) :
    Place.restrictAlong (levelBetaC K M s hS) hβ W ∈ ssPlaces p M K := by
  letI := algebraAlong (levelBetaC K M s hS)
  haveI := isScalarTower_along (levelBetaC K M s hS)
  haveI := isIntegral_along (levelBetaC K M s hS) hβ
  show W.restrict (modularFunctionFieldC K M) ∈ ssPlaces p M K
  obtain ⟨hrat, ⟨hj, hjN⟩, hss⟩ := hW
  have hφj : algebraMap (modularFunctionFieldC K M) (modularFunctionFieldC K (M * s)) (jGeomGen K M) =
      ⟨jqNModC K s, hS⟩ := Subtype.ext (coe_levelBetaC K M s hS _)
  have hφjN : algebraMap (modularFunctionFieldC K M) (modularFunctionFieldC K (M * s)) (jNGeomGen K M) =
      jNGeomGen K (M * s) := by
    refine Subtype.ext ?_
    show qExpand K s (jqNModC K M) = jqNModC K (M * s)
    rw [jqNModC, jqNModC, qExpand_qExpand, qExpand_congr (Nat.mul_comm s M)]
  have hrat' : (W.restrict (modularFunctionFieldC K M)).IsRational := isRational_restrict W hrat
  have hjs : (⟨jqNModC K s, hS⟩ : modularFunctionFieldC K (M * s)) ∈ W.toValuationSubring :=
    jn_mem_valuationSubring _ s (jqModC_mem K (M * s)) hS W.toValuationSubring hj
  have hj' : jGeomGen K M ∈ (W.restrict (modularFunctionFieldC K M)).toValuationSubring := by
    rw [Place.mem_restrict_iff, hφj]; exact hjs
  have hjN' : jNGeomGen K M ∈ (W.restrict (modularFunctionFieldC K M)).toValuationSubring := by
    rw [Place.mem_restrict_iff, hφjN]; exact hjN
  refine ⟨hrat', ⟨hj', hjN'⟩, ?_⟩
  rw [← Place.evalAt_algebraMap_eq_evalAt_restrict W hrat' hj', hφj]
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData s
  exact evalAt_mem_ssJSet_of_evalModularPair_eq_zero (Ne.symm hps) data W hrat hj hjs
    (evalModularPair_j_jn _ data (jqModC_mem K (M * s)) hS) hss

theorem autOnPlaces_mem_ssPlaces (hps : p ≠ s) (hM : jqNModC K M ∈ modularFunctionFieldC K (M * s))
    (hS : jqNModC K s ∈ modularFunctionFieldC K (M * s))
    (σ : modularFunctionFieldC K (M * s) ≃ₐ[K] modularFunctionFieldC K (M * s))
    (hσs : σ ⟨jqNModC K s, hS⟩ = jGeomGen K (M * s)) (hσM : σ ⟨jqNModC K M, hM⟩ = jNGeomGen K (M * s))
    (W : Place K (modularFunctionFieldC K (M * s))) (hW : W ∈ ssPlaces p (M * s) K) :
    autOnPlaces K M s σ W ∈ ssPlaces p (M * s) K := by
  obtain ⟨hrat, ⟨hj, hjN⟩, hss⟩ := hW
  have he : ∀ c : K, σ.toRingEquiv (algebraMap K _ c) = algebraMap K _ c := fun c => σ.commutes c
  show Place.congrRingEquiv σ.toRingEquiv he W ∈ ssPlaces p (M * s) K
  set W' := Place.congrRingEquiv σ.toRingEquiv he W with hW'

  have hjs : (⟨jqNModC K s, hS⟩ : modularFunctionFieldC K (M * s)) ∈ W.toValuationSubring :=
    jn_mem_valuationSubring _ s (jqModC_mem K (M * s)) hS W.toValuationSubring hj
  have hjM : (⟨jqNModC K M, hM⟩ : modularFunctionFieldC K (M * s)) ∈ W.toValuationSubring :=
    jn_mem_valuationSubring _ M (jqModC_mem K (M * s)) hM W.toValuationSubring hj

  have hrat' : W'.IsRational := isRational_congrRingEquiv σ.toRingEquiv he W hrat

  have hcen : IsCentreOf K (M * s)
      (W.evalAt (⟨jqNModC K s, hS⟩ : modularFunctionFieldC K (M * s)),
        W.evalAt (⟨jqNModC K M, hM⟩ : modularFunctionFieldC K (M * s))) W' := by
    constructor
    · have h1 : jGeomGen K (M * s) - algebraMap K (modularFunctionFieldC K (M * s))
          (W.evalAt (⟨jqNModC K s, hS⟩ : modularFunctionFieldC K (M * s))) =
          σ.toRingEquiv ((⟨jqNModC K s, hS⟩ : modularFunctionFieldC K (M * s)) -
            algebraMap K (modularFunctionFieldC K (M * s)) (W.evalAt (⟨jqNModC K s, hS⟩ : modularFunctionFieldC K (M * s)))) := by
        rw [map_sub, he]
        congr 1
        exact hσs.symm
      show 0 < W'.ord _
      rw [h1, hW', Place.ord_congrRingEquiv]
      exact ord_sub_evalAt_pos_of_isRational hrat hjs (jn_sub_algebraMap_ne_zero _ s hS _)
    · have h1 : jNGeomGen K (M * s) - algebraMap K (modularFunctionFieldC K (M * s))
          (W.evalAt (⟨jqNModC K M, hM⟩ : modularFunctionFieldC K (M * s))) =
          σ.toRingEquiv ((⟨jqNModC K M, hM⟩ : modularFunctionFieldC K (M * s)) -
            algebraMap K (modularFunctionFieldC K (M * s)) (W.evalAt (⟨jqNModC K M, hM⟩ : modularFunctionFieldC K (M * s)))) := by
        rw [map_sub, he]
        congr 1
        exact hσM.symm
      show 0 < W'.ord _
      rw [h1, hW', Place.ord_congrRingEquiv]
      exact ord_sub_evalAt_pos_of_isRational hrat hjM (jn_sub_algebraMap_ne_zero _ M hM _)
  refine ⟨hrat', hcen.isAffineGeomPlace, ?_⟩
  rw [hcen.evalAt_jGeomGen]
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData s
  exact evalAt_mem_ssJSet_of_evalModularPair_eq_zero (Ne.symm hps) data W hrat hj hjs
    (evalModularPair_j_jn _ data (jqModC_mem K (M * s)) hS) hss

theorem exists_isAtkinLehnerLevelAut (hpM : ¬ p ∣ M) (hps : p ≠ s) (hsM : ¬ s ∣ M)
    (hM : jqNModC K M ∈ modularFunctionFieldC K (M * s)) (hS : jqNModC K s ∈ modularFunctionFieldC K (M * s)) :
    ∃ σ : modularFunctionFieldC K (M * s) ≃ₐ[K] modularFunctionFieldC K (M * s),
      IsAtkinLehnerLevelAut K M s hM hS σ := by
  haveI : NeZero s := ⟨(Fact.out : s.Prime).ne_zero⟩
  have hMK : (M : K) ≠ 0 := fun h => hpM ((CharP.cast_eq_zero_iff K p M).mp h)
  have hsK : (s : K) ≠ 0 := fun h => hps
    ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : s.Prime)).mp ((CharP.cast_eq_zero_iff K p s).mp h))
  obtain ⟨τ, hτ⟩ := ModularCurve.exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd K M s
    (Fact.out : s.Prime) hsM hMK hsK
  have heq : modularFunctionFieldC K (M * s) = modularFunctionFieldFullC K (M * s) :=
    ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC K p (M * s) (not_dvd_mul p M s hpM hps)
  let ι := IntermediateField.equivOfEq heq
  refine ⟨(ι.trans τ).trans ι.symm, ?_⟩

  have hv : ∀ (x : modularFunctionFieldC K (M * s)),
      ((((ι.trans τ).trans ι.symm) x : modularFunctionFieldC K (M * s)) : LaurentSeries K) =
        ((τ (ι x) : modularFunctionFieldFullC K (M * s)) : LaurentSeries K) := fun x => rfl
  have h1 := hτ 1 inferInstance (one_dvd M)
  have hMd := hτ M inferInstance dvd_rfl
  have e1 : ∀ (h : qExpand K 1 (jqModC K) ∈ modularFunctionFieldFullC K (M * s)),
      (⟨qExpand K 1 (jqModC K), h⟩ : modularFunctionFieldFullC K (M * s)) = ι (jGeomGen K (M * s)) := by
    intro h; refine Subtype.ext ?_; show qExpand K 1 (jqModC K) = jqModC K; exact qExpand_one_apply _
  have e2 : ∀ (h : qExpand K (1 * s) (jqModC K) ∈ modularFunctionFieldFullC K (M * s)),
      (⟨qExpand K (1 * s) (jqModC K), h⟩ : modularFunctionFieldFullC K (M * s)) = ι ⟨jqNModC K s, hS⟩ := by
    intro h; refine Subtype.ext ?_; show qExpand K (1 * s) (jqModC K) = jqNModC K s
    exact qExpand_congr (Nat.one_mul s) _
  have e3 : ∀ (h : qExpand K M (jqModC K) ∈ modularFunctionFieldFullC K (M * s)),
      (⟨qExpand K M (jqModC K), h⟩ : modularFunctionFieldFullC K (M * s)) = ι ⟨jqNModC K M, hM⟩ := by
    intro h; rfl
  have e4 : ∀ (h : qExpand K (M * s) (jqModC K) ∈ modularFunctionFieldFullC K (M * s)),
      (⟨qExpand K (M * s) (jqModC K), h⟩ : modularFunctionFieldFullC K (M * s)) = ι (jNGeomGen K (M * s)) := by
    intro h; rfl
  rw [e1, e2] at h1
  rw [e3, e4] at hMd
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (congrArg ι.symm h1.1).trans (ι.symm_apply_apply _)
  · exact (congrArg ι.symm h1.2).trans (ι.symm_apply_apply _)
  · exact (congrArg ι.symm hMd.2).trans (ι.symm_apply_apply _)
  · exact (congrArg ι.symm hMd.1).trans (ι.symm_apply_apply _)

theorem exists_isAtkinLehnerLevelAut_and_stable (hpM : ¬ p ∣ M) (hps : p ≠ s) (hsM : ¬ s ∣ M)
    (hM : jqNModC K M ∈ modularFunctionFieldC K (M * s)) (hS : jqNModC K s ∈ modularFunctionFieldC K (M * s)) :
    ∃ σ : modularFunctionFieldC K (M * s) ≃ₐ[K] modularFunctionFieldC K (M * s),
      IsAtkinLehnerLevelAut K M s hM hS σ ∧
      ∀ W, W ∈ ssPlaces p (M * s) K → autOnPlaces K M s σ W ∈ ssPlaces p (M * s) K := by
  obtain ⟨σ, hσ⟩ := exists_isAtkinLehnerLevelAut p K M s hpM hps hsM hM hS
  exact ⟨σ, hσ, fun W hW => autOnPlaces_mem_ssPlaces p K M s hps hM hS σ hσ.2.1 hσ.2.2.2 W hW⟩

end Restrictions

section Assembly

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
variable (M s : ℕ) [NeZero M] [NeZero s] [Fact s.Prime]

def build (hsM : ¬ s ∣ M) (hpM : ¬ p ∣ M) (hps : p ≠ s) : SSLevelDatum p K M s :=
  have hM := mem_M p K M s hpM hps
  have hS := mem_s p K M s hpM hps
  have hAL := exists_isAtkinLehnerLevelAut_and_stable p K M s hpM hps hsM hM hS
  have hΦ : ∃ Φ : ModularPolynomialData p, KroneckerCongruence p Φ :=
    ⟨(ModularCurve.nonempty_modularPolynomialData p).some, ModularCurve.kroneckerCongruence p _⟩
  { mem_M := hM
    mem_s := hS
    fstIntegral := levelAlphaC_isIntegral M s hM
    sndIntegral := levelBetaC_isIntegral M s hS
    legsIntegral := fun N _ ℓ _ => legs_isIntegral N ℓ
    fst_mem := restrictAlong_levelAlphaC_mem_ssPlaces p K M s hM _
    snd_mem := restrictAlong_levelBetaC_mem_ssPlaces p K M s hps hS _
    atkinLehnerAut := hAL.choose
    isAtkinLehner := hAL.choose_spec.1
    stable := hAL.choose_spec.2
    frobData := hΦ.choose
    kronecker := hΦ.choose_spec }

end Assembly

end SSLevelSlot

theorem solution
    (N q q' : ℕ) [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q')
    [CharP (IsLocalRing.ResidueField ↥A) q'] [DecidableEq (IsLocalRing.ResidueField ↥A)] :
    Nonempty (SSLevelDatum q' (IsLocalRing.ResidueField ↥A) N q) := by
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  exact ⟨SSLevelSlot.build q' (IsLocalRing.ResidueField ↥A) N q hqN hq'N hqq'⟩

end
end S_ModularCurve_nonempty_ssLevelDatum
end P2MW
export P2MW.S_ModularCurve_nonempty_ssLevelDatum (solution)
