-- Prove2me | solution 1 for ModularCurve.restrictAlong_heckeAlphaC_mem_ssPlaces_iff_restrictAlong_heckeBetaC_mem_ssPlaces_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/8192dac2-65df-5718-a69b-2960f369b846

import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_FibrePoly
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaC
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaC
import Theorems.Thm_ModularCurve_separableAlong_heckeAlphaC_heckeBetaC
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_one_lt
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Theorems.Thm_ModularCurve_mem_ssJSet_of_mem_roots_fibrePoly
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Definitions.Def_ModularCurve_PlaceWidth
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_ssPlaces_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_restrictAlong_heckeAlphaC_mem_ssPlaces_iff_restrictAlong_heckeBetaC_mem_ssPlaces_of_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

p2m_open "AlgebraicCurve ModularCurve~coeffMap_injective"

namespace DegPair

section Transport

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

theorem algHom_eq_of_coe_eq {A E : IntermediateField k L} (ψ ψ' : ↥A →ₐ[k] ↥E)
    (h : ∀ x, (ψ x : L) = (ψ' x : L)) : ψ = ψ' :=
  AlgHom.ext fun x => Subtype.ext (h x)

theorem finiteAlong_transport {A E₁ E₂ : IntermediateField k L} (hE : E₁ = E₂)
    (ψ₁ : ↥A →ₐ[k] ↥E₁) (ψ₂ : ↥A →ₐ[k] ↥E₂) (h : ∀ x, (ψ₁ x : L) = (ψ₂ x : L))
    (hf : FiniteAlong k ψ₁) : FiniteAlong k ψ₂ := by
  subst hE
  rw [← algHom_eq_of_coe_eq ψ₁ ψ₂ h]; exact hf

theorem separableAlong_transport {A E₁ E₂ : IntermediateField k L} (hE : E₁ = E₂)
    (ψ₁ : ↥A →ₐ[k] ↥E₁) (ψ₂ : ↥A →ₐ[k] ↥E₂) (h : ∀ x, (ψ₁ x : L) = (ψ₂ x : L))
    (hf : SeparableAlong k ψ₁) : SeparableAlong k ψ₂ := by
  subst hE
  rw [← algHom_eq_of_coe_eq ψ₁ ψ₂ h]; exact hf

end Transport

section Places

variable (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N]

theorem isRational (x : Place K ↥(modularFunctionFieldC K N)) : x.IsRational := by
  haveI := isCurveOver_modularFunctionFieldC_of_perfectField K N
  exact (Place.isRational_iff_deg_eq_one x).2 (IsCurveOver.deg_eq_one_of_isAlgClosed x)

omit [IsAlgClosed K] in

theorem isIntegral_jNGeomGen :
    IsIntegral (Algebra.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N))) (jNGeomGen K N) := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  set A := Algebra.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N)) with hA
  have hjA : jGeomGen K N ∈ A := Algebra.subset_adjoin rfl
  let g : Polynomial ℤ →+* ↥A := Polynomial.eval₂RingHom (Int.castRingHom ↥A) ⟨jGeomGen K N, hjA⟩
  have hg : (algebraMap ↥A ↥(modularFunctionFieldC K N)).comp g
      = Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldC K N)) (jGeomGen K N) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [g]
  refine ⟨data.Φ.map g, data.monic.map g, ?_⟩
  rw [Polynomial.eval₂_map, hg]
  exact evalModularPair_jGeomGen_eq_zero K N data

omit [IsAlgClosed K] in
theorem isAffineGeomPlace_of_mem (x : Place K ↥(modularFunctionFieldC K N))
    (hj : jGeomGen K N ∈ x.toValuationSubring) : IsAffineGeomPlace K N x :=
  ⟨hj, x.mem_toValuationSubring_of_isIntegral_adjoin hj (isIntegral_jNGeomGen K N)⟩

end Places

section Alpha

variable (q' : ℕ) (M s : ℕ) [NeZero M] [NeZero s] [NeZero (M * s)]
  {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]
  (φ₀ : ↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s)))
  (hφ₀ : φ₀.toRingHom.IsIntegral)
  (hφα : ∀ x, ((φ₀ x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)

include hφα in
theorem map_jGeomGen : φ₀ (jGeomGen k M) = jGeomGen k (M * s) :=
  Subtype.ext (by rw [hφα]; rfl)

include hφα in

theorem ssPlaces_alpha (p : Place k ↥(modularFunctionFieldC k (M * s))) :
    p ∈ ssPlaces q' (M * s) k ↔ Place.restrictAlong φ₀ hφ₀ p ∈ ssPlaces q' M k := by
  letI := algebraAlong φ₀
  haveI := isScalarTower_along φ₀
  haveI := isIntegral_along φ₀ hφ₀
  have hres : Place.restrictAlong φ₀ hφ₀ p = p.restrict ↥(modularFunctionFieldC k M) := rfl
  have hratM := isRational k M (Place.restrictAlong φ₀ hφ₀ p)
  have hratMs := isRational k (M * s) p

  have hjmem : jGeomGen k M ∈ (Place.restrictAlong φ₀ hφ₀ p).toValuationSubring ↔
      jGeomGen k (M * s) ∈ p.toValuationSubring := by
    rw [hres, Place.mem_restrict_iff, show algebraMap _ _ (jGeomGen k M) = φ₀ (jGeomGen k M) from rfl,
      map_jGeomGen M s φ₀ hφα]

  have hval : jGeomGen k (M * s) ∈ p.toValuationSubring →
      (Place.restrictAlong φ₀ hφ₀ p).evalAt (jGeomGen k M) = p.evalAt (jGeomGen k (M * s)) := by
    intro hmem
    rw [hres, ← map_jGeomGen M s φ₀ hφα, show φ₀ (jGeomGen k M) = algebraMap _ _ (jGeomGen k M) from rfl]
    refine (Place.evalAt_algebraMap_eq_evalAt_restrict p (hres ▸ hratM) ?_).symm
    rw [Place.mem_restrict_iff, show algebraMap _ _ (jGeomGen k M) = φ₀ (jGeomGen k M) from rfl,
      map_jGeomGen M s φ₀ hφα]
    exact hmem
  rw [mem_ssPlaces_iff, mem_ssPlaces_iff, isSupersingularPlace_iff, isSupersingularPlace_iff]
  constructor
  · rintro ⟨-, haff, hss⟩
    refine ⟨hratM, isAffineGeomPlace_of_mem k M _ (hjmem.2 haff.1), ?_⟩
    rw [hval haff.1]; exact hss
  · rintro ⟨-, haff, hss⟩
    have hj : jGeomGen k (M * s) ∈ p.toValuationSubring := hjmem.1 haff.1
    refine ⟨hratMs, isAffineGeomPlace_of_mem k (M * s) _ hj, ?_⟩
    rw [← hval hj]; exact hss

end Alpha

section FinSep

variable (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
  (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M)
  {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k]

include hs hsq' hq'M in
theorem not_dvd_mul : ¬ q' ∣ M * s := by
  intro h
  rcases (Nat.Prime.dvd_mul (Fact.out)).mp h with h1 | h2
  · exact hq'M h1
  · exact hsq' ((Nat.prime_dvd_prime_iff_eq (Fact.out) hs).mp h2).symm

include hs hsq' hq'M in

theorem roof_eq [NeZero (M * s)] : charLDegeneracyRoof k M s = modularFunctionFieldC k (M * s) := by
  haveI : NeZero q' := ⟨(Fact.out : q'.Prime).ne_zero⟩
  rw [charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul k q' M s (not_dvd_mul M s q' hs hsq' hq'M),
    modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos k q' (M * s) (not_dvd_mul M s q' hs hsq' hq'M)]

include hs hsq' hq'M in
theorem finite_separable [NeZero (M * s)]
    (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
    (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
    (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x) :
    (∀ i, FiniteAlong k (φ i)) ∧ (∀ i, SeparableAlong k (φ i)) := by
  haveI : Fact s.Prime := ⟨hs⟩
  have hR := roof_eq M s q' hs hsq' hq'M (k := k)
  have hcoeα : ∀ x, ((heckeAlphaC k M s x : ↥(charLDegeneracyRoof k M s)) : LaurentSeries k) =
      ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) := fun x => by
    rw [coe_heckeAlphaC, hφα]
  have hcoeβ : ∀ x, ((heckeBetaC k M s x : ↥(charLDegeneracyRoof k M s)) : LaurentSeries k) =
      ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) := fun x => by
    rw [coe_heckeBetaC, hφβ]
  obtain ⟨hsepα, hsepβ⟩ := separableAlong_heckeAlphaC_heckeBetaC k (ℓ := q') M s (not_dvd_mul M s q' hs hsq' hq'M)
  refine ⟨?_, ?_⟩
  · refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · exact finiteAlong_transport hR _ _ hcoeα (finiteAlong_heckeAlphaC k M s)
    · exact finiteAlong_transport hR _ _ hcoeβ (finiteAlong_heckeBetaC k M s)
  · refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · exact separableAlong_transport hR _ _ hcoeα hsepα
    · exact separableAlong_transport hR _ _ hcoeβ hsepβ

end FinSep

end DegPair

namespace DegPair

section EvalPair

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalModularPair_evalAt_eq_zero (w : Place K F) (hrat : w.IsRational) {x y : F}
    (hx : x ∈ w.toValuationSubring) (hy : y ∈ w.toValuationSubring) (Φ : Polynomial (Polynomial ℤ))
    (h : evalModularPair x y Φ = 0) :
    evalModularPair (w.evalAt x) (w.evalAt y) Φ = 0 := by
  apply (algebraMap K w.ResidueField).injective
  rw [map_zero, map_evalModularPair, w.algebraMap_evalAt hrat hx, w.algebraMap_evalAt hrat hy,
    ← map_evalModularPair (IsLocalRing.residue w.toValuationSubring)]
  have h0 : evalModularPair (⟨x, hx⟩ : w.toValuationSubring) ⟨y, hy⟩ Φ = 0 := by
    apply Subtype.val_injective
    have := map_evalModularPair w.toValuationSubring.subtype ⟨x, hx⟩ ⟨y, hy⟩ Φ
    rw [show w.toValuationSubring.subtype ⟨x, hx⟩ = x from rfl,
      show w.toValuationSubring.subtype ⟨y, hy⟩ = y from rfl, h] at this
    exact this
  rw [h0, map_zero]

end EvalPair

section Beta

variable (M s : ℕ) [NeZero M] [NeZero s] [NeZero (M * s)]
  {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]
  (φ₁ : ↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s)))
  (hφ₁ : φ₁.toRingHom.IsIntegral)
  (hφβ : ∀ x, ((φ₁ x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x)

include hφβ in
theorem coe_map_jGeomGen_beta : ((φ₁ (jGeomGen k M) : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k)
    = jqNModC k s := by
  rw [hφβ]; rfl

include hφβ in

theorem evalModularPair_beta (data : ModularPolynomialData s) :
    evalModularPair (jGeomGen k (M * s)) (φ₁ (jGeomGen k M)) data.Φ = 0 := by
  have hval := map_evalModularPair (modularFunctionFieldC k (M * s)).val.toRingHom
    (jGeomGen k (M * s)) (φ₁ (jGeomGen k M)) data.Φ
  have h1 : (modularFunctionFieldC k (M * s)).val.toRingHom (jGeomGen k (M * s)) = jqModC k := rfl
  have h2 : (modularFunctionFieldC k (M * s)).val.toRingHom (φ₁ (jGeomGen k M)) = jqNModC k s :=
    coe_map_jGeomGen_beta M s φ₁ hφβ
  rw [h1, h2, evalModularPair_jq_eq_zero k data] at hval
  exact (map_eq_zero_iff _ (modularFunctionFieldC k (M * s)).val.toRingHom.injective).mp hval

include hφβ in

theorem isIntegral_map_jGeomGen_beta :
    IsIntegral (Algebra.adjoin k ({jGeomGen k (M * s)} : Set ↥(modularFunctionFieldC k (M * s))))
      (φ₁ (jGeomGen k M)) := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData s
  set A := Algebra.adjoin k ({jGeomGen k (M * s)} : Set ↥(modularFunctionFieldC k (M * s))) with hA
  have hjA : jGeomGen k (M * s) ∈ A := Algebra.subset_adjoin rfl
  let g : Polynomial ℤ →+* ↥A := Polynomial.eval₂RingHom (Int.castRingHom ↥A) ⟨jGeomGen k (M * s), hjA⟩
  have hg : (algebraMap ↥A ↥(modularFunctionFieldC k (M * s))).comp g
      = Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldC k (M * s))) (jGeomGen k (M * s)) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [g]
  refine ⟨data.Φ.map g, data.monic.map g, ?_⟩
  rw [Polynomial.eval₂_map, hg]
  exact evalModularPair_beta M s φ₁ hφβ data

include hφβ in

theorem isAffine_restrict_beta (p : Place k ↥(modularFunctionFieldC k (M * s)))
    (hp : IsAffineGeomPlace k (M * s) p) : IsAffineGeomPlace k M (Place.restrictAlong φ₁ hφ₁ p) := by
  letI := algebraAlong φ₁
  haveI := isScalarTower_along φ₁
  haveI := isIntegral_along φ₁ hφ₁
  have hy : φ₁ (jGeomGen k M) ∈ p.toValuationSubring :=
    p.mem_toValuationSubring_of_isIntegral_adjoin hp.1 (isIntegral_map_jGeomGen_beta M s φ₁ hφβ)
  refine isAffineGeomPlace_of_mem k M _ ?_
  show jGeomGen k M ∈ (p.restrict ↥(modularFunctionFieldC k M)).toValuationSubring
  rw [Place.mem_restrict_iff]
  exact hy

include hφβ in

theorem rootPair_beta (p : Place k ↥(modularFunctionFieldC k (M * s)))
    (hp : IsAffineGeomPlace k (M * s) p) (data : ModularPolynomialData s) :
    evalModularPair (p.evalAt (jGeomGen k (M * s)))
      ((Place.restrictAlong φ₁ hφ₁ p).evalAt (jGeomGen k M)) data.Φ = 0 := by
  letI := algebraAlong φ₁
  haveI := isScalarTower_along φ₁
  haveI := isIntegral_along φ₁ hφ₁
  have hratMs := isRational k (M * s) p
  have hratM := isRational k M (Place.restrictAlong φ₁ hφ₁ p)
  have hy : φ₁ (jGeomGen k M) ∈ p.toValuationSubring :=
    p.mem_toValuationSubring_of_isIntegral_adjoin hp.1 (isIntegral_map_jGeomGen_beta M s φ₁ hφβ)
  have hres : Place.restrictAlong φ₁ hφ₁ p = p.restrict ↥(modularFunctionFieldC k M) := rfl
  have hval : (Place.restrictAlong φ₁ hφ₁ p).evalAt (jGeomGen k M) = p.evalAt (φ₁ (jGeomGen k M)) := by
    rw [hres, show φ₁ (jGeomGen k M) = algebraMap _ _ (jGeomGen k M) from rfl]
    refine (Place.evalAt_algebraMap_eq_evalAt_restrict p (hres ▸ hratM) ?_).symm
    rw [Place.mem_restrict_iff]; exact hy
  rw [hval]
  exact evalModularPair_evalAt_eq_zero p hratMs hp.1 hy data.Φ (evalModularPair_beta M s φ₁ hφβ data)

include hφβ in

theorem isRoot_fibrePoly_beta (p : Place k ↥(modularFunctionFieldC k (M * s)))
    (hp : IsAffineGeomPlace k (M * s) p) (data : ModularPolynomialData s) :
    (fibrePoly data.Φ (p.evalAt (jGeomGen k (M * s)))).IsRoot
      ((Place.restrictAlong φ₁ hφ₁ p).evalAt (jGeomGen k M)) := by
  have := rootPair_beta M s φ₁ hφ₁ hφβ p hp data
  rw [Polynomial.IsRoot.def, fibrePoly, Polynomial.eval_map]
  exact this

end Beta

section AlphaAffine

variable (M s : ℕ) [NeZero M] [NeZero s] [NeZero (M * s)]
  {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]
  (φ₀ : ↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s)))
  (hφ₀ : φ₀.toRingHom.IsIntegral)
  (hφα : ∀ x, ((φ₀ x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)

include hφα in
theorem isAffine_alpha_iff (p : Place k ↥(modularFunctionFieldC k (M * s))) :
    IsAffineGeomPlace k M (Place.restrictAlong φ₀ hφ₀ p) ↔ IsAffineGeomPlace k (M * s) p := by
  letI := algebraAlong φ₀
  haveI := isScalarTower_along φ₀
  haveI := isIntegral_along φ₀ hφ₀
  have hres : Place.restrictAlong φ₀ hφ₀ p = p.restrict ↥(modularFunctionFieldC k M) := rfl
  have hjmem : jGeomGen k M ∈ (Place.restrictAlong φ₀ hφ₀ p).toValuationSubring ↔
      jGeomGen k (M * s) ∈ p.toValuationSubring := by
    rw [hres, Place.mem_restrict_iff, show algebraMap _ _ (jGeomGen k M) = φ₀ (jGeomGen k M) from rfl,
      map_jGeomGen M s φ₀ hφα]
  exact ⟨fun h => isAffineGeomPlace_of_mem k (M * s) _ (hjmem.1 h.1),
    fun h => isAffineGeomPlace_of_mem k M _ (hjmem.2 h.1)⟩

include hφα in
theorem evalAt_alpha (p : Place k ↥(modularFunctionFieldC k (M * s)))
    (hp : IsAffineGeomPlace k (M * s) p) :
    (Place.restrictAlong φ₀ hφ₀ p).evalAt (jGeomGen k M) = p.evalAt (jGeomGen k (M * s)) := by
  letI := algebraAlong φ₀
  haveI := isScalarTower_along φ₀
  haveI := isIntegral_along φ₀ hφ₀
  have hres : Place.restrictAlong φ₀ hφ₀ p = p.restrict ↥(modularFunctionFieldC k M) := rfl
  have hratM := isRational k M (Place.restrictAlong φ₀ hφ₀ p)
  rw [hres, ← map_jGeomGen M s φ₀ hφα, show φ₀ (jGeomGen k M) = algebraMap _ _ (jGeomGen k M) from rfl]
  refine (Place.evalAt_algebraMap_eq_evalAt_restrict p (hres ▸ hratM) ?_).symm
  rw [Place.mem_restrict_iff, show algebraMap _ _ (jGeomGen k M) = φ₀ (jGeomGen k M) from rfl,
    map_jGeomGen M s φ₀ hφα]
  exact hp.1

end AlphaAffine

end DegPair

namespace DegPair

section Swap

theorem evalModularPair_swap_int (N : ℕ) [NeZero N] (hN : 1 < N) (data : ModularPolynomialData N) :
    evalModularPair (jqIntN N) jqInt data.Φ = 0 := by
  apply laurentMap_injective (f := Int.castRingHom ℚ) Int.cast_injective
  rw [map_zero, map_evalModularPair, laurentMap_jqIntN, laurentMap_jqInt]
  have hsym := ModularPolynomialData.evalSymm_of_one_lt N hN data (jqN N) jq
  have h1 : Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) (jqN N)
      = (Polynomial.aeval (R := ℤ) (jqN N)).toRingHom :=
    Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)
  unfold evalModularPair
  rw [h1, hsym]
  exact data.eval_eq_zero

theorem laurentMap_jqInt_geom (K : Type*) [Field K] : laurentMap (Int.castRingHom K) jqInt = jqModC K := by
  rw [jqModC, jqInt, map_mul, laurentMap_single, laurentMap_ofPowerSeries, map_one]

theorem evalModularPair_swap_geom (K : Type*) [Field K] (N : ℕ) [NeZero N] (hN : 1 < N)
    (data : ModularPolynomialData N) :
    evalModularPair (jqNModC K N) (jqModC K) data.Φ = 0 := by
  have h := congrArg (laurentMap (Int.castRingHom K)) (evalModularPair_swap_int N hN data)
  rwa [map_zero, map_evalModularPair, laurentMap_jqIntN_geom, laurentMap_jqInt_geom] at h

end Swap

section BetaConverse

variable (M s : ℕ) [NeZero M] [NeZero s] [NeZero (M * s)] (hs : s.Prime)
  {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]
  (φ₁ : ↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s)))
  (hφ₁ : φ₁.toRingHom.IsIntegral)
  (hφβ : ∀ x, ((φ₁ x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x)

include hs hφβ in
theorem evalModularPair_beta_swap (data : ModularPolynomialData s) :
    evalModularPair (φ₁ (jGeomGen k M)) (jGeomGen k (M * s)) data.Φ = 0 := by
  have hval := map_evalModularPair (modularFunctionFieldC k (M * s)).val.toRingHom
    (φ₁ (jGeomGen k M)) (jGeomGen k (M * s)) data.Φ
  have h1 : (modularFunctionFieldC k (M * s)).val.toRingHom (jGeomGen k (M * s)) = jqModC k := rfl
  have h2 : (modularFunctionFieldC k (M * s)).val.toRingHom (φ₁ (jGeomGen k M)) = jqNModC k s :=
    coe_map_jGeomGen_beta M s φ₁ hφβ
  rw [h1, h2, evalModularPair_swap_geom k s hs.one_lt data] at hval
  exact (map_eq_zero_iff _ (modularFunctionFieldC k (M * s)).val.toRingHom.injective).mp hval

include hs hφβ in

theorem isIntegral_jGeomGen_over_beta :
    IsIntegral (Algebra.adjoin k ({φ₁ (jGeomGen k M)} : Set ↥(modularFunctionFieldC k (M * s))))
      (jGeomGen k (M * s)) := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData s
  set A := Algebra.adjoin k ({φ₁ (jGeomGen k M)} : Set ↥(modularFunctionFieldC k (M * s))) with hA
  have hjA : φ₁ (jGeomGen k M) ∈ A := Algebra.subset_adjoin rfl
  let g : Polynomial ℤ →+* ↥A := Polynomial.eval₂RingHom (Int.castRingHom ↥A) ⟨φ₁ (jGeomGen k M), hjA⟩
  have hg : (algebraMap ↥A ↥(modularFunctionFieldC k (M * s))).comp g
      = Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldC k (M * s))) (φ₁ (jGeomGen k M)) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [g]
  refine ⟨data.Φ.map g, data.monic.map g, ?_⟩
  rw [Polynomial.eval₂_map, hg]
  exact evalModularPair_beta_swap M s hs φ₁ hφβ data

include hs hφβ in

theorem isAffine_beta_iff (p : Place k ↥(modularFunctionFieldC k (M * s))) :
    IsAffineGeomPlace k M (Place.restrictAlong φ₁ hφ₁ p) ↔ IsAffineGeomPlace k (M * s) p := by
  letI := algebraAlong φ₁
  haveI := isScalarTower_along φ₁
  haveI := isIntegral_along φ₁ hφ₁
  refine ⟨fun h => ?_, isAffine_restrict_beta M s φ₁ hφ₁ hφβ p⟩
  have hy : φ₁ (jGeomGen k M) ∈ p.toValuationSubring := by
    have := h.1
    rw [show Place.restrictAlong φ₁ hφ₁ p = p.restrict ↥(modularFunctionFieldC k M) from rfl,
      Place.mem_restrict_iff] at this
    exact this
  exact isAffineGeomPlace_of_mem k (M * s) _
    (p.mem_toValuationSubring_of_isIntegral_adjoin hy (isIntegral_jGeomGen_over_beta M s hs φ₁ hφβ))

end BetaConverse

section Rational

variable (M s : ℕ) [NeZero M] [NeZero s] [NeZero (M * s)]
  {k : Type*} [Field k] [IsAlgClosed k]
  (ψ : ↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))) (hψ : ψ.toRingHom.IsIntegral)

theorem isRational_iff (p : Place k ↥(modularFunctionFieldC k (M * s))) :
    (Place.restrictAlong ψ hψ p).IsRational ↔ p.IsRational :=
  iff_of_true (isRational k M _) (isRational k (M * s) p)

end Rational

end DegPair

open Polynomial

namespace CuspsLegsE4

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) : Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  apply hf
  rw [← coeffMap_coeff, ← coeffMap_coeff, h]

theorem map_eval₂_aeval_toRingHom {A B : Type*} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B]
    (g : A →+* B) (Φ : Polynomial (Polynomial ℤ)) (a b : A) :
    g (Φ.eval₂ (aeval (R := ℤ) a).toRingHom b) = Φ.eval₂ (aeval (R := ℤ) (g a)).toRingHom (g b) := by
  rw [hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp

theorem eval₂_aeval_jqModC_jqNModC_eq_zero (K : Type*) [Field K] (ℓ : ℕ) [NeZero ℓ]
    (data : ModularPolynomialData ℓ) :
    data.Φ.eval₂ (aeval (R := ℤ) (jqModC K)).toRingHom (jqNModC K ℓ) = 0 := by
  have h0 : data.Φ.eval₂ (aeval (R := ℤ) (jqModC ℚ)).toRingHom (jqNModC ℚ ℓ) = 0 := by
    rw [jqNModC_rat, jqModC_rat]
    exact data.eval_eq_zero
  have hZ : data.Φ.eval₂ (aeval (R := ℤ) (jqModC ℤ)).toRingHom (jqNModC ℤ ℓ) = 0 := by
    apply coeffMap_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
    rw [map_eval₂_aeval_toRingHom, coeffMap_jqNModC, coeffMap_jqModC, h0, map_zero]
  have := congrArg (coeffMap (Int.castRingHom K)) hZ
  rwa [map_eval₂_aeval_toRingHom, coeffMap_jqNModC, coeffMap_jqModC, map_zero] at this

theorem eval₂_aeval_jqNModC_jqModC_eq_zero (K : Type*) [Field K] (ℓ : ℕ) [NeZero ℓ]
    (data : ModularPolynomialData ℓ) (hsym : EvalSymm data.Φ) :
    data.Φ.eval₂ (aeval (R := ℤ) (jqNModC K ℓ)).toRingHom (jqModC K) = 0 := by
  have h0 : data.Φ.eval₂ (aeval (R := ℤ) (jqNModC ℚ ℓ)).toRingHom (jqModC ℚ) = 0 := by
    rw [jqNModC_rat, jqModC_rat, hsym (jqN ℓ) jq]
    exact data.eval_eq_zero
  have hZ : data.Φ.eval₂ (aeval (R := ℤ) (jqNModC ℤ ℓ)).toRingHom (jqModC ℤ) = 0 := by
    apply coeffMap_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
    rw [map_eval₂_aeval_toRingHom, coeffMap_jqNModC, coeffMap_jqModC, h0, map_zero]
  have := congrArg (coeffMap (Int.castRingHom K)) hZ
  rwa [map_eval₂_aeval_toRingHom, coeffMap_jqNModC, coeffMap_jqModC, map_zero] at this

theorem isIntegral_adjoin_of_eval₂_eq_zero (K : Type*) [Field K] (F : IntermediateField K (LaurentSeries K))
    (Φ : Polynomial (Polynomial ℤ)) (hΦ : Φ.Monic) (a b : ↥F)
    (h : Φ.eval₂ (aeval (R := ℤ) (a : LaurentSeries K)).toRingHom (b : LaurentSeries K) = 0) :
    IsIntegral (Algebra.adjoin K ({a} : Set ↥F)) b := by
  refine ⟨Φ.map (Polynomial.eval₂RingHom (Int.castRingHom _) ⟨a, Algebra.self_mem_adjoin_singleton K _⟩),
    hΦ.map _, ?_⟩
  apply (algebraMap ↥F (LaurentSeries K)).injective
  have hcomp : (algebraMap ↥F (LaurentSeries K)).comp
      ((algebraMap _ ↥F).comp
        (Polynomial.eval₂RingHom (Int.castRingHom _)
          (⟨a, Algebra.self_mem_adjoin_singleton K _⟩ : ↥(Algebra.adjoin K ({a} : Set ↥F))))) =
      (aeval (R := ℤ) (a : LaurentSeries K)).toRingHom := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, eval₂_X, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, aeval_X]
    rfl
  rw [eval₂_map, hom_eval₂, hcomp, map_zero]
  exact h

end CuspsLegsE4

namespace FltWs24
namespace DegPair

variable {k : Type*} [Field k] [IsAlgClosed k]

theorem isRational_C (N : ℕ) [NeZero N] (x : Place k ↥(modularFunctionFieldC k N)) : x.IsRational := by
  haveI := isCurveOver_modularFunctionFieldC_of_perfectField k N
  exact (Place.isRational_iff_deg_eq_one x).2 (IsCurveOver.deg_eq_one_of_isAlgClosed x)

theorem mem_iff_mem_restrictAlong {F F' : Type*} [Field F] [Field F'] [Algebra k F] [Algebra k F']
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral) (P : Place k F') (g : F) (hg : g ≠ 0)
    (he : 0 < Place.ramificationIndexAlong φ P) :
    φ g ∈ P.toValuationSubring ↔ g ∈ (P.restrictAlong φ hφ).toValuationSubring := by
  have hφg : φ g ≠ 0 := (map_ne_zero φ).mpr hg
  rw [Place.mem_iff_ord_nonneg _ hφg, Place.mem_iff_ord_nonneg _ hg, Place.ord_restrictAlong φ hφ P g]
  constructor
  · intro h
    by_contra hneg
    push Not at hneg
    have : (Place.ramificationIndexAlong φ P : ℤ) * (P.restrictAlong φ hφ).ord g < 0 :=
      mul_neg_of_pos_of_neg (by exact_mod_cast he) hneg
    omega
  · intro h
    exact mul_nonneg (by positivity) h

theorem evalAt_along (N : ℕ) [NeZero N] {F' : Type*} [Field F'] [Algebra k F']
    (φ : ↥(modularFunctionFieldC k N) →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral)
    (P : Place k F') (g : ↥(modularFunctionFieldC k N))
    (he : 0 < Place.ramificationIndexAlong φ P) :
    P.evalAt (φ g) = (P.restrictAlong φ hφ).evalAt g := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [map_zero, show (0 : F') = algebraMap k _ 0 from (map_zero _).symm,
      show (0 : ↥(modularFunctionFieldC k N)) = algebraMap k _ 0 from (map_zero _).symm,
      Place.evalAt_algebraMap, Place.evalAt_algebraMap]
  by_cases hmem : g ∈ (P.restrictAlong φ hφ).toValuationSubring
  · letI := AlgebraicCurve.algebraAlong φ
    haveI := AlgebraicCurve.isScalarTower_along φ
    haveI := AlgebraicCurve.isIntegral_along φ hφ
    exact Place.evalAt_algebraMap_eq_evalAt_restrict P (isRational_C N _) hmem
  · have hmem' : φ g ∉ P.toValuationSubring := fun h => hmem ((mem_iff_mem_restrictAlong φ hφ P g hg he).mp h)
    unfold Place.evalAt
    rw [dif_neg hmem', dif_neg hmem]

theorem rIA_pos {F F' : Type*} [Field F] [Field F'] [Algebra k F] [Algebra k F']
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral) (P : Place k F') :
    0 < Place.ramificationIndexAlong φ P := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI := AlgebraicCurve.isScalarTower_along φ
  haveI := AlgebraicCurve.isIntegral_along φ hφ
  exact P.ramificationIndex_pos (F := F)

omit [IsAlgClosed k] in
theorem isRoot_fibrePoly_evalAt (F : IntermediateField k (LaurentSeries k))
    (Φ : Polynomial (Polynomial ℤ)) (a b : ↥F)
    (h : Φ.eval₂ (aeval (R := ℤ) (a : LaurentSeries k)).toRingHom (b : LaurentSeries k) = 0)
    (v : Place k ↥F) (hv : v.IsRational) (ha : a ∈ v.toValuationSubring) (hb : b ∈ v.toValuationSubring) :
    (fibrePoly Φ (v.evalAt a)).IsRoot (v.evalAt b) := by
  have hF : Φ.eval₂ (aeval (R := ℤ) a).toRingHom b = 0 := by
    apply (algebraMap ↥F (LaurentSeries k)).injective
    rw [CuspsLegsE4.map_eval₂_aeval_toRingHom, map_zero]
    exact h
  have hO : Φ.eval₂ (aeval (R := ℤ) (⟨a, ha⟩ : ↥v.toValuationSubring)).toRingHom ⟨b, hb⟩ = 0 := by
    apply Subtype.val_injective
    have := CuspsLegsE4.map_eval₂_aeval_toRingHom (v.toValuationSubring.subtype) Φ ⟨a, ha⟩ ⟨b, hb⟩
    rw [ZeroMemClass.coe_zero]
    exact this.trans hF
  have hres := congrArg (IsLocalRing.residue ↥v.toValuationSubring) hO
  rw [CuspsLegsE4.map_eval₂_aeval_toRingHom, map_zero,
    ← v.algebraMap_evalAt hv ha, ← v.algebraMap_evalAt hv hb,
    ← CuspsLegsE4.map_eval₂_aeval_toRingHom, map_eq_zero] at hres
  unfold fibrePoly
  rw [IsRoot, eval_map]
  have hhom : Polynomial.eval₂RingHom (Int.castRingHom k) (v.evalAt a) = (aeval (R := ℤ) (v.evalAt a)).toRingHom := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp
  rw [hhom]
  exact hres

end FltWs24.DegPair

namespace Ws47
namespace FaceS

open DegPair

section

variable (M s q' : ℕ) [NeZero M] [NeZero s] [Fact q'.Prime]
variable {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k]

theorem ssPlaces_beta [NeZero (M * s)] (hs : s.Prime) (hsq' : s ≠ q')
    (φ₁ : ↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s)))
    (hφ₁ : φ₁.toRingHom.IsIntegral)
    (hφβ : ∀ x, ((φ₁ x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x)
    (p : Place k ↥(modularFunctionFieldC k (M * s))) :
    p ∈ ssPlaces q' (M * s) k ↔ Place.restrictAlong φ₁ hφ₁ p ∈ ssPlaces q' M k := by
  classical
  haveI : Fact s.Prime := ⟨hs⟩
  obtain ⟨data, hsym⟩ := ModularCurve.exists_modularPolynomialData_evalSymm s
  have hmon : ∀ c : k, fibrePoly data.Φ c ≠ 0 := fun c => (data.monic.map _).ne_zero
  have hb_coe : ((jGeomGen k (M * s) : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = jqModC k := rfl
  have ha_coe : ((φ₁ (jGeomGen k M) : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = jqNModC k s := by
    rw [hφβ]; rfl
  have ha0 : φ₁ (jGeomGen k M) ≠ 0 := by
    intro h0
    have h1 : ((φ₁ (jGeomGen k M) : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = 0 := by rw [h0]; rfl
    rw [ha_coe] at h1
    exact transcendental_jqNModC k s (h1 ▸ isAlgebraic_zero)
  constructor
  · rintro ⟨hprat, hpaff, hpj⟩
    refine ⟨DegPair.isRational k M _, (DegPair.isAffine_beta_iff M s hs φ₁ hφ₁ hφβ p).2 hpaff, ?_⟩
    have hroot := DegPair.isRoot_fibrePoly_beta M s φ₁ hφ₁ hφβ p hpaff data
    exact ModularCurve.mem_ssJSet_of_mem_roots_fibrePoly q' (ℓ := s) hsq' data hpj
      ((Polynomial.mem_roots (hmon _)).2 hroot)
  · rintro ⟨hvrat, hvaff, hvj⟩
    have hprat : p.IsRational := DegPair.isRational k (M * s) p
    have hpaff : IsAffineGeomPlace k (M * s) p := (DegPair.isAffine_beta_iff M s hs φ₁ hφ₁ hφβ p).1 hvaff
    refine ⟨hprat, hpaff, ?_⟩
    have he := FltWs24.DegPair.rIA_pos φ₁ hφ₁ p
    have ha : φ₁ (jGeomGen k M) ∈ p.toValuationSubring :=
      (FltWs24.DegPair.mem_iff_mem_restrictAlong φ₁ hφ₁ p _ (fun h0 => ha0 (by rw [h0, map_zero])) he).2 hvaff.1
    have hroot := FltWs24.DegPair.isRoot_fibrePoly_evalAt (modularFunctionFieldC k (M * s)) data.Φ (φ₁ (jGeomGen k M))
      (jGeomGen k (M * s))
      (by rw [ha_coe, hb_coe]; exact CuspsLegsE4.eval₂_aeval_jqNModC_jqModC_eq_zero k s data hsym) p hprat ha hpaff.1
    rw [FltWs24.DegPair.evalAt_along M φ₁ hφ₁ p (jGeomGen k M) he] at hroot
    exact ModularCurve.mem_ssJSet_of_mem_roots_fibrePoly q' (ℓ := s) hsq' data hvj
      ((Polynomial.mem_roots (hmon _)).2 hroot)

end

theorem ss_iff_gen (K : Type*) [Field K] (N ℓ : ℕ) [NeZero N] [NeZero ℓ]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsAlgClosed K] [DecidableEq K] (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (S : IntermediateField K (LaurentSeries K))
    (hS : S = (haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩; modularFunctionFieldC K (N * ℓ)))
    (ψα ψβ : ↥(modularFunctionFieldC K N) →ₐ[K] ↥S)
    (hψα : ∀ x, ((ψα x : ↥S) : LaurentSeries K) = x) (hψβ : ∀ x, ((ψβ x : ↥S) : LaurentSeries K) = qExpand K ℓ x)
    (hα : ψα.toRingHom.IsIntegral) (hβ : ψβ.toRingHom.IsIntegral)
    (y : Place K ↥S) :
    (y.restrictAlong ψα hα ∈ ssPlaces p N K ↔ y.restrictAlong ψβ hβ ∈ ssPlaces p N K) := by
  subst hS
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩
  rw [← DegPair.ssPlaces_alpha p N ℓ ψα hα hψα y, ssPlaces_beta N ℓ p hℓ hℓp ψβ hβ hψβ y]

theorem roof_eq (K : Type*) [Field K] (N ℓ : ℕ) [NeZero N] [NeZero ℓ] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hpNl : ¬ p ∣ N * ℓ) :
    charLDegeneracyRoof K N ℓ = (haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩; modularFunctionFieldC K (N * ℓ)) := by
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩
  rw [charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul K p N ℓ hpNl,
    ← modularFunctionFieldC_eq_modularFunctionFieldFullC K p (N * ℓ) hpNl]

theorem main (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hN : (N : K) ≠ 0) (hℓp : ℓ ≠ p)
    (hα : (heckeAlphaC K N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC K N ℓ).toRingHom.IsIntegral)
    (y : Place K ↥(charLDegeneracyRoof K N ℓ)) :
    y.restrictAlong (heckeAlphaC K N ℓ) hα ∈ ssPlaces p N K ↔ y.restrictAlong (heckeBetaC K N ℓ) hβ ∈ ssPlaces p N K := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hℓK : (ℓ : K) ≠ 0 := by
    intro h; have := (CharP.cast_eq_zero_iff K p ℓ).1 h
    exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out) (Fact.out)).1 this).symm
  have hpNl : ¬ p ∣ N * ℓ := by
    intro h; have : ((N * ℓ : ℕ) : K) = 0 := (CharP.cast_eq_zero_iff K p _).2 h
    push_cast at this; exact mul_ne_zero hN hℓK this
  exact ss_iff_gen K N ℓ p Fact.out hℓp _ (roof_eq K N ℓ p hpNl)
    (heckeAlphaC K N ℓ) (heckeBetaC K N ℓ) (coe_heckeAlphaC K N ℓ) (coe_heckeBetaC K N ℓ) hα hβ y

end Ws47.FaceS

theorem solution
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hN : (N : K) ≠ 0) (hℓN : ℓ ∣ N) (hℓp : ℓ ≠ p)
    (hα : (heckeAlphaC K N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC K N ℓ).toRingHom.IsIntegral)
    (y : Place K ↥(charLDegeneracyRoof K N ℓ)) :
    y.restrictAlong (heckeAlphaC K N ℓ) hα ∈ ssPlaces p N K ↔ y.restrictAlong (heckeBetaC K N ℓ) hβ ∈ ssPlaces p N K :=
  Ws47.FaceS.main p K N ℓ hN hℓp hα hβ y

end S_ModularCurve_restrictAlong_heckeAlphaC_mem_ssPlaces_iff_restrictAlong_heckeBetaC_mem_ssPlaces_of_dvd
end P2MW
export P2MW.S_ModularCurve_restrictAlong_heckeAlphaC_mem_ssPlaces_iff_restrictAlong_heckeBetaC_mem_ssPlaces_of_dvd (solution)
