-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_gluedMk_eq_nodeUnit_of_isGoodDiv_of_admissible_of_pic0Mk_eq_smul_single_sub_self_of_isModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/33791f0a-bd01-55b4-9705-23c3180e17d1

import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_PlaceWidth
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_heckeAlphaBar
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_heckeBetaBar
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_ProlongationTuple_JumpLaw
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
import Theorems.Thm_ModularCurve_isAffineGeomPlace_frobOnPlacesGeomLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_gluedMk_eq_nodeUnit_of_isGoodDiv_of_admissible_of_pic0Mk_eq_smul_single_sub_self_of_isModel
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_gluedMk_eq_nodeUnit_of_isGoodDiv_of_admissible_of_pic0Mk_eq_smul_single_sub_self_of_isModel.AlgebraicCurve IsLocalRing ModularCurve"

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "Place Place.ext Divisor Divisor.degree Divisor.degree_single Divisor.degZero Divisor.mem_degZero Divisor.principal HasPrincipalDivisors Pic0 Pic0.mk HasPrincipalDivisors.exists_divisor RegularProlongation ConstantReduction ConstantReduction.ord_algebraMap Place.exists_isUnit_of_ord_eq_zero Place.exists_hasValue_of_surjective GluingData GluingData.admissible GluingData.zero_zero_mem_admissible GluingData.IsGluedPrincipal GluedPic0 GluedPic0.mk GluedPic0.mk_eq_zero_iff GluedPic0.nodeUnit GluedPic0.nodeUnit_apply SemilinearAut SemilinearAut.smul_toValuationSubring SemilinearAut.smul_single IsCurveOver IsCurveOver.hasPrincipalDivisors Place.deg_eq_one_iff_surjective_algebraMap_residueField" namespace GluedPic0 p2m_export "AlgebraicCurve.GluedPic0" "mk mk_eq_zero_iff nodeUnit nodeUnit_apply" end AlgebraicCurve.GluedPic0
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.GluedPic0" in
private theorem AlgebraicCurve.GluedPic0.mk_eq_nodeUnit_iff {K F : Type*} [Field K] [Field F]
    [Algebra K F] (S : Finset (Place K F × Place K F)) (x : GluingData K F S)
    (hadm : x ∈ GluingData.admissible S) (χ : ↥S → Additive Kˣ) :
    GluedPic0.mk S ⟨x, hadm⟩ = GluedPic0.nodeUnit S χ
      ↔ GluingData.IsGluedPrincipal S (x - (0, 0, χ)) := by
  rw [GluedPic0.nodeUnit_apply, ← sub_eq_zero, show (GluedPic0.mk S ⟨x, hadm⟩
      - GluedPic0.mk S ⟨(0, 0, χ), GluingData.zero_zero_mem_admissible S χ⟩ : GluedPic0 K F S)
      = GluedPic0.mk S ((⟨x, hadm⟩ : ↥(GluingData.admissible S))
        - ⟨(0, 0, χ), GluingData.zero_zero_mem_admissible S χ⟩) from
    (map_sub (GluedPic0.mk S) _ _).symm, GluedPic0.mk_eq_zero_iff]
  rfl

section GenericK
variable {k : Type*} [Field k] [IsAlgClosed k] {N : ℕ} [NeZero N]
  (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)))
  {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private theorem H2Recon.b2_ii_exists_hasValue_nodePair
    (x : GluingData k (modularFunctionFieldC k N) S) (hadm : x ∈ GluingData.admissible S)
    (g₁ g₂ : ↥(modularFunctionFieldC k N)) (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    (hd₁ : ∀ v, x.1 v = v.ord g₁) (hd₂ : ∀ v, x.2.1 v = v.ord g₂)
    (s : ↥S) :
    ∃ (as bs : kˣ),
      (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1.HasValue g₁ as ∧
      (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).2.HasValue g₂ bs := by
  have ho₁ : (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1.ord g₁ = 0 :=
    (hd₁ _).symm.trans (hadm.2.2 s s.2).1
  have ho₂ : (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).2.ord g₂ = 0 :=
    (hd₂ _).symm.trans (hadm.2.2 s s.2).2

  obtain ⟨hm₁, hu₁⟩ := Place.exists_isUnit_of_ord_eq_zero
    (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 hg₁ ho₁
  obtain ⟨hm₂, hu₂⟩ := Place.exists_isUnit_of_ord_eq_zero
    (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).2 hg₂ ho₂
  obtain ⟨c₁, hc₁, hne₁⟩ := Place.exists_hasValue_of_surjective
    (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1
    ((Place.deg_eq_one_iff_surjective_algebraMap_residueField _).mp
      (place_deg_eq_one_of_isAlgClosed k N _)) hm₁
  obtain ⟨c₂, hc₂, hne₂⟩ := Place.exists_hasValue_of_surjective
    (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).2
    ((Place.deg_eq_one_iff_surjective_algebraMap_residueField _).mp
      (place_deg_eq_one_of_isAlgClosed k N _)) hm₂
  exact ⟨Units.mk0 c₁ (hne₁ hu₁), Units.mk0 c₂ (hne₂ hu₂), hc₁, hc₂⟩

end GenericK

namespace H2Recon
namespace AlphaTS

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_gluedMk_eq_nodeUnit_of_isGoodDiv_of_admissible_of_pic0Mk_eq_smul_single_sub_self_of_isModel.AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization"

section generic

variable {L : Type*} [Field L] {A : ValuationSubring L}
  {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

private theorem exists_smul_mem_and_mem_residue_ne_zero_or
    (R₁ R₂ : RegularProlongation A F Fbar) {f : F} (hf : f ≠ 0) :
    ∃ c : L, c ≠ 0 ∧ ∃ (h₁ : c • f ∈ R₁.integers) (h₂ : c • f ∈ R₂.integers),
      R₁.residue ⟨c • f, h₁⟩ ≠ 0 ∨ R₂.residue ⟨c • f, h₂⟩ ≠ 0 := by
  obtain ⟨c₁, h₁, hr₁⟩ := R₁.exists_smul_mem f hf
  obtain ⟨c₂, h₂, hr₂⟩ := R₂.exists_smul_mem f hf
  have hc₁ : c₁ ≠ 0 := R₁.smul_const_ne_zero h₁ hr₁
  have hc₂ : c₂ ≠ 0 := R₂.smul_const_ne_zero h₂ hr₂
  rcases A.mem_or_inv_mem (c₁ / c₂) with h | h
  ·
    have e : c₁ • f = algebraMap L F (c₁ / c₂) * (c₂ • f) := by
      rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul]
      congr 2
      field_simp
    have h₁₂ : c₁ • f ∈ R₂.integers := by
      rw [e]
      exact mul_mem ((R₂.algebraMap_mem_iff _).mpr h) h₂
    exact ⟨c₁, hc₁, h₁, h₁₂, Or.inl hr₁⟩
  ·
    rw [inv_div] at h
    have e : c₂ • f = algebraMap L F (c₂ / c₁) * (c₁ • f) := by
      rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul]
      congr 2
      field_simp
    have h₂₁ : c₂ • f ∈ R₁.integers := by
      rw [e]
      exact mul_mem ((R₁.algebraMap_mem_iff _).mpr h) h₁
    exact ⟨c₂, hc₂, h₂₁, h₂, Or.inr hr₂⟩

end generic

section tuple

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

private theorem alphaPort_twoSided (R : ProlongationTuple P)
    (f : modularFunctionFieldBar (N * q)) (hf : f ≠ 0) :
    ∃ U : modularFunctionFieldBar (N * q), U ≠ 0 ∧
      ∃ (h₁ : U * f ∈ R.R₁.integers) (h₂ : U * f ∈ R.R₂.integers),
        (R.R₁.residue ⟨U * f, h₁⟩ ≠ 0 ∨ R.R₂.residue ⟨U * f, h₂⟩ ≠ 0) ∧
        ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V.ord U = 0 := by
  obtain ⟨c, hc, h₁, h₂, hor⟩ := exists_smul_mem_and_mem_residue_ne_zero_or R.R₁ R.R₂ hf
  have e : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) c * f = c • f :=
    (Algebra.smul_def c f).symm
  have h₁' : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) c * f ∈ R.R₁.integers := by
    rw [e]; exact h₁
  have h₂' : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) c * f ∈ R.R₂.integers := by
    rw [e]; exact h₂
  refine ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) c,
    (map_ne_zero _).mpr hc, h₁', h₂', ?_, fun V => ConstantReduction.ord_algebraMap V hc⟩
  have e₁ : (⟨_, h₁'⟩ : R.R₁.integers) = ⟨c • f, h₁⟩ := Subtype.ext e
  have e₂ : (⟨_, h₂'⟩ : R.R₂.integers) = ⟨c • f, h₂⟩ := Subtype.ext e
  rw [e₁, e₂]
  exact hor

end tuple

end H2Recon.AlphaTS

namespace H2Recon
namespace GaussJump

open ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

open Classical in

private theorem residues_both_of_jumpLaw (R : ProlongationTuple P) (hJ : _root_.GaussJump.JumpLaw R)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    {f : ↥(modularFunctionFieldBar (N * q))} (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hor : R.R₁.residue ⟨f, h₁⟩ ≠ 0 ∨ R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    {D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hstrict : ∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V)
    (hdiv : ∀ V, D V + (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E) V = V.ord f)
    (hdeg₁ : Divisor.degree (D.filter P.IsStrictFst) = 0)
    (hdeg₂ : Divisor.degree (D.filter P.IsStrictSnd) = 0) :
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨f, h₂⟩ ≠ 0 := by
  obtain ⟨hJ1, hJ2⟩ := hJ σ hσ f h₁ h₂ D E hstrict hdiv
  rcases hor with hr₁ | hr₂
  · refine ⟨hr₁, fun hz => ?_⟩
    have hlt := hJ1 hr₁ hz
    rw [hdeg₂] at hlt
    exact lt_irrefl _ hlt
  · refine ⟨fun hz => ?_, hr₂⟩
    have hlt := hJ2 hr₂ hz
    rw [hdeg₁] at hlt
    exact lt_irrefl _ hlt

open Classical in

private theorem residues_both_of_jumpLaw' (R : ProlongationTuple P) (hJ : _root_.GaussJump.JumpLaw R)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    {f : ↥(modularFunctionFieldBar (N * q))} (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hor : R.R₁.residue ⟨f, h₁⟩ ≠ 0 ∨ R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    {D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hstrict : ∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V)
    (hdiv : ∀ V, D V + (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E) V = V.ord f)
    (hdeg₁ : Divisor.degree (D.filter P.IsStrictFst) = 0)
    (hdeg₂ : Divisor.degree (D.filter P.IsStrictSnd) = 0) :
    R.residue₁ ⟨f, h₁⟩ ≠ 0 ∧ R.residue₂ ⟨f, h₂⟩ ≠ 0 := by
  obtain ⟨hr₁, hr₂⟩ := residues_both_of_jumpLaw R hJ hσ h₁ h₂ hor hstrict hdiv hdeg₁ hdeg₂
  refine ⟨?_, ?_⟩
  · rw [ProlongationTuple.residue₁_apply]
    exact (map_ne_zero_iff R.ι R.ι.injective).mpr hr₁
  · rw [ProlongationTuple.residue₂_apply]
    exact (map_ne_zero_iff R.ι R.ι.injective).mpr hr₂

end H2Recon.GaussJump

open ModularCurve.PlaceSpecialization in
private theorem H2Recon.degree_mapDomain_of_deg_eq {K F K' F' : Type*} [Field K] [Field F] [Algebra K F]
    [Field K'] [Field F'] [Algebra K' F'] (r : Place K F → Place K' F') (hdeg : ∀ v, (r v).deg = v.deg)
    (D : Divisor K F) : Divisor.degree (Finsupp.mapDomain r D) = Divisor.degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
    rw [Finsupp.mapDomain_add, map_add, map_add, ih, Finsupp.mapDomain_single, Divisor.degree_single,
      Divisor.degree_single, hdeg]

open ModularCurve.PlaceSpecialization in
open Classical in
private theorem H2Recon.stepI_residues_both
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} [CharP (ResidueField A) q]
    {P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ}
    (R : PlaceSpecialization.ProlongationTuple P) (hjump : GaussJump.JumpLaw R)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hgood : P.IsGoodDiv D)
    {h : ↥(modularFunctionFieldBar (N * q))} (h₁ : h ∈ R.R₁.integers) (h₂ : h ∈ R.R₂.integers)
    (hor : R.R₁.residue ⟨h, h₁⟩ ≠ 0 ∨ R.R₂.residue ⟨h, h₂⟩ ≠ 0)
    (hdiv : ∀ V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      V'.ord h = ((D - (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
        - Finsupp.single V 1) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) V'))
    (hdeg₁ : Divisor.degree (D.filter P.IsStrictFst) = 0)
    (hdeg₂ : Divisor.degree (D.filter P.IsStrictSnd) = 0) :
    R.residue₁ ⟨h, h₁⟩ ≠ 0 ∧ R.residue₂ ⟨h, h₂⟩ ≠ 0 := by
  have hE : D + (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (-(Finsupp.single V (1 : ℤ)))
      - -(Finsupp.single V (1 : ℤ)))
      = D - (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
        - Finsupp.single V 1) := by
    rw [smul_neg]; abel
  refine H2Recon.GaussJump.residues_both_of_jumpLaw' R hjump hσ h₁ h₂ hor
    (E := -(Finsupp.single V (1 : ℤ))) hgood ?_ hdeg₁ hdeg₂
  intro V'
  rw [← Finsupp.add_apply, hE]
  exact (hdiv V').symm

open ModularCurve.PlaceSpecialization in
set_option maxHeartbeats 1600000 in
private theorem H2Recon.stepI_exists_commonGaussUnit_of_pic0Mk_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [CharP (ResidueField A) q] [DecidableEq (ResidueField A)] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hdeg : arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
        - Finsupp.single V 1
        ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
        (F := ↥(modularFunctionFieldBar (N * q)))))
    (hcls : Pic0.mk D = Pic0.mk ⟨_, hdeg⟩)
    (hgood : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
    (hjump : GaussJump.JumpLaw R)
    (hadm : (P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
        _ × _ × (↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
          → Additive (ResidueField A)ˣ)) ∈
      GluingData.admissible (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)) :
    ∃ (h : ↥(modularFunctionFieldBar (N * q))) (h₁ : h ∈ R.R₁.integers) (h₂ : h ∈ R.R₂.integers),
      R.residue₁ ⟨h, h₁⟩ ≠ 0 ∧ R.residue₂ ⟨h, h₂⟩ ≠ 0 ∧
        ∀ V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
          V'.ord h = (((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
            - (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
            - Finsupp.single V 1) :
              Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) V' := by
  have hker : (D - ⟨_, hdeg⟩ : Divisor.degZero (K := AlgebraicClosure ℚ)
        (F := ↥(modularFunctionFieldBar (N * q))))
      ∈ (Divisor.principal (K := AlgebraicClosure ℚ)
          (F := ↥(modularFunctionFieldBar (N * q)))).addSubgroupOf
        (Divisor.degZero (K := AlgebraicClosure ℚ)
            (F := ↥(modularFunctionFieldBar (N * q)))) := by
    have h0 := (QuotientAddGroup.eq (a := D)
      (b := (⟨_, hdeg⟩ : Divisor.degZero (K := AlgebraicClosure ℚ)
        (F := ↥(modularFunctionFieldBar (N * q)))))).mp hcls
    have : -(-D + (⟨_, hdeg⟩ : Divisor.degZero (K := AlgebraicClosure ℚ)
        (F := ↥(modularFunctionFieldBar (N * q))))) ∈ _ := neg_mem h0
    rwa [neg_add_rev, neg_neg, ← sub_eq_neg_add] at this
  obtain ⟨h₀, hh₀, hdivh₀⟩ := hker
  obtain ⟨U, hU, h₁', h₂', hor, hordU⟩ := H2Recon.AlphaTS.alphaPort_twoSided R h₀ hh₀
  have hdivW : ∀ V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      V'.ord (U * h₀) = (((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
        - (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
        - Finsupp.single V 1) :
          Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) V' := by
    intro V'
    rw [V'.ord_mul hU hh₀, hordU V', zero_add, ← hdivh₀ V']; rfl

  have hdegmap₁ : ∀ V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (P.reduceFst V').deg = V'.deg := fun V' => by
    rw [place_deg_eq_one_of_isAlgClosed (ResidueField A) N (P.reduceFst V'),
      deg_eq_one_modularFunctionFieldBar (N * q) V']
  have hdegmap₂ : ∀ V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (P.reduceSnd V').deg = V'.deg := fun V' => by
    rw [place_deg_eq_one_of_isAlgClosed (ResidueField A) N (P.reduceSnd V'),
      deg_eq_one_modularFunctionFieldBar (N * q) V']
  obtain ⟨hadm₁, hadm₂, -⟩ := hadm
  have hdeg₁ : Divisor.degree (P.fstDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) = 0 := by
    have h0 := Divisor.mem_degZero.mp hadm₁
    change Divisor.degree (Finsupp.mapDomain P.reduceFst
      (P.fstDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))) = 0 at h0
    rwa [H2Recon.degree_mapDomain_of_deg_eq P.reduceFst hdegmap₁] at h0
  have hdeg₂ : Divisor.degree (P.sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) = 0 := by
    have h0 := Divisor.mem_degZero.mp hadm₂
    change Divisor.degree (Finsupp.mapDomain P.reduceSnd
      (P.sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))) = 0 at h0
    rwa [H2Recon.degree_mapDomain_of_deg_eq P.reduceSnd hdegmap₂] at h0
  obtain ⟨hr₁, hr₂⟩ := H2Recon.stepI_residues_both R hjump hσ V hgood h₁' h₂' hor hdivW hdeg₁ hdeg₂
  exact ⟨U * h₀, h₁', h₂', hr₁, hr₂, hdivW⟩

namespace H2Recon
namespace B2hdiv

open ModularCurve.PlaceSpecialization
open scoped Pointwise

private theorem semilinearAut_smul_restrictAlong
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (s : SemilinearAut K F') (t : SemilinearAut K F)
    (h : ∀ x : F, φ (t • x) = s • φ x) (W : Place K F') :
    (s • W).restrictAlong φ hφ = t • W.restrictAlong φ hφ := by
  apply Place.ext
  rw [SemilinearAut.smul_toValuationSubring]
  ext x
  rw [show ((s • W).restrictAlong φ hφ).toValuationSubring
        = (s • W).toValuationSubring.comap φ.toRingHom from rfl,
    show (W.restrictAlong φ hφ).toValuationSubring
        = W.toValuationSubring.comap φ.toRingHom from rfl,
    ValuationSubring.mem_comap, SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_comap]
  have key : φ (t⁻¹ • x) = s⁻¹ • φ x := by
    have e := h (t⁻¹ • x)
    rw [smul_inv_smul] at e
    rw [e, inv_smul_smul]
  change s⁻¹ • φ x ∈ W.toValuationSubring ↔ φ (t⁻¹ • x) ∈ W.toValuationSubring
  rw [key]

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  [CharP (ResidueField A) q]
  {P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ}

private theorem reduceFst_reduceSnd_inertiaSmul
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.reduceFst (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • W) = P.reduceFst W ∧
      P.reduceSnd (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • W)
        = P.reduceSnd W := by
  constructor
  · show P.sp ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ • W).restrictAlong
        (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
      = P.sp (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
    rw [semilinearAut_smul_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
      (arithmeticGalois (modularFunctionFieldFull (N * q)) σ)
      (arithmeticGalois (modularFunctionFieldFull N) σ)
      (fun x => (arithmeticGalois_smul_heckeAlphaBar N q σ x).symm) W]
    exact P.d6_inertia σ hσ _
  · show P.sp ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ • W).restrictAlong
        (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)
      = P.sp (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)
    rw [semilinearAut_smul_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ
      (arithmeticGalois (modularFunctionFieldFull (N * q)) σ)
      (arithmeticGalois (modularFunctionFieldFull N) σ)
      (fun x => (arithmeticGalois_smul_heckeBetaBar N q σ x).symm) W]
    exact P.d6_inertia σ hσ _

private theorem isStrict_inertiaSmul_iff
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    (P.IsStrictFst (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • W)
        ↔ P.IsStrictFst W) ∧
      (P.IsStrictSnd (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • W)
        ↔ P.IsStrictSnd W) := by
  have h := reduceFst_reduceSnd_inertiaSmul (P := P) σ hσ W
  constructor
  · unfold PlaceSpecialization.IsStrictFst; rw [h.1, h.2]
  · unfold PlaceSpecialization.IsStrictSnd; rw [h.1, h.2]

open Classical in
private theorem deltaV_strictFilter_pushforward_zero
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hf : ¬ P.IsStrictFst V) (hs : ¬ P.IsStrictSnd V) :
    let δV := arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
        - Finsupp.single V 1
    Finsupp.mapDomain P.reduceFst (Finsupp.filter P.IsStrictFst δV) = 0 ∧
    Finsupp.mapDomain P.reduceSnd (Finsupp.filter P.IsStrictSnd δV) = 0 := by
  have hiff := isStrict_inertiaSmul_iff (P := P) σ hσ V
  have hσf : ¬ P.IsStrictFst (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) :=
    fun h => hf (hiff.1.mp h)
  have hσs : ¬ P.IsStrictSnd (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) :=
    fun h => hs (hiff.2.mp h)
  have hδV_eq : arithmeticGalois (modularFunctionFieldFull (N * q)) σ
      • (Finsupp.single V (1 : ℤ))
      = Finsupp.single (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) (1 : ℤ) :=
    SemilinearAut.smul_single _ V 1
  refine ⟨?_, ?_⟩ <;>
    (simp only [hδV_eq, Finsupp.filter_sub, Finsupp.mapDomain_sub]
     rw [Finsupp.filter_single_of_neg, Finsupp.filter_single_of_neg]
     · simp
     · assumption
     · assumption)

end H2Recon.B2hdiv

private theorem H2Recon.C2.mapDomain_apply_eq_zero_of_forall {α β : Type*}
    (g : α →₀ ℤ) (f : α → β) (v : β) (h : ∀ a, f a = v → g a = 0) :
    Finsupp.mapDomain f g v = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Finsupp.single_apply]
  split_ifs with hfa
  · exact h a hfa
  · rfl

private theorem H2Recon.C2.divisor_eq_of_forall_ne_of_degree_eq_zero {K F : Type*} [Field K] [Field F]
    [Algebra K F] (Δ G : Divisor K F) (s : Place K F) (hs : s.deg = 1)
    (h : ∀ v, v ≠ s → Δ v = G v) (hΔ : Divisor.degree Δ = 0) (hG : Divisor.degree G = 0) : Δ = G := by
  classical
  have hsub : Δ - G = Finsupp.single s ((Δ - G) s) := by
    ext v
    rw [Finsupp.single_apply]
    split_ifs with hv
    · rw [hv]
    · rw [Finsupp.sub_apply, h v (Ne.symm hv), sub_self]
  have hdeg : Divisor.degree (Δ - G) = 0 := by rw [map_sub, hΔ, hG, sub_self]
  rw [hsub, Divisor.degree_single, hs, Nat.cast_one, mul_one] at hdeg
  have h0 : Δ - G = 0 := by rw [hsub, hdeg, Finsupp.single_zero]
  exact sub_eq_zero.mp h0

open ModularCurve.PlaceSpecialization in

private theorem H2Recon.C2.good_apply_eq_zero_of_fixed_fst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [CharP (ResidueField A) q] [DecidableEq (ResidueField A)]
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hgood : P.IsGoodDiv D) (V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hfix : frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V')) = P.reduceFst V') : D V' = 0 := by
  by_contra hne
  rcases hgood V' (Finsupp.mem_support_iff.mpr hne) with hst | hst
  · exact hst.2 hfix
  · rw [hst.1] at hfix
    exact hst.2 (frobOnPlacesGeomLevel_injective (ResidueField A) N data hKr hfix)

open ModularCurve.PlaceSpecialization in

private theorem H2Recon.C2.good_apply_eq_zero_of_fixed_snd
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [CharP (ResidueField A) q] [DecidableEq (ResidueField A)]
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hgood : P.IsGoodDiv D) (V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hfix : frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceSnd V')) = P.reduceSnd V') : D V' = 0 := by
  by_contra hne
  rcases hgood V' (Finsupp.mem_support_iff.mpr hne) with hst | hst
  · rw [← hst.1] at hfix
    exact hst.2 (frobOnPlacesGeomLevel_injective (ResidueField A) N data hKr hfix)
  · exact hst.2 hfix

open ModularCurve.PlaceSpecialization in

private theorem H2Recon.C2.delta_apply_eq_zero_of_reduceFst_ne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [CharP (ResidueField A) q] [DecidableEq (ResidueField A)]
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hne : P.reduceFst V' ≠ P.reduceFst V) :
    (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ)) - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) V' = 0 := by
  classical
  have hred := H2Recon.B2hdiv.reduceFst_reduceSnd_inertiaSmul (P := P) σ hσ V
  rw [SemilinearAut.smul_single, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply]
  have h1 : arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V ≠ V' := fun h => hne (by rw [← h, hred.1])
  have h2 : V ≠ V' := fun h => hne (by rw [h])
  rw [if_neg h1, if_neg h2, sub_self]

open ModularCurve.PlaceSpecialization in

private theorem H2Recon.C2.delta_apply_eq_zero_of_reduceSnd_ne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [CharP (ResidueField A) q] [DecidableEq (ResidueField A)]
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hne : P.reduceSnd V' ≠ P.reduceSnd V) :
    (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ)) - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) V' = 0 := by
  classical
  have hred := H2Recon.B2hdiv.reduceFst_reduceSnd_inertiaSmul (P := P) σ hσ V
  rw [SemilinearAut.smul_single, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply]
  have h1 : arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V ≠ V' := fun h => hne (by rw [← h, hred.2])
  have h2 : V ≠ V' := fun h => hne (by rw [h])
  rw [if_neg h1, if_neg h2, sub_self]

open ModularCurve.PlaceSpecialization in

private theorem H2Recon.C2.reduceSnd_eq_frob_reduceFst_of_not_strict
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [CharP (ResidueField A) q] [DecidableEq (ResidueField A)]
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hs : ¬ P.IsStrictSnd V) :
    P.reduceSnd V = frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V) := by
  have hd : P.reduceFst V = frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceSnd V) ∨
      frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V) = P.reduceSnd V := P.d1 V
  rcases hd with h | h
  · have hfix : frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceSnd V)) = P.reduceSnd V := by
      by_contra hne
      exact hs ⟨h, hne⟩
    calc P.reduceSnd V = frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceSnd V)) := hfix.symm
      _ = frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V) := by rw [← h]
  · exact h.symm

open ModularCurve.PlaceSpecialization in

private theorem H2Recon.C2.sub_delta_apply_eq_zero_of_fixed_fst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [CharP (ResidueField A) q] [DecidableEq (ResidueField A)]
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hgood : P.IsGoodDiv D) (V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hfix : frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V')) = P.reduceFst V') (hne : P.reduceFst V' ≠ P.reduceFst V) :
    ((D - (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
          - Finsupp.single V 1) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) V' = 0 := by
  rw [Finsupp.sub_apply, H2Recon.C2.good_apply_eq_zero_of_fixed_fst P D hgood V' hfix,
    H2Recon.C2.delta_apply_eq_zero_of_reduceFst_ne P σ hσ V V' hne, sub_self]

open ModularCurve.PlaceSpecialization in

private theorem H2Recon.C2.sub_delta_apply_eq_zero_of_fixed_snd
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [CharP (ResidueField A) q] [DecidableEq (ResidueField A)]
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hgood : P.IsGoodDiv D) (V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hfix : frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceSnd V')) = P.reduceSnd V') (hne : P.reduceSnd V' ≠ P.reduceSnd V) :
    ((D - (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
          - Finsupp.single V 1) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) V' = 0 := by
  rw [Finsupp.sub_apply, H2Recon.C2.good_apply_eq_zero_of_fixed_snd P D hgood V' hfix,
    H2Recon.C2.delta_apply_eq_zero_of_reduceSnd_ne P σ hσ V V' hne, sub_self]

open ModularCurve.PlaceSpecialization in
open Classical in

private theorem H2Recon.C2.push_fst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [CharP (ResidueField A) q] [DecidableEq (ResidueField A)]
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hf : ¬ P.IsStrictFst V) (hs : ¬ P.IsStrictSnd V) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (S : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) × Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))) (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) :
    Finsupp.mapDomain P.reduceFst (Finsupp.filter P.IsStrictFst ((D - (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
          - Finsupp.single V 1) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))) w = (P.glueData S D).1 w := by
  obtain ⟨hδ₁, -⟩ := H2Recon.B2hdiv.deltaV_strictFilter_pushforward_zero (P := P) σ hσ V hf hs
  show _ = Finsupp.mapDomain P.reduceFst (Finsupp.filter P.IsStrictFst D) w
  rw [Finsupp.filter_sub, Finsupp.mapDomain_sub, hδ₁, sub_zero]

open ModularCurve.PlaceSpecialization in
open Classical in

private theorem H2Recon.C2.push_snd
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [CharP (ResidueField A) q] [DecidableEq (ResidueField A)]
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hf : ¬ P.IsStrictFst V) (hs : ¬ P.IsStrictSnd V) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (S : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) × Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))) (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) :
    Finsupp.mapDomain P.reduceSnd (Finsupp.filter P.IsStrictSnd ((D - (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
          - Finsupp.single V 1) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))) w = (P.glueData S D).2.1 w := by
  obtain ⟨-, hδ₂⟩ := H2Recon.B2hdiv.deltaV_strictFilter_pushforward_zero (P := P) σ hσ V hf hs
  show _ = Finsupp.mapDomain P.reduceSnd (Finsupp.filter P.IsStrictSnd D) w
  rw [Finsupp.filter_sub, Finsupp.mapDomain_sub, hδ₂, sub_zero]

open ModularCurve.PlaceSpecialization in
open Classical in

private theorem H2Recon.C2.glueData_fst_apply_eq_zero_of_fixed
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [CharP (ResidueField A) q] [DecidableEq (ResidueField A)]
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (S : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) × Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
    (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) (hw : frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr w) = w) : (P.glueData S D).1 w = 0 := by
  show Finsupp.mapDomain P.reduceFst (Finsupp.filter P.IsStrictFst D) w = 0
  refine H2Recon.C2.mapDomain_apply_eq_zero_of_forall _ _ _ fun V' hV' => ?_
  rw [Finsupp.filter_apply]
  split_ifs with hst
  · exact absurd (by rw [hV']; exact hw) hst.2
  · rfl

open ModularCurve.PlaceSpecialization in
open Classical in

private theorem H2Recon.C2.glueData_snd_apply_eq_zero_of_fixed
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [CharP (ResidueField A) q] [DecidableEq (ResidueField A)]
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (S : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) × Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
    (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) (hw : frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr w) = w) : (P.glueData S D).2.1 w = 0 := by
  show Finsupp.mapDomain P.reduceSnd (Finsupp.filter P.IsStrictSnd D) w = 0
  refine H2Recon.C2.mapDomain_apply_eq_zero_of_forall _ _ _ fun V' hV' => ?_
  rw [Finsupp.filter_apply]
  split_ifs with hst
  · exact absurd (by rw [hV']; exact hw) hst.2
  · rfl

open ModularCurve.PlaceSpecialization in
open Classical in

private theorem H2Recon.C2.legA
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [CharP (ResidueField A) q] [DecidableEq (ResidueField A)]
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
    (hqN : ¬ q ∣ N) (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel) (hreg : R.RegularityLaw W)
    (hO : R.OrderLawFixed)
    (u : ↥(modularFunctionFieldBar (N * q))) (hu₁ : u ∈ R.R₁.integers) (hu₂ : u ∈ R.R₂.integers)
    (hur₁ : R.residue₁ ⟨u, hu₁⟩ ≠ 0) (hur₂ : R.residue₂ ⟨u, hu₂⟩ ≠ 0)
    (hr₁ : R.R₁.residue ⟨u, hu₁⟩ ≠ 0) (hr₂ : R.R₂.residue ⟨u, hu₂⟩ ≠ 0)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hE : ∀ V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), E V' = V'.ord u)
    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) (G : Divisor (ResidueField A) (modularFunctionFieldC (ResidueField A) N))
    (hGfix : ∀ w' : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N), frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr w') = w' → G w' = 0)
    (hEfix : ∀ V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V')) = P.reduceFst V' → P.reduceFst V' ≠ s → E V' = 0)
    (hpush : ∀ w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N), Finsupp.mapDomain P.reduceFst (Finsupp.filter P.IsStrictFst E) w = G w)
    (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) (hw : w ≠ s) : w.ord (R.residue₁ ⟨u, hu₁⟩) = G w := by
  by_cases hwfix : frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr w) = w
  · rw [hGfix w hwfix]
    have hEw : ∀ V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), P.reduceFst V' = w → E V' = 0 := fun V' hV' =>
      hEfix V' (by rw [hV']; exact hwfix) (by rw [hV']; exact hw)
    by_cases haff : IsAffineGeomPlace (ResidueField A) N w
    · have hsum := hO u hu₁ hu₂ hr₁ hr₂ E hE w hwfix haff
      have hzero := H2Recon.C2.mapDomain_apply_eq_zero_of_forall E P.reduceFst w hEw
      rw [hzero] at hsum
      have hnn := hreg.1 u hu₁ hu₂ w hwfix haff (fun V' hV' => le_of_eq (by rw [← hE V', hEw V' hV']))
      have h1 := hnn.1 hur₁
      have h2 := hnn.2 hur₂
      omega
    · obtain ⟨⟨C, hC, hCw⟩, -⟩ :=
        exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace hqN P w haff
      have hcusp := hmodel.2.2.1 u hu₁ hu₂ hr₁ hr₂ E hE C hC
      rw [hCw] at hcusp
      rw [← hcusp]
      refine H2Recon.C2.mapDomain_apply_eq_zero_of_forall _ _ _ fun V' hV' => ?_
      rw [Finsupp.filter_apply]
      split_ifs
      · exact hEw V' hV'
      · rfl
  · rw [← hmodel.1 u hu₁ hu₂ hr₁ hr₂ E hE w hwfix]
    exact hpush w

open ModularCurve.PlaceSpecialization in
open Classical in

private theorem H2Recon.C2.legB
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [CharP (ResidueField A) q] [DecidableEq (ResidueField A)]
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
    (hqN : ¬ q ∣ N) (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel) (hreg : R.RegularityLaw W)
    (hO : R.OrderLawFixed)
    (u : ↥(modularFunctionFieldBar (N * q))) (hu₁ : u ∈ R.R₁.integers) (hu₂ : u ∈ R.R₂.integers)
    (hur₁ : R.residue₁ ⟨u, hu₁⟩ ≠ 0) (hur₂ : R.residue₂ ⟨u, hu₂⟩ ≠ 0)
    (hr₁ : R.R₁.residue ⟨u, hu₁⟩ ≠ 0) (hr₂ : R.R₂.residue ⟨u, hu₂⟩ ≠ 0)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hE : ∀ V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), E V' = V'.ord u)
    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) (G : Divisor (ResidueField A) (modularFunctionFieldC (ResidueField A) N))
    (hGfix : ∀ w' : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N), frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr w') = w' → G w' = 0)
    (hEfix₁ : ∀ V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V')) = P.reduceFst V' → P.reduceFst V' ≠ s → E V' = 0)
    (hEfix₂ : ∀ V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceSnd V')) = P.reduceSnd V' → P.reduceSnd V' ≠ frobOnPlacesGeomLevel (ResidueField A) N data hKr s → E V' = 0)
    (hpush : ∀ w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N), Finsupp.mapDomain P.reduceSnd (Finsupp.filter P.IsStrictSnd E) w = G w)
    (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) (hw : w ≠ frobOnPlacesGeomLevel (ResidueField A) N data hKr s) : w.ord (R.residue₂ ⟨u, hu₂⟩) = G w := by
  by_cases hwfix : frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr w) = w
  · rw [hGfix w hwfix]
    by_cases haff : IsAffineGeomPlace (ResidueField A) N w
    ·
      have hvfix : frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr w)) = frobOnPlacesGeomLevel (ResidueField A) N data hKr w :=
        congrArg (frobOnPlacesGeomLevel (ResidueField A) N data hKr) hwfix
      have hvaff : IsAffineGeomPlace (ResidueField A) N (frobOnPlacesGeomLevel (ResidueField A) N data hKr w) :=
        isAffineGeomPlace_frobOnPlacesGeomLevel (ResidueField A) N data hKr w haff
      have hvne : frobOnPlacesGeomLevel (ResidueField A) N data hKr w ≠ s := by
        intro h
        apply hw
        rw [← h, hwfix]
      have hEv : ∀ V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), P.reduceFst V' = frobOnPlacesGeomLevel (ResidueField A) N data hKr w → E V' = 0 := fun V' hV' =>
        hEfix₁ V' (by rw [hV']; exact hvfix) (by rw [hV']; exact hvne)
      have hsum := hO u hu₁ hu₂ hr₁ hr₂ E hE (frobOnPlacesGeomLevel (ResidueField A) N data hKr w) hvfix hvaff
      have hzero := H2Recon.C2.mapDomain_apply_eq_zero_of_forall E P.reduceFst (frobOnPlacesGeomLevel (ResidueField A) N data hKr w) hEv
      rw [hzero, hwfix] at hsum
      have hnn := hreg.1 u hu₁ hu₂ (frobOnPlacesGeomLevel (ResidueField A) N data hKr w) hvfix hvaff
        (fun V' hV' => le_of_eq (by rw [← hE V', hEv V' hV']))
      have h1 := hnn.1 hur₁
      have h2 := hnn.2 hur₂
      rw [hwfix] at h2
      omega
    · obtain ⟨-, ⟨C, hC, hCw⟩⟩ :=
        exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace hqN P w haff
      have hcusp := hmodel.2.2.2 u hu₁ hu₂ hr₁ hr₂ E hE C hC
      rw [hCw] at hcusp
      rw [← hcusp]
      refine H2Recon.C2.mapDomain_apply_eq_zero_of_forall _ _ _ fun V' hV' => ?_
      rw [Finsupp.filter_apply]
      split_ifs
      · exact hEfix₂ V' (by rw [hV']; exact hwfix) (by rw [hV']; exact hw)
      · rfl
  · rw [← hmodel.2.1 u hu₁ hu₂ hr₁ hr₂ E hE w hwfix]
    exact hpush w

set_option maxHeartbeats 1600000 in
private theorem H2Recon.C2.exists_orderDivisor {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    (g : ↥(modularFunctionFieldC (ResidueField A) N)) (hg : g ≠ 0) :
    ∃ Δ : Divisor (ResidueField A) (modularFunctionFieldC (ResidueField A) N), (∀ v : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N), Δ v = v.ord g) ∧ Divisor.degree Δ = 0 := by
  haveI : IsCurveOver (ResidueField A) (modularFunctionFieldC (ResidueField A) N) :=
    isCurveOver_modularFunctionFieldC_of_perfectField (ResidueField A) N
  haveI : HasPrincipalDivisors (ResidueField A) (modularFunctionFieldC (ResidueField A) N) :=
    IsCurveOver.hasPrincipalDivisors
  exact HasPrincipalDivisors.exists_divisor (K := ResidueField A) g hg

private theorem H2Recon.C2.deg_eq_one {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) : w.deg = 1 :=
  place_deg_eq_one_of_isAlgClosed (ResidueField A) N w

set_option maxHeartbeats 1600000 in
open ModularCurve.PlaceSpecialization in

private theorem H2Recon.C2.identity_fst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [CharP (ResidueField A) q] [DecidableEq (ResidueField A)]
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hf : ¬ P.IsStrictFst V) (hs : ¬ P.IsStrictSnd V)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hgood : P.IsGoodDiv D)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
    (hreg : R.RegularityLaw W) (hO : R.OrderLawFixed)
    (S : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) × Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
    (u : ↥(modularFunctionFieldBar (N * q))) (hu₁ : u ∈ R.R₁.integers) (hu₂ : u ∈ R.R₂.integers)
    (hur₁ : R.residue₁ ⟨u, hu₁⟩ ≠ 0) (hur₂ : R.residue₂ ⟨u, hu₂⟩ ≠ 0)
    (hdivu : ∀ V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      V'.ord u = ((D - (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
          - Finsupp.single V 1) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) V')
    (hdeg₁ : Divisor.degree (P.glueData S D).1 = 0) (v : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) :
    (P.glueData S D).1 v = v.ord (R.residue₁ ⟨u, hu₁⟩) := by
  have hr₁ : R.R₁.residue ⟨u, hu₁⟩ ≠ 0 := fun h0 => hur₁ (by
    rw [PlaceSpecialization.ProlongationTuple.residue₁_apply, h0, map_zero])
  have hr₂ : R.R₂.residue ⟨u, hu₂⟩ ≠ 0 := fun h0 => hur₂ (by
    rw [PlaceSpecialization.ProlongationTuple.residue₂_apply, h0, map_zero])
  obtain ⟨Δ₁, hΔ₁, hΔ₁deg⟩ := H2Recon.C2.exists_orderDivisor _ hur₁
  have hA := H2Recon.C2.legA P W hqN R hmodel hreg hO u hu₁ hu₂ hur₁ hur₂ hr₁ hr₂ _
    (fun V' => (hdivu V').symm) (P.reduceFst V) _
    (H2Recon.C2.glueData_fst_apply_eq_zero_of_fixed P D S)
    (H2Recon.C2.sub_delta_apply_eq_zero_of_fixed_fst P σ hσ V D hgood)
    (H2Recon.C2.push_fst P σ hσ V hf hs D S)
  have h₁ : Δ₁ = (P.glueData S D).1 :=
    H2Recon.C2.divisor_eq_of_forall_ne_of_degree_eq_zero _ _ (P.reduceFst V) (H2Recon.C2.deg_eq_one _)
      (fun w hw => (hΔ₁ w).trans (hA w hw)) hΔ₁deg hdeg₁
  rw [← h₁]
  exact hΔ₁ v

set_option maxHeartbeats 1600000 in
open ModularCurve.PlaceSpecialization in

private theorem H2Recon.C2.identity_snd
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [CharP (ResidueField A) q] [DecidableEq (ResidueField A)]
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hf : ¬ P.IsStrictFst V) (hs : ¬ P.IsStrictSnd V)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hgood : P.IsGoodDiv D)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
    (hreg : R.RegularityLaw W) (hO : R.OrderLawFixed)
    (S : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) × Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
    (u : ↥(modularFunctionFieldBar (N * q))) (hu₁ : u ∈ R.R₁.integers) (hu₂ : u ∈ R.R₂.integers)
    (hur₁ : R.residue₁ ⟨u, hu₁⟩ ≠ 0) (hur₂ : R.residue₂ ⟨u, hu₂⟩ ≠ 0)
    (hdivu : ∀ V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      V'.ord u = ((D - (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
          - Finsupp.single V 1) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) V')
    (hdeg₂ : Divisor.degree (P.glueData S D).2.1 = 0) (v : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) :
    (P.glueData S D).2.1 v = v.ord (R.residue₂ ⟨u, hu₂⟩) := by
  have hr₁ : R.R₁.residue ⟨u, hu₁⟩ ≠ 0 := fun h0 => hur₁ (by
    rw [PlaceSpecialization.ProlongationTuple.residue₁_apply, h0, map_zero])
  have hr₂ : R.R₂.residue ⟨u, hu₂⟩ ≠ 0 := fun h0 => hur₂ (by
    rw [PlaceSpecialization.ProlongationTuple.residue₂_apply, h0, map_zero])
  have hsnd := H2Recon.C2.reduceSnd_eq_frob_reduceFst_of_not_strict P V hs
  obtain ⟨Δ₂, hΔ₂, hΔ₂deg⟩ := H2Recon.C2.exists_orderDivisor _ hur₂
  have hB := H2Recon.C2.legB P W hqN R hmodel hreg hO u hu₁ hu₂ hur₁ hur₂ hr₁ hr₂ _
    (fun V' => (hdivu V').symm) (P.reduceFst V) _
    (H2Recon.C2.glueData_snd_apply_eq_zero_of_fixed P D S)
    (H2Recon.C2.sub_delta_apply_eq_zero_of_fixed_fst P σ hσ V D hgood)
    (fun V' hfix hne => H2Recon.C2.sub_delta_apply_eq_zero_of_fixed_snd P σ hσ V D hgood V' hfix
      (fun h => hne (h.trans hsnd)))
    (H2Recon.C2.push_snd P σ hσ V hf hs D S)
  have h₂ : Δ₂ = (P.glueData S D).2.1 :=
    H2Recon.C2.divisor_eq_of_forall_ne_of_degree_eq_zero _ _ _ (H2Recon.C2.deg_eq_one _)
      (fun w hw => (hΔ₂ w).trans (hB w hw)) hΔ₂deg hdeg₂
  rw [← h₂]
  exact hΔ₂ v

open ModularCurve.PlaceSpecialization in
private theorem H2Recon.b2_i_fixedPlace_divisor_identity
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [CharP (ResidueField A) q] [DecidableEq (ResidueField A)]
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hf : ¬ P.IsStrictFst V) (hs : ¬ P.IsStrictSnd V)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hgood : P.IsGoodDiv D)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
    (hreg : R.RegularityLaw W) (hO : R.OrderLawFixed)
    (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) D
      ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))
    (u : ↥(modularFunctionFieldBar (N * q))) (hu₁ : u ∈ R.R₁.integers) (hu₂ : u ∈ R.R₂.integers)
    (hur₁ : R.residue₁ ⟨u, hu₁⟩ ≠ 0) (hur₂ : R.residue₂ ⟨u, hu₂⟩ ≠ 0)
    (hdivu : ∀ V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      V'.ord u = ((D - (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
          - Finsupp.single V 1) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) V')
    (v : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))
    (_hv : frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr v) = v) :
    (P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) D).1 v = v.ord (R.residue₁ ⟨u, hu₁⟩) ∧
      (P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) D).2.1 v = v.ord (R.residue₂ ⟨u, hu₂⟩) :=
  ⟨H2Recon.C2.identity_fst hqN P R hmodel σ hσ V hf hs D hgood W hreg hO _ u hu₁ hu₂ hur₁ hur₂ hdivu
      (Divisor.mem_degZero.mp hadm.1) v,
    H2Recon.C2.identity_snd hqN P R hmodel σ hσ V hf hs D hgood W hreg hO _ u hu₁ hu₂ hur₁ hur₂ hdivu
      (Divisor.mem_degZero.mp hadm.2.1) v⟩

open ModularCurve.PlaceSpecialization in
open Classical in
set_option maxHeartbeats 1600000 in
private theorem H2Recon.b2_i_exists_principal_glueData_components
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [CharP (ResidueField A) q] [DecidableEq (ResidueField A)] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hf : ¬ P.IsStrictFst V) (hs : ¬ P.IsStrictSnd V)
    (hdeg : (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
            - Finsupp.single V 1)
        ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
        (F := ↥(modularFunctionFieldBar (N * q)))))
    (hcls : Pic0.mk D = Pic0.mk ⟨_, hdeg⟩)
    (hgood : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
    (hJ : GaussJump.JumpLaw R) (hreg : R.RegularityLaw W) (hO : R.OrderLawFixed)
    (hadm : (P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
        _ × _ × (↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
          → Additive (ResidueField A)ˣ)) ∈
      GluingData.admissible (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)) :
        ∃ (g₁ g₂ : ↥(modularFunctionFieldC (ResidueField A) N)), g₁ ≠ 0 ∧ g₂ ≠ 0 ∧
          (∀ v, (P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
            (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))).1 v = v.ord g₁) ∧
          (∀ v, (P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
            (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))).2.1 v = v.ord g₂) := by
  obtain ⟨u, hu₁, hu₂, hur₁, hur₂, hdivu⟩ :=
    H2Recon.stepI_exists_commonGaussUnit_of_pic0Mk_eq hqN P R hmodel σ hσ V hdeg D hcls hgood W hW hJ hadm
  obtain ⟨hδ₁, hδ₂⟩ := H2Recon.B2hdiv.deltaV_strictFilter_pushforward_zero (P := P) σ hσ V hf hs
  have hE : ∀ V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
        - (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
            - Finsupp.single V 1) :
          Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) V' = V'.ord u :=
    fun V' => (hdivu V').symm

  have hr₁' : R.R₁.residue ⟨u, hu₁⟩ ≠ 0 := fun h0 => hur₁ (by rw [PlaceSpecialization.ProlongationTuple.residue₁_apply, h0, map_zero])
  have hr₂' : R.R₂.residue ⟨u, hu₂⟩ ≠ 0 := fun h0 => hur₂ (by rw [PlaceSpecialization.ProlongationTuple.residue₂_apply, h0, map_zero])
  refine ⟨R.residue₁ ⟨u, hu₁⟩, R.residue₂ ⟨u, hu₂⟩, hur₁, hur₂, ?_, ?_⟩
  · intro v
    by_cases hv : frobOnPlacesGeomLevel (ResidueField A) N data hKr
        (frobOnPlacesGeomLevel (ResidueField A) N data hKr v) = v
    · exact (H2Recon.b2_i_fixedPlace_divisor_identity hqN P R hmodel σ hσ V hf hs _ hgood W hreg hO hadm u hu₁ hu₂
        hur₁ hur₂ hdivu v hv).1
    · have law := hmodel.1 u hu₁ hu₂ hr₁' hr₂' _ hE v hv
      rw [← law]
      show Finsupp.mapDomain P.reduceFst
        (Finsupp.filter P.IsStrictFst (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) v = _

      rw [Finsupp.filter_sub, Finsupp.mapDomain_sub, hδ₁, sub_zero]
  · intro v
    by_cases hv : frobOnPlacesGeomLevel (ResidueField A) N data hKr
        (frobOnPlacesGeomLevel (ResidueField A) N data hKr v) = v
    · exact (H2Recon.b2_i_fixedPlace_divisor_identity hqN P R hmodel σ hσ V hf hs _ hgood W hreg hO hadm u hu₁ hu₂
        hur₁ hur₂ hdivu v hv).2
    · have law := hmodel.2.1 u hu₁ hu₂ hr₁' hr₂' _ hE v hv
      rw [← law]
      show Finsupp.mapDomain P.reduceSnd
        (Finsupp.filter P.IsStrictSnd (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) v = _
      rw [Finsupp.filter_sub, Finsupp.mapDomain_sub, hδ₂, sub_zero]

set_option maxHeartbeats 9600000 in
open ModularCurve.PlaceSpecialization in

theorem solution
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
      (hO : R.OrderLawFixed) (hJ : GaussJump.JumpLaw R),
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
          ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V → P.reduceFst V ∈ W →
          ∀ (hdeg : arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
              - Finsupp.single V 1
              ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))
            (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                (F := ↥(modularFunctionFieldBar (N * q)))))
              (hgood : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
              (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
                ∈ GluingData.admissible
                    (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))
              (hcls : Pic0.mk D
                = Pic0.mk ⟨arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
                    - Finsupp.single V 1, hdeg⟩),
                ∃ χ : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) → Additive (ResidueField A)ˣ,
                  GluedPic0.mk (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                      ⟨P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), hadm⟩
                    = GluedPic0.nodeUnit (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) χ := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  intro W hW data hKr hα hβ P R hmodel hreg _hval hO hJ σ hσ V hf hs _hVW hdeg D hgood hadm hcls
  obtain ⟨g₁, g₂, hg₁, hg₂, hd₁, hd₂⟩ :=
    H2Recon.b2_i_exists_principal_glueData_components hqN P R hmodel σ hσ V hf hs hdeg D hcls hgood W hW hJ
      hreg hO hadm
  classical
  let as : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) → (ResidueField A)ˣ :=
    fun s => (H2Recon.b2_ii_exists_hasValue_nodePair _ _ hadm g₁ g₂ hg₁ hg₂ hd₁ hd₂ s).choose
  let bs : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) → (ResidueField A)ˣ :=
    fun s => (H2Recon.b2_ii_exists_hasValue_nodePair _ _ hadm g₁ g₂ hg₁ hg₂ hd₁ hd₂ s).choose_spec.choose
  have hvs : ∀ s : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W),
      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
      × Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)).1.HasValue g₁ (as s) ∧
      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
      × Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)).2.HasValue g₂ (bs s) :=
    fun s => (H2Recon.b2_ii_exists_hasValue_nodePair _ _ hadm g₁ g₂ hg₁ hg₂ hd₁ hd₂ s).choose_spec.choose_spec
  refine ⟨fun s => Additive.ofMul (bs s / as s), ?_⟩
  rw [GluedPic0.mk_eq_nodeUnit_iff]
  refine ⟨g₁, g₂, as, bs, hg₁, hg₂, ?_, ?_, fun s => hvs s, ?_⟩
  · intro v
    show ((P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))).1
      - (0 : Divisor (ResidueField A) (modularFunctionFieldC (ResidueField A) N))) v = v.ord g₁
    rw [sub_zero]; exact hd₁ v
  · intro v
    show ((P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))).2.1
      - (0 : Divisor (ResidueField A) (modularFunctionFieldC (ResidueField A) N))) v = v.ord g₂
    rw [sub_zero]; exact hd₂ v
  · funext s
    show (0 : Additive (ResidueField A)ˣ) - Additive.ofMul (bs s / as s) = Additive.ofMul (as s / bs s)
    rw [zero_sub, show -Additive.ofMul (bs s / as s) = Additive.ofMul (bs s / as s)⁻¹ from rfl, inv_div]

#print axioms solution

end S_ModularCurve_PlaceSpecialization_exists_gluedMk_eq_nodeUnit_of_isGoodDiv_of_admissible_of_pic0Mk_eq_smul_single_sub_self_of_isModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_gluedMk_eq_nodeUnit_of_isGoodDiv_of_admissible_of_pic0Mk_eq_smul_single_sub_self_of_isModel (solution)
