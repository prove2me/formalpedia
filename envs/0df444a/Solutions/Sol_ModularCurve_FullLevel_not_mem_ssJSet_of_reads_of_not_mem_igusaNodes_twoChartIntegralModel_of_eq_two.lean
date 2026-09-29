-- Prove2me | solution 1 for ModularCurve.FullLevel.not_mem_ssJSet_of_reads_of_not_mem_igusaNodes_twoChartIntegralModel_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/784024f5-3c53-5b54-84af-08a97d8a918c

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_forall_apply_mem_ssJSet_of_ker_eq_of_apply_mem_ssJSet
import Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring_of_finiteDimensional
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jqModC
import Theorems.Thm_ModularCurve_isAffineGeomPlace_or_ord_jGeomGen_lt_zero
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_FullLevel_inStalk_and_inMax_iff_mem_asIdeal_chartAlg_twoChartIntegralModel_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_coe_chartAlg_mem_integers_and_exists_residue_algebraMap_eq_twoChartIntegralModel_of_eq_two
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_not_mem_ssJSet_of_reads_of_not_mem_igusaNodes_twoChartIntegralModel_of_eq_two
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply"
p2m_attr_erase "simp" "ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000

namespace T2Aux

section CompositeValuation

variable {K F : Type} [Field K] [Field F] [Algebra K F]

theorem inv_mem_of_isUnit {O : ValuationSubring F} {f : F} (hf : f ∈ O) (hu : IsUnit (⟨f, hf⟩ : ↥O)) : f⁻¹ ∈ O := by
  obtain ⟨u, hu⟩ := hu
  have h1 : ((u⁻¹ : (↥O)ˣ) : ↥O).1 * f = 1 := by
    have h := congrArg Subtype.val (u.inv_mul)
    rw [hu] at h
    exact h
  have h2 : ((u⁻¹ : (↥O)ˣ) : ↥O).1 = f⁻¹ := eq_inv_of_mul_eq_one_left h1
  exact h2 ▸ ((u⁻¹ : (↥O)ˣ) : ↥O).2

theorem mem_maximalIdeal_inv_of_not_mem {O : ValuationSubring F} {f : F} (hf : f ∉ O) :
    ∃ hfi : f⁻¹ ∈ O, (⟨f⁻¹, hfi⟩ : ↥O) ∈ maximalIdeal ↥O := by
  have hfi : f⁻¹ ∈ O := (O.mem_or_inv_mem f).resolve_left hf
  refine ⟨hfi, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact hf (inv_inv f ▸ inv_mem_of_isUnit hfi hu)

theorem ne_zero_of_isUnit_mk {O : ValuationSubring F} {f : F} (hf : f ∈ O) (hu : IsUnit (⟨f, hf⟩ : ↥O)) : f ≠ 0 := by
  rintro rfl
  exact not_isUnit_zero ((show (⟨(0 : F), hf⟩ : ↥O) = 0 from rfl) ▸ hu)

noncomputable def resEquiv (P : Place K F) (hP : P.IsRational) : K ≃+* P.ResidueField :=
  RingEquiv.ofBijective (algebraMap K P.ResidueField) ⟨P.algebraMap_residueField_injective, hP⟩

noncomputable def ev (P : Place K F) (hP : P.IsRational) : ↥P.toValuationSubring →+* K :=
  (resEquiv P hP).symm.toRingHom.comp (IsLocalRing.residue ↥P.toValuationSubring)

theorem ev_eq_evalAt (P : Place K F) (hP : P.IsRational) (f : F) (hf : f ∈ P.toValuationSubring) :
    ev P hP ⟨f, hf⟩ = P.evalAt f := by
  apply P.algebraMap_residueField_injective
  rw [P.algebraMap_evalAt hP hf]
  change (resEquiv P hP) ((resEquiv P hP).symm (IsLocalRing.residue _ ⟨f, hf⟩)) = _
  rw [RingEquiv.apply_symm_apply]

theorem evalAt_algebraMap (P : Place K F) (hP : P.IsRational) (a : K) :
    P.evalAt (algebraMap K F a) = a := by
  rw [← ev_eq_evalAt P hP _ (P.algebraMap_mem' a)]
  apply P.algebraMap_residueField_injective
  change (resEquiv P hP) ((resEquiv P hP).symm (IsLocalRing.residue _ _)) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

theorem ev_eq_zero_iff (P : Place K F) (hP : P.IsRational) (f : ↥P.toValuationSubring) :
    ev P hP f = 0 ↔ f ∈ maximalIdeal ↥P.toValuationSubring := by
  rw [← IsLocalRing.residue_eq_zero_iff]
  change (resEquiv P hP).symm _ = 0 ↔ _
  rw [map_eq_zero_iff _ (resEquiv P hP).symm.injective]

theorem evalAt_mul (P : Place K F) (hP : P.IsRational) {f g : F} (hf : f ∈ P.toValuationSubring) (hg : g ∈ P.toValuationSubring) :
    P.evalAt (f * g) = P.evalAt f * P.evalAt g := by
  rw [← ev_eq_evalAt P hP f hf, ← ev_eq_evalAt P hP g hg, ← ev_eq_evalAt P hP (f * g) (mul_mem hf hg), ← map_mul]; rfl

theorem evalAt_add (P : Place K F) (hP : P.IsRational) {f g : F} (hf : f ∈ P.toValuationSubring) (hg : g ∈ P.toValuationSubring) :
    P.evalAt (f + g) = P.evalAt f + P.evalAt g := by
  rw [← ev_eq_evalAt P hP f hf, ← ev_eq_evalAt P hP g hg, ← ev_eq_evalAt P hP (f + g) (add_mem hf hg), ← map_add]; rfl

theorem evalAt_neg (P : Place K F) (hP : P.IsRational) {f : F} (hf : f ∈ P.toValuationSubring) :
    P.evalAt (-f) = -P.evalAt f := by
  rw [← ev_eq_evalAt P hP f hf, ← ev_eq_evalAt P hP (-f) (neg_mem hf), ← map_neg]; rfl

theorem evalAt_sub (P : Place K F) (hP : P.IsRational) {f g : F} (hf : f ∈ P.toValuationSubring) (hg : g ∈ P.toValuationSubring) :
    P.evalAt (f - g) = P.evalAt f - P.evalAt g := by
  rw [← ev_eq_evalAt P hP f hf, ← ev_eq_evalAt P hP g hg, ← ev_eq_evalAt P hP (f - g) (sub_mem hf hg), ← map_sub]; rfl

theorem evalAt_eq_zero_iff (P : Place K F) (hP : P.IsRational) {f : F} (hf : f ∈ P.toValuationSubring) :
    P.evalAt f = 0 ↔ (⟨f, hf⟩ : ↥P.toValuationSubring) ∈ maximalIdeal ↥P.toValuationSubring := by
  rw [← ev_eq_evalAt P hP f hf, ev_eq_zero_iff]

end CompositeValuation

end T2Aux

namespace E140CR

open ModularCurve ModularCurve.FullLevel IsLocalRing AlgebraicCurve

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem isRational_place_xHFunctionFieldC (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (Q : Place (ResidueField ↥A) ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M'))) :
    Q.IsRational := by
  haveI : (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH _ _)
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  haveI : IsCurveOver (ResidueField ↥A) ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')) :=
    ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed _ _ (ModularCurve.translation_mem_GammaH _ _)
  haveI : Module.Finite (ResidueField ↥A) Q.ResidueField := IsCurveOver.finiteResidue Q
  haveI : Algebra.IsIntegral (ResidueField ↥A) Q.ResidueField := Algebra.IsIntegral.of_finite _ _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ResidueField ↥A) (K := Q.ResidueField)).2

end E140CR

namespace E147B3

abbrev fieldOf {K L : Type*} [Field K] [Field L] [Algebra K L] {S : IntermediateField K L} (_x : ↥S) :
    IntermediateField K L := S
end E147B3

namespace E147B2

section Restrict

variable {K F F' : Type} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

def resHom (s : Place K F) (Q : Place K F') (j : F →+* F')
    (hmem : ∀ g : F, g ∈ s.toValuationSubring ↔ j g ∈ Q.toValuationSubring) :
    ↥s.toValuationSubring →+* ↥Q.toValuationSubring where
  toFun x := ⟨j x, (hmem x).mp x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

theorem coe_resHom (s : Place K F) (Q : Place K F') (j : F →+* F')
    (hmem : ∀ g : F, g ∈ s.toValuationSubring ↔ j g ∈ Q.toValuationSubring) (x : ↥s.toValuationSubring) :
    ((resHom s Q j hmem x : ↥Q.toValuationSubring) : F') = j x := rfl

theorem resHom_mem_maximalIdeal_iff (s : Place K F) (Q : Place K F') (j : F →+* F')
    (hmem : ∀ g : F, g ∈ s.toValuationSubring ↔ j g ∈ Q.toValuationSubring) (x : ↥s.toValuationSubring) :
    resHom s Q j hmem x ∈ maximalIdeal ↥Q.toValuationSubring ↔ x ∈ maximalIdeal ↥s.toValuationSubring := by
  rw [← ValuationSubring.coe_mem_nonunits_iff, ← ValuationSubring.coe_mem_nonunits_iff, coe_resHom,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ← map_inv₀, ← hmem,
    map_eq_zero_iff j j.injective]

scoped instance isLocalHom_resHom (s : Place K F) (Q : Place K F') (j : F →+* F')
    (hmem : ∀ g : F, g ∈ s.toValuationSubring ↔ j g ∈ Q.toValuationSubring) :
    IsLocalHom (resHom s Q j hmem) := by
  constructor
  intro x hx
  by_contra hnu
  have hxm : x ∈ maximalIdeal ↥s.toValuationSubring := (IsLocalRing.mem_maximalIdeal _).mpr hnu
  have := (resHom_mem_maximalIdeal_iff s Q j hmem x).mpr hxm
  exact (IsLocalRing.mem_maximalIdeal _).mp this hx

theorem isRational_restrict (s : Place K F) (Q : Place K F') (j : F →+* F')
    (hmem : ∀ g : F, g ∈ s.toValuationSubring ↔ j g ∈ Q.toValuationSubring)
    (hQ : Q.IsRational) (hjK : ∀ c : K, j (algebraMap K F c) = algebraMap K F' c) : s.IsRational := by
  intro r
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
  obtain ⟨c, hc⟩ := hQ (IsLocalRing.residue _ (resHom s Q j hmem x))
  refine ⟨c, ?_⟩
  change IsLocalRing.residue _ (algebraMap K ↥s.toValuationSubring c) = IsLocalRing.residue _ x
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← resHom_mem_maximalIdeal_iff s Q j hmem,
    ← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub, sub_eq_zero, ← hc]
  have : resHom s Q j hmem (algebraMap K ↥s.toValuationSubring c) = algebraMap K ↥Q.toValuationSubring c :=
    Subtype.ext (hjK c)
  rw [this]
  rfl

theorem evalAt_restrict (s : Place K F) (Q : Place K F') (j : F →+* F')
    (hmem : ∀ g : F, g ∈ s.toValuationSubring ↔ j g ∈ Q.toValuationSubring)
    (hQ : Q.IsRational) (hjK : ∀ c : K, j (algebraMap K F c) = algebraMap K F' c)
    (g : F) (hg : g ∈ s.toValuationSubring) : s.evalAt g = Q.evalAt (j g) := by
  have hs := isRational_restrict s Q j hmem hQ hjK
  have hg' : j g ∈ Q.toValuationSubring := (hmem g).mp hg
  rw [← T2Aux.ev_eq_evalAt s hs g hg, ← T2Aux.ev_eq_evalAt Q hQ (j g) hg']
  apply Q.algebraMap_residueField_injective
  have key : ∀ y : ↥Q.toValuationSubring,
      algebraMap K Q.ResidueField (T2Aux.ev Q hQ y) = IsLocalRing.residue _ y := by
    intro y
    change (T2Aux.resEquiv Q hQ) ((T2Aux.resEquiv Q hQ).symm _) = _
    rw [RingEquiv.apply_symm_apply]
  have key' : ∀ y : ↥s.toValuationSubring,
      algebraMap K s.ResidueField (T2Aux.ev s hs y) = IsLocalRing.residue _ y := by
    intro y
    change (T2Aux.resEquiv s hs) ((T2Aux.resEquiv s hs).symm _) = _
    rw [RingEquiv.apply_symm_apply]
  have hmap : ∀ c : K, IsLocalRing.ResidueField.map (resHom s Q j hmem) (algebraMap K s.ResidueField c) =
      algebraMap K Q.ResidueField c := by
    intro c
    change IsLocalRing.ResidueField.map (resHom s Q j hmem) (IsLocalRing.residue _ (algebraMap K ↥s.toValuationSubring c)) =
      IsLocalRing.residue _ (algebraMap K ↥Q.toValuationSubring c)
    rw [IsLocalRing.ResidueField.map_residue]
    congr 1
    exact Subtype.ext (hjK c)
  rw [key, ← hmap, key', IsLocalRing.ResidueField.map_residue]
  rfl

end Restrict

theorem evalAt_mem_ssJSet_of_apply_mem_ssJSet (q : ℕ) [Fact q.Prime]
    {K Fbar : Type} [Field K] [Field Fbar] [Algebra K Fbar] [DecidableEq K] [CharP K q] [IsAlgClosed K]
    (Q : Place K Fbar) (hQ : Q.IsRational)
    {B : Type} [CommRing B] (ρ : B →+* ↥Q.toValuationSubring) (𝔭 : Ideal B)
    (hker : ∀ b : B, ρ b ∈ maximalIdeal ↥Q.toValuationSubring ↔ b ∈ 𝔭) (a : B)
    (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω] (φ : B →+* Ω)
    (hφ : RingHom.ker φ = 𝔭) (hss : φ a ∈ ssJSet q Ω) :
    Q.evalAt ((ρ a : ↥Q.toValuationSubring) : Fbar) ∈ ssJSet q K := by
  let φ₀ : B →+* K := (T2Aux.ev Q hQ).comp ρ
  have hker₀ : RingHom.ker φ₀ = RingHom.ker φ := by
    rw [hφ]; ext b
    rw [RingHom.mem_ker, RingHom.comp_apply, T2Aux.ev_eq_zero_iff, hker]
  have h := ModularCurve.forall_apply_mem_ssJSet_of_ker_eq_of_apply_mem_ssJSet q a φ hss K φ₀ hker₀
  have : φ₀ a = Q.evalAt ((ρ a : ↥Q.toValuationSubring) : Fbar) := by
    change T2Aux.ev Q hQ (ρ a) = _
    rw [← T2Aux.ev_eq_evalAt Q hQ _ (ρ a).2]
  rw [← this]
  exact h

theorem mem_nodes (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) q] [IsAlgClosed (ResidueField ↥A)]
    (W : Finset (Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField ↥A))
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (NIg : Finset (Place (ResidueField ↥A) Fbar))
    (jmap : ↥(modularFunctionFieldC (ResidueField ↥A) M') →+* Fbar)
    (hjK : ∀ c : ResidueField ↥A, jmap (algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') c) =
      algebraMap (ResidueField ↥A) Fbar c)
    (hNIg : ∀ Q : Place (ResidueField ↥A) Fbar, Q ∈ NIg ↔ ∃ s : ↥W,
      ∀ g : ↥(modularFunctionFieldC (ResidueField ↥A) M'),
        g ∈ (s : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')).toValuationSubring ↔
          jmap g ∈ Q.toValuationSubring)
    (Q : Place (ResidueField ↥A) Fbar) (hQ : Q.IsRational)
    (hj : jmap (jGeomGen (ResidueField ↥A) M') ∈ Q.toValuationSubring)
    (hss : Q.evalAt (jmap (jGeomGen (ResidueField ↥A) M')) ∈ ssJSet q (ResidueField ↥A)) :
    Q ∈ NIg := by
  let O : ValuationSubring ↥(modularFunctionFieldC (ResidueField ↥A) M') := Q.toValuationSubring.comap jmap
  have hOK : ∀ c : ResidueField ↥A, algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') c ∈ O := by
    intro c
    rw [ValuationSubring.mem_comap, hjK]
    exact Q.algebraMap_mem' c
  have hOtop : O ≠ ⊤ := by
    intro htop
    have hall : ∀ g : ↥(modularFunctionFieldC (ResidueField ↥A) M'), jmap g ∈ Q.toValuationSubring := by
      intro g
      have : g ∈ O := by rw [htop]; exact ValuationSubring.mem_top g
      exact ValuationSubring.mem_comap.mp this
    have hg0 : jGeomGen (ResidueField ↥A) M' -
        algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')
          (Q.evalAt (jmap (jGeomGen (ResidueField ↥A) M'))) ≠ 0 := by
      intro h
      have halg : IsAlgebraic (ResidueField ↥A) (jGeomGen (ResidueField ↥A) M') := by
        rw [sub_eq_zero.mp h]
        exact isAlgebraic_algebraMap _
      exact ModularCurve.transcendental_jqModC (ResidueField ↥A) (IntermediateField.isAlgebraic_iff.mp halg)
    have hunit : Q.evalAt (jmap (jGeomGen (ResidueField ↥A) M' -
        algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')
          (Q.evalAt (jmap (jGeomGen (ResidueField ↥A) M'))))) ≠ 0 := by
      rw [Ne, T2Aux.evalAt_eq_zero_iff Q hQ (hall _), IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
      refine isUnit_iff_exists_inv.mpr ⟨⟨jmap (jGeomGen (ResidueField ↥A) M' -
        algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')
          (Q.evalAt (jmap (jGeomGen (ResidueField ↥A) M'))))⁻¹, hall _⟩, Subtype.ext ?_⟩
      change jmap _ * jmap _ = 1
      rw [← map_mul, mul_inv_cancel₀ hg0, map_one]
    apply hunit
    rw [map_sub, T2Aux.evalAt_sub Q hQ (hall _) (hall _), hjK, T2Aux.evalAt_algebraMap Q hQ, sub_self]
  haveI := ModularCurve.finiteDimensional_adjoin_jqModC (N := M') A
  obtain ⟨s, hs⟩ := AlgebraicCurve.Place.exists_of_valuationSubring_of_finiteDimensional
    ((⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) M'⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) M')))
    O hOK hOtop
  have hmem : ∀ g : ↥(modularFunctionFieldC (ResidueField ↥A) M'),
      g ∈ s.toValuationSubring ↔ jmap g ∈ Q.toValuationSubring := by
    intro g; rw [hs]; exact ValuationSubring.mem_comap
  have hsW : s ∈ W := by
    rw [hW, mem_ssPlaces_iff]
    refine ⟨isRational_restrict s Q jmap hmem hQ hjK, ?_, ?_⟩
    · rcases ModularCurve.isAffineGeomPlace_or_ord_jGeomGen_lt_zero (ResidueField ↥A) M' s with h | h
      · exact h
      · exact absurd h (not_lt.mpr (AlgebraicCurve.Place.ord_nonneg_of_mem s ((hmem _).mpr hj)))
    · rw [evalAt_restrict s Q jmap hmem hQ hjK _ ((hmem _).mpr hj)]
      exact hss
  exact (hNIg Q).mpr ⟨⟨s, hsW⟩, hmem⟩

end E147B2
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_not_mem_ssJSet_of_reads_of_not_mem_igusaNodes_twoChartIntegralModel_of_eq_two.E147B2"

namespace E147B2

open ModularCurve.FullLevel CongruenceSubgroup

theorem coeffMap_subtype_laurentMap_jqInt {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) :
    coeffMap A.subtype (laurentMap (Int.castRingHom ↥A) jqInt) = coeffEmb L jq := by
  rw [← laurentMap_jqInt]
  ext k
  rw [coeffMap_coeff, laurentMap_coeff, coeffEmb_coeff, laurentMap_coeff]
  simp

theorem laurentMap_jqInt_geom (K : Type*) [Field K] : laurentMap (Int.castRingHom K) jqInt = jqModC K := by
  rw [jqModC, jqInt, map_mul, laurentMap_single, laurentMap_ofPowerSeries, map_one]

theorem coeffMap_residue_laurentMap_jqInt {L : Type*} [Field L] (A : ValuationSubring L) :
    coeffMap (IsLocalRing.residue ↥A) (laurentMap (Int.castRingHom ↥A) jqInt) = jqModC (ResidueField ↥A) := by
  rw [← laurentMap_jqInt_geom]
  ext k
  rw [coeffMap_coeff, laurentMap_coeff, laurentMap_coeff]
  simp

theorem residue_eq_jmap_jGeomGen (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))
    (jmap : modularFunctionFieldC (ResidueField A) M' →+* xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))
    (hjmap : ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers, R.residue ⟨_, hC⟩ = jmap (R₀.residue ⟨f, hf⟩))
    (t : ↥(fieldBar q M'))
    (ht : t = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')))
    (htR : t ∈ R.integers)
    (hfM : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers) :
    R.residue ⟨t, htR⟩ = jmap (jGeomGen (ResidueField A) M') := by
  obtain ⟨hC, e1⟩ := hjmap _ hfM
  have e0 : (⟨t, htR⟩ : ↥R.integers) = ⟨_, hC⟩ := Subtype.ext ht
  rw [e0, e1]
  congr 1
  have hyA := coeffMap_subtype_laurentMap_jqInt A
  have hy : coeffMap A.subtype (laurentMap (Int.castRingHom ↥A) jqInt) ∈ modularFunctionFieldBar M' := by
    rw [hyA]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))
  obtain ⟨h2, e2⟩ := hR₀ _ hy
  have efm : (⟨coeffMap A.subtype (laurentMap (Int.castRingHom ↥A) jqInt), hy⟩ : ↥(modularFunctionFieldBar M')) =
      ⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :=
    Subtype.ext hyA
  have key : R₀.residue ⟨_, h2⟩ = R₀.residue ⟨_, hfM⟩ := by
    congr 1
    exact Subtype.ext efm
  rw [← key]
  apply Subtype.ext
  rw [e2, coeffMap_residue_laurentMap_jqInt]
  rfl

theorem jmap_algebraMap (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))
    (jmap : modularFunctionFieldC (ResidueField A) M' →+* xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))
    (hjmap : ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers, R.residue ⟨_, hC⟩ = jmap (R₀.residue ⟨f, hf⟩))
    (c : ResidueField ↥A) :
    jmap (algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') c) =
      algebraMap (ResidueField ↥A) ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')) c := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
  have hf : (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (a : AlgebraicClosure ℚ)) ∈ R₀.integers :=
    (R₀.algebraMap_mem_iff _).mpr a.2
  obtain ⟨hC, e1⟩ := hjmap _ hf
  have e2 : (⟨IntermediateField.inclusion hle (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (a : AlgebraicClosure ℚ)), hC⟩ : ↥R.integers) =
      ⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : AlgebraicClosure ℚ), (R.algebraMap_mem_iff _).mpr a.2⟩ :=
    Subtype.ext rfl
  rw [e2, R.residue_algebraMap a] at e1
  have e3 : R₀.residue ⟨_, hf⟩ = algebraMap (ResidueField ↥A) _ (IsLocalRing.residue ↥A a) := R₀.residue_algebraMap a
  rw [e3] at e1
  exact e1.symm

end E147B2
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_not_mem_ssJSet_of_reads_of_not_mem_igusaNodes_twoChartIntegralModel_of_eq_two.E147B2"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hR : R.integers = OIg (lineInfty q))
    (hR₀O : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q))

    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ₀ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ₀⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (ζ₀ : ↥k₀) (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))

    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)
    [IsDiscreteValuationRing ↥A₁] [HenselianLocalRing ↥A₁] :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra

    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ' γ f ∈ F₀) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →

    ∀ [Algebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)],
      (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) →
    ∀ (j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))) →
    ∀ [Fact (j₁ ≠ 0)],

    ∀ (NIg : Finset (Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))),
      (∃ j : modularFunctionFieldC (ResidueField A) M' →+* xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'),
        (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers, R.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
        ∀ Q, Q ∈ NIg ↔ ∃ s : ↥W, ∀ g : modularFunctionFieldC (ResidueField A) M',
          g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
            j g ∈ Q.toValuationSubring) →

    let InStalk : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → Prop := fun x f =>
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))
    let InMax : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → Prop := fun x f =>
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))
    let Centred : Place (AlgebraicClosure ℚ) ↥(fieldBar q M') → ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun P x =>
      P.IsRational ∧ ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), InStalk x f →
        (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A ∧
          (A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ InMax x f)

    let GoodPt : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun x =>
      (AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base x = closedPoint ↥A₁ ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), x ⤳ y → y = x) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* Ω), RingHom.ker φ = y.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ∉ ModularCurve.ssJSet q Ω)

    let Reads : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Prop := fun x Q =>
      ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), InStalk x f →
        ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring ∧
          (R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring.nonunits ↔ InMax x f)

    let OffBranch : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun x =>
      ∀ ℓ : CuspidalType.ProjLine q, ℓ ≠ lineInfty q →
        (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
          ∃ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ (OIg ℓ).nonunits ∧ b ∉ y.asIdeal) ∧
        (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
          ∃ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ (OIg ℓ).nonunits ∧ b ∉ y.asIdeal)

    ∀ x : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁),
      (AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base x = closedPoint ↥A₁ →
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), x ⤳ y → y = x) →
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) →
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) →
      ∀ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg → Reads x Q →
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* Ω), RingHom.ker φ = y.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ∉ ModularCurve.ssJSet q Ω) := by
  intro F₀ hK1 hstab hLD hRAT instAlg hconst j₁ hj₁ instFact NIg hN
  intro InStalk InMax Centred GoodPt Reads OffBranch x hsp hcl hbF hbI Q hQN hreads y hy Ω _ _ _ _ φ hker hss
  subst hy
  have hqprime : q.Prime := Fact.out

  have hrat : Q.IsRational := E140CR.isRational_place_xHFunctionFieldC q M' A Q
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  haveI : CharP (ResidueField ↥A) q := by
    apply (CharP.charP_iff_prime_eq_zero hqprime).mpr
    have h1 : ((q : ↥A) : AlgebraicClosure ℚ) ∈ A.nonunits := by push_cast; exact hA
    have h2 : (q : ↥A) ∈ maximalIdeal ↥A := ValuationSubring.coe_mem_nonunits_iff.mp h1
    have h3 := (IsLocalRing.residue_eq_zero_iff _).mpr h2
    rwa [map_natCast] at h3

  obtain ⟨hdict, -⟩ := ModularCurve.FullLevel.inStalk_and_inMax_iff_mem_asIdeal_chartAlg_twoChartIntegralModel_of_eq_two
    q hq2 M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr R hR hR₀O π hπ hπP k₀ π₀ hπ₀ hdvr hunif hhens hres hκ ℓ hℓ hℓ3 hℓq hℓM' ζ₀ hζ₀ ϖt hϖtA hϖt K₁ hK₁ A₁ hA₁ F₀ hK1 hstab hLD hRAT hconst j₁ hj₁
  obtain ⟨hRint, -, -⟩ := ModularCurve.FullLevel.coe_chartAlg_mem_integers_and_exists_residue_algebraMap_eq_twoChartIntegralModel_of_eq_two
    q hq2 M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr R hR hR₀O π hπ hπP k₀ π₀ hπ₀ hdvr hunif hhens hres hκ ℓ hℓ hℓ3 hℓq hℓM' ζ₀ hζ₀ ϖt hϖtA hϖt K₁ hK₁ A₁ hA₁ F₀ hK1 hstab hLD hRAT hconst j₁ hj₁ NIg hN
  obtain ⟨jmap, hjmap, hNIg⟩ := hN

  have hrd := fun b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(E147B3.fieldOf j₁) j₁) =>
    hreads (b : ↥(E147B3.fieldOf j₁)) (hdict y b).1
  let ι : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(E147B3.fieldOf j₁) j₁) →+* ↥(fieldBar q M') :=
    (algebraMap ↥(E147B3.fieldOf j₁) ↥(fieldBar q M')).comp
      (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(E147B3.fieldOf j₁) j₁) ↥(E147B3.fieldOf j₁))
  let ψ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(E147B3.fieldOf j₁) j₁) →+* ↥R.integers :=
    ι.codRestrict R.integers (fun b => hRint b)
  let ρ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(E147B3.fieldOf j₁) j₁) →+* ↥Q.toValuationSubring :=
    (R.residue.comp ψ).codRestrict Q.toValuationSubring (fun b => (hrd b).snd.1)
  have hkerρ : ∀ b, ρ b ∈ maximalIdeal ↥Q.toValuationSubring ↔ b ∈ y.asIdeal := by
    intro b
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    exact (hrd b).snd.2.trans (hdict y b).2

  have h1 := E147B2.evalAt_mem_ssJSet_of_apply_mem_ssJSet q Q hrat ρ y.asIdeal hkerρ
    (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(E147B3.fieldOf j₁) j₁) Ω φ hker hss
  have hjR : (j₁ : ↥(fieldBar q M')) ∈ R.integers :=
    hRint (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(E147B3.fieldOf j₁) j₁)
  have hfM : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) ∈ R₀.integers := by
    rw [hR₀O, ← hj₁, ← hR]
    exact hjR
  have hstar := E147B2.residue_eq_jmap_jGeomGen q M' A hle R₀ hR₀ R jmap hjmap (j₁ : ↥(fieldBar q M')) hj₁ hjR hfM
  have hρj : ((ρ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(E147B3.fieldOf j₁) j₁) : ↥Q.toValuationSubring) :
      ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M'))) = jmap (jGeomGen (ResidueField ↥A) M') := hstar
  have hjQ : jmap (jGeomGen (ResidueField ↥A) M') ∈ Q.toValuationSubring :=
    hρj ▸ (ρ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(E147B3.fieldOf j₁) j₁)).2
  rw [hρj] at h1

  have hjK := E147B2.jmap_algebraMap q M' A hle R₀ R jmap hjmap
  exact hQN (E147B2.mem_nodes q M' A W hW NIg jmap hjK hNIg Q hrat hjQ h1)

#print axioms solution

end S_ModularCurve_FullLevel_not_mem_ssJSet_of_reads_of_not_mem_igusaNodes_twoChartIntegralModel_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_not_mem_ssJSet_of_reads_of_not_mem_igusaNodes_twoChartIntegralModel_of_eq_two (solution)
