-- Prove2me | solution 1 for ModularCurve.exists_pairing_nsmul_eq_zero_galois_hecke
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/4180c027-d608-5461-b590-696fefeeab76

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_weilReciprocity
import Theorems.Thm_AlgebraicCurve_Pic0_nonempty_divisorialWeilPairingData
import Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_toHom_injective_of_divisible
import Theorems.Thm_AlgebraicCurve_Pic0_exists_zsmul_eq_of_finiteDimensional_ratFunc
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar
import Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_pair_semilinearSmul
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_exists_frickeAlgEquiv_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_galois_smul_ofAlgAut_smul_of_fricke
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero
import Definitions.Def_ModularCurve_JLinePlacesBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_pairing_nsmul_eq_zero_galois_hecke
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateMap_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply HahnSeries.ramScale_apply"

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_pairing_nsmul_eq_zero_galois_hecke.ModularCurve AlgebraicCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "heckeOperatorBar HeckeOperatorsCommuteBar heckeModuleBar heckeModuleBar_heckeGen_smul heckeModuleBar_C_smul arithmeticGalois baseAut_arithmeticGalois galois_smul_pic0_def modularFunctionFieldBar JZero qExpand jq modularFunctionFieldFull coeffEmb HeckeAlg heckeGen heckeOperatorsCommuteBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar exists_transcendental_finiteDimensional_modularFunctionFieldBar isCurveOver_modularFunctionFieldBar exists_frickeAlgEquiv_modularFunctionFieldBar galois_smul_ofAlgAut_smul_of_fricke finiteDimensional_adjoin_coeffEmb_jq_of_neZero jLineBar jLineBarRingEquiv jLineBarRingEquiv_algebraMap"
namespace FrickeTwistedWeilPairing
p2m_open "ModularCurve"

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} [NeZero n] [HasPrincipalDivisors K F]
  (e : DivisorialWeilPairingData K F n) (w : SemilinearAut K F)

def tor (x : Pic0 K F) (hx : n • x = 0) : Pic0.torsion K F n :=
  ⟨x, Pic0.mem_torsion.mpr (by rw [natCast_zsmul]; exact hx)⟩

omit [NeZero n] [HasPrincipalDivisors K F] in
@[scoped simp] theorem coe_tor (x : Pic0 K F) (hx : n • x = 0) : (tor x hx : Pic0 K F) = x := rfl

omit [NeZero n] [HasPrincipalDivisors K F] in
theorem nsmul_coe_eq_zero (x : Pic0.torsion K F n) : n • (x : Pic0 K F) = 0 := by
  have := Pic0.mem_torsion.mp x.2
  rwa [natCast_zsmul] at this

omit [NeZero n] [HasPrincipalDivisors K F] in
theorem tor_coe (x : Pic0.torsion K F n) : tor (x : Pic0 K F) (nsmul_coe_eq_zero x) = x :=
  Subtype.ext rfl

open Classical in

def B (x y : Pic0 K F) : K :=
  if h : n • x = 0 ∧ n • y = 0 then e.pair (tor x h.1) (w • tor y h.2) else 1

theorem B_eq {x y : Pic0 K F} (hx : n • x = 0) (hy : n • y = 0) :
    B e w x y = e.pair (tor x hx) (w • tor y hy) := by
  simp only [B, dif_pos (And.intro hx hy)]

theorem B_coe (X Y : Pic0.torsion K F n) :
    B e w X Y = e.pair X (w • Y) := by
  rw [B_eq e w (nsmul_coe_eq_zero X) (nsmul_coe_eq_zero Y), tor_coe, tor_coe]

omit [NeZero n] [HasPrincipalDivisors K F] in
theorem add_tors {x x' : Pic0 K F} (hx : n • x = 0) (hx' : n • x' = 0) : n • (x + x') = 0 := by
  rw [nsmul_add, hx, hx', add_zero]

omit [NeZero n] [HasPrincipalDivisors K F] in
theorem zsmul_tors {x : Pic0 K F} (k : ℤ) (hx : n • x = 0) : n • (k • x) = 0 := by
  rw [smul_comm, hx, smul_zero]

omit [NeZero n] [HasPrincipalDivisors K F] in
theorem neg_tors {x : Pic0 K F} (hx : n • x = 0) : n • (-x) = 0 := by
  rw [neg_nsmul, hx, neg_zero]

theorem B_add_left {x x' y : Pic0 K F} (hx : n • x = 0) (hx' : n • x' = 0) (hy : n • y = 0) :
    B e w (x + x') y = B e w x y * B e w x' y := by
  rw [B_eq e w (add_tors hx hx') hy, B_eq e w hx hy, B_eq e w hx' hy, ← e.pair_add_left]
  rfl

theorem B_add_right {x y y' : Pic0 K F} (hx : n • x = 0) (hy : n • y = 0) (hy' : n • y' = 0) :
    B e w x (y + y') = B e w x y * B e w x y' := by
  rw [B_eq e w hx (add_tors hy hy'), B_eq e w hx hy, B_eq e w hx hy', ← e.pair_add_right, ← smul_add]
  rfl

theorem B_zero_left {y : Pic0 K F} (hy : n • y = 0) : B e w 0 y = 1 := by
  rw [B_eq e w (nsmul_zero n) hy]
  exact e.pair_zero_left _

theorem B_zero_right {x : Pic0 K F} (hx : n • x = 0) : B e w x 0 = 1 := by
  rw [B_eq e w hx (nsmul_zero n)]
  have : w • tor (0 : Pic0 K F) (nsmul_zero n) = 0 := by
    have h0 : tor (0 : Pic0 K F) (nsmul_zero n) = (0 : Pic0.torsion K F n) := Subtype.ext rfl
    rw [h0, smul_zero]
  rw [this]
  exact e.pair_zero_right _

theorem B_ne_zero {x y : Pic0 K F} (hx : n • x = 0) (hy : n • y = 0) : B e w x y ≠ 0 := by
  rw [B_eq e w hx hy]; exact e.pair_ne_zero _ _

theorem B_neg_left {x y : Pic0 K F} (hx : n • x = 0) (hy : n • y = 0) :
    B e w (-x) y = (B e w x y)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← B_add_left e w (neg_tors hx) hx hy, neg_add_cancel, B_zero_left e w hy]

theorem B_neg_right {x y : Pic0 K F} (hx : n • x = 0) (hy : n • y = 0) :
    B e w x (-y) = (B e w x y)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← B_add_right e w hx (neg_tors hy) hy, neg_add_cancel, B_zero_right e w hx]

theorem toHom_eq_zero_of_forall {x : Pic0 K F} (hx : n • x = 0)
    (h : ∀ y : Pic0 K F, n • y = 0 → B e w x y = 1) : e.toHom (tor x hx) = 0 := by
  have key : ∀ Y : Pic0.torsion K F n, e.pair (tor x hx) Y = 1 := by
    intro Y
    have hY := h ((w⁻¹ • Y : Pic0.torsion K F n) : Pic0 K F) (nsmul_coe_eq_zero _)
    rw [B_eq e w hx (nsmul_coe_eq_zero _), tor_coe, smul_inv_smul] at hY
    exact hY
  show Additive.ofMul (e.toChar (tor x hx)) = 0
  have : e.toChar (tor x hx) = 1 := by
    ext Y
    rw [DivisorialWeilPairingData.toChar_apply, AddChar.one_apply]
    exact key Y
  rw [this, ofMul_one]

theorem B_smul (g : SemilinearAut K F) (hcomm : ∀ Y : Pic0.torsion K F n, g • (w • Y) = w • (g • Y))
    {x y : Pic0 K F} (hx : n • x = 0) (hy : n • y = 0) :
    B e w (g • x) (g • y) = SemilinearAut.baseAut g (B e w x y) := by
  have hgx : n • (g • x) = 0 := nsmul_coe_eq_zero (g • tor x hx)
  have hgy : n • (g • y) = 0 := nsmul_coe_eq_zero (g • tor y hy)
  rw [B_eq e w hgx hgy, B_eq e w hx hy, ← e.pair_semilinearSmul g, hcomm]
  rfl

end Generic

section Tower

variable (N : ℕ) [NeZero N]

@[reducible] def ratFuncAlgebra : Algebra (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar N) :=
  ((algebraMap (jLineBar N) (modularFunctionFieldBar N)).comp (jLineBarRingEquiv N).toRingHom).toAlgebra

attribute [local instance] ratFuncAlgebra

theorem algebraMap_ratFunc_apply (r : RatFunc (AlgebraicClosure ℚ)) :
    algebraMap (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar N) r =
      algebraMap (jLineBar N) (modularFunctionFieldBar N) (jLineBarRingEquiv N r) := rfl

set_option synthInstance.maxHeartbeats 1600000 in
theorem isScalarTower_ratFunc :
    IsScalarTower (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar N) :=
  IsScalarTower.of_algebraMap_eq (fun a => by
    rw [algebraMap_ratFunc_apply, jLineBarRingEquiv_algebraMap, ← IsScalarTower.algebraMap_apply])

attribute [local instance] isScalarTower_ratFunc

set_option synthInstance.maxHeartbeats 1600000 in
theorem finiteDimensional_ratFunc :
    FiniteDimensional (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar N) := by
  letI : Algebra (RatFunc (AlgebraicClosure ℚ)) (jLineBar N) := (jLineBarRingEquiv N).toRingHom.toAlgebra
  haveI : IsScalarTower (RatFunc (AlgebraicClosure ℚ)) (jLineBar N) (modularFunctionFieldBar N) :=
    IsScalarTower.of_algebraMap_eq (fun r => (algebraMap_ratFunc_apply N r))
  haveI : Module.Finite (RatFunc (AlgebraicClosure ℚ)) (jLineBar N) :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc (AlgebraicClosure ℚ)) (jLineBar N))
      (jLineBarRingEquiv N).surjective
  haveI : Module.Finite (jLineBar N) (modularFunctionFieldBar N) :=
    finiteDimensional_adjoin_coeffEmb_jq_of_neZero N
  exact Module.Finite.trans (jLineBar N) (modularFunctionFieldBar N)

attribute [local instance] finiteDimensional_ratFunc

theorem hasPrincipalDivisors : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  hasPrincipalDivisors_modularFunctionFieldBar_unconditional N

attribute [local instance] hasPrincipalDivisors

theorem weilReciprocity_bar : WeilReciprocity (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  AlgebraicCurve.weilReciprocity (AlgebraicClosure ℚ) (modularFunctionFieldBar N)

theorem toHom_injective {n : ℕ} [NeZero n]
    (e : DivisorialWeilPairingData (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n) :
    Function.Injective e.toHom :=
  AlgebraicCurve.DivisorialWeilPairingData.toHom_injective_of_divisible
    (fun L' _ _ _ _ _ => AlgebraicCurve.Pic0.exists_zsmul_eq_of_finiteDimensional_ratFunc (AlgebraicClosure ℚ) L') e

theorem nonempty_datum (n : ℕ) [NeZero n] :
    Nonempty (DivisorialWeilPairingData (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n) := by
  haveI := isCurveOver_modularFunctionFieldBar N
  exact AlgebraicCurve.Pic0.nonempty_divisorialWeilPairingData (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
    (exists_transcendental_finiteDimensional_modularFunctionFieldBar N) n

end Tower

section Hecke

variable (N : ℕ) [NeZero N] {n : ℕ} [NeZero n]

attribute [local instance] hasPrincipalDivisors

theorem B_heckeOperatorBar
    (e : DivisorialWeilPairingData (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n)
    (σ : modularFunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N)
    (hσ : ∀ (a b : ℕ) [NeZero a] [NeZero b], a * b = N →
      ∀ x : modularFunctionFieldBar N,
        (x : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ a jq) →
          ((σ x : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
            = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq))
    (ℓ : Nat.Primes) {x y : JZero N} (hx : n • x = 0) (hy : n • y = 0) :
    B e (SemilinearAut.ofAlgAut σ) (heckeOperatorBar N ℓ x) y =
      B e (SemilinearAut.ofAlgAut σ) x (heckeOperatorBar N ℓ y) := by
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) ℓ.2.ne_zero⟩
  haveI := hasPrincipalDivisors (N * ℓ)
  have hTx : n • heckeOperatorBar N ℓ x = 0 := by rw [← map_nsmul, hx, map_zero]
  have hTy : n • heckeOperatorBar N ℓ y = 0 := by rw [← map_nsmul, hy, map_zero]
  rw [B_eq e _ hTx hy, B_eq e _ hx hTy]
  exact pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar N ℓ n e σ hσ (tor x hx) (tor y hy) _ _ _
    rfl rfl rfl

theorem B_hecke_smul
    (e : DivisorialWeilPairingData (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n)
    (w : SemilinearAut (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hgen : ∀ (ℓ : Nat.Primes) {x y : JZero N}, n • x = 0 → n • y = 0 →
      B e w (heckeOperatorBar N ℓ x) y = B e w x (heckeOperatorBar N ℓ y)) :
    letI := heckeModuleBar N
    ∀ (t : HeckeAlg) (x y : JZero N), n • x = 0 → n • y = 0 → B e w (t • x) y = B e w x (t • y) := by
  letI := heckeModuleBar N
  have hc : HeckeOperatorsCommuteBar N := heckeOperatorsCommuteBar N
  have tors : ∀ (t : HeckeAlg) {x : JZero N}, n • x = 0 → n • (t • x) = 0 := by
    intro t x hx
    rw [← smul_comm t n x, hx, smul_zero]
  intro t
  induction t using MvPolynomial.induction_on with
  | C a =>
    intro x y hx hy
    rw [heckeModuleBar_C_smul, heckeModuleBar_C_smul]

    induction a using Int.induction_on with
    | zero => rw [zero_zsmul, zero_zsmul, B_zero_left e w hy, B_zero_right e w hx]
    | succ k ih =>
      rw [add_zsmul, add_zsmul, one_zsmul, one_zsmul, B_add_left e w (zsmul_tors _ hx) hx hy,
        B_add_right e w hx (zsmul_tors _ hy) hy, ih]
    | pred k ih =>
      have e1 : (-(k : ℤ) - 1) • x = -(k : ℤ) • x + -x := by module
      have e2 : (-(k : ℤ) - 1) • y = -(k : ℤ) • y + -y := by module
      rw [e1, e2, B_add_left e w (zsmul_tors _ hx) (neg_tors hx) hy,
        B_add_right e w hx (zsmul_tors _ hy) (neg_tors hy), B_neg_left e w hx hy, B_neg_right e w hx hy, ih]
  | add p q hp hq =>
    intro x y hx hy
    rw [add_smul, add_smul, B_add_left e w (tors p hx) (tors q hx) hy,
      B_add_right e w hx (tors p hy) (tors q hy), hp x y hx hy, hq x y hx hy]
  | mul_X p ℓ hp =>
    intro x y hx hy
    have hX : ∀ {u v : JZero N}, n • u = 0 → n • v = 0 →
        B e w ((MvPolynomial.X ℓ : HeckeAlg) • u) v = B e w u ((MvPolynomial.X ℓ : HeckeAlg) • v) := by
      intro u v hu hv
      show B e w (heckeGen ℓ • u) v = B e w u (heckeGen ℓ • v)
      rw [heckeModuleBar_heckeGen_smul hc, heckeModuleBar_heckeGen_smul hc]
      exact hgen ℓ hu hv
    rw [mul_smul, mul_smul, hp _ _ (tors _ hx) hy, hX hx (tors _ hy), ← mul_smul, ← mul_smul,
      mul_comm (MvPolynomial.X ℓ) p]

end Hecke

section Assembly

variable (N : ℕ) [NeZero N]

attribute [local instance] ratFuncAlgebra isScalarTower_ratFunc finiteDimensional_ratFunc hasPrincipalDivisors

theorem exists_pairing_of_fricke (n : ℕ) (hn : n ≠ 0)
    (σ : modularFunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N)
    (hσ : ∀ (a b : ℕ) [NeZero a] [NeZero b], a * b = N →
      ∀ x : modularFunctionFieldBar N,
        (x : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ a jq) →
          ((σ x : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
            = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq))
    (hcomm : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero N),
      τ • (SemilinearAut.ofAlgAut σ • x) = SemilinearAut.ofAlgAut σ • (τ • x)) :
    letI := heckeModuleBar N
    ∃ B : JZero N → JZero N → AlgebraicClosure ℚ,
      (∀ x y : JZero N, n • x = 0 → n • y = 0 → B x y ^ n = 1) ∧
      (∀ x x' y : JZero N, n • x = 0 → n • x' = 0 → n • y = 0 → B (x + x') y = B x y * B x' y) ∧
      (∀ x y y' : JZero N, n • x = 0 → n • y = 0 → n • y' = 0 → B x (y + y') = B x y * B x y') ∧
      (∀ x : JZero N, n • x = 0 → (∀ y : JZero N, n • y = 0 → B x y = 1) → x = 0) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x y : JZero N, n • x = 0 → n • y = 0 →
          B (σ • x) (σ • y) = σ (B x y)) ∧
      (∀ t : HeckeAlg, ∀ x y : JZero N, n • x = 0 → n • y = 0 → B (t • x) y = B x (t • y)) := by
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨e⟩ := nonempty_datum N n
  let w := SemilinearAut.ofAlgAut σ
  refine ⟨B e w, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    rw [B_eq e w hx hy]
    exact e.pair_pow_eq_one (weilReciprocity_bar N) _ _
  · intro x x' y hx hx' hy; exact B_add_left e w hx hx' hy
  · intro x y y' hx hy hy'; exact B_add_right e w hx hy hy'
  · intro x hx h
    have h0 := toHom_eq_zero_of_forall e w hx h
    have : tor x hx = 0 := toHom_injective N e (by rw [h0, map_zero])
    exact congrArg Subtype.val this
  · intro τ x y hx hy
    have hcomm' : ∀ Y : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n,
        arithmeticGalois (modularFunctionFieldFull N) τ • (w • Y) =
          w • (arithmeticGalois (modularFunctionFieldFull N) τ • Y) := by
      intro Y
      apply Subtype.ext
      simp only [SemilinearAut.coe_torsion_smul]
      have := hcomm τ (Y : JZero N)
      rwa [galois_smul_pic0_def, galois_smul_pic0_def] at this
    rw [galois_smul_pic0_def, galois_smul_pic0_def, B_smul e w _ hcomm' hx hy, baseAut_arithmeticGalois]
    rfl
  · exact B_hecke_smul N e w (fun ℓ x y hx hy => B_heckeOperatorBar N e σ hσ ℓ hx hy)

theorem exists_pairing (n : ℕ) (hn : n ≠ 0) :
    letI := heckeModuleBar N
    ∃ B : JZero N → JZero N → AlgebraicClosure ℚ,
      (∀ x y : JZero N, n • x = 0 → n • y = 0 → B x y ^ n = 1) ∧
      (∀ x x' y : JZero N, n • x = 0 → n • x' = 0 → n • y = 0 → B (x + x') y = B x y * B x' y) ∧
      (∀ x y y' : JZero N, n • x = 0 → n • y = 0 → n • y' = 0 → B x (y + y') = B x y * B x y') ∧
      (∀ x : JZero N, n • x = 0 → (∀ y : JZero N, n • y = 0 → B x y = 1) → x = 0) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x y : JZero N, n • x = 0 → n • y = 0 →
          B (σ • x) (σ • y) = σ (B x y)) ∧
      (∀ t : HeckeAlg, ∀ x y : JZero N, n • x = 0 → n • y = 0 → B (t • x) y = B x (t • y)) := by
  obtain ⟨σ, hσ⟩ := exists_frickeAlgEquiv_modularFunctionFieldBar N
  exact exists_pairing_of_fricke N n hn σ hσ (fun τ z => galois_smul_ofAlgAut_smul_of_fricke N σ hσ τ z)

end Assembly

end ModularCurve.FrickeTwistedWeilPairing
p2m_reactivate "P2MW.S_ModularCurve_exists_pairing_nsmul_eq_zero_galois_hecke.ModularCurve P2MW.S_ModularCurve_exists_pairing_nsmul_eq_zero_galois_hecke.ModularCurve.FrickeTwistedWeilPairing"
p2m_reactivate "P2MW.S_ModularCurve_exists_pairing_nsmul_eq_zero_galois_hecke.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_pairing_nsmul_eq_zero_galois_hecke.ModularCurve P2MW.S_ModularCurve_exists_pairing_nsmul_eq_zero_galois_hecke.ModularCurve.FrickeTwistedWeilPairing"

theorem solution (N : ℕ) [NeZero N] (n : ℕ) (hn : n ≠ 0) :
    letI := heckeModuleBar N
    ∃ B : JZero N → JZero N → AlgebraicClosure ℚ,
      (∀ x y : JZero N, n • x = 0 → n • y = 0 → B x y ^ n = 1) ∧
      (∀ x x' y : JZero N, n • x = 0 → n • x' = 0 → n • y = 0 → B (x + x') y = B x y * B x' y) ∧
      (∀ x y y' : JZero N, n • x = 0 → n • y = 0 → n • y' = 0 → B x (y + y') = B x y * B x y') ∧
      (∀ x : JZero N, n • x = 0 → (∀ y : JZero N, n • y = 0 → B x y = 1) → x = 0) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x y : JZero N, n • x = 0 → n • y = 0 →
          B (σ • x) (σ • y) = σ (B x y)) ∧
      (∀ t : HeckeAlg, ∀ x y : JZero N, n • x = 0 → n • y = 0 → B (t • x) y = B x (t • y)) :=
  ModularCurve.FrickeTwistedWeilPairing.exists_pairing N n hn

end S_ModularCurve_exists_pairing_nsmul_eq_zero_galois_hecke
end P2MW
export P2MW.S_ModularCurve_exists_pairing_nsmul_eq_zero_galois_hecke (solution)
