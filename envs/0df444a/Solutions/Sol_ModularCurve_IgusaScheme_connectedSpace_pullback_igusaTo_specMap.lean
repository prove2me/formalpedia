-- Prove2me | solution 1 for ModularCurve.IgusaScheme.connectedSpace_pullback_igusaTo_specMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/d575686a-6c58-567b-b5c9-31b0267ae989

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Theorems.Thm_TwoChartCech_Cover_exists_overlap_eq_sub_mem_span_of_H1_torsion_stable
import Theorems.Thm_ModularCurve_IgusaScheme_exists_eq_algebraMap_of_mem_chartAlgFin_of_mem_chartAlgInf
import Theorems.Thm_ModularCurve_IgusaScheme_moduleFinite_chartAlgMid_quotient_range_inclFin_sup_range_inclInf
import Theorems.Thm_ModularCurve_IgusaScheme_nonempty_schemeHomOver_id_igusaTo
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_irreducible_natCast_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"

open scoped TensorProduct

noncomputable section

namespace FibreConnBaseChange

universe u v w

variable {R : Type u} [CommRing R] (𝒰 : TwoChartCech.Cover.{u, v} R)
variable (R' : Type w) [CommRing R'] [Algebra R R']

abbrev bc : TwoChartCech.Cover.{w, max v w} R' where
  A0 := R' ⊗[R] 𝒰.A0
  A1 := R' ⊗[R] 𝒰.A1
  A01 := R' ⊗[R] 𝒰.A01
  ρ0 := Algebra.TensorProduct.map (AlgHom.id R' R') 𝒰.ρ0
  ρ1 := Algebra.TensorProduct.map (AlgHom.id R' R') 𝒰.ρ1

@[scoped simp] theorem bc_ρ0_tmul (r : R') (a : 𝒰.A0) : (bc 𝒰 R').ρ0 (r ⊗ₜ a) = r ⊗ₜ 𝒰.ρ0 a := rfl
@[scoped simp] theorem bc_ρ1_tmul (r : R') (b : 𝒰.A1) : (bc 𝒰 R').ρ1 (r ⊗ₜ b) = r ⊗ₜ 𝒰.ρ1 b := rfl

def ι : R →ₗ[R] (𝒰.A0 × 𝒰.A1) :=
  LinearMap.prod (Algebra.linearMap R 𝒰.A0) (Algebra.linearMap R 𝒰.A1)

def d : (𝒰.A0 × 𝒰.A1) →ₗ[R] 𝒰.A01 :=
  𝒰.ρ0.toLinearMap.coprod (-𝒰.ρ1.toLinearMap)

theorem d_apply (a : 𝒰.A0) (b : 𝒰.A1) : d 𝒰 (a, b) = 𝒰.ρ0 a - 𝒰.ρ1 b := by
  simp [d, sub_eq_add_neg]

theorem ι_apply (r : R) : ι 𝒰 r = (algebraMap R _ r, algebraMap R _ r) := rfl

theorem lTensor_d_eq (z : R' ⊗[R] (𝒰.A0 × 𝒰.A1)) :
    LinearMap.lTensor R' (d 𝒰) z =
      (bc 𝒰 R').ρ0 (TensorProduct.prodRight R R' R' _ _ z).1 -
        (bc 𝒰 R').ρ1 (TensorProduct.prodRight R R' R' _ _ z).2 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r ab =>
    obtain ⟨a, b⟩ := ab
    simp only [LinearMap.lTensor_tmul, d_apply, TensorProduct.prodRight_tmul, TensorProduct.tmul_sub,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  | add x y hx hy =>
    simp only [map_add, hx, hy, Prod.fst_add, Prod.snd_add]
    abel

theorem exists_eq_algebraMap_of_ρ0_eq_ρ1 [Module.Flat R R']
    (hexact : Function.Exact (ι 𝒰) (d 𝒰))
    (x0 : (bc 𝒰 R').A0) (x1 : (bc 𝒰 R').A1)
    (h : (bc 𝒰 R').ρ0 x0 = (bc 𝒰 R').ρ1 x1) :
    ∃ r : R', x0 = algebraMap R' _ r ∧ x1 = algebraMap R' _ r := by
  have hex := Module.Flat.lTensor_exact R' hexact
  let e := TensorProduct.prodRight R R' R' 𝒰.A0 𝒰.A1
  have hz0 : LinearMap.lTensor R' (d 𝒰) (e.symm (x0, x1)) = 0 := by
    rw [lTensor_d_eq, LinearEquiv.apply_symm_apply, h, sub_self]
  obtain ⟨w, hw⟩ := (hex _).mp hz0

  have hw' : w = (TensorProduct.rid R R' w) ⊗ₜ 1 := by
    conv_lhs => rw [← (TensorProduct.rid R R').symm_apply_apply w]
    rfl
  have key : (x0, x1) = e (LinearMap.lTensor R' (ι 𝒰) w) := by
    rw [hw, LinearEquiv.apply_symm_apply]
  rw [hw', LinearMap.lTensor_tmul, ι_apply] at key
  refine ⟨TensorProduct.rid R R' w, ?_, ?_⟩
  · have := congrArg Prod.fst key
    dsimp only at this
    rw [this]
    simp [e, Algebra.TensorProduct.algebraMap_apply]
  · have := congrArg Prod.snd key
    dsimp only at this
    rw [this]
    simp [e, Algebra.TensorProduct.algebraMap_apply]

abbrev W : Submodule R 𝒰.A01 := LinearMap.range 𝒰.ρ0.toLinearMap ⊔ LinearMap.range 𝒰.ρ1.toLinearMap

abbrev Φ : (bc 𝒰 R').A01 →ₗ[R'] R' ⊗[R] (𝒰.A01 ⧸ W 𝒰) := (W 𝒰).mkQ.baseChange R'

theorem range_cechDiff_le_ker_Φ :
    LinearMap.range ((bc 𝒰 R').structureSheaf.cechDiff.restrictScalars R') ≤
      LinearMap.ker (Φ 𝒰 R') := by
  rintro _ ⟨⟨y0, y1⟩, rfl⟩
  rw [LinearMap.mem_ker, LinearMap.restrictScalars_apply, TwoChartCech.Sections.cechDiff_apply]
  change Φ 𝒰 R' (((1 : ((bc 𝒰 R').A01)ˣ) : (bc 𝒰 R').A01) * (bc 𝒰 R').ρ1 y1 - (bc 𝒰 R').ρ0 y0) = 0
  rw [Units.val_one, one_mul, map_sub]
  have h0 : ∀ y : (bc 𝒰 R').A0, Φ 𝒰 R' ((bc 𝒰 R').ρ0 y) = 0 := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r a =>
      rw [bc_ρ0_tmul, LinearMap.baseChange_tmul, Submodule.mkQ_apply]
      have : (Submodule.Quotient.mk (𝒰.ρ0 a) : 𝒰.A01 ⧸ W 𝒰) = 0 :=
        (Submodule.Quotient.mk_eq_zero (W 𝒰)).mpr (Submodule.mem_sup_left (LinearMap.mem_range_self _ a))
      rw [this, TensorProduct.tmul_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  have h1 : ∀ y : (bc 𝒰 R').A1, Φ 𝒰 R' ((bc 𝒰 R').ρ1 y) = 0 := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r a =>
      rw [bc_ρ1_tmul, LinearMap.baseChange_tmul, Submodule.mkQ_apply]
      have : (Submodule.Quotient.mk (𝒰.ρ1 a) : 𝒰.A01 ⧸ W 𝒰) = 0 :=
        (Submodule.Quotient.mk_eq_zero (W 𝒰)).mpr (Submodule.mem_sup_right (LinearMap.mem_range_self _ a))
      rw [this, TensorProduct.tmul_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  rw [h0, h1, sub_self]

theorem lTensor_subtype_mem_range (w : R' ⊗[R] ↥(W 𝒰)) :
    LinearMap.lTensor R' (W 𝒰).subtype w ∈
      LinearMap.range ((bc 𝒰 R').structureSheaf.cechDiff.restrictScalars R') := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul r v =>
    obtain ⟨v, hv⟩ := v
    rw [LinearMap.lTensor_tmul, Submodule.subtype_apply]
    obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨a, rfl⟩ := ha'
    obtain ⟨b, rfl⟩ := hb'
    rw [TensorProduct.tmul_add]
    refine Submodule.add_mem _ ⟨(-(r ⊗ₜ a), 0), ?_⟩ ⟨(0, r ⊗ₜ b), ?_⟩
    · rw [LinearMap.restrictScalars_apply, TwoChartCech.Sections.cechDiff_apply]
      change ((1 : ((bc 𝒰 R').A01)ˣ) : (bc 𝒰 R').A01) * (bc 𝒰 R').ρ1 0 - (bc 𝒰 R').ρ0 (-(r ⊗ₜ a)) = _
      rw [map_zero, mul_zero, map_neg, bc_ρ0_tmul, zero_sub, neg_neg]
      rfl
    · rw [LinearMap.restrictScalars_apply, TwoChartCech.Sections.cechDiff_apply]
      change ((1 : ((bc 𝒰 R').A01)ˣ) : (bc 𝒰 R').A01) * (bc 𝒰 R').ρ1 (r ⊗ₜ b) - (bc 𝒰 R').ρ0 0 = _
      rw [map_zero, sub_zero, Units.val_one, one_mul, bc_ρ1_tmul]
      rfl
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

theorem ker_Φ_le_range_cechDiff :
    LinearMap.ker (Φ 𝒰 R') ≤
      LinearMap.range ((bc 𝒰 R').structureSheaf.cechDiff.restrictScalars R') := by
  intro z hz
  have hex := lTensor_exact R' (LinearMap.exact_subtype_mkQ (W 𝒰)) (Submodule.mkQ_surjective _)
  have hz' : LinearMap.lTensor R' (W 𝒰).mkQ z = 0 := by
    rw [← LinearMap.baseChange_eq_ltensor]; exact hz
  obtain ⟨w, rfl⟩ := (hex z).mp hz'
  exact lTensor_subtype_mem_range 𝒰 R' w

theorem exists_ker_pow_smul_stable {M : Type*} [AddCommGroup M] [Module R M] [IsNoetherian R M] (p : R) :
    ∃ n, ∀ m, n ≤ m → LinearMap.ker (LinearMap.lsmul R M (p ^ n)) = LinearMap.ker (LinearMap.lsmul R M (p ^ m)) := by
  let f : ℕ →o Submodule R M :=
    { toFun := fun k => LinearMap.ker (LinearMap.lsmul R M (p ^ k))
      monotone' := fun k m hkm x hx => by
        rw [LinearMap.mem_ker, LinearMap.lsmul_apply] at hx ⊢
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
        rw [add_comm, pow_add, mul_smul, hx, smul_zero] }
  obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian.mpr ‹_›) f
  exact ⟨n, hn⟩

theorem lTensor_lsmul_apply {M : Type*} [AddCommGroup M] [Module R M] (q : R) (z : R' ⊗[R] M) :
    LinearMap.lTensor R' (LinearMap.lsmul R M q) z = q • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r m => rw [LinearMap.lTensor_tmul, LinearMap.lsmul_apply, TensorProduct.tmul_smul]
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

theorem lTensor_subtype_ker_smul_eq_zero {M : Type*} [AddCommGroup M] [Module R M] (p : R) (n : ℕ)
    (hn : LinearMap.ker (LinearMap.lsmul R M (p ^ n)) = LinearMap.ker (LinearMap.lsmul R M (p ^ (n + 1))))
    (w : R' ⊗[R] ↥(LinearMap.ker (LinearMap.lsmul R M (p ^ (n + 1))))) :
    p ^ n • LinearMap.lTensor R' (LinearMap.ker (LinearMap.lsmul R M (p ^ (n + 1)))).subtype w = 0 := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul r m =>
    obtain ⟨m, hm⟩ := m
    rw [← hn] at hm
    rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, ← TensorProduct.tmul_smul]
    change r ⊗ₜ[R] (p ^ n • m) = 0
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply] at hm
    rw [hm, TensorProduct.tmul_zero]
  | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]

theorem pow_smul_eq_zero_of_pow_succ_smul_eq_zero [Module.Flat R R']
    {M : Type*} [AddCommGroup M] [Module R M] (p : R) (n : ℕ)
    (hn : LinearMap.ker (LinearMap.lsmul R M (p ^ n)) = LinearMap.ker (LinearMap.lsmul R M (p ^ (n + 1))))
    (z : R' ⊗[R] M) (hz : (algebraMap R R' p) ^ (n + 1) • z = 0) :
    (algebraMap R R' p) ^ n • z = 0 := by
  have hex := Module.Flat.lTensor_exact R'
    (LinearMap.exact_subtype_ker_map (LinearMap.lsmul R M (p ^ (n + 1))))
  have hz' : LinearMap.lTensor R' (LinearMap.lsmul R M (p ^ (n + 1))) z = 0 := by
    rw [lTensor_lsmul_apply, ← algebraMap_smul (A := R'), map_pow]
    exact hz
  obtain ⟨w, rfl⟩ := (hex z).mp hz'
  rw [← map_pow, algebraMap_smul]
  exact lTensor_subtype_ker_smul_eq_zero R' p n hn w

theorem exists_torsion_H1_stable [Module.Flat R R'] [IsNoetherian R (𝒰.A01 ⧸ W 𝒰)] (p : R) :
    ∃ n, ∀ x : (bc 𝒰 R').structureSheaf.H1,
      (algebraMap R R' p) ^ (n + 1) • x = 0 → (algebraMap R R' p) ^ n • x = 0 := by
  obtain ⟨n, hn⟩ := exists_ker_pow_smul_stable (M := 𝒰.A01 ⧸ W 𝒰) p
  refine ⟨n, fun x hx => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx ⊢

  have hx' : (algebraMap R R' p) ^ (n + 1) • x ∈
      LinearMap.range ((bc 𝒰 R').structureSheaf.cechDiff.restrictScalars R') := by
    obtain ⟨y, hy⟩ := hx; exact ⟨y, hy⟩
  have hker := range_cechDiff_le_ker_Φ 𝒰 R' hx'
  rw [LinearMap.mem_ker, map_smul] at hker
  have h2 := pow_smul_eq_zero_of_pow_succ_smul_eq_zero R' p n (hn (n + 1) (Nat.le_succ n)) _ hker
  rw [← map_smul, ← LinearMap.mem_ker] at h2
  obtain ⟨y, hy⟩ := ker_Φ_le_range_cechDiff 𝒰 R' h2
  exact ⟨y, hy⟩

end FibreConnBaseChange
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnBaseChange"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnBaseChange"

open scoped TensorProduct

noncomputable section

namespace FibreConnReduction

universe u v w w'

variable {R : Type u} [CommRing R]
variable {R' : Type w} [CommRing R'] [Algebra R R']
variable {L : Type w'} [CommRing L] [Algebra R L]
variable (π : R' →ₐ[R] L) (ϖ : R')

def θ (A : Type v) [CommRing A] [Algebra R A] : R' ⊗[R] A →ₐ[R] A ⊗[R] L :=
  (Algebra.TensorProduct.comm R L A).toAlgHom.comp (Algebra.TensorProduct.map π (AlgHom.id R A))

variable {A : Type v} [CommRing A] [Algebra R A]
variable {B : Type v} [CommRing B] [Algebra R B]

@[scoped simp] theorem θ_tmul (r : R') (a : A) : θ π A (r ⊗ₜ a) = a ⊗ₜ π r := by
  simp [θ]

theorem θ_surjective (hπ : Function.Surjective π) : Function.Surjective (θ π A) := by
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a l =>
    obtain ⟨r, rfl⟩ := hπ l
    exact ⟨r ⊗ₜ a, θ_tmul π r a⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩

theorem θ_map (f : A →ₐ[R] B) (x : R' ⊗[R] A) :
    θ π B (Algebra.TensorProduct.map (AlgHom.id R' R') f x) =
      Algebra.TensorProduct.map f (AlgHom.id R L) (θ π A x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r a => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem θ_algebraMap (r : R') : θ π A (algebraMap R' (R' ⊗[R] A) r) = 1 ⊗ₜ π r := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply, θ_tmul]

theorem θ_eq_zero_of_mem (hϖ : π ϖ = 0) (x : R' ⊗[R] A)
    (hx : x ∈ Ideal.span {algebraMap R' (R' ⊗[R] A) ϖ}) : θ π A x = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  rw [map_mul, θ_algebraMap, hϖ, TensorProduct.tmul_zero, mul_zero]

theorem mem_of_θ_eq_zero (hπ : Function.Surjective π) (hker : ∀ r : R', π r = 0 → r ∈ Ideal.span {ϖ})
    (x : R' ⊗[R] A) (hx : θ π A x = 0) : x ∈ Ideal.span {algebraMap R' (R' ⊗[R] A) ϖ} := by

  have hex := rTensor_exact A (LinearMap.exact_subtype_ker_map π.toLinearMap)
    (fun l => hπ l)
  have hx' : LinearMap.rTensor A π.toLinearMap x = 0 := by
    have hcomm : Function.Injective (Algebra.TensorProduct.comm R L A) := (Algebra.TensorProduct.comm R L A).injective
    apply hcomm
    rw [map_zero]
    have : ∀ z : R' ⊗[R] A, Algebra.TensorProduct.comm R L A (LinearMap.rTensor A π.toLinearMap z) = θ π A z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul r a => simp
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [this, hx]
  obtain ⟨w, rfl⟩ := (hex x).mp hx'
  clear hx hx'
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Ideal.zero_mem _
  | tmul k a =>
    obtain ⟨k, hk⟩ := k
    have hk' : k ∈ Ideal.span {ϖ} := hker k (by simpa using hk)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hk'
    rw [LinearMap.rTensor_tmul, Submodule.subtype_apply]
    change (c * ϖ) ⊗ₜ[R] a ∈ _
    have : (c * ϖ) ⊗ₜ[R] a = (c ⊗ₜ a) * algebraMap R' (R' ⊗[R] A) ϖ := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  | add x y hx hy =>
    rw [map_add]
    exact Ideal.add_mem _ hx hy

end FibreConnReduction
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnBaseChange P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnReduction"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnBaseChange P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnReduction"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

noncomputable section

namespace FibreConnGeometry

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
variable (L : Type u) [CommRing L] [Algebra R L]

abbrev XL : Scheme.{u} := pullback f (Scheme.TwoAffineOpenCover.specMap R L)

section chart

variable {B : Type u} [CommRing B] [Algebra R B]

def gChart (h : Spec (.of B) ⟶ X) (hh : h ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    Spec (.of (B ⊗[R] L)) ⟶ XL f L :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := B) (B := L))) ≫ h)
    (Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
      (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := L)))))
    (by
      rw [Category.assoc, hh, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp]
      congr 2
      ext r
      change algebraMap R B r ⊗ₜ[R] (1 : L) = (1 : B) ⊗ₜ[R] algebraMap R L r
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul])

@[reassoc]
theorem gChart_fst (h : Spec (.of B) ⟶ X) (hh : h ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    gChart f L h hh ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := B) (B := L))) ≫ h :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem gChart_snd (h : Spec (.of B) ⟶ X) (hh : h ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    gChart f L h hh ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := L)))) :=
  pullback.lift_snd _ _ _

theorem mem_range_gChart (h : Spec (.of B) ⟶ X) (hh : h ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (z : XL f L) (hz : (pullback.fst _ _ : XL f L ⟶ _) z ∈ Set.range h) :
    z ∈ Set.range (gChart f L h hh) := by
  let k : pullback (h ≫ f) (Scheme.TwoAffineOpenCover.specMap R L) ⟶ Spec (.of (B ⊗[R] L)) :=
    (pullback.congrHom hh rfl).hom ≫ (pullbackSpecIso R B L).hom
  have hfac : pullback.map (h ≫ f) (Scheme.TwoAffineOpenCover.specMap R L)
      f (Scheme.TwoAffineOpenCover.specMap R L) h (𝟙 _) (𝟙 _)
      (by simp) (by simp) = k ≫ gChart f L h hh := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, gChart_fst]
      simp only [k, Category.assoc]
      rw [pullbackSpecIso_hom_fst_assoc, pullback.congrHom_hom, pullback.lift_fst_assoc, Category.comp_id]
    · rw [pullback.lift_snd, Category.assoc, gChart_snd]
      simp only [k, Category.assoc]
      rw [pullbackSpecIso_hom_snd, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
  have hrange := Scheme.Pullback.range_map (h ≫ f) (Scheme.TwoAffineOpenCover.specMap R L)
    f (Scheme.TwoAffineOpenCover.specMap R L) h (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hz' : z ∈ Set.range (pullback.map (h ≫ f) (Scheme.TwoAffineOpenCover.specMap R L)
      f (Scheme.TwoAffineOpenCover.specMap R L) h (𝟙 _) (𝟙 _) (by simp) (by simp)) := by
    rw [hrange]
    refine ⟨hz, ?_⟩
    simp
  rw [hfac] at hz'
  obtain ⟨t, rfl⟩ := hz'
  exact ⟨k t, rfl⟩

theorem exists_idempotent_preimage_eq {B' : Type u} [CommRing B'] (g : Spec (.of B') ⟶ XL f L)
    (C : Set (XL f L)) (hC : IsClopen C) :
    ∃ e : B', IsIdempotentElem e ∧ (g ⁻¹' C : Set (PrimeSpectrum B')) = PrimeSpectrum.basicOpen e := by
  have hS : IsClopen (g ⁻¹' C : Set (PrimeSpectrum B')) := hC.preimage g.continuous
  exact PrimeSpectrum.isClopen_iff.mp hS

omit [Algebra R L] in

theorem preimage_basicOpen {B' B'' : Type u} [CommRing B'] [CommRing B''] (φ : B' →+* B'') (e : B') :
    (Spec.map (CommRingCat.ofHom φ) ⁻¹' (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum B')) :
      Set (PrimeSpectrum B'')) = PrimeSpectrum.basicOpen (φ e) := by
  have := congrArg SetLike.coe (PrimeSpectrum.comap_basicOpen φ e)
  rw [TopologicalSpace.Opens.coe_comap] at this
  exact this

omit [Algebra R L] in

theorem idempotent_eq_of_basicOpen_eq {B' : Type u} [CommRing B'] {e e' : B'} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e')
    (h : (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum B')) = PrimeSpectrum.basicOpen e') : e = e' := by
  have h' : PrimeSpectrum.basicOpen e = PrimeSpectrum.basicOpen e' := SetLike.coe_injective h
  have h1 : e ∈ (Ideal.span {e'}).radical := (PrimeSpectrum.basicOpen_le_basicOpen_iff e e').mp h'.le
  have h2 : e' ∈ (Ideal.span {e}).radical := (PrimeSpectrum.basicOpen_le_basicOpen_iff e' e).mp h'.ge
  have he_mem : e ∈ Ideal.span {e'} := by
    obtain ⟨n, hn⟩ := h1
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [pow_zero] at hn
      simpa using Ideal.mul_mem_left _ e hn
    · rwa [← Nat.sub_add_cancel hn0, IsIdempotentElem.pow_succ_eq (n - 1) he] at hn
  have he'_mem : e' ∈ Ideal.span {e} := by
    obtain ⟨m, hm⟩ := h2
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · rw [pow_zero] at hm
      simpa using Ideal.mul_mem_left _ e' hm
    · rwa [← Nat.sub_add_cancel hm0, IsIdempotentElem.pow_succ_eq (m - 1) he'] at hm
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp he_mem
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp he'_mem
  have h3 : e * e' = e := by
    calc e * e' = a * e' * e' := by rw [ha]
      _ = a * (e' * e') := by ring
      _ = e := by rw [he'.eq, ha]
  have h4 : e' * e = e' := by
    calc e' * e = b * e * e := by rw [hb]
      _ = b * (e * e) := by ring
      _ = e' := by rw [he.eq, hb]
  rw [← h3, mul_comm, h4]

end chart
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnBaseChange P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnReduction"

variable {B0 B1 B01 : Type u} [CommRing B0] [Algebra R B0] [CommRing B1] [Algebra R B1]
  [CommRing B01] [Algebra R B01] (ρ0 : B0 →ₐ[R] B01) (ρ1 : B1 →ₐ[R] B01)
  (h0 : Spec (.of B0) ⟶ X) (h1 : Spec (.of B1) ⟶ X)
  (hh0 : h0 ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B0)))
  (hh1 : h1 ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B1)))

abbrev τ0 : B0 ⊗[R] L →ₐ[R] B01 ⊗[R] L := Algebra.TensorProduct.map ρ0 (AlgHom.id R L)
abbrev τ1 : B1 ⊗[R] L →ₐ[R] B01 ⊗[R] L := Algebra.TensorProduct.map ρ1 (AlgHom.id R L)

theorem compat
    (hglue : Spec.map (CommRingCat.ofHom ρ0.toRingHom) ≫ h0 = Spec.map (CommRingCat.ofHom ρ1.toRingHom) ≫ h1) :
    Spec.map (CommRingCat.ofHom (τ0 L ρ0).toRingHom) ≫ gChart f L h0 hh0 =
      Spec.map (CommRingCat.ofHom (τ1 L ρ1).toRingHom) ≫ gChart f L h1 hh1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, gChart_fst, gChart_fst, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    have e0 : (τ0 L ρ0).toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := B0) (B := L)) =
        (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := B01) (B := L)).comp ρ0.toRingHom := by
      ext a; rfl
    have e1 : (τ1 L ρ1).toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := B1) (B := L)) =
        (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := B01) (B := L)).comp ρ1.toRingHom := by
      ext a; rfl
    rw [e0, e1, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp_assoc, Spec.map_comp_assoc,
      hglue]
  · rw [Category.assoc, Category.assoc, gChart_snd, gChart_snd, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext l
    simp [Algebra.TensorProduct.map_tmul]

include hh0 hh1 in

theorem connectedSpace_of [Nonempty (XL f L)]
    (hglue : Spec.map (CommRingCat.ofHom ρ0.toRingHom) ≫ h0 = Spec.map (CommRingCat.ofHom ρ1.toRingHom) ≫ h1)
    (hcov : ∀ x : X, x ∈ Set.range h0 ∨ x ∈ Set.range h1)
    (H : ∀ (e0 : B0 ⊗[R] L) (e1 : B1 ⊗[R] L),
      IsIdempotentElem e0 → IsIdempotentElem e1 → τ0 L ρ0 e0 = τ1 L ρ1 e1 →
      (e0 = 0 ∧ e1 = 0) ∨ (e0 = 1 ∧ e1 = 1)) :
    ConnectedSpace (XL f L) := by
  have cover : ∀ z : XL f L, z ∈ Set.range (gChart f L h0 hh0) ∨ z ∈ Set.range (gChart f L h1 hh1) := by
    intro z
    rcases hcov ((pullback.fst _ _ : XL f L ⟶ _) z) with h | h
    · exact Or.inl (mem_range_gChart f L _ _ z h)
    · exact Or.inr (mem_range_gChart f L _ _ z h)
  rw [connectedSpace_iff_clopen]
  refine ⟨inferInstance, fun C hC => ?_⟩
  obtain ⟨e0, he0, hC0⟩ := exists_idempotent_preimage_eq f L (gChart f L h0 hh0) C hC
  obtain ⟨e1, he1, hC1⟩ := exists_idempotent_preimage_eq f L (gChart f L h1 hh1) C hC

  have hc := compat f L ρ0 ρ1 h0 h1 hh0 hh1 hglue
  have hov : (PrimeSpectrum.basicOpen (τ0 L ρ0 e0) : Set (PrimeSpectrum (B01 ⊗[R] L))) =
      PrimeSpectrum.basicOpen (τ1 L ρ1 e1) := by
    have p0 := preimage_basicOpen (τ0 L ρ0).toRingHom e0
    have p1 := preimage_basicOpen (τ1 L ρ1).toRingHom e1
    rw [Set.ext_iff] at p0 p1 hC0 hC1 ⊢
    intro t
    refine (p0 t).symm.trans (Iff.trans ?_ (p1 t))
    refine (hC0 _).symm.trans (Iff.trans ?_ (hC1 _))
    rw [Set.mem_preimage, Set.mem_preimage, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hc]
  have hτ : τ0 L ρ0 e0 = τ1 L ρ1 e1 :=
    idempotent_eq_of_basicOpen_eq (he0.map _) (he1.map _) hov
  rcases H e0 e1 he0 he1 hτ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    rcases cover z with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · have : t ∈ ((gChart f L h0 hh0) ⁻¹' C : Set (PrimeSpectrum _)) := hz
      rw [hC0, PrimeSpectrum.basicOpen_zero] at this
      exact this
    · have : t ∈ ((gChart f L h1 hh1) ⁻¹' C : Set (PrimeSpectrum _)) := hz
      rw [hC1, PrimeSpectrum.basicOpen_zero] at this
      exact this
  · right
    rw [Set.eq_univ_iff_forall]
    intro z
    rcases cover z with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · have : t ∈ ((gChart f L h0 hh0) ⁻¹' C : Set (PrimeSpectrum _)) := by
        rw [hC0, PrimeSpectrum.basicOpen_one]; trivial
      exact this
    · have : t ∈ ((gChart f L h1 hh1) ⁻¹' C : Set (PrimeSpectrum _)) := by
        rw [hC1, PrimeSpectrum.basicOpen_one]; trivial
      exact this

end FibreConnGeometry
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnBaseChange P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnReduction"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnBaseChange P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnReduction"

noncomputable section

namespace FibreConnCore

open scoped TensorProduct
open FibreConnBaseChange FibreConnReduction

universe u v w

variable {R : Type u} [CommRing R] (𝒰 : TwoChartCech.Cover.{u, v} R)
variable (R' : Type w) [CommRing R'] [Algebra R R'] [Module.Flat R R']
variable {L : Type w} [CommRing L] [Algebra R L]
variable (π : R' →ₐ[R] L) (ϖ : R')

theorem exists_eq_one_tmul (hπ : Function.Surjective π) (hϖ : π ϖ = 0)
    (hker : ∀ r : R', π r = 0 → r ∈ Ideal.span {ϖ}) (n : ℕ)
    (htors : ∀ x : (bc 𝒰 R').structureSheaf.H1, ϖ ^ (n + 1) • x = 0 → ϖ ^ n • x = 0)
    (hexact : Function.Exact (ι 𝒰) (d 𝒰))
    (e0 : 𝒰.A0 ⊗[R] L) (e1 : 𝒰.A1 ⊗[R] L) (he0 : IsIdempotentElem e0) (he1 : IsIdempotentElem e1)
    (hcompat : Algebra.TensorProduct.map 𝒰.ρ0 (AlgHom.id R L) e0 =
      Algebra.TensorProduct.map 𝒰.ρ1 (AlgHom.id R L) e1) :
    ∃ lam : L, e0 = 1 ⊗ₜ lam ∧ e1 = 1 ⊗ₜ lam := by

  obtain ⟨c0, hc0⟩ := θ_surjective π hπ e0
  obtain ⟨c1, hc1⟩ := θ_surjective π hπ e1
  have h0 : c0 * c0 - c0 ∈ Ideal.span {algebraMap R' (bc 𝒰 R').A0 ϖ} := by
    refine mem_of_θ_eq_zero π ϖ hπ hker _ ?_
    rw [map_sub, map_mul, hc0, he0.eq, sub_self]
  have h1 : c1 * c1 - c1 ∈ Ideal.span {algebraMap R' (bc 𝒰 R').A1 ϖ} := by
    refine mem_of_θ_eq_zero π ϖ hπ hker _ ?_
    rw [map_sub, map_mul, hc1, he1.eq, sub_self]
  have h01 : (bc 𝒰 R').ρ0 c0 - (bc 𝒰 R').ρ1 c1 ∈ Ideal.span {algebraMap R' (bc 𝒰 R').A01 ϖ} := by
    refine mem_of_θ_eq_zero π ϖ hπ hker _ ?_
    rw [map_sub]
    change θ π 𝒰.A01 (Algebra.TensorProduct.map (AlgHom.id R' R') 𝒰.ρ0 c0) -
      θ π 𝒰.A01 (Algebra.TensorProduct.map (AlgHom.id R' R') 𝒰.ρ1 c1) = 0
    rw [θ_map, θ_map, hc0, hc1, hcompat, sub_self]
  obtain ⟨a0, a1, hglue, ha0, ha1⟩ :=
    (bc 𝒰 R').exists_overlap_eq_sub_mem_span_of_H1_torsion_stable ϖ n htors c0 c1 h0 h1 h01
  obtain ⟨r, hr0, hr1⟩ := exists_eq_algebraMap_of_ρ0_eq_ρ1 𝒰 R' hexact a0 a1 hglue
  refine ⟨π r, ?_, ?_⟩
  · have : θ π 𝒰.A0 (a0 - c0) = 0 := θ_eq_zero_of_mem π ϖ hϖ _ ha0
    rw [map_sub, sub_eq_zero, hc0, hr0] at this
    rw [← this]
    exact θ_algebraMap π r
  · have : θ π 𝒰.A1 (a1 - c1) = 0 := θ_eq_zero_of_mem π ϖ hϖ _ ha1
    rw [map_sub, sub_eq_zero, hc1, hr1] at this
    rw [← this]
    exact θ_algebraMap π r

theorem idempotents_trivial {L : Type w} [Field L] [Algebra R L] (π : R' →ₐ[R] L)
    (hπ : Function.Surjective π) (hϖ : π ϖ = 0)
    (hker : ∀ r : R', π r = 0 → r ∈ Ideal.span {ϖ}) (n : ℕ)
    (htors : ∀ x : (bc 𝒰 R').structureSheaf.H1, ϖ ^ (n + 1) • x = 0 → ϖ ^ n • x = 0)
    (hexact : Function.Exact (ι 𝒰) (d 𝒰))
    (e0 : 𝒰.A0 ⊗[R] L) (e1 : 𝒰.A1 ⊗[R] L) (he0 : IsIdempotentElem e0) (he1 : IsIdempotentElem e1)
    (hcompat : Algebra.TensorProduct.map 𝒰.ρ0 (AlgHom.id R L) e0 =
      Algebra.TensorProduct.map 𝒰.ρ1 (AlgHom.id R L) e1) :
    (e0 = 0 ∧ e1 = 0) ∨ (e0 = 1 ∧ e1 = 1) := by
  obtain ⟨lam, rfl, rfl⟩ := exists_eq_one_tmul 𝒰 R' π ϖ hπ hϖ hker n htors hexact e0 e1 he0 he1 hcompat

  have key : ∀ {A : Type v} [CommRing A] [Algebra R A], IsIdempotentElem ((1 : A) ⊗ₜ[R] lam) →
      Nontrivial (A ⊗[R] L) → lam = 0 ∨ lam = 1 := by
    intro A _ _ hid hnt
    let j : L →+* A ⊗[R] L :=
      RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := L))
    have hj : Function.Injective j := j.injective
    have : lam * lam = lam := by
      apply hj
      change (1 : A) ⊗ₜ[R] (lam * lam) = (1 : A) ⊗ₜ[R] lam
      have := hid.eq
      rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one] at this
    rcases mul_eq_zero.mp (show lam * (lam - 1) = 0 by rw [mul_sub, this, mul_one, sub_self]) with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  by_cases hnt0 : Nontrivial (𝒰.A0 ⊗[R] L)
  · rcases key he0 hnt0 with rfl | rfl
    · left; simp
    · right; exact ⟨rfl, rfl⟩
  · by_cases hnt1 : Nontrivial (𝒰.A1 ⊗[R] L)
    · rcases key he1 hnt1 with rfl | rfl
      · left; simp
      · right; exact ⟨rfl, rfl⟩
    · rw [not_nontrivial_iff_subsingleton] at hnt0 hnt1
      left
      exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

end FibreConnCore
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnBaseChange P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnReduction"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnBaseChange P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnReduction"

noncomputable section

namespace FibreConnWitt

set_option synthInstance.maxHeartbeats 1600000

variable (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)

scoped instance span_int_isPrime : (Ideal.span {(ℓ : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp Fact.out)

scoped instance dvr : IsDiscreteValuationRing ℤℓ := GaloisRep.isDiscreteValuationRing_ratLocalizedAt ℓ Fact.out

private theorem _root_.FibreConnWitt.maximalIdeal_eq : IsLocalRing.maximalIdeal ℤℓ = Ideal.span {((ℓ : ℕ) : ℤℓ)} :=
  (GaloisRep.irreducible_natCast_ratLocalizedAt ℓ Fact.out).maximalIdeal_eq

p2m_export "FibreConnWitt" "maximalIdeal_eq"

theorem injective_of_map_natCast_ne_zero {S : Type*} [CommRing S] [IsDomain S] (φ : ℤℓ →+* S)
    (hℓ : φ ℓ ≠ 0) : Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  have hprime : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hne : RingHom.ker φ ≠ ⊥ := fun h => hr0 (by
    have : r ∈ RingHom.ker φ := hr
    rw [h] at this
    exact this)
  have hmax : (RingHom.ker φ).IsMaximal := hprime.isMaximal hne
  have heq : RingHom.ker φ = IsLocalRing.maximalIdeal ℤℓ := IsLocalRing.eq_maximalIdeal hmax
  have : ((ℓ : ℕ) : ℤℓ) ∈ RingHom.ker φ := by
    rw [heq, maximalIdeal_eq]; exact Ideal.subset_span rfl
  exact hℓ this

theorem flat_of_isDomain {S : Type*} [CommRing S] [IsDomain S] [Algebra ℤℓ S]
    (hℓ : algebraMap ℤℓ S ℓ ≠ 0) : Module.Flat ℤℓ S := by
  have hinj := injective_of_map_natCast_ne_zero ℓ (algebraMap ℤℓ S) hℓ
  haveI : Module.IsTorsionFree ℤℓ S := Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (hinj (by rw [h, map_zero]))
    · exact Or.inr h
  infer_instance

section Witt

variable (L : Type) [Field L] [CharP L ℓ] [PerfectRing L ℓ]

omit [PerfectRing L ℓ] in

theorem natCast_witt_ne_zero (n : ℕ) (hn : n ≠ 0) : (n : WittVector ℓ L) ≠ 0 := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn ℓ (Fact.out : ℓ.Prime).ne_one
  rw [Nat.cast_mul, Nat.cast_pow]
  refine mul_ne_zero (pow_ne_zero _ (WittVector.p_nonzero ℓ L)) ?_
  have hunit : IsUnit (m : WittVector ℓ L) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [← WittVector.constantCoeff_apply, map_natCast]
    intro h
    exact hm ((CharP.cast_eq_zero_iff L ℓ m).mp h)
  exact hunit.ne_zero

def φ : ℤℓ →+* WittVector ℓ L :=
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := ℓ) Fact.out
  IsLocalization.lift (M := (Ideal.span {(ℓ : ℤ)}).primeCompl) (S := ℤℓ) (g := Int.castRingHom (WittVector ℓ L))
    (by
      rintro ⟨y, hy⟩
      apply WittVector.isUnit_of_coeff_zero_ne_zero
      rw [← WittVector.constantCoeff_apply]
      change WittVector.constantCoeff ((y : ℤ) : WittVector ℓ L) ≠ 0
      rw [map_intCast]
      intro h
      apply hy
      change y ∈ Ideal.span {(ℓ : ℤ)}
      rw [Ideal.mem_span_singleton]
      exact (CharP.intCast_eq_zero_iff L ℓ y).mp h)

@[reducible] def wittAlgebra : Algebra ℤℓ (WittVector ℓ L) := (φ ℓ L).toAlgebra

attribute [local instance] wittAlgebra

omit [PerfectRing L ℓ] in
theorem algebraMap_witt_natCast : algebraMap ℤℓ (WittVector ℓ L) ℓ = (ℓ : WittVector ℓ L) := map_natCast _ ℓ

scoped instance flat_witt : Module.Flat ℤℓ (WittVector ℓ L) :=
  flat_of_isDomain ℓ (by rw [algebraMap_witt_natCast]; exact WittVector.p_nonzero ℓ L)

def π [Algebra ℤℓ L] : WittVector ℓ L →ₐ[ℤℓ] L :=
  { WittVector.constantCoeff with
    commutes' := fun r => by
      change WittVector.constantCoeff (algebraMap ℤℓ (WittVector ℓ L) r) = algebraMap ℤℓ L r
      haveI := GaloisRep.isLocalization_ratLocalizedAt (p := ℓ) Fact.out
      have h : (WittVector.constantCoeff.comp (algebraMap ℤℓ (WittVector ℓ L))) = algebraMap ℤℓ L := by
        refine IsLocalization.ringHom_ext (Ideal.span {(ℓ : ℤ)}).primeCompl ?_
        exact RingHom.ext_int _ _
      exact RingHom.congr_fun h r }

omit [PerfectRing L ℓ] in
theorem π_apply [Algebra ℤℓ L] (x : WittVector ℓ L) : π ℓ L x = x.coeff 0 := rfl

omit [PerfectRing L ℓ] in
theorem π_surjective [Algebra ℤℓ L] : Function.Surjective (π ℓ L) := fun l =>
  ⟨WittVector.teichmuller ℓ l, by rw [π_apply, WittVector.teichmuller_coeff_zero]⟩

omit [PerfectRing L ℓ] in
theorem π_natCast [Algebra ℤℓ L] : π ℓ L (ℓ : WittVector ℓ L) = 0 := by
  rw [map_natCast, CharP.cast_eq_zero]

theorem mem_span_of_π_eq_zero [Algebra ℤℓ L] (r : WittVector ℓ L) (hr : π ℓ L r = 0) :
    r ∈ Ideal.span {(ℓ : WittVector ℓ L)} := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact Ideal.zero_mem _
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul r hr0
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exfalso
    rw [pow_zero, one_mul, π_apply] at hr
    exact hb hr
  · rw [← Nat.sub_add_cancel hm, pow_succ, mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))

end Witt
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnBaseChange P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnReduction"

end FibreConnWitt
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnBaseChange P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnReduction P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnWitt"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnBaseChange P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnReduction P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnWitt"

noncomputable section

namespace FibreConnIgusa

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme
open scoped TensorProduct
open FibreConnBaseChange

set_option synthInstance.maxHeartbeats 1600000

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)
set_option quotPrecheck false in
local notation "F" => ↥(modularFunctionFieldFull N)

abbrev cov : TwoChartCech.Cover.{0, 0} ℤℓ where
  A0 := ↥(chartAlgFin N ℓ)
  A1 := ↥(chartAlgInf N ℓ)
  A01 := ↥(chartAlgMid N ℓ)
  ρ0 := inclFin N ℓ
  ρ1 := inclInf N ℓ

theorem exact_cov : Function.Exact (ι (cov N ℓ)) (d (cov N ℓ)) := by
  intro ab
  obtain ⟨a, b⟩ := ab
  constructor
  · intro h
    have h' : inclFin N ℓ a = inclInf N ℓ b := by
      have h2 := d_apply (cov N ℓ) a b
      rw [h] at h2
      exact (sub_eq_zero.mp h2.symm)
    have hab : (a : F) = (b : F) := by
      have := congrArg (fun z : ↥(chartAlgMid N ℓ) => (z : F)) h'
      rw [coe_chartIncl, coe_chartIncl] at this
      exact this
    obtain ⟨r, hr⟩ := exists_eq_algebraMap_of_mem_chartAlgFin_of_mem_chartAlgInf N ℓ (a : F) a.2 (hab ▸ b.2)
    refine ⟨r, ?_⟩
    rw [ι_apply]
    have hrF : algebraMap ℤℓ F r = algebraMap ℚ F (r : ℚ) := IsScalarTower.algebraMap_apply ℤℓ ℚ F r
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change ((algebraMap ℤℓ ↥(chartAlgFin N ℓ) r : ↥(chartAlgFin N ℓ)) : F) = a
      rw [Subalgebra.coe_algebraMap, hrF, ← hr]
    · change ((algebraMap ℤℓ ↥(chartAlgInf N ℓ) r : ↥(chartAlgInf N ℓ)) : F) = b
      rw [Subalgebra.coe_algebraMap, hrF, ← hr, hab]
  · rintro ⟨r, hr⟩
    rw [← hr, ι_apply, d_apply]
    change inclFin N ℓ (algebraMap ℤℓ _ r) - inclInf N ℓ (algebraMap ℤℓ _ r) = 0
    rw [AlgHom.commutes, AlgHom.commutes, sub_self]

scoped instance isNoetherian_H1 : IsNoetherian ℤℓ ((cov N ℓ).A01 ⧸ W (cov N ℓ)) := by
  haveI : IsNoetherianRing ℤℓ := inferInstance
  haveI : Module.Finite ℤℓ ((cov N ℓ).A01 ⧸ W (cov N ℓ)) :=
    moduleFinite_chartAlgMid_quotient_range_inclFin_sup_range_inclInf N ℓ
  infer_instance

scoped instance nonempty_XL (L : Type) [Field L] [Algebra ℤℓ L] :
    Nonempty (FibreConnGeometry.XL (igusaTo N ℓ) L) := by
  obtain ⟨⟨s, hs⟩⟩ := nonempty_schemeHomOver_id_igusaTo N ℓ
  let pt : Spec (CommRingCat.of L) ⟶ FibreConnGeometry.XL (igusaTo N ℓ) L :=
    pullback.lift (Scheme.TwoAffineOpenCover.specMap ℤℓ L ≫ s) (𝟙 _)
      (by rw [Category.assoc, hs, Category.comp_id, Category.id_comp])
  obtain ⟨x⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of L)))
  exact ⟨pt x⟩

set_option maxHeartbeats 6400000 in

theorem connectedSpace_of_coeff (L : Type) [Field L] [Algebra ℤℓ L]
    (R' : Type) [CommRing R'] [Algebra ℤℓ R'] [Module.Flat ℤℓ R']
    (π : R' →ₐ[ℤℓ] L) (hπ : Function.Surjective π) (ϖ : R') (hϖ : π ϖ = 0)
    (hker : ∀ r : R', π r = 0 → r ∈ Ideal.span {ϖ}) (n : ℕ)
    (htors : ∀ x : (bc (cov N ℓ) R').structureSheaf.H1, ϖ ^ (n + 1) • x = 0 → ϖ ^ n • x = 0) :
    ConnectedSpace (FibreConnGeometry.XL (igusaTo N ℓ) L) :=
  FibreConnGeometry.connectedSpace_of (igusaTo N ℓ) L (inclFin N ℓ) (inclInf N ℓ) (ιFin N ℓ) (ιInf N ℓ)
    (ιFin_igusaTo N ℓ) (ιInf_igusaTo N ℓ) (glue_condition N ℓ) (mem_range_ιFin_or_mem_range_ιInf N ℓ)
    (fun e0 e1 he0 he1 hcompat =>
      FibreConnCore.idempotents_trivial (cov N ℓ) R' ϖ π hπ hϖ hker n htors (exact_cov N ℓ) e0 e1 he0 he1 hcompat)

end FibreConnIgusa
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnBaseChange P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnReduction P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnWitt P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnIgusa"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnBaseChange P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnReduction P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnWitt P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnIgusa"

noncomputable section

namespace FibreConnFinal

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme
open scoped TensorProduct
open FibreConnBaseChange FibreConnIgusa FibreConnWitt

set_option synthInstance.maxHeartbeats 1600000

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)

theorem connectedSpace_of_perfect (L : Type) [Field L] [Algebra ℤℓ L] [CharP L ℓ] [PerfectRing L ℓ] :
    ConnectedSpace (FibreConnGeometry.XL (igusaTo N ℓ) L) := by
  letI : Algebra ℤℓ (WittVector ℓ L) := FibreConnWitt.wittAlgebra ℓ L
  obtain ⟨n, hn⟩ := exists_torsion_H1_stable (cov N ℓ) (WittVector ℓ L) ((ℓ : ℕ) : ℤℓ)
  refine connectedSpace_of_coeff N ℓ L (WittVector ℓ L) (FibreConnWitt.π ℓ L) (π_surjective ℓ L)
    (ℓ : WittVector ℓ L) (π_natCast ℓ L) (mem_span_of_π_eq_zero ℓ L) n ?_
  intro x hx
  have := hn x
  rw [algebraMap_witt_natCast] at this
  exact this hx

theorem connectedSpace_of_ne_zero (L : Type) [Field L] [Algebra ℤℓ L] (h : algebraMap ℤℓ L ℓ ≠ 0) :
    ConnectedSpace (FibreConnGeometry.XL (igusaTo N ℓ) L) := by
  haveI : Module.Flat ℤℓ L := flat_of_isDomain ℓ h
  refine connectedSpace_of_coeff N ℓ L L (AlgHom.id ℤℓ L) Function.surjective_id 0 rfl
    (fun r hr => ?_) 1 (fun x _ => by rw [pow_one, zero_smul])
  change r = 0 at hr
  rw [hr]; exact Ideal.zero_mem _

theorem connectedSpace_of_extension (L : Type) [Field L] [Algebra ℤℓ L] (L' : Type) [Field L'] [Algebra ℤℓ L']
    [Algebra L L'] [IsScalarTower ℤℓ L L'] [ConnectedSpace (FibreConnGeometry.XL (igusaTo N ℓ) L')] :
    ConnectedSpace (FibreConnGeometry.XL (igusaTo N ℓ) L) := by
  let g := Scheme.TwoAffineOpenCover.specMap ℤℓ L
  let g' : Spec (CommRingCat.of L') ⟶ Spec (CommRingCat.of L) := Spec.map (CommRingCat.ofHom (algebraMap L L'))
  have heq : Scheme.TwoAffineOpenCover.specMap ℤℓ L' = g' ≫ g := by
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq ℤℓ L L']
  haveI : Surjective g' := ⟨fun x => by
    obtain ⟨y⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of L')))
    exact ⟨y, Subsingleton.elim _ _⟩⟩
  let e : FibreConnGeometry.XL (igusaTo N ℓ) L' ⟶ FibreConnGeometry.XL (igusaTo N ℓ) L :=
    (pullback.congrHom rfl heq).hom ≫ (pullbackLeftPullbackSndIso (igusaTo N ℓ) g g').inv ≫
      pullback.fst (pullback.snd (igusaTo N ℓ) g) g'
  haveI : Surjective (pullback.fst (pullback.snd (igusaTo N ℓ) g) g') :=
    MorphismProperty.pullback_fst _ _ inferInstance
  haveI : Surjective e := inferInstance
  exact e.surjective.connectedSpace e.continuous

theorem connectedSpace_of_eq_zero (L : Type) [Field L] [Algebra ℤℓ L] (h : algebraMap ℤℓ L ℓ = 0) :
    ConnectedSpace (FibreConnGeometry.XL (igusaTo N ℓ) L) := by
  haveI : CharP L ℓ := (CharP.charP_iff_prime_eq_zero Fact.out).mpr (by rw [← map_natCast (algebraMap ℤℓ L), h])
  let L' := AlgebraicClosure L
  haveI : CharP L' ℓ := charP_of_injective_algebraMap (algebraMap L L').injective ℓ
  haveI : ExpChar L' ℓ := ExpChar.prime Fact.out
  haveI : PerfectRing L' ℓ := PerfectField.toPerfectRing ℓ
  haveI := connectedSpace_of_perfect N ℓ L'
  exact connectedSpace_of_extension N ℓ L L'

end FibreConnFinal
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnBaseChange P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnReduction P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnWitt P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnIgusa"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnBaseChange P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnReduction P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnWitt P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.FibreConnIgusa"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme in
theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type) [Field L] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) L] :
    ConnectedSpace ↥(pullback (igusaTo N ℓ)
      (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt ℓ) L)) := by
  by_cases h : algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) L ℓ = 0
  · exact FibreConnFinal.connectedSpace_of_eq_zero N ℓ L h
  · exact FibreConnFinal.connectedSpace_of_ne_zero N ℓ L h

end S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap (solution)
