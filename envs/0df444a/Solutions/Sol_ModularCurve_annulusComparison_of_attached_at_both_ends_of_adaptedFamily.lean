-- Prove2me | solution 1 for ModularCurve.annulusComparison_of_attached_at_both_ends_of_adaptedFamily
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/c8289ef2-5aad-5a9e-8039-dc4c4ad2e43e

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_AlgebraicCurve_Annulus_sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends
import Theorems.Thm_AlgebraicCurve_prox_eq_neg_log_iSup_sub_of_chart
import Theorems.Thm_AlgebraicCurve_exists_evalVec_eq_smul_mulVec_of_eq_sum_smul
import Theorems.Thm_AlgebraicCurve_prox_smul_smul
import Theorems.Thm_AlgebraicCurve_abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le
import Theorems.Thm_AlgebraicCurve_Annulus_abv_evalAt_sub_eq_abv_param_sub_of_isAttached_both_ends_of_ord_residue_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_annulusComparison_of_attached_at_both_ends_of_adaptedFamily
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.jqNModC_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_annulusComparison_of_attached_at_both_ends_of_adaptedFamily.AlgebraicCurve ModularCurve IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.ord_zero HasPrincipalDivisors Place.evalAt_one prox evalVec Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends prox_eq_neg_log_iSup_sub_of_chart exists_evalVec_eq_smul_mulVec_of_eq_sum_smul prox_smul_smul abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le Annulus.abv_evalAt_sub_eq_abv_param_sub_of_isAttached_both_ends_of_ord_residue_eq_one"
p2m_open "AlgebraicCurve"

open IsLocalRing

section IsometryHelpers

namespace Place p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField ord ord_zero ord_coe_unit ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring IsRational algebraMap_residueField_injective residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt evalAt_one" end Place
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.exists_isUnit_of_ord_eq_zero_G {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    ∃ hm : f ∈ v.toValuationSubring, IsUnit (⟨f, hm⟩ : v.toValuationSubring) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [h, zpow_zero, mul_one] at hu
  subst hu
  exact ⟨(u : v.toValuationSubring).2, u.isUnit⟩

end Place
p2m_export "AlgebraicCurve" "Place.exists_isUnit_of_ord_eq_zero_G"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem_G {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

end Place
p2m_export "AlgebraicCurve" "Place.ord_nonneg_of_mem_G"
p2m_open_scoped "AlgebraicCurve.Place" in

theorem Place.mem_of_ord_nonneg_G {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.evalAt_mul_G {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (mul_mem hf hg), map_mul, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_mul_G"
p2m_open_scoped "AlgebraicCurve.Place" in

theorem Place.evalAt_sub_G {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (sub_mem hf hg), map_sub, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in
private theorem _root_.AlgebraicCurve.Place.evalAt_algebraMap_G {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have h : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [h, ← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
    v.residueInv_algebraMap]

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_algebraMap_G"
p2m_open_scoped "AlgebraicCurve.Place" in

theorem Place.ord_eq_zero_of_evalAt_ne_zero_G {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    v.ord f = 0 := by
  have h0 : 0 ≤ v.ord f := v.ord_nonneg_of_mem_G hf
  by_contra hne
  have hpos : 0 < v.ord f := lt_of_le_of_ne h0 (Ne.symm hne)
  apply h
  have hnu : ¬ IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    intro hu
    obtain ⟨u, hu⟩ := hu
    have : v.ord f = 0 := by
      have := v.ord_coe_unit u
      rwa [hu] at this
    omega
  have hmax : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    (IsLocalRing.mem_maximalIdeal _).2 hnu
  rw [v.evalAt_of_mem hf, (IsLocalRing.residue_eq_zero_iff _).2 hmax, ← map_zero (algebraMap K _),
    v.residueInv_algebraMap]

p2m_open_scoped "AlgebraicCurve.Place" in

theorem Place.ord_pos_of_evalAt_eq_zero_G {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) (h : v.evalAt f = 0) :
    0 < v.ord f := by
  have h0 := v.ord_nonneg_of_mem_G hf
  rcases h0.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero_G hf0 heq.symm
    have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hm⟩ ≠ 0 :=
      (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu
    apply hres
    rw [← v.algebraMap_evalAt hv hm, h, map_zero]

namespace ComponentChart p2m_export "AlgebraicCurve.ComponentChart" "integers algebraMap_mem_iff residue residue_algebraMap ker_residue dom" end ComponentChart
p2m_open_scoped "AlgebraicCurve.ComponentChart" in

theorem ComponentChart.isUnit_of_residue_ne_zero_G
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0) :
    IsUnit (⟨f, hf⟩ : C.integers) := by
  by_contra hnu
  apply hres
  have : (⟨f, hf⟩ : C.integers) ∈ RingHom.ker C.residue := by
    rw [C.ker_residue]; exact (IsLocalRing.mem_maximalIdeal _).2 hnu
  exact this

theorem inv_mem_of_isUnit_G {F : Type*} [Field F] {O : ValuationSubring F} {x : F}
    (hx : x ∈ O) (hu : IsUnit (⟨x, hx⟩ : O)) : x⁻¹ ∈ O := by
  obtain ⟨u, hu⟩ := hu
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : (u : O) = 0 := by rw [hu]; rfl
    exact u.ne_zero this
  have hval : ((u⁻¹ : Oˣ) : O).1 = x⁻¹ := by
    have h1 := congrArg (fun t : O => (t : F)) u.mul_inv
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
    rw [hu] at h1
    exact (eq_inv_of_mul_eq_one_right h1)
  exact hval ▸ ((u⁻¹ : Oˣ) : O).2

p2m_open_scoped "AlgebraicCurve.ComponentChart" in

theorem ComponentChart.residue_inv_G
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (hfi : f⁻¹ ∈ C.integers) : C.residue ⟨f⁻¹, hfi⟩ = (C.residue ⟨f, hf⟩)⁻¹ := by
  have hf0 : f ≠ 0 := by
    rintro rfl; apply hres
    have : (⟨(0 : F), hf⟩ : C.integers) = 0 := rfl
    rw [this, map_zero]
  have h1 : C.residue ⟨f⁻¹, hfi⟩ * C.residue ⟨f, hf⟩ = 1 := by
    rw [← map_mul]
    have : (⟨f⁻¹, hfi⟩ : C.integers) * ⟨f, hf⟩ = 1 := Subtype.ext (inv_mul_cancel₀ hf0)
    rw [this, map_one]
  exact eq_inv_of_mul_eq_one_left h1

namespace ComponentChart
p2m_open_scoped "AlgebraicCurve.ComponentChart" in

private theorem _root_.AlgebraicCurve.ComponentChart.residue_algebraMap_eq_zero_G
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A)
    (h : algebraMap L F a ∈ C.integers) : C.residue ⟨algebraMap L F a, h⟩ = 0 := by
  have e1 : (⟨algebraMap L F a, h⟩ : C.integers) = ⟨algebraMap L F a, (C.algebraMap_mem_iff a).mpr a.2⟩ := rfl
  rw [e1, C.residue_algebraMap a, (IsLocalRing.residue_eq_zero_iff _).2 ha, map_zero]

end ComponentChart
p2m_export "AlgebraicCurve" "ComponentChart.residue_algebraMap_eq_zero_G"

theorem abv_lt_one_of_mem_maximalIdeal_G {L : Type*} [Field L] {A : ValuationSubring L}
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    {m : ↥A} (hm : m ∈ IsLocalRing.maximalIdeal ↥A) : μ (m : L) < 1 := by
  have hle : μ (m : L) ≤ 1 := (hμA _).1 m.2
  refine lt_of_le_of_ne hle fun h1 => ?_
  apply (IsLocalRing.mem_maximalIdeal _).1 hm
  have hm0 : (m : L) ≠ 0 := fun h0 => by rw [h0, map_zero] at h1; exact zero_ne_one h1
  have hinv : (m : L)⁻¹ ∈ A := (hμA _).2 (by rw [map_inv₀, h1, inv_one])
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hm0)⟩

theorem mem_maximalIdeal_of_abv_lt_one_G {L : Type*} [Field L] {A : ValuationSubring L}
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    {x : L} (hx : x ∈ A) (h : μ x < 1) : (⟨x, hx⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨u, hu⟩ := hu
  have hx0 : x ≠ 0 := by
    intro h0
    have : (u : ↥A) = 0 := by rw [hu]; exact Subtype.ext h0
    exact u.ne_zero this
  have hinv : ((u⁻¹ : (↥A)ˣ) : ↥A).1 = x⁻¹ := by
    have h1 := congrArg (fun t : ↥A => (t : L)) u.mul_inv
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
    rw [hu] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hxinv : μ x⁻¹ ≤ 1 := (hμA _).1 (hinv ▸ ((u⁻¹ : (↥A)ˣ) : ↥A).2)
  rw [map_inv₀] at hxinv
  have : 1 < (μ x)⁻¹ := (one_lt_inv₀ (μ.pos hx0)).2 h
  linarith

theorem residue_ne_zero_of_abv_eq_one_G {L : Type*} [Field L] {A : ValuationSubring L}
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    {x : L} (hx : x ∈ A) (h : μ x = 1) : IsLocalRing.residue ↥A ⟨x, hx⟩ ≠ 0 := by
  rw [IsLocalRing.residue_ne_zero_iff_isUnit]
  have hx0 : x ≠ 0 := fun h0 => by rw [h0, map_zero] at h; exact zero_ne_one h
  have hinv : x⁻¹ ∈ A := (hμA _).2 (by rw [map_inv₀, h, inv_one])
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in
private theorem _root_.AlgebraicCurve.Place.evalAt_add_G {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (add_mem hf hg), map_add, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_add_G"
namespace Annulus p2m_export "AlgebraicCurve.Annulus" "IsAttached existsUnique_evalAt_eq modulus modulus_mem dom mem_dom param sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends abv_evalAt_sub_eq_abv_param_sub_of_isAttached_both_ends_of_ord_residue_eq_one" end Annulus
p2m_open_scoped "AlgebraicCurve.Annulus" in

theorem Annulus.exists_mem_dom_abv_evalAt_param_ne_G {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F]
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An : Annulus A F) (hmod0 : (An.modulus : L) ≠ 0) :
    ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, μ (Q₁.evalAt An.param) ≠ μ (Q₂.evalAt An.param) := by
  set π : L := (An.modulus : L) with hπ
  have hμπ0 : 0 < μ π := μ.pos hmod0
  have hμπ1 : μ π < 1 := abv_lt_one_of_mem_maximalIdeal_G μ hμA An.modulus_mem
  obtain ⟨c₂, hc₂⟩ := IsAlgClosed.exists_pow_nat_eq π (by norm_num : 0 < 2)
  obtain ⟨c₃, hc₃⟩ := IsAlgClosed.exists_pow_nat_eq π (by norm_num : 0 < 3)
  have hμc₂ : μ c₂ ^ 2 = μ π := by rw [← map_pow, hc₂]
  have hμc₃ : μ c₃ ^ 3 = μ π := by rw [← map_pow, hc₃]
  have hc₂0 : c₂ ≠ 0 := by rintro rfl; apply hmod0; rw [← hc₂]; norm_num
  have hc₃0 : c₃ ≠ 0 := by rintro rfl; apply hmod0; rw [← hc₃]; norm_num
  have hμc₂1 : μ c₂ < 1 := by
    by_contra h; push Not at h
    have : 1 ≤ μ c₂ ^ 2 := one_le_pow₀ h
    linarith
  have hμc₃1 : μ c₃ < 1 := by
    by_contra h; push Not at h
    have : 1 ≤ μ c₃ ^ 3 := one_le_pow₀ h
    linarith
  have hc₂A : c₂ ∈ A := (hμA _).2 hμc₂1.le
  have hc₃A : c₃ ∈ A := (hμA _).2 hμc₃1.le
  have hc₂𝔪 := mem_maximalIdeal_of_abv_lt_one_G μ hμA hc₂A hμc₂1
  have hc₃𝔪 := mem_maximalIdeal_of_abv_lt_one_G μ hμA hc₃A hμc₃1
  have hc₃sqA : c₃ ^ 2 ∈ A := pow_mem hc₃A 2
  have hc₃sq𝔪 : (⟨c₃ ^ 2, hc₃sqA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    have e1 : (⟨c₃ ^ 2, hc₃sqA⟩ : ↥A) = (⟨c₃, hc₃A⟩ : ↥A) ^ 2 := Subtype.ext (by simp)
    rw [e1]; exact Ideal.pow_mem_of_mem _ hc₃𝔪 2 (by norm_num)
  obtain ⟨Q₂, ⟨hQ₂, hzQ₂⟩, -⟩ := An.existsUnique_evalAt_eq ⟨c₂, hc₂A⟩ hc₂𝔪 hc₂0
    ⟨⟨c₂, hc₂A⟩, hc₂𝔪, by rw [← hπ, ← hc₂]; ring⟩
  obtain ⟨Q₃, ⟨hQ₃, hzQ₃⟩, -⟩ := An.existsUnique_evalAt_eq ⟨c₃, hc₃A⟩ hc₃𝔪 hc₃0
    ⟨⟨c₃ ^ 2, hc₃sqA⟩, hc₃sq𝔪, by rw [← hπ, ← hc₃]; ring⟩
  refine ⟨Q₂, hQ₂, Q₃, hQ₃, ?_⟩
  rw [hzQ₂, hzQ₃]
  show μ c₂ ≠ μ c₃
  intro heq
  have h0 : 0 < μ c₂ := μ.pos hc₂0
  have h23 : μ c₂ ^ 2 = μ c₂ ^ 3 := by rw [hμc₂, ← hμc₃, heq]
  have : μ c₂ ^ 2 * (1 - μ c₂) = 0 := by ring_nf; linarith [h23]
  rcases mul_eq_zero.1 this with h | h
  · exact (pow_pos h0 2).ne' h
  · exact hμc₂1.ne (by linarith)

end IsometryHelpers

end AlgebraicCurve

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem solution (N : ℕ) [NeZero N]
    {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (p : ℕ) (hp : p.Prime)
    (hpN : p ∣ N) (hp2 : ¬ p ^ 2 ∣ N) :
    ∀ (k₀ : ℕ) (t : Fin r → modularFunctionFieldBar N)
      (M Minv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (nexp : Fin r → ℕ) (Bl : ℕ),
    (∀ l : Fin r, (l : ℕ) = 0 → t l = 1) →
    (∀ i, s i = ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (M i j) * t j) →
    Minv * M = 1 → M * Minv = 1 →
    (∀ l : Fin r, (l : ℕ) = 0 → nexp l = 0) → (∀ l : Fin r, 1 ≤ (l : ℕ) → 1 ≤ nexp l) →
    (∀ l, nexp l ≤ k₀) →
    ∃ (Cc : ℝ), ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ {Fbar Fbar' : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
      [Field Fbar'] [Algebra (ResidueField ↥A) Fbar']
      (C : ComponentChart A (modularFunctionFieldBar N) Fbar)
      (C' : ComponentChart A (modularFunctionFieldBar N) Fbar')
      (x : Place (ResidueField ↥A) Fbar) (x' : Place (ResidueField ↥A) Fbar')
      (An An' : Annulus A (modularFunctionFieldBar N)),
    An.IsAttached C x → An'.IsAttached C' x' →
    (An'.dom = An.dom ∧ An'.modulus = An.modulus ∧
      ((An.modulus : AlgebraicClosure ℚ)) ≠ 0 ∧
      An'.param * An.param
        = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((An.modulus : AlgebraicClosure ℚ))) →
    ∀ (πx : AlgebraicClosure ℚ), πx ≠ 0 → (∃ hmem : πx ∈ A, (⟨πx, hmem⟩ : A) ∈ maximalIdeal A) →
    (∃ u : AlgebraicClosure ℚ, u ∈ A ∧ u⁻¹ ∈ A ∧
      ((An.modulus : AlgebraicClosure ℚ)) * u = πx) →
    (∃ a : AlgebraicClosure ℚ, a ∈ A ∧ (p : AlgebraicClosure ℚ) ^ k₀ = πx * a) →
    (∃ b : AlgebraicClosure ℚ, b ∈ A ∧ πx = (p : AlgebraicClosure ℚ) * b) →
    (∃ u : AlgebraicClosure ℚ, u ∈ A ∧ u⁻¹ ∈ A ∧
      ((An.modulus : AlgebraicClosure ℚ)) = (p : AlgebraicClosure ℚ) * u) →
    (∀ i j, (p : AlgebraicClosure ℚ) ^ Bl * M i j ∈ A ∧ (p : AlgebraicClosure ℚ) ^ Bl * Minv i j ∈ A) →
    (∀ l : Fin r, ∃ h : t l ∈ C'.integers,
      C'.residue ⟨t l, h⟩ ≠ 0 ∧ (1 ≤ (l : ℕ) → 1 ≤ x'.ord (C'.residue ⟨t l, h⟩))) →
    (∃ l : Fin r, 1 ≤ (l : ℕ) ∧ ∃ h : t l ∈ C'.integers, x'.ord (C'.residue ⟨t l, h⟩) = 1) →
    (∀ l : Fin r, ∃ h : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        ((p : AlgebraicClosure ℚ) ^ nexp l))⁻¹ * t l ∈ C.integers, C.residue ⟨_, h⟩ ≠ 0) →
    (∀ R ∈ An.dom, ∀ l : Fin r, 1 ≤ (l : ℕ) →
      t l ∈ R.toValuationSubring ∧
        ∃ h : R.evalAt (t l) ∈ A, (⟨R.evalAt (t l), h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A) →
    (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ P ∈ An.dom, ∀ Q ∈ An.dom, P ≠ Q →
        (∃ i j, evalVec s P i * evalVec s Q j ≠ evalVec s P j * evalVec s Q i) →
        |prox μ (evalVec s P) (evalVec s Q)
            + Real.log (μ (P.evalAt An.param - Q.evalAt An.param))|
          ≤ Cc * (-Real.log (μ ((An.modulus : AlgebraicClosure ℚ))))) := by
  intro k₀ t M Minv nexp Bl ht0eq hst hMinvM hMMinv hnexp0 hnexp1 hnexpk
  refine ⟨4 * (Bl : ℝ) + 2, ?_⟩
  intro A hA Fbar Fbar' instF instA instF' instA' C C' x x' An An' hatt hatt' htwoE πx hπx0 hπx𝔪 hassoc hpk hpb hwidth hwin
    hCt hpiv hCfar hsmall μ hμ hμA P hP Q hQ hPQ hnonprop
  classical
  obtain ⟨hdom, hmod, hmod0, htwo⟩ := htwoE
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  have hPL : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p : AlgebraicClosure ℚ) ≠ 0 :=
    (map_ne_zero _).2 hp0
  set π : AlgebraicClosure ℚ := (An.modulus : AlgebraicClosure ℚ) with hπ
  obtain ⟨u, huA, huiA, hπu⟩ := hwidth
  have hu0 : u ≠ 0 := by
    rintro rfl; apply hmod0; rw [hπu, mul_zero]
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0
  have hμu : μ u = 1 := by
    refine le_antisymm ((hμA u).1 huA) ?_
    have h1 : μ u⁻¹ ≤ 1 := (hμA _).1 huiA
    rw [map_inv₀] at h1
    exact (inv_le_one₀ (μ.pos hu0)).1 h1
  have hμπ : μ π = μ (p : AlgebraicClosure ℚ) := by rw [hπu, map_mul, hμu, mul_one]
  have hμπ1 : μ π < 1 := abv_lt_one_of_mem_maximalIdeal_G μ hμA An.modulus_mem
  have hμp1 : μ (p : AlgebraicClosure ℚ) < 1 := hμπ ▸ hμπ1
  have hp𝔪 : (⟨(p : AlgebraicClosure ℚ), hpA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A :=
    mem_maximalIdeal_of_abv_lt_one_G μ hμA hpA hμp1
  have hlam : 0 ≤ -Real.log (μ (p : AlgebraicClosure ℚ)) := by linarith [Real.log_nonpos hμp0.le hμp1.le]
  have hlogp : Real.log (μ (p : AlgebraicClosure ℚ)) < 0 := Real.log_neg hμp0 hμp1
  have hμui : μ u⁻¹ = 1 := by rw [map_inv₀, hμu, inv_one]
  have huires : IsLocalRing.residue ↥A ⟨u⁻¹, huiA⟩ ≠ 0 := residue_ne_zero_of_abv_eq_one_G μ hμA huiA hμui

  set z := An.param with hz
  set z' := An'.param with hz'
  have hdomG : An.dom = An'.dom := hdom.symm
  have hmodG : An.modulus = An'.modulus := hmod.symm
  have hπ' : ((An'.modulus : AlgebraicClosure ℚ)) = π := by rw [hmod]
  have hmod0G : ((An'.modulus : AlgebraicClosure ℚ)) ≠ 0 := by rw [hπ']; exact hmod0
  have htwoG : z * z' = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((An'.modulus : AlgebraicClosure ℚ)) := by
    rw [mul_comm, hz', hz, htwo, hπ']
  have hwideG := Annulus.exists_mem_dom_abv_evalAt_param_ne_G μ hμA An' hmod0G
  obtain ⟨-, hz'C', hz'ord, -⟩ := id hatt'
  have hz'res0 : C'.residue ⟨z', hz'C'⟩ ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hz'ord; exact zero_ne_one hz'ord

  have hdomR : ∀ R ∈ An.dom,
      R.IsRational ∧ z ∈ R.toValuationSubring ∧ z' ∈ R.toValuationSubring ∧
      R.evalAt z' ≠ 0 ∧ R.evalAt z * R.evalAt z' = π ∧ μ π < μ (R.evalAt z') ∧ μ (R.evalAt z') < 1 := by
    intro R hR
    obtain ⟨hrat, hzR, -, -, -⟩ := An.mem_dom R hR
    obtain ⟨-, hz'R, ⟨hz'A, hz'𝔪⟩, hz'R0, m, hm𝔪, hm⟩ := An'.mem_dom R (hdom ▸ hR)
    have hprod : R.evalAt z * R.evalAt z' = π := by
      rw [← R.evalAt_mul_G hrat hzR hz'R, htwoG, R.evalAt_algebraMap_G, hπ']
    refine ⟨hrat, hzR, hz'R, hz'R0, hprod, ?_, abv_lt_one_of_mem_maximalIdeal_G μ hμA hz'𝔪⟩
    rw [← hπ', hm, map_mul]
    have h0 : 0 < μ (R.evalAt z') := μ.pos hz'R0
    have hm1 : μ (m : AlgebraicClosure ℚ) < 1 := abv_lt_one_of_mem_maximalIdeal_G μ hμA hm𝔪
    calc μ (R.evalAt z') * μ (m : AlgebraicClosure ℚ) < μ (R.evalAt z') * 1 := mul_lt_mul_of_pos_left hm1 h0
      _ = μ (R.evalAt z') := mul_one _
  have hinj : ∀ R ∈ An.dom, ∀ R' ∈ An.dom, R.evalAt z' = R'.evalAt z' → R = R' := by
    intro R hR R' hR' hRR'
    obtain ⟨-, -, ⟨haA, ha𝔪⟩, ha0, hm⟩ := An'.mem_dom R' (hdom ▸ hR')
    obtain ⟨P₀, -, huniq⟩ := An'.existsUnique_evalAt_eq ⟨R'.evalAt z', haA⟩ ha𝔪 ha0 hm
    exact (huniq R ⟨hdom ▸ hR, hRR'⟩).trans (huniq R' ⟨hdom ▸ hR', rfl⟩).symm
  obtain ⟨hPrat, hzP, hz'P, hz'P0, hprodP, hμz'P, hμz'P1⟩ := hdomR P hP
  obtain ⟨hQrat, hzQ, hz'Q, hz'Q0, hprodQ, hμz'Q, hμz'Q1⟩ := hdomR Q hQ
  set δ : ℝ := μ (P.evalAt z' - Q.evalAt z') with hδ
  have hδ0 : 0 < δ := by
    rw [hδ]; apply μ.pos
    rw [sub_ne_zero]
    exact fun h => hPQ (hinj P hP Q hQ h)

  obtain ⟨l, hl, hlC', hordl⟩ := hpiv
  have hr : 0 < r := Fin.pos l
  set o : Fin r := ⟨0, hr⟩ with ho
  have hto : t o = 1 := ht0eq o rfl
  have htC' : ∀ i, t i ∈ C'.integers := fun i => (hCt i).fst
  have htres' : ∀ i, C'.residue ⟨t i, htC' i⟩ ≠ 0 := fun i => (hCt i).snd.1
  have hordl' : x'.ord (C'.residue ⟨t l, htC' l⟩) = 1 := hordl
  have htC : ∀ i, (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      ((p : AlgebraicClosure ℚ) ^ nexp i))⁻¹ * t i ∈ C.integers := fun i => (hCfar i).fst
  have htCres : ∀ i, C.residue ⟨_, htC i⟩ ≠ 0 := fun i => (hCfar i).snd
  have ht0 : ∀ i, t i ≠ 0 := by
    intro i h0; apply htres' i
    have : (⟨t i, htC' i⟩ : C'.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hreg : ∀ i, ∀ R ∈ An.dom, t i ∈ R.toValuationSubring ∧ μ (R.evalAt (t i)) ≤ 1 := by
    intro i R hR
    by_cases hi : 1 ≤ (i : ℕ)
    · obtain ⟨hm, hA', -⟩ := hsmall R hR i hi
      exact ⟨hm, (hμA _).1 hA'⟩
    · have hi0 : (i : ℕ) = 0 := by omega
      rw [ht0eq i hi0]
      exact ⟨one_mem _, by rw [Place.evalAt_one, map_one]⟩

  have hpC' : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p : AlgebraicClosure ℚ) ∈ C'.integers :=
    (C'.algebraMap_mem_iff _).2 hpA
  have hpC'res : C'.residue ⟨_, hpC'⟩ = 0 := C'.residue_algebraMap_eq_zero_G ⟨(p : AlgebraicClosure ℚ), hpA⟩ hp𝔪 hpC'
  have hpnA : ∀ n : ℕ, (p : AlgebraicClosure ℚ) ^ n ∈ A := fun n => pow_mem hpA n
  have hpnC : ∀ n : ℕ, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((p : AlgebraicClosure ℚ) ^ n)
      ∈ C.integers := fun n => (C.algebraMap_mem_iff _).2 (hpnA n)
  have hpnCres : ∀ n : ℕ, 1 ≤ n → C.residue ⟨_, hpnC n⟩ = 0 := by
    intro n hn
    apply C.residue_algebraMap_eq_zero_G ⟨(p : AlgebraicClosure ℚ) ^ n, hpnA n⟩ _ (hpnC n)
    have e1 : (⟨(p : AlgebraicClosure ℚ) ^ n, hpnA n⟩ : ↥A) = (⟨(p : AlgebraicClosure ℚ), hpA⟩ : ↥A) ^ n :=
      Subtype.ext (by simp)
    rw [e1]
    exact Ideal.pow_mem_of_mem _ hp𝔪 n hn
  have huiC : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) u⁻¹ ∈ C.integers :=
    (C.algebraMap_mem_iff _).2 huiA
  have huiCres : C.residue ⟨_, huiC⟩ ≠ 0 := by
    have e1 : (⟨_, huiC⟩ : C.integers)
        = ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((⟨u⁻¹, huiA⟩ : ↥A) : AlgebraicClosure ℚ),
            (C.algebraMap_mem_iff _).mpr (⟨u⁻¹, huiA⟩ : ↥A).2⟩ := rfl
    rw [e1, C.residue_algebraMap]
    exact (map_ne_zero_iff _ (algebraMap (IsLocalRing.ResidueField ↥A) _).injective).2 huires

  have hfar : ∀ (g : modularFunctionFieldBar N)
      (hg : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p : AlgebraicClosure ℚ))⁻¹ * g ∈ C.integers),
      C.residue ⟨_, hg⟩ ≠ 0 →
      ∃ hG : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((An'.modulus : AlgebraicClosure ℚ)))⁻¹ * g
          ∈ C.integers, C.residue ⟨_, hG⟩ ≠ 0 := by
    intro g hg hgres
    have key : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((An'.modulus : AlgebraicClosure ℚ)))⁻¹ * g
        = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) u⁻¹
          * ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p : AlgebraicClosure ℚ))⁻¹ * g) := by
      rw [hπ', hπu, map_mul, map_inv₀, mul_inv]; ring
    have hG : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((An'.modulus : AlgebraicClosure ℚ)))⁻¹ * g
        ∈ C.integers := by rw [key]; exact mul_mem huiC hg
    refine ⟨hG, ?_⟩
    have e1 : (⟨_, hG⟩ : C.integers) = ⟨_, huiC⟩ * ⟨_, hg⟩ := Subtype.ext key
    rw [e1, map_mul]; exact mul_ne_zero huiCres hgres

  have hpole_l : ∀ R ∈ An'.dom, 0 ≤ R.ord (t l) := fun R hR => R.ord_nonneg_of_mem_G (hreg l R (hdom ▸ hR)).1
  have hn : 1 ≤ nexp l := hnexp1 l hl
  obtain ⟨D, hD0, hDsupp, hDord, hdeg, hsum⟩ :=
    AlgebraicCurve.Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends μ hμA
      An' An hdomG hmodG hmod0G htwoG C' x' hatt' C x hatt hwideG (t l) (htC' l) (htres' l)
      ((p : AlgebraicClosure ℚ) ^ nexp l) (pow_ne_zero _ hp0) (hpnA _) (htC l) (htCres l) hpole_l
  rw [hordl'] at hdeg
  have hDzero : D = 0 := by
    by_contra hne
    obtain ⟨R, hDR⟩ : ∃ R, D R ≠ 0 := by
      by_contra hall; push Not at hall; exact hne (Finsupp.ext hall)
    have hRdom : R ∈ An'.dom := hDsupp R hDR
    set d : ℤ := D.sum fun _ m => m with hd
    have hDR1 : 1 ≤ D R := lt_of_le_of_ne (hD0 R) (Ne.symm hDR)
    have hlow : (d : ℝ) * Real.log (μ (p : AlgebraicClosure ℚ))
        < D.sum fun Q m => (m : ℝ) * Real.log (μ (Q.evalAt z')) := by
      rw [hd, Finsupp.sum, Finsupp.sum, Int.cast_sum, Finset.sum_mul]
      apply Finset.sum_lt_sum
      · intro Q' hQ'
        have hQ'dom : Q' ∈ An'.dom := hDsupp Q' (Finsupp.mem_support_iff.1 hQ')
        have hDQ : (0 : ℝ) ≤ (D Q' : ℝ) := by exact_mod_cast hD0 Q'
        refine mul_le_mul_of_nonneg_left (Real.log_le_log hμp0 ?_) hDQ
        rw [← hμπ]; exact (hdomR Q' (hdom ▸ hQ'dom)).2.2.2.2.2.1.le
      · refine ⟨R, Finsupp.mem_support_iff.2 hDR, ?_⟩
        have hDRpos : (0 : ℝ) < (D R : ℝ) := by exact_mod_cast hDR1
        refine mul_lt_mul_of_pos_left (Real.log_lt_log hμp0 ?_) hDRpos
        rw [← hμπ]; exact (hdomR R (hdom ▸ hRdom)).2.2.2.2.2.1
    have ha' : x.ord (C.residue ⟨_, htC l⟩) = d - 1 := by rw [hd]; omega
    rw [ha', hπ', hμπ, map_pow, Real.log_pow] at hsum
    have hrhs : (D.sum fun Q m => (m : ℝ) * Real.log (μ (Q.evalAt z')))
        ≤ (d : ℝ) * Real.log (μ (p : AlgebraicClosure ℚ)) := by
      rw [hsum]
      have hn' : (1 : ℝ) ≤ (nexp l : ℝ) := by exact_mod_cast hn
      push_cast; nlinarith
    exact absurd (hlow.trans_le hrhs) (lt_irrefl _)
  rw [hDzero, Finsupp.sum_zero_index] at hdeg hsum
  have ha' : x.ord (C.residue ⟨_, htC l⟩) = -1 := by omega
  rw [ha', hπ', hμπ, map_pow, Real.log_pow] at hsum
  have hn1 : nexp l = 1 := by
    have h1 : ((nexp l : ℝ) - 1) * Real.log (μ (p : AlgebraicClosure ℚ)) = 0 := by
      push_cast at hsum; linarith
    rcases mul_eq_zero.1 h1 with h | h
    · exact_mod_cast (sub_eq_zero.1 h)
    · exact absurd h hlogp.ne

  have htlp : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p : AlgebraicClosure ℚ))⁻¹ * t l ∈ C.integers := by
    have := htC l; rwa [hn1, pow_one] at this
  have htlpres : C.residue ⟨_, htlp⟩ ≠ 0 := by
    have e1 : (⟨_, htlp⟩ : C.integers) = ⟨_, htC l⟩ := Subtype.ext (by
        show (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p : AlgebraicClosure ℚ))⁻¹ * t l
          = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((p : AlgebraicClosure ℚ) ^ nexp l))⁻¹ * t l
        rw [hn1, pow_one])
    rw [e1]; exact htCres l
  have hGl : ∀ R ∈ An.dom, ∀ R' ∈ An.dom,
      μ (R.evalAt (t l) - R'.evalAt (t l)) = μ (R.evalAt z' - R'.evalAt z') := by
    intro R hR R' hR'
    obtain ⟨hG, hGres⟩ := hfar (t l) htlp htlpres
    obtain ⟨-, hIso⟩ :=
      AlgebraicCurve.Annulus.abv_evalAt_sub_eq_abv_param_sub_of_isAttached_both_ends_of_ord_residue_eq_one μ hμA
        An' An hdomG hmodG hmod0G htwoG C' x' hatt' C x hatt hwideG (t l) (htC' l) (htres' l) hordl' hG hGres
        (fun R hR => (hreg l R (hdom ▸ hR)).1)
    exact (hIso R (hdom ▸ hR) R' (hdom ▸ hR')).2
  have hGi : ∀ i : Fin r, 1 ≤ (i : ℕ) → ∀ R ∈ An.dom, ∀ R' ∈ An.dom,
      μ (R.evalAt (t l + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p : AlgebraicClosure ℚ) * t i)
          - R'.evalAt (t l + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p : AlgebraicClosure ℚ) * t i))
        = μ (R.evalAt z' - R'.evalAt z') := by
    intro i hi R hR R' hR'
    set fi : modularFunctionFieldBar N :=
      t l + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p : AlgebraicClosure ℚ) * t i with hfi
    have hfiC' : fi ∈ C'.integers := add_mem (htC' l) (mul_mem hpC' (htC' i))
    have hfires' : C'.residue ⟨fi, hfiC'⟩ = C'.residue ⟨t l, htC' l⟩ := by
      have e1 : (⟨fi, hfiC'⟩ : C'.integers) = ⟨t l, htC' l⟩ + ⟨_, hpC'⟩ * ⟨t i, htC' i⟩ := Subtype.ext rfl
      rw [e1, map_add, map_mul, hpC'res, zero_mul, add_zero]
    have hfires'0 : C'.residue ⟨fi, hfiC'⟩ ≠ 0 := by rw [hfires']; exact htres' l
    have hfiord : x'.ord (C'.residue ⟨fi, hfiC'⟩) = 1 := by rw [hfires']; exact hordl'
    have hn_i : 1 ≤ nexp i := hnexp1 i hi
    have htiZ : t i = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((p : AlgebraicClosure ℚ) ^ nexp i)
        * ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((p : AlgebraicClosure ℚ) ^ nexp i))⁻¹ * t i) := by
      rw [← mul_assoc, mul_inv_cancel₀ ((map_ne_zero _).2 (pow_ne_zero _ hp0)), one_mul (t i)]
    have key : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p : AlgebraicClosure ℚ))⁻¹ * fi
        = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p : AlgebraicClosure ℚ))⁻¹ * t l
          + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((p : AlgebraicClosure ℚ) ^ nexp i)
            * ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((p : AlgebraicClosure ℚ) ^ nexp i))⁻¹ * t i) := by
      rw [hfi, mul_add, ← mul_assoc _ (algebraMap _ _ (p : AlgebraicClosure ℚ)) (t i), inv_mul_cancel₀ hPL, one_mul (t i), ← htiZ]
    have hfiC : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p : AlgebraicClosure ℚ))⁻¹ * fi ∈ C.integers := by
      rw [key]; exact add_mem htlp (mul_mem (hpnC _) (htC i))
    have hfiCres : C.residue ⟨_, hfiC⟩ ≠ 0 := by
      have e1 : (⟨_, hfiC⟩ : C.integers) = ⟨_, htlp⟩ + ⟨_, hpnC _⟩ * ⟨_, htC i⟩ := Subtype.ext key
      rw [e1, map_add, map_mul, hpnCres _ hn_i, zero_mul, add_zero]; exact htlpres
    obtain ⟨hG, hGres⟩ := hfar fi hfiC hfiCres
    have hfireg : ∀ R ∈ An'.dom, fi ∈ R.toValuationSubring := fun R hR =>
      add_mem (hreg l R (hdom ▸ hR)).1 (mul_mem (R.algebraMap_mem' _) (hreg i R (hdom ▸ hR)).1)
    obtain ⟨-, hIso⟩ :=
      AlgebraicCurve.Annulus.abv_evalAt_sub_eq_abv_param_sub_of_isAttached_both_ends_of_ord_residue_eq_one μ hμA
        An' An hdomG hmodG hmod0G htwoG C' x' hatt' C x hatt hwideG fi hfiC' hfires'0 hfiord hG hGres hfireg
    exact (hIso R (hdom ▸ hR) R' (hdom ▸ hR')).2

  set xr : Fin r → AlgebraicClosure ℚ := fun i => P.evalAt (t i * (t o)⁻¹) with hxr
  set yr : Fin r → AlgebraicClosure ℚ := fun i => Q.evalAt (t i * (t o)⁻¹) with hyr
  have hxeval : ∀ i, xr i = P.evalAt (t i) := fun i => by simp [hxr, hto]
  have hyeval : ∀ i, yr i = Q.evalAt (t i) := fun i => by simp [hyr, hto]
  have hxo : xr o = 1 := by rw [hxeval, hto, Place.evalAt_one]
  have hyo : yr o = 1 := by rw [hyeval, hto, Place.evalAt_one]
  have hxle : ∀ i, μ (xr i) ≤ 1 := fun i => by rw [hxeval]; exact (hreg i P hP).2
  have hyle : ∀ i, μ (yr i) ≤ 1 := fun i => by rw [hyeval]; exact (hreg i Q hQ).2
  have hsub : ∀ a b : AlgebraicClosure ℚ, μ (a - b) ≤ max (μ a) (μ b) := by
    intro a b; rw [sub_eq_add_neg, ← AbsoluteValue.map_neg μ b]; exact hμ _ _
  have hdl : μ (xr l - yr l) = δ := by rw [hxeval, hyeval, hδ]; exact hGl P hP Q hQ
  have hdi : ∀ i, μ (xr i - yr i) ≤ δ * (μ (p : AlgebraicClosure ℚ))⁻¹ := by
    intro i
    by_cases hi : 1 ≤ (i : ℕ)
    · have hfi := hGi i hi P hP Q hQ
      have hPi : P.evalAt (t l + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p : AlgebraicClosure ℚ) * t i)
          = P.evalAt (t l) + (p : AlgebraicClosure ℚ) * P.evalAt (t i) := by
        rw [P.evalAt_add_G hPrat (hreg l P hP).1 (mul_mem (P.algebraMap_mem' _) (hreg i P hP).1),
          P.evalAt_mul_G hPrat (P.algebraMap_mem' _) (hreg i P hP).1, P.evalAt_algebraMap_G]
      have hQi : Q.evalAt (t l + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p : AlgebraicClosure ℚ) * t i)
          = Q.evalAt (t l) + (p : AlgebraicClosure ℚ) * Q.evalAt (t i) := by
        rw [Q.evalAt_add_G hQrat (hreg l Q hQ).1 (mul_mem (Q.algebraMap_mem' _) (hreg i Q hQ).1),
          Q.evalAt_mul_G hQrat (Q.algebraMap_mem' _) (hreg i Q hQ).1, Q.evalAt_algebraMap_G]
      rw [hPi, hQi] at hfi
      have hrew : (p : AlgebraicClosure ℚ) * (xr i - yr i)
          = (P.evalAt (t l) + (p : AlgebraicClosure ℚ) * P.evalAt (t i) - (Q.evalAt (t l) + (p : AlgebraicClosure ℚ) * Q.evalAt (t i)))
            - (P.evalAt (t l) - Q.evalAt (t l)) := by rw [hxeval, hyeval]; ring
      have h1 : μ ((p : AlgebraicClosure ℚ) * (xr i - yr i)) ≤ δ := by
        rw [hrew]
        exact (hsub _ _).trans (max_le (le_of_eq hfi) (le_of_eq (hGl P hP Q hQ)))
      rw [map_mul] at h1
      rw [le_mul_inv_iff₀ hμp0, mul_comm]; exact h1
    · have hi0 : (i : ℕ) = 0 := by omega
      rw [hxeval, hyeval, ht0eq i hi0, Place.evalAt_one, Place.evalAt_one, sub_self, map_zero]
      exact mul_nonneg hδ0.le (inv_nonneg.2 hμp0.le)
  have hS := AlgebraicCurve.prox_eq_neg_log_iSup_sub_of_chart μ hμ xr yr o hxo hyo hxle hyle
  haveI : Nonempty (Fin r) := ⟨o⟩
  have hS_ge : δ ≤ ⨆ i, μ (xr i - yr i) := by
    rw [← hdl]; exact le_ciSup (Finite.bddAbove_range fun i => μ (xr i - yr i)) l
  have hS_le : (⨆ i, μ (xr i - yr i)) ≤ δ * (μ (p : AlgebraicClosure ℚ))⁻¹ := ciSup_le hdi
  have hS0 : 0 < ⨆ i, μ (xr i - yr i) := hδ0.trans_le hS_ge
  have hproxt_le : prox μ xr yr + Real.log δ ≤ 0 := by
    rw [hS]; have := Real.log_le_log hδ0 hS_ge; linarith
  have hproxt_ge : -(-Real.log (μ (p : AlgebraicClosure ℚ))) ≤ prox μ xr yr + Real.log δ := by
    rw [hS]
    have h1 := Real.log_le_log hS0 hS_le
    rw [Real.log_mul hδ0.ne' (inv_ne_zero hμp0.ne'), Real.log_inv] at h1
    linarith
  have hproxt : |prox μ xr yr + Real.log δ| ≤ -Real.log (μ (p : AlgebraicClosure ℚ)) :=
    abs_le.2 ⟨hproxt_ge, hproxt_le.trans hlam⟩

  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hst' : ∀ i, s i = ∑ j, M i j • t j := by
    intro i; rw [hst i]; exact Finset.sum_congr rfl fun j _ => (Algebra.smul_def _ _).symm
  obtain ⟨dP, hdP0, hdP⟩ := AlgebraicCurve.exists_evalVec_eq_smul_mulVec_of_eq_sum_smul hr s t hs0 ht0 M Minv
    hMinvM hMMinv hst' P hPrat o (fun j => by rw [hto, inv_one, mul_one]; exact (hreg j P hP).1)
  obtain ⟨dQ, hdQ0, hdQ⟩ := AlgebraicCurve.exists_evalVec_eq_smul_mulVec_of_eq_sum_smul hr s t hs0 ht0 M Minv
    hMinvM hMMinv hst' Q hQrat o (fun j => by rw [hto, inv_one, mul_one]; exact (hreg j Q hQ).1)
  obtain ⟨i', j', hij⟩ := hnonprop
  have hminor : ∀ i j, evalVec s P i * evalVec s Q j - evalVec s P j * evalVec s Q i
      = dP * dQ * (M.mulVec xr i * M.mulVec yr j - M.mulVec xr j * M.mulVec yr i) := by
    intro i j; rw [hdP, hdQ]; simp only [Pi.smul_apply, smul_eq_mul]; ring
  have hMm : M.mulVec xr i' * M.mulVec yr j' - M.mulVec xr j' * M.mulVec yr i' ≠ 0 := by
    intro h0; apply hij; exact sub_eq_zero.1 (by rw [hminor, h0, mul_zero])
  have hsupM : (⨆ q : Fin r × Fin r, μ (M.mulVec xr q.1 * M.mulVec yr q.2 - M.mulVec xr q.2 * M.mulVec yr q.1)) ≠ 0 :=
    ((μ.pos hMm).trans_le (le_ciSup (Finite.bddAbove_range
      (fun q : Fin r × Fin r => μ (M.mulVec xr q.1 * M.mulVec yr q.2 - M.mulVec xr q.2 * M.mulVec yr q.1))) (i', j'))).ne'
  have hm1 : xr o * yr l - xr l * yr o ≠ 0 := by
    rw [hxo, hyo, one_mul, mul_one]
    intro h0
    have : μ (xr l - yr l) = 0 := by rw [← neg_sub, AbsoluteValue.map_neg, h0, map_zero]
    rw [hdl] at this
    exact hδ0.ne' this
  have hx0 : xr ≠ 0 := by
    intro h0; have := congrFun h0 o
    rw [hxo] at this; exact one_ne_zero this
  have hy0 : yr ≠ 0 := by
    intro h0; have := congrFun h0 o
    rw [hyo] at this; exact one_ne_zero this
  set β : ℝ := (μ (p : AlgebraicClosure ℚ))⁻¹ ^ Bl with hβ
  have hβ1 : 1 ≤ β := one_le_pow₀ ((one_le_inv₀ hμp0).2 hμp1.le)
  have hlogβ : Real.log β = (Bl : ℝ) * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
    rw [hβ, Real.log_pow, Real.log_inv]
  have hentry : ∀ m : AlgebraicClosure ℚ, (p : AlgebraicClosure ℚ) ^ Bl * m ∈ A → μ m ≤ β := by
    intro m hm
    have h1 : μ ((p : AlgebraicClosure ℚ) ^ Bl * m) ≤ 1 := (hμA _).1 hm
    rw [map_mul, map_pow] at h1
    have hpB : 0 < μ (p : AlgebraicClosure ℚ) ^ Bl := pow_pos hμp0 _
    rw [hβ, inv_pow]
    calc μ m = (μ (p : AlgebraicClosure ℚ) ^ Bl * μ m) * (μ (p : AlgebraicClosure ℚ) ^ Bl)⁻¹ := by field_simp
      _ ≤ 1 * (μ (p : AlgebraicClosure ℚ) ^ Bl)⁻¹ := mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hpB.le)
      _ = (μ (p : AlgebraicClosure ℚ) ^ Bl)⁻¹ := one_mul _
  have hMβ : ∀ i j, μ (M i j) ≤ β := fun i j => hentry _ (hwin i j).1
  have hMβ' : ∀ i j, μ (Minv i j) ≤ β := fun i j => hentry _ (hwin i j).2
  have hprox1 : prox μ (evalVec s P) (evalVec s Q) = prox μ (M.mulVec xr) (M.mulVec yr) := by
    rw [hdP, hdQ]; exact AlgebraicCurve.prox_smul_smul μ _ _ hdP0 hdQ0 hsupM
  have hL := AlgebraicCurve.abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le μ hμ M Minv hMinvM
    β hβ1 hMβ hMβ' xr yr hx0 hy0 ⟨o, l, hm1⟩
  rw [hlogβ, ← hprox1] at hL

  set lam : ℝ := -Real.log (μ (p : AlgebraicClosure ℚ)) with hlam_def
  have hzPe : P.evalAt z = π * (P.evalAt z')⁻¹ := by rw [← hprodP, mul_inv_cancel_right₀ hz'P0]
  have hzQe : Q.evalAt z = π * (Q.evalAt z')⁻¹ := by rw [← hprodQ, mul_inv_cancel_right₀ hz'Q0]
  have hdiffz : P.evalAt z - Q.evalAt z = π * (Q.evalAt z' - P.evalAt z') * (P.evalAt z' * Q.evalAt z')⁻¹ := by
    rw [hzPe, hzQe]; field_simp
  have hμz'P0 : 0 < μ (P.evalAt z') := μ.pos hz'P0
  have hμz'Q0 : 0 < μ (Q.evalAt z') := μ.pos hz'Q0
  have hμdiffz : μ (P.evalAt z - Q.evalAt z) = μ π * δ * (μ (P.evalAt z') * μ (Q.evalAt z'))⁻¹ := by
    rw [hdiffz, map_mul, map_mul, map_inv₀, map_mul, ← neg_sub (P.evalAt z') (Q.evalAt z'), AbsoluteValue.map_neg]
  have hlogz : Real.log (μ (P.evalAt z - Q.evalAt z))
      = Real.log (μ (p : AlgebraicClosure ℚ)) + Real.log δ - Real.log (μ (P.evalAt z')) - Real.log (μ (Q.evalAt z')) := by
    rw [hμdiffz, hμπ, Real.log_mul (mul_ne_zero hμp0.ne' hδ0.ne') (inv_ne_zero (mul_ne_zero hμz'P0.ne' hμz'Q0.ne')),
      Real.log_mul hμp0.ne' hδ0.ne', Real.log_inv, Real.log_mul hμz'P0.ne' hμz'Q0.ne']
    ring
  have hlP1 : Real.log (μ (P.evalAt z')) < 0 := Real.log_neg hμz'P0 hμz'P1
  have hlQ1 : Real.log (μ (Q.evalAt z')) < 0 := Real.log_neg hμz'Q0 hμz'Q1
  have hlP0 : Real.log (μ (p : AlgebraicClosure ℚ)) < Real.log (μ (P.evalAt z')) := Real.log_lt_log hμp0 (hμπ ▸ hμz'P)
  have hlQ0 : Real.log (μ (p : AlgebraicClosure ℚ)) < Real.log (μ (Q.evalAt z')) := Real.log_lt_log hμp0 (hμπ ▸ hμz'Q)
  have hcmp : |Real.log (μ (P.evalAt z - Q.evalAt z)) - Real.log δ| ≤ lam := by
    rw [hlogz, hlam_def, abs_le]; constructor <;> linarith

  have hmodlog : -Real.log (μ ((An.modulus : AlgebraicClosure ℚ))) = lam := by
    rw [hlam_def]; show -Real.log (μ π) = _; rw [hμπ]
  rw [hmodlog]
  have h1 : |prox μ (evalVec s P) (evalVec s Q) + Real.log (μ (P.evalAt z - Q.evalAt z))|
      ≤ |prox μ (evalVec s P) (evalVec s Q) - prox μ xr yr| + |prox μ xr yr + Real.log δ|
        + |Real.log (μ (P.evalAt z - Q.evalAt z)) - Real.log δ| := by
    have e1 : prox μ (evalVec s P) (evalVec s Q) + Real.log (μ (P.evalAt z - Q.evalAt z))
        = (prox μ (evalVec s P) (evalVec s Q) - prox μ xr yr) + (prox μ xr yr + Real.log δ)
          + (Real.log (μ (P.evalAt z - Q.evalAt z)) - Real.log δ) := by ring
    rw [e1]
    exact (abs_add_le _ _).trans (by linarith [abs_add_le (prox μ (evalVec s P) (evalVec s Q) - prox μ xr yr) (prox μ xr yr + Real.log δ)])
  calc |prox μ (evalVec s P) (evalVec s Q) + Real.log (μ (P.evalAt z - Q.evalAt z))|
      ≤ 4 * ((Bl : ℝ) * lam) + lam + lam := by rw [hlam_def]; linarith [h1, hL, hproxt, hcmp]
    _ = (4 * (Bl : ℝ) + 2) * lam := by ring

end S_ModularCurve_annulusComparison_of_attached_at_both_ends_of_adaptedFamily
end P2MW
export P2MW.S_ModularCurve_annulusComparison_of_attached_at_both_ends_of_adaptedFamily (solution)
