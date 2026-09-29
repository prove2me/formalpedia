-- Prove2me | solution 1 for ModularCurve.exists_inertiaStable_degZero_pic0Mk_eq_xH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/9f329081-d478-5bec-aad5-604a692549c5

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental
import Theorems.Thm_ModularCurve_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq_place_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "translation_mem_GammaH xHFunctionFieldC xHFunctionField xHFunctionFieldBar JH qExpFunctionFieldC arithmeticGalois baseAut_arithmeticGalois coe_arithmeticGalois_smul coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single laurentBaseChange JOneES.exists_transcendental_finiteDimensional_laurentBaseChange JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq_place_laurentBaseChange"
namespace GaloisDescent
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH.ModularCurve"

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

abbrev Fb : Type := ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)

abbrev Gal : Type := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

abbrev gal (σ : Gal) : SemilinearAut (AlgebraicClosure ℚ) (Fb F₀) :=
  arithmeticGalois F₀ σ

def lc (f : Fb F₀) : AlgebraicClosure ℚ := (f : LaurentSeries (AlgebraicClosure ℚ)).leadingCoeff

variable {F₀}

theorem lc_ne_zero {f : Fb F₀} : lc F₀ f ≠ 0 ↔ f ≠ 0 := by
  rw [lc, HahnSeries.leadingCoeff_ne_zero, ne_eq, ne_eq, ZeroMemClass.coe_eq_zero]

theorem lc_zero : lc F₀ (0 : Fb F₀) = 0 := by
  rw [lc, ZeroMemClass.coe_zero, HahnSeries.leadingCoeff_zero]

theorem lc_mul (f h : Fb F₀) : lc F₀ (f * h) = lc F₀ f * lc F₀ h := by
  rw [lc, lc, lc, MulMemClass.coe_mul, HahnSeries.leadingCoeff_mul]

theorem lc_one : lc F₀ (1 : Fb F₀) = 1 := by
  rw [lc, OneMemClass.coe_one, ← HahnSeries.single_zero_one, HahnSeries.leadingCoeff_of_single]

theorem lc_algebraMap (c : AlgebraicClosure ℚ) : lc F₀ (algebraMap (AlgebraicClosure ℚ) (Fb F₀) c) = c := by
  rw [lc, show ((algebraMap (AlgebraicClosure ℚ) (Fb F₀) c : Fb F₀) : LaurentSeries (AlgebraicClosure ℚ))
      = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c from rfl,
    algebraMap_laurentSeries_eq_single, HahnSeries.leadingCoeff_of_single]

theorem lc_inv (f : Fb F₀) : lc F₀ f⁻¹ = (lc F₀ f)⁻¹ := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [inv_zero, lc_zero, inv_zero]
  · apply eq_inv_of_mul_eq_one_left
    rw [← lc_mul, inv_mul_cancel₀ hf, lc_one]

theorem leadingCoeff_coeffMap {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) (x : LaurentSeries R) :
    (coeffMap φ x).leadingCoeff = φ x.leadingCoeff := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, HahnSeries.leadingCoeff_zero, HahnSeries.leadingCoeff_zero, map_zero]
  have hsupp : (coeffMap φ x).support = x.support := by
    ext n
    rw [HahnSeries.mem_support, HahnSeries.mem_support, coeffMap_coeff, map_ne_zero_iff φ hφ]
  have hx' : coeffMap φ x ≠ 0 := by
    intro h
    apply hx
    ext n
    have := congrArg (fun y => y.coeff n) h
    simp only [coeffMap_coeff, HahnSeries.coeff_zero] at this
    exact (map_eq_zero_iff φ hφ).mp this
  have horder : (coeffMap φ x).order = x.order := by
    rw [HahnSeries.order_of_ne hx', HahnSeries.order_of_ne hx]
    congr 1
  rw [HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq, horder, coeffMap_coeff]

theorem lc_smul (σ : Gal) (f : Fb F₀) : lc F₀ (gal F₀ σ • f) = σ (lc F₀ f) := by
  rw [lc, lc, coe_arithmeticGalois_smul]
  exact leadingCoeff_coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) σ.injective _

def IsDivOf (f : Fb F₀) (E : Divisor (AlgebraicClosure ℚ) (Fb F₀)) : Prop :=
  f ≠ 0 ∧ ∀ v : Place (AlgebraicClosure ℚ) (Fb F₀), E v = v.ord f

theorem IsDivOf.mul {f h : Fb F₀} {E E' : Divisor (AlgebraicClosure ℚ) (Fb F₀)}
    (hf : IsDivOf f E) (hh : IsDivOf h E') : IsDivOf (f * h) (E + E') :=
  ⟨mul_ne_zero hf.1 hh.1, fun v => by rw [Finsupp.add_apply, hf.2 v, hh.2 v, v.ord_mul hf.1 hh.1]⟩

theorem IsDivOf.inv {f : Fb F₀} {E : Divisor (AlgebraicClosure ℚ) (Fb F₀)} (hf : IsDivOf f E) :
    IsDivOf f⁻¹ (-E) :=
  ⟨inv_ne_zero hf.1, fun v => by rw [Finsupp.neg_apply, hf.2 v, v.ord_inv]⟩

theorem IsDivOf.smul (σ : Gal) {f : Fb F₀} {E : Divisor (AlgebraicClosure ℚ) (Fb F₀)} (hf : IsDivOf f E) :
    IsDivOf (gal F₀ σ • f) (gal F₀ σ • E) := by
  refine ⟨by rw [SemilinearAut.smul_def]; exact (map_ne_zero_iff _ (SemilinearAut.toRingAut (gal F₀ σ)).injective).mpr hf.1,
    fun w => ?_⟩
  rw [SemilinearAut.divisor_smul_apply, hf.2]
  have h := SemilinearAut.ord_smul (gal F₀ σ) ((gal F₀ σ)⁻¹ • w) f
  rw [smul_inv_smul] at h
  exact h.symm

theorem IsDivOf.algebraMap_mul {f : Fb F₀} {E : Divisor (AlgebraicClosure ℚ) (Fb F₀)} (hf : IsDivOf f E)
    {c : AlgebraicClosure ℚ} (hc : c ≠ 0) : IsDivOf (algebraMap (AlgebraicClosure ℚ) (Fb F₀) c * f) E := by
  refine ⟨mul_ne_zero ((map_ne_zero_iff _ (algebraMap (AlgebraicClosure ℚ) (Fb F₀)).injective).mpr hc) hf.1, fun v => ?_⟩
  rw [v.ord_mul ((map_ne_zero_iff _ (algebraMap (AlgebraicClosure ℚ) (Fb F₀)).injective).mpr hc) hf.1, ← hf.2 v]

  have h1 : v.ord (algebraMap (AlgebraicClosure ℚ) (Fb F₀) c) = 0 := by
    have hu : IsUnit (⟨algebraMap (AlgebraicClosure ℚ) (Fb F₀) c, v.algebraMap_mem' c⟩ : v.toValuationSubring) := by
      refine IsUnit.of_mul_eq_one (⟨algebraMap (AlgebraicClosure ℚ) (Fb F₀) c⁻¹, v.algebraMap_mem' c⁻¹⟩ : v.toValuationSubring) ?_
      apply Subtype.ext
      show algebraMap (AlgebraicClosure ℚ) (Fb F₀) c * algebraMap (AlgebraicClosure ℚ) (Fb F₀) c⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hc, map_one]
    exact v.ord_coe_unit hu.unit
  rw [h1, zero_add]

structure ConstantsData (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) : Prop where
  const_of_ord_zero : ∀ {x : Fb F₀}, (∀ v : Place (AlgebraicClosure ℚ) (Fb F₀), v.ord x = 0) →
    x ∈ (algebraMap (AlgebraicClosure ℚ) (Fb F₀)).range

variable (hC : ConstantsData F₀)
include hC

theorem IsDivOf.eq_of_lc_eq {f f' : Fb F₀} {E : Divisor (AlgebraicClosure ℚ) (Fb F₀)}
    (hf : IsDivOf f E) (hf' : IsDivOf f' E) (hlc : lc F₀ f = lc F₀ f') : f = f' := by
  have hq : IsDivOf (f * f'⁻¹) (E + -E) := hf.mul hf'.inv
  rw [add_neg_cancel] at hq
  obtain ⟨c, hc⟩ := hC.const_of_ord_zero (fun v => by rw [← hq.2 v]; rfl)
  have hlcq : lc F₀ (f * f'⁻¹) = 1 := by
    rw [lc_mul, lc_inv, hlc, mul_inv_cancel₀ (lc_ne_zero.mpr hf'.1)]
  have hc1 : c = 1 := by rw [← lc_algebraMap (F₀ := F₀) c, hc, hlcq]
  rw [hc1, map_one] at hc

  have := congrArg (· * f') hc
  simp only [one_mul, inv_mul_cancel_right₀ hf'.1] at this
  exact this.symm

omit hC in

theorem exists_isDivOf_lc_eq_one {E : Divisor (AlgebraicClosure ℚ) (Fb F₀)}
    (hE : E ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := Fb F₀)) :
    ∃ f : Fb F₀, IsDivOf f E ∧ lc F₀ f = 1 := by
  obtain ⟨f, hf0, hf⟩ := hE
  refine ⟨algebraMap (AlgebraicClosure ℚ) (Fb F₀) (lc F₀ f)⁻¹ * f,
    IsDivOf.algebraMap_mul ⟨hf0, hf⟩ (inv_ne_zero (lc_ne_zero.mpr hf0)), ?_⟩
  rw [lc_mul, lc_algebraMap, inv_mul_cancel₀ (lc_ne_zero.mpr hf0)]

variable (I : Subgroup Gal) (D : Divisor (AlgebraicClosure ℚ) (Fb F₀))
variable (hD : ∀ σ ∈ I, gal F₀ σ • D - D ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := Fb F₀))
include hD

omit hC in
theorem exists_cocycleFun : ∃ c : I → Fb F₀, ∀ σ : I, IsDivOf (c σ) (gal F₀ σ • D - D) ∧ lc F₀ (c σ) = 1 :=
  ⟨fun σ => (exists_isDivOf_lc_eq_one (hD σ σ.2)).choose,
    fun σ => (exists_isDivOf_lc_eq_one (hD σ σ.2)).choose_spec⟩

def cocycleFun : I → Fb F₀ := (exists_cocycleFun I D hD).choose

omit hC in
theorem cocycleFun_spec (σ : I) : IsDivOf (cocycleFun I D hD σ) (gal F₀ σ • D - D) ∧ lc F₀ (cocycleFun I D hD σ) = 1 :=
  (exists_cocycleFun I D hD).choose_spec σ

theorem cocycleFun_mul (σ τ : I) :
    cocycleFun I D hD (σ * τ) = (gal F₀ σ • cocycleFun I D hD τ) * cocycleFun I D hD σ := by
  apply IsDivOf.eq_of_lc_eq hC (cocycleFun_spec I D hD (σ * τ)).1
  · have h1 := (cocycleFun_spec I D hD τ).1.smul (σ : Gal)
    have h2 := (cocycleFun_spec I D hD σ).1
    have e : gal F₀ ((σ * τ : I) : Gal) • D - D = gal F₀ σ • (gal F₀ τ • D - D) + (gal F₀ σ • D - D) := by
      rw [Subgroup.coe_mul, show gal F₀ ((σ : Gal) * (τ : Gal)) = gal F₀ σ * gal F₀ τ from map_mul _ _ _,
        mul_smul, smul_sub]
      abel
    rw [e]
    exact h1.mul h2
  · rw [(cocycleFun_spec I D hD (σ * τ)).2, lc_mul, lc_smul, (cocycleFun_spec I D hD τ).2,
      (cocycleFun_spec I D hD σ).2, map_one, mul_one]

theorem cocycleFun_eq_one_of_smul_eq {ρ : I} (hρ : gal F₀ ρ • D = D) : cocycleFun I D hD ρ = 1 := by
  apply IsDivOf.eq_of_lc_eq hC (cocycleFun_spec I D hD ρ).1
  · refine ⟨one_ne_zero, fun v => ?_⟩
    rw [hρ, sub_self, Finsupp.zero_apply, v.ord_one]
  · rw [(cocycleFun_spec I D hD ρ).2, lc_one]

end ModularCurve.GaloisDescent

end

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "translation_mem_GammaH xHFunctionFieldC xHFunctionField xHFunctionFieldBar JH qExpFunctionFieldC arithmeticGalois baseAut_arithmeticGalois coe_arithmeticGalois_smul coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single laurentBaseChange JOneES.exists_transcendental_finiteDimensional_laurentBaseChange JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq_place_laurentBaseChange"
namespace GaloisDescent
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH.ModularCurve"

variable {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}

structure OpenStabilisers (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) : Prop where
  exists_fd : ∀ v : Place (AlgebraicClosure ℚ) (Fb F₀),
    ∃ L₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L₀ ∧
      ∀ σ ∈ L₀.fixingSubgroup, gal F₀ σ • v = v

theorem exists_fd_forall_smul_eq (hO : OpenStabilisers F₀) (S : Finset (Place (AlgebraicClosure ℚ) (Fb F₀))) :
    ∃ L₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L₀ ∧
      ∀ σ ∈ L₀.fixingSubgroup, ∀ v ∈ S, gal F₀ σ • v = v := by
  classical
  choose L hL using hO.exists_fd
  refine ⟨⨆ v ∈ S, L v, ?_, ?_⟩
  · haveI : ∀ v, FiniteDimensional ℚ (L v) := fun v => (hL v).1
    exact IntermediateField.finiteDimensional_iSup_of_finset
  · intro σ hσ v hv
    apply (hL v).2 σ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro x hx
    exact hσ x ((le_iSup₂ (f := fun v (_ : v ∈ S) => L v) v hv) hx)

theorem smul_divisor_eq_of_forall_mem_support {g : SemilinearAut (AlgebraicClosure ℚ) (Fb F₀)}
    {D : Divisor (AlgebraicClosure ℚ) (Fb F₀)} (h : ∀ v ∈ D.support, g • v = v) : g • D = D := by
  rw [SemilinearAut.divisor_smul_def]
  conv_rhs => rw [← Finsupp.mapDomain_id (v := D)]
  exact Finsupp.mapDomain_congr (fun v hv => h v hv)

theorem finiteIndex_fixingSubgroup (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L₀] :
    L₀.fixingSubgroup.FiniteIndex := by
  classical

  let r : Gal → (L₀ →ₐ[ℚ] AlgebraicClosure ℚ) := fun σ => (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).comp L₀.val
  have hr : ∀ σ τ : Gal, r σ = r τ ↔ σ⁻¹ * τ ∈ L₀.fixingSubgroup := by
    intro σ τ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      have hx' : σ x = τ x := by
        have := congrArg (fun φ : L₀ →ₐ[ℚ] AlgebraicClosure ℚ => φ ⟨x, hx⟩) h
        exact this
      show σ⁻¹ (τ x) = x
      rw [← hx', show σ⁻¹ (σ x) = x from σ.symm_apply_apply x]
    · intro h
      ext ⟨x, hx⟩
      show σ x = τ x
      have h1 : σ⁻¹ (τ x) = x := h x hx
      have := congrArg σ h1
      rw [show σ (σ⁻¹ (τ x)) = τ x from σ.apply_symm_apply (τ x)] at this
      exact this.symm
  haveI : Finite (Gal ⧸ L₀.fixingSubgroup) := by
    refine Finite.of_injective (Quotient.lift r (fun σ τ (hστ : QuotientGroup.leftRel _ σ τ) =>
      (hr σ τ).mpr (QuotientGroup.leftRel_apply.mp hστ)) : Gal ⧸ L₀.fixingSubgroup → _) ?_
    intro q₁ q₂ h
    induction q₁ using Quotient.inductionOn with
    | h σ =>
      induction q₂ using Quotient.inductionOn with
      | h τ =>
        apply Quotient.sound
        exact QuotientGroup.leftRel_apply.mpr ((hr σ τ).mp h)
  exact Subgroup.finiteIndex_of_finite_quotient

theorem exists_level (hO : OpenStabilisers F₀) (D : Divisor (AlgebraicClosure ℚ) (Fb F₀)) :
    ∃ L₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L₀ ∧
      L₀.fixingSubgroup.FiniteIndex ∧ ∀ σ ∈ L₀.fixingSubgroup, gal F₀ σ • D = D := by
  obtain ⟨L₀, hfd, hfix⟩ := exists_fd_forall_smul_eq hO D.support
  haveI := hfd
  exact ⟨L₀, hfd, finiteIndex_fixingSubgroup L₀,
    fun σ hσ => smul_divisor_eq_of_forall_mem_support (hfix σ hσ)⟩

theorem smul_algebraMap_eq_of_mem_fixingSubgroup {L₀ : IntermediateField ℚ (AlgebraicClosure ℚ)}
    {σ : Gal} (hσ : σ ∈ L₀.fixingSubgroup) {a : AlgebraicClosure ℚ} (ha : a ∈ L₀) :
    gal F₀ σ • algebraMap (AlgebraicClosure ℚ) (Fb F₀) a = algebraMap (AlgebraicClosure ℚ) (Fb F₀) a := by
  rw [SemilinearAut.smul_algebraMap, baseAut_arithmeticGalois]
  show algebraMap (AlgebraicClosure ℚ) (Fb F₀) (σ a) = _
  rw [(IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ a ha]

theorem mem_fixingSubgroup_of_smul_algebraMap_eq {L₀ : IntermediateField ℚ (AlgebraicClosure ℚ)} {σ : Gal}
    (h : ∀ a ∈ L₀, gal F₀ σ • algebraMap (AlgebraicClosure ℚ) (Fb F₀) a = algebraMap (AlgebraicClosure ℚ) (Fb F₀) a) :
    σ ∈ L₀.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro a ha
  have h1 := h a ha
  rw [SemilinearAut.smul_algebraMap, baseAut_arithmeticGalois] at h1
  exact (algebraMap (AlgebraicClosure ℚ) (Fb F₀)).injective h1

end ModularCurve.GaloisDescent

end

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "translation_mem_GammaH xHFunctionFieldC xHFunctionField xHFunctionFieldBar JH qExpFunctionFieldC arithmeticGalois baseAut_arithmeticGalois coe_arithmeticGalois_smul coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single laurentBaseChange JOneES.exists_transcendental_finiteDimensional_laurentBaseChange JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq_place_laurentBaseChange"
namespace GaloisDescent
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH.ModularCurve"

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (I : Subgroup Gal) (H : Subgroup ↥I)

def Fix : Subfield (Fb F₀) where
  carrier := {x | ∀ τ : ↥H, gal F₀ ((τ : ↥I) : Gal) • x = x}
  mul_mem' {x y} hx hy τ := by rw [smul_mul', hx τ, hy τ]
  one_mem' τ := smul_one _
  add_mem' {x y} hx hy τ := by rw [smul_add, hx τ, hy τ]
  zero_mem' τ := smul_zero _
  neg_mem' {x} hx τ := by rw [smul_neg, hx τ]
  inv_mem' x hx τ := by rw [smul_inv'', hx τ]

variable {F₀ I H}

theorem mem_Fix_iff {x : Fb F₀} : x ∈ Fix F₀ I H ↔ ∀ τ : ↥H, gal F₀ ((τ : ↥I) : Gal) • x = x := Iff.rfl

variable (F₀ I H)
variable [hHn : H.Normal]

theorem smul_mem_Fix (σ : ↥I) {x : Fb F₀} (hx : x ∈ Fix F₀ I H) : gal F₀ (σ : Gal) • x ∈ Fix F₀ I H := by
  rw [mem_Fix_iff] at hx ⊢
  intro τ
  have hconj : σ⁻¹ * (τ : ↥I) * σ⁻¹⁻¹ ∈ H := hHn.conj_mem (τ : ↥I) τ.2 σ⁻¹
  rw [inv_inv] at hconj
  have key : gal F₀ ((τ : ↥I) : Gal) * gal F₀ (σ : Gal) = gal F₀ (σ : Gal) * gal F₀ (((σ⁻¹ * (τ : ↥I) * σ : ↥I)) : Gal) := by
    rw [show gal F₀ ((τ : ↥I) : Gal) * gal F₀ (σ : Gal) = gal F₀ (((τ : ↥I) : Gal) * (σ : Gal)) from (map_mul _ _ _).symm,
      show gal F₀ (σ : Gal) * gal F₀ (((σ⁻¹ * (τ : ↥I) * σ : ↥I)) : Gal)
        = gal F₀ ((σ : Gal) * (((σ⁻¹ * (τ : ↥I) * σ : ↥I)) : Gal)) from (map_mul _ _ _).symm]
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  calc gal F₀ ((τ : ↥I) : Gal) • gal F₀ (σ : Gal) • x
      = (gal F₀ ((τ : ↥I) : Gal) * gal F₀ (σ : Gal)) • x := by rw [mul_smul]
    _ = (gal F₀ (σ : Gal) * gal F₀ (((σ⁻¹ * (τ : ↥I) * σ : ↥I)) : Gal)) • x := by rw [key]
    _ = gal F₀ (σ : Gal) • (gal F₀ (((σ⁻¹ * (τ : ↥I) * σ : ↥I)) : Gal) • x) := by rw [mul_smul]
    _ = gal F₀ (σ : Gal) • x := by rw [hx ⟨_, hconj⟩]

def fixAut (σ : ↥I) : Fix F₀ I H ≃+* Fix F₀ I H where
  toFun x := ⟨gal F₀ (σ : Gal) • (x : Fb F₀), smul_mem_Fix F₀ I H σ x.2⟩
  invFun x := ⟨gal F₀ ((σ⁻¹ : ↥I) : Gal) • (x : Fb F₀), smul_mem_Fix F₀ I H σ⁻¹ x.2⟩
  left_inv x := Subtype.ext (by
    show gal F₀ ((σ⁻¹ : ↥I) : Gal) • gal F₀ (σ : Gal) • (x : Fb F₀) = x
    rw [← mul_smul, show gal F₀ ((σ⁻¹ : ↥I) : Gal) * gal F₀ (σ : Gal) = gal F₀ (((σ⁻¹ : ↥I) : Gal) * (σ : Gal))
      from (map_mul _ _ _).symm, Subgroup.coe_inv, inv_mul_cancel, show gal F₀ (1 : Gal) = 1 from map_one _, one_smul])
  right_inv x := Subtype.ext (by
    show gal F₀ (σ : Gal) • gal F₀ ((σ⁻¹ : ↥I) : Gal) • (x : Fb F₀) = x
    rw [← mul_smul, show gal F₀ (σ : Gal) * gal F₀ ((σ⁻¹ : ↥I) : Gal) = gal F₀ ((σ : Gal) * ((σ⁻¹ : ↥I) : Gal))
      from (map_mul _ _ _).symm, Subgroup.coe_inv, mul_inv_cancel, show gal F₀ (1 : Gal) = 1 from map_one _, one_smul])
  map_mul' x y := Subtype.ext (smul_mul' _ _ _)
  map_add' x y := Subtype.ext (smul_add _ _ _)

theorem fixAut_apply (σ : ↥I) (x : Fix F₀ I H) : ((fixAut F₀ I H σ x : Fix F₀ I H) : Fb F₀) = gal F₀ (σ : Gal) • (x : Fb F₀) := rfl

def psi : ↥I →* (Fix F₀ I H ≃+* Fix F₀ I H) where
  toFun := fixAut F₀ I H
  map_one' := RingEquiv.ext fun x => Subtype.ext (by
    show gal F₀ ((1 : ↥I) : Gal) • (x : Fb F₀) = x
    rw [Subgroup.coe_one, show gal F₀ (1 : Gal) = 1 from map_one _, one_smul])
  map_mul' σ τ := RingEquiv.ext fun x => Subtype.ext (by
    show gal F₀ ((σ * τ : ↥I) : Gal) • (x : Fb F₀) = gal F₀ (σ : Gal) • gal F₀ (τ : Gal) • (x : Fb F₀)
    rw [Subgroup.coe_mul, show gal F₀ ((σ : Gal) * (τ : Gal)) = gal F₀ σ * gal F₀ τ from map_mul _ _ _, mul_smul])

theorem psi_apply (σ : ↥I) (x : Fix F₀ I H) : ((psi F₀ I H σ x : Fix F₀ I H) : Fb F₀) = gal F₀ (σ : Gal) • (x : Fb F₀) := rfl

theorem le_ker_psi : H ≤ (psi F₀ I H).ker := by
  intro τ hτ
  rw [MonoidHom.mem_ker]
  exact RingEquiv.ext fun x => Subtype.ext (by rw [psi_apply]; exact x.2 ⟨τ, hτ⟩)

theorem finite_range_psi [H.FiniteIndex] : Finite (psi F₀ I H).range := by
  haveI : (psi F₀ I H).ker.FiniteIndex := Subgroup.finiteIndex_of_le (le_ker_psi F₀ I H)
  exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange (psi F₀ I H)).toEquiv

abbrev Q : Subgroup (Fix F₀ I H ≃+* Fix F₀ I H) := (psi F₀ I H).range

abbrev Kf : Subfield (Fix F₀ I H) := FixedPoints.subfield ↥(Q F₀ I H) (Fix F₀ I H)

theorem Q_smul_def (γ : ↥(Q F₀ I H)) (x : Fix F₀ I H) : γ • x = (γ : Fix F₀ I H ≃+* Fix F₀ I H) x := rfl

example : FaithfulSMul ↥(Q F₀ I H) (Fix F₀ I H) := inferInstance

def artin [H.FiniteIndex] :
    haveI := finite_range_psi F₀ I H
    ↥(Q F₀ I H) ≃* (Fix F₀ I H ≃ₐ[↥(Kf F₀ I H)] Fix F₀ I H) :=
  haveI := finite_range_psi F₀ I H
  FixedPoints.toAlgAutMulEquiv ↥(Q F₀ I H) (Fix F₀ I H)

theorem artin_apply [H.FiniteIndex] (γ : ↥(Q F₀ I H)) (x : Fix F₀ I H) :
    (artin F₀ I H γ) x = (γ : Fix F₀ I H ≃+* Fix F₀ I H) x := rfl

end ModularCurve.GaloisDescent

end

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "translation_mem_GammaH xHFunctionFieldC xHFunctionField xHFunctionFieldBar JH qExpFunctionFieldC arithmeticGalois baseAut_arithmeticGalois coe_arithmeticGalois_smul coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single laurentBaseChange JOneES.exists_transcendental_finiteDimensional_laurentBaseChange JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq_place_laurentBaseChange"
namespace GaloisDescent
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH.ModularCurve groupCohomology"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

example (G : Type) [Group G] (A B : Subgroup G) [A.FiniteIndex] : (A.subgroupOf B).FiniteIndex := inferInstance

section Descent

variable (hC : ConstantsData F₀)
variable (I : Subgroup Gal) (D : Divisor (AlgebraicClosure ℚ) (Fb F₀))
variable (hD : ∀ σ ∈ I, gal F₀ σ • D - D ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := Fb F₀))
variable (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [hNs : L₀.fixingSubgroup.FiniteIndex]
variable (hL₀ : ∀ σ ∈ L₀.fixingSubgroup, gal F₀ σ • D = D)

abbrev Hsub : Subgroup ↥I := ((L₀.fixingSubgroup).subgroupOf I).normalCore

scoped instance Hsub_normal : (Hsub I L₀).Normal := Subgroup.normalCore_normal _

scoped instance Hsub_finiteIndex : (Hsub I L₀).FiniteIndex := by
  haveI : ((L₀.fixingSubgroup).subgroupOf I).FiniteIndex := inferInstance
  infer_instance

theorem coe_mem_fixingSubgroup_of_mem_Hsub {τ : ↥I} (hτ : τ ∈ Hsub I L₀) : (τ : Gal) ∈ L₀.fixingSubgroup :=
  Subgroup.mem_subgroupOf.mp (Subgroup.normalCore_le _ hτ)

include hC hL₀ in

theorem cocycleFun_mem_Fix (σ : ↥I) : cocycleFun I D hD σ ∈ Fix F₀ I (Hsub I L₀) := by
  rw [mem_Fix_iff]
  intro τ
  have hτF₀ : ((τ : ↥I) : Gal) ∈ L₀.fixingSubgroup := coe_mem_fixingSubgroup_of_mem_Hsub I L₀ τ.2

  have hconj : σ⁻¹ * (τ : ↥I) * σ⁻¹⁻¹ ∈ Hsub I L₀ := (Hsub_normal I L₀).conj_mem (τ : ↥I) τ.2 σ⁻¹
  rw [inv_inv] at hconj
  have hconjN := coe_mem_fixingSubgroup_of_mem_Hsub I L₀ hconj
  have e : gal F₀ ((τ : ↥I) : Gal) • (gal F₀ (σ : Gal) • D - D) = gal F₀ (σ : Gal) • D - D := by
    rw [smul_sub, hL₀ _ hτF₀, ← mul_smul,
      show gal F₀ ((τ : ↥I) : Gal) * gal F₀ (σ : Gal) = gal F₀ (((τ : ↥I) : Gal) * (σ : Gal)) from (map_mul _ _ _).symm,
      show ((τ : ↥I) : Gal) * (σ : Gal) = (σ : Gal) * (((σ⁻¹ * (τ : ↥I) * σ : ↥I)) : Gal) by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group,
      show gal F₀ ((σ : Gal) * (((σ⁻¹ * (τ : ↥I) * σ : ↥I)) : Gal)) = gal F₀ σ * gal F₀ (((σ⁻¹ * (τ : ↥I) * σ : ↥I)) : Gal)
        from map_mul _ _ _, mul_smul, hL₀ _ hconjN]
  have h := (cocycleFun_spec I D hD σ).1.smul ((τ : ↥I) : Gal)
  rw [e] at h
  apply IsDivOf.eq_of_lc_eq hC h (cocycleFun_spec I D hD σ).1
  rw [lc_smul, (cocycleFun_spec I D hD σ).2, map_one]

include hC hL₀ in

theorem cocycleFun_eq_of_psi_eq {σ σ' : ↥I} (h : psi F₀ I (Hsub I L₀) σ = psi F₀ I (Hsub I L₀) σ') :
    cocycleFun I D hD σ = cocycleFun I D hD σ' := by
  have hρ : ((σ⁻¹ * σ' : ↥I) : Gal) ∈ L₀.fixingSubgroup := by
    apply mem_fixingSubgroup_of_smul_algebraMap_eq (F₀ := F₀)
    intro a ha
    have hmem : algebraMap (AlgebraicClosure ℚ) (Fb F₀) a ∈ Fix F₀ I (Hsub I L₀) :=
      fun τ => smul_algebraMap_eq_of_mem_fixingSubgroup (coe_mem_fixingSubgroup_of_mem_Hsub I L₀ τ.2) ha
    have h1 := congrArg (fun e : Fix F₀ I (Hsub I L₀) ≃+* Fix F₀ I (Hsub I L₀) => ((e ⟨_, hmem⟩ : Fix F₀ I (Hsub I L₀)) : Fb F₀)) h
    simp only [psi_apply] at h1

    rw [Subgroup.coe_mul, show gal F₀ (((σ⁻¹ : ↥I) : Gal) * (σ' : Gal)) = gal F₀ ((σ⁻¹ : ↥I) : Gal) * gal F₀ σ' from map_mul _ _ _,
      mul_smul, ← h1, ← mul_smul,
      show gal F₀ ((σ⁻¹ : ↥I) : Gal) * gal F₀ (σ : Gal) = gal F₀ (((σ⁻¹ : ↥I) : Gal) * (σ : Gal)) from (map_mul _ _ _).symm,
      Subgroup.coe_inv, inv_mul_cancel, show gal F₀ (1 : Gal) = 1 from map_one _, one_smul]
  have hfix : gal F₀ ((σ⁻¹ * σ' : ↥I) : Gal) • D = D := hL₀ _ hρ
  have h1 := cocycleFun_eq_one_of_smul_eq hC I D hD hfix
  have h2 := cocycleFun_mul hC I D hD σ (σ⁻¹ * σ')
  rw [mul_inv_cancel_left, h1, smul_one, one_mul] at h2
  exact h2.symm

def pre (γ : ↥(Q F₀ I (Hsub I L₀))) : ↥I := (MonoidHom.mem_range.mp γ.2).choose

theorem psi_pre (γ : ↥(Q F₀ I (Hsub I L₀))) : psi F₀ I (Hsub I L₀) (pre F₀ I L₀ γ) = γ :=
  (MonoidHom.mem_range.mp γ.2).choose_spec

include hC hL₀ in
theorem cocycleFun_pre_psi (σ : ↥I) :
    cocycleFun I D hD (pre F₀ I L₀ ⟨psi F₀ I (Hsub I L₀) σ, ⟨σ, rfl⟩⟩) = cocycleFun I D hD σ :=
  cocycleFun_eq_of_psi_eq F₀ hC I D hD L₀ hL₀ (psi_pre F₀ I L₀ _)

attribute [irreducible] artin

def cocycleAut (φ : Fix F₀ I (Hsub I L₀) ≃ₐ[↥(Kf F₀ I (Hsub I L₀))] Fix F₀ I (Hsub I L₀)) : (Fix F₀ I (Hsub I L₀))ˣ :=
  Units.mk0 ⟨cocycleFun I D hD (pre F₀ I L₀ ((artin F₀ I (Hsub I L₀)).symm φ)),
      cocycleFun_mem_Fix F₀ hC I D hD L₀ hL₀ _⟩
    (fun h => (cocycleFun_spec I D hD _).1.1 (congrArg Subtype.val h))

theorem val_cocycleAut (φ : Fix F₀ I (Hsub I L₀) ≃ₐ[↥(Kf F₀ I (Hsub I L₀))] Fix F₀ I (Hsub I L₀)) :
    ((cocycleAut F₀ hC I D hD L₀ hL₀ φ : (Fix F₀ I (Hsub I L₀))ˣ) : Fix F₀ I (Hsub I L₀))
      = ⟨cocycleFun I D hD (pre F₀ I L₀ ((artin F₀ I (Hsub I L₀)).symm φ)), cocycleFun_mem_Fix F₀ hC I D hD L₀ hL₀ _⟩ := rfl

theorem coe_cocycleAut (φ : Fix F₀ I (Hsub I L₀) ≃ₐ[↥(Kf F₀ I (Hsub I L₀))] Fix F₀ I (Hsub I L₀)) :
    (((cocycleAut F₀ hC I D hD L₀ hL₀ φ : (Fix F₀ I (Hsub I L₀))ˣ) : Fix F₀ I (Hsub I L₀)) : Fb F₀)
      = cocycleFun I D hD (pre F₀ I L₀ ((artin F₀ I (Hsub I L₀)).symm φ)) := rfl

attribute [irreducible] cocycleAut

omit hNs in
theorem units_smul_val (φ : Fix F₀ I (Hsub I L₀) ≃ₐ[↥(Kf F₀ I (Hsub I L₀))] Fix F₀ I (Hsub I L₀)) (u : (Fix F₀ I (Hsub I L₀))ˣ) :
    ((φ • u : (Fix F₀ I (Hsub I L₀))ˣ) : Fix F₀ I (Hsub I L₀)) = φ (u : Fix F₀ I (Hsub I L₀)) := rfl

include hC hL₀ in
set_option maxHeartbeats 16000000 in
theorem isMulCocycle₁_cocycleAut : IsMulCocycle₁ (cocycleAut F₀ hC I D hD L₀ hL₀) := by
  intro φ χ
  apply Units.ext
  rw [Units.val_mul, units_smul_val, val_cocycleAut, val_cocycleAut, val_cocycleAut]
  apply Subtype.ext
  show cocycleFun I D hD (pre F₀ I L₀ ((artin F₀ I (Hsub I L₀)).symm (φ * χ)))
    = ((φ ⟨cocycleFun I D hD (pre F₀ I L₀ ((artin F₀ I (Hsub I L₀)).symm χ)), cocycleFun_mem_Fix F₀ hC I D hD L₀ hL₀ _⟩ :
        Fix F₀ I (Hsub I L₀)) : Fb F₀) * cocycleFun I D hD (pre F₀ I L₀ ((artin F₀ I (Hsub I L₀)).symm φ))

  set γφ := (artin F₀ I (Hsub I L₀)).symm φ with hγφ
  set γχ := (artin F₀ I (Hsub I L₀)).symm χ with hγχ
  have hφ : φ = artin F₀ I (Hsub I L₀) γφ := ((artin F₀ I (Hsub I L₀)).apply_symm_apply φ).symm
  have hprod : (artin F₀ I (Hsub I L₀)).symm (φ * χ) = γφ * γχ := by rw [map_mul]
  have hact : ((φ ⟨cocycleFun I D hD (pre F₀ I L₀ γχ), cocycleFun_mem_Fix F₀ hC I D hD L₀ hL₀ _⟩ : Fix F₀ I (Hsub I L₀)) : Fb F₀)
      = gal F₀ ((pre F₀ I L₀ γφ : ↥I) : Gal) • cocycleFun I D hD (pre F₀ I L₀ γχ) := by
    rw [hφ, artin_apply, ← psi_pre F₀ I L₀ γφ]
    rfl
  rw [hprod, hact]
  have hsame : psi F₀ I (Hsub I L₀) (pre F₀ I L₀ (γφ * γχ)) = psi F₀ I (Hsub I L₀) (pre F₀ I L₀ γφ * pre F₀ I L₀ γχ) := by
    rw [map_mul, psi_pre, psi_pre, psi_pre, Subgroup.coe_mul]
  rw [cocycleFun_eq_of_psi_eq F₀ hC I D hD L₀ hL₀ hsame, cocycleFun_mul hC I D hD]

include hC hL₀ in

theorem exists_generator : ∃ g : Fb F₀, g ≠ 0 ∧ ∀ σ : ↥I, gal F₀ (σ : Gal) • g = cocycleFun I D hD σ * g := by
  haveI := finite_range_psi F₀ I (Hsub I L₀)
  obtain ⟨u, hu⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
    (cocycleAut F₀ hC I D hD L₀ hL₀) (isMulCocycle₁_cocycleAut F₀ hC I D hD L₀ hL₀)
  refine ⟨((u : Fix F₀ I (Hsub I L₀)) : Fb F₀), fun h => u.ne_zero (Subtype.ext h), fun σ => ?_⟩
  let γ : ↥(Q F₀ I (Hsub I L₀)) := ⟨psi F₀ I (Hsub I L₀) σ, ⟨σ, rfl⟩⟩
  have h := hu (artin F₀ I (Hsub I L₀) γ)

  have h1 : (((artin F₀ I (Hsub I L₀) γ • u : (Fix F₀ I (Hsub I L₀))ˣ) : Fix F₀ I (Hsub I L₀)) : Fb F₀)
      = gal F₀ (σ : Gal) • (((u : Fix F₀ I (Hsub I L₀)) : Fb F₀)) := by
    rw [units_smul_val, artin_apply]
    rfl
  have h2 := congrArg (fun w : (Fix F₀ I (Hsub I L₀))ˣ => ((w : Fix F₀ I (Hsub I L₀)) : Fb F₀)) h
  simp only [Units.val_div_eq_div_val, Subfield.coe_div, h1, coe_cocycleAut] at h2
  rw [(artin F₀ I (Hsub I L₀)).symm_apply_apply, cocycleFun_pre_psi F₀ hC I D hD L₀ hL₀ σ,
    div_eq_iff (fun h0 => u.ne_zero (Subtype.ext h0))] at h2
  exact h2

end Descent

end ModularCurve.GaloisDescent
p2m_reactivate "P2MW.S_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH.ModularCurve P2MW.S_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH.ModularCurve.GaloisDescent"
p2m_reactivate "P2MW.S_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH.ModularCurve P2MW.S_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH.ModularCurve.GaloisDescent"

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "translation_mem_GammaH xHFunctionFieldC xHFunctionField xHFunctionFieldBar JH qExpFunctionFieldC arithmeticGalois baseAut_arithmeticGalois coe_arithmeticGalois_smul coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single laurentBaseChange JOneES.exists_transcendental_finiteDimensional_laurentBaseChange JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq_place_laurentBaseChange"
namespace GaloisDescent
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH.ModularCurve"

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

section Assembly

variable (hC : ConstantsData F₀) (hO : OpenStabilisers F₀)
variable [hP : HasPrincipalDivisors (AlgebraicClosure ℚ) (Fb F₀)]
variable (I : Subgroup Gal)

include hC hO in

theorem exists_smul_eq_and_mk_eq (x : Pic0 (AlgebraicClosure ℚ) (Fb F₀)) (hx : ∀ σ ∈ I, gal F₀ σ • x = x) :
    ∃ D₀ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := Fb F₀)),
      (∀ σ ∈ I, gal F₀ σ • (D₀ : Divisor (AlgebraicClosure ℚ) (Fb F₀)) = D₀) ∧ Pic0.mk D₀ = x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x

  have hD : ∀ σ ∈ I, gal F₀ σ • (D : Divisor (AlgebraicClosure ℚ) (Fb F₀)) - D
      ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := Fb F₀) := by
    intro σ hσ
    have h := hx σ hσ
    rw [SemilinearAut.pic0_smul_mk, Pic0.mk, Pic0.mk, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h

    have e : gal F₀ σ • (D : Divisor (AlgebraicClosure ℚ) (Fb F₀)) - D
        = -(((-(SemilinearAut.degZeroSMulHom (gal F₀ σ) D) + D :
            ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := Fb F₀))) : Divisor (AlgebraicClosure ℚ) (Fb F₀))) := by
      rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, SemilinearAut.coe_degZeroSMulHom]
      abel
    rw [e]
    exact neg_mem h
  obtain ⟨L₀, hfd, hfi, hL₀⟩ := exists_level hO (D : Divisor (AlgebraicClosure ℚ) (Fb F₀))
  haveI := hfd
  haveI := hfi
  obtain ⟨g, hg0, hg⟩ := exists_generator F₀ hC I (D : Divisor (AlgebraicClosure ℚ) (Fb F₀)) hD L₀ hL₀
  obtain ⟨E, hE, hEdeg⟩ := hP.exists_divisor g hg0
  have hEg : IsDivOf g E := ⟨hg0, hE⟩
  have hmem : (D : Divisor (AlgebraicClosure ℚ) (Fb F₀)) - E ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := Fb F₀) := by
    rw [Divisor.mem_degZero, map_sub, hEdeg, sub_zero]
    exact D.2
  refine ⟨⟨(D : Divisor (AlgebraicClosure ℚ) (Fb F₀)) - E, hmem⟩, ?_, ?_⟩
  · intro σ hσ
    show gal F₀ σ • ((D : Divisor (AlgebraicClosure ℚ) (Fb F₀)) - E) = D - E
    ext v
    rw [smul_sub, Finsupp.sub_apply, Finsupp.sub_apply]
    have h1 : (gal F₀ σ • (D : Divisor (AlgebraicClosure ℚ) (Fb F₀))) v - (D : Divisor (AlgebraicClosure ℚ) (Fb F₀)) v
        = v.ord (cocycleFun I _ hD ⟨σ, hσ⟩) := by
      have := (cocycleFun_spec I (D : Divisor (AlgebraicClosure ℚ) (Fb F₀)) hD ⟨σ, hσ⟩).1.2 v
      rw [Finsupp.sub_apply] at this
      exact this
    have h2 : (gal F₀ σ • E) v = v.ord (cocycleFun I _ hD ⟨σ, hσ⟩) + E v := by
      rw [(hEg.smul σ).2 v, hg ⟨σ, hσ⟩,
        v.ord_mul (cocycleFun_spec I (D : Divisor (AlgebraicClosure ℚ) (Fb F₀)) hD ⟨σ, hσ⟩).1.1 hg0, ← hE v]
    linarith
  ·
    show Pic0.mk _ = Pic0.mk D
    rw [Pic0.mk, Pic0.mk, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    have e : ((-(⟨(D : Divisor (AlgebraicClosure ℚ) (Fb F₀)) - E, hmem⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := Fb F₀))) + D :
        ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := Fb F₀))) : Divisor (AlgebraicClosure ℚ) (Fb F₀)) = E := by
      rw [AddSubgroup.coe_add, AddSubgroup.coe_neg]
      show -((D : Divisor (AlgebraicClosure ℚ) (Fb F₀)) - E) + D = E
      abel
    rw [e]
    exact ⟨g, hg0, hE⟩

end Assembly
p2m_reactivate "P2MW.S_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH.ModularCurve P2MW.S_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH.ModularCurve.GaloisDescent"

end ModularCurve.GaloisDescent
p2m_reactivate "P2MW.S_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH.ModularCurve P2MW.S_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH.ModularCurve.GaloisDescent"
p2m_reactivate "P2MW.S_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH.ModularCurve P2MW.S_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH.ModularCurve.GaloisDescent"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH.ModularCurve P2MW.S_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH.ModularCurve.GaloisDescent"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH.ModularCurve in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {A : ValuationSubring (AlgebraicClosure ℚ)}
    (x : JH M H) (hx : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x) :
    ∃ D₀ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (xHFunctionField M H) σ •
          (D₀ : Divisor (AlgebraicClosure ℚ) (xHFunctionFieldBar M H)) = D₀) ∧
      Pic0.mk D₀ = x := by

  show ∃ D₀ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
      (F := ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))),
    (∀ σ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) σ •
        (D₀ : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) =
          D₀) ∧
    Pic0.mk D₀ = x
  obtain ⟨t, ht, hfd⟩ := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) (CohCarrier.GammaH M H) (translation_mem_GammaH M H)
  haveI := hfd
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) :=
    AlgebraicCurve.hasPrincipalDivisors_of_transcendental (AlgebraicClosure ℚ) t ht
  have hC : GaloisDescent.ConstantsData (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) :=
    ⟨fun {y} hy => AlgebraicCurve.Place.mem_range_algebraMap_of_forall_ord_eq_zero t ht hy⟩
  have hO : GaloisDescent.OpenStabilisers (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := ⟨fun v => by
    obtain ⟨L₀, hL₀fd, hL₀⟩ :=
      ModularCurve.exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq_place_laurentBaseChange
        (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))
        (ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC (CohCarrier.GammaH M H)
          (translation_mem_GammaH M H)) v
    exact ⟨L₀, hL₀fd, fun σ hσ => hL₀ σ hσ⟩⟩
  exact GaloisDescent.exists_smul_eq_and_mk_eq (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) hC hO
    (A.inertiaSubgroupIn ℚ) x (fun σ hσ => hx σ hσ)

#print axioms solution

end S_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH
end P2MW
export P2MW.S_ModularCurve_exists_inertiaStable_degZero_pic0Mk_eq_xH (solution)
