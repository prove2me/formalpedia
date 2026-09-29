-- Prove2me | solution 1 for ModularCurve.exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq_place_laurentBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/6430940d-1afd-5cb2-b4d1-b9a2224f2b45

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_of_coe_eq_coeffEmb
import Theorems.Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq_place_laurentBaseChange
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

open ModularCurve AlgebraicCurve

noncomputable section

open IntermediateField Polynomial
open scoped Pointwise

private abbrev Qbar := AlgebraicClosure ℚ

private abbrev FF (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) : Type _ :=
  ↥(laurentBaseChange Qbar F₀)

private theorem mwfl_hasPrincipalDivisors (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (hF₀ : ∃ x : F₀, Transcendental ℚ x ∧
      FiniteDimensional (IntermediateField.adjoin ℚ ({x} : Set F₀)) F₀) :
    HasPrincipalDivisors Qbar (FF F₀) := by
  obtain ⟨x, hx, hfd⟩ := hF₀
  haveI := hfd
  haveI : Algebra.IsAlgebraic ℚ Qbar := by
    convert AlgebraicClosure.isAlgebraic ℚ
    rfl
    rfl
  set jb : FF F₀ := ⟨coeffEmb Qbar ((x : F₀) : LaurentSeries ℚ),
    coeffEmb_mem_laurentBaseChange Qbar x.2⟩ with hjb
  obtain ⟨htr, hfin⟩ :=
    transcendental_and_finiteDimensional_adjoin_laurentBaseChange_of_coe_eq_coeffEmb
      Qbar F₀ x hx jb rfl
  haveI := hfin
  haveI : CharZero Qbar := inferInstance
  exact AlgebraicCurve.hasPrincipalDivisors_of_transcendental Qbar jb htr

private theorem mwfl_mem_left {L₁ L₂ : IntermediateField ℚ Qbar} {a : Qbar} (ha : a ∈ L₁) :
    a ∈ L₁ ⊔ L₂ :=
  SetLike.le_def.mp le_sup_left ha

private theorem mwfl_mem_right {L₁ L₂ : IntermediateField ℚ Qbar} {a : Qbar} (ha : a ∈ L₂) :
    a ∈ L₁ ⊔ L₂ :=
  SetLike.le_def.mp le_sup_right ha

private theorem mwfl_mem_iSup {ι : Sort*} (t : ι → IntermediateField ℚ Qbar) (i : ι)
    {a : Qbar} (ha : a ∈ t i) : a ∈ ⨆ j, t j :=
  SetLike.le_def.mp (le_iSup t i) ha

private theorem mwfl_isIntegral (a : Qbar) : IsIntegral ℚ a := by
  have h : Algebra.IsAlgebraic ℚ Qbar := by
    convert AlgebraicClosure.isAlgebraic ℚ
    rfl
    rfl
  exact (Algebra.isAlgebraic_iff_isIntegral.mp h).isIntegral a

private theorem mwfl_coeff_level (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) [HasPrincipalDivisors Qbar (FF F₀)] {z : LaurentSeries Qbar}
    (hz : z ∈ laurentBaseChange Qbar F₀) :
    ∃ L : IntermediateField ℚ Qbar, FiniteDimensional ℚ L ∧
      ∀ σ : Qbar ≃ₐ[ℚ] Qbar, (∀ a ∈ L, σ a = a) →
        coeffMap (σ : Qbar →+* Qbar) z = z := by
  have hbot : FiniteDimensional ℚ (⊥ : IntermediateField ℚ Qbar) :=
    (IntermediateField.botEquiv ℚ Qbar).symm.toLinearEquiv.finiteDimensional
  rw [mem_laurentBaseChange_iff] at hz
  induction hz using Subfield.closure_induction with
  | mem y hy =>
    rcases hy with ⟨a, rfl⟩ | ⟨w, hw, rfl⟩
    · exact ⟨IntermediateField.adjoin ℚ {a},
        IntermediateField.adjoin.finiteDimensional (mwfl_isIntegral a),
        fun σ hσ => by
          rw [coeffMap_algebraMap]
          exact congrArg _ (hσ a (IntermediateField.mem_adjoin_simple_self ℚ a))⟩
    · exact ⟨⊥, hbot, fun σ _ => coeffMap_coeffEmb σ w⟩
  | one => exact ⟨⊥, hbot, fun σ _ => map_one _⟩
  | add x y _ _ hx hy =>
    obtain ⟨L₁, h₁, f₁⟩ := hx
    obtain ⟨L₂, h₂, f₂⟩ := hy
    haveI := h₁; haveI := h₂
    exact ⟨L₁ ⊔ L₂, IntermediateField.finiteDimensional_sup L₁ L₂, fun σ hσ => by
      rw [map_add, f₁ σ (fun a ha => hσ a (mwfl_mem_left ha)),
        f₂ σ (fun a ha => hσ a (mwfl_mem_right ha))]⟩
  | neg x _ hx =>
    obtain ⟨L, h, f⟩ := hx
    exact ⟨L, h, fun σ hσ => by rw [map_neg, f σ hσ]⟩
  | inv x _ hx =>
    obtain ⟨L, h, f⟩ := hx
    exact ⟨L, h, fun σ hσ => by rw [map_inv₀, f σ hσ]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨L₁, h₁, f₁⟩ := hx
    obtain ⟨L₂, h₂, f₂⟩ := hy
    haveI := h₁; haveI := h₂
    exact ⟨L₁ ⊔ L₂, IntermediateField.finiteDimensional_sup L₁ L₂, fun σ hσ => by
      rw [map_mul, f₁ σ (fun a ha => hσ a (mwfl_mem_left ha)),
        f₂ σ (fun a ha => hσ a (mwfl_mem_right ha))]⟩

private theorem mwfl_element_level (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) [HasPrincipalDivisors Qbar (FF F₀)] (z : FF F₀) :
    ∃ L : IntermediateField ℚ Qbar, FiniteDimensional ℚ L ∧
      ∀ σ : Qbar ≃ₐ[ℚ] Qbar, (∀ a ∈ L, σ a = a) →
        arithmeticGalois F₀ σ • z = z := by
  obtain ⟨L, hL, hfix⟩ := mwfl_coeff_level F₀ z.2
  refine ⟨L, hL, fun σ hσ => Subtype.ext ?_⟩
  rw [coe_arithmeticGalois_smul]
  exact hfix σ hσ

private theorem mwfl_place_eq_of_le {Kf F : Type*} [Field Kf] [Field F] [Algebra Kf F]
    {v w : Place Kf F} (hle : v.toValuationSubring ≤ w.toValuationSubring) : v = w := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hπv : v.ord (π : F) = 1 := v.ord_coe_irreducible hπ
  have hm0 : 0 ≤ w.ord (π : F) := (w.mem_iff_ord_nonneg hπ0).mp (hle π.2)
  have key : ∀ f : F, f ≠ 0 → w.ord f = v.ord f * w.ord (π : F) := by
    intro f hf
    have hpz : ((π : F) ^ (-(v.ord f))) ≠ 0 := zpow_ne_zero _ hπ0
    have hu0 : f * (π : F) ^ (-(v.ord f)) ≠ 0 := mul_ne_zero hf hpz
    have hv_u : v.ord (f * (π : F) ^ (-(v.ord f))) = 0 := by
      rw [v.ord_mul hf hpz, v.ord_zpow, hπv]; ring
    have hv_ui : v.ord (f * (π : F) ^ (-(v.ord f)))⁻¹ = 0 := by
      rw [v.ord_inv, hv_u, neg_zero]
    have hw_u : 0 ≤ w.ord (f * (π : F) ^ (-(v.ord f))) :=
      (w.mem_iff_ord_nonneg hu0).mp (hle ((v.mem_iff_ord_nonneg hu0).mpr hv_u.ge))
    have hw_ui : 0 ≤ w.ord (f * (π : F) ^ (-(v.ord f)))⁻¹ :=
      (w.mem_iff_ord_nonneg (inv_ne_zero hu0)).mp
        (hle ((v.mem_iff_ord_nonneg (inv_ne_zero hu0)).mpr hv_ui.ge))
    rw [w.ord_inv] at hw_ui
    have hw_u0 : w.ord (f * (π : F) ^ (-(v.ord f))) = 0 := le_antisymm (by linarith) hw_u
    have hexp := w.ord_mul hf hpz
    rw [w.ord_zpow, hw_u0] at hexp
    linarith
  rcases eq_or_lt_of_le hm0 with hm | hm
  · exfalso
    apply w.ne_top'
    refine SetLike.ext fun z => ⟨fun _ => ValuationSubring.mem_top z, fun _ => ?_⟩
    rcases eq_or_ne z 0 with rfl | hz
    · exact zero_mem _
    · refine (w.mem_iff_ord_nonneg hz).mpr ?_
      rw [key z hz, ← hm, mul_zero]
  · apply Place.ext
    refine le_antisymm hle fun z hz => ?_
    rcases eq_or_ne z 0 with rfl | hz0
    · exact zero_mem _
    · have h1 := (w.mem_iff_ord_nonneg hz0).mp hz
      rw [key z hz0] at h1
      refine (v.mem_iff_ord_nonneg hz0).mpr ?_
      by_contra hneg
      have hneg' := not_le.mp hneg
      nlinarith

set_option synthInstance.maxHeartbeats 800000 in

private theorem mwfl_finite_ord_ne_zero (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) [HasPrincipalDivisors Qbar (FF F₀)] {f : FF F₀} (hf : f ≠ 0) :
    {w : Place Qbar (FF F₀) | w.ord f ≠ 0}.Finite := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := Qbar) (F := FF F₀) f hf
  have h : {w : Place Qbar (FF F₀) | w.ord f ≠ 0} = ↑D.support := by
    ext w
    rw [Set.mem_setOf_eq, ← hD w, Finset.mem_coe, Finsupp.mem_support_iff]
  rw [h]
  exact D.support.finite_toSet

set_option maxHeartbeats 3200000 in

private theorem mwfl_pin (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) [HasPrincipalDivisors Qbar (FF F₀)] (v : Place Qbar (FF F₀)) {e : FF F₀}
    (he0 : e ≠ 0) (hev : v.ord e ≠ 0)
    (L₁ : IntermediateField ℚ Qbar) (hL₁ : FiniteDimensional ℚ L₁)
    (hfixe : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, (∀ a ∈ L₁, σ a = a) →
      arithmeticGalois F₀ σ • e = e) :
    ∃ L : IntermediateField ℚ Qbar, FiniteDimensional ℚ L ∧
      ∀ σ : Qbar ≃ₐ[ℚ] Qbar, (∀ a ∈ L, σ a = a) →
        arithmeticGalois F₀ σ • v = v := by
  have hS : {w : Place Qbar (FF F₀) | w.ord e ≠ 0}.Finite := mwfl_finite_ord_ne_zero F₀ he0
  haveI : Finite ↥({w : Place Qbar (FF F₀) | w.ord e ≠ 0} \ {v}) :=
    (hS.diff).to_subtype
  have hsep : ∀ w : ↥({w : Place Qbar (FF F₀) | w.ord e ≠ 0} \ {v}),
      ∃ z : FF F₀, z ∈ v.toValuationSubring ∧ z ∉ (w : Place Qbar (FF F₀)).toValuationSubring := by
    intro w
    have hwne : (w : Place Qbar (FF F₀)) ≠ v := w.2.2
    have hnle : ¬ v.toValuationSubring ≤ (w : Place Qbar (FF F₀)).toValuationSubring :=
      fun hle => hwne (mwfl_place_eq_of_le hle).symm
    exact SetLike.not_le_iff_exists.mp hnle
  choose sep hsep₁ hsep₂ using hsep
  have hlev : ∀ w : ↥({w : Place Qbar (FF F₀) | w.ord e ≠ 0} \ {v}),
      ∃ L : IntermediateField ℚ Qbar, FiniteDimensional ℚ L ∧
        ∀ σ : Qbar ≃ₐ[ℚ] Qbar, (∀ a ∈ L, σ a = a) →
          arithmeticGalois F₀ σ • sep w = sep w :=
    fun w => mwfl_element_level F₀ (sep w)
  choose lev hlevfd hlevfix using hlev
  haveI : ∀ w, FiniteDimensional ℚ (lev w) := hlevfd
  haveI := hL₁
  refine ⟨L₁ ⊔ ⨆ w, lev w, IntermediateField.finiteDimensional_sup _ _, fun σ hσ => ?_⟩
  by_contra hne
  have h0 := SemilinearAut.ord_smul (arithmeticGalois F₀ σ) v e
  rw [hfixe σ (fun a ha => hσ a (mwfl_mem_left ha))] at h0
  have h1 : (arithmeticGalois F₀ σ • v).ord e ≠ 0 := by
    rw [h0]; exact hev
  set w : ↥({w : Place Qbar (FF F₀) | w.ord e ≠ 0} \ {v}) :=
    ⟨arithmeticGalois F₀ σ • v, ⟨h1, hne⟩⟩ with hw
  have hzfix : arithmeticGalois F₀ σ • sep w = sep w :=
    hlevfix w σ (fun a ha => hσ a (mwfl_mem_right (mwfl_mem_iSup lev w ha)))
  have hz' : arithmeticGalois F₀ σ • sep w ∈
      (arithmeticGalois F₀ σ • v).toValuationSubring := by
    rw [SemilinearAut.smul_toValuationSubring]
    exact ValuationSubring.smul_mem_pointwise_smul _ _ _ (hsep₁ w)
  rw [hzfix] at hz'
  exact hsep₂ w hz'

private theorem mwfl_place_level_hpd (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) [HasPrincipalDivisors Qbar (FF F₀)] (v : Place Qbar (FF F₀)) :
    ∃ L : IntermediateField ℚ Qbar, FiniteDimensional ℚ L ∧
      ∀ σ : Qbar ≃ₐ[ℚ] Qbar, (∀ a ∈ L, σ a = a) →
        arithmeticGalois F₀ σ • v = v := by
  obtain ⟨z, hz⟩ : ∃ z : FF F₀, z ∉ v.toValuationSubring := by
    by_contra h
    exact v.ne_top' (SetLike.ext fun x =>
      ⟨fun _ => ValuationSubring.mem_top x,
       fun _ => Classical.byContradiction fun hx => h ⟨x, hx⟩⟩)
  have hz0 : z ≠ 0 := fun h => hz (h ▸ zero_mem _)
  have hzord : v.ord z < 0 := by
    by_contra hge
    exact hz ((v.mem_iff_ord_nonneg hz0).mpr (not_lt.mp hge))
  have hg0 : z⁻¹ ≠ 0 := inv_ne_zero hz0
  have hgord : 0 < v.ord z⁻¹ := by
    rw [v.ord_inv]
    omega
  obtain ⟨L₁, hL₁, hfix⟩ := mwfl_element_level F₀ z⁻¹
  exact mwfl_pin F₀ v hg0 hgord.ne' L₁ hL₁ hfix

theorem solution
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (hF₀ : ∃ x : F₀, Transcendental ℚ x ∧
      FiniteDimensional (IntermediateField.adjoin ℚ ({x} : Set F₀)) F₀)
    (v : AlgebraicCurve.Place (AlgebraicClosure ℚ)
      (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀)) :
    ∃ L₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L₀ ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ L₀.fixingSubgroup →
        ModularCurve.arithmeticGalois F₀ σ • v = v := by
  haveI := mwfl_hasPrincipalDivisors F₀ hF₀
  obtain ⟨L, hL, hfix⟩ := mwfl_place_level_hpd F₀ v
  exact ⟨L, hL, fun σ hσ =>
    hfix σ ((IntermediateField.mem_fixingSubgroup_iff L σ).mp hσ)⟩

end

end S_ModularCurve_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq_place_laurentBaseChange
end P2MW
export P2MW.S_ModularCurve_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq_place_laurentBaseChange (solution)
