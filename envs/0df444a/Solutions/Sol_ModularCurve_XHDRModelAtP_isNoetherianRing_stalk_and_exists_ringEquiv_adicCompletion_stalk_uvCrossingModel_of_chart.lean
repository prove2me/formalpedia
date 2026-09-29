-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.isNoetherianRing_stalk_and_exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/469a8a6d-d0ac-5220-b892-c57f9531ae9e

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_chart_baseChange_mem_and_flat_and_map_maximalIdeal_eq_and_isIso_residueFieldMap_and_germ_eq_of_chart
import Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_of_flat_of_map_maximalIdeal_eq_of_isIso_residueFieldMap
import Theorems.Thm_ModularCurve_XHDRModelAtP_isIntegral_xO_of_mem_maximalIdeal
import Theorems.Thm_IsLocalRing_exists_adicCompletion_ringEquiv_of_flat_of_map_maximalIdeal_eq_of_residue_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_isNoetherianRing_stalk_and_exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_of_chart
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial

open scoped MatrixGroups

namespace Ws5B13N2

theorem power {O O' : Type} [CommRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    (σ : O →+* O') (p e : ℕ) (he : 1 ≤ e)
    (hp0 : ((p : ℕ) : O') ≠ 0) (hp : ((p : ℕ) : O') ∈ IsLocalRing.maximalIdeal O')
    (ϖ' : O') (hϖ' : IsLocalRing.maximalIdeal O' = Ideal.span {ϖ'}) :
    ∃ (E : ℕ) (_ : 1 ≤ E) (w : O'ˣ), σ (((p : ℕ) : O) ^ e) = (w : O') * ϖ' ^ E := by
  have hirr : Irreducible ϖ' := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal ϖ' ?ne hϖ'
  case ne =>
    rintro rfl
    apply hp0
    have : IsLocalRing.maximalIdeal O' = ⊥ := by rw [hϖ', Ideal.span_singleton_eq_bot]
    simpa [this] using hp
  obtain ⟨k, u, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hirr
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hk
    exact (IsLocalRing.mem_maximalIdeal _).mp hp (hk ▸ u.isUnit)
  refine ⟨k * e, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hk0 (by omega)), u ^ e, ?_⟩
  rw [map_pow, map_natCast, hk, mul_pow, Units.val_pow_eq_pow_val, pow_mul]

theorem completion_transport {R S : Type} [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] (θ : R ≃+* S) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+* AdicCompletion (IsLocalRing.maximalIdeal S) S,
      ∀ r : R, e (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r) =
        algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (θ r) := by
  letI : Algebra R S := θ.toRingHom.toAlgebra
  have halg : (algebraMap R S : R →+* S) = θ.toRingHom := rfl
  have hθloc : IsLocalHom θ.toRingHom := ⟨(isLocalHom_equiv θ).map_nonunit⟩
  haveI hloc : IsLocalHom (algebraMap R S) := by rw [halg]; exact hθloc

  let L : S ≃ₗ[R] R :=
    { θ.symm.toAddEquiv with
      map_smul' := fun r s => by
        show θ.symm (algebraMap R S r * s) = r * θ.symm s
        rw [halg]
        show θ.symm (θ r * s) = r * θ.symm s
        rw [map_mul, RingEquiv.symm_apply_apply] }
  haveI : Module.Flat R S := Module.Flat.of_linearEquiv L
  have hmax : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S := by
    rw [halg]
    have hc : Ideal.comap θ.toRingHom (IsLocalRing.maximalIdeal S) = IsLocalRing.maximalIdeal R :=
      ((IsLocalRing.local_hom_TFAE θ.toRingHom).out 0 4).mp hθloc
    rw [← hc, Ideal.map_comap_of_surjective θ.toRingHom θ.surjective]
  have hres : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R S)) := by
    intro s
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective s
    refine ⟨IsLocalRing.residue R (θ.symm s), ?_⟩
    rw [IsLocalRing.ResidueField.map_residue, halg]
    show IsLocalRing.residue S (θ (θ.symm s)) = _
    rw [RingEquiv.apply_symm_apply]
  obtain ⟨e, he⟩ := IsLocalRing.exists_adicCompletion_ringEquiv_of_flat_of_map_maximalIdeal_eq_of_residue_surjective
    (R := R) (S := S) hmax hres
  exact ⟨e, fun r => by rw [he r]; rfl⟩

end Ws5B13N2

set_option maxHeartbeats 2400000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)

    (jO : O →+* AlgebraicClosure ℚ) (hjO : jO.comp ρO = algebraMap (R p) (AlgebraicClosure ℚ))
    (ιA : O →+* ↥A) (hιA : A.subtype.comp ιA = jO) (hιAκ : (IsLocalRing.residue ↥A).comp ιA = toκ)

    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (e : ℕ) (he : 1 ≤ e) (U : (XO (ΓM M H) hj ρO).Opens) (hxU : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n ∈ U)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e))
    (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e)))) = U.ι ≫ pullback.snd _ _)
    (hfib : ∀ y : ↥(U : Scheme.{0}),
      (CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∧ CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ↔ U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n)
    (hpt : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
      (f.stalkMap y).hom.Flat ∧ Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧ IsIso (f.residueFieldMap y))
    (het : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n → ∃ V : (U : Scheme.{0}).Opens, y ∈ V ∧ Etale (V.ι ≫ f))
    (hor₁ : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal → U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (hor₂ : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal → U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (hor₃ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal)
    (hor₄ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal)

    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    (σ : O →+* O') (ιA' : O' →+* ↥A) (hσ : ιA'.comp σ = ιA) (hιA'inj : Function.Injective ιA') (hιA'loc : IsLocalHom ιA')
    (jO' : O' →+* AlgebraicClosure ℚ) (hjO' : jO'.comp (σ.comp ρO) = algebraMap (R p) (AlgebraicClosure ℚ)) (hιA'j : A.subtype.comp ιA' = jO')
    (htoκ' : ((IsLocalRing.residue ↥A).comp ιA').comp (σ.comp ρO) = (IsLocalRing.residue ↥A).comp ρ) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prJ : XQ ⟶ XO (ΓM M H) hj ρO :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])
    letI VM : (𝔛.Meta).C.Opens := 𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ U)
    letI Q := CrossingQuotient O (((p : ℕ) : O) ^ e)
    letI φ : Q →+* Γ(CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
    letI gv : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.V (((p : ℕ) : O) ^ e))))
    letI gu : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.U (((p : ℕ) : O) ^ e))))
    letI bc' := bcMap (ΓM M H) hj (σ.comp ρO) ((IsLocalRing.residue ↥A).comp ιA') htoκ'
    letI xn' : ↥(XO (ΓM M H) hj (σ.comp ρO)) := (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc').base n
    letI prJ' : XQ ⟶ XO (ΓM M H) hj (σ.comp ρO) :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO'])
    letI prσ : XO (ΓM M H) hj (σ.comp ρO) ⟶ XO (ΓM M H) hj ρO :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom σ)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
    letI B := (XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalk xn'
    letI σB : O' →+* ↥B := ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ ⊤ xn' trivial).hom.comp
      (((XO.toBase (ΓM M H) hj (σ.comp ρO)).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)
    ∀ (ϖ' : O'), IsLocalRing.maximalIdeal O' = Ideal.span {ϖ'} →
    IsNoetherianRing ↥B ∧ IsDomain ↥B ∧
    ∃ (E' : ℕ) (_ : 1 ≤ E') (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W') W')
      (σ' : O' →+* W') (_ : IsLocalRing.maximalIdeal W' = Ideal.span {σ' ϖ'})
      (_ : Function.Surjective ((IsLocalRing.residue W').comp σ'))
      (ι' : AdicCompletion (IsLocalRing.maximalIdeal ↥B) ↥B ≃+* UVCrossingModel W' ((σ' ϖ') ^ E')),
      (∀ o : O', ι' (algebraMap ↥B (AdicCompletion (IsLocalRing.maximalIdeal ↥B) ↥B) (σB o)) = UVCrossingModel.const ((σ' ϖ') ^ E') (σ' o)) ∧
      ∃ hmem : xn' ∈ prσ ⁻¹ᵁ (U.ι ''ᵁ ⊤),
        (∃ wu : (UVCrossingModel W' ((σ' ϖ') ^ E'))ˣ,
          ι' (algebraMap ↥B (AdicCompletion (IsLocalRing.maximalIdeal ↥B) ↥B) (((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ (prσ ⁻¹ᵁ (U.ι ''ᵁ ⊤)) xn' hmem).hom ((prσ.app (U.ι ''ᵁ ⊤)).hom gu))) = UVCrossingModel.U ((σ' ϖ') ^ E') * (wu : UVCrossingModel W' ((σ' ϖ') ^ E'))) ∧
        ι' (algebraMap ↥B (AdicCompletion (IsLocalRing.maximalIdeal ↥B) ↥B) (((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ (prσ ⁻¹ᵁ (U.ι ''ᵁ ⊤)) xn' hmem).hom ((prσ.app (U.ι ''ᵁ ⊤)).hom gv))) = UVCrossingModel.V ((σ' ϖ') ^ E') := by
  intro ϖ' hϖ'
  classical

  let Q := CrossingQuotient O (((p : ℕ) : O) ^ e)
  let φ : Q →+* Γ(CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
  let gv : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.V (((p : ℕ) : O) ^ e))))
  let gu : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.U (((p : ℕ) : O) ^ e))))
  let bc' := bcMap (ΓM M H) hj (σ.comp ρO) ((IsLocalRing.residue ↥A).comp ιA') htoκ'
  let xn' : ↥(XO (ΓM M H) hj (σ.comp ρO)) := (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc').base n
  let prσ : XO (ΓM M H) hj (σ.comp ρO) ⟶ XO (ΓM M H) hj ρO :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom σ)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
  let B := (XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalk xn'
  let σB : O' →+* ↥B := ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ ⊤ xn' trivial).hom.comp
      (((XO.toBase (ΓM M H) hj (σ.comp ρO)).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)

  have hpA : ((p : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    simp at hA ⊢
    exact hA
  have hpA0 : ((p : ℕ) : ↥A) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp0' : ((p : ℕ) : O') ≠ 0 := by
    intro h
    apply hpA0
    have h' := congrArg ιA' h
    rwa [map_natCast, map_zero] at h'
  have hp' : ((p : ℕ) : O') ∈ IsLocalRing.maximalIdeal O' := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' := hu.map ιA'
    rw [map_natCast] at hu'
    exact (IsLocalRing.mem_maximalIdeal _).mp hpA hu'

  obtain ⟨E, hE, w, hw⟩ := Ws5B13N2.power σ p e he hp0' hp' ϖ' hϖ'

  haveI := 𝔛.isProper
  haveI : IsLocallyNoetherian (XO (ΓM M H) hj (σ.comp ρO)) :=
    LocallyOfFiniteType.isLocallyNoetherian (XO.toBase (ΓM M H) hj (σ.comp ρO))
  haveI : IsIntegral (XO (ΓM M H) hj (σ.comp ρO)) :=
    ModularCurve.XHDRModelAtP.isIntegral_xO_of_mem_maximalIdeal p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O' (σ.comp ρO) hp0' hp'
  have hN : IsNoetherianRing ↥B := by
    show IsNoetherianRing ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalk xn')
    infer_instance
  have hD : IsDomain ↥B := by
    show IsDomain ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalk xn')
    infer_instance
  haveI hlocB : IsLocalRing ↥B := by
    show IsLocalRing ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalk xn')
    infer_instance
  refine ⟨hN, hD, ?_⟩

  have hN2a := ModularCurve.XHDRModelAtP.exists_chart_baseChange_mem_and_flat_and_map_maximalIdeal_eq_and_isIso_residueFieldMap_and_germ_eq_of_chart
    p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ jO hjO ιA hιA hιAκ n e he U hxU f hover hfib hpt het hor₁ hor₂ hor₃ hor₄
    O' σ ιA' hσ hιA'inj hιA'loc jO' hjO' hιA'j htoκ'
  obtain ⟨hmem, g, hgover, hvert, hpt', hgermU, hgermV⟩ := hN2a

  let ιY := (prσ ⁻¹ᵁ (U.ι ''ᵁ ⊤)).ι
  let y : ↥(↑(prσ ⁻¹ᵁ (U.ι ''ᵁ ⊤)) : Scheme.{0}) := ⟨xn', hmem⟩
  let θ : ↥B ≃+* ↥((↑(prσ ⁻¹ᵁ (U.ι ''ᵁ ⊤)) : Scheme.{0}).presheaf.stalk y) :=
    (asIso (ιY.stalkMap y)).commRingCatIsoToRingEquiv
  have hθ : ∀ b, θ b = (ιY.stalkMap y).hom b := fun b => rfl
  have hNY : IsNoetherianRing ↥((↑(prσ ⁻¹ᵁ (U.ι ''ᵁ ⊤)) : Scheme.{0}).presheaf.stalk y) :=
    isNoetherianRing_of_ringEquiv ↥B θ

  have hC1 := @AlgebraicGeometry.exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_of_flat_of_map_maximalIdeal_eq_of_isIso_residueFieldMap
      O' _ _ _ ϖ' hϖ' E hE w (σ (((p : ℕ) : O) ^ e)) hw (↑(prσ ⁻¹ᵁ (U.ι ''ᵁ ⊤))) g y hNY hvert hpt'
  obtain ⟨W', i1, i2, i3, i4, σ', hσ'ϖ, hσ'res, ιC, hrest⟩ := hC1

  haveI hlocY : IsLocalRing ↥((↑(prσ ⁻¹ᵁ (U.ι ''ᵁ ⊤)) : Scheme.{0}).presheaf.stalk y) :=
    (↑(prσ ⁻¹ᵁ (U.ι ''ᵁ ⊤)) : Scheme.{0}).toLocallyRingedSpace.isLocalRing y
  have hct := @Ws5B13N2.completion_transport ↥B _ _ _ hN hNY hlocB hlocY θ
  obtain ⟨ê, hê⟩ := hct

  have hψ : ∀ o : O',
      (ιY.appTop).hom (((XO.toBase (ΓM M H) hj (σ.comp ρO)).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom o)) =
        (g.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O' (σ (((p : ℕ) : O) ^ e))))).inv.hom
          (algebraMap O' (CrossingQuotient O' (σ (((p : ℕ) : O) ^ e))) o)) := fun o => by
    have h1 := congrArg (fun χ => (Scheme.Hom.appTop χ).hom ((Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom o)) hgover
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h1
    have h2 := congrArg (fun χ => χ.hom o)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap O' (CrossingQuotient O' (σ (((p : ℕ) : O) ^ e))))))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h2
    rw [← h2] at h1
    exact h1.symm
  have hθσ : ∀ o : O', θ (σB o) = ((↑(prσ ⁻¹ᵁ (U.ι ''ᵁ ⊤)) : Scheme.{0}).presheaf.germ ⊤ y trivial).hom ((g.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O' (σ (((p : ℕ) : O) ^ e))))).inv.hom (algebraMap O' (CrossingQuotient O' (σ (((p : ℕ) : O) ^ e))) o))) := fun o => by
    rw [← hψ o, hθ]
    exact Scheme.Hom.germ_stalkMap_apply ιY ⊤ y trivial _
  let GU : ↥B := ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ (prσ ⁻¹ᵁ (U.ι ''ᵁ ⊤)) xn' hmem).hom ((prσ.app (U.ι ''ᵁ ⊤)).hom gu)
  let GV : ↥B := ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ (prσ ⁻¹ᵁ (U.ι ''ᵁ ⊤)) xn' hmem).hom ((prσ.app (U.ι ''ᵁ ⊤)).hom gv)
  have hgermU' : θ GU = ((↑(prσ ⁻¹ᵁ (U.ι ''ᵁ ⊤)) : Scheme.{0}).presheaf.germ ⊤ y trivial).hom
      ((g.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O' (σ (((p : ℕ) : O) ^ e))))).inv.hom
        (CrossingQuotient.U (σ (((p : ℕ) : O) ^ e))))) := hgermU
  have hgermV' : θ GV = ((↑(prσ ⁻¹ᵁ (U.ι ''ᵁ ⊤)) : Scheme.{0}).presheaf.germ ⊤ y trivial).hom
      ((g.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O' (σ (((p : ℕ) : O) ^ e))))).inv.hom
        (CrossingQuotient.V (σ (((p : ℕ) : O) ^ e))))) := hgermV
  refine ⟨E, hE, W', i1, i2, i3, i4, σ', hσ'ϖ, hσ'res, ê.trans ιC, ?_, hmem, ?_, ?_⟩
  · intro o
    show (ê.trans ιC) (algebraMap ↥B (AdicCompletion (IsLocalRing.maximalIdeal ↥B) ↥B) (σB o)) = _
    rw [RingEquiv.trans_apply, hê, hθσ]
    exact hrest.1 o
  · refine Exists.imp (fun w' h => ?_) hrest.2.1
    show (ê.trans ιC) (algebraMap ↥B (AdicCompletion (IsLocalRing.maximalIdeal ↥B) ↥B) GU) = _
    rw [RingEquiv.trans_apply, hê, hgermU']
    exact h
  · show (ê.trans ιC) (algebraMap ↥B (AdicCompletion (IsLocalRing.maximalIdeal ↥B) ↥B) GV) = _
    rw [RingEquiv.trans_apply, hê, hgermV']
    exact hrest.2.2

end S_ModularCurve_XHDRModelAtP_isNoetherianRing_stalk_and_exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_of_chart
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_isNoetherianRing_stalk_and_exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_of_chart (solution)
