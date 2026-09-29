-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_section_comp_one_placeOfPoint_eq_reduceSnd_of_isStrictSnd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/f3b06112-e72d-5fce-98df-66898fa048c2

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_section_comp_one_placeOfPoint_eq_reduceSnd_of_isStrictSnd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

set_option maxHeartbeats 3200000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)

    (hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0)) :
    ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W →
      ∃ (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C),
        barPt A ≫ u.1 = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ∧
        uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1 ∧
        uκ ≫ pullback.snd _ _ = 𝟙 _ ∧
        (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∧
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W ∧
        uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 0).base := by
  intro W hW
  have hp : p.Prime := Fact.out
  have hsub : algebraMap (↥A) (AlgebraicClosure ℚ) = A.subtype := RingHom.ext fun _ => rfl

  haveI : IsProper (toBase p (ΓM M H) hj) := 𝔛.isProper
  have hE : ValuativeCriterion.Existence (toBase p (ΓM M H) hj) := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) (toBase p (ΓM M H) hj) := by
      rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
    exact h.1
  let y := (𝔛.Meta).pointEquivPlace.symm W
  let i₁ : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ X p (ΓM M H) hj := y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _
  have hsq : CommSq i₁ (Spec.map (CommRingCat.ofHom (algebraMap (↥A) (AlgebraicClosure ℚ))))
      (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) := by
    refine ⟨?_⟩
    show (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _) ≫ toBase p (ΓM M H) hj = _
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, y.2, Category.id_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, hsub, hρ]
  let S : ValuativeCommSq (toBase p (ΓM M H) hj) :=
    { R := ↥A, K := AlgebraicClosure ℚ, i₁ := i₁, i₂ := Spec.map (CommRingCat.ofHom ρ), commSq := hsq }
  obtain ⟨⟨l, hl₁, hl₂⟩⟩ := (hE S).exists_lift
  let u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj) := ⟨l, hl₂⟩
  have hu : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ := by
    show barPt A ≫ l = i₁
    rw [show barPt A = Spec.map (CommRingCat.ofHom (algebraMap (↥A) (AlgebraicClosure ℚ))) by rw [hsub]]
    exact hl₁

  have huκc : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) ≫ toBase p (ΓM M H) hj =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) := by
    rw [Category.assoc, u.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Category.id_comp]
  let uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) :=
    pullback.lift (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (𝟙 _) huκc
  have huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1 := pullback.lift_fst _ _ _
  have huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  set c := uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) with hc

  haveI : IsSeparated (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  haveI : IsClosedImmersion uκ := by
    have : IsClosedImmersion (uκ ≫ pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) := by
      rw [huκ₂]; infer_instance
    exact IsClosedImmersion.of_comp uκ (pullback.snd _ _)
  have hc_closed : IsClosed ({c} : Set (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) := by
    have hr : Set.range uκ.base = {c} := by
      ext z
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨t, rfl⟩
        rw [hc, Subsingleton.elim t (IsLocalRing.closedPoint (ResidueField ↥A))]
      · rintro rfl
        exact ⟨_, rfl⟩
    rw [← hr]
    exact (IsClosedImmersion.base_closed (f := uκ)).isClosed_range
  haveI := 𝔛.efib_iso A hA ρ hρ
  have hinv : ∀ x, (𝔛.efib A hA ρ hρ).base ((inv (𝔛.efib A hA ρ hρ)).base x) = x := by
    intro x
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have hinv' : ∀ P, (inv (𝔛.efib A hA ρ hρ)).base ((𝔛.efib A hA ρ hρ).base P) = P := by
    intro P
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
    rfl
  have hclosed : ∀ (i : Fin 2) (x : fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)),
      (𝔛.comp A hA ρ hρ i).base x = c → (inv (𝔛.efib A hA ρ hρ)).base x ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C := by
    intro i x hx
    haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ i
    have hxc : IsClosed ({x} : Set (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) := by
      have : ({x} : Set _) = (𝔛.comp A hA ρ hρ i).base ⁻¹' {c} := by
        ext z
        simp only [Set.mem_singleton_iff, Set.mem_preimage]
        constructor
        · rintro rfl; exact hx
        · intro hz; exact (𝔛.comp A hA ρ hρ i).isClosedEmbedding.injective (hz.trans hx.symm)
      rw [this]
      exact hc_closed.preimage (𝔛.comp A hA ρ hρ i).base.hom.continuous
    show IsClosed ({(inv (𝔛.efib A hA ρ hρ)).base x} : Set _)
    have : ({(inv (𝔛.efib A hA ρ hρ)).base x} : Set _) = (𝔛.efib A hA ρ hρ).base ⁻¹' {x} := by
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl; exact hinv x
      · intro hz; rw [← hz, hinv']
    rw [this]
    exact hxc.preimage (𝔛.efib A hA ρ hρ).base.hom.continuous

  have hpN : ¬ p ∣ M / p := by
    rintro ⟨k, hk⟩
    apply hpM2
    refine ⟨k, ?_⟩
    rw [pow_two, mul_assoc, ← hk, Nat.mul_div_cancel' hpM]
  have hδφ : ∀ v, δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v) =
      qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (δ v) := by
    intro v
    rw [hδ, hδ]
    exact (ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul (ResidueField ↥A) p (M / p) hpN
      (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb) v).symm

  have key : ∀ x₀ : fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ), (𝔛.comp A hA ρ hρ 0).base x₀ = c → False := by
    intro x₀ hx₀
    have hP₀pt : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base ((inv (𝔛.efib A hA ρ hρ)).base x₀) = c := by
      rw [Scheme.Hom.comp_apply, hinv, hx₀]
    have hr₁ := hcompat 0 y u hu uκ huκ₁ huκ₂ ⟨_, hclosed 0 x₀ hx₀⟩ hP₀pt
    have hr₂ := hcompat' 0 y u hu uκ huκ₁ huκ₂ ⟨_, hclosed 0 x₀ hx₀⟩ hP₀pt
    rw [if_pos rfl, Equiv.apply_symm_apply] at hr₁ hr₂

    obtain ⟨hcol, hnf⟩ := hW
    apply hnf
    show qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p
        (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W))) =
      Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W
    rw [← hcol, ← hδφ, ← hr₁, ← hr₂]

  have hnot : c ∉ Set.range (𝔛.comp A hA ρ hρ 0).base := by
    rintro ⟨x₀, hx₀⟩; exact key x₀ hx₀
  rcases 𝔛.comp_jointly_surjective A hA ρ hρ c with ⟨x₀, hx₀⟩ | ⟨x₁, hx₁⟩
  · exact (key x₀ hx₀).elim
  · have hP₁pt : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base ((inv (𝔛.efib A hA ρ hρ)).base x₁) = c := by
      rw [Scheme.Hom.comp_apply, hinv, hx₁]
    have hr := hcompat 1 y u hu uκ huκ₁ huκ₂ ⟨_, hclosed 1 x₁ hx₁⟩ hP₁pt
    rw [if_neg (by decide), Equiv.apply_symm_apply] at hr
    exact ⟨u, uκ, ⟨_, hclosed 1 x₁ hx₁⟩, hu, huκ₁, huκ₂, hP₁pt, hr, hnot⟩

end S_ModularCurve_XHDRModelAtP_exists_section_comp_one_placeOfPoint_eq_reduceSnd_of_isStrictSnd
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_section_comp_one_placeOfPoint_eq_reduceSnd_of_isStrictSnd (solution)
