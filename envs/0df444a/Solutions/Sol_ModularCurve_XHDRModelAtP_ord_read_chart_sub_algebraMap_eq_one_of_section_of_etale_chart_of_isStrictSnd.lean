-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.ord_read_chart_sub_algebraMap_eq_one_of_section_of_etale_chart_of_isStrictSnd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/335e495e-84f1-5bbc-b50c-5c7ab1a7b070

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Theorems.Thm_ModularCurve_XHDRModelAtP_isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
import Theorems.Thm_AlgebraicCurve_CurveModel_ord_placeOfPoint_ffEquiv_symm_algebraMap_eq_one_of_maximalIdeal_eq_span
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_ord_read_chart_sub_algebraMap_eq_one_of_section_of_etale_chart_of_isStrictSnd

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

set_option maxHeartbeats 1600000 in
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
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))

    (Q : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQ : Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q)
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hu : barPt A ≫ u.1 = ((𝔛.Meta).pointEquivPlace.symm Q).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP0Q : (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q)
    (hsmooth : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 0).base)

    (U : (XO (ΓM M H) hj ρ).Opens) (hxU : (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) ∈ U)
    (f : (U : Scheme.{0}) ⟶ Spec (CommRingCat.of (Polynomial ↥A)))
    (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥A (Polynomial ↥A))) = U.ι ≫ pullback.snd _ _)
    (het : Etale f)
    (hpt : f.base ⟨_, hxU⟩ = (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ↥A)))).base (IsLocalRing.closedPoint ↥A))
    :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    letI bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl

    letI x₀ : ↥(XO (ΓM M H) hj ρ) := bcA.base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))

    letI φT : Polynomial ↥A →+* Γ(Spec (CommRingCat.of (Polynomial ↥A)), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv.hom
    letI gT : Γ(XO (ΓM M H) hj ρ, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φT Polynomial.X))
    ∀ hgen : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤)),
    letI read : Γ(XO (ΓM M H) hj ρ, U.ι ''ᵁ ⊤) →+* ↥(xHFunctionFieldBar M H) :=
      (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
          ((𝔛.eeta.app (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp (prA.app (U.ι ''ᵁ ⊤)).hom))
    letI param : ↥(xHFunctionFieldBar M H) := read gT
    ∀ (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), W.IsRational →
      ∀ (s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})),
        s ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ →
        barPt A ≫ s ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prA →
        U.ι.base (s.base (IsLocalRing.closedPoint ↥A)) = x₀ →
      ∀ (χ : Polynomial ↥A →+* ↥A), s ≫ f = Spec.map (CommRingCat.ofHom χ) →
        χ Polynomial.X ∈ maximalIdeal ↥A ∧
        param ∈ W.toValuationSubring ∧ W.evalAt param = ((χ Polynomial.X : ↥A) : AlgebraicClosure ℚ) ∧
        W.ord (param - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((χ Polynomial.X : ↥A) : AlgebraicClosure ℚ)) = 1 := by
  intro hgen W hW s hs_sec hs_gen hs_pt χ hχ

  let XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
  let prA : XQ ⟶ XO (ΓM M H) hj ρ :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
  let bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl
  let x₀ : ↥(XO (ΓM M H) hj ρ) := bcA.base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
  let φT : Polynomial ↥A →+* Γ(Spec (CommRingCat.of (Polynomial ↥A)), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv.hom
  let gT : Γ(XO (ΓM M H) hj ρ, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φT Polynomial.X))
  let read : Γ(XO (ΓM M H) hj ρ, U.ι ''ᵁ ⊤) →+* ↥(xHFunctionFieldBar M H) :=
    (𝔛.Meta).ffEquiv.symm.toRingHom.comp
      (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
        ((𝔛.eeta.app (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp (prA.app (U.ι ''ᵁ ⊤)).hom))
  let param : ↥(xHFunctionFieldBar M H) := read gT
  let c : ↥A := χ Polynomial.X

  have hχC : χ.comp Polynomial.C = RingHom.id ↥A := by
    have h : Spec.map (CommRingCat.ofHom χ) ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥A (Polynomial ↥A))) = 𝟙 _ := by
      rw [← hχ, Category.assoc, hover, hs_sec]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  have hχeval : χ = Polynomial.evalRingHom c := by
    apply Polynomial.ringHom_ext
    · intro a; have := DFunLike.congr_fun hχC a; simpa using this
    · simp [c]

  have hspt : s.base (IsLocalRing.closedPoint ↥A) = ⟨x₀, hxU⟩ := by
    apply U.ι.isOpenEmbedding.injective
    exact hs_pt

  have h1 : c ∈ maximalIdeal ↥A := by
    have hfs : f.base (s.base (IsLocalRing.closedPoint ↥A)) =
        (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ↥A)))).base (IsLocalRing.closedPoint ↥A) := by
      rw [hspt]; exact hpt
    rw [← Scheme.Hom.comp_apply, hχ] at hfs

    have key : (PrimeSpectrum.comap χ (IsLocalRing.closedPoint ↥A)).asIdeal =
        (PrimeSpectrum.comap (Polynomial.evalRingHom (0 : ↥A)) (IsLocalRing.closedPoint ↥A)).asIdeal := by
      exact congrArg PrimeSpectrum.asIdeal hfs
    have hX0 : Polynomial.X ∈ (PrimeSpectrum.comap (Polynomial.evalRingHom (0 : ↥A)) (IsLocalRing.closedPoint ↥A)).asIdeal := by
      show Polynomial.evalRingHom (0 : ↥A) Polynomial.X ∈ maximalIdeal ↥A
      simp
    rw [← key] at hX0
    exact hX0

  let y := (𝔛.Meta).pointEquivPlace.symm W
  have hyW : (𝔛.Meta).pointEquivPlace y = W := Equiv.apply_symm_apply _ _
  let W' : (XO (ΓM M H) hj ρ).Opens := U.ι ''ᵁ ⊤
  let gA : (𝔛.Meta).C ⟶ XO (ΓM M H) hj ρ := 𝔛.eeta ≫ prA
  let V : (𝔛.Meta).C.Opens := 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ W')
  haveI hVne : Nonempty (Scheme.Opens.toScheme V) := ⟨⟨genericPoint (𝔛.Meta).C, hgen⟩⟩
  let sect : Γ((𝔛.Meta).C, V) := (𝔛.eeta.app (prA ⁻¹ᵁ W')).hom ((prA.app W').hom gT)
  have hparam : param = (𝔛.Meta).ffEquiv.symm ((𝔛.Meta).C.germToFunctionField V sect) := rfl
  have hz : ⊤ ≤ y.1 ⁻¹ᵁ V := by
    intro q _
    show prA.base (𝔛.eeta.base (y.1.base q)) ∈ (U.ι ''ᵁ ⊤ : (XO (ΓM M H) hj ρ).Opens)
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hs_gen, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact ⟨s.base ((barPt A).base q), trivial, rfl⟩
  obtain ⟨hmem, hnon⟩ :=
    AlgebraicCurve.CurveModel.ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
      (𝔛.Meta) V sect y hz
  rw [hyW] at hmem hnon
  have h2 : param ∈ W.toValuationSubring := hparam ▸ hmem
  have hsect : sect = (gA.app W') gT := by
    show _ = ((𝔛.eeta ≫ prA).app W') gT
    rw [Scheme.Hom.comp_app]; rfl
  have hB : (y.1.appLE V ⊤ hz) sect = ((y.1 ≫ gA).appLE W' ⊤ hz) gT := by
    rw [hsect, Scheme.Hom.comp_appLE]; rfl

  have appLE_congr : ∀ {X' Y' : Scheme.{0}} {m m' : X' ⟶ Y'} (_ : m = m') (U₁ : Y'.Opens) (V₁ : X'.Opens)
      (e : V₁ ≤ m ⁻¹ᵁ U₁) (e' : V₁ ≤ m' ⁻¹ᵁ U₁) (x : Γ(Y', U₁)), (m.appLE U₁ V₁ e) x = (m'.appLE U₁ V₁ e') x := by
    intro X' Y' m m' h; subst h; intro U₁ V₁ e e' x; rfl
  let t₀ : Γ((U : Scheme.{0}), ⊤) := f.appTop (φT Polynomial.X)
  have e₁ : (⊤ : (Spec (CommRingCat.of (AlgebraicClosure ℚ))).Opens) ≤ (barPt A ≫ s ≫ U.ι) ⁻¹ᵁ W' := by
    intro q _
    show (barPt A ≫ s ≫ U.ι).base q ∈ (U.ι ''ᵁ ⊤ : (XO (ΓM M H) hj ρ).Opens)
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact ⟨s.base ((barPt A).base q), trivial, rfl⟩
  have hC : ((y.1 ≫ gA).appLE W' ⊤ hz) gT = ((barPt A ≫ s ≫ U.ι).appLE W' ⊤ e₁) gT :=
    appLE_congr hs_gen.symm W' ⊤ hz e₁ gT
  have eU : (⊤ : (U : Scheme.{0}).Opens) ≤ U.ι ⁻¹ᵁ W' := fun q _ => ⟨q, trivial, rfl⟩
  have hD1 : ((barPt A ≫ s ≫ U.ι).appLE W' ⊤ e₁) gT = ((barPt A ≫ s).appLE ⊤ ⊤ le_top) ((U.ι.appLE W' ⊤ eU) gT) := by
    have hcomp := Scheme.Hom.appLE_comp_appLE (barPt A ≫ s) U.ι W' ⊤ ⊤ eU le_top
    conv_rhs => rw [← CommRingCat.comp_apply, hcomp]
    exact appLE_congr (Category.assoc (barPt A) s U.ι).symm W' ⊤ e₁ _ gT
  have hUι : (U.ι.appLE W' ⊤ eU) gT = t₀ := by
    have h := Scheme.Hom.appIso_hom' U.ι ⊤
    have : (U.ι.appLE W' ⊤ eU) gT = (U.ι.appIso ⊤).hom gT := by rw [h]
    rw [this]
    exact (U.ι.appIso ⊤).inv_hom_id_apply t₀
  have hD2 : ((barPt A ≫ s).appLE ⊤ ⊤ le_top) t₀ = (barPt A).appTop (s.appTop t₀) := by
    have hcomp := Scheme.Hom.appLE_comp_appLE (barPt A) s ⊤ ⊤ ⊤ le_top le_top
    rw [← hcomp, CommRingCat.comp_apply]
    show _ = (barPt A).app ⊤ ((s.app ⊤) t₀)
    rw [Scheme.Hom.app_eq_appLE (barPt A), Scheme.Hom.app_eq_appLE s]
    rfl
  have ΓSpec_inv_nat : ∀ {R' S' : CommRingCat.{0}} (g : R' ⟶ S') (r : R'),
      (Spec.map g).appTop ((Scheme.ΓSpecIso R').inv r) = (Scheme.ΓSpecIso S').inv (g r) := by
    intro R' S' g r
    have := Scheme.ΓSpecIso_inv_naturality g
    have h := congrArg (fun k => k.hom r) this
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
    exact h.symm
  have hD3 : s.appTop t₀ = (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv c := by
    show s.appTop (f.appTop (φT Polynomial.X)) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hχ]
    exact ΓSpec_inv_nat (CommRingCat.ofHom χ) Polynomial.X
  have hD4 : (barPt A).appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv c) =
      (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).inv ((c : ↥A) : AlgebraicClosure ℚ) :=
    ΓSpec_inv_nat (CommRingCat.ofHom A.subtype) c
  have hval : (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).hom (y.1.appLE V ⊤ hz sect) =
      ((c : ↥A) : AlgebraicClosure ℚ) := by
    rw [hB, hC, hD1, hUι, hD2, hD3, hD4]
    exact (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).inv_hom_id_apply _
  rw [hval] at hnon

  have evalAt_eq : ∀ (v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (_ : v.IsRational)
      (g : ↥(xHFunctionFieldBar M H)) (a : AlgebraicClosure ℚ) (hg : g ∈ v.toValuationSubring)
      (_ : g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) a ∈ v.toValuationSubring.nonunits), v.evalAt g = a := by
    intro v hv g a hg hsub
    rw [Place.evalAt_of_mem _ hg]
    have hmem' : (((⟨g, hg⟩ : v.toValuationSubring) - algebraMap (AlgebraicClosure ℚ) v.toValuationSubring a :
        v.toValuationSubring) : ↥(xHFunctionFieldBar M H)) ∈ v.toValuationSubring.nonunits := hsub
    rw [ValuationSubring.coe_mem_nonunits_iff] at hmem'
    have hquot : IsLocalRing.residue v.toValuationSubring ⟨g, hg⟩ = algebraMap (AlgebraicClosure ℚ) v.ResidueField a := by
      show _ = IsLocalRing.residue v.toValuationSubring (algebraMap (AlgebraicClosure ℚ) v.toValuationSubring a)
      exact Ideal.Quotient.eq.mpr hmem'
    rw [hquot, Place.residueInv_algebraMap]
  have h3 : W.evalAt param = ((c : ↥A) : AlgebraicClosure ℚ) := by
    rw [hparam]
    exact evalAt_eq W hW _ _ hmem hnon

  haveI := het
  let ξ : ↥(Spec (CommRingCat.of ↥A)) := (barPt A).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))
  let q₀ : ↥(U : Scheme.{0}) := s.base ξ

  have hfq : (f.base q₀).asIdeal = Ideal.span {Polynomial.X - Polynomial.C c} := by
    have hq : f.base q₀ = (Spec.map (CommRingCat.ofHom χ ≫ CommRingCat.ofHom A.subtype)).base
        (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) := by
      show f.base (s.base ((barPt A).base _)) = _
      rw [← Scheme.Hom.comp_apply s f, hχ, ← Scheme.Hom.comp_apply, Spec.map_comp]
    rw [hq]
    have hbot : (IsLocalRing.closedPoint (AlgebraicClosure ℚ)).asIdeal = ⊥ :=
      IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField (AlgebraicClosure ℚ))
    show Ideal.comap (CommRingCat.ofHom χ ≫ CommRingCat.ofHom A.subtype).hom (IsLocalRing.closedPoint (AlgebraicClosure ℚ)).asIdeal = _
    rw [hbot, CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, ← RingHom.ker_eq_comap_bot,
      RingHom.ker_comp_of_injective _ (Subtype.val_injective), hχeval, Polynomial.ker_evalRingHom]

  let R₁ := (AlgebraicGeometry.structurePresheafInCommRingCat (Polynomial ↥A)).stalk (f.base q₀)
  let S₁ := (U : Scheme.{0}).presheaf.stalk q₀
  haveI hR₁loc : IsLocalRing R₁ := IsLocalization.AtPrime.isLocalRing R₁ (f.base q₀).asIdeal
  have hmaxR : IsLocalRing.maximalIdeal R₁ =
      Ideal.span {(AlgebraicGeometry.structurePresheafInCommRingCat (Polynomial ↥A)).germ ⊤ (f.base q₀) trivial (φT (Polynomial.X - Polynomial.C c))} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (f.base q₀).asIdeal R₁, hfq, Ideal.map_span, Set.image_singleton]
    rfl

  let φ₁ : R₁ →+* S₁ := (f.stalkMap q₀).hom
  have hmaxS : IsLocalRing.maximalIdeal S₁ = Ideal.span {(U : Scheme.{0}).presheaf.germ ⊤ q₀ trivial (f.appTop (φT (Polynomial.X - Polynomial.C c)))} := by
    letI := φ₁.toAlgebra
    haveI : IsLocalHom (algebraMap R₁ S₁) := inferInstanceAs (IsLocalHom (f.stalkMap q₀).hom)
    haveI : Algebra.EssFiniteType R₁ S₁ := by
      rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
      exact LocallyOfFiniteType.stalkMap f q₀
    haveI : Algebra.FormallyUnramified R₁ S₁ := by
      rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
      exact FormallyUnramified.stalkMap f q₀
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R₁) (S := S₁), hmaxR, Ideal.map_span, Set.image_singleton,
      RingHom.algebraMap_toAlgebra]
    exact congrArg (fun t => Ideal.span {t}) (Scheme.Hom.germ_stalkMap_apply f ⊤ q₀ trivial (φT (Polynomial.X - Polynomial.C c)))

  let cA : Γ(XO (ΓM M H) hj ρ, ⊤) := (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv c)
  let cU : Γ((U : Scheme.{0}), ⊤) := U.ι.appTop cA
  have hφTc : φT (Polynomial.C c) = (Spec.map (CommRingCat.ofHom (algebraMap ↥A (Polynomial ↥A)))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv c) :=
    (ΓSpec_inv_nat (CommRingCat.ofHom (algebraMap ↥A (Polynomial ↥A))) c).symm
  have hfc : f.appTop (φT (Polynomial.C c)) = cU := by
    rw [hφTc, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hover, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have ht₀c : f.appTop (φT (Polynomial.X - Polynomial.C c)) = t₀ - cU := by
    rw [map_sub, map_sub, hfc]

  have maxIdeal_of_iso : ∀ {R' S' : CommRingCat.{0}} [IsLocalRing R'] [IsLocalRing S'] (e : R' ≅ S') (r : R'),
      IsLocalRing.maximalIdeal S' = Ideal.span {e.hom r} → IsLocalRing.maximalIdeal R' = Ideal.span {r} := by
    intro R' S' _ _ e r h
    let e' : R' ≃+* S' := e.commRingCatIsoToRingEquiv
    have he' : ∀ a, e' a = e.hom a := fun _ => rfl
    apply le_antisymm
    · intro a ha
      have ha' : e' a ∈ IsLocalRing.maximalIdeal S' := map_nonunit (e' : R' →+* S') a ha
      rw [h, Ideal.mem_span_singleton'] at ha'
      obtain ⟨t, ht⟩ := ha'
      rw [Ideal.mem_span_singleton']
      refine ⟨e'.symm t, ?_⟩
      apply e'.injective
      rw [map_mul, e'.apply_symm_apply, he' r]
      exact ht
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have hr : e' r ∈ IsLocalRing.maximalIdeal S' := by rw [h, he']; exact Ideal.mem_span_singleton_self _
      exact (IsLocalRing.mem_maximalIdeal _).mpr (fun hu => (IsLocalRing.mem_maximalIdeal _).mp hr ((hu.map e')))
  have maxIdeal_to_iso : ∀ {R' S' : CommRingCat.{0}} [IsLocalRing R'] [IsLocalRing S'] (e : R' ≅ S') (r : R'),
      IsLocalRing.maximalIdeal R' = Ideal.span {r} → IsLocalRing.maximalIdeal S' = Ideal.span {e.hom r} := by
    intro R' S' _ _ e r h
    apply maxIdeal_of_iso e.symm (e.hom r)
    rw [h]; congr 1
    exact congrArg (fun t => ({t} : Set R')) (e.hom_inv_id_apply r).symm

  let gTc : Γ(XO (ΓM M H) hj ρ, W') := gT - (XO (ΓM M H) hj ρ).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op cA
  have hW'mem : U.ι.base q₀ ∈ W' := ⟨q₀, trivial, rfl⟩
  have hgerm_U : (U.ι.stalkMap q₀) ((XO (ΓM M H) hj ρ).presheaf.germ W' (U.ι.base q₀) hW'mem gTc) =
      (U : Scheme.{0}).presheaf.germ ⊤ q₀ trivial (t₀ - cU) := by
    rw [Scheme.Hom.germ_stalkMap_apply U.ι W' q₀ hW'mem gTc]
    show (U : Scheme.{0}).presheaf.germ (U.ι ⁻¹ᵁ W') q₀ hW'mem ((U.ι.app W') (gT - _)) = _
    rw [map_sub, map_sub, map_sub]
    congr 1
    · show (U : Scheme.{0}).presheaf.germ (U.ι ⁻¹ᵁ W') q₀ hW'mem ((U.ι.app (U.ι ''ᵁ ⊤)) ((U.ι.appIso ⊤).inv t₀)) = _
      rw [Scheme.Hom.appIso_inv_app_apply, TopCat.Presheaf.germ_res_apply]
    · have hnat := Scheme.Hom.naturality U.ι (homOfLE (le_top : W' ≤ ⊤)).op
      have hnat' := congrArg (fun k => k.hom cA) hnat
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat'
      rw [hnat']
      exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hmaxXA : IsLocalRing.maximalIdeal ((XO (ΓM M H) hj ρ).presheaf.stalk (U.ι.base q₀)) =
      Ideal.span {(XO (ΓM M H) hj ρ).presheaf.germ W' (U.ι.base q₀) hW'mem gTc} := by
    apply maxIdeal_of_iso (asIso (U.ι.stalkMap q₀)) _
    rw [asIso_hom, hgerm_U, ← ht₀c]
    exact hmaxS

  have hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _ := by
    show (𝔛.eeta ≫ prA) ≫ _ = _
    rw [Category.assoc, pullback.lift_fst, Category.comp_id]
  have hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A := by
    show (𝔛.eeta ≫ prA) ≫ _ = _
    rw [Category.assoc, pullback.lift_snd, ← Category.assoc, 𝔛.heeta]
  obtain ⟨-, -, hgAoi⟩ :=
    ModularCurve.XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
      p M hpM H A hA hj 𝔛 ρ hρ gA hgA₁ hgA₂
  haveI := hgAoi

  let xW : closedPoints (𝔛.Meta).C := pointEquivClosedPoint (𝔛.Meta).toBase y
  have hxW : (𝔛.Meta).placeOfPoint xW = W := by rw [← AlgebraicCurve.CurveModel.pointEquivPlace_apply]; exact hyW
  have hzq : gA.base xW.1 = U.ι.base q₀ := by
    show (y.1 ≫ 𝔛.eeta ≫ prA).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = U.ι.base (s.base ((barPt A).base _))
    rw [← hs_gen, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  have hW'z : gA.base xW.1 ∈ W' := hzq ▸ hW'mem
  have hxV : xW.1 ∈ V := hW'z
  have hmaxXA' : IsLocalRing.maximalIdeal ((XO (ΓM M H) hj ρ).presheaf.stalk (gA.base xW.1)) =
      Ideal.span {(XO (ΓM M H) hj ρ).presheaf.germ W' (gA.base xW.1) hW'z gTc} := by
    have P : ∀ (x : ↥(XO (ΓM M H) hj ρ)) (hx : x ∈ W'), x = U.ι.base q₀ →
        IsLocalRing.maximalIdeal ((XO (ΓM M H) hj ρ).presheaf.stalk x) =
          Ideal.span {(XO (ΓM M H) hj ρ).presheaf.germ W' x hx gTc} := by
      rintro x hx rfl; exact hmaxXA
    exact P _ hW'z hzq

  have hgerm_C : (gA.stalkMap xW.1) ((XO (ΓM M H) hj ρ).presheaf.germ W' (gA.base xW.1) hW'z gTc) =
      (𝔛.Meta).C.presheaf.germ V xW.1 hxV ((gA.app W') gTc) :=
    Scheme.Hom.germ_stalkMap_apply gA W' xW.1 hW'z gTc
  have hmaxC : IsLocalRing.maximalIdeal ((𝔛.Meta).C.presheaf.stalk xW.1) =
      Ideal.span {(𝔛.Meta).C.presheaf.germ V xW.1 hxV ((gA.app W') gTc)} := by
    have := maxIdeal_to_iso (asIso (gA.stalkMap xW.1)) _ hmaxXA'
    rwa [asIso_hom, hgerm_C] at this

  have hord := AlgebraicCurve.CurveModel.ord_placeOfPoint_ffEquiv_symm_algebraMap_eq_one_of_maximalIdeal_eq_span
    (𝔛.Meta) xW _ hmaxC
  rw [hxW] at hord

  have halg : ∀ σ : Γ((𝔛.Meta).C, V),
      algebraMap ((𝔛.Meta).C.presheaf.stalk xW.1) (𝔛.Meta).C.functionField ((𝔛.Meta).C.presheaf.germ V xW.1 hxV σ) =
        (𝔛.Meta).C.presheaf.germ V (genericPoint (𝔛.Meta).C) hgen σ := by
    intro σ
    show ((𝔛.Meta).C.presheaf.germ V xW.1 hxV ≫ (𝔛.Meta).C.presheaf.stalkSpecializes _) σ = _
    rw [TopCat.Presheaf.germ_stalkSpecializes]
  let cV : Γ((𝔛.Meta).C, V) := (gA.app W') ((XO (ΓM M H) hj ρ).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op cA)
  have hgTc : (gA.app W') gTc = sect - cV := by
    show (gA.app W') (gT - _) = _
    rw [map_sub, hsect]
    rfl
  have hcV : (𝔛.Meta).C.presheaf.germ V (genericPoint (𝔛.Meta).C) hgen cV =
      AlgebraicCurve.baseToFunctionField (𝔛.Meta).toBase ((c : ↥A) : AlgebraicClosure ℚ) := by
    have hnat := Scheme.Hom.naturality gA (homOfLE (le_top : W' ≤ ⊤)).op
    have hnat' := congrArg (fun k => k.hom cA) hnat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat'
    have happ : gA.appTop cA = (𝔛.Meta).toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).inv ((c : ↥A) : AlgebraicClosure ℚ)) := by
      show gA.appTop ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop _) = _
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hgA₂, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hD4]
    have step1 : (𝔛.Meta).C.presheaf.germ V (genericPoint (𝔛.Meta).C) hgen cV =
        (𝔛.Meta).C.presheaf.germ ⊤ (genericPoint (𝔛.Meta).C) trivial (gA.appTop cA) := by
      show (𝔛.Meta).C.presheaf.germ V (genericPoint (𝔛.Meta).C) hgen ((gA.app W') (((XO (ΓM M H) hj ρ).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op) cA)) = _
      rw [hnat']
      exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [step1, happ]
    rfl
  have hread : (𝔛.Meta).ffEquiv.symm (algebraMap ((𝔛.Meta).C.presheaf.stalk xW.1) (𝔛.Meta).C.functionField
      ((𝔛.Meta).C.presheaf.germ V xW.1 hxV ((gA.app W') gTc))) =
      param - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((c : ↥A) : AlgebraicClosure ℚ) := by
    rw [halg, hgTc, map_sub, map_sub, hcV, ← (𝔛.Meta).ffEquiv_algebraMap, RingEquiv.symm_apply_apply]
    rfl
  rw [hread] at hord
  exact ⟨h1, h2, h3, hord⟩

end S_ModularCurve_XHDRModelAtP_ord_read_chart_sub_algebraMap_eq_one_of_section_of_etale_chart_of_isStrictSnd
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_ord_read_chart_sub_algebraMap_eq_one_of_section_of_etale_chart_of_isStrictSnd (solution)
