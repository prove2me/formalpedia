-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_etale_chart_affineLine_of_isStrictFst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/d9ba0f93-b881-5362-98ae-365699afc379

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Theorems.Thm_AlgebraicGeometry_mem_smoothLocus_of_not_mem_range_of_isClosedImmersion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_etale_chart_affineLine_of_isStrictFst

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

universe u

namespace SmoothChartAux

theorem exists_etale_polynomial_of_isStandardSmoothOfRelativeDimension_one
    {O S : Type u} {κ : Type u} [CommRing O] [CommRing S] [CommRing κ]
    (φ : O →+* S) (hφ : φ.IsStandardSmoothOfRelativeDimension 1)
    (ψ : S →+* κ) (r : O →+* κ) (hr : Function.Surjective r) (hψ : ψ.comp φ = r) :
    ∃ g : Polynomial O →+* S, g.comp Polynomial.C = φ ∧ g.Etale ∧ ψ (g Polynomial.X) = 0 := by
  classical
  obtain ⟨g₀, hg₀C, hg₀E⟩ := hφ.exists_etale_mvPolynomial
  obtain ⟨a, ha⟩ := hr (ψ (g₀ (MvPolynomial.X 0)))
  let E : Polynomial O ≃ₐ[O] MvPolynomial (Fin 1) O :=
    (Polynomial.algEquivAevalXAddC (-a)).trans (MvPolynomial.uniqueAlgEquiv O (Fin 1)).symm
  have hEX : E Polynomial.X = MvPolynomial.X 0 - MvPolynomial.C a := by
    simp [E, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_add_neg, Fin.default_eq_zero]
  have hEC : (E : Polynomial O →+* MvPolynomial (Fin 1) O).comp Polynomial.C = MvPolynomial.C := by
    refine RingHom.ext fun x => ?_
    have := E.commutes x
    rwa [Polynomial.algebraMap_eq, MvPolynomial.algebraMap_eq] at this
  refine ⟨g₀.comp (E : Polynomial O →+* MvPolynomial (Fin 1) O), ?_, ?_, ?_⟩
  · rw [RingHom.comp_assoc, hEC, hg₀C]
  · exact RingHom.Etale.respectsIso.2 g₀ E.toRingEquiv hg₀E
  · have h1 : ψ (g₀ (MvPolynomial.C a)) = r a := by
      rw [← hψ, ← hg₀C]; rfl
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [show (E : Polynomial O →+* MvPolynomial (Fin 1) O) Polynomial.X = E Polynomial.X from rfl, hEX,
      map_sub, map_sub, h1, ha, sub_self]

theorem exists_etale_chart_affineLine_of_smoothOfRelativeDimension_one
    {O : Type u} [CommRing O] [IsLocalRing O] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (CommRingCat.of O)) [SmoothOfRelativeDimension 1 g]
    (z : Spec (CommRingCat.of (ResidueField O)) ⟶ Z)
    (hz : z ≫ g = Spec.map (CommRingCat.ofHom (residue O))) :
    ∃ (U : Z.Opens) (hxU : z.base (closedPoint (ResidueField O)) ∈ U)
      (f : (U : Scheme.{u}) ⟶ Spec (CommRingCat.of (Polynomial O))),
      f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (Polynomial O))) = U.ι ≫ g ∧
      Etale f ∧
      f.base ⟨_, hxU⟩ = (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : O)))).base (closedPoint O) := by
  classical
  set x₀ : Z := z.base (closedPoint (ResidueField O)) with hx₀

  have hgx₀ : g.base x₀ = closedPoint O := by
    rw [hx₀, ← Scheme.Hom.comp_apply, hz, Spec.map_apply]
    exact IsLocalRing.comap_closedPoint (residue O)
  obtain ⟨U₀, hU₀, V, hV, hxV, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := g) x₀
  obtain rfl : U₀ = ⊤ := IsLocalRing.closed_point_mem_iff.mp (hgx₀ ▸ e hxV)

  let φ : O →+* Γ(Z, V) := ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ g.appLE ⊤ V e).hom
  have hφ : φ.IsStandardSmoothOfRelativeDimension 1 :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 (g.appLE ⊤ V e).hom
      (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv hstd

  let κ := ResidueField O
  have hTop : (⊤ : (Spec (CommRingCat.of κ)).Opens) ≤ z ⁻¹ᵁ V := by
    intro pt _
    obtain rfl : pt = closedPoint κ := Subsingleton.elim _ _
    exact hxV
  let ψ' : Γ(Z, V) ⟶ CommRingCat.of κ := z.appLE V ⊤ hTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom
  have aux : ∀ {w : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of O)} (hw : (⊤ : (Spec (CommRingCat.of κ)).Opens) ≤ w ⁻¹ᵁ ⊤),
      w = Spec.map (CommRingCat.ofHom (residue O)) → w.appLE ⊤ ⊤ hw = (Spec.map (CommRingCat.ofHom (residue O))).appTop := by
    rintro w hw rfl; rfl
  have key : g.appLE ⊤ V e ≫ z.appLE V ⊤ hTop = (Spec.map (CommRingCat.ofHom (residue O))).appTop := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact aux _ hz
  have hψ : ψ'.hom.comp φ = residue O := by
    change ((((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ g.appLE ⊤ V e)) ≫
      (z.appLE V ⊤ hTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom)).hom = _
    rw [Category.assoc, reassoc_of% key, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc,
      CommRingCat.hom_ofHom]
  obtain ⟨gX, hgXC, hgXE, hgX0⟩ :=
    exists_etale_polynomial_of_isStandardSmoothOfRelativeDimension_one φ hφ ψ'.hom (residue O)
      residue_surjective hψ
  have hEt : Etale (Spec.map (CommRingCat.ofHom gX)) := HasRingHomProperty.Spec_iff.mpr hgXE
  refine ⟨V, hxV, hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom gX), ?_, inferInstance, ?_⟩
  ·
    have hφ' : CommRingCat.ofHom φ = (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ g.appLE ⊤ V e := rfl
    rw [Polynomial.algebraMap_eq, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hgXC, hφ',
      Spec.map_comp, IsAffineOpen.isoSpec_hom, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc,
      Scheme.Opens.toSpecΓ_top, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id,
      Scheme.Hom.resLE_comp_ι]
  ·
    let t : ((⊤ : (Spec (CommRingCat.of κ)).Opens) : Scheme.{u}) := ⟨closedPoint κ, trivial⟩
    have hpt : (⟨x₀, hxV⟩ : (V : Scheme.{u})) = (z.resLE V ⊤ hTop).base t := by
      apply Subtype.ext
      rw [← Scheme.Opens.ι_apply V ((z.resLE V ⊤ hTop).base t), ← Scheme.Hom.comp_apply,
        Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
    have hzT : z.resLE V ⊤ hTop ≫ V.toSpecΓ = (⊤ : (Spec (CommRingCat.of κ)).Opens).ι ≫ Spec.map ψ' := by
      rw [← Scheme.Opens.toSpecΓ_SpecMap_appLE, Scheme.Opens.toSpecΓ_top, ← SpecMap_ΓSpecIso_hom,
        Category.assoc, ← Spec.map_comp]
    have hcomp : ψ'.hom.comp gX = (residue O).comp (Polynomial.evalRingHom 0) := by
      refine Polynomial.ringHom_ext (fun a => ?_) ?_
      · simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_C]
        rw [← RingHom.comp_apply gX Polynomial.C a, hgXC, ← RingHom.comp_apply, hψ]
      · simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_X,
          map_zero]
        exact hgX0
    rw [hpt, ← Scheme.Hom.comp_apply, IsAffineOpen.isoSpec_hom, reassoc_of% hzT, ← Spec.map_comp,
      Scheme.Hom.comp_apply, Scheme.Opens.ι_apply,
      Spec.map_apply, Spec.map_apply, CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, hcomp,
      PrimeSpectrum.comap_comp_apply, IsLocalRing.comap_closedPoint]

end SmoothChartAux

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

    (Q : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQ : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q)
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hu : barPt A ≫ u.1 = ((𝔛.Meta).pointEquivPlace.symm Q).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP0Q : (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = Psp.reduceFst α hα Q)
    (hsmooth : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 1).base)
    :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    letI bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl

    letI x₀ : ↥(XO (ΓM M H) hj ρ) := bcA.base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    ∃ (U : (XO (ΓM M H) hj ρ).Opens) (hxU : x₀ ∈ U) (f : (U : Scheme.{0}) ⟶ Spec (CommRingCat.of (Polynomial ↥A))),
      f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥A (Polynomial ↥A))) = U.ι ≫ pullback.snd _ _ ∧
      Etale f ∧
      f.base ⟨_, hxU⟩ = (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ↥A)))).base (IsLocalRing.closedPoint ↥A) := by
  classical

  haveI := 𝔛.flat
  haveI := 𝔛.lfp
  haveI := 𝔛.smooth0
  haveI := 𝔛.smoothLocus_relDim
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 1
  haveI : IsReduced (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) := 𝔛.fibre_reduced A hA ρ hρ
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  haveI : SmoothOfRelativeDimension 1
      (pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) :=
    MorphismProperty.pullback_snd _ _ 𝔛.smooth0

  have hy : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
      (uκ.base (closedPoint (ResidueField ↥A))) ∈ (toBase p (ΓM M H) hj).smoothLocus :=
    AlgebraicGeometry.mem_smoothLocus_of_not_mem_range_of_isClosedImmersion (toBase p (ΓM M H) hj)
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))
      (pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))
      (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) (𝔛.comp_over A hA ρ hρ 0) (𝔛.comp_jointly_surjective A hA ρ hρ) _ hsmooth

  have hle : (toBase p (ΓM M H) hj).smoothLocus ≤ 𝔛.smoothLocus := by
    refine 𝔛.smoothLocus_maximal _ ?_
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq, Scheme.Opens.ι_preimage_self]

  let π₁ := pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))
  let WA : (XO (ΓM M H) hj ρ).Opens := π₁ ⁻¹ᵁ 𝔛.smoothLocus
  have sq : IsPullback (π₁ ∣_ 𝔛.smoothLocus) (WA.ι ≫ pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))
      (𝔛.smoothLocus.ι ≫ toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) :=
    (isPullback_morphismRestrict π₁ 𝔛.smoothLocus).paste_vert (IsPullback.of_hasPullback _ _)
  haveI : SmoothOfRelativeDimension 1 (WA.ι ≫ pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) :=
    MorphismProperty.of_isPullback sq inferInstance

  have hz_snd : (uκ ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl) ≫ pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) := by
    rw [Category.assoc, bcMap_snd, reassoc_of% huκ₂]
  have hxWA : (uκ ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base (closedPoint (ResidueField ↥A)) ∈ WA := by
    show π₁.base ((uκ ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base (closedPoint (ResidueField ↥A))) ∈ 𝔛.smoothLocus
    rw [← Scheme.Hom.comp_apply, Category.assoc, bcMap_fst]
    exact hle hy
  have hrange : Set.range (uκ ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base ⊆ Set.range WA.ι.base := by
    rintro _ ⟨pt, rfl⟩
    obtain rfl : pt = closedPoint (ResidueField ↥A) := Subsingleton.elim _ _
    rw [Scheme.Opens.range_ι]
    exact hxWA
  have hzW_fac := IsOpenImmersion.lift_fac _ _ hrange

  obtain ⟨U', hxU', f', hover', het', hpt'⟩ :=
    SmoothChartAux.exists_etale_chart_affineLine_of_smoothOfRelativeDimension_one
      (WA.ι ≫ pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) (IsOpenImmersion.lift _ _ hrange)
      (by rw [← Category.assoc, hzW_fac, hz_snd])
  have hx₀ : (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base (uκ.base (closedPoint (ResidueField ↥A))) =
      WA.ι.base ((IsOpenImmersion.lift _ _ hrange).base (closedPoint (ResidueField ↥A))) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hzW_fac]
  have hxU : (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base (uκ.base (closedPoint (ResidueField ↥A))) ∈ WA.ι ''ᵁ U' := by
    rw [hx₀]
    exact ⟨_, hxU', rfl⟩
  refine ⟨WA.ι ''ᵁ U', hxU, (WA.ι.isoImage U').inv ≫ f', ?_, inferInstance, ?_⟩
  · rw [Category.assoc, hover', Scheme.Hom.isoImage_inv_ι_assoc]
  · have hinj : Function.Injective (U'.ι ≫ WA.ι).base := (U'.ι ≫ WA.ι).isOpenEmbedding.injective
    have hv : (WA.ι.isoImage U').inv.base ⟨_, hxU⟩ =
        ⟨(IsOpenImmersion.lift _ _ hrange).base (closedPoint (ResidueField ↥A)), hxU'⟩ := by
      apply hinj
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.isoImage_inv_ι, Scheme.Opens.ι_apply, Scheme.Hom.comp_apply,
        Scheme.Opens.ι_apply]
      exact hx₀
    rw [Scheme.Hom.comp_apply, hv, hpt']

end S_ModularCurve_XHDRModelAtP_exists_etale_chart_affineLine_of_isStrictFst
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_etale_chart_affineLine_of_isStrictFst (solution)
