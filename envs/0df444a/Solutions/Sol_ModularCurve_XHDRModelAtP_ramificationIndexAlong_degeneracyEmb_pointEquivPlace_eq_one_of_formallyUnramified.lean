-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.ramificationIndexAlong_degeneracyEmb_pointEquivPlace_eq_one_of_formallyUnramified
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/4986f8f0-8e65-567c-9e28-389a3e36ee39

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_XHDRModelAtP_fromSpecStalk_genericPoint_comp_eq_specMap_ffEquiv_degeneracyEmb_of_chartPin
import Theorems.Thm_AlgebraicCurve_CurveModel_ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_ramificationIndexAlong_degeneracyEmb_pointEquivPlace_eq_one_of_formallyUnramified

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel

open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (αH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hαint : αH.toRingHom.IsIntegral)
    (Meta₀ : CurveModel (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (eeta₀ : Meta₀.C ⟶ pullback (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
    [IsIso eeta₀]
    (heeta₀ : eeta₀ ≫ pullback.snd _ _ = Meta₀.toBase)
    (hne₀ : Nonempty (Scheme.Opens.toScheme ((eeta₀ ≫ pullback.fst (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((ιFin p (XHDRLevel.ΓN p M H hpM) hj) ''ᵁ ⊤))))
    (hpin₀ : haveI := hne₀
      ∀ a : ↥(chartAlgFin p (XHDRLevel.ΓN p M H hpM) hj),
            ((Meta₀.ffEquiv.symm
                (Meta₀.C.germToFunctionField
                  ((eeta₀ ≫ pullback.fst (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((ιFin p (XHDRLevel.ΓN p M H hpM) hj) ''ᵁ ⊤))
                  (((eeta₀ ≫ pullback.fst (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app ((ιFin p (XHDRLevel.ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
                    (((ιFin p (XHDRLevel.ΓN p M H hpM) hj).appIso ⊤).inv
                      ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (XHDRLevel.ΓN p M H hpM) hj))).inv a))))
                : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) =
              coeffEmb (AlgebraicClosure ℚ) ((a : ↥(qExpFunctionFieldC ℚ (XHDRLevel.ΓN p M H hpM))) : LaurentSeries ℚ))
    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (V : (X p (ΓM M H) hj).Opens)
    (hyV : (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ V)
    (hV : FormallyUnramified (V.ι ≫ 𝔛.π.1)) :
    Place.ramificationIndexAlong αH (𝔛.Meta.pointEquivPlace y) = 1 := by
  haveI := 𝔛.eeta_iso
  haveI := hne₀
  haveI := 𝔛.Meta_chart_nonempty

  have hinv₀ : inv eeta₀ ≫ Meta₀.toBase =
      pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) := by
    rw [IsIso.inv_comp_eq, heeta₀]
  obtain ⟨πM, hπM₁, hπM₂⟩ : ∃ πM : 𝔛.Meta.C ⟶ Meta₀.C,
      πM ≫ eeta₀ ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 ∧ πM ≫ Meta₀.toBase = 𝔛.Meta.toBase := by
    refine ⟨pullback.lift (𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1) (𝔛.eeta ≫ pullback.snd _ _)
      (by simp only [Category.assoc, 𝔛.π.2]; rw [pullback.condition]) ≫ inv eeta₀, ?_, ?_⟩
    · simp only [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]
    · simp only [Category.assoc, hinv₀, pullback.lift_snd, 𝔛.heeta]

  have hgen := ModularCurve.XHDRModelAtP.fromSpecStalk_genericPoint_comp_eq_specMap_ffEquiv_degeneracyEmb_of_chartPin
    p M H hpM hj 𝔛 αH hα Meta₀ eeta₀ heeta₀ hne₀ hpin₀ πM hπM₁ hπM₂

  let W : 𝔛.Meta.C.Opens := (𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ V
  have hyW : y.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ W := by
    show (𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).base (y.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) ∈ V
    rw [← Scheme.Hom.comp_apply]
    exact hyV
  have hRℚ : (algebraMap (R p) (AlgebraicClosure ℚ)).FormallyUnramified := by
    have hR : (algebraMap (R p) ℚ).FormallyUnramified := by
      rw [RingHom.formallyUnramified_algebraMap]
      haveI : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ℤ)
      exact Algebra.FormallyUnramified.of_restrictScalars ℤ (R p) ℚ
    have hQ : (algebraMap ℚ (AlgebraicClosure ℚ)).FormallyUnramified := by
      rw [RingHom.formallyUnramified_algebraMap]
      haveI : PerfectField ℚ := PerfectField.ofCharZero
      haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by convert AlgebraicClosure.isAlgebraic ℚ; rfl; rfl
      haveI : Algebra.IsSeparable ℚ (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.isSeparable_of_perfectField
      exact Algebra.FormallyUnramified.of_isSeparable ℚ (AlgebraicClosure ℚ)
    have heq : algebraMap (R p) (AlgebraicClosure ℚ) = (algebraMap ℚ (AlgebraicClosure ℚ)).comp (algebraMap (R p) ℚ) :=
      IsScalarTower.algebraMap_eq (R p) ℚ (AlgebraicClosure ℚ)
    rw [heq]
    exact RingHom.FormallyUnramified.stableUnderComposition _ _ hR hQ
  have hfst : FormallyUnramified (pullback.fst (toBase p (ΓM M H) hj)
      (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) :=
    MorphismProperty.pullback_fst _ _ ((HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mpr hRℚ)
  have hf : FormallyUnramified (𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) := MorphismProperty.comp_mem _ _ _ inferInstance hfst
  have h1 : FormallyUnramified (W.ι ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) := MorphismProperty.comp_mem _ _ _ inferInstance hf
  have hsub : Set.range (W.ι ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).base ⊆ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact t.2
  let l := IsOpenImmersion.lift V.ι (W.ι ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) hsub
  have hl : l ≫ V.ι = W.ι ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) := IsOpenImmersion.lift_fac _ _ _
  have h2 : FormallyUnramified l := by
    have : FormallyUnramified (l ≫ V.ι) := by rw [hl]; exact h1
    exact FormallyUnramified.of_comp l V.ι
  have h3 : FormallyUnramified (l ≫ V.ι ≫ 𝔛.π.1) := MorphismProperty.comp_mem _ _ _ h2 hV
  have h4 : (W.ι ≫ πM) ≫ eeta₀ ≫ pullback.fst _ _ = l ≫ V.ι ≫ 𝔛.π.1 := by
    rw [Category.assoc, hπM₁, ← Category.assoc l, hl, Category.assoc, Category.assoc]
  have h5 : FormallyUnramified ((W.ι ≫ πM) ≫ eeta₀ ≫ pullback.fst _ _) := by rw [h4]; exact h3
  have hFUW : FormallyUnramified (W.ι ≫ πM) := FormallyUnramified.of_comp (W.ι ≫ πM) (eeta₀ ≫ pullback.fst _ _)

  exact AlgebraicCurve.CurveModel.ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified
    𝔛.Meta Meta₀ αH hαint πM hπM₂ hgen y W hyW hFUW

#print axioms solution

end S_ModularCurve_XHDRModelAtP_ramificationIndexAlong_degeneracyEmb_pointEquivPlace_eq_one_of_formallyUnramified
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_ramificationIndexAlong_degeneracyEmb_pointEquivPlace_eq_one_of_formallyUnramified (solution)
