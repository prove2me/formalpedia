-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.section_eq_of_comp_chart_eq_of_base_closedPoint_eq_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/fe4480aa-cad0-5f88-afe9-f2e82f8a697c

import Mathlib
import Theorems.Thm_AlgebraicGeometry_eq_of_comp_eq_of_forall_specializes_of_lift_mem_range_diagonal
import Theorems.Thm_AlgebraicGeometry_eq_of_comp_eq_of_base_closedPoint_eq_of_isIso_residueFieldMap
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_section_eq_of_comp_chart_eq_of_base_closedPoint_eq_of_chart

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial

open scoped MatrixGroups

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
    (hor₄ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) :
    ∀ s s' : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0}),
      s ≫ U.ι ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA) →
      s' ≫ U.ι ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA) →
      U.ι.base (s.base (IsLocalRing.closedPoint ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
      U.ι.base (s'.base (IsLocalRing.closedPoint ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
      s ≫ f = s' ≫ f → s = s' := by
  intro s s' hs hs' hspt hs'pt hsf
  have hinjU : Function.Injective U.ι.base := U.ι.isOpenEmbedding.injective
  have hy : s'.base (IsLocalRing.closedPoint ↥A) = s.base (IsLocalRing.closedPoint ↥A) := hinjU (hs'pt.trans hspt.symm)
  obtain ⟨V, hyV, hV⟩ := het (s.base (IsLocalRing.closedPoint ↥A)) hspt
  haveI : Etale (V.ι ≫ f) := hV

  have hrs : Set.range s.base ⊆ Set.range V.ι.base := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ((IsLocalRing.specializes_closedPoint t).map s.continuous).mem_open V.isOpen hyV
  have hrs' : Set.range s'.base ⊆ Set.range V.ι.base := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ((IsLocalRing.specializes_closedPoint t).map s'.continuous).mem_open V.isOpen (hy ▸ hyV)
  set sV := IsOpenImmersion.lift V.ι s hrs with hsVdef
  set sV' := IsOpenImmersion.lift V.ι s' hrs' with hsV'def
  have hsV : sV ≫ V.ι = s := IsOpenImmersion.lift_fac _ _ _
  have hsV' : sV' ≫ V.ι = s' := IsOpenImmersion.lift_fac _ _ _
  have hfV : sV ≫ (V.ι ≫ f) = sV' ≫ (V.ι ≫ f) := by
    rw [← Category.assoc, hsV, ← Category.assoc, hsV', hsf]

  set ι : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥A)) ⟶ Spec (CommRingCat.of ↥A) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) with hιdef
  have hι : ι.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A)) = IsLocalRing.closedPoint ↥A :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue ↥A)
  have hv : V.ι.base ((ι ≫ sV).base (IsLocalRing.closedPoint _)) = s.base (IsLocalRing.closedPoint ↥A) := by
    rw [Scheme.Hom.comp_apply, hι, ← Scheme.Hom.comp_apply, hsV]
  have hv' : V.ι.base ((ι ≫ sV').base (IsLocalRing.closedPoint _)) = s.base (IsLocalRing.closedPoint ↥A) := by
    rw [Scheme.Hom.comp_apply, hι, ← Scheme.Hom.comp_apply, hsV', hy]
  have hptV : (ι ≫ sV).base (IsLocalRing.closedPoint _) = (ι ≫ sV').base (IsLocalRing.closedPoint _) :=
    V.ι.isOpenEmbedding.injective (hv.trans hv'.symm)

  have hκ : IsIso ((V.ι ≫ f).residueFieldMap ((ι ≫ sV).base (IsLocalRing.closedPoint _))) := by
    rw [Scheme.residueFieldMap_comp]
    obtain ⟨-, -, hiso⟩ := hpt (V.ι.base ((ι ≫ sV).base (IsLocalRing.closedPoint _))) (hv ▸ hspt)
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hiso inferInstance
  have hagree : ι ≫ sV = ι ≫ sV' :=
    AlgebraicGeometry.eq_of_comp_eq_of_base_closedPoint_eq_of_isIso_residueFieldMap (V.ι ≫ f) (ι ≫ sV) (ι ≫ sV')
      (by rw [Category.assoc, Category.assoc, hfV]) hptV hκ

  have hΔ : (pullback.lift sV sV' hfV).base (IsLocalRing.closedPoint ↥A) ∈ Set.range (pullback.diagonal (V.ι ≫ f)).base := by
    refine ⟨(ι ≫ sV).base (IsLocalRing.closedPoint _), ?_⟩
    rw [← hι, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    have hcomp : (ι ≫ sV) ≫ pullback.diagonal (V.ι ≫ f) = ι ≫ pullback.lift sV sV' hfV := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.diagonal_fst, pullback.lift_fst, Category.comp_id]
      · simp only [Category.assoc, pullback.diagonal_snd, pullback.lift_snd, Category.comp_id, hagree]
    rw [hcomp]
  have key := AlgebraicGeometry.eq_of_comp_eq_of_forall_specializes_of_lift_mem_range_diagonal (V.ι ≫ f) sV sV' hfV
    (IsLocalRing.closedPoint ↥A) (fun t => IsLocalRing.specializes_closedPoint t) hΔ
  rw [← hsV, ← hsV', key]

end S_ModularCurve_XHDRModelAtP_section_eq_of_comp_chart_eq_of_base_closedPoint_eq_of_chart
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_section_eq_of_comp_chart_eq_of_base_closedPoint_eq_of_chart (solution)
