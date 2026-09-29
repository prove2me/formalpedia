-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_isRational_comp_eq_pointEquivPlace_and_eq_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/e0fe2caa-5b3b-5498-b6ba-03c5e95e2dc4

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableCharts

import Theorems.Thm_AlgebraicCurve_CurveModel_isRational_pointEquivPlace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_isRational_comp_eq_pointEquivPlace_and_eq_of_comp_eq

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
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prJ : XQ ⟶ XO (ΓM M H) hj ρO :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])
    (∀ s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0}),
      s ≫ U.ι ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA) →
      ∃ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), W.IsRational ∧
        barPt A ≫ s ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prJ) ∧
    (∀ W W' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prJ = ((𝔛.Meta).pointEquivPlace.symm W').1 ≫ 𝔛.eeta ≫ prJ → W = W') := by
  let XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
  let prJ : XQ ⟶ XO (ΓM M H) hj ρO :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])
  have hbar : barPt A = Spec.map (CommRingCat.ofHom A.subtype) := rfl
  constructor
  · intro s hs1

    let g : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ XO (ΓM M H) hj ρO := barPt A ≫ s ≫ U.ι
    have hg_snd : g ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom jO) := by
      simp only [g, Category.assoc]
      rw [hs1, hbar, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hιA]
    have hw : (g ≫ pullback.fst _ _) ≫ toBase p (ΓM M H) hj =
        𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
      rw [Category.id_comp, Category.assoc, pullback.condition, ← Category.assoc, hg_snd, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, hjO]
    let t : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ XQ := pullback.lift (g ≫ pullback.fst _ _) (𝟙 _) hw
    have ht_fst : t ≫ pullback.fst _ _ = g ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
    have ht_snd : t ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have ht_prJ : t ≫ prJ = g := by
      apply pullback.hom_ext
      · simp only [prJ, Category.assoc, pullback.lift_fst, Category.comp_id]
        exact ht_fst
      · simp only [prJ, Category.assoc, pullback.lift_snd]
        rw [← Category.assoc, ht_snd, Category.id_comp, hg_snd]
    let pt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ (𝔛.Meta).C := t ≫ inv 𝔛.eeta
    have hpt : pt ≫ (𝔛.Meta).toBase = 𝟙 _ := by
      rw [← 𝔛.heeta]
      simp only [pt, Category.assoc, IsIso.inv_hom_id_assoc]
      exact ht_snd
    refine ⟨(𝔛.Meta).pointEquivPlace ⟨pt, hpt⟩, AlgebraicCurve.CurveModel.isRational_pointEquivPlace _ _, ?_⟩
    rw [Equiv.symm_apply_apply]
    show g = (t ≫ inv 𝔛.eeta) ≫ 𝔛.eeta ≫ prJ
    rw [Category.assoc, IsIso.inv_hom_id_assoc, ht_prJ]
  · intro W W' h
    have h1 : ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta = ((𝔛.Meta).pointEquivPlace.symm W').1 ≫ 𝔛.eeta := by
      apply pullback.hom_ext
      · have h' := congrArg (fun k => k ≫ pullback.fst _ _) h
        simp only [Category.assoc, prJ, pullback.lift_fst, Category.comp_id] at h'
        simpa only [Category.assoc] using h'
      · rw [Category.assoc, Category.assoc, 𝔛.heeta, ((𝔛.Meta).pointEquivPlace.symm W).2, ((𝔛.Meta).pointEquivPlace.symm W').2]
    have h2 : ((𝔛.Meta).pointEquivPlace.symm W).1 = ((𝔛.Meta).pointEquivPlace.symm W').1 := (cancel_mono 𝔛.eeta).mp h1
    have h3 : (𝔛.Meta).pointEquivPlace.symm W = (𝔛.Meta).pointEquivPlace.symm W' := Subtype.ext h2
    exact (𝔛.Meta).pointEquivPlace.symm.injective h3

end S_ModularCurve_XHDRModelAtP_exists_isRational_comp_eq_pointEquivPlace_and_eq_of_comp_eq
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_isRational_comp_eq_pointEquivPlace_and_eq_of_comp_eq (solution)
