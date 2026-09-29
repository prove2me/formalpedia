-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_isUnit_section_read_eq_stalkRead_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/683fb92d-3ee2-5a5b-bde4-316354640a0d

import Mathlib
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

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_isUnit_section_read_eq_stalkRead_of_isUnit

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial

open scoped MatrixGroups

theorem germ_app_app_app_eq_of_comp_eq {P Q R T : Scheme.{0}} (a : P ⟶ Q) (b : Q ⟶ R) (d : R ⟶ T) (c : Q ⟶ T)
    (h : b ≫ d = c) (V : T.Opens) (z : ↥P) (hz : z ∈ a ⁻¹ᵁ (b ⁻¹ᵁ (d ⁻¹ᵁ V))) (hz' : z ∈ a ⁻¹ᵁ (c ⁻¹ᵁ V)) (s : Γ(T, V)) :
    (P.presheaf.germ (a ⁻¹ᵁ (b ⁻¹ᵁ (d ⁻¹ᵁ V))) z hz).hom ((a.app (b ⁻¹ᵁ (d ⁻¹ᵁ V))).hom ((b.app (d ⁻¹ᵁ V)).hom ((d.app V).hom s))) =
      (P.presheaf.germ (a ⁻¹ᵁ (c ⁻¹ᵁ V)) z hz').hom ((a.app (c ⁻¹ᵁ V)).hom ((c.app V).hom s)) := by
  subst h; rfl

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
    ∀ hgen : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤)),
    letI read : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) →+* ↥(xHFunctionFieldBar M H) :=
      (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
          ((𝔛.eeta.app (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp (prJ.app (U.ι ''ᵁ ⊤)).hom))
    letI param : ↥(xHFunctionFieldBar M H) := read gv
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
    ∀ (hsp : prJ'.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) ⤳ xn'),
    letI emb : ↥B →+* ↥(xHFunctionFieldBar M H) := (𝔛.Meta).ffEquiv.symm.toRingHom.comp
      ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
        ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
          ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes hsp).hom))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    letI bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl
    ∀ t : ↥B, IsUnit t →
      ∃ (U' : (XO (ΓM M H) hj ρ).Opens)
        (hx : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA).base n ∈ U')
        (hgenA : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ U'))
        (γ : Γ(XO (ΓM M H) hj ρ, U')),
        IsUnit γ ∧
        (𝔛.Meta).ffEquiv.symm
          (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ U')) (genericPoint (𝔛.Meta).C) hgenA).hom
            ((𝔛.eeta.app (prA ⁻¹ᵁ U')).hom ((prA.app U').hom γ))) = emb t := by
  intro hgen hsp t ht
  let XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
  let prJ : XQ ⟶ XO (ΓM M H) hj ρO :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])
  let VM : (𝔛.Meta).C.Opens := 𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ U)
  let Q := CrossingQuotient O (((p : ℕ) : O) ^ e)
  let φ : Q →+* Γ(CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
  let gv : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.V (((p : ℕ) : O) ^ e))))
  let gu : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.U (((p : ℕ) : O) ^ e))))
  let read : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) →+* ↥(xHFunctionFieldBar M H) :=
    (𝔛.Meta).ffEquiv.symm.toRingHom.comp
      (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
        ((𝔛.eeta.app (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp (prJ.app (U.ι ''ᵁ ⊤)).hom))
  let param : ↥(xHFunctionFieldBar M H) := read gv
  let param' : ↥(xHFunctionFieldBar M H) := read gu
  let bc' := bcMap (ΓM M H) hj (σ.comp ρO) ((IsLocalRing.residue ↥A).comp ιA') htoκ'
  let xn' : ↥(XO (ΓM M H) hj (σ.comp ρO)) := (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc').base n
  let prJ' : XQ ⟶ XO (ΓM M H) hj (σ.comp ρO) :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO'])
  let prσ : XO (ΓM M H) hj (σ.comp ρO) ⟶ XO (ΓM M H) hj ρO :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom σ)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
  let B := (XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalk xn'
  let σB : O' →+* ↥B := ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ ⊤ xn' trivial).hom.comp
    (((XO.toBase (ΓM M H) hj (σ.comp ρO)).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)
  let emb : ↥B →+* ↥(xHFunctionFieldBar M H) := (𝔛.Meta).ffEquiv.symm.toRingHom.comp
    ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
      ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
        ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes hsp).hom))
  let prA : XQ ⟶ XO (ΓM M H) hj ρ :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
  let bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl
  haveI := 𝔛.eeta_iso

  have hex := (XO (ΓM M H) hj (σ.comp ρO)).presheaf.exists_germ_eq t
  obtain ⟨V, hxV, s, hs⟩ := hex
  have hres := AlgebraicGeometry.RingedSpace.isUnit_res_of_isUnit_germ (X := (XO (ΓM M H) hj (σ.comp ρO)).toLocallyRingedSpace.toSheafedSpace) V s xn' hxV (by rw [hs]; exact ht)
  obtain ⟨V', i, hxV', hunit⟩ := hres
  have hs' : (XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ V' xn' hxV' ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.map i.op s) = t := by
    rw [TopCat.Presheaf.germ_res_apply, hs]

  have hρ' : ιA'.comp (σ.comp ρO) = ρ := by
    ext r
    have h1 := RingHom.congr_fun hιA'j (σ (ρO r))
    have h2 := RingHom.congr_fun hjO' r
    have h3 := RingHom.congr_fun hρ r
    simp only [RingHom.comp_apply] at h1 h2 h3
    show A.subtype ((ιA'.comp (σ.comp ρO)) r) = A.subtype (ρ r)
    simp only [RingHom.comp_apply]
    rw [h1, h2, h3]
  let pr' : XO (ΓM M H) hj ρ ⟶ XO (ΓM M H) hj (σ.comp ρO) :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom ιA')) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ'])
  have hbc : bcA ≫ pr' = bc' := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pr', bcA, bc', pullback.lift_fst, Category.comp_id, bcMap_fst]
    · simp only [Category.assoc, pr', bcA, bc', pullback.lift_snd]
      rw [bcMap_snd_assoc, bcMap_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hpp : prA ≫ pr' = prJ' := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pr', prA, prJ', pullback.lift_fst, Category.comp_id]
    · simp only [Category.assoc, pr', prA, prJ', pullback.lift_snd]
      rw [pullback.lift_snd_assoc, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hιA'j]
  refine ⟨pr' ⁻¹ᵁ V', ?_, ?_, (pr'.app V').hom ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.map i.op s), hunit.map (pr'.app V').hom, ?_⟩
  ·
    show pr'.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA).base n) ∈ V'
    rw [← Scheme.Hom.comp_apply]
    simp only [Category.assoc]
    rw [hbc]
    exact hxV'
  ·
    show pr'.base (prA.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C))) ∈ V'
    rw [← Scheme.Hom.comp_apply _ pr', hpp]
    exact hsp.mem_open V'.2 hxV'
  ·
    rw [← hs']
    show (𝔛.Meta).ffEquiv.symm _ = (𝔛.Meta).ffEquiv.symm ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom
      ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom
        (((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes hsp).hom ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ V' xn' hxV' ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.map i.op s)))))
    congr 1
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply]
    exact germ_app_app_app_eq_of_comp_eq 𝔛.eeta prA pr' prJ' hpp V' (genericPoint (𝔛.Meta).C) _ _ _

end S_ModularCurve_XHDRModelAtP_exists_isUnit_section_read_eq_stalkRead_of_isUnit
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_isUnit_section_read_eq_stalkRead_of_isUnit (solution)
