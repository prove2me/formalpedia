-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.section_closedPoint_eq_crossing_of_reduceFst_eq_of_not_isStrict_of_offDiag
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/68bf28d3-02fa-57b1-a7ec-3f060217b5a4

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_section_closedPoint_eq_crossing_of_reduceFst_eq_of_not_isStrict_of_offDiag
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut"

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
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)

    (jO : O →+* AlgebraicClosure ℚ) (hjO : jO.comp ρO = algebraMap (R p) (AlgebraicClosure ℚ))
    (ιA : O →+* ↥A) (hιA : A.subtype.comp ιA = jO) (hιAκ : (IsLocalRing.residue ↥A).comp ιA = toκ)
    (hsurj : Function.Surjective toκ)
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (nd : ↥SS)
    (hn : (𝔛.placeOn0 A hA ρ hρ n, 𝔛.placeOn1 A hA ρ hρ n) = (nd : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))

    (sA : Spec (CommRingCat.of ↥A) ⟶ XO (ΓM M H) hj ρO)
    (hsA₁ : sA ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA))
    (hsA₂ : barPt A ≫ sA = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫
      (pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
          (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO)) (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO]) :
          pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρO))
    (hW : Psp.reduceFst α hα W = nd.1.1)
    (h₁ : ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W) (h₂ : ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W) :
    sA.base (IsLocalRing.closedPoint ↥A) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n := by
  have hp : p.Prime := Fact.out

  have hιρ : ιA.comp ρO = ρ := by
    apply RingHom.ext
    intro r
    apply Subtype.val_injective
    have h1 := congrArg (fun f : R p →+* AlgebraicClosure ℚ => f r) hjO
    have h2 := congrArg (fun f : R p →+* AlgebraicClosure ℚ => f r) hρ
    have h3 := congrArg (fun f : O →+* AlgebraicClosure ℚ => f (ρO r)) hιA
    simp only [RingHom.coe_comp, Function.comp_apply] at h1 h2 h3
    show ((ιA (ρO r) : ↥A) : AlgebraicClosure ℚ) = ((ρ r : ↥A) : AlgebraicClosure ℚ)
    rw [show ((ιA (ρO r) : ↥A) : AlgebraicClosure ℚ) = A.subtype (ιA (ρO r)) from rfl, h3, h1,
      show ((ρ r : ↥A) : AlgebraicClosure ℚ) = A.subtype (ρ r) from rfl, h2]

  have hu_over : (sA ≫ pullback.fst _ _) ≫ toBase p (ΓM M H) hj = Spec.map (CommRingCat.ofHom ρ) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hsA₁, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hιρ]
  let u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj) := ⟨sA ≫ pullback.fst _ _, hu_over⟩
  have hu : barPt A ≫ u.1 = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ pullback.fst _ _ := by
    show barPt A ≫ sA ≫ pullback.fst _ _ = _
    rw [← Category.assoc, hsA₂]
    simp only [Category.assoc, pullback.lift_fst, Category.comp_id]

  have huκc : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) ≫ toBase p (ΓM M H) hj =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) := by
    rw [Category.assoc, u.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Category.id_comp]
  let uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) :=
    pullback.lift (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (𝟙 _) huκc
  have huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1 := pullback.lift_fst _ _ _
  have huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _

  have hbc : uκ ≫ bcMap (ΓM M H) hj ρO toκ htoκ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ sA := by
    apply pullback.hom_ext
    · rw [Category.assoc, XHDRLevel.bcMap_fst, huκ₁, Category.assoc]
    · rw [Category.assoc, XHDRLevel.bcMap_snd, ← Category.assoc, huκ₂, Category.id_comp, Category.assoc, hsA₁, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, hιAκ]
  have hcl : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))).base (IsLocalRing.closedPoint (ResidueField ↥A)) =
      IsLocalRing.closedPoint ↥A := IsLocalRing.comap_closedPoint (IsLocalRing.residue ↥A)

  set c := uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) with hc
  suffices hcross : c = (𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n) by
    have h1 : (bcMap (ΓM M H) hj ρO toκ htoκ).base c =
        sA.base ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))).base (IsLocalRing.closedPoint (ResidueField ↥A))) := by
      rw [hc, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hbc]
    rw [hcl] at h1
    rw [← h1, hcross]
    rfl

  haveI : IsProper (toBase p (ΓM M H) hj) := 𝔛.isProper
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

  obtain ⟨⟨h1mem, hP1⟩, ⟨h0mem, hP0⟩⟩ := 𝔛.node_pin A hA ρ hρ n
  have hn0 : 𝔛.placeOn0 A hA ρ hρ n = nd.1.1 := congrArg Prod.fst hn
  rcases 𝔛.comp_jointly_surjective A hA ρ hρ c with ⟨x₀, hx₀⟩ | ⟨x₁, hx₁⟩
  ·
    have hP₀pt : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base ((inv (𝔛.efib A hA ρ hρ)).base x₀) = c := by
      rw [Scheme.Hom.comp_apply, hinv, hx₀]
    have hr := hcompat 0 ((𝔛.Meta).pointEquivPlace.symm W) u hu uκ huκ₁ huκ₂ ⟨_, hclosed 0 x₀ hx₀⟩ hP₀pt
    have hP0' : (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨_, h0mem⟩ = 𝔛.placeOn0 A hA ρ hρ n := hP0
    rw [if_pos rfl, Equiv.apply_symm_apply, hW, ← hn0, ← hP0'] at hr

    have hPeq := (𝔛.Mfib A hA ρ hρ).placeOfPoint_bijective.1 hr
    have hxeq : x₀ = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n := by
      have := congrArg Subtype.val hPeq
      simp only at this
      rw [← hinv x₀, this, hinv]
    rw [← hx₀, hxeq]
  ·
    have hP₁pt : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base ((inv (𝔛.efib A hA ρ hρ)).base x₁) = c := by
      rw [Scheme.Hom.comp_apply, hinv, hx₁]
    have hr := hcompat' 1 ((𝔛.Meta).pointEquivPlace.symm W) u hu uκ huκ₁ huκ₂ ⟨_, hclosed 1 x₁ hx₁⟩ hP₁pt
    rw [if_neg (by decide), Equiv.apply_symm_apply, hW, ← hn0] at hr

    have hφ := (qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (JHNeronObjectAtP.ΓN p M H hpM)).1 hr

    rw [← hP1] at hφ
    have hPeq := (𝔛.Mfib A hA ρ hρ).placeOfPoint_bijective.1 hφ
    have hxeq : x₁ = (pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n := by
      have := congrArg Subtype.val hPeq
      simp only at this
      rw [← hinv x₁, ← this, hinv]
    rw [← hx₁, hxeq, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]

end S_ModularCurve_XHDRModelAtP_section_closedPoint_eq_crossing_of_reduceFst_eq_of_not_isStrict_of_offDiag
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_section_closedPoint_eq_crossing_of_reduceFst_eq_of_not_isStrict_of_offDiag (solution)
