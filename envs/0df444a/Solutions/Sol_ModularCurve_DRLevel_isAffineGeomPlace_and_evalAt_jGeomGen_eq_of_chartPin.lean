-- Prove2me | solution 1 for ModularCurve.DRLevel.isAffineGeomPlace_and_evalAt_jGeomGen_eq_of_chartPin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/fa95676a-bb1f-5669-9c87-07760771512e

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
import Theorems.Thm_ModularCurve_IgusaScheme_qExpand_jq_mem_chartAlgFin_and_jFull_mem_chartAlg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRLevel_isAffineGeomPlace_and_evalAt_jGeomGen_eq_of_chartPin
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
p2m_open "ModularCurve P2MW.S_ModularCurve_DRLevel_isAffineGeomPlace_and_evalAt_jGeomGen_eq_of_chartPin.ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel P2MW.S_ModularCurve_DRLevel_isAffineGeomPlace_and_evalAt_jGeomGen_eq_of_chartPin.ModularCurve.DRLevel"

set_option linter.unusedVariables false

namespace ModularCurve
p2m_export "ModularCurve" "DRLevel.R DRLevel.toBase0 DRLevel.fibre0 IgusaScheme.chartAlgFin IgusaScheme.jChartFin IgusaScheme IgusaScheme.ιFin qExpand jq modularFunctionFieldFull jqd_mem_full jGeomGen jNGeomGen IsAffineGeomPlace modularFunctionFieldC IgusaScheme.qExpand_jq_mem_chartAlgFin_and_jFull_mem_chartAlg"
namespace DRLevel
p2m_export "ModularCurve.DRLevel" "R X toBase toBase0 fibre0"
namespace ChartRead
p2m_open "ModularCurve.DRLevel ModularCurve"

universe u

theorem stalkClosedPointTo_germ_congr {K : Type u} [Field K] {Y : Scheme.{u}}
    (F₁ F₂ : Spec (CommRingCat.of K) ⟶ Y) (hF : F₁ = F₂) (W : Y.Opens) (t : Γ(Y, W))
    (h₁ : F₁.base (IsLocalRing.closedPoint K) ∈ W) (h₂ : F₂.base (IsLocalRing.closedPoint K) ∈ W) :
    (Scheme.stalkClosedPointTo F₁).hom ((Y.presheaf.germ W _ h₁).hom t) =
      (Scheme.stalkClosedPointTo F₂).hom ((Y.presheaf.germ W _ h₂).hom t) := by
  subst hF; rfl

theorem stalkClosedPointTo_germ_app {K : Type u} [Field K] {X Y : Scheme.{u}}
    (p : Spec (CommRingCat.of K) ⟶ X) (g : X ⟶ Y) (W : Y.Opens) (t : Γ(Y, W))
    (hx : g.base (p.base (IsLocalRing.closedPoint K)) ∈ W) :
    (Scheme.stalkClosedPointTo p).hom
        ((X.presheaf.germ (g ⁻¹ᵁ W) (p.base (IsLocalRing.closedPoint K)) hx).hom ((g.app W).hom t)) =
      (Scheme.stalkClosedPointTo (p ≫ g)).hom ((Y.presheaf.germ W ((p ≫ g).base (IsLocalRing.closedPoint K)) hx).hom t) := by
  rw [← Scheme.Hom.germ_stalkMap_apply g W (p.base (IsLocalRing.closedPoint K)) hx t, Scheme.stalkClosedPointTo_comp]
  rfl

theorem stalkClosedPointTo_specMap_comp {K : Type u} [Field K] {A : CommRingCat.{u}} {Y : Scheme.{u}}
    (ι : Spec A ⟶ Y) [IsOpenImmersion ι] (ψ : A ⟶ CommRingCat.of K) (b : A)
    (h : ι.base ((Spec.map ψ).base (IsLocalRing.closedPoint K)) ∈ ι ''ᵁ ⊤) :
    (Scheme.stalkClosedPointTo (Spec.map ψ ≫ ι)).hom
        ((Y.presheaf.germ (ι ''ᵁ ⊤) ((Spec.map ψ ≫ ι).base (IsLocalRing.closedPoint K)) h).hom
          ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv b))) = ψ b := by
  rw [Scheme.stalkClosedPointTo_comp]
  change (Scheme.stalkClosedPointTo (Spec.map ψ)).hom ((ι.stalkMap ((Spec.map ψ).base (IsLocalRing.closedPoint K))).hom
    ((Y.presheaf.germ (ι ''ᵁ ⊤) (ι.base ((Spec.map ψ).base (IsLocalRing.closedPoint K))) h).hom
      ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv b)))) = ψ b
  rw [Scheme.Hom.germ_stalkMap_apply ι (ι ''ᵁ ⊤) ((Spec.map ψ).base (IsLocalRing.closedPoint K)) h,
    ← CommRingCat.comp_apply (ι.appIso ⊤).inv, Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply',
    ← CommRingCat.comp_apply _ (Scheme.stalkClosedPointTo (Spec.map ψ)), Scheme.germ_stalkClosedPointTo_Spec,
    CommRingCat.comp_apply, Iso.inv_hom_id_apply]

end ModularCurve.DRLevel.ChartRead

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] (toκ : DRLevel.R q →+* κ)
    (M : CurveModel κ ↥(modularFunctionFieldC κ N₀)) (e : M.C ⟶ DRLevel.fibre0 (N₀ := N₀) toκ) [IsIso e]
    (heM : e ≫ pullback.snd _ _ = M.toBase)
    [hMne : Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ
      ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)))]
    (hMpin : ∀ b : ↥(IgusaScheme.chartAlgFin N₀ q),
        let readb : ↥(modularFunctionFieldC κ N₀) :=
          M.ffEquiv.symm
            (M.C.germToFunctionField
              ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤))
              (((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))).app ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)).hom
                (((IgusaScheme.ιFin N₀ q).appIso ⊤).inv
                  ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).inv b))))
        ((b = IgusaScheme.jChartFin N₀ q → readb = jGeomGen κ N₀) ∧
          (((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ) = qExpand ℚ N₀ jq → readb = jNGeomGen κ N₀)))
    (pt : Spec (CommRingCat.of κ) ⟶ DRLevel.fibre0 (N₀ := N₀) toκ) (hpt : pt ≫ pullback.snd _ _ = 𝟙 _)
    (ψ : ↥(IgusaScheme.chartAlgFin N₀ q) →+* κ)
    (hψ : pt ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom ψ) ≫ IgusaScheme.ιFin N₀ q) :
    ∃ h : (inv e).base (pt.base (IsLocalRing.closedPoint κ)) ∈ closedPoints M.C,
      (M.placeOfPoint ⟨_, h⟩).IsRational ∧ IsAffineGeomPlace κ N₀ (M.placeOfPoint ⟨_, h⟩) ∧
      (M.placeOfPoint ⟨_, h⟩).evalAt (jGeomGen κ N₀) = ψ (IgusaScheme.jChartFin N₀ q) := by
  open ModularCurve.DRLevel.ChartRead in

  have hsec : (pt ≫ inv e) ≫ M.toBase = 𝟙 _ := by
    rw [← heM, Category.assoc, IsIso.inv_hom_id_assoc, hpt]

  have hcl : (inv e).base (pt.base (IsLocalRing.closedPoint κ)) ∈ closedPoints M.C :=
    (pointEquivClosedPoint M.toBase ⟨pt ≫ inv e, hsec⟩).2
  refine ⟨hcl, ?_⟩

  have hP : M.placeOfPoint ⟨_, hcl⟩ = M.pointEquivPlace ⟨pt ≫ inv e, hsec⟩ := by
    rw [CurveModel.pointEquivPlace_apply]; rfl
  rw [hP]

  have hgfac : (pt ≫ inv e) ≫ (e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) =
      Spec.map (CommRingCat.ofHom ψ) ≫ IgusaScheme.ιFin N₀ q := by
    rw [Category.assoc, IsIso.inv_hom_id_assoc, hψ]
  have hxW : (Spec.map (CommRingCat.ofHom ψ) ≫ IgusaScheme.ιFin N₀ q).base (IsLocalRing.closedPoint κ) ∈
      (IgusaScheme.ιFin N₀ q) ''ᵁ (⊤ : (Spec (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).Opens) :=
    ⟨(Spec.map (CommRingCat.ofHom ψ)).base (IsLocalRing.closedPoint κ), trivial, rfl⟩
  have hxU : (e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base
      ((pt ≫ inv e).base (IsLocalRing.closedPoint κ)) ∈
      (IgusaScheme.ιFin N₀ q) ''ᵁ (⊤ : (Spec (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).Opens) := by
    rw [← Scheme.Hom.comp_apply, hgfac]; exact hxW

  have key : ∀ b : ↥(IgusaScheme.chartAlgFin N₀ q),
      ∃ g : M.C.presheaf.stalk ((pt ≫ inv e).base (IsLocalRing.closedPoint κ)),
        M.ffEquiv.symm (algebraMap _ M.C.functionField g) =
          M.ffEquiv.symm
            (M.C.germToFunctionField
              ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤))
              (((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))).app ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)).hom
                (((IgusaScheme.ιFin N₀ q).appIso ⊤).inv
                  ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).inv b)))) ∧
        (Scheme.stalkClosedPointTo (pt ≫ inv e)).hom g = ψ b := by
    intro b
    refine ⟨(M.C.presheaf.germ _ ((pt ≫ inv e).base (IsLocalRing.closedPoint κ)) hxU).hom
      (((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))).app ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)).hom
        (((IgusaScheme.ιFin N₀ q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).inv b))), ?_, ?_⟩
    ·
      change M.ffEquiv.symm ((M.C.presheaf.stalkSpecializes ((genericPoint_spec M.C).specializes trivial)).hom _) = _
      congr 1
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    · rw [stalkClosedPointTo_germ_app, stalkClosedPointTo_germ_congr _ _ hgfac _ _ _ hxW]
      exact stalkClosedPointTo_specMap_comp (IgusaScheme.ιFin N₀ q) (CommRingCat.ofHom ψ) b hxW

  have hpinj := (hMpin (IgusaScheme.jChartFin N₀ q)).1 rfl
  obtain ⟨-, hbmem, -⟩ := ModularCurve.IgusaScheme.qExpand_jq_mem_chartAlgFin_and_jFull_mem_chartAlg N₀ q N₀ dvd_rfl
  have hpinN := (hMpin ⟨⟨qExpand ℚ N₀ jq, jqd_mem_full N₀ dvd_rfl⟩, hbmem⟩).2 rfl
  obtain ⟨gj, hgj, hvj⟩ := key (IgusaScheme.jChartFin N₀ q)
  obtain ⟨gN, hgN, -⟩ := key ⟨⟨qExpand ℚ N₀ jq, jqd_mem_full N₀ dvd_rfl⟩, hbmem⟩
  rw [hpinj] at hgj
  rw [hpinN] at hgN

  have Hj := AlgebraicCurve.CurveModel.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo M ⟨pt ≫ inv e, hsec⟩ gj
  have HN := AlgebraicCurve.CurveModel.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo M ⟨pt ≫ inv e, hsec⟩ gN
  obtain ⟨hjmem, -, hjval⟩ := Hj
  obtain ⟨hNmem, -, -⟩ := HN
  rw [hgj] at hjmem hjval
  rw [hgN] at hNmem
  refine ⟨?_, ⟨hjmem, hNmem⟩, by rw [hjval, hvj]⟩

  intro r
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective r
  have hy : (y : ↥(modularFunctionFieldC κ N₀)) ∈ (M.placeOfPoint (pointEquivClosedPoint M.toBase ⟨pt ≫ inv e, hsec⟩)).toValuationSubring.toSubring := by
    rw [← CurveModel.pointEquivPlace_apply]; exact y.2
  rw [← M.range_stalk_eq] at hy
  obtain ⟨s, hs⟩ := hy
  obtain ⟨hsmem, hsres, -⟩ :=
    AlgebraicCurve.CurveModel.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo M ⟨pt ≫ inv e, hsec⟩ s
  refine ⟨(Scheme.stalkClosedPointTo (pt ≫ inv e)).hom s, ?_⟩
  rw [← hsres]
  congr 1
  exact Subtype.ext hs

end S_ModularCurve_DRLevel_isAffineGeomPlace_and_evalAt_jGeomGen_eq_of_chartPin
end P2MW
export P2MW.S_ModularCurve_DRLevel_isAffineGeomPlace_and_evalAt_jGeomGen_eq_of_chartPin (solution)
