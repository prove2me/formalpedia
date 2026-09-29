-- Prove2me | solution 1 for ModularCurve.DRLevel.fromSpecStalk_comp_eq_of_chartPin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e3f09cb6-4789-50db-99bb-f0813feb0496

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Theorems.Thm_ModularCurve_IgusaScheme_qExpand_jq_mem_chartAlgFin_and_jFull_mem_chartAlg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRLevel_fromSpecStalk_comp_eq_of_chartPin
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

theorem GENID_ringHom_ext {K : Type*} [Field K] (N : ℕ) [NeZero N] {L : Type*} [Field L]
    (f g : ↥(modularFunctionFieldC K N) →+* L)
    (hK : ∀ a : K, f (algebraMap K ↥(modularFunctionFieldC K N) a) = g (algebraMap K ↥(modularFunctionFieldC K N) a))
    (hj : f (jGeomGen K N) = g (jGeomGen K N)) (hjN : f (jNGeomGen K N) = g (jNGeomGen K N)) : f = g := by
  apply RingHom.ext
  rintro ⟨x, hx⟩
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
      rcases hx with rfl | rfl
      · exact hj
      · exact hjN
  | algebraMap a => exact hK a
  | add x y hx hy ihx ihy =>
      show f (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
      rw [map_add, map_add, ihx, ihy]
  | inv x hx ih =>
      show f (⟨x, hx⟩⁻¹) = g (⟨x, hx⟩⁻¹)
      rw [map_inv₀, map_inv₀, ih]
  | mul x y hx hy ihx ihy =>
      show f (⟨x, hx⟩ * ⟨y, hy⟩) = g (⟨x, hx⟩ * ⟨y, hy⟩)
      rw [map_mul, map_mul, ihx, ihy]

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)

    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)

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

    (M' : CurveModel κ ↥(modularFunctionFieldC κ N₀)) (e' : M'.C ⟶ DRLevel.fibre0 (N₀ := N₀) toκ) [IsIso e']
    (heM' : e' ≫ pullback.snd _ _ = M'.toBase)
    [hMne' : Nonempty (Scheme.Opens.toScheme ((e' ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ
      ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)))]
    (hMpin' : ∀ b : ↥(IgusaScheme.chartAlgFin N₀ q),
        let readb' : ↥(modularFunctionFieldC κ N₀) :=
          M'.ffEquiv.symm
            (M'.C.germToFunctionField
              ((e' ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤))
              (((e' ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))).app ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)).hom
                (((IgusaScheme.ιFin N₀ q).appIso ⊤).inv
                  ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).inv b))))
        ((b = IgusaScheme.jChartFin N₀ q → readb' = jGeomGen κ N₀) ∧
          (((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ) = qExpand ℚ N₀ jq → readb' = jNGeomGen κ N₀))) :
    M.C.fromSpecStalk (genericPoint M.C) ≫ e ≫ inv e' =
      Spec.map (CommRingCat.ofHom (M.ffEquiv.toRingHom.comp M'.ffEquiv.symm.toRingHom)) ≫
        M'.C.fromSpecStalk (genericPoint M'.C) := by

  let θ : M.C ⟶ M'.C := e ≫ inv e'
  have hθfst : θ ≫ e' ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)) =
      e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)) := by
    simp [θ]
  have hθbase : θ ≫ M'.toBase = M.toBase := by
    rw [← heM', ← heM]; simp [θ]
  have hθη : θ.base (genericPoint M.C) = genericPoint M'.C := genericPoint_eq_of_isOpenImmersion θ
  have hspec : θ.base (genericPoint M.C) ⤳ genericPoint M'.C := hθη ▸ specializes_rfl

  let ψ : M'.C.functionField ⟶ M.C.functionField :=
    M'.C.presheaf.stalkSpecializes hspec ≫ θ.stalkMap (genericPoint M.C)

  have aux : ∀ {Y : Scheme} (W : Y.Opens) (t : Γ(Y, W)) (G₁ G₂ : M.C ⟶ Y) (hG : G₁ = G₂)
      (h₁ : G₁.base (genericPoint M.C) ∈ W) (h₂ : G₂.base (genericPoint M.C) ∈ W),
      M.C.presheaf.germ (G₁ ⁻¹ᵁ W) (genericPoint M.C) h₁ ((G₁.app W).hom t) =
        M.C.presheaf.germ (G₂ ⁻¹ᵁ W) (genericPoint M.C) h₂ ((G₂.app W).hom t) := by
    intro Y W t G₁ G₂ hG h₁ h₂; subst hG; rfl

  have hψgerm : ∀ (V : M'.C.Opens) (hV : genericPoint M'.C ∈ V) (s : Γ(M'.C, V)),
      ψ.hom ((M'.C.presheaf.germ V (genericPoint M'.C) hV).hom s) =
        (M.C.presheaf.germ (θ ⁻¹ᵁ V) (genericPoint M.C) (by show θ.base _ ∈ V; rw [hθη]; exact hV)).hom ((θ.app V).hom s) := by
    intro V hV s
    show (θ.stalkMap (genericPoint M.C)).hom ((M'.C.presheaf.stalkSpecializes hspec).hom
      ((M'.C.presheaf.germ V (genericPoint M'.C) hV).hom s)) = _
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]

  have hψK : ∀ a : κ, ψ.hom (M'.ffEquiv (algebraMap κ ↥(modularFunctionFieldC κ N₀) a)) =
      M.ffEquiv (algebraMap κ ↥(modularFunctionFieldC κ N₀) a) := by
    intro a
    rw [M'.ffEquiv_algebraMap, M.ffEquiv_algebraMap]
    show ψ.hom ((M'.C.presheaf.germ ⊤ (genericPoint M'.C) trivial).hom
      (M'.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom a))) =
      (M.C.presheaf.germ ⊤ (genericPoint M.C) trivial).hom (M.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom a))
    rw [hψgerm]
    have := aux (Y := Spec (CommRingCat.of κ)) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom a) (θ ≫ M'.toBase) M.toBase hθbase
      trivial trivial
    simp [Scheme.Hom.comp_app] at this
    exact this

  set W : (IgusaScheme N₀ q).Opens := (IgusaScheme.ιFin N₀ q) ''ᵁ ⊤ with hW
  have hpinj := (hMpin (IgusaScheme.jChartFin N₀ q)).1 rfl
  have hpinj' := (hMpin' (IgusaScheme.jChartFin N₀ q)).1 rfl

  have hgenU : (e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base (genericPoint M.C) ∈ W := by
    obtain ⟨⟨y, hy⟩⟩ := hMne
    exact (genericPoint_specializes y).mem_open
      ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ W).2 hy

  have hψj : ψ.hom (M'.ffEquiv (jGeomGen κ N₀)) = M.ffEquiv (jGeomGen κ N₀) := by
    conv_lhs => rw [← hpinj']
    conv_rhs => rw [← hpinj]
    simp only [RingEquiv.apply_symm_apply]
    dsimp only [Scheme.germToFunctionField]
    rw [hψgerm]
    have hθF : θ ≫ e' ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)) =
        e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)) := hθfst
    have := aux W ((((IgusaScheme.ιFin N₀ q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).inv
        (IgusaScheme.jChartFin N₀ q)))) (θ ≫ e' ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)))
        (e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) hθF
        (by rw [hθF]; exact hgenU) hgenU
    simp [Scheme.Hom.comp_app] at this
    exact this

  have hψjN : ψ.hom (M'.ffEquiv (jNGeomGen κ N₀)) = M.ffEquiv (jNGeomGen κ N₀) := by
    obtain ⟨-, hbmem, -⟩ := ModularCurve.IgusaScheme.qExpand_jq_mem_chartAlgFin_and_jFull_mem_chartAlg N₀ q N₀ dvd_rfl
    let b : ↥(IgusaScheme.chartAlgFin N₀ q) := ⟨⟨qExpand ℚ N₀ jq, jqd_mem_full N₀ dvd_rfl⟩, hbmem⟩
    have hb : (((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ)) = qExpand ℚ N₀ jq := rfl
    have hpinN := (hMpin b).2 hb
    have hpinN' := (hMpin' b).2 hb
    conv_lhs => rw [← hpinN']
    conv_rhs => rw [← hpinN]
    simp only [RingEquiv.apply_symm_apply]
    dsimp only [Scheme.germToFunctionField]
    rw [hψgerm]
    have hθF : θ ≫ e' ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)) =
        e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)) := hθfst
    have := aux W ((((IgusaScheme.ιFin N₀ q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).inv b)))
        (θ ≫ e' ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)))
        (e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) hθF
        (by rw [hθF]; exact hgenU) hgenU
    simp [Scheme.Hom.comp_app] at this
    exact this

  have hψff : ψ.hom.comp M'.ffEquiv.toRingHom = M.ffEquiv.toRingHom :=
    GENID_ringHom_ext N₀ _ _ hψK hψj hψjN
  have hψ : ψ = CommRingCat.ofHom (M.ffEquiv.toRingHom.comp M'.ffEquiv.symm.toRingHom) := by
    apply CommRingCat.hom_ext
    rw [CommRingCat.hom_ofHom, ← hψff, RingHom.comp_assoc, RingEquiv.toRingHom_comp_symm_toRingHom, RingHom.comp_id]

  rw [← hψ]
  simp only [ψ, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]
  rfl

end S_ModularCurve_DRLevel_fromSpecStalk_comp_eq_of_chartPin
end P2MW
export P2MW.S_ModularCurve_DRLevel_fromSpecStalk_comp_eq_of_chartPin (solution)
