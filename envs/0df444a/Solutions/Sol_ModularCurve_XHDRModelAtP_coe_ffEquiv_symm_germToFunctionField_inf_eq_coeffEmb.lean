-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_inf_eq_coeffEmb
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ce26da7d-8de8-5f9d-ac56-0774211649c6

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_inf_eq_coeffEmb

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve Opposite

namespace TwoChartRead

open AlgebraicCurve.TwoChartIntegralModel

variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
variable {Z : Scheme.{u}} [IrreducibleSpace Z] (g : Z ⟶ TwoChartIntegralModel R F j)

noncomputable def readHom {B : Type u} [CommRing B] (ι : Spec (CommRingCat.of B) ⟶ TwoChartIntegralModel R F j)
    [IsOpenImmersion ι] [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ (ι ''ᵁ ⊤)))] :
    CommRingCat.of B ⟶ Z.functionField :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (ι.appIso ⊤).inv ≫ g.app (ι ''ᵁ ⊤) ≫
    Z.germToFunctionField (g ⁻¹ᵁ (ι ''ᵁ ⊤))

theorem readHom_apply {B : Type u} [CommRing B] (ι : Spec (CommRingCat.of B) ⟶ TwoChartIntegralModel R F j)
    [IsOpenImmersion ι] [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ (ι ''ᵁ ⊤)))] (b : B) :
    (readHom j g ι).hom b = Z.germToFunctionField (g ⁻¹ᵁ (ι ''ᵁ ⊤))
      ((g.app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b))) := rfl

omit [IrreducibleSpace Z] in

theorem mem_mid_of_mem (x : Z)
    (hF : g.base x ∈ (ιFin R F j) ''ᵁ ⊤) (hI : g.base x ∈ (ιInf R F j) ''ᵁ ⊤) :
    g.base x ∈ (fFin R F j ≫ ιFin R F j) ''ᵁ ⊤ := by
  rw [Scheme.Hom.image_top_eq_opensRange] at hF hI ⊢
  obtain ⟨xF, hxF⟩ := hF
  obtain ⟨xI, hxI⟩ := hI
  have h := hxF.trans hxI.symm
  obtain ⟨k, fi, fj, xm, h1, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span (fFin R F j) (fInf R F j))
    (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := xF) (xj := xI)).mp h
  rcases k with _ | k
  · have hfi : fi = WalkingSpan.Hom.fst := Subsingleton.elim _ _
    subst hfi
    refine ⟨xm, ?_⟩
    rw [← hxF, ← h1]
    rfl
  · rcases k
    · exact nomatch fj
    · exact nomatch fi

theorem app_germToFunctionField_eq {V V' : (TwoChartIntegralModel R F j).Opens} (hle : V' ≤ V)
    [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ V))] [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ V'))] :
    g.app V ≫ Z.germToFunctionField (g ⁻¹ᵁ V) =
      (TwoChartIntegralModel R F j).presheaf.map (homOfLE hle).op ≫ g.app V' ≫ Z.germToFunctionField (g ⁻¹ᵁ V') := by
  rw [Scheme.Hom.naturality_assoc]
  simp only [Scheme.germToFunctionField]
  rw [TopCat.Presheaf.germ_res]

noncomputable abbrev ιMid : XMid R F j ⟶ TwoChartIntegralModel R F j := fFin R F j ≫ ιFin R F j

theorem ιMid_le_fin : (ιMid j) ''ᵁ ⊤ ≤ (ιFin R F j) ''ᵁ ⊤ := by
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.image_top_eq_opensRange]
  rintro _ ⟨x, rfl⟩
  exact ⟨fFin R F j x, rfl⟩

theorem ιMid_le_inf : (ιMid j) ''ᵁ ⊤ ≤ (ιInf R F j) ''ᵁ ⊤ := by
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.image_top_eq_opensRange]
  rintro _ ⟨x, rfl⟩
  refine ⟨fInf R F j x, ?_⟩
  show (fInf R F j ≫ ιInf R F j).base x = (fFin R F j ≫ ιFin R F j).base x
  rw [glue_condition]

theorem appIso_inv_appLE_of_eq {B B' : Type u} [CommRing B] [CommRing B']
    (ι : Spec (CommRingCat.of B) ⟶ TwoChartIntegralModel R F j) [IsOpenImmersion ι]
    (φ : B →+* B') (κ : Spec (CommRingCat.of B') ⟶ TwoChartIntegralModel R F j)
    (hκ : κ = Spec.map (CommRingCat.ofHom φ) ≫ ι) (e : (⊤ : (Spec (CommRingCat.of B')).Opens) ≤ κ ⁻¹ᵁ (ι ''ᵁ ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (ι.appIso ⊤).inv ≫ κ.appLE (ι ''ᵁ ⊤) ⊤ e =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of B')).inv := by
  subst hκ
  have h2 : (Spec.map (CommRingCat.ofHom φ) ≫ ι).appLE (ι ''ᵁ ⊤) ⊤ e =
      ι.appLE (ι ''ᵁ ⊤) ⊤ (by rw [Scheme.Hom.preimage_image_eq]) ≫ (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_top := by
    rw [Scheme.Hom.appLE_comp_appLE]
  have h3 : (ι.appIso ⊤).inv ≫ ι.appLE (ι ''ᵁ ⊤) ⊤ (by rw [Scheme.Hom.preimage_image_eq]) = 𝟙 _ := by
    rw [Scheme.Hom.appIso_inv_appLE]
    convert (Spec (CommRingCat.of B)).presheaf.map_id _
    rfl
  have h4 : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_top = (Spec.map (CommRingCat.ofHom φ)).appTop :=
    Scheme.Hom.appLE_eq_app _
  rw [h2, ← Category.assoc (ι.appIso ⊤).inv, h3, Category.id_comp, h4, ← Scheme.ΓSpecIso_inv_naturality]

theorem appIso_inv_map_of_eq {B : Type u} [CommRing B]
    (ι : Spec (CommRingCat.of B) ⟶ TwoChartIntegralModel R F j) [IsOpenImmersion ι]
    (φ : B →+* chartAlgMid R F j) (hκ : ιMid j = Spec.map (CommRingCat.ofHom φ) ≫ ι) (hle : (ιMid j) ''ᵁ ⊤ ≤ ι ''ᵁ ⊤) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (ι.appIso ⊤).inv ≫
        (TwoChartIntegralModel R F j).presheaf.map (homOfLE hle).op =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgMid R F j))).inv ≫ ((ιMid j).appIso ⊤).inv := by
  rw [← Category.assoc (CommRingCat.ofHom φ), ← appIso_inv_appLE_of_eq j ι φ (ιMid j) hκ
    (by rw [hκ]; rintro x -; show _ ∈ ι ''ᵁ ⊤; rw [Scheme.Hom.image_top_eq_opensRange]; exact ⟨_, rfl⟩)]
  simp only [Category.assoc]
  congr 2
  rw [← cancel_mono ((ιMid j).appIso ⊤).hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

theorem readHom_fin [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ ((ιFin R F j) ''ᵁ ⊤)))]
    [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ ((ιMid j) ''ᵁ ⊤)))] :
    readHom j g (ιFin R F j) = CommRingCat.ofHom (inclFin R F j).toRingHom ≫ readHom j g (ιMid j) := by
  simp only [readHom]
  have H := appIso_inv_map_of_eq j (ιFin R F j) (inclFin R F j).toRingHom rfl (ιMid_le_fin j)
  rw [app_germToFunctionField_eq j g (ιMid_le_fin j), reassoc_of% H]

theorem readHom_inf [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ ((ιInf R F j) ''ᵁ ⊤)))]
    [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ ((ιMid j) ''ᵁ ⊤)))] :
    readHom j g (ιInf R F j) = CommRingCat.ofHom (inclInf R F j).toRingHom ≫ readHom j g (ιMid j) := by
  simp only [readHom]
  have H := appIso_inv_map_of_eq j (ιInf R F j) (inclInf R F j).toRingHom (glue_condition R F j) (ιMid_le_inf j)
  rw [app_germToFunctionField_eq j g (ιMid_le_inf j), reassoc_of% H]

theorem nonempty_mid [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ ((ιFin R F j) ''ᵁ ⊤)))]
    [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ ((ιInf R F j) ''ᵁ ⊤)))] :
    Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ ((ιMid j) ''ᵁ ⊤))) := by
  have hF : genericPoint Z ∈ g ⁻¹ᵁ ((ιFin R F j) ''ᵁ ⊤) := by
    obtain ⟨⟨x, hx⟩⟩ := ‹Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ ((ιFin R F j) ''ᵁ ⊤)))›
    refine ((genericPoint_spec Z).mem_open_set_iff (g ⁻¹ᵁ ((ιFin R F j) ''ᵁ ⊤)).isOpen).mpr ?_
    simp only [Set.top_eq_univ, Set.univ_inter, Set.inter_univ]
    exact ⟨x, hx⟩
  have hI : genericPoint Z ∈ g ⁻¹ᵁ ((ιInf R F j) ''ᵁ ⊤) := by
    obtain ⟨⟨x, hx⟩⟩ := ‹Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ ((ιInf R F j) ''ᵁ ⊤)))›
    refine ((genericPoint_spec Z).mem_open_set_iff (g ⁻¹ᵁ ((ιInf R F j) ''ᵁ ⊤)).isOpen).mpr ?_
    simp only [Set.top_eq_univ, Set.univ_inter, Set.inter_univ]
    exact ⟨x, hx⟩
  exact ⟨⟨genericPoint Z, mem_mid_of_mem j g _ hF hI⟩⟩

theorem readHom_fin_eq_pow_mul_readHom_inf [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ ((ιFin R F j) ''ᵁ ⊤)))]
    [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ ((ιInf R F j) ''ᵁ ⊤)))]
    (a : chartAlgInf R F j) (c : chartAlgFin R F j) (n : ℕ) (hc : (c : F) = j ^ n * a) :
    (readHom j g (ιFin R F j)).hom c =
      (readHom j g (ιFin R F j)).hom (jChartFin R F j) ^ n * (readHom j g (ιInf R F j)).hom a := by
  haveI := nonempty_mid j g
  have hmid : inclFin R F j c = inclFin R F j (jChartFin R F j) ^ n * inclInf R F j a := by
    apply Subtype.ext
    simp only [coe_chartIncl, Subalgebra.coe_mul, Subalgebra.coe_pow, coe_jChartFin]
    exact hc
  rw [readHom_fin, readHom_inf]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, hmid, map_mul, map_pow]

end TwoChartRead

set_option maxHeartbeats 6400000 in
open ModularCurve ModularCurve.XHDRLevel TwoChartRead AlgebraicCurve.TwoChartIntegralModel in
open scoped MatrixGroups in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [Nonempty (Scheme.Opens.toScheme ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
      (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)))]
    (a : ↥(chartAlgInf p (ΓM M H) hj)) :
    ((𝔛.Meta.ffEquiv.symm
        (𝔛.Meta.C.germToFunctionField
          ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
            ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))
          (((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app
              ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom
            (((ιInf p (ΓM M H) hj).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv a))))
        : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((a : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) := by
  haveI := 𝔛.Meta_chart_nonempty

  have ha : (a : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ∈
      chartAlg (XHDRLevel.R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) {(jAt (ΓM M H) hj)⁻¹, jAt (ΓM M H) hj} := by
    rw [Set.pair_comm]
    exact chartAlg_mono (XHDRLevel.R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (sInf_subset _ _) a.2
  obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartAlg (R := XHDRLevel.R p)
    (S := ({(jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H)))} : Set _))
    (s := (jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H)))) rfl (Fact.out) ha
  let c : ↥(chartAlgFin p (ΓM M H) hj) := ⟨_, hn⟩
  have hmul := readHom_fin_eq_pow_mul_readHom_inf (jAt (ΓM M H) hj)
    (𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
    a c n rfl

  have hφ := congrArg
    (fun x => ((𝔛.Meta.ffEquiv.symm x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))) hmul
  simp only [map_mul, map_pow, MulMemClass.coe_mul, SubmonoidClass.coe_pow] at hφ
  rw [readHom_apply, readHom_apply, readHom_apply, 𝔛.Meta_pin, 𝔛.Meta_pin] at hφ

  have hc : coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      coeffEmb (AlgebraicClosure ℚ)
          ((TwoChartIntegralModel.jChartFin (XHDRLevel.R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) :
            ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) ^ n *
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) := by
    rw [← map_pow, ← map_mul]
    rfl
  rw [hc] at hφ
  have hj0 : coeffEmb (AlgebraicClosure ℚ)
      ((TwoChartIntegralModel.jChartFin (XHDRLevel.R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) :
        ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) ≠ 0 := by
    rw [TwoChartIntegralModel.coe_jChartFin, coe_jAt]
    exact (map_ne_zero_iff _ (coeffEmb (AlgebraicClosure ℚ)).injective).mpr jqModC_rat_ne_zero
  exact (mul_left_cancel₀ (pow_ne_zero n hj0) hφ).symm

end S_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_inf_eq_coeffEmb
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_inf_eq_coeffEmb (solution)
