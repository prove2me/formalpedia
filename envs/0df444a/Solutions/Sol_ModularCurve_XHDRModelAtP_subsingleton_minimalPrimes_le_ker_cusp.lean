-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.subsingleton_minimalPrimes_le_ker_cusp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/d9ecc773-4228-5e44-aaa5-865c7ab54eed

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_XHDRLevel_exists_retraction_chartInf_comp_zero_eq_of_dvd
import Theorems.Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffMap_of_mfib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_subsingleton_minimalPrimes_le_ker_cusp
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve P2MW.S_ModularCurve_XHDRModelAtP_subsingleton_minimalPrimes_le_ker_cusp.AlgebraicCurve ModularCurve ModularCurve.XHDRLevel"
open scoped MatrixGroups TensorProduct

universe u

noncomputable section

namespace DictGlue

section Rings

variable {R κ O O' : Type*} [CommRing R] [CommRing κ] [CommRing O] [CommRing O'] [Algebra R κ] [Algebra R O] [Algebra R O']

theorem comm_comp_includeLeftRingHom :
    (Algebra.TensorProduct.comm R O κ).toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := O) (B := κ)) =
      (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O)).toRingHom := by
  refine RingHom.ext fun o => ?_
  show Algebra.TensorProduct.comm R O κ (o ⊗ₜ[R] (1 : κ)) = (1 : κ) ⊗ₜ[R] o
  exact Algebra.TensorProduct.comm_tmul R o (1 : κ)

theorem comm_comp_includeRight :
    (Algebra.TensorProduct.comm R O κ).toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := R) (A := O) (B := κ)).toRingHom =
      Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := O) := by
  refine RingHom.ext fun a => ?_
  show Algebra.TensorProduct.comm R O κ ((1 : O) ⊗ₜ[R] a) = a ⊗ₜ[R] (1 : O)
  exact Algebra.TensorProduct.comm_tmul R (1 : O) a

theorem map_id_comp_includeRight (ι : O' →ₐ[R] O) :
    (Algebra.TensorProduct.map (AlgHom.id R κ) ι).toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O')).toRingHom =
      (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O)).toRingHom.comp ι.toRingHom := by
  refine RingHom.ext fun b => ?_
  show Algebra.TensorProduct.map (AlgHom.id R κ) ι ((1 : κ) ⊗ₜ[R] b) = (1 : κ) ⊗ₜ[R] (ι b)
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem map_id_comp_includeLeftRingHom (ι : O' →ₐ[R] O) :
    (Algebra.TensorProduct.map (AlgHom.id R κ) ι).toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := O')) =
      Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := O) := by
  refine RingHom.ext fun a => ?_
  show Algebra.TensorProduct.map (AlgHom.id R κ) ι (a ⊗ₜ[R] (1 : O')) = a ⊗ₜ[R] (1 : O)
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

end Rings

section Chart

variable (p : ℕ) (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (κ : Type) [CommRing κ] [Algebra (R p) κ]

theorem chartInf_baseChange :
    ∃ g : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p Γ hj))) ⟶ fibre (Γ := Γ) (hj := hj) (algebraMap (R p) κ),
      IsOpenImmersion g ∧
      g ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := R p) (A := κ) (B := ↥(chartAlgInf p Γ hj))).toRingHom) ≫ ιInf p Γ hj ∧
      g ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := R p) (A := κ) (B := ↥(chartAlgInf p Γ hj)))) ∧
      Set.range g.base = ((pullback.fst (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)))) ⁻¹ᵁ
        ((ιInf p Γ hj) ''ᵁ ⊤) : Set ↥(fibre (Γ := Γ) (hj := hj) (algebraMap (R p) κ))) := by
  set A : Type := ↥(chartAlgInf p Γ hj) with hA
  set b : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of (R p)) := Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)) with hb
  set a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (R p)) := Spec.map (CommRingCat.ofHom (algebraMap (R p) A)) with ha
  have hιa : ιInf p Γ hj ≫ toBase p Γ hj = a := TwoChartIntegralModel.ιInf_toBase _ _ _
  let g' : pullback a b ⟶ pullback (toBase p Γ hj) b :=
    pullback.lift (pullback.fst a b ≫ ιInf p Γ hj) (pullback.snd a b) (by rw [Category.assoc, hιa, pullback.condition])
  have hg'fst : g' ≫ pullback.fst _ _ = pullback.fst a b ≫ ιInf p Γ hj := pullback.lift_fst _ _ _
  have hg'snd : g' ≫ pullback.snd _ _ = pullback.snd a b := pullback.lift_snd _ _ _
  have sq : IsPullback (pullback.fst a b) g' (ιInf p Γ hj) (pullback.fst (toBase p Γ hj) b) := by
    refine IsPullback.of_bot ?_ hg'fst.symm (IsPullback.of_hasPullback (toBase p Γ hj) b)
    rw [hg'snd, hιa]
    exact IsPullback.of_hasPullback a b
  have hopen : IsOpenImmersion g' := MorphismProperty.of_isPullback sq inferInstance
  have hrange : Set.range g'.base = ((pullback.fst (toBase p Γ hj) b) ⁻¹ᵁ ((ιInf p Γ hj) ''ᵁ ⊤) : Set _) := by
    have e1 : g' = sq.isoPullback.hom ≫ pullback.snd (ιInf p Γ hj) (pullback.fst (toBase p Γ hj) b) :=
      (sq.isoPullback_hom_snd).symm
    have hs1 : Function.Surjective sq.isoPullback.hom.base := sq.isoPullback.hom.homeomorph.surjective
    rw [e1, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr hs1, Set.image_univ,
      Scheme.Pullback.range_snd]
    ext x
    simp only [Set.mem_preimage, Set.mem_range]
    constructor
    · rintro ⟨y, hy⟩; exact ⟨y, trivial, hy⟩
    · rintro ⟨y, -, hy⟩; exact ⟨y, hy⟩

  set gq : Spec (CommRingCat.of (A ⊗[R p] κ)) ⟶ pullback (toBase p Γ hj) b := (pullbackSpecIso (R p) A κ).inv ≫ g' with hgq
  have hgqfst : gq ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
      (R := R p) (A := A) (B := κ))) ≫ ιInf p Γ hj := by
    rw [hgq, Category.assoc, hg'fst, ← Category.assoc, pullbackSpecIso_inv_fst]
  have hgqsnd : gq ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
      (R := R p) (A := A) (B := κ)).toRingHom) := by
    rw [hgq, Category.assoc, hg'snd, pullbackSpecIso_inv_snd]
    rfl
  set tw : Spec (CommRingCat.of (κ ⊗[R p] A)) ⟶ Spec (CommRingCat.of (A ⊗[R p] κ)) :=
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.comm (R p) A κ).toAlgHom.toRingHom) with htw
  haveI : IsIso tw := by
    have e : tw = Spec.map ((Algebra.TensorProduct.comm (R p) A κ).toRingEquiv.toCommRingCatIso.hom) := rfl
    rw [e]
    infer_instance
  refine ⟨tw ≫ gq, inferInstance, ?_, ?_, ?_⟩
  · rw [Category.assoc, hgqfst, ← Category.assoc, htw, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      comm_comp_includeLeftRingHom]
  · rw [Category.assoc, hgqsnd, htw, ← Spec.map_comp, ← CommRingCat.ofHom_comp, comm_comp_includeRight]
  · have hs2 : Function.Surjective (pullbackSpecIso (R p) A κ).inv.base := (pullbackSpecIso (R p) A κ).inv.homeomorph.surjective
    have hs3 : Function.Surjective tw.base := (asIso tw).hom.homeomorph.surjective
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr hs3, Set.image_univ, hgq,
      Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr hs2, Set.image_univ, hrange]

theorem isOpenImmersion_and_range_of_comp_eq
    (c' : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p Γ hj))) ⟶ fibre (Γ := Γ) (hj := hj) (algebraMap (R p) κ))
    (hc'fst : c' ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p Γ hj))).toRingHom) ≫ ιInf p Γ hj)
    (hc'snd : c' ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgInf p Γ hj))))) :
    IsOpenImmersion c' ∧
      Set.range c'.base = ((pullback.fst (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)))) ⁻¹ᵁ
        ((ιInf p Γ hj) ''ᵁ ⊤) : Set ↥(fibre (Γ := Γ) (hj := hj) (algebraMap (R p) κ))) := by
  obtain ⟨g, hg, hgfst, hgsnd, hrange⟩ := chartInf_baseChange p Γ hj κ
  have heq : c' = g := by
    apply pullback.hom_ext
    · rw [hc'fst, hgfst]
    · rw [hc'snd, hgsnd]
  subst heq
  exact ⟨hg, hrange⟩

end Chart

section Bundle

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
  (𝔓 : XHDRModelAtP p M H hpM hj) (κ : Type) [CommRing κ] [Algebra (R p) κ]

theorem fibreMap_comp_fst {Γ Γ' : Subgroup SL(2, ℤ)}
    (φ : NeronModelInfra.SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj)) (toκ : R p →+* κ) :
    fibreMap φ toκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ φ.1 := by
  unfold fibreMap
  rw [pullback.lift_fst]

theorem fibreMap_comp_snd {Γ Γ' : Subgroup SL(2, ℤ)}
    (φ : NeronModelInfra.SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj)) (toκ : R p →+* κ) :
    fibreMap φ toκ ≫ pullback.snd _ _ = pullback.snd _ _ := by
  unfold fibreMap
  rw [pullback.lift_snd, Category.comp_id]

theorem comp_fibreMap_pi_eq_spec_map_comp
    (c' : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))) ⟶
      fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ))
    (hc'fst : c' ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom) ≫ ιInf p (ΓM M H) hj)
    (hc'snd : c' ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj)))))
    (c₀ : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj))) ⟶
      fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) κ))
    (hc₀fst : c₀ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓN p M H hpM) hj))).toRingHom) ≫ ιInf p (ΓN p M H hpM) hj)
    (hc₀snd : c₀ ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓN p M H hpM) hj))))) :
    c' ≫ fibreMap 𝔓.π (algebraMap (R p) κ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id (R p) κ) 𝔓.iotaInf).toRingHom) ≫ c₀ := by
  apply pullback.hom_ext
  · rw [Category.assoc, fibreMap_comp_fst, ← Category.assoc, hc'fst, Category.assoc, 𝔓.pi_chartInf, ← Category.assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, Category.assoc, hc₀fst, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, map_id_comp_includeRight]
  · rw [Category.assoc, fibreMap_comp_snd, hc'snd, Category.assoc, hc₀snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      map_id_comp_includeLeftRingHom]

theorem spec_map_comp_eq_sectionFibre_εinf
    (c' : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))) ⟶
      fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ))
    (hc'fst : c' ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom) ≫ ιInf p (ΓM M H) hj)
    (hc'snd : c' ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj)))))
    (ev : κ ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj) →ₐ[κ] κ)
    (hev : ∀ b : ↥(chartAlgInf p (ΓM M H) hj), ev ((1 : κ) ⊗ₜ[R p] b) = algebraMap (R p) κ (𝔓.rhoInf b)) :
    Spec.map (CommRingCat.ofHom ev.toRingHom) ≫ c' = sectionFibre 𝔓.εinf (algebraMap (R p) κ) := by
  have h1 : ev.toRingHom.comp (Algebra.TensorProduct.includeRight
      (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom =
      (algebraMap (R p) κ).comp 𝔓.rhoInf.toRingHom := by
    refine RingHom.ext fun b => ?_
    exact hev b
  have h2 : ev.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom
      (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj))) = RingHom.id κ := by
    refine RingHom.ext fun a => ?_
    show ev (a ⊗ₜ[R p] (1 : ↥(chartAlgInf p (ΓM M H) hj))) = a
    exact ev.commutes a
  apply pullback.hom_ext
  · rw [Category.assoc, hc'fst, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h1, CommRingCat.ofHom_comp,
      Spec.map_comp, Category.assoc, ← 𝔓.εinf_chart, sectionFibre, pullback.lift_fst]
  · rw [Category.assoc, hc'snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h2, CommRingCat.ofHom_id, Spec.map_id,
      sectionFibre, pullback.lift_snd]

theorem base_spec_map_mem_range_sectionFibre_εinf
    (c' : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))) ⟶
      fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ))
    (hc'fst : c' ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom) ≫ ιInf p (ΓM M H) hj)
    (hc'snd : c' ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj)))))
    (ev : κ ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj) →ₐ[κ] κ)
    (hev : ∀ b : ↥(chartAlgInf p (ΓM M H) hj), ev ((1 : κ) ⊗ₜ[R p] b) = algebraMap (R p) κ (𝔓.rhoInf b))
    (x : ↥(Spec (CommRingCat.of κ))) :
    c'.base ((Spec.map (CommRingCat.ofHom ev.toRingHom)).base x) ∈
      Set.range (sectionFibre 𝔓.εinf (algebraMap (R p) κ)).base := by
  refine ⟨x, ?_⟩
  have := congrArg (fun f => f.base x) (spec_map_comp_eq_sectionFibre_εinf 𝔓 κ c' hc'fst hc'snd ev hev)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
  exact this.symm

end Bundle

end DictGlue

namespace DictGlue

section Reshapes

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
  (𝔓 : XHDRModelAtP p M H hpM hj) (κ : Type) [CommRing κ] [Algebra (R p) κ]

theorem map_id_kappa_toRingHom_eq :
    (Algebra.TensorProduct.map (AlgHom.id κ κ) 𝔓.iotaInf).toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id (R p) κ) 𝔓.iotaInf).toRingHom := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    show Algebra.TensorProduct.map (AlgHom.id κ κ) 𝔓.iotaInf (a ⊗ₜ b) =
      Algebra.TensorProduct.map (AlgHom.id (R p) κ) 𝔓.iotaInf (a ⊗ₜ b)
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy =>
    simp only [map_add]
    rw [show (Algebra.TensorProduct.map (AlgHom.id κ κ) 𝔓.iotaInf).toRingHom x =
        (Algebra.TensorProduct.map (AlgHom.id (R p) κ) 𝔓.iotaInf).toRingHom x from hx,
      show (Algebra.TensorProduct.map (AlgHom.id κ κ) 𝔓.iotaInf).toRingHom y =
        (Algebra.TensorProduct.map (AlgHom.id (R p) κ) 𝔓.iotaInf).toRingHom y from hy]

theorem comp_fibreMap_pi_eq_spec_map_kappa_comp
    (c' : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))) ⟶
      fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ))
    (hc'fst : c' ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom) ≫ ιInf p (ΓM M H) hj)
    (hc'snd : c' ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj)))))
    (c₀ : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj))) ⟶
      fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) κ))
    (hc₀fst : c₀ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓN p M H hpM) hj))).toRingHom) ≫ ιInf p (ΓN p M H hpM) hj)
    (hc₀snd : c₀ ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓN p M H hpM) hj))))) :
    c' ≫ fibreMap 𝔓.π (algebraMap (R p) κ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) 𝔓.iotaInf).toRingHom) ≫ c₀ := by
  rw [map_id_kappa_toRingHom_eq]
  exact comp_fibreMap_pi_eq_spec_map_comp 𝔓 κ c' hc'fst hc'snd c₀ hc₀fst hc₀snd

end Reshapes

section Point

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
  (𝔓 : XHDRModelAtP p M H hpM hj) (κ : Type) [Field κ] [Algebra (R p) κ]

theorem base_spec_map_eq_ker {A : Type} [CommRing A] (φ : A →+* κ) (x : ↥(Spec (CommRingCat.of κ))) :
    (Spec.map (CommRingCat.ofHom φ)).base x = ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ := by
  apply PrimeSpectrum.ext
  show Ideal.comap φ x.asIdeal = RingHom.ker φ
  have hx : x.asIdeal = ⊥ := by
    haveI : x.asIdeal.IsPrime := x.isPrime
    exact Ideal.eq_bot_of_prime (K := κ) x.asIdeal
  rw [hx]
  rfl

theorem ker_mem_range_sectionFibre_εinf
    (c' : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))) ⟶
      fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ))
    (hc'fst : c' ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom) ≫ ιInf p (ΓM M H) hj)
    (hc'snd : c' ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj)))))
    (ev : κ ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj) →ₐ[κ] κ)
    (hev : ∀ b : ↥(chartAlgInf p (ΓM M H) hj), ev ((1 : κ) ⊗ₜ[R p] b) = algebraMap (R p) κ (𝔓.rhoInf b)) :
    c'.base ⟨RingHom.ker ev.toRingHom, RingHom.ker_isPrime ev.toRingHom⟩ ∈
      Set.range (sectionFibre 𝔓.εinf (algebraMap (R p) κ)).base := by
  have h := base_spec_map_mem_range_sectionFibre_εinf 𝔓 κ c' hc'fst hc'snd ev hev (IsLocalRing.closedPoint κ)
  rwa [base_spec_map_eq_ker] at h

end Point

end DictGlue

end

namespace SmcPlace

section Value

variable {R : CommRingCat.{u}} [IsLocalRing R] {X Y : Scheme.{u}}

theorem stalkClosedPointTo_germ_appIso_inv (ι : Y ⟶ X) [IsOpenImmersion ι] (l : Spec R ⟶ Y)
    (w : Γ(Y, ⊤)) (h : (l ≫ ι).base (IsLocalRing.closedPoint R) ∈ ι ''ᵁ ⊤) :
    Scheme.stalkClosedPointTo (l ≫ ι) (X.presheaf.germ (ι ''ᵁ ⊤) _ h ((ι.appIso ⊤).inv w)) =
      Scheme.stalkClosedPointTo l (Y.presheaf.germ ⊤ _ trivial w) := by
  rw [Scheme.stalkClosedPointTo_comp]
  show Scheme.stalkClosedPointTo l (ι.stalkMap (l.base (IsLocalRing.closedPoint R))
    (X.presheaf.germ (ι ''ᵁ ⊤) (ι.base (l.base (IsLocalRing.closedPoint R))) h ((ι.appIso ⊤).inv w))) = _
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appIso_inv_app_apply, TopCat.Presheaf.germ_res_apply]

theorem stalkClosedPointTo_SpecMap_germ {A : CommRingCat.{u}} (φ : A ⟶ R) (b : A) :
    Scheme.stalkClosedPointTo (Spec.map φ) ((Spec A).presheaf.germ ⊤ _ trivial ((Scheme.ΓSpecIso A).inv b)) =
      φ b := by
  rw [← CommRingCat.comp_apply, Scheme.germ_stalkClosedPointTo_Spec, CommRingCat.comp_apply,
    Iso.inv_hom_id_apply]

theorem stalkClosedPointTo_congr {g g' : Spec R ⟶ X} (hg : g = g') (U : X.Opens)
    (h : g.base (IsLocalRing.closedPoint R) ∈ U) (h' : g'.base (IsLocalRing.closedPoint R) ∈ U) (s : Γ(X, U)) :
    Scheme.stalkClosedPointTo g (X.presheaf.germ U _ h s) = Scheme.stalkClosedPointTo g' (X.presheaf.germ U _ h' s) := by
  subst hg; rfl

theorem stalkClosedPointTo_germ_app (y : Spec R ⟶ Y) (f : Y ⟶ X) (U : X.Opens)
    (h : (y ≫ f).base (IsLocalRing.closedPoint R) ∈ U) :
    ∀ s : Γ(X, U), Scheme.stalkClosedPointTo y (Y.presheaf.germ (f ⁻¹ᵁ U) (y.base (IsLocalRing.closedPoint R)) h (f.app U s)) =
      Scheme.stalkClosedPointTo (y ≫ f) (X.presheaf.germ U _ h s) := by
  intro s
  rw [Scheme.stalkClosedPointTo_comp]
  show _ = Scheme.stalkClosedPointTo y (f.stalkMap (y.base (IsLocalRing.closedPoint R))
    (X.presheaf.germ U (f.base (y.base (IsLocalRing.closedPoint R))) h s))
  rw [Scheme.Hom.germ_stalkMap_apply]

end Value

theorem algebraMap_germ_eq_germToFunctionField {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) (x : X) (hx : x ∈ U)
    (s : Γ(X, U)) :
    haveI : Nonempty U := ⟨⟨x, hx⟩⟩
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx s) = X.germToFunctionField U s := by
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  show (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom (X.presheaf.germ U x hx s) = _
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]

theorem qExpand_jqModC_eq_pow (κ : Type*) [Field κ] (p : ℕ) [Fact p.Prime] [CharP κ p] :
    qExpand κ p (jqModC κ) = jqModC κ ^ p := by
  refine qExpand_eq_pow_of_coeff_fixed κ p _ fun k => ?_
  rw [← map_jqModC (Int.castRingHom κ), HahnSeries.map_coeff]
  rw [← frobenius_def, eq_intCast]
  exact map_intCast (frobenius κ p) _

theorem mem_qExpFrobeniusPlaceModL_of_isSSPlaceQExp (κ : Type*) [Field κ] (Γ : Subgroup SL(2, ℤ))
    (p : ℕ) [Fact p.Prime] [CharP κ p] (y : Place κ ↥(qExpFunctionFieldC κ Γ)) (hy : IsSSPlaceQExp κ Γ p y)
    (x : ↥(qExpFunctionFieldC κ Γ)) (hx : (x : LaurentSeries κ) = jqModC κ) :
    x ∈ (qExpFrobeniusPlaceModL κ Γ p y).toValuationSubring := by
  obtain ⟨x', a, hx', hval, -⟩ := hy
  have hxx : x' = x := Subtype.ext (hx'.trans hx.symm)
  subst hxx
  rw [mem_qExpFrobeniusPlaceModL_iff]
  have hfrob : qExpFrobeniusModL κ Γ p x' = x' ^ p := by
    apply Subtype.ext
    rw [coe_qExpFrobeniusModL, hx', SubmonoidClass.coe_pow, hx']
    exact qExpand_jqModC_eq_pow κ p
  rw [hfrob]
  exact pow_mem hval.mem p

section Fibre

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
  (𝔓 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
  (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

noncomputable def reading
    [Nonempty (Scheme.Opens.toScheme ((𝔓.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)))]
    (b : ↥(chartAlgInf p (ΓN p M H hpM) hj)) :
    ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) :=
  (𝔓.Mfib A hA ρ hρ).ffEquiv.symm
    ((𝔓.Mfib A hA ρ hρ).C.germToFunctionField
      ((𝔓.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
          (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤))
      (((𝔓.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
          (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
        (((ιInf p (ΓN p M H hpM) hj).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓN p M H hpM) hj))).inv b))))

theorem hasValue_pointEquivPlace_reading
    [Nonempty (Scheme.Opens.toScheme ((𝔓.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)))]
    (Q : {s : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥A)) ⟶ (𝔓.Mfib A hA ρ hρ).C // s ≫ (𝔓.Mfib A hA ρ hρ).toBase = 𝟙 _})
    (χ : ↥(chartAlgInf p (ΓN p M H hpM) hj) →+* IsLocalRing.ResidueField ↥A)
    (hQ : Q.1 ≫ 𝔓.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
        (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) =
      Spec.map (CommRingCat.ofHom χ) ≫ ιInf p (ΓN p M H hpM) hj)
    (b : ↥(chartAlgInf p (ΓN p M H hpM) hj)) :
    ((𝔓.Mfib A hA ρ hρ).pointEquivPlace Q).HasValue (reading 𝔓 A hA ρ hρ b) (χ b) := by
  set f := 𝔓.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
    (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) with hf
  set U : (X p (ΓN p M H hpM) hj).Opens := (ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤ with hU
  set sec : Γ(X p (ΓN p M H hpM) hj, U) :=
    ((ιInf p (ΓN p M H hpM) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓN p M H hpM) hj))).inv b)
    with hsec
  have hQf : Q.1 ≫ f = Spec.map (CommRingCat.ofHom χ) ≫ ιInf p (ΓN p M H hpM) hj := by rw [hf]; exact hQ
  have hmemU : (Q.1 ≫ f).base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A)) ∈ U := by
    rw [hQf]
    exact ⟨(Spec.map (CommRingCat.ofHom χ)).base (IsLocalRing.closedPoint _), trivial, rfl⟩
  have hmemU' : (Spec.map (CommRingCat.ofHom χ) ≫ ιInf p (ΓN p M H hpM) hj).base
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A)) ∈ U := hQf ▸ hmemU
  set s := (𝔓.Mfib A hA ρ hρ).C.presheaf.germ (f ⁻¹ᵁ U) (Q.1.base (IsLocalRing.closedPoint _)) hmemU (f.app U sec) with hs
  obtain ⟨hmem, hres, -⟩ :=
    AlgebraicCurve.CurveModel.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo (𝔓.Mfib A hA ρ hρ) Q s
  have helt : (𝔓.Mfib A hA ρ hρ).ffEquiv.symm (algebraMap _ (𝔓.Mfib A hA ρ hρ).C.functionField s) =
      reading 𝔓 A hA ρ hρ b := by
    rw [reading, hs, algebraMap_germ_eq_germToFunctionField]
  have hval : (Scheme.stalkClosedPointTo Q.1).hom s = χ b := by
    show Scheme.stalkClosedPointTo Q.1 s = χ b
    rw [hs, stalkClosedPointTo_germ_app Q.1 f U hmemU sec, stalkClosedPointTo_congr hQf U hmemU hmemU' sec, hsec,
      stalkClosedPointTo_germ_appIso_inv, stalkClosedPointTo_SpecMap_germ]
    rfl
  have H' : ∃ h : (𝔓.Mfib A hA ρ hρ).ffEquiv.symm (algebraMap _ (𝔓.Mfib A hA ρ hρ).C.functionField s) ∈
      ((𝔓.Mfib A hA ρ hρ).pointEquivPlace Q).toValuationSubring,
      IsLocalRing.residue ((𝔓.Mfib A hA ρ hρ).pointEquivPlace Q).toValuationSubring ⟨_, h⟩ =
        algebraMap (IsLocalRing.ResidueField ↥A) ((𝔓.Mfib A hA ρ hρ).pointEquivPlace Q).ResidueField (χ b) :=
    ⟨hmem, by rw [hres, hval]⟩
  rw [helt] at H'
  exact H'

end Fibre

section Cusp

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
  (𝔓 : XHDRModelAtP p M H hpM hj)

theorem jqModC_rat_ne_zero : jqModC ℚ ≠ 0 := by
  intro h
  have := congrArg (fun s : LaurentSeries ℚ => s.coeff (-1)) h
  simp only [coeff_jqModC_neg_one, HahnSeries.coeff_zero] at this
  exact one_ne_zero this

theorem coeff_zero_inv_jqModC : ((jqModC ℚ)⁻¹).coeff 0 = 0 := by
  have hu : jNumQ * jNumQ.invOfUnit 1 = 1 := PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_jNumQ]; rfl)
  have hj : jqModC ℚ = HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℚ jNumQ := rfl
  have hinv : (jqModC ℚ)⁻¹ = HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.X * jNumQ.invOfUnit 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [hj, map_mul, HahnSeries.ofPowerSeries_X, mul_mul_mul_comm, HahnSeries.single_mul_single, neg_add_cancel, one_mul,
      ← map_mul, hu, map_one (HahnSeries.ofPowerSeries ℤ ℚ), mul_one]
    rfl
  rw [hinv, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_zero_X_mul]

theorem coeffMap_jqModC' {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T) : coeffMap f (jqModC S) = jqModC T :=
  map_jqModC f

theorem coeffMap_R_injective : Function.Injective (coeffMap (algebraMap (R p) ℚ)) := by
  intro a c h
  ext k
  have := congrArg (fun s : LaurentSeries ℚ => s.coeff k) h
  simp only [coeffMap_coeff] at this
  exact_mod_cast this

theorem iotaInf_jInvChartInf :
    𝔓.iotaInf (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)) =
      TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) := by
  apply Subtype.ext; apply Subtype.ext
  rw [𝔓.iotaInf_spec, TwoChartIntegralModel.coe_jInvChartInf, TwoChartIntegralModel.coe_jInvChartInf]
  simp [jAt]

theorem rhoInf_jInvChartInf :
    𝔓.rhoInf (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)) = 0 := by
  apply Subtype.ext
  rw [𝔓.rhoInf_spec, TwoChartIntegralModel.coe_jInvChartInf]
  show ((((jAt (ΓM M H) hj)⁻¹ : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)).coeff 0 = ((0 : R p) : ℚ)
  have : (((jAt (ΓM M H) hj)⁻¹ : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = (jqModC ℚ)⁻¹ := by
    rw [← coe_jAt (ΓM M H) hj]; rfl
  rw [this, coeff_zero_inv_jqModC]
  rfl

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
  (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

theorem hasValue_inv_zero_and_not_mem_pointEquivPlace_cusp
    [Nonempty (Scheme.Opens.toScheme ((𝔓.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)))]
    (hpinInf : ∀ (b : ↥(chartAlgInf p (ΓN p M H hpM) hj)) (y : LaurentSeries (R p)),
      coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) →
        ((reading 𝔓 A hA ρ hρ b : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) :
          LaurentSeries (IsLocalRing.ResidueField ↥A)) = coeffMap ((IsLocalRing.residue ↥A).comp ρ) y)
    (Q : {s : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥A)) ⟶ (𝔓.Mfib A hA ρ hρ).C // s ≫ (𝔓.Mfib A hA ρ hρ).toBase = 𝟙 _})
    (hQ : Q.1 ≫ 𝔓.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
        (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) =
      Spec.map (CommRingCat.ofHom ((((IsLocalRing.residue ↥A).comp ρ).comp 𝔓.rhoInf.toRingHom).comp 𝔓.iotaInf.toRingHom)) ≫
        ιInf p (ΓN p M H hpM) hj)
    (x : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))
    (hx : (x : LaurentSeries (IsLocalRing.ResidueField ↥A)) = jqModC (IsLocalRing.ResidueField ↥A)) :
    ((𝔓.Mfib A hA ρ hρ).pointEquivPlace Q).HasValue x⁻¹ 0 ∧
      x ∉ ((𝔓.Mfib A hA ρ hρ).pointEquivPlace Q).toValuationSubring := by
  set jN := TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) with hjN

  have hval0 := hasValue_pointEquivPlace_reading 𝔓 A hA ρ hρ Q _ hQ jN
  have hzero : ((((IsLocalRing.residue ↥A).comp ρ).comp 𝔓.rhoInf.toRingHom).comp 𝔓.iotaInf.toRingHom) jN = 0 := by
    show ((IsLocalRing.residue ↥A).comp ρ) (𝔓.rhoInf (𝔓.iotaInf jN)) = 0
    rw [hjN, iotaInf_jInvChartInf, rhoInf_jInvChartInf, map_zero]
  rw [hzero] at hval0

  obtain ⟨y, hy⟩ := (ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
    (ΓN p M H hpM) p (jAt (ΓN p M H hpM) hj) (coe_jAt (ΓN p M H hpM) hj)).2 jN
  have hyj : y * jqModC (R p) = 1 := by
    apply coeffMap_R_injective
    rw [map_mul, map_one, hy, hjN, TwoChartIntegralModel.coe_jInvChartInf, coeffMap_jqModC']
    have : (((jAt (ΓN p M H hpM) hj)⁻¹ : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) = (jqModC ℚ)⁻¹ := by
      rw [← coe_jAt (ΓN p M H hpM) hj]; rfl
    rw [this]
    exact inv_mul_cancel₀ jqModC_rat_ne_zero
  have h1 : coeffMap ((IsLocalRing.residue ↥A).comp ρ) y * jqModC (IsLocalRing.ResidueField ↥A) = 1 := by
    have := congrArg (coeffMap ((IsLocalRing.residue ↥A).comp ρ)) hyj
    rwa [map_mul, map_one, coeffMap_jqModC'] at this
  have hx0 : (x : LaurentSeries (IsLocalRing.ResidueField ↥A)) ≠ 0 := by
    intro h0
    rw [← hx, h0, mul_zero] at h1
    exact zero_ne_one h1
  have hread : reading 𝔓 A hA ρ hρ jN = x⁻¹ := by
    apply Subtype.ext
    rw [hpinInf jN y hy]
    show _ = ((x : LaurentSeries (IsLocalRing.ResidueField ↥A)))⁻¹
    rw [hx]
    exact eq_inv_of_mul_eq_one_left h1
  rw [hread] at hval0
  refine ⟨hval0, fun hxmem => ?_⟩
  obtain ⟨hinvmem, hres⟩ := hval0
  rw [map_zero, IsLocalRing.residue_eq_zero_iff] at hres
  have hx0' : x ≠ 0 := fun h => hx0 (by rw [h]; rfl)
  have hone : (⟨x, hxmem⟩ : ((𝔓.Mfib A hA ρ hρ).pointEquivPlace Q).toValuationSubring) * ⟨x⁻¹, hinvmem⟩ = 1 :=
    Subtype.ext (mul_inv_cancel₀ hx0')
  apply (IsLocalRing.maximalIdeal.isMaximal ((𝔓.Mfib A hA ρ hρ).pointEquivPlace Q).toValuationSubring).ne_top
  rw [Ideal.eq_top_iff_one, ← hone]
  exact Ideal.mul_mem_left _ _ hres

end Cusp

section Export

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
  (𝔓 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
  (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

theorem exists_coe_eq_jqModC
    [Nonempty (Scheme.Opens.toScheme ((𝔓.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)))]
    (hpinInf : ∀ (b : ↥(chartAlgInf p (ΓN p M H hpM) hj)) (y : LaurentSeries (R p)),
      coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) →
        ((reading 𝔓 A hA ρ hρ b : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) :
          LaurentSeries (IsLocalRing.ResidueField ↥A)) = coeffMap ((IsLocalRing.residue ↥A).comp ρ) y) :
    ∃ x : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)),
      (x : LaurentSeries (IsLocalRing.ResidueField ↥A)) = jqModC (IsLocalRing.ResidueField ↥A) := by
  set jN := TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) with hjN
  obtain ⟨y, hy⟩ := (ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
    (ΓN p M H hpM) p (jAt (ΓN p M H hpM) hj) (coe_jAt (ΓN p M H hpM) hj)).2 jN
  have hyj : y * jqModC (R p) = 1 := by
    apply coeffMap_R_injective
    rw [map_mul, map_one, hy, hjN, TwoChartIntegralModel.coe_jInvChartInf, coeffMap_jqModC']
    have : (((jAt (ΓN p M H hpM) hj)⁻¹ : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) = (jqModC ℚ)⁻¹ := by
      rw [← coe_jAt (ΓN p M H hpM) hj]; rfl
    rw [this]
    exact inv_mul_cancel₀ jqModC_rat_ne_zero
  have h1 : coeffMap ((IsLocalRing.residue ↥A).comp ρ) y * jqModC (IsLocalRing.ResidueField ↥A) = 1 := by
    have := congrArg (coeffMap ((IsLocalRing.residue ↥A).comp ρ)) hyj
    rwa [map_mul, map_one, coeffMap_jqModC'] at this
  refine ⟨(reading 𝔓 A hA ρ hρ jN)⁻¹, ?_⟩
  show ((reading 𝔓 A hA ρ hρ jN : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) :
      LaurentSeries (IsLocalRing.ResidueField ↥A))⁻¹ = _
  rw [hpinInf jN y hy]
  exact inv_eq_of_mul_eq_one_right h1

end Export

end SmcPlace

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "Place TwoChartIntegralModel.jInvChartInf TwoChartIntegralModel.coe_jInvChartInf TwoChartIntegralModel TwoChartIntegralModel.ιInf_toBase CurveModel CurveModel.pointEquivPlace_apply CurveModel.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo" namespace CurveModel p2m_export "AlgebraicCurve.CurveModel" "pointEquivPlace pointEquivPlace_apply placeOfPoint toBase C ffEquiv ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo" end AlgebraicCurve.CurveModel
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.CurveModel" in

theorem AlgebraicCurve.CurveModel.pointEquivPlace_eq_placeOfPoint {K : Type*} [Field K] [IsAlgClosed K]
    {L : Type*} [Field L] [Algebra K L] (M : CurveModel K L)
    (Q : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) (x : closedPoints M.C)
    (hx : Q.1.base (IsLocalRing.closedPoint K) = x.1) :
    M.pointEquivPlace Q = M.placeOfPoint x := by
  rw [CurveModel.pointEquivPlace_apply]
  congr 1
  exact Subtype.ext hx

set_option maxHeartbeats 12800000 in
theorem solution
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (𝔓 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) (IsLocalRing.ResidueField ↥A)]
    (halg : algebraMap (R p) (IsLocalRing.ResidueField ↥A) = (IsLocalRing.residue ↥A).comp ρ)
    (ev : (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj) →ₐ[IsLocalRing.ResidueField ↥A]
      IsLocalRing.ResidueField ↥A)
    (hev : ∀ b : ↥(chartAlgInf p (ΓM M H) hj),
      ev (1 ⊗ₜ b) = algebraMap (R p) (IsLocalRing.ResidueField ↥A) (𝔓.rhoInf b)) :
    ∀ (P P' : Ideal ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))),
      P ∈ minimalPrimes ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj)) →
      P' ∈ minimalPrimes ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj)) →
      P ≤ RingHom.ker ev → P' ≤ RingHom.ker ev → P = P' := by
  classical

  obtain rfl : ‹Algebra (R p) (IsLocalRing.ResidueField ↥A)› = ((IsLocalRing.residue ↥A).comp ρ).toAlgebra :=
    Algebra.algebra_ext _ _ (fun r => by
      rw [RingHom.algebraMap_toAlgebra]
      exact congrArg (fun φ : R p →+* (IsLocalRing.ResidueField ↥A) => φ r) halg)
  letI instκ : Algebra (R p) (IsLocalRing.ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
  intro P P' hP hP' hPle hP'le

  obtain ⟨c', hc'open, hc'fst, hc'snd, hc'range⟩ := DictGlue.chartInf_baseChange p (ΓM M H) hj (IsLocalRing.ResidueField ↥A)
  obtain ⟨c₀, hc₀open, hc₀fst, hc₀snd, hc₀range⟩ := DictGlue.chartInf_baseChange p (ΓN p M H hpM) hj (IsLocalRing.ResidueField ↥A)
  have L3 : c' ≫ fibreMap 𝔓.π (algebraMap (R p) (IsLocalRing.ResidueField ↥A)) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) 𝔓.iotaInf).toRingHom) ≫ c₀ :=
    DictGlue.comp_fibreMap_pi_eq_spec_map_kappa_comp 𝔓 (IsLocalRing.ResidueField ↥A) c' hc'fst hc'snd c₀ hc₀fst hc₀snd
  have L4 : c'.base ⟨RingHom.ker ev.toRingHom, RingHom.ker_isPrime ev.toRingHom⟩ ∈ Set.range (𝔓.comp A hA ρ hρ 0).base :=
    𝔓.εinf_mem_comp0 A hA ρ hρ (DictGlue.ker_mem_range_sectionFibre_εinf 𝔓 (IsLocalRing.ResidueField ↥A) c' hc'fst hc'snd ev hev)

  obtain ⟨σ₀, hσret, hσc⟩ := ModularCurve.XHDRLevel.exists_retraction_chartInf_comp_zero_eq_of_dvd p M H hpM hj
    𝔓.π 𝔓.iotaInf 𝔓.iotaInf_spec 𝔓.pi_chartInf (IsLocalRing.ResidueField ↥A) c₀ hc₀fst hc₀snd c' hc'fst hc'snd
    (𝔓.comp A hA ρ hρ) (𝔓.comp_over A hA ρ hρ) (𝔓.comp_isClosedImmersion A hA ρ hρ) (𝔓.comp_pi A hA ρ hρ)
  have hσsurj : Function.Surjective σ₀ := fun w => ⟨_, hσret w⟩
  have key : ∀ w : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))),
      c'.base w ∈ Set.range (𝔓.comp A hA ρ hρ 0).base → RingHom.ker σ₀.toRingHom ≤ w.asIdeal := by
    intro w
    rintro ⟨v, hv⟩

    have hv' : (fibreMap 𝔓.π (algebraMap (R p) (IsLocalRing.ResidueField ↥A))).base (c'.base w) = v := by
      rw [← hv]
      change ((𝔓.comp A hA ρ hρ 0) ≫ fibreMap 𝔓.π ((IsLocalRing.residue ↥A).comp ρ)).base v = v
      rw [𝔓.comp_pi A hA ρ hρ]
      rfl

    have hw₀ : (fibreMap 𝔓.π (algebraMap (R p) (IsLocalRing.ResidueField ↥A))).base (c'.base w) =
        c₀.base ((Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) 𝔓.iotaInf).toRingHom)).base w) := by
      change (c' ≫ fibreMap 𝔓.π (algebraMap (R p) (IsLocalRing.ResidueField ↥A))).base w = _
      rw [L3]
      rfl

    have e1 : c'.base w = c'.base ((Spec.map (CommRingCat.ofHom σ₀.toRingHom)).base
        ((Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) 𝔓.iotaInf).toRingHom)).base w)) := by
      rw [← hv, ← hv', hw₀]
      change (c₀ ≫ 𝔓.comp A hA ρ hρ 0).base _ = (Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c').base _
      rw [hσc]
    have e2 := hc'open.base_open.injective e1
    rw [e2]
    intro t ht
    rw [RingHom.mem_ker] at ht
    change t ∈ Ideal.comap σ₀.toRingHom _
    rw [Ideal.mem_comap, ht]
    exact Ideal.zero_mem _

  let evN : (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj) →ₐ[(IsLocalRing.ResidueField ↥A)] (IsLocalRing.ResidueField ↥A) :=
    Algebra.TensorProduct.lift (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) ((Algebra.ofId (R p) (IsLocalRing.ResidueField ↥A)).comp (𝔓.rhoInf.comp 𝔓.iotaInf))
      (fun _ _ => Commute.all _ _)
  have hevN : ∀ (a : (IsLocalRing.ResidueField ↥A)) (b : ↥(chartAlgInf p (ΓN p M H hpM) hj)), evN (a ⊗ₜ b) = a * algebraMap (R p) (IsLocalRing.ResidueField ↥A) (𝔓.rhoInf (𝔓.iotaInf b)) := by
    intro a b
    simp only [evN, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, AlgHom.comp_apply, Algebra.ofId_apply]
  haveI hntN : Nontrivial ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj)) := evN.toRingHom.domain_nontrivial
  haveI := 𝔓.efib_iso A hA ρ hρ
  haveI hneFN : Nonempty (fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) (IsLocalRing.ResidueField ↥A))) := ⟨(𝔓.efib A hA ρ hρ).base (Classical.arbitrary _)⟩
  haveI hintFN : IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) (IsLocalRing.ResidueField ↥A))) := isIntegral_of_isOpenImmersion (inv (𝔓.efib A hA ρ hρ))
  haveI hintSN : IsIntegral (Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj)))) := isIntegral_of_isOpenImmersion c₀
  haveI hdomN : IsDomain ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj)) :=
    MulEquiv.isDomain Γ(Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj))), ⊤)
      (Scheme.ΓSpecIso (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj)))).symm.commRingCatIsoToRingEquiv.toMulEquiv
  have hkerprime : (RingHom.ker σ₀.toRingHom).IsPrime := RingHom.ker_isPrime σ₀.toRingHom

  suffices hcore : ∀ Q : Ideal ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj)), Q ∈ minimalPrimes ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj)) →
      Q ≤ RingHom.ker ev → Q = RingHom.ker σ₀.toRingHom by
    rw [hcore P hP hPle, hcore P' hP' hP'le]
  intro Q hQ hQle
  let q : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))) := ⟨Q, hQ.1.1⟩
  rcases 𝔓.comp_jointly_surjective A hA ρ hρ (c'.base q) with h0 | h1
  · exact le_antisymm (hQ.2 ⟨hkerprime, bot_le⟩ (key q h0)) (key q h0)
  · exfalso

    let kev : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))) := ⟨RingHom.ker ev.toRingHom, RingHom.ker_isPrime ev.toRingHom⟩
    have hqk : q ⤳ kev := (PrimeSpectrum.le_iff_specializes q kev).mp hQle
    have hk1 : c'.base kev ∈ Set.range (𝔓.comp A hA ρ hρ 1).base :=
      (hqk.map c'.continuous).mem_closed (𝔓.comp_isClosedImmersion A hA ρ hρ 1).base_closed.isClosed_range h1

    let ptN : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj))) := ⟨RingHom.ker evN.toRingHom, RingHom.ker_isPrime evN.toRingHom⟩
    have hevext : ev.comp (Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) 𝔓.iotaInf) = evN := by
      apply Algebra.TensorProduct.ext'
      intro a b
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hevN]
      rw [show a ⊗ₜ[R p] 𝔓.iotaInf b = a • ((1 : (IsLocalRing.ResidueField ↥A)) ⊗ₜ[R p] 𝔓.iotaInf b) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, hev, smul_eq_mul]
    have hpt : (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) 𝔓.iotaInf).toRingHom)).base kev = ptN := by
      apply PrimeSpectrum.ext
      change Ideal.comap (Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) 𝔓.iotaInf).toRingHom (RingHom.ker ev.toRingHom) =
        RingHom.ker evN.toRingHom
      rw [← hevext]
      ext t
      simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.comp_apply]
    obtain ⟨v, hv⟩ := L4
    have hv' : (fibreMap 𝔓.π (algebraMap (R p) (IsLocalRing.ResidueField ↥A))).base (c'.base kev) = v := by
      rw [← hv]
      change ((𝔓.comp A hA ρ hρ 0) ≫ fibreMap 𝔓.π ((IsLocalRing.residue ↥A).comp ρ)).base v = v
      rw [𝔓.comp_pi A hA ρ hρ]
      rfl
    have hvx : v = c₀.base ptN := by
      rw [← hv', ← hpt]
      change (c' ≫ fibreMap 𝔓.π (algebraMap (R p) (IsLocalRing.ResidueField ↥A))).base kev = _
      rw [L3]
      rfl

    obtain ⟨y1, hy1⟩ := hk1
    obtain ⟨n, hn1, -⟩ := Scheme.Pullback.exists_preimage_pullback (c₀.base ptN) y1 (by rw [← hvx, hv, hy1])
    obtain ⟨-, ⟨hcl, hplace⟩⟩ := 𝔓.node_pin A hA ρ hρ n

    have hevN_left : evN.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := (IsLocalRing.ResidueField ↥A)) (B := ↥(chartAlgInf p (ΓN p M H hpM) hj))) = RingHom.id _ := by
      ext a
      simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, hevN, map_one, mul_one, RingHom.id_apply]
    have hevN_right : evN.toRingHom.comp (Algebra.TensorProduct.includeRight
        (R := R p) (A := (IsLocalRing.ResidueField ↥A)) (B := ↥(chartAlgInf p (ΓN p M H hpM) hj))).toRingHom =
        (((IsLocalRing.residue ↥A).comp ρ).comp 𝔓.rhoInf.toRingHom).comp 𝔓.iotaInf.toRingHom := by
      ext b
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Algebra.TensorProduct.includeRight_apply, hevN, one_mul]
      rfl
    let Q₀ : {s : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥A)) ⟶ (𝔓.Mfib A hA ρ hρ).C // s ≫ (𝔓.Mfib A hA ρ hρ).toBase = 𝟙 _} :=
      ⟨Spec.map (CommRingCat.ofHom evN.toRingHom) ≫ c₀ ≫ inv (𝔓.efib A hA ρ hρ), by
        rw [Category.assoc, Category.assoc, ← 𝔓.hefib A hA ρ hρ, IsIso.inv_hom_id_assoc]
        change Spec.map (CommRingCat.ofHom evN.toRingHom) ≫ c₀ ≫ pullback.snd _ _ = 𝟙 _
        rw [hc₀snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hevN_left, CommRingCat.ofHom_id, Spec.map_id]⟩
    have hQ₀ : Q₀.1 ≫ 𝔓.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
        (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) =
        Spec.map (CommRingCat.ofHom ((((IsLocalRing.residue ↥A).comp ρ).comp 𝔓.rhoInf.toRingHom).comp 𝔓.iotaInf.toRingHom)) ≫
          ιInf p (ΓN p M H hpM) hj := by
      change (Spec.map (CommRingCat.ofHom evN.toRingHom) ≫ c₀ ≫ inv (𝔓.efib A hA ρ hρ)) ≫ 𝔓.efib A hA ρ hρ ≫ pullback.fst _ _ = _
      rw [Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc]
      change Spec.map (CommRingCat.ofHom evN.toRingHom) ≫ c₀ ≫ pullback.fst _ _ = _
      rw [hc₀fst, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hevN_right]

    have hbase : Q₀.1.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A)) =
        (inv (𝔓.efib A hA ρ hρ)).base ((pullback.fst (𝔓.comp A hA ρ hρ 0) (𝔓.comp A hA ρ hρ 1)).base n) := by
      rw [hn1]
      change (inv (𝔓.efib A hA ρ hρ)).base (c₀.base ((Spec.map (CommRingCat.ofHom evN.toRingHom)).base _)) = _
      rw [DictGlue.base_spec_map_eq_ker]
    have hplace' : (𝔓.Mfib A hA ρ hρ).pointEquivPlace Q₀ =
        qExpFrobeniusPlaceModL (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p
          ((𝔓.nodeEquiv A hA ρ hρ n : ↥(ssPlacesQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p)) : Place (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) := by
      rw [AlgebraicCurve.CurveModel.pointEquivPlace_eq_placeOfPoint _ Q₀ ⟨_, hcl⟩ hbase]
      exact hplace

    obtain ⟨hneI, hpin⟩ := ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffMap_of_mfib
      p M H hpM hj 𝔓 A hA ρ hρ (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj))
    haveI := hneI
    have hpinInf : ∀ (b : ↥(chartAlgInf p (ΓN p M H hpM) hj)) (y : LaurentSeries (R p)),
        coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) →
        ((SmcPlace.reading 𝔓 A hA ρ hρ b : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) = coeffMap ((IsLocalRing.residue ↥A).comp ρ) y := by
      intro b y hy
      obtain ⟨_, h⟩ := ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffMap_of_mfib
        p M H hpM hj 𝔓 A hA ρ hρ b
      exact h y hy
    obtain ⟨x, hx⟩ := SmcPlace.exists_coe_eq_jqModC 𝔓 A hA ρ hρ hpinInf
    have hpole := (SmcPlace.hasValue_inv_zero_and_not_mem_pointEquivPlace_cusp 𝔓 A hA ρ hρ hpinInf Q₀ hQ₀ x hx).2
    have hreg := SmcPlace.mem_qExpFrobeniusPlaceModL_of_isSSPlaceQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p _
      (𝔓.nodeEquiv A hA ρ hρ n).2 x hx
    rw [hplace'] at hpole
    exact hpole hreg

#print axioms solution

end S_ModularCurve_XHDRModelAtP_subsingleton_minimalPrimes_le_ker_cusp
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_subsingleton_minimalPrimes_le_ker_cusp (solution)
