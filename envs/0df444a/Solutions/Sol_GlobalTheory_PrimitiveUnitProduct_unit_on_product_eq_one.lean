-- Prove2me | solution 1 for GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:32:31.206144+00:00
-- url     : https://prove2.me/submissions/b9c4a5ab-fb93-43e7-b592-b4cd762dd9c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
import Theorems.Thm_GlobalTheory_PrimitiveUnitProduct_unit_eq_one
import Theorems.Thm_GlobalTheory_PrimitiveUnitProduct_appTop_comp_apply
import Theorems.Thm_GlobalTheory_PrimitiveUnitProduct_specMap_appTop_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct CategoryTheory AlgebraicGeometry Limits
open GlobalTheory GlobalTheory.PrimitiveUnitProduct
namespace GlobalTheory.PrimitiveUnitProduct
theorem _root_.solution {K : Type} [Field K] [IsAlgClosed K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) [GeometricallyIntegral f]
    (e : Spec (CommRingCat.of K) ⟶ X) (he : e ≫ f = 𝟙 _) (a₁ a₂ : X ⟶ pullback f f)
    (h₁₁ : a₁ ≫ pullback.fst f f = 𝟙 X) (h₁₂ : a₁ ≫ pullback.snd f f = f ≫ e)
    (h₂₁ : a₂ ≫ pullback.fst f f = f ≫ e) (h₂₂ : a₂ ≫ pullback.snd f f = 𝟙 X)
    (u : Γ(pullback f f, ⊤)) (hu : IsUnit u) (hu₁ : a₁.appTop.hom u = 1)
    (hu₂ : a₂.appTop.hom u = 1) : u = 1 := by
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  have : IsReduced (pullback f f) := by
    have : Finite (irreducibleComponents X) := by
      rw [irreducibleComponents_eq_singleton]; infer_instance
    exact GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents (pullback.fst f f)
  have : IsIntegral (pullback f f) := isIntegral_of_irreducibleSpace_of_isReduced _
  obtain ⟨A, g, hg, hge⟩ : ∃ (A : CommRingCat) (g : Spec A ⟶ X), IsOpenImmersion g ∧
      Set.range e ⊆ Set.range g := by
    let x := e (IsLocalRing.closedPoint K)
    refine ⟨_, X.affineOpenCover.f (X.affineOpenCover.idx x), inferInstance, ?_⟩
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y (IsLocalRing.closedPoint K)]
    exact X.affineOpenCover.covers x
  obtain ⟨α, hα⟩ := Spec.map_surjective (g ≫ f)
  obtain ⟨ε₀, hε₀⟩ := Spec.map_surjective (IsOpenImmersion.lift g e hge)
  have hε : Spec.map ε₀ ≫ g = e := by rw [hε₀, IsOpenImmersion.lift_fac]
  have hαε : α ≫ ε₀ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, reassoc_of% hε, he, Spec.map_id]
  let _ : Algebra K A := α.hom.toAlgebra
  have hα' : Spec.map (CommRingCat.ofHom (algebraMap K A)) = g ≫ f := hα
  let ε : A →ₐ[K] K := { ε₀.hom with commutes' := fun k => congrArg (fun t => t.hom k) hαε }
  have hA : Nontrivial A := ε₀.hom.domain_nontrivial
  have : Nonempty (Spec A) := inferInstanceAs (Nonempty (PrimeSpectrum A))
  have : IsIntegral (Spec A) := isIntegral_of_isOpenImmersion g
  have : IsDomain A := (affine_isIntegral_iff A).mp inferInstance
  have H : ∀ (L : Type) [Field L] [Algebra K L], IsDomain (L ⊗[K] A) := by
    intro L _ _
    let y := Spec.map (CommRingCat.ofHom (algebraMap K L))
    have : IsIntegral (pullback y f) :=
      pullback_of_geometrically' GeometricallyIntegral.geometrically_isIntegral L y
    let i : Spec (.of (L ⊗[K] A)) ⟶ pullback y f := (pullbackSpecIso K L A).inv ≫
      pullback.map _ _ _ _ (𝟙 _) g (𝟙 _) (by simp [y]) (by simp [hα'])
    have : Nonempty (Spec (.of (L ⊗[K] A))) := inferInstanceAs (Nonempty (PrimeSpectrum _))
    have : IsIntegral (Spec (.of (L ⊗[K] A))) := isIntegral_of_isOpenImmersion i
    exact (affine_isIntegral_iff (.of (L ⊗[K] A))).mp inferInstance
  let i : Spec (.of (A ⊗[K] A)) ⟶ pullback f f := (pullbackSpecIso K A A).inv ≫
    pullback.map _ _ _ _ g g (𝟙 _) (by simp [hα']) (by simp [hα'])
  have hi₁ : i ≫ pullback.fst f f =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ g := by
    simp only [i, Category.assoc, pullback.lift_fst, pullbackSpecIso_inv_fst_assoc]
  have hi₂ : i ≫ pullback.snd f f =
      Spec.map (CommRingCat.ofHom
        (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := A)))) ≫ g := by
    simp only [i, Category.assoc, pullback.lift_snd, pullbackSpecIso_inv_snd_assoc]
  let p₁ : A ⊗[K] A →ₐ[K] A := Algebra.TensorProduct.lift (AlgHom.id K A)
    ((Algebra.ofId K A).comp ε) (fun _ _ => Commute.all _ _)
  let p₂ : A ⊗[K] A →ₐ[K] A := Algebra.TensorProduct.lift ((Algebra.ofId K A).comp ε)
    (AlgHom.id K A) (fun _ _ => Commute.all _ _)
  have hgfe : g ≫ f ≫ e = Spec.map (ε₀ ≫ α) ≫ g := by
    rw [Spec.map_comp, Category.assoc, hε, hα, Category.assoc]
  have c₁ : Spec.map (CommRingCat.ofHom p₁.toRingHom) ≫ i = g ≫ a₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hi₁, Category.assoc, h₁₁, ← Spec.map_comp_assoc, Category.comp_id]
      conv_rhs => rw [← Category.id_comp g, ← Spec.map_id]
      congr 2
      ext a
      simp [p₁]
    · rw [Category.assoc, hi₂, Category.assoc, h₁₂, ← Spec.map_comp_assoc, hgfe]
      congr 2
      ext a
      simp [p₁]
      rfl
  have c₂ : Spec.map (CommRingCat.ofHom p₂.toRingHom) ≫ i = g ≫ a₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hi₁, Category.assoc, h₂₁, ← Spec.map_comp_assoc, hgfe]
      congr 2
      ext a
      simp [p₂]
      rfl
    · rw [Category.assoc, hi₂, Category.assoc, h₂₂, ← Spec.map_comp_assoc, Category.comp_id]
      conv_rhs => rw [← Category.id_comp g, ← Spec.map_id]
      congr 2
      ext a
      change p₂ (1 ⊗ₜ a) = a
      simp [p₂]
  let u' : A ⊗[K] A := (Scheme.ΓSpecIso (.of (A ⊗[K] A))).hom (i.appTop u)
  have hu' : u' = 1 := by
    refine unit_eq_one H ε u' ((hu.map _).map _) p₁.toRingHom p₂.toRingHom
      (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_
    · have := specMap_appTop_apply (CommRingCat.ofHom p₁.toRingHom) (i.appTop u)
      rw [← appTop_comp_apply, c₁, appTop_comp_apply, hu₁, map_one, map_one] at this
      exact this.symm
    · have := specMap_appTop_apply (CommRingCat.ofHom p₂.toRingHom) (i.appTop u)
      rw [← appTop_comp_apply, c₂, appTop_comp_apply, hu₂, map_one, map_one] at this
      exact this.symm
  have h1 : i.appTop u = 1 := by
    apply (Scheme.ΓSpecIso (.of (A ⊗[K] A))).commRingCatIsoToRingEquiv.injective
    rw [map_one]
    exact hu'
  have : Nonempty (Spec (.of (A ⊗[K] A))) := inferInstanceAs (Nonempty (PrimeSpectrum _))
  have : IsOpenImmersion i := inferInstance
  have hd : Dense (Set.range i) := i.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  by_contra hne
  obtain ⟨x, hx, y, rfl⟩ := hd.inter_open_nonempty _ ((pullback f f).basicOpen (u - 1)).isOpen
    (TopologicalSpace.Opens.ne_bot_iff_nonempty _ |>.mp hne)
  have hy : y ∈ i ⁻¹ᵁ (pullback f f).basicOpen (u - 1) := hx
  rw [Scheme.preimage_basicOpen_top, map_sub, h1, map_one, sub_self, Scheme.basicOpen_zero] at hy
  exact hy
end GlobalTheory.PrimitiveUnitProduct
