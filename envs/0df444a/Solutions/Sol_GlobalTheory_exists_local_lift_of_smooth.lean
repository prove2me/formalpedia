-- Prove2me | solution 1 for GlobalTheory.exists_local_lift_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:44:54.436259+00:00
-- url     : https://prove2.me/submissions/94cc3d65-11c2-4976-a71f-bc498c45f09a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Theorems.Thm_GlobalTheory_surjective_of_isNilpotent_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory
theorem _root_.solution {X S T₀ T : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (i : T₀ ⟶ T) [IsClosedImmersion i] (hi : IsNilpotent i.ker)
    (g : T₀ ⟶ X) (h : T ⟶ S) (w : g ≫ f = i ≫ h) (t : T) :
    ∃ (W : T.Opens) (_ : t ∈ W) (l : W.toScheme ⟶ X), l ≫ f = W.ι ≫ h ∧
      (i ∣_ W) ≫ l = (i ⁻¹ᵁ W).ι ≫ g := by
  obtain ⟨t, rfl⟩ := (surjective_of_isNilpotent_ker i hi).surj t
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (g t))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ f ⁻¹ᵁ U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).isOpen
  obtain ⟨O, hO, hO'⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp (g ⁻¹ᵁ V).isOpen
  have htO : i t ∈ O := by
    have : t ∈ i ⁻¹' O := hO' ▸ hxV
    exact this
  have hth : h (i t) ∈ U := by
    rw [← Scheme.Hom.comp_apply, ← w, Scheme.Hom.comp_apply]; exact hxU
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWO⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
    (show i t ∈ O ∩ (h ⁻¹ᵁ U : Set T) from ⟨htO, hth⟩) (hO.inter (h ⁻¹ᵁ U).isOpen)
  have hWU : W ≤ h ⁻¹ᵁ U := fun x hx ↦ (hWO hx).2
  have hWV : i ⁻¹ᵁ W ≤ g ⁻¹ᵁ V := fun x hx ↦ by
    have : x ∈ i ⁻¹' O := (hWO hx).1
    rwa [hO'] at this
  have hsm := f.smooth_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom, (h.appLE U W hWU).hom,
    ((h.appLE U W hWU) ≫ i.app W).hom]
  let ψ₀ : Γ(X, V) →ₐ[Γ(S, U)] Γ(T₀, i ⁻¹ᵁ W) := ⟨(g.appLE _ _ hWV).hom, fun r ↦ by
    simp [RingHom.algebraMap_toAlgebra, ← CategoryTheory.comp_apply, -CommRingCat.hom_comp,
      Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, w, -Scheme.Hom.comp_appLE]⟩
  let π : Γ(T, W) →ₐ[Γ(S, U)] Γ(T₀, i ⁻¹ᵁ W) := ⟨(i.app W).hom, fun r ↦ rfl⟩
  have hπ : Function.Surjective π := i.app_surjective W hW
  have hπ' : IsNilpotent (RingHom.ker (π : Γ(T, W) →+* Γ(T₀, i ⁻¹ᵁ W))) := by
    obtain ⟨n, hn⟩ := hi
    exact ⟨n, by simpa using! congr(($hn).ideal ⟨W, hW⟩)⟩
  let ψ := Algebra.FormallySmooth.liftOfSurjective ψ₀ π hπ hπ'
  have hψ : π.comp ψ = ψ₀ := Algebra.FormallySmooth.comp_liftOfSurjective ψ₀ π hπ hπ'
  have e₁ : f.appLE U V hVU ≫ CommRingCat.ofHom ψ.toRingHom = h.appLE U W hWU :=
    CommRingCat.hom_ext ψ.comp_algebraMap
  have e₂ : CommRingCat.ofHom ψ.toRingHom ≫ i.app W = g.appLE _ _ hWV :=
    CommRingCat.hom_ext congr(($hψ).toRingHom)
  refine ⟨W, hxW, Scheme.Opens.toSpecΓ W ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV hVU,
      ← Spec.map_comp_assoc, e₁, hU.SpecMap_appLE_fromSpec h hW hWU, hW.toSpecΓ_fromSpec_assoc]
  · rw [← Scheme.Opens.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc, e₂,
      hV.SpecMap_appLE_fromSpec g (hW.preimage i) hWV, IsAffineOpen.toSpecΓ_fromSpec_assoc]
end GlobalTheory
