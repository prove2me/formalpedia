-- Prove2me | solution 1 for GlobalTheory.existsUnique_lift_of_etale_of_henselian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:46:51.946284+00:00
-- url     : https://prove2.me/submissions/69f03033-5bab-4873-9565-c9006d66e3e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Theorems.Thm_GlobalTheory_eq_of_isLocalRing_of_unramified
import Theorems.Thm_GlobalTheory_exists_algHom_lift_of_henselian
import Theorems.Thm_GlobalTheory_exists_specMap_fromSpec_eq

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
namespace GlobalTheory
theorem _root_.solution {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]
    {R K : Type u} [CommRing R] [HenselianLocalRing R] [Field K] (π : R →+* K)
    (hπ : Function.Surjective π) (g : Spec (.of K) ⟶ X) (h : Spec (.of R) ⟶ S)
    (w : g ≫ f = Spec.map (CommRingCat.ofHom π) ≫ h) :
    ∃! l : Spec (.of R) ⟶ X, Spec.map (CommRingCat.ofHom π) ≫ l = g ∧ l ≫ f = h := by
  have hloc : IsLocalHom π := .of_surjective _ hπ
  have hcl : Spec.map (CommRingCat.ofHom π) (IsLocalRing.closedPoint K) =
      IsLocalRing.closedPoint R := IsLocalRing.comap_closedPoint π
  refine existsUnique_of_exists_of_unique ?_ fun l₁ l₂ h₁ h₂ ↦
    eq_of_isLocalRing_of_unramified f (h₁.2.trans h₂.2.symm) _ ⟨_, hcl⟩ (h₁.1.trans h₂.1.symm)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f (g (IsLocalRing.closedPoint K)))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ f ⁻¹ᵁ U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).isOpen
  replace hU : IsAffineOpen U := hU
  replace hV : IsAffineOpen V := hV
  have hgV : g ⁻¹ᵁ V = ⊤ := (IsLocalRing.closed_point_mem_iff (R := K)).mp hxV
  have hhU : h ⁻¹ᵁ U = ⊤ := (IsLocalRing.closed_point_mem_iff (R := R)).mp (by
    have : h (Spec.map (CommRingCat.ofHom π) (IsLocalRing.closedPoint K)) ∈ U := by
      have e : f (g (IsLocalRing.closedPoint K)) =
          h (Spec.map (CommRingCat.ofHom π) (IsLocalRing.closedPoint K)) :=
        congr($w (IsLocalRing.closedPoint K))
      exact e ▸ hxU
    rw [hcl] at this
    exact this)
  obtain ⟨φ, rfl⟩ := exists_specMap_fromSpec_eq g hV (by
    rintro _ ⟨x, rfl⟩; exact (hgV.ge (Set.mem_univ x) :))
  obtain ⟨α, rfl⟩ := exists_specMap_fromSpec_eq h hU (by
    rintro _ ⟨x, rfl⟩; exact (hhU.ge (Set.mem_univ x) :))
  rw [Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV hVU, ← Spec.map_comp_assoc,
    ← Spec.map_comp_assoc, cancel_mono, Spec.map_inj] at w
  have het := f.etale_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  letI : Algebra Γ(S, U) R := α.hom.toAlgebra
  letI : Algebra Γ(S, U) K := (π.comp α.hom).toAlgebra
  obtain ⟨ψ, hψ⟩ := exists_algHom_lift_of_henselian (B := Γ(S, U)) (A := Γ(X, V))
    ⟨π, fun _ ↦ rfl⟩ hπ ⟨φ.hom, fun r ↦ congr($w r)⟩
  have e₁ : f.appLE U V hVU ≫ CommRingCat.ofHom ψ.toRingHom = α :=
    CommRingCat.hom_ext ψ.comp_algebraMap
  have e₂ : CommRingCat.ofHom ψ.toRingHom ≫ CommRingCat.ofHom π = φ :=
    CommRingCat.hom_ext congr(($hψ).toRingHom)
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec, ?_, ?_⟩
  · rw [← Spec.map_comp_assoc, e₂]
  · rw [Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV hVU, ← Spec.map_comp_assoc, e₁]
end GlobalTheory
