-- Prove2me | solution 1 for GlobalTheory.LiePull.basis_transport
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:01:07.792565+00:00
-- url     : https://prove2.me/submissions/65b7221f-86f9-4a04-906f-f61c42c8c23b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPushEquiv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LiePull
namespace GlobalTheory.LiePull
theorem _root_.solution {A B k : Type} [Monoid A] [Monoid B] (e : A ≃* B) {P : A → Prop} {Q : B → Prop}
    {R : k → A → A → Prop} {R' : k → B → B → Prop} (hP : ∀ x, P x ↔ Q (e x))
    (hR : ∀ c x y, R c x y ↔ R' c (e x) (e y)) (n : ℕ)
    (H : ∃ v : Fin n → A, (∀ i, P (v i)) ∧ ∀ w, P w →
      ∃! c : Fin n → k, ∃ u : Fin n → A, (∀ i, R (c i) (u i) (v i)) ∧ w = (List.ofFn u).prod) :
    ∃ v : Fin n → B, (∀ i, Q (v i)) ∧ ∀ w, Q w →
      ∃! c : Fin n → k, ∃ u : Fin n → B, (∀ i, R' (c i) (u i) (v i)) ∧ w = (List.ofFn u).prod := by
  obtain ⟨v, hv, H⟩ := H
  refine ⟨fun i => e (v i), fun i => (hP _).1 (hv i), fun w hw => ?_⟩
  obtain ⟨w, rfl⟩ := e.surjective w
  have pr : ∀ u : Fin n → A, e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod := fun u => by
    rw [map_list_prod, List.map_ofFn]; rfl
  refine (existsUnique_congr fun c => ⟨?_, ?_⟩).1 (H w ((hP _).2 hw))
  · rintro ⟨u, hu, rfl⟩
    exact ⟨fun i => e (u i), fun i => (hR _ _ _).1 (hu i), pr u⟩
  · rintro ⟨u, hu, hw⟩
    refine ⟨fun i => e.symm (u i), fun i => (hR _ _ _).2 (by simpa using hu i), e.injective ?_⟩
    rw [pr, hw]
    simp
end GlobalTheory.LiePull
