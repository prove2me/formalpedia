-- Prove2me | solution 1 for GlobalTheory.finite_of_isClosed_torusExtension_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:25:45.324546+00:00
-- url     : https://prove2.me/submissions/068ce1ff-adb2-41ec-99a0-de22a95779bc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteOfIsClosedSplitTorusOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteOfIsClosedTorusExtensionOfPowEqOne
import Theorems.Thm_GlobalTheory_map_eq_one_of_pow_eq_one_of_finite_ker
import Theorems.Thm_GlobalTheory_RationalPoint_range_left_subset_iff
import Theorems.Thm_GlobalTheory_exists_isClosed_image_of_isClosed_subgroup
import Theorems.Thm_GlobalTheory_finite_of_isClosed_splitTorus_of_pow_eq_one
import Theorems.Thm_GlobalTheory_laurentEval_single
import Theorems.Thm_GlobalTheory_torusCoord_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.laurentEval_single
attribute [local simp] GlobalTheory.torusCoord_apply



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open RationalPoint
namespace GlobalTheory
theorem _root_.solution :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (n : ℕ), IsAbelianScheme B → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C) → ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (n : ℕ), LocallyOfFiniteType G.hom → QuasiCompact G.hom → Nonempty (TorusExtension G) → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) (Z : Set G.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C := by
  intro hab k _ _ G _ _ n _ _ ⟨E⟩ hp hn C Z hZ hC htors
  letI := E.addCommGroup
  letI := E.free
  letI := E.finite
  letI := E.grpB
  haveI := E.q_hom
  haveI := E.i_hom
  haveI := E.isAbelian.proper
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ E.B) :=
    MonoidHom.mk' (fun x => x ≫ E.q) fun x y => MonObj.mul_comp x y E.q
  let j : (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) E.X) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ E.i) fun x y => MonObj.mul_comp x y E.i
  have hj : Function.Injective j := fun x y hxy =>
    E.isKernel.hom_ext hxy (toUnit_unique _ _)
  have hker : ∀ x, φ x = 1 → ∃ t, j t = x := fun x hx =>
    ⟨E.isKernel.lift x (toUnit _) hx, E.isKernel.lift_fst _ _ _⟩
  have hT : Finite (C.comap j) := by
    refine finite_of_isClosed_splitTorus_of_pow_eq_one k E.X n hp hn _ (E.i.left ⁻¹' Z)
      (hZ.preimage E.i.left.continuous) (fun x => ?_) fun x hx h1 => ?_
    · rw [Subgroup.mem_comap, hC, range_left_subset_iff, range_left_subset_iff]
      rfl
    · exact hj (by rw [map_one]; exact htors _ hx (by rw [← map_pow, h1, map_one]))
  let ψ : C →* (𝟙_ (Over (Sp k)) ⟶ E.B) := φ.comp C.subtype
  have hK : Finite ψ.ker := by
    choose s hs using fun x : ψ.ker => hker x.1.1 x.2
    refine Finite.of_injective
      (fun x : ψ.ker => (⟨s x, by rw [Subgroup.mem_comap, hs]; exact x.1.2⟩ : C.comap j))
      fun x y hxy => ?_
    have := congrArg (fun t : C.comap j => j t.1) hxy
    simp only [hs] at this
    exact Subtype.ext (Subtype.ext this)
  obtain ⟨Z', hZ', h'⟩ := exists_isClosed_image_of_isClosed_subgroup k G E.B E.q inferInstance
    inferInstance inferInstance inferInstance inferInstance C Z hZ hC
  have hR : Finite ψ.range := by
    refine hab k E.B n E.isAbelian hp hn _ Z' hZ' (fun y => ?_) ?_
    · rw [← h']
      exact ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, hx⟩, fun ⟨x, hx, hy⟩ => ⟨⟨x, hx⟩, hy⟩⟩
    · rintro _ ⟨y, rfl⟩ hy
      exact map_eq_one_of_pow_eq_one_of_finite_ker ψ hp
        (fun x hx => Subtype.ext (htors x.1 x.2 (congrArg Subtype.val hx))) y hy
  exact (MonoidHom.finite_iff_finite_ker_range ψ).2 ⟨hK, hR⟩
end GlobalTheory
