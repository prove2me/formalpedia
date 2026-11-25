-- Prove2me | solution 1 for GlobalTheory.ReducedSubgroup.exists_smooth_closed_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:02:11.57185+00:00
-- url     : https://prove2.me/submissions/ef893c71-ec15-48a5-aa18-dc4e9f189d51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyReducedOfPerfectField
import Theorems.Thm_GlobalTheory_ReducedSubgroup_exists_grpObj_of_mono
import Theorems.Thm_GlobalTheory_ReducedSubgroup_isReduced_subscheme_vanishingIdeal
import Theorems.Thm_GlobalTheory_ReducedSubgroup_vanishingIdeal_le_ker
import Theorems.Thm_GlobalTheory_ReducedSubgroup_geometricallyReduced_of_perfectField
import Theorems.Thm_GlobalTheory_ReducedSubgroup_range_subset_of_points

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ReducedSubgroup
open Scheme.IdealSheafData
namespace GlobalTheory.ReducedSubgroup
theorem _root_.solution (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k))
    [GrpObj B] (hB : LocallyOfFiniteType B.hom) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B))
    (Z : Set B.left) (hZ : IsClosed Z) (hC : ∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) :
    ∃ (N : Over (Sp k)) (_ : GrpObj N) (ν : N ⟶ B), IsMonHom ν ∧ IsClosedImmersion ν.left ∧
      Smooth N.hom ∧ Set.range ν.left = Z := by
  let I : B.left.IdealSheafData := vanishingIdeal ⟨Z, hZ⟩
  let N : Over (Sp k) := Over.mk (I.subschemeι ≫ B.hom)
  let ν : N ⟶ B := Over.homMk I.subschemeι rfl
  have hν : IsClosedImmersion ν.left := inferInstanceAs (IsClosedImmersion I.subschemeι)
  have hr : Set.range ν.left = Z := by
    change Set.range I.subschemeι = Z
    rw [range_subschemeι]
    rfl
  have : Mono ν := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono ν.left))
  have hred : IsReduced N.left := isReduced_subscheme_vanishingIdeal _
  have hft : LocallyOfFiniteType N.hom :=
    inferInstanceAs (LocallyOfFiniteType (I.subschemeι ≫ B.hom))
  have hgr : GeometricallyReduced N.hom := geometricallyReduced_of_perfectField N.hom
  have hnoeth : IsLocallyNoetherian N.left := LocallyOfFiniteType.isLocallyNoetherian N.hom
  have hlift : ∀ {T : Over (Sp k)} [IsReduced T.left] [LocallyOfFiniteType T.hom] (g : T ⟶ B),
      (∀ x : 𝟙_ (Over (Sp k)) ⟶ T, x ≫ g ∈ C) → ∃ l : T ⟶ N, l ≫ ν = g := by
    intro T _ _ g hg
    have h1 := range_subset_of_points g hZ fun x => (hC _).mp (hg x)
    have h2 : I.subschemeι.ker ≤ g.left.ker := by
      rw [ker_subschemeι]
      exact vanishingIdeal_le_ker g.left ⟨Z, hZ⟩ h1
    have h3 := IsClosedImmersion.lift_fac I.subschemeι g.left h2
    refine ⟨Over.homMk (IsClosedImmersion.lift I.subschemeι g.left h2) ?_, ?_⟩
    · change _ ≫ I.subschemeι ≫ B.hom = _
      rw [← Category.assoc, h3, Over.w]
    · ext1
      exact h3
  have hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C := fun x => by
    rw [hC, ← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨x.left t, rfl⟩
  have : IsReduced (𝟙_ (Over (Sp k))).left := inferInstanceAs (IsReduced (Sp k))
  have : LocallyOfFiniteType (𝟙_ (Over (Sp k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Sp k)))
  have : IsReduced (N ⊗ N).left := inferInstanceAs (IsReduced (pullback N.hom N.hom))
  have : LocallyOfFiniteType (N ⊗ N).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst N.hom N.hom ≫ N.hom))
  obtain ⟨e, he⟩ := hlift η[B] fun x => by
    rw [toUnit_unique x (toUnit _), ← Hom.one_def]
    exact C.one_mem
  obtain ⟨m, hm⟩ := hlift ((ν ⊗ₘ ν) ≫ μ[B]) fun x => by
    have : x ≫ (ν ⊗ₘ ν) ≫ μ[B] = ((x ≫ fst N N) ≫ ν) * ((x ≫ snd N N) ≫ ν) := by
      rw [Hom.mul_def, ← lift_map, Category.assoc, ← comp_lift, lift_fst_snd, Category.comp_id]
    rw [this]
    exact C.mul_mem (hmem _) (hmem _)
  obtain ⟨i, hi⟩ := hlift (ν ≫ GrpObj.inv) fun x => by
    rw [← Category.assoc, ← Hom.inv_def]
    exact C.inv_mem (hmem _)
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono ν e m i he hm hi
  refine ⟨N, G, ν, hG, hν, ?_, hr⟩
  letI : GrpObj (Over.mk N.hom) := G
  exact smooth_of_grpObj N.hom
end GlobalTheory.ReducedSubgroup
