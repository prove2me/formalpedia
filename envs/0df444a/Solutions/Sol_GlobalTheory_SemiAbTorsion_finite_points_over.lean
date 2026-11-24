-- Prove2me | solution 1 for GlobalTheory.SemiAbTorsion.finite_points_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:12:26.799711+00:00
-- url     : https://prove2.me/submissions/1dc23996-e57c-4ac9-bfce-023c4eefd28a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SemiAbelianTorsionFiniteAndClosedPointFiniteOrde
import Theorems.Thm_GlobalTheory_SemiAbTorsion_finite_hom_range_subset

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.SemiAbTorsion
namespace GlobalTheory.SemiAbTorsion
theorem _root_.solution {Z : Scheme.{0}} (π : Z ⟶ Sp ℤ) [LocallyOfFiniteType π] (G : Over Z)
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] (F : Type) [Field F] [Finite F]
    (t : Sp F ⟶ Z) : Finite (Over.mk t ⟶ G) := by
  let pt : Sp F := default
  have hpt : ∀ y : Sp F, y = pt := fun y => Subsingleton.elim _ _
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (t pt)) isOpen_univ
  have hc : IsCompact (G.hom ⁻¹ᵁ U : Set G.left) :=
    QuasiCompact.isCompact_preimage (f := G.hom) _ U.isOpen hU.isCompact
  obtain ⟨s, hs, hsU⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens).mp hc
  have hfin : (⋃ V ∈ s, {f : Sp F ⟶ G.left | Set.range f ⊆ V.1}).Finite :=
    hs.biUnion fun V _ => finite_hom_range_subset (G.hom ≫ π) (CommRingCat.of F) V.1 V.2
  haveI := hfin.to_subtype
  have hm : ∀ x : Over.mk t ⟶ G,
      x.left ∈ ⋃ V ∈ s, {f : Sp F ⟶ G.left | Set.range f ⊆ V.1} := by
    intro x
    have h1 : x.left pt ∈ G.hom ⁻¹ᵁ U := by
      change (x.left ≫ G.hom) pt ∈ U
      rw [Over.w x]
      exact hxU
    rw [hsU] at h1
    simp only [TopologicalSpace.Opens.mem_iSup] at h1
    obtain ⟨V, hV, hx⟩ := h1
    refine Set.mem_biUnion hV ?_
    rintro _ ⟨y, rfl⟩
    rw [hpt y]
    exact hx
  exact Finite.of_injective (fun x => (⟨x.left, hm x⟩ : (⋃ V ∈ s,
    {f : Sp F ⟶ G.left | Set.range f ⊆ V.1} : Set _)))
    fun a b h => Over.OverMorphism.ext (congrArg Subtype.val h)
end GlobalTheory.SemiAbTorsion
