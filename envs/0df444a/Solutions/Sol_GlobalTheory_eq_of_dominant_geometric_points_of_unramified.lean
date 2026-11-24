-- Prove2me | solution 1 for GlobalTheory.eq_of_dominant_geometric_points_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:56:35.587227+00:00
-- url     : https://prove2.me/submissions/87a1a47a-9db4-4c0b-a5c0-28a25d6c4e34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqOfDominantGeometricPointsOfUnramified
import Theorems.Thm_GlobalTheory_exists_point_over_dominant_geometric_point
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_P2M_GlobalTheory_eq_of_range_equalizer___eq_univ_5724cbc41fd4
import Theorems.Thm_P2M_GlobalTheory_isClosedImmersion_equalizer___of_isSeparated_bdcf708e7a7d
import Theorems.Thm_P2M_GlobalTheory_range_subset_range_equalizer___aeb7241b0453
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
universe u
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X S T : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] [IsSeparated f] (g : T ⟶ S)
    [UniversallyOpen g] [LocallyOfFiniteType g] {a b : T ⟶ X} (ha : a ≫ f = g) (hb : b ≫ f = g)
    {F : Type u} [Field F] [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t]
    (h : ∀ j : Spec (.of F) ⟶ T, j ≫ g = t → j ≫ a = j ≫ b) : a = b := by
  have hab : a ≫ f = b ≫ f := ha.trans hb.symm
  have := isClosedImmersion_equalizer_ι_of_isSeparated f hab
  refine eq_of_range_equalizer_ι_eq_univ f hab ?_
  by_contra hne
  let U : T.Opens := ⟨(Set.range (equalizer.ι a b))ᶜ,
    (equalizer.ι a b).isClosedEmbedding.isClosed_range.isOpen_compl⟩
  obtain ⟨y, hy⟩ := Set.nonempty_compl.mpr hne
  have : Nonempty U.toScheme := ⟨⟨y, hy⟩⟩
  obtain ⟨j, hj⟩ := exists_point_over_dominant_geometric_point (U.ι ≫ g) t
  have h1 := range_subset_range_equalizer_ι (j ≫ U.ι) (h _ (by simpa using hj))
  obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of F)) := inferInstance
  have h2 : (j ≫ U.ι) p ∈ U := by
    rw [Scheme.Hom.comp_apply]
    exact (j p).2
  exact h2 (h1 ⟨_, rfl⟩)
end GlobalTheory
