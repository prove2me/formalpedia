-- Prove2me | solution 1 for GlobalTheory.GenScheme.prop_of_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:28:25.442865+00:00
-- url     : https://prove2.me/submissions/b660a12f-2a03-40c4-9490-4b2a7af473a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
import Theorems.Thm_GlobalTheory_GenScheme_exists_isPullback
import Theorems.Thm_GlobalTheory_Diag_exists_isPullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory
open GlobalTheory.GenScheme
variable {B : Scheme.{0}} {κ : Type} {N : κ → LB B} {G : Scheme.{0}} {q : G ⟶ B}
  {u : ∀ k (i : (N k).ι), Γ(G, q ⁻¹ᵁ (N k).U i)ˣ}
namespace GlobalTheory.GenScheme
theorem _root_.solution [Fintype κ] (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    (hP : ∀ V : Scheme.{0}, P (splitTorus V (κ →₀ ℤ)).hom)
    (hN : ∀ k, (N k).IsLB) (hu : ∀ k, Compat (N k) q (u k)) (hU : Univ N q u) : P q := by
  let W : (∀ k, (N k).ι) → B.Opens := fun j =>
    ⟨⋂ k, ((N k).U (j k) : Set B), isOpen_iInter_of_finite fun k => ((N k).U (j k)).isOpen⟩
  have hW : iSup W = ⊤ := by
    refine top_le_iff.1 fun x _ => ?_
    have : ∀ k, ∃ i, x ∈ (N k).U i := fun k =>
      TopologicalSpace.Opens.mem_iSup.1 ((hN k).cover.ge trivial)
    choose j hj using this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, Set.mem_iInter.2 hj⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top W hW fun j => ?_
  obtain ⟨p, hp⟩ := exists_isPullback hN hu hU (W j).ι j
    fun k x _ => Set.mem_iInter.1 x.2 k
  have h := (isPullback_morphismRestrict q (W j)).flip
  rw [← h.isoIsPullback_hom_snd _ _ hp, MorphismProperty.cancel_left_of_respectsIso P]
  exact hP _
end GlobalTheory.GenScheme
