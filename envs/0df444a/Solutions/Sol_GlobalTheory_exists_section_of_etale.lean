-- Prove2me | solution 1 for GlobalTheory.exists_section_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:47.172324+00:00
-- url     : https://prove2.me/submissions/cede2009-4070-4804-ab5e-fa177f8a4c79

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Theorems.Thm_GlobalTheory_isOpenImmersion_of_section_of_etale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of K)) [Etale f] (x : X) :
    ∃ s : Spec (CommRingCat.of K) ⟶ X, s ≫ f = 𝟙 _ ∧ x ∈ Set.range s := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  let W : Set X := ⋃ s : {s : Spec (CommRingCat.of K) ⟶ X // s ≫ f = 𝟙 _}, Set.range s.1
  have hW : IsOpen W := isOpen_iUnion fun s => by
    have := isOpenImmersion_of_section_of_etale f s.1 s.2
    exact s.1.isOpenEmbedding.isOpen_range
  have hx : x ∈ W := by
    by_contra hx
    obtain ⟨c, hc, hc'⟩ := nonempty_inter_closedPoints (Z := Wᶜ) ⟨x, hx⟩
      hW.isClosed_compl.isLocallyClosed
    replace hc' : IsClosed {c} := hc'
    exact hc (Set.mem_iUnion.mpr ⟨⟨_, pointOfClosedPoint_comp f c hc'⟩,
      IsLocalRing.closedPoint K, pointOfClosedPoint_apply f c hc' _⟩)
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
  exact ⟨s.1, s.2, hs⟩
end GlobalTheory
