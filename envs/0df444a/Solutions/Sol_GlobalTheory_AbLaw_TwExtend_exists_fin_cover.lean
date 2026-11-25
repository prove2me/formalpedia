-- Prove2me | solution 1 for GlobalTheory.AbLaw.TwExtend.exists_fin_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:33:45.722796+00:00
-- url     : https://prove2.me/submissions/44a9a629-afbe-42e0-bf0a-b14b5504844d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsTwExtendPowMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_mem_of_cover


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.TwExtend
variable {Y : Scheme.{0}}
namespace GlobalTheory.AbLaw.TwExtend
theorem _root_.solution [CompactSpace Y] {M H : LB Y} (hM : M.IsLB) (hH : H.IsLB) :
    ∃ (κ : Type) (_ : Fintype κ) (W : κ → Y.Opens) (p : κ → M.ι) (l : κ → H.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ M.U (p a) ⊓ H.U (l a)) ∧ ⊤ ≤ ⨆ a, W a := by
  have h : ∀ x : Y, ∃ (W : Y.Opens) (p : M.ι) (l : H.ι),
      IsAffineOpen W ∧ x ∈ W ∧ W ≤ M.U p ⊓ H.U l := by
    intro x
    obtain ⟨p, hp⟩ := LB.mem_of_cover hM x
    obtain ⟨l, hl⟩ := LB.mem_of_cover hH x
    obtain ⟨_, ⟨W, hW, rfl⟩, hx, hle⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ M.U p ⊓ H.U l from ⟨hp, hl⟩)
        (M.U p ⊓ H.U l).isOpen
    exact ⟨W, p, l, hW, hx, hle⟩
  choose W p l hW hx hle using h
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set Y))
    (fun x => (W x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  refine ⟨s, inferInstance, fun a => W a, fun a => p a, fun a => l a, fun a => hW a,
    fun a => hle a, ?_⟩
  intro x _
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩
end GlobalTheory.AbLaw.TwExtend
