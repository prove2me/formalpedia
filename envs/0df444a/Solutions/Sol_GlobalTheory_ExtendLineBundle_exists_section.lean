-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.exists_section
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:15.204062+00:00
-- url     : https://prove2.me/submissions/ab77b2b8-ed59-44c5-a57a-5fbe297baaa7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Theorems.Thm_GlobalTheory_ExtendLineBundle_exists_section_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open GlobalTheory GlobalTheory.ExtendLineBundle
variable {X Y : Scheme.{0}} [IsIntegral X]
namespace GlobalTheory.ExtendLineBundle
theorem _root_.solution {U : X.Opens} (h : genericPoint X ∈ U) {t : X.functionField}
    (ht : ∀ x ∈ U, t ∈ localSubring x) : ∃ s : Γ(X, U), X.presheaf.germ U _ h s = t := by
  choose V hV s hs using fun x : U => exists_section_of_mem (ht x.1 x.2)
  have hη : ∀ x : U, genericPoint X ∈ V x ⊓ U := fun x => ⟨genericPoint_mem (hV x), h⟩
  have hs' : ∀ x : U, X.presheaf.germ (V x ⊓ U) _ (hη x)
      (X.presheaf.map (homOfLE (inf_le_left : V x ⊓ U ≤ V x)).op (s x)) = t := fun x =>
    (X.presheaf.germ_res_apply _ _ _ _).trans (hs x)
  obtain ⟨a, ha, -⟩ := X.sheaf.existsUnique_gluing' (fun x : U => V x ⊓ U) U
    (fun x => homOfLE inf_le_right)
    (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hV _, hy⟩)
    (fun x => X.presheaf.map (homOfLE (inf_le_left : V x ⊓ U ≤ V x)).op (s x))
    (fun x y => germ_injective_of_isIntegral X (U := (V x ⊓ U) ⊓ (V y ⊓ U)) _ ⟨hη x, hη y⟩
      (((X.presheaf.germ_res_apply _ _ _ _).trans (hs' x)).trans
        ((X.presheaf.germ_res_apply _ _ _ _).trans (hs' y)).symm))
  refine ⟨a, ?_⟩
  rw [← hs' ⟨_, h⟩]
  exact (X.presheaf.germ_res_apply (homOfLE inf_le_right) _ (hη ⟨_, h⟩) a).symm.trans
    (congrArg _ (ha ⟨_, h⟩))
end GlobalTheory.ExtendLineBundle
