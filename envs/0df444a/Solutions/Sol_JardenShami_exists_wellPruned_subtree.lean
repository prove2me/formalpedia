-- Prove2me | solution 1 for JardenShami.exists_wellPruned_subtree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:47:36.879907+00:00
-- url     : https://prove2.me/submissions/26bbdaec-9354-4cdb-b854-37b1926d254b

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
import Theorems.Thm_JardenShami_exists_wellPruned_subtree_downward

set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution (κ : Cardinal.{w}) (hκ : κ.IsRegular)
    (T : Type w) [PartialOrder T] [IsTree T] (hT : IsKappaTree κ T) :
    ∃ S : Set T, IsKappaTree κ S ∧ WellPruned S := by
  obtain ⟨S, -, hS, hwp⟩ := exists_wellPruned_subtree_downward κ hκ T hT
  exact ⟨S, hS, hwp⟩
end JardenShami
