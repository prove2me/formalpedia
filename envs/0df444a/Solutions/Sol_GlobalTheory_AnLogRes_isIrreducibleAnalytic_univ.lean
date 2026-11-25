-- Prove2me | solution 1 for GlobalTheory.AnLogRes.isIrreducibleAnalytic_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:41:09.012639+00:00
-- url     : https://prove2.me/submissions/5c0ddcb0-3fb1-40ae-b64f-72a7c6ea68c4

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AnalyticLogResolution
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__LogResolutionProjectiveLine_09840aae280abe50
import Theorems.Thm_GlobalTheory_AnLogRes_eq_univ_of_interior_nonempty
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_isClosed
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
open GlobalTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open GlobalTheory.AnLogRes
variable {d : ℕ} {X : Type} [TopologicalSpace X]
namespace GlobalTheory.AnLogRes
theorem _root_.solution [ConnectedSpace X] (A : FinHolAtlas d X) :
    IsIrreducibleAnalytic A Set.univ := by
  refine ⟨fun x => ⟨Set.univ, isOpen_univ, trivial, 0, Fin.elim0, fun i => i.elim0, by simp⟩,
    Set.univ_nonempty, fun Z₁ Z₂ h₁ h₂ h => ?_⟩
  by_cases e : Set.univ = Z₁
  · exact Or.inl e
  · refine Or.inr (eq_univ_of_interior_nonempty A h₂ ?_).symm
    obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).1 (Ne.symm e)
    refine ⟨x, mem_interior.2 ⟨Z₁ᶜ, fun y hy => ?_, (pushA_isClosed A h₁).isOpen_compl, hx⟩⟩
    exact (h ▸ Set.mem_univ y : y ∈ Z₁ ∪ Z₂).resolve_left hy
end GlobalTheory.AnLogRes
