-- Prove2me | solution 1 for GlobalTheory.FiniteGL.mem_mirabInducedSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:25:24.637242+00:00
-- url     : https://prove2.me/submissions/61551cd2-ec4f-4557-9899-d155001bcf5b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONLeaves
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Theorems.Thm_GlobalTheory_FiniteGL_genericLine_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FiniteGL.genericLine_apply

set_option autoImplicit false
noncomputable section
open Matrix Formalism.EigenvalueLevelCeiling Formalism.L2.Indef.Tree
open GlobalTheory GlobalTheory.FiniteGL
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
namespace GlobalTheory.FiniteGL
theorem _root_.solution (ψ₀ : AddChar k ℂ) (f : mirabSub k n → ℂ) :
    f ∈ MirabInducedSpace n ψ₀ ↔
      ∀ (u : uniSub k n) (x : mirabSub k n), f ((u : mirabSub k n) * x) = genericChar n ψ₀ u * f x := by
  rw [Representation.mem_coindV]
  simp only [Subgroup.coe_subtype, genericLine_apply]
end GlobalTheory.FiniteGL
