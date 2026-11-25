-- Prove2me | solution 1 for GlobalTheory.TateDecomp.root_mem_subC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:05:50.930801+00:00
-- url     : https://prove2.me/submissions/ead8ccfa-d6f8-4da9-9184-7567089cef31

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Theorems.Thm_GlobalTheory_TateDecomp_root_mem_Ks
import Theorems.Thm_GlobalTheory_TateDecomp_exists_prim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.TateDecomp
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.TateDecomp
theorem _root_.solution (K : FinExt l) {i : ℕ} {ξ : PadicComplex l} (h : ξ ^ (l ^ i) = 1) :
    ξ ∈ subC (Ks K i) := by
  haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_prim (l := l) i
  obtain ⟨k, -, rfl⟩ := (hζ.map_of_injective (io l).injective).eq_pow_of_pow_eq_one h
  exact pow_mem (⟨ζ, root_mem_Ks K hζ.pow_eq_one, rfl⟩ : io l ζ ∈ subC (Ks K i)) k
end GlobalTheory.TateDecomp
