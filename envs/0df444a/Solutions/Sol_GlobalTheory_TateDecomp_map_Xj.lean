-- Prove2me | solution 1 for GlobalTheory.TateDecomp.map_Xj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:03:38.830342+00:00
-- url     : https://prove2.me/submissions/0e53e47f-e32d-486e-989f-f39aad78073d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Theorems.Thm_GlobalTheory_TateDecomp_Xlev_le_Xsum
import Theorems.Thm_GlobalTheory_TateDecomp_mem_Xj

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
theorem _root_.solution {K : FinExt l} {j : ℕ} (f : PadicComplex l →+ PadicComplex l) (hf : Continuous f)
    (h : ∀ i, j < i → ∀ ζ y : PadicComplex l, IsPrimitiveRoot ζ (l ^ i) →
      y ∈ intC (Ks K (i - 1)) → f (ζ * y) ∈ Xlev K i) {x : PadicComplex l} (hx : x ∈ Xj K j) :
    f x ∈ Xj K j := by
  have h1 : Xsum K j ≤ (Xsum K j).comap f := by
    refine iSup₂_le fun i hi => ?_
    rw [Xlev, AddSubgroup.closure_le]
    rintro z ⟨ζ, y, hζ, hy, rfl⟩
    exact Xlev_le_Xsum K hi (h i hi ζ y hζ hy)
  exact map_mem_closure hf (mem_Xj.1 hx) fun y hy => h1 hy
end GlobalTheory.TateDecomp
