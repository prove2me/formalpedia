-- Prove2me | solution 1 for GlobalTheory.LatClass.topCoord_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:07:17.067814+00:00
-- url     : https://prove2.me/submissions/86d6a1fb-01f3-4dda-bf22-873e8d91b993

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZpowMulMemPow
import Theorems.Thm_GlobalTheory_LatClass_N_mulVec
import Theorems.Thm_GlobalTheory_LatClass_embX_mulVec
import Theorems.Thm_GlobalTheory_RootEx_Radical_exists_of_mem_R
import Theorems.Thm_GlobalTheory_StepData_mulVec_mem_latOf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.LatClass
variable {k : Type} [Field k] [ValuativeRel k] {ϖ : kˣ}
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.LatClass
theorem _root_.solution {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c 1) (h : GL (n ⊕ Fin c) k) (i : Fin c) :
    topCoord (latOf h) i ⊆ topCoord (latOf (r * h)) i := by
  obtain ⟨x, u, hu, rfl⟩ := Radical.exists_of_mem_R hr
  rintro _ ⟨y, hy, h0, rfl⟩
  have key : ∀ l, i ≤ l → ((embX c x * u).val *ᵥ y) (.inr l) = y (.inr l) := fun l hl => by
    rw [Units.val_mul, ← mulVec_mulVec, embX_mulVec, Sum.elim_inr]
    refine N_mulVec hu y _ ?_
    rintro (s | s) hs
    · simp [lev] at hs
    · apply h0
      simp [lev] at hs
      exact lt_of_le_of_lt hl hs
  exact ⟨_, (mulVec_mem_latOf _).2 hy, fun l hl => (key l hl.le).trans (h0 l hl), key i le_rfl⟩
end GlobalTheory.LatClass
