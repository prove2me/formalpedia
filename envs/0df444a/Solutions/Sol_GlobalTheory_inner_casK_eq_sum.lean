-- Prove2me | solution 1 for GlobalTheory.inner_casK_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:34:26.178905+00:00
-- url     : https://prove2.me/submissions/8760cd78-f68b-425e-957a-9a48bc9e39eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CasKIsSymmetricAndForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}
    {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (h : KUnit ε E) (x y : M) :
    ⟪x, CasK ε E y⟫_ℂ = ∑ a, ∑ b, if ε a = ε b then ⟪E a b x, E a b y⟫_ℂ else 0 := by
  unfold CasK
  rw [Finset.sum_comm]
  simp only [LinearMap.sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : ε a = ε b
  · rw [if_pos hab.symm, if_pos hab, Module.End.mul_apply, h a b hab]
  · rw [if_neg (fun e => hab e.symm), if_neg hab]
    simp
end GlobalTheory
