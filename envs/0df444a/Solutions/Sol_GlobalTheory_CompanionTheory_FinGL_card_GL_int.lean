-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinGL.card_GL_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:48:35.885796+00:00
-- url     : https://prove2.me/submissions/459f00c5-6e01-4fc5-bd29-4b3bf4aab2b9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardParabolicSubgroup
import Theorems.Thm_GlobalTheory_CompanionTheory_FinGL_prod_pow_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinGL
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
namespace GlobalTheory.CompanionTheory.FinGL
theorem _root_.solution (ι : Type) [Fintype ι] [DecidableEq ι] :
    (Nat.card (GL ι K) : ℤ) = (Fintype.card K : ℤ) ^ (Fintype.card ι).choose 2 *
      ∏ i ∈ Finset.Icc 1 (Fintype.card ι), ((Fintype.card K : ℤ) ^ i - 1) := by
  rw [Nat.card_congr (glEquiv K (Fintype.equivFin ι)).toEquiv, Matrix.card_GL_field,
    ← prod_pow_sub, Fin.prod_univ_eq_prod_range (fun i => Fintype.card K ^ Fintype.card ι - Fintype.card K ^ i),
    Nat.cast_prod]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hq : 0 < Fintype.card K := Fintype.card_pos
  have hle : Fintype.card K ^ i ≤ Fintype.card K ^ Fintype.card ι :=
    Nat.pow_le_pow_right hq (Finset.mem_range.mp hi).le
  push_cast [Nat.cast_sub hle]
  rfl
end GlobalTheory.CompanionTheory.FinGL
