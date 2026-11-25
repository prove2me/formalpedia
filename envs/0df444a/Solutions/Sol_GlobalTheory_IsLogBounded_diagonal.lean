-- Prove2me | solution 1 for GlobalTheory.IsLogBounded.diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:58:07.433382+00:00
-- url     : https://prove2.me/submissions/e08d4797-e335-415f-a8a3-6805dd1120e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology
open GlobalTheory
variable {κ κ' X X' m n : Type*} [TopologicalSpace X] [TopologicalSpace X']
variable [DecidableEq n] [DecidableEq m] {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
  {G G' : X → Matrix n n ℂ} {H : X → Matrix m m ℂ}
variable [Fintype n]
open GlobalTheory.IsLogBounded
namespace GlobalTheory.IsLogBounded
theorem _root_.solution {g : n → X → ℝ} (hg : ∀ i, IsLogBoundedScalar S w U (g i)) :
    IsLogBounded S w U fun x => Matrix.diagonal fun i => (g i x : ℂ) := by
  have key : ∀ {g : n → X → ℝ}, (∀ i, IsLogBoundedScalar S w U (g i)) →
      HasLogGrowthEntries S w U fun x => Matrix.diagonal fun i => (g i x : ℂ) := by
    intro g hg i j
    refine (hg i).hasLogGrowth.of_norm_le fun x _ _ => ?_
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [diagonal_apply_ne _ h]
  refine isLogBounded_iff_entries.2 ⟨fun x hx hB => PosDef.diagonal fun i => ?_, key hg,
    (key fun i => (hg i).inv).congr fun x hx hB => inv_eq_left_inv ?_⟩
  · exact_mod_cast (hg i).pos hx hB
  · rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact_mod_cast inv_mul_cancel₀ ((hg i).pos hx hB).ne'
end GlobalTheory.IsLogBounded
