-- Prove2me | solution 1 for GlobalTheory.IsLogBounded.of_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:02:14.011405+00:00
-- url     : https://prove2.me/submissions/c8a5c9c7-b2f6-47c2-8dca-73841fd51b80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_isLogBounded_iff_exists_scalar

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
theorem _root_.solution {G₁ G₂ : X → Matrix n n ℂ} (h₁ : IsLogBounded S w U G₁)
    (h₂ : IsLogBounded S w U G₂) (h : ∀ x ∈ U, x ∉ coordDivisor S w → G₁ x ≤ G x ∧ G x ≤ G₂ x) :
    IsLogBounded S w U G := by
  obtain ⟨g₁, hg₁, h₁⟩ := isLogBounded_iff_exists_scalar.1 h₁
  obtain ⟨g₂, hg₂, h₂⟩ := isLogBounded_iff_exists_scalar.1 h₂
  refine of_le (hg₁.hasLogGrowth.add hg₂.hasLogGrowth) fun x hx hB => ?_
  have p₁ := hg₁.pos hx hB
  have p₂ := hg₂.pos hx hB
  exact ⟨add_pos p₁ p₂,
    (real_smul_one_le_real_smul_one (inv_anti₀ p₁ (by linarith))).trans
      ((h₁ x hx hB).1.trans (h x hx hB).1),
    ((h x hx hB).2.trans (h₂ x hx hB).2).trans (real_smul_one_le_real_smul_one (by linarith))⟩
end GlobalTheory.IsLogBounded
