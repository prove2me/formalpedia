-- Prove2me | solution 1 for GlobalTheory.TateMatrices.pairing_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:24:28.046139+00:00
-- url     : https://prove2.me/submissions/0a7b8daa-3117-4f55-9a59-89e068bcb6e1

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_CharR
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsTateMatricesLink
import Theorems.Thm_GlobalTheory_TateMatrices_pairing_zero_left
import Theorems.Thm_GlobalTheory_TateMatrices_pairing_nsmul_left
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isPairingValue_add_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2
noncomputable section
open GlobalTheory
open GlobalTheory.TateMatrices
variable {R₀ : Type} [CommRing R₀] (B : BX R₀) {R : LAlg R₀}
namespace GlobalTheory.TateMatrices
theorem _root_.solution {ι : Type} (s : Finset ι) (N : ℕ) (x : ι → B.G R) (y : B.G R)
    (ζ : (R : Type)ˣ) (a e : ι → ℕ) (hy : N • y = 0) (h : ∀ i, B.IsPairing N (x i) y (ζ ^ e i)) :
    B.IsPairing N (∑ i ∈ s, a i • x i) y (ζ ^ ∑ i ∈ s, a i * e i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, pow_zero]
    exact pairing_zero_left B N y hy
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, pow_add, mul_comm (a b), pow_mul]
    exact B.isPairingValue_add_left N _ _ _ _ _ (pairing_nsmul_left B N _ _ _ (h b) _) ih
end GlobalTheory.TateMatrices
