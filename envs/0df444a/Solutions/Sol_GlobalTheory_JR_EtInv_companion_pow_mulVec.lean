-- Prove2me | solution 1 for GlobalTheory.JR.EtInv.companion_pow_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:19:54.962987+00:00
-- url     : https://prove2.me/submissions/580e8cb3-e46e-4554-b423-8422b1dba202

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit
import Theorems.Thm_GlobalTheory_JR_EtInv_leftMulMatrix_eq_companion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtInv
variable {F K : Type} [Field F] [CommRing K] [Algebra F K] {r : ℕ} {τ : K} {p : Fin r → F}
namespace GlobalTheory.JR.EtInv
theorem _root_.solution (bb : Module.Basis (Fin r) F K) (hb : ∀ i, bb i = τ ^ (i : ℕ))
    (hr : τ ^ r + ∑ i, p i • τ ^ (i : ℕ) = 0) (n : ℕ) :
    (companion p ^ n) *ᵥ (fun i : Fin r => if (i : ℕ) = 0 then (1 : F) else 0) = ⇑(bb.repr (τ ^ n)) := by
  classical
  induction n with
  | zero =>
    rw [pow_zero, Matrix.one_mulVec, pow_zero]
    funext i
    have hr0 : 0 < r := lt_of_le_of_lt (Nat.zero_le _) i.2
    have h1 : (1 : K) = bb ⟨0, hr0⟩ := by rw [hb]; simp
    rw [h1, bb.repr_self, Finsupp.single_apply]
    by_cases hi : (i : ℕ) = 0
    · rw [if_pos hi, if_pos (Fin.ext hi.symm)]
    · rw [if_neg hi, if_neg (fun h => hi (by rw [← h]))]
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, ← leftMulMatrix_eq_companion bb hb hr,
      Algebra.leftMulMatrix_apply, LinearMap.toMatrix_mulVec_repr, pow_succ']
    rfl
end GlobalTheory.JR.EtInv
