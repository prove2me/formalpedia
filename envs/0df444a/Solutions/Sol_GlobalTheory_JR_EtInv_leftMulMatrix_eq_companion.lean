-- Prove2me | solution 1 for GlobalTheory.JR.EtInv.leftMulMatrix_eq_companion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:58:43.806269+00:00
-- url     : https://prove2.me/submissions/a0be55e4-0eb1-4414-ad1a-ec9f09821227

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit

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
    (hr : τ ^ r + ∑ i, p i • τ ^ (i : ℕ) = 0) : Algebra.leftMulMatrix bb τ = companion p := by
  classical
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, hb, ← pow_succ']
  simp only [companion, Matrix.of_apply]
  by_cases hj : (j : ℕ) + 1 = r
  · rw [if_pos hj, hj, eq_neg_of_add_eq_zero_left hr]
    have : ∑ k, p k • τ ^ (k : ℕ) = ∑ k, p k • bb k := by simp [hb]
    rw [this, map_neg, Finsupp.neg_apply, bb.repr_sum_self]
  · rw [if_neg hj]
    have hlt : (j : ℕ) + 1 < r := by omega
    have : τ ^ ((j : ℕ) + 1) = bb ⟨(j : ℕ) + 1, hlt⟩ := by rw [hb]
    rw [this, bb.repr_self, Finsupp.single_apply]
    by_cases hi : (i : ℕ) = (j : ℕ) + 1
    · rw [if_pos (Fin.ext hi.symm), if_pos hi]
    · rw [if_neg (fun h => hi (by rw [← h])), if_neg hi]
end GlobalTheory.JR.EtInv
