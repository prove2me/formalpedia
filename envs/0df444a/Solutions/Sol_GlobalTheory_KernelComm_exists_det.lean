-- Prove2me | solution 1 for GlobalTheory.KernelComm.exists_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:13:47.354488+00:00
-- url     : https://prove2.me/submissions/57309308-d3d4-4c66-902b-da45d31ef4d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity
import Theorems.Thm_GlobalTheory_LatPair_stdPair_hasVal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity GlobalTheory.PairOp
noncomputable section
open GlobalTheory GlobalTheory.KernelComm
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}
variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
namespace GlobalTheory.KernelComm
theorem _root_.solution (q : Unif k) (P : Pair k n) :
    ∃ d : GL n k, d • P.ker = P.lat ∧ Matrix.GeneralLinearGroup.det d = q.unit⁻¹ := by
  obtain ⟨i⟩ : Nonempty n := by
    by_contra h
    haveI := not_nonempty_iff.1 h
    exact P.fn_ne (LinearMap.ext fun y => by rw [Subsingleton.elim y 0]; simp)
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq (GL n k) (stdPair k i) P
  have hdet : (Matrix.diagonal (Function.update (1 : n → k) i (q.1 : k))).det = (q.1 : k) := by
    simp [Matrix.det_diagonal, Finset.prod_update_of_mem]
  let d : GL n k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet ▸ q.ne_zero)
  have hd : ∀ (y : n → k) j, (d • y) j = Function.update (1 : n → k) i (q.1 : k) j * y j := fun y j =>
    Matrix.mulVec_diagonal _ _ _
  have h1 : d⁻¹ • (stdPair k i).ker = (stdPair k i).lat := by
    ext y
    rw [mem_smul_iff, inv_inv, Pair.mem_ker, stdPair_hasVal]
    change _ ↔ y ∈ stdLat k n
    rw [mem_stdLat]
    constructor
    · rintro ⟨h, h0⟩ j
      by_cases hj : j = i
      · subst hj
        obtain ⟨s, hs⟩ := q.mem_max_iff.1 ((residue_eq_zero_iff _).1 h0)
        have h2 : (q.1 : k) * y j = q.1 * s := by simpa [hd] using congrArg Subtype.val hs
        rw [mul_left_cancel₀ q.ne_zero h2]
        exact s.2
      · simpa [hd, hj] using h j
    · intro h
      refine ⟨fun j => ?_, (residue_eq_zero_iff _).2 (q.mem_max_iff.2 ⟨⟨y i, h i⟩, Subtype.ext (by simp [hd])⟩)⟩
      by_cases hj : j = i
      · subst hj
        simpa [hd] using mul_mem q.1.2 (h j)
      · simpa [hd, hj] using h j
  refine ⟨a * d⁻¹ * a⁻¹, by rw [Pair.smul_ker, Pair.smul_lat, mul_smul, mul_smul, inv_smul_smul, h1], ?_⟩
  rw [map_mul, map_mul, map_inv, map_inv, mul_inv_cancel_comm, _root_.inv_inj]
  exact Units.ext hdet
end GlobalTheory.KernelComm
