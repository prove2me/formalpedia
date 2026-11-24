-- Prove2me | solution 1 for GlobalTheory.PairOp.sumOp_dia
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:38.51792+00:00
-- url     : https://prove2.me/submissions/b901a8cd-0db8-4e7e-b309-a6f6dc2cd2ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Theorems.Thm_GlobalTheory_LatPair_sumOp_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
open GlobalTheory GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.PairOp
theorem _root_.solution (S : Pair k n → Finset (Pair k n)) (w : Pair k n → Pair k n → ℂ) (c : 𝓀[k]ˣ)
    (hS : ∀ P Q, Q ∈ S P ↔ c • Q ∈ S (c • P)) (hw : ∀ P, ∀ Q ∈ S P, w (c • P) (c • Q) = w P Q) :
    (sumOp S w * dia c : Module.End ℂ (Form k n M)) = dia c * sumOp S w := by
  refine LinearMap.ext fun φ => funext fun P => ?_
  simp only [Module.End.mul_apply, sumOp_apply, dia_apply]
  refine Finset.sum_nbij' (fun Q => c • Q) (fun Q => c⁻¹ • Q) (fun Q hQ => (hS P Q).mp hQ)
    (fun Q hQ => (hS P (c⁻¹ • Q)).mpr (by rwa [smul_inv_smul])) (fun Q _ => inv_smul_smul c Q)
    (fun Q _ => smul_inv_smul c Q) fun Q hQ => ?_
  rw [hw P Q hQ]
end GlobalTheory.PairOp
