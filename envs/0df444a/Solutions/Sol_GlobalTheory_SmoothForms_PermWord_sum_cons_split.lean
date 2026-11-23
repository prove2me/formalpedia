-- Prove2me | solution 1 for GlobalTheory.SmoothForms.PermWord.sum_cons_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:16.67472+00:00
-- url     : https://prove2.me/submissions/2fae6707-510d-45b0-a05f-dbab9760e3f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.PermWord
variable {S : Type} [CommRing S] {n : ℕ}
namespace GlobalTheory.SmoothForms.PermWord
theorem _root_.solution {d : ℕ} (f : (Fin (d + 1) → Fin n) → S) :
    ∑ K, f K = ∑ K : Fin d → Fin n, ∑ j : Fin n, f (Fin.cons j K) := by
  rw [Finset.sum_comm, ← (Fin.consEquiv fun _ : Fin (d + 1) => Fin n).sum_comp, Fintype.sum_prod_type]
  rfl
end GlobalTheory.SmoothForms.PermWord
