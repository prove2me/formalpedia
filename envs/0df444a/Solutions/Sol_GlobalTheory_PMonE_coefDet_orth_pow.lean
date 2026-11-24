-- Prove2me | solution 1 for GlobalTheory.PMonE.coefDet_orth_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:17:30.329869+00:00
-- url     : https://prove2.me/submissions/234242c0-7119-4f8f-8bf9-487b25033003

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MoorePowSubSelfEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalizedRowCoefficientMatricesDetNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset
variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
namespace GlobalTheory.PMonE
theorem _root_.solution {h : ℕ} (lam : Fin h → F) (hO : Orth p lam) : Orth p (fun j => lam j ^ p) := by
  intro c j hc
  have h1 := hO c j hc
  have e : (∑ i, (c i : F) * lam i) ^ p = ∑ i, (c i : F) * lam i ^ p := by
    rw [← frobenius_def (R := F) p, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_intCast, frobenius_def]
  show ‖lam j ^ p‖ ≤ ‖∑ i, (c i : F) * lam i ^ p‖
  rw [← e, norm_pow, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 p
end GlobalTheory.PMonE
