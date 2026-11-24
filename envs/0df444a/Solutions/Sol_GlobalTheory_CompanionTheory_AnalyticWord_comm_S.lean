-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnalyticWord.comm_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:17:18.277163+00:00
-- url     : https://prove2.me/submissions/c9158ed9-3776-4851-9573-b8cd963d03fe

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SkewAdjointCasimirSpectral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AnalyticWord
variable {V H : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type}
namespace GlobalTheory.CompanionTheory.AnalyticWord
theorem _root_.solution (Z : ι → Module.End ℂ V) [Fintype ι] (K : Finset ι) (c : ι → ι → ι → ℂ)
    (hcomm : ∀ κ i, Z κ * Z i - Z i * Z κ = ∑ l, c κ i l • Z l) (i : ι) :
    (∑ κ ∈ K, Z κ * Z κ) * Z i - Z i * (∑ κ ∈ K, Z κ * Z κ) =
      ∑ κ ∈ K, ∑ n, c κ i n • (Z κ * Z n + Z n * Z κ) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun κ _ => ?_
  have e : Z κ * Z κ * Z i - Z i * (Z κ * Z κ) =
      Z κ * (Z κ * Z i - Z i * Z κ) + (Z κ * Z i - Z i * Z κ) * Z κ := by
    simp only [mul_sub, sub_mul, mul_assoc]
    abel
  rw [e, hcomm, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, smul_add]
end GlobalTheory.CompanionTheory.AnalyticWord
