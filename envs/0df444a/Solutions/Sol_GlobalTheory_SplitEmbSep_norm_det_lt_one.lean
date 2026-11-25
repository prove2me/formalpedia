-- Prove2me | solution 1 for GlobalTheory.SplitEmbSep.norm_det_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:03:38.174798+00:00
-- url     : https://prove2.me/submissions/969fba35-d0ae-49eb-a5af-b0fe852c2cca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsNormSubEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.SplitEmbSep
open NumberField
namespace GlobalTheory.SplitEmbSep
namespace _root_.GlobalTheory.SplitEmbSep
theorem _root_.solution {C ι : Type*} [NormedField C] [IsUltrametricDist C]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι C) (hM : ∀ i j, ‖M i j‖ ≤ 1) (k : ι)
    (hk : ∀ i, ‖M i k‖ < 1) : ‖M.det‖ < 1 := by
  rw [Matrix.det_apply]
  obtain ⟨σ, -, hle⟩ := IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty
    (Finset.univ_nonempty (α := Equiv.Perm ι))
    (fun σ => Equiv.Perm.sign σ • ∏ i, M (σ i) i)
  refine lt_of_le_of_lt hle ?_
  have hprod : ‖∏ i, M (σ i) i‖ < 1 := by
    rw [norm_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (hk _)
      (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hM _ _))
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
    simpa [hs, Units.smul_def] using hprod
end _root_.GlobalTheory.SplitEmbSep
end GlobalTheory.SplitEmbSep
