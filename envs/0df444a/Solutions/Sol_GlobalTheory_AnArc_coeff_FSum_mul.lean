-- Prove2me | solution 1 for GlobalTheory.AnArc.coeff_FSum_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:57:45.18282+00:00
-- url     : https://prove2.me/submissions/959e2ade-c2d3-4ec7-9147-6bb79ef0abb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
import Theorems.Thm_GlobalTheory_AnArc_coeff_FSum
import Theorems.Thm_GlobalTheory_AnArc_e_mul_intCast


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
variable {A} {T₀ : ℝ} (hT : A.IsConvLine T₀) {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ}
include hT
variable [NeZero j]
omit hT
namespace GlobalTheory.AnArc
theorem _root_.solution (w : ℂ) (v : A.V) (n : ℤ) : (A.FSum j α th v).coeff n * eTwoPi w ^ n =
    ∑ μ ∈ A.level j α n, A.term j α th μ v * eTwoPi (w * A.exponent j α μ) := by
  rw [coeff_FSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [e_mul_intCast, A.mem_level.1 hμ]
end GlobalTheory.AnArc
