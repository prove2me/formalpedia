-- Prove2me | solution 1 for GlobalTheory.AnArc.differentiable_coeff_FSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:57:41.094478+00:00
-- url     : https://prove2.me/submissions/7725c63c-7a73-40a9-979a-b44d7f76f58f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
import Theorems.Thm_GlobalTheory_AnArc_differentiable_term


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
theorem _root_.solution (h : Differentiable ℂ th) (n : ℤ) :
    Differentiable ℂ fun v => (A.FSum j α th v).coeff n :=
  Differentiable.fun_sum fun μ _ => A.differentiable_term j α h μ
end GlobalTheory.AnArc
