-- Prove2me | solution 1 for GlobalTheory.AnArc.hasSum_coeff_FSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:39:20.964875+00:00
-- url     : https://prove2.me/submissions/05fc9662-4ab8-42a9-8a24-bf056d37a885

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
import Theorems.Thm_GlobalTheory_AnArc_hasSum_term
import Theorems.Thm_GlobalTheory_AnArc_hasSum_level
import Theorems.Thm_GlobalTheory_AnArc_coeff_FSum_mul

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
namespace GlobalTheory.AnArc
theorem _root_.solution (h : th ∈ A.Theta j α) {w : ℂ} (hw : T₀ < w.im) (v : A.V) :
    HasSum (fun n : ℤ => (A.FSum j α th v).coeff n * eTwoPi w ^ n) (A.Sum j α th w v) := by
  simp only [coeff_FSum_mul]
  exact hasSum_level (hasSum_term hT (NeZero.ne j) h hw v)
end GlobalTheory.AnArc
