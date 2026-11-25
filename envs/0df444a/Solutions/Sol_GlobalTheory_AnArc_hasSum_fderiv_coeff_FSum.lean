-- Prove2me | solution 1 for GlobalTheory.AnArc.hasSum_fderiv_coeff_FSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:21:36.402174+00:00
-- url     : https://prove2.me/submissions/4125bb34-dd73-4ce8-a5a2-597a7ebef770

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
import Theorems.Thm_GlobalTheory_AnArc_hasSum_fderiv_term
import Theorems.Thm_GlobalTheory_AnArc_hasSum_level
import Theorems.Thm_GlobalTheory_AnArc_fderiv_coeff_FSum
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
namespace GlobalTheory.AnArc
theorem _root_.solution (h : th ∈ A.Theta j α) {w : ℂ} (hw : T₀ < w.im) (v v₀ : A.V) :
    HasSum (fun n : ℤ => fderiv ℂ (fun v => (A.FSum j α th v).coeff n) v v₀ * eTwoPi w ^ n)
      (fderiv ℂ (A.Sum j α th w) v v₀) := by
  refine (hasSum_level (j := j) (α := α) (hasSum_fderiv_term hT (NeZero.ne j) h hw v v₀)).congr_fun fun n => ?_
  rw [fderiv_coeff_FSum h.1, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [e_mul_intCast, A.mem_level.1 hμ]
end GlobalTheory.AnArc
