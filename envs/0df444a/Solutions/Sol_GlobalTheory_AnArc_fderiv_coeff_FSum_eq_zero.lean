-- Prove2me | solution 1 for GlobalTheory.AnArc.fderiv_coeff_FSum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:57:47.271334+00:00
-- url     : https://prove2.me/submissions/ba165f5f-5138-4428-9e96-e517d7e5df22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
import Theorems.Thm_GlobalTheory_AnArc_coeff_FSum_eq_zero


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
theorem _root_.solution {n : ℤ} (hn : n < -A.be α α) (v : A.V) :
    fderiv ℂ (fun v => (A.FSum j α th v).coeff n) v = 0 := by
  simp only [A.coeff_FSum_eq_zero j α th _ hn, fderiv_fun_const, Pi.zero_apply]
end GlobalTheory.AnArc
