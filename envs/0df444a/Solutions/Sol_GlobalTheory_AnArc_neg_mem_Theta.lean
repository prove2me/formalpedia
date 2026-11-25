-- Prove2me | solution 1 for GlobalTheory.AnArc.neg_mem_Theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:34:21.234331+00:00
-- url     : https://prove2.me/submissions/928a8470-86ad-4e68-90eb-066d1e7b7b82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_H_neg_left
import Theorems.Thm_GlobalTheory_AnArc_H_neg_right
import Theorems.Thm_GlobalTheory_IsAlgebraicIn_comp
import Theorems.Thm_GlobalTheory_IsRigFrame_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) :
    (fun z => th (-z)) ∈ A.Theta j (-α) :=
  ⟨h.1.comp differentiable_id.neg, fun l z => by
    have := h.2 (-l) (-z)
    simp only [ah, A.chi_neg, Submodule.coe_neg, H_neg_left, H_neg_right, neg_neg] at this
    show th (-(z + l)) = _ * _ * th (-z)
    rw [neg_add, this, ah, map_neg, H_neg_left]⟩
end GlobalTheory.AnArc
