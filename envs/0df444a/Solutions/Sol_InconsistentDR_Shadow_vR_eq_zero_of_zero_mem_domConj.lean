-- Prove2me | solution 1 for InconsistentDR.Shadow.vR_eq_zero_of_zero_mem_domConj
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T22:55:30.422064+00:00
-- url     : https://prove2.me/submissions/13122e7a-0b48-40cd-82f1-8663e46c5c73

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_FRBSplitting_Weak_Setting
import Definitions.Def_InconsistentDR_Shadow_Operators
import Definitions.Def_InconsistentDR_Shadow_Optimization
import Theorems.Thm_InconsistentDR_Shadow_closure_domConj_eq_closure_ran_subgrad

open scoped InnerProductSpace Topology Pointwise
open Filter ThreeOpSplitting.Convergence MoreauProx.Characterization FRBSplitting.Weak
open InconsistentDR.Shadow

theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f g : X → EReal) (hf : GammaZero f) (hg : GammaZero g)
    (vR : X) (hvR : IsMinNormPt (closure (setR (subgrad f) (subgrad g))) vR)
    (h0 : (0 : X) ∈ domConj f + domConj g) :
    vR = 0 := by
  have h0R : (0 : X) ∈ closure (setR (subgrad f) (subgrad g)) := by
    obtain ⟨a, ha, b, hb, hab⟩ := h0
    have ha' : a ∈ closure (ran (subgrad f)) := by
      rw [← closure_domConj_eq_closure_ran_subgrad f hf]; exact subset_closure ha
    have hb' : b ∈ closure (ran (subgrad g)) := by
      rw [← closure_domConj_eq_closure_ran_subgrad g hg]; exact subset_closure hb
    have := map_mem_closure₂ (f := fun a b : X => a + b) (u := setR (subgrad f) (subgrad g))
      continuous_add ha' hb' (fun a ha b hb => Set.add_mem_add ha hb)
    simpa [hab] using this
  have := hvR.2 0 h0R
  rw [norm_zero] at this
  exact norm_le_zero_iff.mp this
