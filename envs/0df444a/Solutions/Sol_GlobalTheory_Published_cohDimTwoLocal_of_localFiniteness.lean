-- Prove2me | solution 1 for GlobalTheory.Published.cohDimTwoLocal_of_localFiniteness
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:10:19.633424+00:00
-- url     : https://prove2.me/submissions/d259aa09-0029-4bdc-8418-87e162cace71

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__CohDimTwoLocalOfLocalFiniteness_b2c2e165733ad400

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open GlobalTheory GlobalTheory.Published
namespace GlobalTheory.Published
theorem _root_.solution (h : LocalFiniteness) : CohDimTwoLocal := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ v A rho hA hc n hn
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    exact Module.subsingleton (ZMod (l ^ 0)) _
  · exact (h F Ω l r M A rho v hr hA hc).2.2.2 n hn
end GlobalTheory.Published
