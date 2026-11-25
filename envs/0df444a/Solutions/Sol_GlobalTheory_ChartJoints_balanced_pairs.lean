-- Prove2me | solution 1 for GlobalTheory.ChartJoints.balanced_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:57:47.402162+00:00
-- url     : https://prove2.me/submissions/abf9b6d4-9838-4567-ad32-05ef9bbcdc2f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_BalancedPairs
import Theorems.Thm_GlobalTheory_ChartJoints_emb_bar
import Theorems.Thm_Formalism_L2_Pj_embK_coe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.ChartJoints
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.ChartJoints
theorem _root_.solution (H : Host E) {l : Level H} (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S]
    (τ τ' : E →+* ℂ) (v : S)
    (hv : ∀ a : 𝓞 E, algebraMap c.F S (embK c τ a) * v = algebraMap c.F S (embK c τ' (H.bar a)) * v)
    (hne : τ ≠ ComplexEmbedding.conjugate τ') : v = 0 := by
  have : ∃ a : 𝓞 E, embK c τ a ≠ embK c τ' (H.bar a) := by
    by_contra hcon
    push_neg at hcon
    apply hne
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    ext a
    have := congrArg (fun z : c.F => (z : ℂ)) (hcon a)
    simp only [embK_coe] at this
    rw [emb_bar] at this
    exact this
  obtain ⟨a, ha⟩ := this
  have hu : IsUnit (algebraMap c.F S (embK c τ a - embK c τ' (H.bar a))) :=
    (IsUnit.mk0 _ (sub_ne_zero.2 ha)).map _
  apply hu.mul_left_cancel
  rw [map_sub, sub_mul, hv a, sub_self, mul_zero]
end GlobalTheory.ChartJoints
