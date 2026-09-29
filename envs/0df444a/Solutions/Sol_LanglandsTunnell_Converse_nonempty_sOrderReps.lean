-- Prove2me | solution 1 for LanglandsTunnell.Converse.nonempty_sOrderReps
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/2b4cd14e-5c0c-5968-8d47-3b2befb56b37

import Definitions.Def_LanglandsTunnell_JLData
import Theorems.Thm_LanglandsTunnell_Converse_exists_ne_zero_valuation_eq_exp_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_nonempty_sOrderReps

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.Converse

private theorem sunitRep_valued_localOf {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (α : Kˣ) :
    Valued.v ((localOf K v α : (v.adicCompletion K)ˣ) : v.adicCompletion K) = v.valuation K (α : K) := by
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := K) (v := v) (α : K)

theorem solution (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) : Nonempty (SOrderReps K S) := by
  refine ⟨⟨fun n => Units.mk0 (Classical.choose (exists_ne_zero_valuation_eq_exp_neg K S n))
    (Classical.choose_spec (exists_ne_zero_valuation_eq_exp_neg K S n)).1, fun n v => ?_⟩⟩
  rw [sunitRep_valued_localOf]
  exact (Classical.choose_spec (exists_ne_zero_valuation_eq_exp_neg K S n)).2 v

end S_LanglandsTunnell_Converse_nonempty_sOrderReps
end P2MW
export P2MW.S_LanglandsTunnell_Converse_nonempty_sOrderReps (solution)
