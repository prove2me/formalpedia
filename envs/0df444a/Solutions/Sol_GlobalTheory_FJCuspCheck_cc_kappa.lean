-- Prove2me | solution 1 for GlobalTheory.FJCuspCheck.cc_kappa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:48:18.503059+00:00
-- url     : https://prove2.me/submissions/0a3633c5-71b1-4d4c-be25-d3f65586b913

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_TransvMemZGam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj.FJ
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.FJCuspCheck
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace GlobalTheory.FJCuspCheck
theorem _root_.solution (X : Data E r) : cc X.κ0 = -X.κ0 := by
  have h := X.ξ0_im
  unfold cc at h ⊢
  rcases X.κ0_xi with h' | h' <;> rw [h'] <;> simp [h, map_ofNat]
end GlobalTheory.FJCuspCheck
