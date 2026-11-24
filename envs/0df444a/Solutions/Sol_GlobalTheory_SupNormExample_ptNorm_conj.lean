-- Prove2me | solution 1 for GlobalTheory.SupNormExample.ptNorm_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:00:05.324537+00:00
-- url     : https://prove2.me/submissions/d63884b9-17f9-46c2-b621-70d88631bd3b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ChosenEqOfAllRules

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SupNormExample
open Formalism.L2.Pj
variable {K : Type} [Field K] {ι : Type} [Fintype ι]
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
namespace GlobalTheory.SupNormExample
theorem _root_.solution (σ : K →+* ℂ) (fn : pts (CAt σ) → ι → ℝ)
    (fn' : pts (CAt ((starRingEnd ℂ).comp σ)) → ι → ℝ) (e : ι → ℕ) (f : Rules pts)
    (y : pts (CAt σ)) (z : pts (CAt ((starRingEnd ℂ).comp σ)))
    (hv : evalAt pts mapR f z = conjAt σ (evalAt pts mapR f y)) (hn : ∀ i, |fn' z i| = |fn y i|) :
    ptNorm pts mapR _ fn' e f z = ptNorm pts mapR σ fn e f y := by
  unfold ptNorm
  rw [hv]
  simp only [hn]
  congr 1
  exact RCLike.norm_conj (K := ℂ) _
end GlobalTheory.SupNormExample
