-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.f_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:03:21.256377+00:00
-- url     : https://prove2.me/submissions/024e56e5-01ae-4241-9344-afee0d9ed68b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StagedEstimateHolds
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_rep_cls

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
open PositivityTheory.RgEis
variable {G : Type} [Group G] {P Δ Γ : Subgroup G}
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution {X : Type} {f : G → X} (hf : ∀ γ ∈ Γ, γ ∈ P → ∀ x, f (γ * x) = f x) (y : Γ) (g : G) :
    f (rep (cls y : Cos P Γ) * g) = f (y * g) := by
  obtain ⟨p, hpP, hpΓ, hp⟩ := rep_cls (P := P) y
  rw [hp, mul_assoc, hf p hpΓ hpP]
end GlobalTheory.CompanionTheory.RgEis
