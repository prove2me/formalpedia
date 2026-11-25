-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.inFlagDomain_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:36:37.187256+00:00
-- url     : https://prove2.me/submissions/d5b5a16e-cf89-49aa-8093-8d0091beed41

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_InFlagDomainOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open Matrix
open scoped ComplexOrder
namespace GlobalTheory.CompanionTheory.Ar.PB
theorem _root_.solution (N : ℕ) : InFlagDomain N N 1 := by
  refine ⟨by simp, ?_⟩
  haveI : IsEmpty {a : Fin N // (a : ℕ) < N - N} := ⟨fun a => by have := a.2; omega⟩
  refine ⟨by ext i; exact isEmptyElim i, fun x hx => ?_⟩
  exact absurd (by ext i; exact isEmptyElim i) hx
end GlobalTheory.CompanionTheory.Ar.PB
