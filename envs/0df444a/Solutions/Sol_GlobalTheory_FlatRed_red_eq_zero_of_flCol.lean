-- Prove2me | solution 1 for GlobalTheory.FlatRed.red_eq_zero_of_flCol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:56:26.846844+00:00
-- url     : https://prove2.me/submissions/f2446d17-ba61-4b45-ac12-73437dfc8af4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEqZeroOfFlatMapColumnZero
import Theorems.Thm_GlobalTheory_FlatRed_integral_pi_subtype_iff
import Theorems.Thm_GlobalTheory_FlatRed_fill_eq
import Theorems.Thm_GlobalTheory_FlatRed_ch_add_colAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open GlobalTheory GlobalTheory.FlatRed
open GlobalTheory.FlatFactor GlobalTheory.LocFlat
namespace GlobalTheory.FlatRed
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ), c = 2 * ρ → ∀ Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ, (∀ x, GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ x = 0) → ∀ t, GlobalTheory.FlatFactor.red ν (GlobalTheory.FlatFactor.evAll n n' c ρ) (GlobalTheory.FlatFactor.itFree n n' c ρ) (basePt c (0 : Matrix n n' k)) (fun t => (ψ (-ch t) : ℂ) * Φ t) t = 0 := by
  intro k _ _ _ _ _ _ ψ ν n n' _ _ _ _ c ρ hc Φ hΦ t
  have h : ρ < c + 1 := by omega
  rw [← hΦ (readPart ρ h t)]
  unfold red flCol opE
  refine integral_pi_subtype_iff (mem_itFree ρ) ν _ _ fun a => ?_
  beta_reduce
  rw [fill_eq ρ h t a, ch_add_colAt, mul_comm]
end GlobalTheory.FlatRed
