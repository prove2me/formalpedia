-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TfLoc.Iw.not_val_lt_val_aut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:20:54.94253+00:00
-- url     : https://prove2.me/submissions/14d85dcb-61d0-4d56-9af1-512df52e563d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_val_aut_strictMono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel PositivityTheory.Rg.Tf.Loc Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TfLoc GlobalTheory.CompanionTheory.TfLoc.Iw
variable {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E]
namespace GlobalTheory.CompanionTheory.TfLoc.Iw
theorem _root_.solution [IsGalois k E] (τ : E ≃ₐ[k] E) (y : E) :
    ¬ valuation E y < valuation E (τ y) := by
  intro h
  have hp : ∀ i : ℕ, (τ ^ (i + 1)) y = τ ((τ ^ i) y) := fun i => by
    rw [pow_succ']
    rfl
  have hstep : ∀ i : ℕ, valuation E ((τ ^ i) y) < valuation E ((τ ^ (i + 1)) y) := by
    intro i
    induction i with
    | zero => simpa using h
    | succ i ih =>
      have := val_aut_strictMono τ ih
      rw [hp (i + 1)]
      conv_lhs => rw [hp i]
      exact this
  have hlt : ∀ i : ℕ, valuation E y < valuation E ((τ ^ (i + 1)) y) := by
    intro i
    induction i with
    | zero => simpa using h
    | succ i ih => exact ih.trans (hstep (i + 1))
  have hpos : 0 < orderOf τ := orderOf_pos τ
  have := hlt (orderOf τ - 1)
  rw [Nat.sub_add_cancel hpos, pow_orderOf_eq_one] at this
  simp at this
end GlobalTheory.CompanionTheory.TfLoc.Iw
