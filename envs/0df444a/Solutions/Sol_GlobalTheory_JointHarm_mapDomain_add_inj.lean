-- Prove2me | solution 1 for GlobalTheory.JointHarm.mapDomain_add_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:28:50.022565+00:00
-- url     : https://prove2.me/submissions/08e8ee2e-f157-4a6a-827b-073b94b90e2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LowerUnipotentMinors
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JointHarmonicOfHookNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.JointHarm
open MvPolynomial Matrix GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionPolynomials
variable {n p q : ℕ}
open Formalism.E
variable {σ₁ σ₂ τ : Type} {f : σ₁ → τ} {g : σ₂ → τ}
namespace GlobalTheory.JointHarm
theorem _root_.solution (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ x y, f x ≠ g y) {α α' : σ₁ →₀ ℕ} {β β' : σ₂ →₀ ℕ}
    (h : α.mapDomain f + β.mapDomain g = α'.mapDomain f + β'.mapDomain g) : α = α' ∧ β = β' := by
  constructor
  · ext x
    have := DFunLike.congr_fun h (f x)
    have hx : f x ∉ Set.range g := fun ⟨y, hy⟩ => hfg x y hy.symm
    simpa [Finsupp.mapDomain_apply hf, Finsupp.mapDomain_notin_range _ _ hx] using this
  · ext y
    have := DFunLike.congr_fun h (g y)
    have hy : g y ∉ Set.range f := fun ⟨x, hx⟩ => hfg x y hx
    simpa [Finsupp.mapDomain_apply hg, Finsupp.mapDomain_notin_range _ _ hy] using this
end GlobalTheory.JointHarm
