-- Prove2me | solution 1 for GlobalTheory.JointHarm.mfact_mapDomain_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:29:03.35767+00:00
-- url     : https://prove2.me/submissions/27dc8c0b-4a2f-458b-b8b4-ef3279b941a5

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
    (hfg : ∀ x y, f x ≠ g y) (α : σ₁ →₀ ℕ) (β : σ₂ →₀ ℕ) :
    Formalism.A.mfact (α.mapDomain f + β.mapDomain g) = Formalism.A.mfact α * Formalism.A.mfact β := by
  classical
  unfold Formalism.A.mfact
  rw [Finsupp.prod_add_index_of_disjoint, Finsupp.prod_mapDomain_index_inj hf,
    Finsupp.prod_mapDomain_index_inj hg]
  rw [Finsupp.mapDomain_support_of_injective hf, Finsupp.mapDomain_support_of_injective hg,
    Finset.disjoint_left]
  intro t h1 h2
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp h1
  obtain ⟨y, -, hy⟩ := Finset.mem_image.mp h2
  exact hfg x y hy.symm
end GlobalTheory.JointHarm
