-- Prove2me | solution 1 for GlobalTheory.JointHarm.coeff_rename_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:36:55.007185+00:00
-- url     : https://prove2.me/submissions/37ffff20-bc43-4f30-8be1-f8d088b47895

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LowerUnipotentMinors
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JointHarmonicOfHookNorm
import Theorems.Thm_GlobalTheory_JointHarm_mapDomain_add_inj

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
    (hfg : ∀ x y, f x ≠ g y) (α : σ₁ →₀ ℕ) (β : σ₂ →₀ ℕ) (P : MvPolynomial σ₁ ℂ)
    (Q : MvPolynomial σ₂ ℂ) :
    coeff (α.mapDomain f + β.mapDomain g) (rename f P * rename g Q) = coeff α P * coeff β Q := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P P' h h' => simp only [map_add, add_mul, coeff_add, h, h']
  | monomial α' x =>
    induction Q using MvPolynomial.induction_on' with
    | add Q Q' h h' => simp only [map_add, mul_add, coeff_add, h, h']
    | monomial β' y =>
      rw [rename_monomial, rename_monomial, monomial_mul, coeff_monomial, coeff_monomial,
        coeff_monomial]
      by_cases h : α'.mapDomain f + β'.mapDomain g = α.mapDomain f + β.mapDomain g
      · obtain ⟨rfl, rfl⟩ := mapDomain_add_inj hf hg hfg h
        simp
      · rw [if_neg h]
        split_ifs with h1 h2
        · exact absurd (by rw [h1, h2]) h
        all_goals simp
end GlobalTheory.JointHarm
