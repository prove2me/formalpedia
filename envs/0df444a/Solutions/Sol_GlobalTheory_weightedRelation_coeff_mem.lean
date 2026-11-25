-- Prove2me | solution 1 for GlobalTheory.weightedRelation_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:52:35.163992+00:00
-- url     : https://prove2.me/submissions/2afb374b-f019-4003-be01-8f8fb68ab1ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffMemSpanOfWeightedHomogeneousRelationQuasiRe
import Theorems.Thm_GlobalTheory_weightedRelation_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory
open MvPolynomial
variable {R : Type} [CommRing R] {n : ℕ}
namespace GlobalTheory
theorem _root_.solution (z : Fin n → R) (w : Fin n → ℕ) (hw : ∀ i, 1 ≤ w i)
    (hz : IsQuasiRegularSeq R z) (D : ℕ) (j : ℕ) : ∀ (k : ℕ) (H : MvPolynomial (Fin n) R),
    (∀ β, H.coeff β ≠ 0 → k ≤ β.degree ∧ D ≤ Finsupp.weight w β) →
    MvPolynomial.eval z H = 0 → ∀ α : Fin n →₀ ℕ, α.degree = k + j →
    Finsupp.weight w α = D → H.coeff α ∈ Ideal.span (Set.range z) := by
  induction j with
  | zero =>
    intro k H hH h0 α hα _
    exact (weightedRelation_step z w hw hz D k H hH h0).1 α hα
  | succ j ih =>
    intro k H hH h0 α hα hαw
    obtain ⟨-, H', h1, h2, h3⟩ := weightedRelation_step z w hw hz D k H hH h0
    rw [← h3 α hαw (by omega)]
    exact ih (k + 1) H' h1 h2 α (by omega) hαw
end GlobalTheory
