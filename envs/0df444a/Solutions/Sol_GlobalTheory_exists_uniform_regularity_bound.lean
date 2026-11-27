-- Prove2me | solution 1 for GlobalTheory.exists_uniform_regularity_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:16.984227+00:00
-- url     : https://prove2.me/submissions/c41ffb80-f4c4-4715-a6fb-90a6d937c4ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
import Theorems.Thm_GlobalTheory_RegBound_bound_infinite
import Theorems.Thm_GlobalTheory_RegBound_contr_comp
import Theorems.Thm_GlobalTheory_RegBound_contr_map
import Theorems.Thm_GlobalTheory_RegBound_finrank_extSub
import Theorems.Thm_GlobalTheory_RegBound_piece_extIdeal
import Theorems.Thm_GlobalTheory_RegBound_mem_genIn_of_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory
open RegBound
namespace GlobalTheory
theorem _root_.solution :
    ∀ (σ : Type) [Finite σ] (Q : Polynomial ℚ), ∃ d₀ : ℕ, ∀ (K : Type) [Field K] (I : Ideal (MvPolynomial σ K)), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → (∀ F, (∀ i, MvPolynomial.X i * F ∈ I) → F ∈ I) → (∀ᶠ e in Filter.atTop, (Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e ⊓ I.restrictScalars K) : ℚ) = Q.eval (e : ℚ)) → ∀ e ≥ d₀, (Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e ⊓ I.restrictScalars K) : ℚ) = Q.eval (e : ℚ) ∧ ∀ F ∈ I, F.IsHomogeneous e → F ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d₀} := by
  intro σ _ Q
  obtain ⟨d, hd⟩ := bound_infinite σ (nmon σ 1) fun e => Q.eval (e : ℚ)
  refine ⟨d, fun K _ I hI hsat hq => ?_⟩
  haveI : Infinite (AlgebraicClosure K) := IsAlgClosed.instInfinite
  have hdim : ∀ e, finrank (AlgebraicClosure K) (piece (extIdeal (AlgebraicClosure K) I) e) =
      finrank K (piece I e) := fun e => by rw [piece_extIdeal, finrank_extSub]
  have h := hd (AlgebraicClosure K) (extIdeal (AlgebraicClosure K) I)
    (fun F hF e φ => by rw [contr_comp]; exact hI _ (hF φ) e)
    (fun F hF φ => hsat _ fun i => by rw [← contr_X_mul]; exact hF i φ)
    (Nat.le_add_left _ _) (by simpa only [hdim] using hq)
  simp only [hdim] at h
  intro e he
  refine ⟨(h e he).1, ?_⟩
  induction e, he using Nat.le_induction with
  | base => exact fun F hF hFe => Ideal.subset_span ⟨hF, hFe⟩
  | succ n hn ih =>
    intro F hF hFe
    refine (Ideal.span_le.2 fun G hG => ih G hG.1 hG.2 : genIn I n ≤ genIn I d) ?_
    refine mem_genIn_of_map (L := AlgebraicClosure K) ((h n hn).2 _ (fun φ => ?_) (hFe.map _))
    rw [contr_map, smul_eq_C_mul]
    exact I.mul_mem_left _ hF
end GlobalTheory
