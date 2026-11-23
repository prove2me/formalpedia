-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:54.426402+00:00
-- url     : https://prove2.me/submissions/f41b2ff9-55ce-4711-95cd-9d8abe13c43c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_prod_emb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
variable (F : Type) [Field F] [NumberField F]
variable {F}
open NumberField Complex
open scoped nonZeroDivisors ContDiff
variable (F : Type) [Field F] [NumberField F]
variable {F}
namespace GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
theorem _root_.solution [IsTotallyReal F] {k : ℕ} (hk : Even k)
    (σ : ℂ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (ε : (𝓞 F)ˣ) (a b : F) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm k σ z (((ε : 𝓞 F) : F) * a, ((ε : 𝓞 F) : F) * b) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm k σ z (a, b) := by
  have hprod : ∏ τ, _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latPt z (((ε : 𝓞 F) : F) * a, ((ε : 𝓞 F) : F) * b) τ =
      ((Algebra.norm ℚ ((ε : 𝓞 F) : F) : ℚ) : ℂ) * ∏ τ, _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latPt z (a, b) τ := by
    rw [← _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.prod_emb, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latPt, map_mul]
    push_cast
    ring
  have hn : |Algebra.norm ℚ ((ε : 𝓞 F) : F)| = 1 := NumberField.Units.norm F ε
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm
  rw [hprod]
  rcases (abs_eq zero_le_one).mp hn with h | h <;> rw [h] <;>
    simp [hk.neg_pow, inv_neg, norm_neg]
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
end GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
