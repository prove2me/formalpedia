-- Prove2me | solution 1 for GlobalTheory.JHMult.jhMult_exact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:42.882132+00:00
-- url     : https://prove2.me/submissions/49b38242-9dda-4996-b5d4-233ec8064f9c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_JhMultSubAddQuot
import Theorems.Thm_GlobalTheory_JHMult_subMap_mono
import Theorems.Thm_GlobalTheory_JHMult_subComap_mono
import Theorems.Thm_GlobalTheory_JHMult_step_iff
import Theorems.Thm_GlobalTheory_JHMult_occurs_of_finset
import Theorems.Thm_GlobalTheory_JHMult_occurs_zero
import Theorems.Thm_GlobalTheory_JHMult_step_dichotomy
import Theorems.Thm_GlobalTheory_JHMult_occurs_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.JHMult
variable {F G V W V₁ V₂ : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
variable {σ : Representation F G W} {ρ : Representation F G V} {ρ₁ : Representation F G V₁}
  {ρ₂ : Representation F G V₂} (ι : ρ₁.IntertwiningMap ρ) (p : ρ.IntertwiningMap ρ₂)
namespace GlobalTheory.JHMult
theorem _root_.solution (hσ : σ.IsIrreducible) (hι : Function.Injective ι)
    (hp : Function.Surjective p) (h0 : ∀ u, p (ι u) = 0) (hker : ∀ v, p v = 0 → ∃ u, ι u = v) :
    jhMult σ ρ = jhMult σ ρ₁ + jhMult σ ρ₂ := by
  classical
  apply le_antisymm
  · refine iSup₂_le ?_
    rintro r ⟨S, T, h1, h2, h3⟩
    let A : Finset (Fin r) :=
      Finset.univ.filter fun i => Step σ (subComap ι (S i)) (subComap ι (T i))
    have hA := occurs_of_finset (σ := σ) A (fun i => subComap ι (S i)) (fun i => subComap ι (T i))
      (fun i => subComap_mono ι (h1 i)) (fun i j h => subComap_mono ι (h2 i j h))
      (fun i hi => (Finset.mem_filter.1 hi).2)
    have hB := occurs_of_finset (σ := σ) Aᶜ (fun i => subMap p (S i)) (fun i => subMap p (T i))
      (fun i => subMap_mono p (h1 i)) (fun i j h => subMap_mono p (h2 i j h))
      (fun i hi => (step_dichotomy ι p hσ hker (h1 i) (step_iff.1 (h3 i))).resolve_left
        fun h => Finset.mem_compl.1 hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))
    have hc : (r : ℕ∞) = (A.card : ℕ∞) + (Aᶜ.card : ℕ∞) := by
      rw [← Nat.cast_add, Finset.card_add_card_compl, Fintype.card_fin]
    rw [hc]
    exact add_le_add (le_iSup₂_of_le _ hA le_rfl) (le_iSup₂_of_le _ hB le_rfl)
  · refine ENat.biSup_add_biSup_le' ⟨0, occurs_zero _ _⟩ ⟨0, occurs_zero _ _⟩ fun a ha b hb => ?_
    rw [← Nat.cast_add]
    exact le_iSup₂_of_le _ (occurs_add ι p hι hp h0 ha hb) le_rfl
end GlobalTheory.JHMult
