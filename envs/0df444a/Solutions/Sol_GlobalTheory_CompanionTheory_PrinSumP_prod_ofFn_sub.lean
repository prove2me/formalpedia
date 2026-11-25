-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PrinSumP.prod_ofFn_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:51:59.953827+00:00
-- url     : https://prove2.me/submissions/690679dc-c725-489d-846c-0d9c43c6ed6e

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PrincipalSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrinSumP
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (capEntry cminor)
open Formalism.REAL (Tm qminor qdet)
variable {A : Type*} [Ring A] [Algebra ℂ A]
namespace GlobalTheory.CompanionTheory.PrinSumP
theorem _root_.solution : ∀ (m : ℕ) (f g : Fin (m + 1) → A) (d : Fin (m + 1)),
    (∀ j, j ≠ d → f j = g j) → f d = g d + 1 →
    (List.ofFn f).prod - (List.ofFn g).prod = (List.ofFn (f ∘ d.succAbove)).prod := by
  intro m
  induction m with
  | zero =>
    intro f g d _ hd
    have hd0 : d = 0 := Fin.fin_one_eq_zero d
    subst hd0
    simp [hd]
  | succ m ih =>
    intro f g d h hd
    rw [List.ofFn_succ (f := f), List.ofFn_succ (f := g), List.prod_cons, List.prod_cons]
    induction d using Fin.cases with
    | zero =>
      have ht : (fun i : Fin (m + 1) => f i.succ) = fun i => g i.succ :=
        funext fun i => h _ (Fin.succ_ne_zero i)
      rw [ht, hd, add_mul, one_mul, add_sub_cancel_left]
      congr 2
      funext i
      simp [ht, congrFun ht i]
    | succ e =>
      have h0 : f 0 = g 0 := h 0 (Fin.succ_ne_zero e).symm
      have key := ih (fun i => f i.succ) (fun i => g i.succ) e
        (fun j hj => h _ (fun hh => hj (Fin.succ_injective _ hh))) hd
      rw [← h0, ← mul_sub, key, List.ofFn_succ, List.prod_cons]
      congr 2
      simp [Function.comp_def, Fin.succ_succAbove_succ]
end GlobalTheory.CompanionTheory.PrinSumP
