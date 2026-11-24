-- Prove2me | solution 1 for GlobalTheory.FunObj.integral_pi_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:59:13.632852+00:00
-- url     : https://prove2.me/submissions/de6b0626-405e-4114-9f1a-7452e16eb4b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorPureTensorEqProdContr
import Theorems.Thm_GlobalTheory_FunObj_integral_pi_succ_succ
import Theorems.Thm_GlobalTheory_FunObj_prod_even_succ_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.LocFlat
namespace GlobalTheory.FunObj
theorem _root_.solution (q : ℕ) : ∀ (E : ℕ → Type) [∀ j, MeasurableSpace (E j)] (μ : ∀ j, Measure (E j))
    [∀ j, SigmaFinite (μ j)] (H : ∀ j : Fin (2 * q), E j → E (j + 1) → ℂ) (L : E (2 * q) → ℂ),
    ∫ w : ∀ j : Fin (2 * q + 1), E j, (∏ j : Fin (2 * q), if Even j.1 then H j (w ⟨j, by omega⟩) (w ⟨j + 1, by omega⟩) else 1) *
      L (w ⟨2 * q, by omega⟩) ∂(Measure.pi fun j : Fin (2 * q + 1) => μ j) =
    (∏ j : Fin (2 * q), if Even j.1 then ∫ p : E j × E (j + 1), H j p.1 p.2 ∂((μ j).prod (μ (j + 1))) else 1) *
      ∫ u, L u ∂(μ (2 * q)) := by
  induction q with
  | zero =>
    intro E _ μ _ H L
    have := integral_fintype_prod_eq_prod (μ := fun j : Fin 1 => μ j) (E := fun j : Fin 1 => E j)
      (fun j : Fin 1 => (Fin.cons L finZeroElim : ∀ j : Fin 1, E j → ℂ) j)
    simpa using this
  | succ q ih =>
    intro E _ μ _ H L
    have h := ih (fun j => E (j + 2)) (fun j => μ (j + 2)) (fun j => H (j.succ.succ : Fin (2 * q + 2))) L
    refine (integral_pi_succ_succ (n := 2 * q + 1) (E := fun j => E j) (fun j => μ j) _).trans ?_
    refine Eq.trans ?_ (congrArg (· * _) (prod_even_succ_succ (2 * q) _).symm)
    rw [mul_assoc]
    refine Eq.trans ?_ (congrArg (_ * ·) h)
    refine Eq.trans ?_ (integral_prod_mul _ _)
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    refine (congrArg (· * _) (prod_even_succ_succ (2 * q) _)).trans ?_
    rw [mul_assoc]
    rfl
end GlobalTheory.FunObj
