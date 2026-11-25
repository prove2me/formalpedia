-- Prove2me | solution 1 for GlobalTheory.FunObj.flatTensor_pureTensor_eq_prod_contr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:44:19.451377+00:00
-- url     : https://prove2.me/submissions/46611cca-7fd1-4d07-93c4-88e3e881581d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorPureTensorEqProdContr
import Theorems.Thm_GlobalTheory_FunObj_integral_pi_pairs_even
import Theorems.Thm_GlobalTheory_FunObj_prod_pairs_even
import Theorems.Thm_GlobalTheory_FunObj_integral_double_step
import Theorems.Thm_GlobalTheory_FunObj_integral_last_step
import Theorems.Thm_GlobalTheory_FunObj_flatTensor_pureTensor
import Theorems.Thm_GlobalTheory_FunObj_keptCol_eq
import Theorems.Thm_GlobalTheory_FunObj_keptRow_eq
import Theorems.Thm_GlobalTheory_FunObj_stepDatum_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (hm : 2 ≤ G.m), Even G.m → ∀ (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ), (∀ j < G.m - 1, φ (.theta G.m j) ∈ SB _) → ∀ (x : ColArgs G) (y : RowArgs G), flatTensor hs ψ ν (G.lines₂ (oppositePath G.m) φ) x y = (∏ i ∈ Finset.range G.m, φ (.ex i G.m) (y i)ᵀ) * (φ (.theta G.m (G.m - 1)) (lastMap hs (by omega) x)ᵀ * GlobalTheory.StepData.hat ψ ν (-1) (fun u => flCol ψ ν 1 (stepDatum hs φ ⟨G.m - 2, by omega⟩) (fromCols (x (G.m - 2)) (Matrix.of fun r _ => u r))) (x (G.m - 2 + 1) (topLast G (G.m - 2 + 1 + 1)))) * ∏ j : Fin (G.m - 2), if Even j.1 then contr ψ ν (flCol ψ ν ((G.m - 2 - j) / 2 + 1) (stepDatum hs φ ⟨j, by omega⟩)) (flRow ψ ν ((G.m - 2 - (j + 1)) / 2 + 1) (stepDatum hs φ ⟨j + 1, by omega⟩)) (x j, x (j + 1)) else 1 := by
  intro k _ _ _ _ _ _ G hs hm he ψ ν hψ _ hν φ hφ x y
  classical
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hchar : ∀ (s : Finset (Fin (G.m - 1))) (f : Fin (G.m - 1) → k),
      (ψ (-∑ j ∈ s, f j) : ℂ) = ∏ j ∈ s, (ψ (-f j) : ℂ) := fun s f => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, neg_add, AddChar.map_add_eq_mul,
        Circle.coe_mul, ih]
  have he' := Nat.even_iff.1 he
  have ev : ∀ j : Fin (G.m - 2), Even j.1 → Even (G.m - 2 - j) := fun j hj => by
    have := j.2; rw [Nat.even_iff] at hj ⊢; omega
  have od : ∀ j : Fin (G.m - 2), Even j.1 → Odd (G.m - 2 - (j + 1)) := fun j hj => by
    have := j.2; rw [Nat.even_iff] at hj; rw [Nat.odd_iff]; omega
  have el : Even (G.m - 2 - (G.m - 2)) := by simp
  have key := integral_pi_pairs_even hm he
    (fun j => KeptVar (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j)) → k)
    (fun _ => Measure.pi fun _ => ν)
    (fun j a b => if hj : Even j.1 then flatStep ψ ν (stepDatum hs φ ⟨j, by omega⟩) (x j) a *
      flatStep ψ ν (stepDatum hs φ ⟨j + 1, by omega⟩) (x (j + 1)) b *
      (ψ (-∑ r, b (rowIx (od j hj) r) * a (colIx (ev j hj) r)) : ℂ) else 1)
    (fun a => flatStep ψ ν (stepDatum hs φ ⟨G.m - 2, by omega⟩) (x (G.m - 2)) a *
      (ψ (-∑ r, x (G.m - 2 + 1) (topLast G (G.m - 2 + 1 + 1)) r * a (colIx el r)) : ℂ))
  rw [(flatTensor_pureTensor hs ν (by omega) hψ φ hφ x y).2.2, mul_assoc, mul_assoc, mul_assoc]
  congr 2
  rw [mul_comm]
  refine Eq.trans ?_ (key.trans ?_)
  · unfold keptVol
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have h1 : (ψ (-pairPhase x w) : ℂ) = ∏ j : Fin (G.m - 1),
        if Even (G.m - 2 - j) then (ψ (-∑ r, keptRow x w (j + 1) r * keptCol w j r) : ℂ) else 1 := by
      rw [pairPhase, hchar]
      refine Finset.prod_congr rfl fun j _ => ?_
      split_ifs <;> simp
    simp only
    rw [contractIntegrand, h1, prod_pairs_even hm he]
    congr 1
    · refine Finset.prod_congr rfl fun j _ => if_ctx_congr Iff.rfl (fun hj => ?_) fun _ => rfl
      rw [dif_pos hj]
      congr 4
      refine Finset.sum_congr rfl fun r _ => ?_
      exact congrArg₂ (· * ·) (keptRow_eq x w ⟨j + 1, by omega⟩ (od j hj) r) (keptCol_eq w ⟨j, by omega⟩ (ev j hj) r)
    · congr 4
      refine Finset.sum_congr rfl fun r _ => ?_
      exact congrArg₂ (· * ·) (dif_neg (by simp only; omega)) (keptCol_eq w ⟨G.m - 2, by omega⟩ el r)
  · congr 1
    · refine Finset.prod_congr rfl fun j _ => if_ctx_congr Iff.rfl (fun hj => ?_) fun _ => rfl
      simp only [dif_pos hj]
      convert integral_double_step ν hψ (ev j hj) (od j hj)
        (stepDatum_mem_SB hs ⟨j, by omega⟩ (hφ j (by omega)))
        (stepDatum_mem_SB hs ⟨j + 1, by omega⟩ (hφ (j + 1) (by omega))) (x j) (x (j + 1))
    · have h := integral_last_step (ψ := ψ) ν el (stepDatum hs φ ⟨G.m - 2, by omega⟩) (x (G.m - 2))
        (x (G.m - 2 + 1) (topLast G (G.m - 2 + 1 + 1)))
      rw [show (G.m - 2 - (G.m - 2)) / 2 + 1 = 1 by omega] at h
      convert h
end GlobalTheory.FunObj
