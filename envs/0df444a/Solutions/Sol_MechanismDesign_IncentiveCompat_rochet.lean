-- Prove2me | solution 1 for MechanismDesign.IncentiveCompat.rochet
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T05:06:17.813325+00:00
-- url     : https://prove2.me/submissions/815418f8-c122-4c71-a234-e5851744881b

import Definitions.Def_MechanismDesign_IncentiveCompat_Model
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace RochetCodex
open MechanismDesign.IncentiveCompat
open scoped BigOperators
variable {A Θ : Type*}

def weight (u : A → Θ → ℝ) (q : Θ → A) (x y : Θ) : ℝ :=
  u (q x) y - u (q x) x

def pathValue (u : A → Θ → ℝ) (q : Θ → A) {n : ℕ}
    (f : Fin (n+1) → Θ) : ℝ :=
  ∑ i : Fin n, weight u q (f i.castSucc) (f i.succ)

theorem pathValue_snoc (u : A → Θ → ℝ) (q : Θ → A) {n : ℕ}
    (f : Fin (n+1) → Θ) (y : Θ) :
    pathValue u q (Fin.snoc f y) = pathValue u q f + weight u q (f (Fin.last n)) y := by
  unfold pathValue
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]

def pathValues (u : A → Θ → ℝ) (q : Θ → A) (a b : Θ) : Set ℝ :=
  {r | ∃ n : ℕ, ∃ f : Fin (n+1) → Θ,
    f 0 = a ∧ f (Fin.last n) = b ∧ pathValue u q f = r}

theorem pathValues_nonempty (u : A → Θ → ℝ) (q : Θ → A) (a b : Θ) :
    (pathValues u q a b).Nonempty := by
  refine ⟨weight u q a b, 1, ![a,b], ?_, ?_, ?_⟩ <;>
    simp [pathValue]

theorem pathValues_extend (u : A → Θ → ℝ) (q : Θ → A) {a b : Θ}
    {r : ℝ} (hr : r ∈ pathValues u q a b) (c : Θ) :
    r + weight u q b c ∈ pathValues u q a c := by
  obtain ⟨n,f,h0,hn,hv⟩ := hr
  refine ⟨n+1, Fin.snoc f c, ?_, ?_, ?_⟩
  · simpa only [Fin.snoc_apply_zero] using h0
  · exact Fin.snoc_last _ _
  · rw [pathValue_snoc, hn, hv]

theorem pathValues_bdd (u : A → Θ → ℝ) (q : Θ → A)
    (hcm : CyclicallyMonotone u q) (a b : Θ) :
    BddAbove (pathValues u q a b) := by
  refine ⟨-weight u q b a, ?_⟩
  intro r hr
  obtain ⟨n,f,h0,hn,hv⟩ := hr
  have hclosed : (Fin.snoc f a : Fin (n+2) → Θ) 0 =
      (Fin.snoc f a : Fin (n+2) → Θ) (Fin.last (n+1)) := by
    simpa only [Fin.snoc_apply_zero, Fin.snoc_last] using h0
  have h := hcm (n+1) (Fin.snoc f a) hclosed
  change pathValue u q (Fin.snoc f a) ≤ 0 at h
  rw [pathValue_snoc, hn, hv] at h
  linarith

theorem potential_step (u : A → Θ → ℝ) (q : Θ → A)
    (hcm : CyclicallyMonotone u q) (a x y : Θ) :
    sSup (pathValues u q a x) + weight u q x y ≤ sSup (pathValues u q a y) := by
  have hbound : sSup (pathValues u q a x) ≤ sSup (pathValues u q a y) - weight u q x y := by
    apply csSup_le (pathValues_nonempty u q a x)
    intro r hr
    have h := le_csSup (pathValues_bdd u q hcm a y) (pathValues_extend u q hr y)
    linarith
  linarith

theorem implementable_of_cyclic [Nonempty Θ] (u : A → Θ → ℝ) (q : Θ → A)
    (hcm : CyclicallyMonotone u q) : Implementable u q := by
  classical
  let a : Θ := Classical.choice inferInstance
  let U : Θ → ℝ := fun x => sSup (pathValues u q a x)
  refine ⟨fun x => u (q x) x - U x, ?_⟩
  intro x y
  have h := potential_step u q hcm a y x
  dsimp [U, weight] at *
  linarith

theorem cyclic_of_implementable (u : A → Θ → ℝ) (q : Θ → A)
    (hic : Implementable u q) : CyclicallyMonotone u q := by
  obtain ⟨t,ht⟩ := hic
  let U : Θ → ℝ := fun x => u (q x) x - t x
  intro n f hf
  have hedge (x y : Θ) : weight u q x y ≤ U y - U x := by
    have h := ht y x
    dsimp [IsIC, U, weight] at *
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun (i : Fin n) _ => hedge (f i.castSucc) (f i.succ))
  have htelescope : (∑ i : Fin n, (U (f i.succ) - U (f i.castSucc))) =
      U (f (Fin.last n)) - U (f 0) := by
    rw [Finset.sum_sub_distrib]
    have hfirst := Fin.sum_univ_succ (fun i : Fin (n+1) => U (f i))
    have hlast := Fin.sum_univ_castSucc (fun i : Fin (n+1) => U (f i))
    linarith
  rw [htelescope, hf, sub_self] at hsum
  exact hsum

end RochetCodex

open MechanismDesign.IncentiveCompat
theorem solution {A Θ : Type*} [Nonempty Θ] (u : A → Θ → ℝ) (q : Θ → A) :
    Implementable u q ↔ CyclicallyMonotone u q :=
  ⟨RochetCodex.cyclic_of_implementable u q, RochetCodex.implementable_of_cyclic u q⟩
