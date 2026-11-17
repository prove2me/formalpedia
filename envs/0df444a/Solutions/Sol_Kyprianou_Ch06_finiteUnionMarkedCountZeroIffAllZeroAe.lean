-- Prove2me | solution 1 for Kyprianou.Ch06.finiteUnionMarkedCountZeroIffAllZeroAe
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:27:12.515849+00:00
-- url     : https://prove2.me/submissions/d2799a51-f2c1-404d-9cc2-50b51d39129c

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.finiteUnionMarkedCountZeroIffAllZeroAe
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (m : Nat) (B : Fin m → Set E) :
    ∀ᵐ omega ∂P, ∀ t : NNReal,
      (∀ i : Fin m, N omega t (B i) = 0) ↔
      N omega t (⋃ i : Fin m, B i) = 0 := by
  filter_upwards [hPPP.2.1] with omega h t
  have hadd := h.2.1 t
  -- union of two sets: zero iff both zero
  have hU : ∀ X Y : Set E, (N omega t X = 0 ∧ N omega t Y = 0) ↔ N omega t (X ∪ Y) = 0 := by
    intro X Y
    have h1 : N omega t (X ∪ Y) = N omega t X + N omega t (Y \ X) := by
      rw [← hadd X (Y \ X) (Set.disjoint_left.2 fun x hx hx' => hx'.2 hx), Set.union_sdiff_self]
    have h2 : N omega t Y = N omega t (Y ∩ X) + N omega t (Y \ X) := by
      rw [← hadd (Y ∩ X) (Y \ X) (Set.disjoint_left.2 fun x hx hx' => hx'.2 hx.2),
        Set.inter_union_sdiff]
    have h3 : N omega t X = N omega t (Y ∩ X) + N omega t (X \ Y) := by
      rw [← hadd (Y ∩ X) (X \ Y) (Set.disjoint_left.2 fun x hx hx' => hx'.2 hx.1),
        Set.inter_comm, Set.inter_union_sdiff]
    constructor
    · rintro ⟨hX, hY⟩; omega
    · intro h; omega
  have hempty : N omega t ∅ = 0 := by
    have := hadd ∅ ∅ (disjoint_bot_left)
    simp at this
    omega
  induction m with
  | zero => simp [hempty]
  | succ k ih =>
    have hun : (⋃ i : Fin (k+1), B i) = B 0 ∪ ⋃ i : Fin k, B i.succ := by
      ext x; simp [Fin.exists_fin_succ]
    rw [Fin.forall_fin_succ, hun]
    have ih' := ih (fun i => B i.succ)
    exact ⟨fun ⟨h0, hs⟩ => (hU _ _).1 ⟨h0, ih'.1 hs⟩,
      fun hh => ⟨((hU _ _).2 hh).1, ih'.2 ((hU _ _).2 hh).2⟩⟩

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (m : Nat) (B : Fin m → Set E) :
    ∀ᵐ omega ∂P, ∀ t : NNReal,
      (∀ i : Fin m, N omega t (B i) = 0) ↔
      N omega t (⋃ i : Fin m, B i) = 0 :=
  Kyprianou.Ch06.finiteUnionMarkedCountZeroIffAllZeroAe P n N hPPP m B
