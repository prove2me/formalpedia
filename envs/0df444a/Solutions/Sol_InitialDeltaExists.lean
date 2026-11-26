-- Prove2me | solution 1 for InitialDeltaExists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:04:25.009902+00:00
-- url     : https://prove2.me/submissions/7c3be4fb-5e97-43df-8bb5-fa7782b197ce

import Definitions.Def_Tablet_StrictResolutionExists
import Definitions.Def_Tablet_smallPieceCount
import Definitions.Def_Tablet_IsDeltaEpsN
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_InitialDeltaExists
import Theorems.Thm_StrictResolutionExists


set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (γ : Curve E) (hpg : IsPiecewiseGeodesic γ)
    (hclosed : IsClosedCurve γ) (hlen : 0 < γ.len) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ smallPieceCount γ δ = 0 ∧ IsDeltaEpsN γ δ ε 0 := by
-- BODY
  obtain ⟨k, hk, s, hres, hstrict⟩ := StrictResolutionExists γ hpg hlen
  have hne : (Finset.Icc 1 k).Nonempty := Finset.nonempty_Icc.mpr hk
  -- Step 1: `δ` is the shortest edge length of the strict resolution `(k, s)`.
  set δ : ℝ := (Finset.Icc 1 k).inf' hne (fun j => s j - s (j - 1)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef, Finset.lt_inf'_iff]
    intro j hj
    obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.mp hj
    have h := hstrict (j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega] at h
    linarith
  -- Step 2: no edge of `(k, s)` is shorter than `δ`.
  have hnosmall : ∀ j ∈ Finset.Icc 1 k, ¬ (s j - s (j - 1) < δ) := fun j hj =>
    not_lt.mpr (Finset.inf'_le _ hj)
  -- Step 3: `(k, s)` witnesses a small-edge count of `0`.
  have hspc : smallPieceCount γ δ = 0 := by
    have hle : smallPieceCount γ δ
        ≤ ((Finset.Icc 1 k).filter (fun j => s j - s (j - 1) < δ)).card :=
      Nat.sInf_le ⟨k, s, hres, rfl⟩
    rw [Finset.filter_eq_empty_iff.mpr hnosmall, Finset.card_empty] at hle
    omega
  -- Step 4: both clauses of `IsDeltaEpsN` count subsets of that empty set.
  refine ⟨δ, hδpos, hspc, k, s, hres, ?_, ?_⟩
  · intro t t' _ _ _ _
    refine Nat.le_zero.mpr (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr ?_))
    intro j hj hp
    exact hnosmall j hj hp.2.2
  · intro _ t t' _ _ _ _
    refine Nat.le_zero.mpr (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr ?_))
    intro j hj hp
    exact hnosmall j hj hp.2
