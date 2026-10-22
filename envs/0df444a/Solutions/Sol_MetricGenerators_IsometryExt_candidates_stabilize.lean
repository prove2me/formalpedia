-- Prove2me | solution 1 for MetricGenerators.IsometryExt.candidates_stabilize
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:03:18.805816+00:00
-- url     : https://prove2.me/submissions/ccb77042-20b1-4544-a061-2ef2a854e97a

import Mathlib
import Definitions.Def_MetricGenerators_IsometryExt_Basic
import Definitions.Def_MetricGenerators_IsometryExt_Representation

set_option autoImplicit false
open MetricGenerators.IsometryExt

theorem solution {VH VG : Type*} [Fintype VH] [Fintype VG]
    (H : SimpleGraph VH) (G : SimpleGraph VG) (hH : H.Connected) (hG : G.Connected)
    (T : Finset VH) (f : ↥T → VG) :
    (∀ i : ℕ, candSet H G T f (i + 1) ⊆ candSet H G T f i ∧
      ∀ u : VH, cand H G T f (i + 1) u ⊆ cand H G T f i u) ∧
    (∀ k : ℕ, Fintype.card VG ≤ k →
      candSet H G T f k = candSet H G T f (Fintype.card VG) ∧
      ∀ u : VH, cand H G T f k u = cand H G T f (Fintype.card VG) u) := by
  have c1 : ∀ i, candSet H G T f (i + 1) =
      {x | x ∈ candSet H G T f i ∧ ∀ u v : VH, x ∈ cand H G T f i u → H.Adj u v →
        ∃ y ∈ cand H G T f i v, G.Adj x y} := fun i => rfl
  have c2 : ∀ i u, cand H G T f (i + 1) u = cand H G T f i u ∩ candSet H G T f (i + 1) :=
    fun i u => rfl
  have sub1 : ∀ i, candSet H G T f (i + 1) ⊆ candSet H G T f i := by
    intro i x hx
    rw [c1] at hx
    exact hx.1
  have sub2 : ∀ i u, cand H G T f (i + 1) u ⊆ cand H G T f i u := by
    intro i u x hx
    rw [c2] at hx
    exact hx.1
  have inv : ∀ i u, cand H G T f i u ⊆ candSet H G T f i := by
    intro i
    cases i with
    | zero => intro u x hx; exact Set.mem_iUnion.mpr ⟨u, hx⟩
    | succ i => intro u x hx; rw [c2] at hx; exact hx.2
  have stat : ∀ i, candSet H G T f (i + 1) = candSet H G T f i → ∀ j,
      candSet H G T f (i + j) = candSet H G T f i ∧
        ∀ u, cand H G T f (i + j) u = cand H G T f i u := by
    intro i hi j
    induction j with
    | zero => exact ⟨rfl, fun u => rfl⟩
    | succ j ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have e0 : candSet H G T f (i + j + 1) = candSet H G T f (i + 1) := by
        simp only [c1, ih1, ih2]
      have e1 : candSet H G T f (i + (j + 1)) = candSet H G T f i := by
        rw [← add_assoc]
        exact e0.trans hi
      refine ⟨e1, fun u => ?_⟩
      have e2 : candSet H G T f (i + j + 1) = candSet H G T f i := by rw [e0, hi]
      show cand H G T f (i + j + 1) u = cand H G T f i u
      rw [c2, e2, ih2 u]
      exact Set.inter_eq_left.mpr (inv i u)
  have hex : ∃ i ≤ Fintype.card VG, candSet H G T f (i + 1) = candSet H G T f i := by
    by_contra hcon
    push_neg at hcon
    have hfin : ∀ i, (candSet H G T f i).Finite := fun i => Set.toFinite _
    have hmain : ∀ i ≤ Fintype.card VG,
        (candSet H G T f i).ncard + i ≤ Fintype.card VG := by
      intro i
      induction i with
      | zero =>
        intro _
        calc (candSet H G T f 0).ncard + 0 = (candSet H G T f 0).ncard := rfl
          _ ≤ (Set.univ : Set VG).ncard := Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
          _ = Nat.card VG := Set.ncard_univ _
          _ = Fintype.card VG := Nat.card_eq_fintype_card
      | succ i ih =>
        intro hi
        have h1 := ih (by omega)
        have h2 : candSet H G T f (i + 1) ⊂ candSet H G T f i :=
          ⟨sub1 i, fun h => hcon i (by omega) (Set.Subset.antisymm (sub1 i) h)⟩
        have h3 := Set.ncard_lt_ncard h2 (hfin i)
        omega
    have h0 := hmain (Fintype.card VG) le_rfl
    have h4 : (candSet H G T f (Fintype.card VG)).ncard = 0 := by omega
    have h5 := (Set.ncard_eq_zero (hfin _)).mp h4
    apply hcon (Fintype.card VG) le_rfl
    apply Set.Subset.antisymm (sub1 _)
    rw [h5]
    exact Set.empty_subset _
  obtain ⟨i, hi, hst⟩ := hex
  refine ⟨fun i => ⟨sub1 i, sub2 i⟩, fun k hk => ?_⟩
  have hk' := stat i hst (k - i)
  have hn := stat i hst (Fintype.card VG - i)
  rw [show i + (k - i) = k by omega] at hk'
  rw [show i + (Fintype.card VG - i) = Fintype.card VG by omega] at hn
  exact ⟨hk'.1.trans hn.1.symm, fun u => (hk'.2 u).trans (hn.2 u).symm⟩
