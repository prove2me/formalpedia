-- Prove2me | solution 1 for IsVLArchimedean_of_sigmaConditionallyCompleteLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:16:33.955664+00:00
-- url     : https://prove2.me/submissions/5dd442fd-fc47-49bc-9b4a-9fe09441daaf

module
public import Mathlib.Algebra.Order.Group.Pointwise.Bounds
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Data.Set.Countable
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderComplete
public import Theorems.Thm_isVLArchimedean_of_eq_zero_of_nonneg_of_forall_nsmul_le


set_option autoImplicit true
@[expose] public section
public section
open Set
universe u
theorem _root_.solution
    {X : Type*} [SigmaConditionallyCompleteLattice X] [AddCommGroup X]
    [IsOrderedAddMonoid X] : IsVLArchimedean X := by
  apply isVLArchimedean_of_eq_zero_of_nonneg_of_forall_nsmul_le
  intro x y hx hn
  set S : Set X := Set.range (fun n : ℕ => n • x) with hS_def
  have hS_count : S.Countable := Set.countable_range _
  have hS_ne : S.Nonempty := ⟨0 • x, 0, rfl⟩
  have hS_bdd : BddAbove S := ⟨y, by rintro _ ⟨n, rfl⟩; exact hn n⟩
  set u := sSup S with hu_def
  have hm : ∀ m : ℕ, m • x ≤ u := fun m =>
    SigmaConditionallyCompleteLattice.le_csSup S _ hS_count hS_bdd ⟨m, rfl⟩
  have hub : u - x ∈ upperBounds S := by
    rintro _ ⟨m, rfl⟩
    rw [le_sub_iff_add_le, ← succ_nsmul]
    exact hm (m + 1)
  have hu' : u ≤ u - x :=
    SigmaConditionallyCompleteLattice.csSup_le S _ hS_count hS_ne hub
  have hx_nonpos : x ≤ 0 := by
    have h : u + x ≤ u := le_sub_iff_add_le.mp hu'
    have h' : u + x ≤ u + 0 := by rwa [add_zero]
    exact (add_le_add_iff_left u).mp h'
  exact le_antisymm hx_nonpos hx
