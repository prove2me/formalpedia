-- Prove2me | solution 1 for HunterPDE.Compactness.memW_iff_sobolev
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T09:14:32.902576+00:00
-- url     : https://prove2.me/submissions/9caa4407-c9d4-4890-b1db-b023939970fd

import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem solution {n k : ℕ} {p : ℝ≥0∞}
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    HunterPDE.Compactness.MemW k p Ω f ↔ HunterPDE.Sobolev.MemW k p Ω f := by
  classical
  have happ (u : EuclideanSpace ℝ (Fin n) → ℝ) (a b : List (Fin n)) :
      HunterPDE.Shared.iteratedPartial u (a ++ b) =
        HunterPDE.Shared.iteratedPartial (HunterPDE.Shared.iteratedPartial u b) a := by
    induction a with
    | nil => rfl
    | cons i a ih => simp only [List.cons_append, HunterPDE.Shared.iteratedPartial, ih]
  have hrep (u : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n) (r : ℕ) :
      HunterPDE.Shared.iteratedPartial u (List.replicate r i) =
        (HunterPDE.Sobolev.partialDeriv i)^[r] u := by
    induction r with
    | zero => rfl
    | succ r ih =>
      simp only [List.replicate_succ, HunterPDE.Shared.iteratedPartial, ih,
        Function.iterate_succ_apply']
      rfl
  have hword (u : EuclideanSpace ℝ (Fin n) → ℝ) (α : Fin n → ℕ)
      (l : List (Fin n)) :
      HunterPDE.Shared.iteratedPartial u (l.flatMap (fun i => List.replicate (α i) i)) =
        l.foldr (fun i v => (HunterPDE.Sobolev.partialDeriv i)^[α i] v) u := by
    induction l with
    | nil => rfl
    | cons i l ih => rw [List.flatMap_cons, happ, hrep, ih, List.foldr_cons]
  have hderiv (u : EuclideanSpace ℝ (Fin n) → ℝ) (α : Fin n → ℕ) :
      HunterPDE.Shared.multiDeriv u α = HunterPDE.Sobolev.iteratedPartial α u :=
    hword u α (List.finRange n)
  have hweak (α : Fin n → ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ) :
      HunterPDE.Shared.HasWeakDeriv Ω α f g ↔ HunterPDE.Sobolev.HasWeakDeriv Ω α f g := by
    simp only [HunterPDE.Shared.HasWeakDeriv, HunterPDE.Sobolev.HasWeakDeriv,
      HunterPDE.Shared.IsTestFunction, HunterPDE.Sobolev.IsTestFunction, hderiv]
  have hindex (α : Fin n → ℕ) :
      α ∈ HunterPDE.Compactness.multiIndicesLe n k ↔ ∑ i, α i ≤ k := by
    simp only [HunterPDE.Compactness.multiIndicesLe, Finset.mem_filter,
      Fintype.mem_piFinset, Finset.mem_range]
    exact ⟨And.right, fun h => ⟨fun i => Nat.lt_succ_of_le
      ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans h), h⟩⟩
  constructor
  · intro h
    have hz : (0 : Fin n → ℕ) ∈ HunterPDE.Compactness.multiIndicesLe n k :=
      (hindex _).mpr (by simp)
    obtain ⟨g, hg, _⟩ := h _ hz
    refine ⟨hg.1, fun α hα => ?_⟩
    obtain ⟨g, hg, hgp⟩ := h α ((hindex _).mpr hα)
    exact ⟨g, (hweak _ _).mp hg, hgp⟩
  · intro h α hα
    obtain ⟨g, hg, hgp⟩ := h.2 α ((hindex _).mp hα)
    exact ⟨g, (hweak _ _).mpr hg, hgp⟩
