-- Prove2me | solution 2 for OAI.Problem356.exists_compact_small_partition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:34:27.501386+00:00
-- url     : https://prove2.me/submissions/a1897011-d793-44f8-b96f-32c9ef696edd

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/CompactPartition.lean:L19-L57
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.exists_compact_small_partition. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure

-- ---- from OAI.Analysis.CoulombTransport.CompactPartition ----
namespace OAI

universe uX uIndex

noncomputable section

open Set MeasureTheory Metric

namespace Problem356

/-- Disjointification preserves measurability for finite ordered index sets. -/
theorem measurableSet_disjointed_fin {X : Type uX} [MeasurableSpace X]
    {n : ℕ} {A : Fin n → Set X} (hA : ∀ i, MeasurableSet (A i)) (i : Fin n) :
    MeasurableSet (disjointed A i) := by
  exact disjointedRec (fun _ _ ht => ht.diff (hA _)) (hA i)

/-- A compact metric set admits a finite Borel partition into sets of arbitrarily
small diameter. Empty cells are permitted, so the indexing is uniform. -/
theorem exists_compact_small_partition {X : Type uX} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {K : Set X} (hK : IsCompact K)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (A : Fin n → Set X),
      (∀ i, MeasurableSet (A i)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      (⋃ i, A i) = K ∧
      (∀ i, A i ⊆ K) ∧
      (∀ i, ∀ x ∈ A i, ∀ y ∈ A i, dist x y < δ) := by
  classical
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : X => ball x (δ / 2)) (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨x, mem_ball_self (half_pos hδ)⟩)
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let B : Fin (Fintype.card s) → Set X := fun i => K ∩ ball (e.symm i).val (δ / 2)
  have hB : ∀ i, MeasurableSet (B i) := fun _ =>
    hK.measurableSet.inter measurableSet_ball
  have hCover : (⋃ i, B i) = K := by
    apply Subset.antisymm
    · exact iUnion_subset fun i => inter_subset_left
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
      refine mem_iUnion.mpr ⟨e ⟨y, hy⟩, hx, ?_⟩
      simpa only [Equiv.symm_apply_apply] using hxy
  refine ⟨Fintype.card s, disjointed B, measurableSet_disjointed_fin hB,
    disjoint_disjointed B, ?_, ?_, ?_⟩
  · rw [iUnion_disjointed, hCover]
  · intro i
    exact (disjointed_subset B i).trans inter_subset_left
  · intro i x hx y hy
    have hx' := (disjointed_subset B i hx).2
    have hy' := (disjointed_subset B i hy).2
    calc
      dist x y ≤ dist x (e.symm i).val + dist (e.symm i).val y := dist_triangle _ _ _
      _ < δ / 2 + δ / 2 := add_lt_add (mem_ball.mp hx') (by simpa only [dist_comm] using (mem_ball.mp hy'))
      _ = δ := by ring

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open Set MeasureTheory Metric


theorem solution.{uX} : type_of% @_root_.OAI.Problem356.exists_compact_small_partition.{uX} := @_root_.OAI.Problem356.exists_compact_small_partition.{uX}
