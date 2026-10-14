-- Prove2me | solution 1 for Komlos.closedConvexFold_geometry
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T09:56:13.820843+00:00
-- url     : https://prove2.me/submissions/256de0b3-2e43-4abd-8bfa-323b99fe55fe

import Definitions.Def_Komlos_convex_fold
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith

open Set
open scoped Pointwise
set_option autoImplicit false



private lemma fold_raw_subset (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin m)))
    (hK : Convex ℝ K) (u : EuclideanSpace ℝ (Fin m)) :
    ((K + (fun t : ℝ => t • u) '' Icc (-1) 1) ∩
      ((K ∩ (fun y => y + (2 : ℝ) • u) ⁻¹' K) + Set.range (fun t : ℝ => t • u))) ⊆
      {x | x + u ∈ K ∨ x - u ∈ K} := by
  rintro x ⟨⟨k, hk, z, ⟨s, hs, rfl⟩, hks⟩, ⟨y, ⟨hy, hy2⟩, z, ⟨t, rfl⟩, hyt⟩⟩
  change k + s • u = x at hks
  change y + t • u = x at hyt
  have hline : Convex ℝ {a : ℝ | y + a • u ∈ K} := by
    intro a ha b hb p q hp hq hpq
    change y + (p * a + q * b) • u ∈ K
    have h := hK ha hb hp hq hpq
    have he : y + (p * a + q * b) • u = p • (y + a • u) + q • (y + b • u) := by
      rw [show q = 1-p by linarith]
      module
    rwa [he]
  have hzero : (0 : ℝ) ∈ {a : ℝ | y + a • u ∈ K} := by simpa using hy
  have htwo : (2 : ℝ) ∈ {a : ℝ | y + a • u ∈ K} := hy2
  have hk' : t - s ∈ {a : ℝ | y + a • u ∈ K} := by
    change y + (t - s) • u ∈ K
    have he : y + (t - s) • u = k := by
      calc
        _ = (y + t • u) - s • u := by module
        _ = x - s • u := by rw [hyt]
        _ = k := by rw [← hks]; module
    rwa [he]
  rcases le_total (1 : ℝ) t with ht | ht
  · right
    have h := hline.ordConnected.out hzero hk' (show t - 1 ∈ Icc 0 (t-s) by constructor <;> linarith [hs.2])
    change y + (t-1) • u ∈ K at h
    rw [← hyt]
    convert h using 1
    module
  · left
    have h := hline.ordConnected.out hk' htwo (show t + 1 ∈ Icc (t-s) 2 by constructor <;> linarith [hs.1])
    change y + (t+1) • u ∈ K at h
    rw [← hyt]
    convert h using 1
    module

theorem solution (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin m)))
    (hconv : Convex ℝ K) (hcomp : IsCompact K) (u : EuclideanSpace ℝ (Fin m)) :
    Convex ℝ (Komlos.closedConvexFold m K u) ∧
      IsCompact (Komlos.closedConvexFold m K u) ∧
      ∀ x ∈ Komlos.closedConvexFold m K u, x + u ∈ K ∨ x - u ∈ K := by
  let f : ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin m) := LinearMap.toSpanSingleton ℝ _ u
  have hj : Convex ℝ ((fun t : ℝ => t • u) '' Icc (-1) 1) :=
    (convex_Icc (-1 : ℝ) 1).linear_image f
  have hr : Convex ℝ (Set.range (fun t : ℝ => t • u)) := by
    simpa only [image_univ, show (f : ℝ → EuclideanSpace ℝ (Fin m)) = (fun t => t • u) from rfl] using (convex_univ : Convex ℝ (univ : Set ℝ)).linear_image f
  have hc : Convex ℝ (K ∩ (fun y => y + (2 : ℝ) • u) ⁻¹' K) :=
    hconv.inter (hconv.translate_preimage_left _)
  have hjcomp : IsCompact ((fun t : ℝ => t • u) '' Icc (-1) 1) :=
    isCompact_Icc.image (continuous_id.smul continuous_const)
  have hbcomp := hcomp.add hjcomp
  refine ⟨((hconv.add hj).inter (hc.add hr)).closure, ?_, ?_⟩
  · exact hbcomp.of_isClosed_subset isClosed_closure
      (closure_minimal inter_subset_left hbcomp.isClosed)
  · have hclosed : IsClosed {x | x + u ∈ K ∨ x - u ∈ K} :=
      (hcomp.isClosed.preimage (continuous_id.add continuous_const)).union
        (hcomp.isClosed.preimage (continuous_id.sub continuous_const))
    exact closure_minimal (fold_raw_subset m K hconv u) hclosed

