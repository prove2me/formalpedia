-- Prove2me | solution 1 for Kakutani1941.FixedPoint.closed_graph_iff
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:58:11.019399+00:00
-- url     : https://prove2.me/submissions/1d85f249-3de6-4d03-ae9b-d73503f4bd69

import Mathlib
import Definitions.Def_Kakutani1941_FixedPoint_UpperSemicontinuous
set_option autoImplicit false
open Kakutani1941.FixedPoint

theorem solution {m : ℕ} {S : Set (EuclideanSpace ℝ (Fin m))}
    (hSclosed : IsClosed S)
    (Φ : EuclideanSpace ℝ (Fin m) → Set (EuclideanSpace ℝ (Fin m)))
    (hΦsub : ∀ x ∈ S, Φ x ⊆ S) :
    IsUpperSemicontinuous S Φ ↔
      IsClosed {p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) |
        p.1 ∈ S ∧ p.2 ∈ Φ p.1} := by
  constructor
  · intro h
    rw [← isSeqClosed_iff_isClosed]
    intro p p0 hp hlim
    have h1 : Filter.Tendsto (fun n => (p n).1) Filter.atTop (nhds p0.1) :=
      (continuous_fst.tendsto _).comp hlim
    have h2 : Filter.Tendsto (fun n => (p n).2) Filter.atTop (nhds p0.2) :=
      (continuous_snd.tendsto _).comp hlim
    have hS0 : p0.1 ∈ S := hSclosed.mem_of_tendsto h1 (Filter.Eventually.of_forall fun n => (hp n).1)
    exact ⟨hS0, h (fun n => (p n).1) (fun n => (p n).2) p0.1 p0.2 (fun n => (hp n).1) hS0 h1
      (fun n => (hp n).2) h2⟩
  · intro h x y x0 y0 hx hx0 hxl hy hyl
    have hlim : Filter.Tendsto (fun n => (x n, y n)) Filter.atTop (nhds (x0, y0)) :=
      hxl.prodMk_nhds hyl
    have hmem : ∀ n, (x n, y n) ∈ {p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) |
        p.1 ∈ S ∧ p.2 ∈ Φ p.1} := fun n => ⟨hx n, hy n⟩
    exact (h.isSeqClosed hmem hlim).2
