-- Prove2me | solution 1 for NonconvexSplitting.ProxGrad.limitingSubdiff_robust
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:20:55.935107+00:00
-- url     : https://prove2.me/submissions/d952e55d-4a69-4460-b807-a05ca9920b08

import Mathlib.Topology.Sequences
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
open Filter Topology NonconvexSplitting.Shared

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : ∀ y, f y ≠ ⊥) (x v : EuclideanSpace ℝ (Fin n)) (hx : f x ≠ ⊤)
    (xs vs : ℕ → EuclideanSpace ℝ (Fin n))
    (hxs : Tendsto xs atTop (𝓝 x)) (hfxs : Tendsto (fun t => f (xs t)) atTop (𝓝 (f x)))
    (hvs : Tendsto vs atTop (𝓝 v)) (hmem : ∀ t, vs t ∈ LimitingSubdiff f (xs t)) :
    v ∈ LimitingSubdiff f x := by
  let R : Set (EuclideanSpace ℝ (Fin n) × EReal × EuclideanSpace ℝ (Fin n)) :=
    {z | f z.1 = z.2.1 ∧ IsRegularSubgrad f z.1 z.2.2}
  have hC : ∀ t, (xs t,f (xs t),vs t) ∈ closure R := by
    intro t
    obtain ⟨_,ys,ws,hys,hfys,hws,hreg⟩ := hmem t
    apply mem_closure_iff_seq_limit.mpr
    exact ⟨fun k => (ys k,f (ys k),ws k),fun k => ⟨rfl,hreg k⟩,by simpa only [nhds_prod_eq] using hys.prodMk (hfys.prodMk hws)⟩
  have hcl : (x,f x,v) ∈ closure R :=
    isClosed_closure.mem_of_tendsto (by simpa only [nhds_prod_eq] using hxs.prodMk (hfxs.prodMk hvs)) (Eventually.of_forall hC)
  obtain ⟨z,hz,hzt⟩ := mem_closure_iff_seq_limit.mp hcl
  simp only [nhds_prod_eq] at hzt
  refine ⟨hx,fun t => (z t).1,fun t => (z t).2.2,hzt.fst,?_,hzt.snd.snd,?_⟩
  · have he : (fun t => f (z t).1) = (fun t => (z t).2.1) := funext fun t => (hz t).1
    rw [he]
    exact hzt.snd.fst
  · intro t
    exact (hz t).2
