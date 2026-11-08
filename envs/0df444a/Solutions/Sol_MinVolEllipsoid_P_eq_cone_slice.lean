-- Prove2me | solution 1 for MinVolEllipsoid.P_eq_cone_slice
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:47:02.821332+00:00
-- url     : https://prove2.me/submissions/e38ae10b-af71-41ed-8139-ce8a01044d86

import Mathlib
import Definitions.Def_MinVolEllipsoid_liftCone

open MinVolEllipsoid in
theorem solution {n : ℕ} (P : Set (Fin n → ℝ)) (hPc : IsCompact P) (hPcv : Convex ℝ P)
    (hPi : (interior P).Nonempty) :
    P = {x : Fin n → ℝ | lift x ∈ liftCone P} := by
  ext x
  simp only [Set.mem_setOf_eq, liftCone]
  constructor
  · intro hx
    refine ⟨1, fun _ => 1, fun _ => x, fun _ => zero_le_one, fun _ => hx, ?_⟩
    simp
  · rintro ⟨m, c, xs, hc, hxs, hv⟩
    have h1 : ∑ s, c s = 1 := by
      have := congrFun hv (Sum.inr ())
      simp only [lift, Sum.elim_inr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        mul_one] at this
      linarith
    have h2 : x = ∑ s, c s • xs s := by
      funext i
      have := congrFun hv (Sum.inl i)
      simp only [lift, Sum.elim_inl, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [Finset.sum_apply]
      simpa only [Pi.smul_apply, smul_eq_mul] using this
    rw [h2]
    exact hPcv.sum_mem (fun s _ => hc s) h1 (fun s _ => hxs s)
