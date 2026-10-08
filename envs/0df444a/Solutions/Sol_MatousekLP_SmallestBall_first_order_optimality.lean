-- Prove2me | solution 1 for MatousekLP.SmallestBall.first_order_optimality
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T04:34:10.141814+00:00
-- url     : https://prove2.me/submissions/10b55b67-a794-424f-a96a-062bb7cc0609

import Definitions.Def_MatousekLP_SmallestBall_Basic
import Mathlib

theorem solution {n : ℕ} (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (f : (Fin n → ℝ) → ℝ) (hf : Differentiable ℝ f) (hfc : ConvexOn ℝ Set.univ f)
    (xstar : Fin n → ℝ) (hxstar : xstar ∈ C) :
    IsMinOn f C xstar ↔ ∀ x ∈ C, 0 ≤ fderiv ℝ f xstar (x - xstar) := by
  constructor
  · intro hmin x hx
    have hloc : IsLocalMinOn f C xstar := hmin.localize
    have hseg : segment ℝ xstar (xstar + (x - xstar)) ⊆ C := by
      rw [add_sub_cancel]; exact hC.segment_subset hxstar hx
    exact hloc.hasFDerivWithinAt_nonneg (hf xstar).hasFDerivAt.hasFDerivWithinAt
      (mem_posTangentConeAt_of_segment_subset hseg)
  · intro h x hx
    set v := x - xstar
    set g : ℝ → ℝ := fun t => f (xstar + t • v)
    have hg : ConvexOn ℝ Set.univ g := by
      refine ⟨convex_univ, fun s _ t _ a b ha hb hab => ?_⟩
      have := hfc.2 (Set.mem_univ (xstar + s • v)) (Set.mem_univ (xstar + t • v)) ha hb hab
      simp only [g, smul_eq_mul] at this ⊢
      convert this using 2
      rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul, smul_smul, smul_smul,
        ← add_smul]
    have hline : HasDerivAt (fun t : ℝ => xstar + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add xstar
    have hline' : HasDerivAt (fun t : ℝ => xstar + t • v) v 0 := hline
    have hgd : HasDerivAt g (fderiv ℝ f xstar v) 0 := by
      have h0 : HasFDerivAt f (fderiv ℝ f xstar) (xstar + (0 : ℝ) • v) := by
        simpa using (hf xstar).hasFDerivAt
      have := h0.comp_hasDerivAt (0 : ℝ) hline
      exact this
    have hslope := hg.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hgd
    simp only [slope, g, vsub_eq_sub, sub_zero, inv_one, one_smul, zero_smul, add_zero, smul_eq_mul,
      one_mul] at hslope
    have h1 : xstar + v = x := by simp [v]
    rw [h1] at hslope
    have := h x hx
    show f xstar ≤ f x
    linarith
