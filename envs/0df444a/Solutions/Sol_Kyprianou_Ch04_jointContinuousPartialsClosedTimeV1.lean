-- Prove2me | solution 1 for Kyprianou.Ch04.jointContinuousPartialsClosedTimeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:20:59.79833+00:00
-- url     : https://prove2.me/submissions/9ed173ff-d64a-4d8a-a3ac-f948975559d1

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_jointContinuousPartialsPositiveTimeV1
open Set Filter Topology
open scoped Topology
set_option autoImplicit false

/-- The continuous joint derivative extends to the closed positive-time half-plane. -/
theorem solution (f fTime fSpace : ℝ → ℝ → ℝ)
    (ht : ∀ s x, HasDerivAt (fun u => f u x) (fTime s x) s)
    (hx : ∀ s x, HasDerivAt (f s) (fSpace s x) x)
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hct : ContinuousOn (fun z : ℝ × ℝ => fTime z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hcx : ContinuousOn (fun z : ℝ × ℝ => fSpace z.1 z.2) (Ici (0 : ℝ) ×ˢ univ)) :
    ContDiffOn ℝ 1 (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ univ) := by
  let U := Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)
  let S := Ici (0 : ℝ) ×ˢ (univ : Set ℝ)
  let G := fun z : ℝ × ℝ => f z.1 z.2
  let D := fun p : ℝ × ℝ =>
    fTime p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ +
      fSpace p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hUS : U ⊆ S := prod_mono Ioi_subset_Ici_self subset_rfl
  have hcl : closure U = S := by simp [U,S,closure_prod_eq,closure_Ioi]
  have hD : ContinuousOn D S :=
    (hct.smul continuousOn_const).add (hcx.smul continuousOn_const)
  have hd (p : ℝ × ℝ) (hp : p ∈ U) : HasFDerivAt G (D p) p :=
    Kyprianou.Ch04.jointContinuousPartialsPositiveTimeV1 f fTime fSpace ht hx hct hcx p hp.1
  have hw (p : ℝ × ℝ) (hp : p ∈ S) : HasFDerivWithinAt G (D p) S p := by
    rw [← hcl]
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun q hq => (hd q hq).differentiableAt.differentiableWithinAt)
      ((convex_Ioi (0 : ℝ)).prod convex_univ)
      (isOpen_Ioi.prod isOpen_univ)
      (fun q hq => (hf q (show q ∈ S from hcl ▸ hq)).mono hUS)
    refine ((hD p hp).mono hUS).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (hd q hq).fderiv.symm
  have hu : UniqueDiffOn ℝ S := (uniqueDiffOn_Ici (0 : ℝ)).prod uniqueDiffOn_univ
  have hder : ContinuousOn (fderivWithin ℝ G S) S :=
    hD.congr (fun p hp => (hw p hp).fderivWithin (hu p hp))
  exact contDiffOn_succ_of_fderivWithin (n := 0)
    (fun p hp => (hw p hp).differentiableWithinAt) (by simp)
    (contDiffOn_zero.mpr hder)
