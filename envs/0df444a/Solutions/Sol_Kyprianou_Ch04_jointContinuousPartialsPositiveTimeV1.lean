-- Prove2me | solution 1 for Kyprianou.Ch04.jointContinuousPartialsPositiveTimeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:54:44.294516+00:00
-- url     : https://prove2.me/submissions/8ca689ee-624b-44fc-9351-071d59549e92

import Mathlib
open Set Filter Topology
open scoped Topology
set_option autoImplicit false

/-- Continuous partial derivatives imply the stated joint derivative at positive times. -/
theorem solution (f fTime fSpace : ℝ → ℝ → ℝ)
    (ht : ∀ s x, HasDerivAt (fun u => f u x) (fTime s x) s)
    (hx : ∀ s x, HasDerivAt (f s) (fSpace s x) x)
    (hct : ContinuousOn (fun z : ℝ × ℝ => fTime z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hcx : ContinuousOn (fun z : ℝ × ℝ => fSpace z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (p : ℝ × ℝ) (hp : 0 < p.1) :
    HasFDerivAt (fun z : ℝ × ℝ => f z.1 z.2)
      (fTime p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ +
        fSpace p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  let I := ContinuousLinearMap.id ℝ ℝ
  let a := fun s x => fTime s x • I
  let b := fun s x => fSpace s x • I
  have ha (z : ℝ × ℝ) : HasFDerivAt (fun u => f u z.2) (a z.1 z.2) z.1 := by
    have he : a z.1 z.2 = ContinuousLinearMap.toSpanSingleton ℝ (fTime z.1 z.2) := by
      ext r
      simp [a,I,mul_comm]
    rw [he]
    exact (ht z.1 z.2).hasFDerivAt
  have hb (z : ℝ × ℝ) : HasFDerivAt (f z.1) (b z.1 z.2) z.2 := by
    have he : b z.1 z.2 = ContinuousLinearMap.toSpanSingleton ℝ (fSpace z.1 z.2) := by
      ext r
      simp [b,I,mul_comm]
    rw [he]
    exact (hx z.1 z.2).hasFDerivAt
  have hN : Ici (0 : ℝ) ×ˢ (univ : Set ℝ) ∈ 𝓝 p :=
    mem_of_superset ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hp,mem_univ _⟩)
      (prod_mono Ioi_subset_Ici_self subset_rfl)
  have hc : ContinuousAt (Function.uncurry a) p :=
    ((hct.continuousAt hN).smul continuousAt_const)
  have hd : ContinuousAt (Function.uncurry b) p :=
    ((hcx.continuousAt hN).smul continuousAt_const)
  have h := (hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (f := f) (f₁ := a) (f₂ := b) (u := p)
    (Eventually.of_forall ha) (Eventually.of_forall hb) hc hd).hasFDerivAt
  have he : fTime p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ +
      fSpace p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ =
      (Function.uncurry a p).coprod (Function.uncurry b p) := by
    apply ContinuousLinearMap.ext
    intro z
    simp [a,b,I,Function.uncurry,ContinuousLinearMap.coprod_apply]
  rw [he]
  exact h
