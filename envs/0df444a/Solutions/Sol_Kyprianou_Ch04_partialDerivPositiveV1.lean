-- Prove2me | solution 1 for Kyprianou.Ch04.partialDerivPositiveV1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:32:45.552827+00:00
-- url     : https://prove2.me/submissions/02b0943c-222e-4713-9421-939bb8407a57

import Mathlib
open Filter Set Topology
set_option autoImplicit false


namespace Kyprianou.Ch04
theorem _root_.solution (f ft fx : ℝ → ℝ → ℝ)
    (ht : ∀ s x, HasDerivAt (fun u => f u x) (ft s x) s)
    (hx : ∀ s x, HasDerivAt (f s) (fx s x) x)
    (hct : ContinuousOn (fun z : ℝ × ℝ => ft z.1 z.2) (Ici 0 ×ˢ univ))
    (hcx : ContinuousOn (fun z : ℝ × ℝ => fx z.1 z.2) (Ici 0 ×ˢ univ))
    (s x : ℝ) (hs : 0 < s) (a b : ℝ) :
    fderiv ℝ (fun z : ℝ × ℝ => f z.1 z.2) (s,x) (a,b) =
      ft s x * a + fx s x * b := by
  set U : Set (ℝ × ℝ) := Ioi 0 ×ˢ univ with hU
  have hUo : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hmem : (s, x) ∈ U := ⟨hs, trivial⟩
  have hsub : U ⊆ Ici 0 ×ˢ univ := prod_mono Ioi_subset_Ici_self subset_rfl
  have h := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (f := f)
    (f₁ := fun p q : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (ft p q))
    (f₂ := fun p q : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (fx p q))
    (u := (s, x))
    (by
      filter_upwards [hUo.mem_nhds hmem] with z _
      exact (ht z.1 z.2).hasFDerivAt)
    (by
      filter_upwards [hUo.mem_nhds hmem] with z _
      exact (hx z.1 z.2).hasFDerivAt)
    (by
      have hc := (hct.mono hsub).continuousAt (hUo.mem_nhds hmem)
      exact ((ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous.continuousAt).comp hc)
    (by
      have hc := (hcx.mono hsub).continuousAt (hUo.mem_nhds hmem)
      exact ((ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous.continuousAt).comp hc)
  have e : fderiv ℝ (fun z : ℝ × ℝ => f z.1 z.2) (s, x) = _ := h.hasFDerivAt.fderiv
  rw [e]
  show a • ft s x + b • fx s x = ft s x * a + fx s x * b
  simp only [smul_eq_mul]; ring

end Kyprianou.Ch04

