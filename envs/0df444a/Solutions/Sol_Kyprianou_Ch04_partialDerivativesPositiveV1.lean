-- Prove2me | solution 1 for Kyprianou.Ch04.partialDerivativesPositiveV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:33:48.129872+00:00
-- url     : https://prove2.me/submissions/e8b1c16d-ca49-4543-96ef-22f714edede0

import Mathlib
open Filter Set Topology
set_option autoImplicit false

/-- Joint derivative on the positive-time half-plane from continuous partial derivatives. -/
theorem solution (f ft fx : ℝ → ℝ → ℝ)
    (ht : ∀ s x, HasDerivAt (fun u => f u x) (ft s x) s)
    (hx : ∀ s x, HasDerivAt (f s) (fx s x) x)
    (hct : ContinuousOn (fun z : ℝ × ℝ => ft z.1 z.2) (Ici 0 ×ˢ univ))
    (hcx : ContinuousOn (fun z : ℝ × ℝ => fx z.1 z.2) (Ici 0 ×ˢ univ))
    (s x : ℝ) (hs : 0 < s) (a b : ℝ) :
    fderiv ℝ (fun z : ℝ × ℝ => f z.1 z.2) (s,x) (a,b) =
      ft s x * a + fx s x * b := by
  let D (y : ℝ) := ContinuousLinearMap.toSpanSingleton ℝ y
  have hD : Continuous D := by
    have h : D = fun y => (1 : ℝ →L[ℝ] ℝ).smulRight y := by
      funext y
      ext z
      simp [D]
    rw [h]
    fun_prop
  have hn : Ici (0 : ℝ) ×ˢ (univ : Set ℝ) ∈ 𝓝 (s,x) :=
    prod_mem_nhds (Ici_mem_nhds hs) univ_mem
  have hm : (s,x) ∈ Ici (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hs.le, mem_univ _⟩
  have ht' : ContinuousAt (fun z : ℝ × ℝ => D (ft z.1 z.2)) (s,x) :=
    hD.continuousAt.comp ((hct (s,x) hm).continuousAt hn)
  have hx' : ContinuousAt (fun z : ℝ × ℝ => D (fx z.1 z.2)) (s,x) :=
    hD.continuousAt.comp ((hcx (s,x) hm).continuousAt hn)
  have hf := hasStrictFDerivAt_uncurry_coprod
    (f := f) (f₁ := fun s x => D (ft s x))
    (f₂ := fun s x => D (fx s x))
    (Eventually.of_forall fun z => by
      exact (ht z.1 z.2).hasFDerivAt)
    (Eventually.of_forall fun z => by
      exact (hx z.1 z.2).hasFDerivAt)
    ht' hx'
  change fderiv ℝ (fun z : ℝ × ℝ => f z.1 z.2) (s,x) (a,b) = _
  have hfd : HasFDerivAt (fun z : ℝ × ℝ => f z.1 z.2)
      ((D (ft s x)).coprod (D (fx s x))) (s,x) := hf.hasFDerivAt
  rw [hfd.fderiv, ContinuousLinearMap.coprod_apply]
  simp [D, smul_eq_mul, mul_comm]
