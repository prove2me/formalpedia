-- Prove2me | solution 1 for OAI.SevenEighths.ThetaProduct.rectangularPair_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:39:14.781414+00:00
-- url     : https://prove2.me/submissions/02575788-c337-4568-b3e4-085b343ea944

import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_ThetaProduct
import Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_k
attribute [local simp] OAI.SevenEighths.ThetaProduct.rectangularPair_k

set_option autoImplicit false
open OAI
noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology
open OAI.SevenEighths OAI.SevenEighths.ThetaProduct
namespace OAI.SevenEighths.ThetaProduct
theorem _root_.solution (a b u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ =>
      (Real.exp (-Real.pi * (u * (n.1 + a) ^ 2 + v * (n.2 + b) ^ 2) * t) : ℂ))
      ((rectangularPair a b u v hu hv).f t) := by
  have h₁ := HurwitzZeta.hasSum_int_evenKernel a (mul_pos hu ht)
  have h₂ := HurwitzZeta.hasSum_int_evenKernel b (mul_pos hv ht)
  have hprod := h₁.mul h₂ (h₁.summable.mul_of_nonneg h₂.summable
    (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le))
  have hid (n : ℤ × ℤ) :
      Real.exp (-Real.pi * (u * (n.1 + a) ^ 2 + v * (n.2 + b) ^ 2) * t) =
      Real.exp (-Real.pi * (n.1 + a) ^ 2 * (u * t)) *
        Real.exp (-Real.pi * (n.2 + b) ^ 2 * (v * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [hid]
  simpa only [rectangularPair, product, scaledEvenPair, rescale,
    HurwitzZeta.hurwitzEvenFEPair, Function.comp_apply, Complex.ofReal_mul] using
    (Complex.hasSum_ofReal.mpr hprod)
end OAI.SevenEighths.ThetaProduct
