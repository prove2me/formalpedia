-- Prove2me | solution 1 for OAI.SevenEighths.HeckeMellinIdentity.eq_of_f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:12:51.217984+00:00
-- url     : https://prove2.me/submissions/46c5f635-967d-4db8-b3e2-3d5c5a9646f9

import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_MellinIdentity
import Theorems.Thm_OAI_SevenEighths_HeckeMellinIdentity_scaled_eq

set_option autoImplicit false
open OAI
noncomputable section
open Set Filter
open scoped Topology
open OAI.SevenEighths OAI.SevenEighths.HeckeMellinIdentity
namespace OAI.SevenEighths.HeckeMellinIdentity
theorem _root_.solution (P Q : WeakFEPair ℂ) (hP : P.k = 1) (hQ : Q.k = 1)
    (hf : ∀ t : ℝ, 0 < t → P.f t = Q.f t) (hf₀ : P.f₀ = Q.f₀)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : P.Λ s = Q.Λ s := by
  have h := scaled_eq P Q hP hQ 1 zero_lt_one (fun z hz => by
    simp only [Complex.ofReal_one, Complex.one_cpow, one_mul]
    rw [← (P.hasMellin (by rwa [hP])).2, ← (Q.hasMellin (by rwa [hQ])).2]
    unfold mellin
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [hf t ht, hf₀]) h0 h1
  simpa only [Complex.ofReal_one, Complex.one_cpow, one_mul] using h
end OAI.SevenEighths.HeckeMellinIdentity
