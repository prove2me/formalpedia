-- Prove2me | solution 1 for GlobalTheory.TriSqrt.det_eq_prod_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:39.267796+00:00
-- url     : https://prove2.me/submissions/90307670-2aea-404e-bbdd-9d0024f43f07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ContinuousOnNormDiagOfTriangularSqrt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.TriSqrt
namespace GlobalTheory.TriSqrt
theorem _root_.solution {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α] (t : n → α) (w : n → ℕ)
    (hinj : ∀ j j', t j = t j' → w j = w j' → j = j')
    (h : Matrix n n ℂ) (hs : ∀ j j', h j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') :
    h.det = ∏ j, h j j := by
  have hi : Function.Injective (fun j => toLex (Fintype.equivFin α (t j), w j)) := by
    intro k l hkl
    have h' := toLex.injective hkl
    rw [Prod.mk.injEq] at h'
    exact hinj _ _ ((Fintype.equivFin α).injective h'.1) h'.2
  letI : LinearOrder n := LinearOrder.lift' _ hi
  refine Matrix.det_of_upperTriangular fun k l hkl => ?_
  by_contra hne
  obtain ⟨h1, h2⟩ := hs k l hne
  have hkl' : toLex (Fintype.equivFin α (t l), w l) < toLex (Fintype.equivFin α (t k), w k) := hkl
  simp only [h1, Prod.Lex.toLex_lt_toLex, lt_self_iff_false, true_and, false_or] at hkl'
  omega
end GlobalTheory.TriSqrt
