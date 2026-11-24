-- Prove2me | solution 1 for GlobalTheory.BoundedBasis.pairing_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:02:39.928051+00:00
-- url     : https://prove2.me/submissions/f9fd33bc-2046-4da3-af10-5b373b17630e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases
import Theorems.Thm_GlobalTheory_BoundedBasis_det_gramOf_ne_zero
import Theorems.Thm_GlobalTheory_BoundedBasis_exists_vecMul_eq
import Theorems.Thm_GlobalTheory_BoundedBasis_coe_pairing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
open GlobalTheory.BoundedBasis
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)
namespace GlobalTheory.BoundedBasis
theorem _root_.solution {v : Fin r → Fin r → E} (hv : ∀ i, v i ∈ X.L')
    (hi : LinearIndependent E v) : Function.Injective (pairing X v hv) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, hc⟩ := exists_vecMul_eq hi x
  have h : ((X.NA : E) • c) ᵥ* gramOf X.Gm v = 0 := by
    funext k
    rw [← coe_pairing X v hv x c hc k, hx]
    simp
  have h1 := Matrix.eq_zero_of_vecMul_eq_zero (det_gramOf_ne_zero X.Gm_det hi) h
  have h2 : c = 0 := (smul_eq_zero.1 h1).resolve_left (by exact_mod_cast X.NA_pos.ne')
  refine Subtype.ext ?_
  rw [hc, h2, zero_vecMul]
  rfl
end GlobalTheory.BoundedBasis
