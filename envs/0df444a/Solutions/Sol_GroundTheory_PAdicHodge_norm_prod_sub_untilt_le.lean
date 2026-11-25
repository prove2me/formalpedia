-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_prod_sub_untilt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:19:05.24182+00:00
-- url     : https://prove2.me/submissions/5ded824f-3b6a-4836-a8a4-b886f18c4b88

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField C p]
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution (s : Multiset 𝒪C♭) {Q : (normInteger C)[X]}
    (hQ : Q.map (Ideal.Quotient.mk (Ideal.span {(p : normInteger C)})) =
      ((s.map fun b => X - Polynomial.C b).prod).map (PreTilt.coeff 0))
    {z : normInteger C} (hz : Q.eval z = 0) :
    ‖(s.map fun b => (z : C) - ((PreTilt.untilt b : normInteger C) : C)).prod‖ ≤ ‖(p : C)‖ := by
  set mk := Ideal.Quotient.mk (Ideal.span {(p : normInteger C)})
  set R : (normInteger C)[X] := (s.map fun b => X - Polynomial.C (PreTilt.untilt b)).prod
  have h1 : ((s.map fun b => X - Polynomial.C b).prod).map (PreTilt.coeff 0) = R.map mk := by
    simp only [R, Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, mk, PreTilt.mk_untilt_eq_coeff_zero]
  have h2 : mk (R.eval z) = 0 := by
    rw [← eval₂_at_apply, ← eval_map, ← h1, ← hQ, eval_map, eval₂_at_apply, hz, map_zero]
  have h3 := (mk_eq_zero_iff_norm_le (p := p)).1 h2
  have h4 : ((R.eval z : normInteger C) : C) =
      (s.map fun b => (z : C) - ((PreTilt.untilt b : normInteger C) : C)).prod := by
    simp only [R, eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_sub, eval_X,
      eval_C]
    rw [← (normInteger C).subtype_apply, map_multiset_prod, Multiset.map_map]
    rfl
  rw [← h4]
  exact h3
end GroundTheory.PAdicHodge
