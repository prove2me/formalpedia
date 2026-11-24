-- Prove2me | solution 1 for GlobalTheory.Published.Landherr.det_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:15:39.162215+00:00
-- url     : https://prove2.me/submissions/3fd2837b-de24-45f7-9a5e-c629574e3583

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Theorems.Thm_GlobalTheory_Published_det_map_cc
import Theorems.Thm_GlobalTheory_Published_cc_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.Landherr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {G G' : Matrix (Fin r) (Fin r) E}
namespace GlobalTheory.Published.Landherr
theorem _root_.solution (hG : G.det ≠ 0)
    (h : ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc) :
    ∃ x : E, G.det / G'.det = x * cc x := by
  obtain ⟨P, hP, rfl⟩ := h
  refine ⟨P.det⁻¹, ?_⟩
  have h1 : cc P.det⁻¹ = (cc P.det)⁻¹ := by simp [cc]
  have h2 := cc_ne_zero hP
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_map_cc, h1]
  field_simp
end GlobalTheory.Published.Landherr
