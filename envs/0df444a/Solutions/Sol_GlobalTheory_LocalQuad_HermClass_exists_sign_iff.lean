-- Prove2me | solution 1 for GlobalTheory.LocalQuad.HermClass.exists_sign_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:47.839855+00:00
-- url     : https://prove2.me/submissions/ef04ce54-8e87-4186-bb00-d49de30cff33

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.HermClass
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.LocalQuad.HermClass
theorem _root_.solution (τ : E →+* ℂ) {r : ℕ} {g g' : Fin r → E}
    (h : posCount τ g = posCount τ g') (j : Fin r) :
    ∃ i, (0 < (τ (g i)).re ↔ 0 < (τ (g' j)).re) := by
  by_contra hne
  push Not at hne
  by_cases hj : 0 < (τ (g' j)).re
  · have h1 : posCount τ g = 0 := by
      rw [posCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ hi
      rcases hne i with h | h
      · exact absurd hj (not_lt.mpr h.2)
      · exact absurd hi (not_lt.mpr h.1)
    rw [h, posCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h1
    exact h1 (Finset.mem_univ j) hj
  · have h1 : posCount τ g = Fintype.card (Fin r) := by
      rw [posCount, Finset.card_eq_iff_eq_univ, Finset.filter_eq_self]
      intro i _
      rcases hne i with h | h
      · exact h.1
      · exact absurd h.2 hj
    rw [h, posCount, Finset.card_eq_iff_eq_univ, Finset.filter_eq_self] at h1
    exact hj (h1 j (Finset.mem_univ j))
end GlobalTheory.LocalQuad.HermClass
