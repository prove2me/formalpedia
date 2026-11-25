-- Prove2me | solution 1 for GlobalTheory.BigOn.on_of_onWith_canonical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:10:19.599035+00:00
-- url     : https://prove2.me/submissions/abcfec9d-1985-48c8-99c4-84cc0949e9f7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OnOfOnWithCanonical
import Theorems.Thm_GlobalTheory_BigOn_canonical_error_real
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_lw_pos
import Theorems.Thm_Formalism_L2_Indef_Tree_lw_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Indef Formalism.L2.Indef.Tree
open GlobalTheory GlobalTheory.BigOn
namespace GlobalTheory.BigOn
theorem _root_.solution :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (Z : IndefScale Bs) (C C' CH CH' : ℝ) (err : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ), 0 < S.D → 0 ≤ Z.E1u → 2 * C ≤ C' → (∀ w ∈ S.Tw, ∀ j, 0 ≤ Z.J0 (S.μ w) w j) → (∀ w j, S.err0 w j = max 0 ((∑ j', ((S.Iw j' (S.μ w) w : ℝ) + (S.Iw j' (S.μ w) (Formalism.DivisionValues.conjPl w) : ℝ))) / (S.D : ℝ) - ∑ j', 2 * ((Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * Z.F0 w j') - (Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (2 / (Formalism.EigenvalueLevelCeiling.plc w : ℝ) ^ 2)) / ((Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (Fintype.card Bs.J : ℝ))) → ONwith S (Z.num C CH) err → S.ON (Z.num C' CH') := by
  intro K _ _ _ Bs Df S Z C C' CH CH' err hD hE hC hJ h0 h
  rw [on_iff_with]
  obtain ⟨h1, h2, h3⟩ := h
  exact canonical_error_real S.Tw
    (fun w j => (S.Iw j (S.μ w) w : ℝ) + (S.Iw j (S.μ w) (Formalism.DivisionValues.conjPl w) : ℝ)) Z.F0 err S.err0
    (fun w j => Z.J0 (S.μ w) w j) (fun w => (Formalism.EigenvalueLevelCeiling.ramw w : ℝ))
    (fun w => (Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (2 / (Formalism.EigenvalueLevelCeiling.plc w : ℝ) ^ 2)) (fun w => Formalism.DivisionValues.lw w) (S.D : ℝ)
    (C * Z.E1u) (C' * Z.E1u) (by exact_mod_cast hD) (fun w => ramw_pos w) (fun w => (lw_pos w).le)
    (by nlinarith [mul_le_mul_of_nonneg_right hC hE]) hJ h0 h1 h2 h3
end GlobalTheory.BigOn
