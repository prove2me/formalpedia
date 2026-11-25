-- Prove2me | solution 1 for GlobalTheory.LeafCoordWeight.wtGe1_of_ordGe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:51:35.241092+00:00
-- url     : https://prove2.me/submissions/12f5a963-788e-443a-8f3f-020238e5104b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupCoordinatesPullbackLinearTangentBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeafCoordinateWeightNonnegOfAdaptedChainData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open Formalism.BaseCaseIdentities (Data Kn s0)
open ReciprocityTheory.PGsh (OrdGe lgSum)
open GlobalTheory GlobalTheory.LeafCoordWeight
namespace GlobalTheory.LeafCoordWeight
theorem _root_.solution {C : Type} [Field C] {V : VF C} {i N : ℕ} {w : ℝ}
    {f : MvPowerSeries (Fin N) C}
    (h : OrdGe V.v (fun _ => 1 / ((V.l : ℝ) ^ 2 - 1) + 3 / (8 * (V.l : ℝ) ^ i)) f w) :
    WtGe1 V i w f := by
  intro μ
  have h1 : r1 V.l i - del V.l i = 1 / ((V.l : ℝ) ^ 2 - 1) + 3 / (8 * (V.l : ℝ) ^ i) := by
    have : (V.l : ℝ) ≠ 0 := by exact_mod_cast V.l_prime.ne_zero
    have h3 : 1 / (2 * (V.l : ℝ) ^ i) - 1 / (8 * (V.l : ℝ) ^ i) = 3 / (8 * (V.l : ℝ) ^ i) := by
      field_simp
      ring
    rw [← h3]
    unfold r1 del rho
    ring
  have h2 : (μ.degree : ℝ) = ∑ m, (μ m : ℝ) := by
    rw [Finsupp.degree_eq_sum]
    push_cast
    rfl
  refine le_trans ?_ (add_le_add (h μ) le_rfl)
  rw [← WithTop.coe_add, h1, h2, ← Finset.mul_sum]
  exact WithTop.coe_le_coe.2 (le_of_eq (by ring))
end GlobalTheory.LeafCoordWeight
