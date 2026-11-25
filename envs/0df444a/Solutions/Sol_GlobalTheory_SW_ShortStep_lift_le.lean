-- Prove2me | solution 1 for GlobalTheory.SW.ShortStep.lift_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:09:53.525384+00:00
-- url     : https://prove2.me/submissions/c8c09ccd-5d5a-44d5-96da-c952d762377e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSte
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_comb_le
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ShortStep
open MinkowskiProductBounds
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
namespace GlobalTheory.SW.ShortStep
theorem _root_.solution {n m : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef)
    (V : Matrix (Fin 1) (Fin n) ℂ) (B : Matrix (Fin m) (Fin n) ℂ) (L : Matrix (Fin m) (Fin 1) ℂ)
    (t : Fin m → ℂ) (α : ℂ) {C M : ℝ} (hM : 1 ≤ M) (h1 : (V 0 ⬝ᵥ H *ᵥ star (V 0)).re ≤ C)
    (h2 : (t ⬝ᵥ ((B - L * V) * H * (B - L * V)ᴴ) *ᵥ star t).re ≤ C)
    (h3 : ‖α + (t ᵥ* L) 0‖ ≤ M) :
    ((t ᵥ* B + α • V 0) ⬝ᵥ H *ᵥ star (t ᵥ* B + α • V 0)).re ≤ (2 * (M * √C)) ^ 2 := by
  have e : t ᵥ* B + α • V 0 = ∑ j, ![1, α + (t ᵥ* L) 0] j • ![t ᵥ* (B - L * V), V 0] j := by
    have : (t ᵥ* L) ᵥ* V = (t ᵥ* L) 0 • V 0 := by
      ext j; simp [vecMul, dotProduct]
    rw [Fin.sum_univ_two, vecMul_sub, ← vecMul_vecMul, this]
    simp [add_smul]
  rw [e]
  refine comb_le hH _ _ (fun j => ?_) fun j => ?_
  · fin_cases j
    · rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_vecMul] at h2
      exact h2
    · exact h1
  · fin_cases j
    · simpa using hM
    · exact h3
end GlobalTheory.SW.ShortStep
