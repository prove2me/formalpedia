-- Prove2me | solution 1 for GlobalTheory.SW.Reduct.shortIso_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:04:11.052635+00:00
-- url     : https://prove2.me/submissions/b22515c7-7cb1-4383-a30b-c6ba3b89f68e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryMoveHermitianHalfSpaceHigh
import Theorems.Thm_GlobalTheory_SW_exists_shortIso
import Theorems.Thm_GlobalTheory_T_shortIsotropicVectorsExistence_succ_of_very_short_step


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Reduct
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.Reduct
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (N : ℕ) :
    ∀ D : ℕ, 0 < D → ∃ C : ℝ, ShortIso Ψ N D 0 C := by
  induction N with
  | zero =>
    intro D _
    refine ⟨0, fun G H _ _ _ _ hW _ _ => ?_⟩
    obtain ⟨W, hW⟩ := hW
    exact ⟨W, fun i => i.elim0, hW, fun i => i.elim0⟩
  | succ N ih =>
    exact GlobalTheory.T.shortIsotropicVectorsExistence_succ_of_very_short_step E Ψ hΨ N ih fun D ε hD hε => GlobalTheory.SW.exists_shortIso E Ψ hΨ (N + 1) D ε hD hε
end GlobalTheory.SW.Reduct
