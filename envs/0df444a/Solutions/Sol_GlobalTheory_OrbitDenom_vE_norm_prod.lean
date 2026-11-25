-- Prove2me | solution 1 for GlobalTheory.OrbitDenom.vE_norm_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:45:01.797929+00:00
-- url     : https://prove2.me/submissions/268c6895-1ecd-4df8-828d-9868fb295fcd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramVal_vE_valuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.OrbitDenom
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.OrbitDenom
theorem _root_.solution (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {ι : Type} (x : ι → E)
    (hx : ∀ i, IsUnit (x i)) (s : Finset ι) :
    vE L ϖ ((∏ i ∈ s, x i) * L.cj (∏ i ∈ s, x i)) = ∑ i ∈ s, vE L ϖ (x i * L.cj (x i)) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)
  have hadd := (GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).1
  have hn : ∀ y : E, IsUnit y → ∃ c : F, c ≠ 0 ∧ algebraMap F E c = y * L.cj y := by
    intro y hy
    obtain ⟨c, hc⟩ := (L.cj_fix (y * L.cj y)).1 (by rw [map_mul, L.cj_cj, mul_comm])
    refine ⟨c, ?_, hc⟩
    rintro rfl
    exact (hy.mul (hy.map L.cj)).ne_zero (by rw [← hc, map_zero])
  induction s using Finset.induction_on with
  | empty =>
    have := hadd 1 1 one_ne_zero one_ne_zero
    simp only [mul_one, map_one, Finset.prod_empty, Finset.sum_empty] at this ⊢
    omega
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ← ih]
    obtain ⟨c, hc0, hc⟩ := hn _ (hx a)
    obtain ⟨d, hd0, hd⟩ := hn (∏ i ∈ s, x i) (IsUnit.prod_iff.2 fun i _ => hx i)
    rw [← hc, ← hd, ← hadd c d hc0 hd0, map_mul (algebraMap F E), hc, hd, map_mul]
    congr 1
    ring
end GlobalTheory.OrbitDenom
