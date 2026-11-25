-- Prove2me | solution 1 for GlobalTheory.SW.SwdHeat.isSB_member
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:36:40.198922+00:00
-- url     : https://prove2.me/submissions/c854a010-0aef-4885-8469-7d688596c034

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThHStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisensteinSeriesOfSchwartzIsHolomorphic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisensteinSeriesOfSchwartzIsHolomorphicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatSwd
import Theorems.Thm_GlobalTheory_SW_Base_mem_stdL
import Theorems.Thm_GlobalTheory_SW_Model_mem_stdL
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SW.rowEmb_apply
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SwdHeat
open GlobalTheory.SW.EisHeat
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
namespace GlobalTheory.SW.SwdHeat
theorem _root_.solution {M R : ℕ} {φ : Fam E n N} (h : admitted M R φ) {Λ : Lt E n}
    (hΛ : Λ ∈ Vset E n M) : IsSB (φ Λ) := by
  obtain ⟨s, hs, -, h1, h2⟩ := hΛ.2.2
  refine ⟨s * R, Nat.mul_pos hs h.pos.2, fun x hx k a => ?_, fun x y hy => ?_⟩
  · have := (Base.mem_stdL _).1 (h1 _ (h.supp Λ hΛ x hx a)) k
    simpa [mul_assoc] using this
  · have := h.per Λ hΛ x ((s : E) • y) fun a => h2 _ ((Base.mem_stdL (yᵀ a)).2 fun k => hy k a)
    rw [smul_smul, mul_comm, ← Nat.cast_mul] at this
    exact this
end GlobalTheory.SW.SwdHeat
