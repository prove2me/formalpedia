-- Prove2me | solution 1 for GlobalTheory.SW.EisHeat.eventually_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:53:10.860801+00:00
-- url     : https://prove2.me/submissions/3cb7f547-f0d7-4238-b1f2-656c86e09e03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisAutomorphyLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DerivDerivConstMulCexpBilinearAtZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisensteinSeriesOfSchwartzIsHolomorphic
import Theorems.Thm_GlobalTheory_SW_EisHeat_imH_isHermitian
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_spanCovol_bot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhB_posDef_eventually
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisHeat
variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
namespace GlobalTheory.SW.EisHeat
theorem _root_.solution (δ : ℝ) {p : CF Ψ N N × CF Ψ n N × CF Ψ n N}
    (hp : ∀ τ, (imH (p.1 τ) - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosDef) :
    ∀ᶠ q : CF Ψ N N × CF Ψ n N × CF Ψ n N in 𝓝 p,
      ∀ τ, (imH (q.1 τ) - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosDef := by
  refine Filter.eventually_all.2 fun τ => ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.posDef_eventually
    (fun q : CF Ψ N N × CF Ψ n N × CF Ψ n N =>
      imH (q.1 τ) - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) (fun i j => ?_) (fun q => ?_) p (hp τ)
  · change Continuous fun q : CF Ψ N N × CF Ψ n N × CF Ψ n N =>
      (2 * I)⁻¹ * (q.1 τ i j - star (q.1 τ j i)) - ((δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) i j
    fun_prop
  · refine (imH_isHermitian _).sub ?_
    unfold IsHermitian
    rw [conjTranspose_smul, conjTranspose_one]
    simp
end GlobalTheory.SW.EisHeat
