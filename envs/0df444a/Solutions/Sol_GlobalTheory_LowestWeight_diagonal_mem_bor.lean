-- Prove2me | solution 1 for GlobalTheory.LowestWeight.diagonal_mem_bor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:53:22.838516+00:00
-- url     : https://prove2.me/submissions/358d29d0-7981-4622-a525-e1b1011fe590

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LowestWeightFunctionMulEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix Filter Topology
open scoped ComplexConjugate ComplexOrder
open GlobalTheory.LowestWeight
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace GlobalTheory.LowestWeight
theorem _root_.solution (d : X.Ψ → Fin r → ℂ) (hd : ∀ τ a, d τ a ≠ 0) :
    (fun τ => (diagonal (d τ) : Matrix (Fin r) (Fin r) ℂ)) ∈ Bor X.Ψ r := by
  intro τ
  refine ⟨?_, fun a c h => diagonal_apply_ne _ h.ne'⟩
  change (diagonal (d τ)).det ≠ 0
  rw [det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun a _ => hd τ a
end GlobalTheory.LowestWeight
