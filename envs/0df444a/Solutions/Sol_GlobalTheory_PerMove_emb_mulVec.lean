-- Prove2me | solution 1 for GlobalTheory.PerMove.emb_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:35.72838+00:00
-- url     : https://prove2.me/submissions/c2ab53fd-dadf-4085-ab72-f47b32e89c80

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PerMove
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField Matrix
open scoped nonZeroDivisors
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.PerMove
namespace _root_.GlobalTheory.PerMove
theorem _root_.solution (τ : E →+* ℂ) (γ : Matrix (Fin r) (Fin r) E) (v : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (γ *ᵥ v) = γ.map τ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v := by
  ext a
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, Matrix.mulVec, dotProduct, map_sum]
end _root_.GlobalTheory.PerMove
end GlobalTheory.PerMove
