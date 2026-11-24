-- Prove2me | solution 1 for GlobalTheory.LinDescent.eventually_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:45:10.692254+00:00
-- url     : https://prove2.me/submissions/e8998909-915a-4160-a5f8-ef3f3448cbe9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
import Theorems.Thm_GlobalTheory_LinDescent_gs_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.LinDescent
theorem _root_.solution {D V : X.Opens} (hD : IsAffineOpen D) (f : Γ(X, D))
    (hV : X.basicOpen f ≤ V) (y : Γ(X, V)) :
    ∀ᶠ n in Filter.atTop, ∃ b : Γ(X, D), ∀ x ∈ X.basicOpen f,
      gs (𝟙 X) x D b = gs (𝟙 X) x D f ^ n * gs (𝟙 X) x V y := by
  obtain ⟨n, b, hb⟩ := exists_eq_pow_mul_of_isAffineOpen X D hD f (rs hV y)
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  refine ⟨f ^ (m - n) * b, fun x hx => ?_⟩
  have hxD : x ∈ D := X.basicOpen_le f hx
  have e : gs (𝟙 X) x _ (rs (X.basicOpen_le f) b) =
      gs (𝟙 X) x _ (rs (X.basicOpen_le f) f ^ n * rs hV y) := congrArg _ hb
  rw [gs_mul _ x _ hx, gs_pow _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx] at e
  rw [gs_mul _ x _ hxD, gs_pow _ x _ hxD, e, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]
end GlobalTheory.LinDescent
