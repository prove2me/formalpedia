-- Prove2me | solution 1 for GlobalTheory.LogKS.isKS_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:10:19.754054+00:00
-- url     : https://prove2.me/submissions/65d76439-53bd-4588-b407-2917d0859cf9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsChartIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Theorems.Thm_GlobalTheory_LogKS_isField_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped Matrix
open GlobalTheory GlobalTheory.LogKS
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
namespace GlobalTheory.LogKS
theorem _root_.solution (V : X.Opens) (U : X.affineOpens) {n : ℕ}
    (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) : IsKS t V U v (fun _ => 0) 0 := by
  refine ⟨t.PP.L.ι, fun i => t.G.hom ⁻¹ᵁ (U.1 ⊓ V) ⊓ t.PP.L.U i, id, fun _ _ _ => 0, ?_, fun _ => inf_le_right,
    fun _ => isField_zero _, fun _ _ _ => (map_zero _).symm, fun i i' O _ f S _ φ g₀ w _ h _ => ?_⟩
  · rw [← inf_iSup_eq, t.PP.isLB.cover, inf_top_eq]
  · simp [valR, h]
end GlobalTheory.LogKS
