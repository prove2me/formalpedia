-- Prove2me | solution 1 for GlobalTheory.lb_div_pull_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:52:33.845795+00:00
-- url     : https://prove2.me/submissions/70c9f6ee-cd2e-469d-8495-e3dc24d16c47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_lcg_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_pullU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution (L M : LB X) (f : Y ⟶ X)
    (p q : (PUnit.{u + 1} → M.ι) × (PUnit.{u + 1} → L.ι)) :
    ((M.pull f).div (L.pull f)).g p q =
      res (inf_le_inf (lb_div_pull_U L M f p).le (lb_div_pull_U L M f q).le)
        (pullU f ((M.div L).U (p.1 PUnit.unit, p.2 PUnit.unit) ⊓
            (M.div L).U (q.1 PUnit.unit, q.2 PUnit.unit))
          ((M.div L).g (p.1 PUnit.unit, p.2 PUnit.unit) (q.1 PUnit.unit, q.2 PUnit.unit))) := by
  have key : ∀ {a b a' b' : X.Opens} {c d c' d' : Y.Opens}
      (h₁ : c ⊓ c' ≤ f ⁻¹ᵁ (a ⊓ a')) (h₂ : d ⊓ d' ≤ f ⁻¹ᵁ (b ⊓ b'))
      (h₃ : c ⊓ d ⊓ (c' ⊓ d') ≤ f ⁻¹ᵁ (a ⊓ b ⊓ (a' ⊓ b'))) (x : Γ(X, a ⊓ a')ˣ) (y : Γ(X, b ⊓ b')ˣ)
      (x' : Γ(Y, c ⊓ c')ˣ) (y' : Γ(Y, d ⊓ d')ˣ),
      x' = res h₁ (pullU f _ x) →
      y' = res h₂ (pullU f _ y) →
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          c ⊓ d ⊓ (c' ⊓ d') ≤ c ⊓ c') x' *
        (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          c ⊓ d ⊓ (c' ⊓ d') ≤ d ⊓ d') y')⁻¹ =
      res h₃ (pullU f _
        (res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          a ⊓ b ⊓ (a' ⊓ b') ≤ a ⊓ a') x *
        (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          a ⊓ b ⊓ (a' ⊓ b') ≤ b ⊓ b') y)⁻¹)) := by
    rintro a b a' b' c d c' d' h₁ h₂ h₃ x y _ _ rfl rfl
    simp only [map_mul, map_inv, LB.pullU_res, LB.res_res]
  exact key _ _ _ _ _ _ _ (LB.lcg_pull M f p.1 q.1) (LB.lcg_pull L f p.2 q.2)
end GlobalTheory
