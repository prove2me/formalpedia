-- Prove2me | solution 1 for GlobalTheory.KerPow.HasGen.comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:36:05.12426+00:00
-- url     : https://prove2.me/submissions/7fe177bd-cd7f-4a45-9787-700c6fdaea89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LocGenOfTrivial
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.KerPow
variable {X Y Y' B B' : Scheme.{0}} {L : LB X} {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']
namespace GlobalTheory.KerPow
namespace HasGen
theorem _root_.solution (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {φ'' : K'' → (Y ⟶ X)} {ε'' : K'' → ℤ} (H : HasGen L φ ε) (H' : HasGen L φ' ε')
    (e : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U),
      (∏ k, h (φ k) ^ ε k) * (∏ k, h (φ' k) ^ ε' k)⁻¹ = ∏ k, h (φ'' k) ^ ε'' k) : HasGen L φ'' ε'' := by
  obtain ⟨t, ht⟩ := H
  obtain ⟨t', ht'⟩ := H'
  obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := φ'') (ε' := ε'') (fun U _ h => by
      rw [← e U h, Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib])
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ t'))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ ht'))
  exact ⟨u, hu⟩
end HasGen
end GlobalTheory.KerPow
