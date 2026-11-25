-- Prove2me | solution 1 for GlobalTheory.TorsionIntegral.corr_of_val_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:30:03.811695+00:00
-- url     : https://prove2.me/submissions/544d9f4c-41ce-42f2-a1ea-94e2620cf81f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorsionPointsIntegral
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory
open GlobalTheory.TorsionIntegral
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace GlobalTheory.TorsionIntegral
theorem _root_.solution (hL : L.IsLB) (φ : Z ⟶ Y) (z : Z)
    (hd : ∀ (U : Y.Opens) (y : Y), y ∈ U → φ z ∈ U)
    (hi : ∀ (U : Y.Opens), φ z ∈ U → Function.Injective (gm φ z U))
    (he : ∀ ψ ψ' : Y ⟶ X, φ ≫ ψ = φ ≫ ψ' → ψ = ψ')
    {ψ : K → (Y ⟶ X)} {ε : K → ℤ} {ψ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L ψ ε)} {t' : LB.Gen (LB.LinComb L ψ' ε')}
    (h : ∀ J, Good L z J → val t φ z J = val t' φ z J) : LB.Gen.Corr L ψ ε ψ' ε' t t' := by
  intro j j' c₁ c₂ c₃
  refine unit_ext fun y hy => congrArg _ ?_
  have hz := hd _ y hy
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (fun k => φ ≫ Sum.elim ψ ψ' k) (Sum.elim j j') (by
    rintro (a | a) (b | b) e
    exacts [c₁ a b (he _ _ e), c₃ a b (he _ _ e), (c₃ b a (he _ _ e).symm).symm, c₂ a b (he _ _ e)]) (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 hz.1 a, Set.mem_iInter.1 hz.2 a])
  have := h J hJ
  rw [val_of t _ z J j (fun k => e (.inl k)), val_of t' _ z J j' (fun k => e (.inr k))] at this
  exact hi _ hz ((gm_res _ z _ hz _).trans (this.trans (gm_res _ z _ hz _).symm))
end GlobalTheory.TorsionIntegral
