-- Prove2me | solution 1 for GlobalTheory.corr_of_corr_pullGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:52:55.200949+00:00
-- url     : https://prove2.me/submissions/e35ad163-05c3-4354-b88b-eac039a47af6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CorrOfGenericOfIsSeparated
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_pullU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_ts_pullGen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution {X Y Z : Scheme.{u}} (L : LB X) {I I' : Type u} [Fintype I] [Fintype I']
    (φ : I → (Y ⟶ X)) (ε : I → ℤ) (φ' : I' → (Y ⟶ X)) (ε' : I' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (h : Z ⟶ Y)
    (hinj : ∀ U, Function.Injective (h.app U).hom) (hc : ∀ a b : Y ⟶ X, h ≫ a = h ≫ b → a = b)
    (H : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t h) (LB.pullGen L _ _ t' h)) :
    LB.Gen.Corr L _ _ _ _ t t' := by
  intro j j' c₁ c₂ c₃
  have e := H j j' (fun a b e => c₁ a b (hc _ _ e)) (fun a b e => c₂ a b (hc _ _ e))
    (fun a b e => c₃ a b (hc _ _ e))
  have le : h ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ' j') ≤
      LB.wchart L (fun k => h ≫ φ k) j ⊓ LB.wchart L (fun k => h ≫ φ' k) j' := fun _ hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k⟩
  have e' := congrArg (res le) e
  change res le (res _ (LB.ts (LB.pullGen L _ _ t h) j)) = res le (res _ (LB.ts (LB.pullGen L _ _ t' h) j')) at e'
  rw [LB.ts_pullGen, LB.ts_pullGen] at e'
  simp only [LB.res_res] at e'
  refine Units.map_injective (f := (h.app (LB.wchart L φ j ⊓ LB.wchart L φ' j')).hom.toMonoidHom)
    (hinj _) ?_
  exact (LB.pullU_res h _ _).trans (e'.trans (LB.pullU_res h _ _).symm)
end GlobalTheory
