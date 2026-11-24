-- Prove2me | solution 1 for GlobalTheory.DivConst.exists_genPull_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:51:30.047445+00:00
-- url     : https://prove2.me/submissions/f208a600-367e-41c8-9eee-2e7037618e3a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlobalGeneratorDivBaseUnitEqGeneric
import Theorems.Thm_GlobalTheory_DivConst_gs_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.DivConst
namespace GlobalTheory.DivConst
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (X : Over (Sp R)) (Y : Scheme.{0}) (φ : Y ⟶ X.left) (p : Y ⟶ Sp K), φ ≫ X.hom = p ≫ spMap (algebraMap R K) → ∀ (M : LB X.left) (c : LB.Gen (M.pull φ)) (a : Kˣ) (b : Rˣ), algebraMap R K (b : R) = (a : K) → ∀ (u : LB.Gen M), u.IsGen → (∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), φ (r z) ∈ M.U i → (gm (r ≫ φ) z (M.U i) (u.s i)).val = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull φ).U fun _ => i) (c.s fun _ => i)).val) → ∃ r' : LB.Gen M, r'.IsGen ∧ LB.genPull M r' φ = c := by
  intro R K _ _ _ X Y φ p w M c a b hab u hu H
  let β : Γ(X.left, ⊤)ˣ := Units.map (X.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toMonoidHom b
  refine ⟨⟨fun i => u.s i * (res le_top β)⁻¹⟩, fun i j => unit_ext fun x hx => ?_, ?_⟩
  · have e := congrArg (gm (𝟙 X.left) x (M.U i ⊓ M.U j)) (hu i j)
    simp only [map_mul, map_inv] at e ⊢
    rw [e, gm_res _ x _ hx (res le_top β), gm_res _ x _ hx (res le_top β), gm_res _ x _ hx.1 β,
      gm_res _ x _ hx.2 β, mul_assoc]
  · obtain ⟨s⟩ := c
    refine congrArg LB.Gen.mk (funext fun j => unit_ext fun y hy => ?_)
    have hy' : φ y ∈ M.U (j PUnit.unit) := mem_pull.1 hy
    refine (gm_res _ y _ hy _).trans ((gm_pull (𝟙 Y) φ y _ hy' _).trans ?_)
    have e := H (j PUnit.unit) Y (𝟙 Y) y hy'
    have e' : (gm (𝟙 Y ≫ φ) y ⊤ β).val = gs (𝟙 Y ≫ p) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) := by
      rw [← gs_unit _ y ⊤ trivial, ← hab, Category.id_comp, Category.id_comp]
      exact gs_const _ w y b
    rw [← e', ← Units.val_mul] at e
    rw [map_mul, map_inv, gm_res (𝟙 Y ≫ φ) y _ hy' β, Units.ext e, mul_inv_cancel_comm]
    rfl
end GlobalTheory.DivConst
