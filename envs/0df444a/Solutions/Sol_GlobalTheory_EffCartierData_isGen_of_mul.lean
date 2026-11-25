-- Prove2me | solution 1 for GlobalTheory.EffCartierData.isGen_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:17:25.280703+00:00
-- url     : https://prove2.me/submissions/7fd3ace4-0a3c-4e3c-be4d-5f245e082121

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mul
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mul_right_cancel
import Theorems.Thm_GlobalTheory_Cartier_val_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_dg


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
open GlobalTheory
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open Cartier
open GlobalTheory.EffCartierData
variable {X Y Z : Scheme.{0}}
variable (D D' : EffCartierData X)
namespace GlobalTheory.EffCartierData
theorem _root_.solution {N L M : LB X} {a : L.Sec} {b : M.Sec} {c : N.Sec} (ha : IsRegularSec a)
    (hb : IsRegularSec b) (w : LB.Gen (LB.div (LB.div N L) M))
    (H : ∀ (i : N.ι) (j : L.ι) (k : M.ι) {W : X.Opens} (h : W ≤ N.U i ⊓ L.U j ⊓ M.U k),
      resG X (h.trans (inf_le_left.trans inf_le_left)) (c.f i) =
        (res h (w.s ((i, j), k)) : Γ(X, W)ˣ) *
          (resG X (h.trans (inf_le_left.trans inf_le_right)) (a.f j) *
            resG X (h.trans inf_le_right) (b.f k))) : w.IsGen := by
  rintro ⟨⟨i, j⟩, k⟩ ⟨⟨i', j'⟩, k'⟩
  have key : ∀ {W : X.Opens} (h : W ≤ N.U i ⊓ L.U j ⊓ M.U k) (h' : W ≤ N.U i' ⊓ L.U j' ⊓ M.U k'),
      res h (w.s ((i, j), k)) =
        res (le_inf (h.trans (inf_le_left.trans inf_le_left))
          (h'.trans (inf_le_left.trans inf_le_left))) (N.g i i') *
        (res (le_inf (h.trans (inf_le_left.trans inf_le_right))
          (h'.trans (inf_le_left.trans inf_le_right))) (L.g j j'))⁻¹ *
        (res (le_inf (h.trans inf_le_right) (h'.trans inf_le_right)) (M.g k k'))⁻¹ *
        res h' (w.s ((i', j'), k')) := by
    intro W h h'
    rw [mul_right_comm, mul_right_comm _ _⁻¹, eq_mul_inv_iff_mul_eq, eq_mul_inv_iff_mul_eq]
    refine Units.ext ((((ha j').resG (h'.trans (inf_le_left.trans inf_le_right))).mul
      ((hb k').resG (h'.trans inf_le_right))).mul_right_cancel ?_)
    have e₁ := H i j k h
    have e₂ := H i' j' k' h'
    rw [sec_compat c i i' _ (h'.trans (inf_le_left.trans inf_le_left)), e₂,
      sec_compat a j j' _ (h'.trans (inf_le_left.trans inf_le_right)),
      sec_compat b k k' _ (h'.trans inf_le_right)] at e₁
    simp only [Units.val_mul, val_res] at e₁ ⊢
    linear_combination -e₁
  refine (key inf_le_left inf_le_right).trans (congrArg (· * _) (congrArg (· * _) ?_))
  exact (LB.res_dg N L (i, j) (i', j') _).symm
end GlobalTheory.EffCartierData
