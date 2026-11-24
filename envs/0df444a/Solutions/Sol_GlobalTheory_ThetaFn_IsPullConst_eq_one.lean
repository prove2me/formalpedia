-- Prove2me | solution 1 for GlobalTheory.ThetaFn.IsPullConst.eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:29:59.953856+00:00
-- url     : https://prove2.me/submissions/893499a3-f818-4ff4-a3d0-bcba6ca7d9e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_mem_pairChart_iff
import Theorems.Thm_GlobalTheory_ThetaFn_IsPullConst_origin
import Theorems.Thm_GlobalTheory_CubeValues_ex_zero
import Theorems.Thm_GlobalTheory_CubeValues_val_unit_ne_zero
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_exists_chart
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_valueRules
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
variable {u p}
namespace GlobalTheory.ThetaFn
namespace IsPullConst
theorem _root_.solution (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec A))} (hrig : u.IsRig rig)
    {m : T ⊗ A ⟶ A} {Φ : (Fin g → ℂ) → Fin g → ℂ} (h0 : Φ 0 = 0)
    (hΦ : exAt u p 0 ≫ m.left = (u.ex 0).left) {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} {c : ℂ}
    (hc : IsPullConst u p Φ a b α c)
    (hn : ∀ j : Fin 2 → L.ι, ⊤ ≤ exAt u p 0 ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j →
      valAt' (exAt u p 0) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
          valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => j 1) (rig.s fun _ => j 1).val ^ b =
        valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => j 0) (rig.s fun _ => j 0).val ^ a) :
    c = 1 := by
  obtain ⟨i, hi⟩ := exists_chart u valueRules hL 0
  have hj := (exAt_mem_pairChart_iff hΦ fun _ => i).2 ⟨hi, hi⟩
  have e := (hc.origin hrig h0 hΦ _ hj).symm.trans (hn _ hj)
  refine (mul_eq_right₀ (zpow_ne_zero a (val_unit_ne_zero _ valueRules ?_ _))).1 e
  rw [ex_zero] at hi
  exact fun _ hy => Set.mem_iInter.2 fun _ => hi hy
end IsPullConst
end GlobalTheory.ThetaFn
