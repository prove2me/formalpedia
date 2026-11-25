-- Prove2me | solution 1 for GlobalTheory.ThetaFn.IsPullConst.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:25:45.486566+00:00
-- url     : https://prove2.me/submissions/c4587647-5e27-40a4-b3a7-ab09f0017d8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_mem_pairChart_iff
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
theorem _root_.solution (hL : L.IsLB) {m : T ⊗ A ⟶ A} {Φ : (Fin g → ℂ) → Fin g → ℂ}
    (hΦ : ∀ z, exAt u p z ≫ m.left = (u.ex (Φ z)).left) {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} {c c' : ℂ}
    (hc : IsPullConst u p Φ a b α c) (hc' : IsPullConst u p Φ a b α c') : c = c' := by
  obtain ⟨i, hi⟩ := exists_chart u valueRules hL 0
  obtain ⟨i', hi'⟩ := exists_chart u valueRules hL (Φ 0)
  have hj := (exAt_mem_pairChart_iff (hΦ 0) ![i, i']).2 ⟨hi, hi'⟩
  exact mul_right_cancel₀ (zpow_ne_zero a (u.fr_ne i 0 hi)) ((hc _ 0 hj).symm.trans (hc' _ 0 hj))
end IsPullConst
end GlobalTheory.ThetaFn
