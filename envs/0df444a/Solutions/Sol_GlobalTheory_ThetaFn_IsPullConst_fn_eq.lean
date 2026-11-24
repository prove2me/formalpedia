-- Prove2me | solution 1 for GlobalTheory.ThetaFn.IsPullConst.fn_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:56:06.310329+00:00
-- url     : https://prove2.me/submissions/087b40c2-0ec6-4a34-8e23-b908970813d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_mem_pairChart_iff
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_exists_chart
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_valueRules
import Theorems.Thm_GlobalTheory_ThetaFn_IsFnAt_twistPull
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
theorem _root_.solution (hL : L.IsLB) {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A}
    {hm : ψ ≫ snd T A = m} {Φ : (Fin g → ℂ) → Fin g → ℂ}
    (hψ : ∀ z, exAt u p z ≫ ψ.left = exAt u p (Φ z)) {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} {c : ℂ}
    (hc : IsPullConst u p Φ a b α c) {s : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)}
    (ht : IsTwistPull A L ψ m hm a b α s s') {θ θ' : (Fin g → ℂ) → ℂ}
    (h : IsFnAt u p b s θ) (h' : IsFnAt u p a s' θ') (z : Fin g → ℂ) : θ' z = c * θ (Φ z) := by
  obtain ⟨i, hi⟩ := exists_chart u valueRules hL z
  obtain ⟨i', hi'⟩ := exists_chart u valueRules hL (Φ z)
  have hΦ : exAt u p z ≫ m.left = (u.ex (Φ z)).left := by
    rw [← hm, Over.comp_left, ← Category.assoc, hψ, exAt_snd]
  have hj := (exAt_mem_pairChart_iff hΦ ![i, i']).2 ⟨hi, hi'⟩
  have e := h.twistPull h' ht (hψ z) _ hj
  refine mul_right_cancel₀ (zpow_ne_zero a (u.fr_ne i z hi)) (e.trans ?_)
  rw [mul_left_comm, hc _ z hj]
  exact (mul_left_comm _ _ _).trans (_root_.mul_assoc _ _ _).symm
end IsPullConst
end GlobalTheory.ThetaFn
