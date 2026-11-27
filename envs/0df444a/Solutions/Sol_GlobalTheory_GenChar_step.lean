-- Prove2me | solution 1 for GlobalTheory.GenChar.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:24:49.351964+00:00
-- url     : https://prove2.me/submissions/8853aebe-5916-45e1-b1cb-2f7d89f61fde

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralCharacterGeneralizedEigen
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.GenChar
namespace GlobalTheory.GenChar
theorem _root_.solution {C : Type} [Field C] {O κ : Type} [Fintype κ] [DecidableEq κ]
    (n : O → Matrix κ κ C) (hc : ∀ x y, Commute (n x) (n y)) (w : κ → C) (hw : w ≠ 0)
    (hn : ∀ x, ∃ k : ℕ, ((n x) ^ k).mulVec w = 0) (x₀ : O) :
    ∃ u : κ → C, u ≠ 0 ∧ (∀ x, ∃ k : ℕ, ((n x) ^ k).mulVec u = 0) ∧ (n x₀).mulVec u = 0 ∧
      ∀ y, (n y).mulVec w = 0 → (n y).mulVec u = 0 := by
  classical
  have hk := Nat.find_spec (hn x₀)
  have hk0 : Nat.find (hn x₀) ≠ 0 := by
    intro h
    rw [h, pow_zero, Matrix.one_mulVec] at hk
    exact hw hk
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hlt : ¬ ((n x₀) ^ j).mulVec w = 0 := Nat.find_min (hn x₀) (by omega)
  have key : ∀ (y : O) (k : ℕ), ((n y) ^ k).mulVec w = 0 →
      ((n y) ^ k).mulVec (((n x₀) ^ j).mulVec w) = 0 := by
    intro y k h
    rw [Matrix.mulVec_mulVec, ((hc y x₀).pow_pow k j).eq, ← Matrix.mulVec_mulVec, h,
      Matrix.mulVec_zero]
  refine ⟨((n x₀) ^ j).mulVec w, hlt, fun x => ?_, ?_, fun y hy => ?_⟩
  · obtain ⟨k, h⟩ := hn x
    exact ⟨k, key x k h⟩
  · rw [Matrix.mulVec_mulVec, ← pow_succ']
    rw [hj] at hk
    exact hk
  · have := key y 1 (by rwa [pow_one])
    rwa [pow_one] at this
end GlobalTheory.GenChar
