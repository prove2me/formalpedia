-- Prove2me | solution 1 for GlobalTheory.GenChar.exists_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:58:07.323634+00:00
-- url     : https://prove2.me/submissions/2ddfc367-e2b4-4cdb-9309-baed3b16755b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralCharacterGeneralizedEigen
import Theorems.Thm_GlobalTheory_GenChar_step
import Theorems.Thm_GlobalTheory_GenChar_ge_of_eigen
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.GenChar
namespace GlobalTheory.GenChar
theorem _root_.solution : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (κ : Type) [Fintype κ] [DecidableEq κ] (L : O →+* Matrix κ κ C), (∀ x i j, V.Ge 0 (L x i j)) → ∀ (χ : O → C) (w : κ → C), w ≠ 0 → (∀ x, ∃ k : ℕ, ((L x - χ x • (1 : Matrix κ κ C)) ^ k).mulVec w = 0) → ∃ ψ : O →+* C, (∀ x, ψ x = χ x) ∧ ∀ x, V.Ge 0 (ψ x) := by
  intro C _ V O _ κ _ _ L hL χ w hw hn
  set n : O → Matrix κ κ C := fun x => L x - χ x • (1 : Matrix κ κ C) with hndef
  have hLc : ∀ x y, Commute (L x) (L y) := fun x y => (Commute.all x y).map L
  have hc : ∀ x y, Commute (n x) (n y) := fun x y =>
    ((hLc x y).sub_right ((Commute.one_right _).smul_right _)).sub_left
      ((Commute.one_left _).smul_left _)
  have heig : ∀ (x : O) (u : κ → C), (n x).mulVec u = 0 → (L x).mulVec u = χ x • u := by
    intro x u h
    simp only [hndef, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    exact sub_eq_zero.mp h
  have three : ∀ x y z : O, ∃ u : κ → C, u ≠ 0 ∧ (L x).mulVec u = χ x • u ∧
      (L y).mulVec u = χ y • u ∧ (L z).mulVec u = χ z • u := by
    intro x y z
    obtain ⟨u₁, h1, h1n, h1x, -⟩ := step n hc w hw hn x
    obtain ⟨u₂, h2, h2n, h2y, h2p⟩ := step n hc u₁ h1 h1n y
    obtain ⟨u₃, h3, -, h3z, h3p⟩ := step n hc u₂ h2 h2n z
    exact ⟨u₃, h3, heig _ _ (h3p _ (h2p _ h1x)), heig _ _ (h3p _ h2y), heig _ _ h3z⟩
  have h1 : χ 1 = 1 := by
    obtain ⟨u, hu, h, -, -⟩ := three 1 1 1
    rw [map_one, Matrix.one_mulVec] at h
    apply smul_left_injective C hu
    simpa using h.symm
  have h0 : χ 0 = 0 := by
    obtain ⟨u, hu, h, -, -⟩ := three 0 0 0
    rw [map_zero, Matrix.zero_mulVec] at h
    apply smul_left_injective C hu
    simpa using h.symm
  have hadd : ∀ x y, χ (x + y) = χ x + χ y := by
    intro x y
    obtain ⟨u, hu, hx, hy, h⟩ := three x y (x + y)
    rw [map_add, Matrix.add_mulVec, hx, hy, ← add_smul] at h
    exact smul_left_injective C hu h.symm
  have hmul : ∀ x y, χ (x * y) = χ x * χ y := by
    intro x y
    obtain ⟨u, hu, hx, hy, h⟩ := three x y (x * y)
    rw [map_mul, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_smul, hx, smul_smul, mul_comm (χ y)] at h
    exact smul_left_injective C hu h.symm
  refine ⟨⟨⟨⟨χ, h1⟩, hmul⟩, h0, hadd⟩, fun _ => rfl, fun x => ?_⟩
  obtain ⟨u, hu, h, -, -⟩ := three x x x
  exact ge_of_eigen V (L x) (hL x) (χ x) u hu h
end GlobalTheory.GenChar
