-- Prove2me | solution 1 for GlobalTheory.RowVal.MapSumDiagonal.split_abstract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T06:19:16.277785+00:00
-- url     : https://prove2.me/submissions/f73a1dae-0747-4bd1-82a0-cac8da20d3eb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeBiadditiveSymmAdjointIntegralEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DiagonalSplit
import Theorems.Thm_GlobalTheory_RowVal_MapSumDiagonal_map_sum_of_pred
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
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
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowVal GlobalTheory.RowVal.MapSumDiagonal
namespace GlobalTheory.RowVal.MapSumDiagonal
theorem _root_.solution {R Q Orb : Type} [Ring R] [AddCommGroup Q] [Fintype Orb] (P : R → Prop) (h : R → R → Q)
    (P0 : P 0) (Padd : ∀ a b, P a → P b → P (a + b)) (Pmul : ∀ a b, P a → P b → P (a * b))
    (h0 : ∀ a, h a 0 = 0 ∧ h 0 a = 0)
    (hl : ∀ a a' b, P a → P a' → P b → h (a + a') b = h a b + h a' b)
    (hr : ∀ a a' b, P a → P a' → P b → h b (a + a') = h b a + h b a')
    (hs : ∀ a b, P a → P b → h b a = h a b)
    (W W' : R) (hW : P W) (hW' : P W') (hadj : ∀ a b, P a → P b → h (W * a) b = h a (W' * b))
    (hWW : W + W' = 1) (π : Orb → Fin 2 → R) (hπ : ∀ o g, P (π o g))
    (horth : ∀ o g o' g', ¬ (o = o' ∧ g' = 1 - g) → h (π o g) (W * π o' g') = 0) :
    ∑ o, h (π o 0) (π o 1) = h (∑ o, ∑ g, π o g) (W * ∑ o, ∑ g, π o g) := by
  classical
  have hWπ : ∀ o g, P (W * π o g) := fun o g => Pmul _ _ hW (hπ o g)
  have e1 : (∑ o, ∑ g, π o g) = ∑ p : Orb × Fin 2, π p.1 p.2 := by rw [Fintype.sum_prod_type]
  have hB : P (∑ p : Orb × Fin 2, W * π p.1 p.2) :=
    (map_sum_of_pred P (fun _ => (0 : Q)) P0 Padd rfl (by simp) _ _ (fun p : Orb × Fin 2 => hWπ p.1 p.2)).1
  rw [e1, Finset.mul_sum]
  rw [(map_sum_of_pred P (fun a => h a (∑ p : Orb × Fin 2, W * π p.1 p.2)) P0 Padd (h0 _).2
    (fun a b ha hb => hl a b _ ha hb hB) Finset.univ (fun p : Orb × Fin 2 => π p.1 p.2)
    (fun p => hπ p.1 p.2)).2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun o _ => ?_
  have e2 : ∀ g, h (π o g) (∑ p : Orb × Fin 2, W * π p.1 p.2) = h (π o g) (W * π o (1 - g)) := by
    intro g
    rw [(map_sum_of_pred P (fun a => h (π o g) a) P0 Padd (h0 _).1
      (fun a b ha hb => hr a b _ ha hb (hπ o g)) Finset.univ (fun p : Orb × Fin 2 => W * π p.1 p.2)
      (fun p => hWπ p.1 p.2)).2]
    refine Finset.sum_eq_single (o, 1 - g) ?_ (by simp)
    intro p _ hp
    apply horth
    rintro ⟨h1, h2⟩
    exact hp (Prod.ext h1.symm h2)
  rw [Fin.sum_univ_two, e2, e2, sub_zero, sub_self, ← hs _ _ (hπ o 1) (hWπ o 0),
    hadj _ _ (hπ o 0) (hπ o 1), ← hr _ _ _ (hWπ o 1) (Pmul _ _ hW' (hπ o 1)) (hπ o 0), ← add_mul, hWW, one_mul]
end GlobalTheory.RowVal.MapSumDiagonal
