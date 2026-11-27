-- Prove2me | solution 1 for GlobalTheory.RowLaw.hAt_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T06:13:45.591092+00:00
-- url     : https://prove2.me/submissions/35e8a9c1-643a-48ae-8f87-4da18c023d55

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGaugeBilinearTermOfTypeNe
import Theorems.Thm_GlobalTheory_RowLaw_coeff_subst_eq_zero_of_lt_order
import Theorems.Thm_GlobalTheory_RowLaw_subst_sum_smul
import Theorems.Thm_GlobalTheory_RowLaw_bexp_inj
import Theorems.Thm_GlobalTheory_RowLaw_eq_bexp
import Theorems.Thm_GlobalTheory_RowLaw_X_mul_X_eq
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
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
noncomputable section
open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw
variable {C : Type} [Field C]
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
namespace GlobalTheory.RowLaw
theorem _root_.solution (Y : RawChart C d I κ)
    (hax : ∀ (g : Fin 2) (e : Fin 2 × κ →₀ ℕ), (∀ s ∈ e.support, s.1 ≠ g) → coeff e Y.h = 0)
    {τ : Type} {a b : κ → MvPowerSeries τ C} (ha : ∀ x, constantCoeff (a x) = 0)
    (hb : ∀ x, constantCoeff (b x) = 0) :
    ((3 : ℕ) : ℕ∞) ≤ (hAt Y a b - ∑ p : κ × κ, coeff (bexp p.1 p.2) Y.h • (a p.1 * b p.2)).order := by
  have hc : ∀ p : Fin 2 × κ, constantCoeff (if p.1 = 0 then a p.2 else b p.2) = 0 := fun p => by
    split_ifs
    · exact ha _
    · exact hb _
  have hs := hasSubst_of_constantCoeff_zero hc
  have key := coeff_subst_eq_zero_of_lt_order hc (n := 3)
    (f := Y.h - ∑ p : κ × κ, coeff (bexp p.1 p.2) Y.h • (X (0, p.1) * X (1, p.2))) (by
      intro e he
      rw [map_sub, map_sum, sub_eq_zero]
      simp only [coeff_smul, X_mul_X_eq, coeff_monomial]
      by_cases h : ∃ x y, e = bexp x y
      · obtain ⟨x, y, rfl⟩ := h
        rw [Finset.sum_eq_single (x, y)]
        · simp
        · intro p _ hp
          rw [if_neg, mul_zero]
          intro h
          exact hp (Prod.ext (bexp_inj h).1.symm (bexp_inj h).2.symm)
        · simp
      · push Not at h
        rw [Finset.sum_eq_zero fun p _ => by rw [if_neg (h _ _), mul_zero]]
        by_cases h0 : ∀ s ∈ e.support, s.1 ≠ 0
        · exact hax 0 e h0
        by_cases h1 : ∀ s ∈ e.support, s.1 ≠ 1
        · exact hax 1 e h1
        push Not at h0 h1
        obtain ⟨⟨g, x⟩, hx, rfl⟩ := h0
        obtain ⟨⟨g', y⟩, hy, rfl⟩ := h1
        exact absurd (eq_bexp e he hx hy) (h x y))
  rw [subst_sub hs, subst_sum_smul hs] at key
  simpa only [subst_mul hs, subst_X hs, hAt, if_true, one_ne_zero, if_false] using key
end GlobalTheory.RowLaw
