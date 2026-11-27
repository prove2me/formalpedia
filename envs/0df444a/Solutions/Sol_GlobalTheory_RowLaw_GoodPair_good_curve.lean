-- Prove2me | solution 1 for GlobalTheory.RowLaw.GoodPair.good_curve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T06:22:16.600216+00:00
-- url     : https://prove2.me/submissions/84192c4f-a35d-4361-bf69-9ac37821d659

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AddCurveStableOfIntegralGaugedFormalGroupLaw
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FrobeniusMemTypicalCurveSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GoodCurvesPairingMemMaxIdeal
import Theorems.Thm_GlobalTheory_RowLaw_GoodPair_ee_zero
import Theorems.Thm_GlobalTheory_RowLaw_GoodPair_ee_one
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_tyS_of_ne
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_tyS_pow
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


attribute [local simp] GlobalTheory.RowLaw.GoodPair.ee_zero
attribute [local simp] GlobalTheory.RowLaw.GoodPair.ee_one

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowLaw.CvEnd GlobalTheory.RowVal MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GoodPair
variable {C : Type} [Field C]
variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {X : RawChart C d I κ}
namespace GlobalTheory.RowLaw.GoodPair
theorem _root_.solution [NeZero d] {g : Fin 2} (H : X.CartHyp V g) {a : ZMod d} {w : I g → C}
    {x : ℕ → I g ⊕ JJ I g → C} (hx : (RawChart.cart H).Good a w x) :
    ∃ γ : κ → PowerSeries C, IsCv V γ ∧
      (∀ i n, V.l ∣ n → n < V.l * V.l → PowerSeries.coeff n (alongCv γ (X.lg i)) = 0) ∧
      (∀ i, PowerSeries.coeff 1 (alongCv γ (X.lg i)) = ∑ c, X.u g c i * w c) ∧
      (∀ i, (V.l : C) * PowerSeries.coeff (V.l * V.l) (alongCv γ (X.lg i)) =
        ∑ c, X.u g c i * (RawChart.cart H).V2 x c) ∧
      ∀ q : I (1 - g), ∃ z, V.Ge 0 z ∧ (V.l : C) * PowerSeries.coeff V.l (alongCv γ (X.sg (X.u (1 - g) q))) =
        (V.l : C) * z - (RawChart.cart H).c0' x q := by
  have hl := V.l_prime
  have hl2 := hl.two_le
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ : x ∈ X.TySet V g := hx.1.1
  have c0 : ∀ y : ℕ → C, PowerSeries.coeff 1 (tyS V.l y) = y 0 := fun y => by
    simpa using coeff_tyS_pow hl2 y 0
  have c1 : ∀ y : ℕ → C, PowerSeries.coeff V.l (tyS V.l y) = y 1 := fun y => by
    simpa using coeff_tyS_pow hl2 y 1
  have c2 : ∀ y : ℕ → C, PowerSeries.coeff (V.l * V.l) (tyS V.l y) = y 2 := fun y => by
    simpa [pow_two] using coeff_tyS_pow hl2 y 2
  refine ⟨γ, hγ, fun i n hd hn => ?_, fun i => ?_, fun i => ?_, fun q => ⟨_, (hlam q).2 V.l, ?_⟩⟩
  · rw [h1, map_sum]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [PowerSeries.coeff_smul]
    by_cases hs : ∃ s, V.l ^ s = n
    · obtain ⟨s, rfl⟩ := hs
      have hs2 : s < 2 := by
        rw [← pow_two] at hn
        exact (Nat.pow_lt_pow_iff_right hl.one_lt).1 hn
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact hl.one_lt.ne' (Nat.dvd_one.1 (by simpa using hd))
      rw [show s = 1 by omega, coeff_tyS_pow hl2, hx.2 c, smul_zero]
    · push Not at hs
      rw [coeff_tyS_of_ne _ _ hs, smul_zero]
  · rw [h1, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [PowerSeries.coeff_smul, c0, hx.1.2.1]
    rfl
  · rw [h1, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [PowerSeries.coeff_smul, c2, smul_eq_mul, Cart.V2]
    ring
  · have e := congrArg (PowerSeries.coeff V.l) (h2 q)
    rw [c1, map_add, map_sub, map_sum, Finset.sum_eq_zero, add_zero] at e
    · rw [Cart.c0', e]; ring
    · intro c _
      split_ifs
      · rw [PowerSeries.coeff_smul, c1, hx.2 c, smul_zero]
      · exact map_zero _
end GlobalTheory.RowLaw.GoodPair
