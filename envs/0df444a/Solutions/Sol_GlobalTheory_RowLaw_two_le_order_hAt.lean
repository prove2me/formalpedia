-- Prove2me | solution 1 for GlobalTheory.RowLaw.two_le_order_hAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T06:18:47.754881+00:00
-- url     : https://prove2.me/submissions/46cb0d94-4835-46d4-82d5-296ab4766dda

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGaugeBilinearTermOfTypeNe
import Theorems.Thm_GlobalTheory_RowLaw_hAt_order
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw
variable {C : Type} [Field C]
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
variable {Y : RawChart C d I κ} {V : VF C}
namespace GlobalTheory.RowLaw
theorem _root_.solution (h : RLaw Y V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ x, constantCoeff (a x) = 0) (hb : ∀ x, constantCoeff (b x) = 0) (e : τ →₀ ℕ)
    (he : e.degree < 2) : coeff e (hAt Y a b) = 0 := by
  have h3 := coeff_of_lt_order (d := e) (lt_of_lt_of_le (by exact_mod_cast (by omega : e.degree < 3))
    (hAt_order Y h.axes ha hb))
  rw [map_sub, sub_eq_zero, map_sum] at h3
  rw [h3]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [coeff_smul, coeff_of_lt_order (d := e), mul_zero]
  refine lt_of_lt_of_le ?_ le_order_mul
  refine lt_of_lt_of_le ?_ (add_le_add (one_le_order_iff_constCoeff_eq_zero.2 (ha _))
    (one_le_order_iff_constCoeff_eq_zero.2 (hb _)))
  exact_mod_cast he
end GlobalTheory.RowLaw
