-- Prove2me | solution 1 for GlobalTheory.Per.exists_div_X_sub_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:01:03.71345+00:00
-- url     : https://prove2.me/submissions/928eae8b-ea02-4955-a266-ff5d6cfc0650

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ProdPrimePowDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory GlobalTheory.Per
open PowerSeries
namespace GlobalTheory.Per
theorem _root_.solution {O : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : O) (hx : ¬ IsUnit x) (a : PowerSeries O) :
    ∃ (b : PowerSeries O) (c : O), a = (PowerSeries.X - PowerSeries.C x) * b + PowerSeries.C c := by
  have hres : (PowerSeries.X - PowerSeries.C x : PowerSeries O).map (IsLocalRing.residue O) =
      PowerSeries.X := by
    have hx0 : IsLocalRing.residue O x = 0 :=
      (IsLocalRing.residue_eq_zero_iff x).2 ((IsLocalRing.mem_maximalIdeal x).2 hx)
    rw [map_sub, PowerSeries.map_X, PowerSeries.map_C, hx0, map_zero, sub_zero]
  have hne : (PowerSeries.X - PowerSeries.C x : PowerSeries O).map (IsLocalRing.residue O) ≠ 0 := by
    rw [hres]; exact PowerSeries.X_ne_zero
  obtain ⟨q, r, hdeg, heq⟩ := a.exists_isWeierstrassDivision hne
  change r.degree < ((PowerSeries.X - PowerSeries.C x : PowerSeries O).map
      (IsLocalRing.residue O)).order.toNat at hdeg
  rw [hres, PowerSeries.order_X] at hdeg
  have hr : r = Polynomial.C (r.coeff 0) := by
    have h1 : r.degree < 0 + 1 := by simpa using hdeg
    exact Polynomial.eq_C_of_degree_le_zero (Order.le_of_lt_succ h1)
  refine ⟨q, r.coeff 0, ?_⟩
  rw [heq, hr, Polynomial.coe_C, Polynomial.coeff_C_zero]
end GlobalTheory.Per
