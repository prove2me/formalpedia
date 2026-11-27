-- Prove2me | solution 1 for GlobalTheory.RowLaw.GaugeDeriv.sg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T06:06:23.129169+00:00
-- url     : https://prove2.me/submissions/1d9df6a7-85e3-48a7-892d-cb436e903b69

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeDerivEqPairingOfIntegralGaugedLaw
import Theorems.Thm_GlobalTheory_RowLaw_GaugeDeriv_coeff_subst_kill
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


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
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GaugeDeriv
variable {C : Type} [Field C] {V : VF C} {σ τ υ : Type}
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {Y : RawChart C d I κ}
namespace GlobalTheory.RowLaw.GaugeDeriv
theorem _root_.solution (v : κ → C) : Y.sg v = -∑ i, v i • subst (pr (X : κ → MvPowerSeries κ C) fun _ => 0)
    (pderiv C ((1 : Fin 2), i) Y.h) := by
  classical
  let e : κ ↪ Fin 2 × κ := ⟨fun x => (0, x), fun x y h => (Prod.mk.inj h).2⟩
  have he : ∀ t, (pr (X : κ → MvPowerSeries κ C) fun _ => 0) t = killCompl e (X t) := by
    rintro ⟨j, i⟩
    fin_cases j
    · exact (killCompl_X (e := e) i).symm
    · show (0 : MvPowerSeries κ C) = _
      rw [killCompl_X_eq_zero]
      rintro ⟨x, hx⟩
      exact absurd (congrArg Prod.fst hx) (show ¬ (0 : Fin 2) = 1 by decide)
  ext μ
  rw [map_neg, map_sum]
  show -∑ i, v i * coeff (μ.mapDomain (fun x : κ => ((0 : Fin 2), x)) + Finsupp.single ((1 : Fin 2), i) 1) Y.h = _
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_smul, coeff_subst_kill e _ _ he, coeff_pderiv, Finsupp.embDomain_notin_range, Finsupp.embDomain_eq_mapDomain]
  · rw [Nat.cast_zero, zero_add, mul_one]
    rfl
  · rintro ⟨x, hx⟩
    exact absurd (congrArg Prod.fst hx) (show ¬ (0 : Fin 2) = 1 by decide)
end GlobalTheory.RowLaw.GaugeDeriv
