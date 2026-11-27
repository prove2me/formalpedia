-- Prove2me | solution 1 for GlobalTheory.RowLaw.AddCurve.subst_killCompl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:40:05.542097+00:00
-- url     : https://prove2.me/submissions/a2befce0-7a5e-4196-8673-da7db44eac50

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AddCurveStableOfIntegralGaugedFormalGroupLaw
import Theorems.Thm_GlobalTheory_RowLaw_AddCurve_subst_eq_zero_of_van
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
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
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.AddCurve
variable {C : Type} [Field C]
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
namespace GlobalTheory.RowLaw.AddCurve
theorem _root_.solution {τ : Type} {γ : κ → MvPowerSeries τ C} (hγ : ∀ s, constantCoeff (γ s) = 0)
    (F : MvPowerSeries (Fin 2 × κ) C) :
    subst γ (killCompl (fstEmb κ) F) = subst (fun p : Fin 2 × κ => if p.1 = 0 then γ p.2 else 0) F := by
  have h0 : ∀ p : Fin 2 × κ, constantCoeff (if p.1 = 0 then γ p.2 else 0) = 0 := by
    intro p
    split_ifs
    · exact hγ _
    · exact map_zero _
  have hS := hasSubst_of_constantCoeff_zero h0
  have hv : Van {p : Fin 2 × κ | p.1 ≠ 0} (F - rename (fstEmb κ) (killCompl (fstEmb κ) F)) := by
    intro ν hν
    have : ν ∈ Set.range (Finsupp.embDomain (fstEmb κ)) := by
      rw [Finsupp.mem_range_embDomain_iff]
      intro w hw
      have h1 : w.1 = 0 := by simpa using hν w hw
      exact ⟨w.2, Prod.ext h1.symm rfl⟩
    obtain ⟨μ, rfl⟩ := this
    rw [map_sub, coeff_embDomain_rename, coeff_killCompl, sub_self]
  have hz := subst_eq_zero_of_van h0 (fun s (hs : s.1 ≠ 0) => if_neg hs) hv
  rw [subst_sub hS, sub_eq_zero] at hz
  rw [hz, rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) hS]
  congr 1
  funext x
  simp only [Function.comp_apply]
  rw [subst_X hS]
  exact (if_pos rfl).symm
end GlobalTheory.RowLaw.AddCurve
