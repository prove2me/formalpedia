-- Prove2me | solution 1 for GlobalTheory.RowLaw.CvDiv.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T06:14:36.807156+00:00
-- url     : https://prove2.me/submissions/b222c04a-5657-4c35-84e3-9d3aa3166f6c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedFormalGroupCurveLogarithmsAddSubgroupRescaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedCurveLogarithmsClosedUnderTadicLimitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CurveLogarithmsInvNatCastSmulMem
import Theorems.Thm_GlobalTheory_RowLaw_CvDiv_coeff_alongCv_le
import Theorems.Thm_GlobalTheory_RowLaw_CvDiv_coeff_alongCv_smul
import Theorems.Thm_GlobalTheory_RowLaw_CvDiv_isCv_smul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_constantCoeff_sg
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
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.CvDiv
variable {C : Type} [Field C]
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
namespace GlobalTheory.RowLaw.CvDiv
theorem _root_.solution {X : RawChart C d I κ} {V : VF C} (hX : RLaw X V) (g : Fin 2) {c : C} (hc : V.Ge 0 c)
    (m : ℕ) {a : (κ → PowerSeries C) × (JJ I g → PowerSeries C)} (ha : a ∈ Cv X V g)
    (hv : ∀ i, ∀ k < m, PowerSeries.coeff k (a.1 i) = 0) :
    ∃ b ∈ Cv X V g, ∀ k ≤ m, (∀ i, PowerSeries.coeff k (b.1 i) = c * PowerSeries.coeff k (a.1 i)) ∧
      ∀ q, PowerSeries.coeff k (b.2 q) = c * PowerSeries.coeff k (a.2 q) := by
  classical
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := ha
  have hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := fun i => by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hX.lin i 0 (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]
  have hlg1 : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (X.lg i) = if j = i then 1 else 0 := fun i j => by
    rw [hX.lin i _ (by rw [Finsupp.degree_single]), MvPowerSeries.coeff_X]
    by_cases hji : j = i
    · rw [hji, if_pos rfl, if_pos rfl]
    · rw [if_neg hji, if_neg]
      intro h
      exact hji (Finsupp.single_left_injective one_ne_zero h)
  have h0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => (hγ i).1
  have hord : ∀ k, k < m → ∀ i, PowerSeries.coeff k (γ i) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk i
      have e1 := coeff_alongCv_le h0 (fun i m' hm' => ih m' hm' (by omega) i) (hlg0 i)
      rw [h1 i, hv i k hk] at e1
      simp only [hlg1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e1
      exact e1.symm
  refine ⟨(fun i => alongCv (c • γ) (X.lg i), fun q => (c • lam) q - alongCv (c • γ) (X.sg (X.u (1 - g) q))),
    ⟨c • γ, c • lam, isCv_smul hc hγ, isCv_smul hc hlam, fun _ => rfl, fun _ => rfl⟩, fun k hk => ⟨fun i => ?_, fun q => ?_⟩⟩
  · rw [← h1 i]
    exact coeff_alongCv_smul c h0 (fun i m' hm' => hord m' (by omega) i) (hlg0 i)
  · rw [h2 q]
    simp only [map_sub, Pi.smul_apply, PowerSeries.coeff_smul, smul_eq_mul]
    rw [coeff_alongCv_smul c h0 (fun i m' hm' => hord m' (by omega) i) (X.constantCoeff_sg (hX.axes 0) _)]
    ring
end GlobalTheory.RowLaw.CvDiv
