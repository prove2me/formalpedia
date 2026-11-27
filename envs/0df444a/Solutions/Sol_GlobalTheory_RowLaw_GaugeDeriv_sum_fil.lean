-- Prove2me | solution 1 for GlobalTheory.RowLaw.GaugeDeriv.sum_fil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T06:14:48.440028+00:00
-- url     : https://prove2.me/submissions/c52020a1-07d3-4f67-b46c-eb3173b5c61c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeDerivEqPairingOfIntegralGaugedLaw
import Theorems.Thm_GlobalTheory_RowLaw_GaugeDeriv_coeff_subst_tyS
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
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
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GaugeDeriv
variable {C : Type} [Field C] {V : VF C} {σ τ υ : Type}
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {Y : RawChart C d I κ}
variable {I₁ J₁ : Type} [Fintype I₁] [Fintype J₁] {G : Cart V d I₁ J₁} (S : Sys G) {t : I₁ → MvPowerSeries I₁ C}
  (ht : S.IsT t)
include ht
namespace GlobalTheory.RowLaw.GaugeDeriv
theorem _root_.solution (q : J₁) :
    ∑ c, subst (fun _ : Unit => t c) (tyS V.l fun s => S.cur c s (Sum.inr q)) = -S.ze t q := by
  classical
  ext μ
  rw [map_sum, map_neg]
  simp only [coeff_subst_tyS V.l_prime.two_le (ht.1 _)]
  rw [Finset.sum_comm]
  show _ = -(-(∑ s ∈ Finset.Icc 1 μ.degree, ∑ c, S.be c s q * coeff μ (t c ^ (V.l ^ s))))
  rw [neg_neg]
  symm
  refine Finset.sum_subset (fun s hs => ?_) fun s hs hs' => ?_
  · rw [Finset.mem_Icc] at hs
    rw [Finset.mem_range]
    omega
  · rw [Finset.mem_Icc] at hs'
    rw [Finset.mem_range] at hs
    have : s = 0 := by omega
    subst this
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Sys.be, (S.curve c).2.1]
    simp
end GlobalTheory.RowLaw.GaugeDeriv
