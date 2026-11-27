-- Prove2me | solution 1 for GlobalTheory.RowLaw.TypPart.coeff_filt_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T06:25:37.539856+00:00
-- url     : https://prove2.me/submissions/779ad324-9aef-46b2-b2a6-b9569810fe6d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedFormalGroupCurveLogarithmsAddSubgroupRescaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedCurveLogarithmsClosedUnderTadicLimits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CurveLogarithmsInvNatCastSmulMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowExponentPartMemGaugedCurveLogarithms
import Theorems.Thm_GlobalTheory_RowLaw_TypPart_coeff_filt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_tyS_of_ne
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_tyS_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
noncomputable section
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.TypPart
variable {C : Type} [Field C]
namespace GlobalTheory.RowLaw.TypPart
theorem _root_.solution {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (f : PowerSeries C) (m n : ℕ) (hn : m + 3 ≤ n) :
    PowerSeries.coeff m (filt (Good l n) f) = PowerSeries.coeff m (typ l f) := by
  rw [coeff_filt]
  unfold typ
  by_cases hm : ∃ s, l ^ s = m
  · obtain ⟨s, rfl⟩ := hm
    rw [coeff_tyS_pow hl.two_le, if_pos]
    intro p _ hp hpl hd
    exact hpl ((Nat.prime_dvd_prime_iff_eq hp hl).1 (hp.dvd_of_dvd_pow hd))
  · rw [coeff_tyS_of_ne _ m (fun s hs => hm ⟨s, hs⟩), if_neg]
    intro hg
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact hg 2 (by omega) Nat.prime_two (Ne.symm hl2) (dvd_zero 2)
    · apply hm
      refine ⟨_, (Nat.eq_prime_pow_of_unique_prime_dvd hpos.ne' ?_).symm⟩
      intro q hq hqm
      by_contra hne
      exact hg q (by have := Nat.le_of_dvd hpos hqm; omega) hq hne hqm
end GlobalTheory.RowLaw.TypPart
