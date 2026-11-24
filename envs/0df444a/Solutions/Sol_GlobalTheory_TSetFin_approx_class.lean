-- Prove2me | solution 1 for GlobalTheory.TSetFin.approx_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:26:04.947837+00:00
-- url     : https://prove2.me/submissions/fc75447e-c374-4db1-8029-3daac94c50c6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HeckeDoubleCosetAdicCompletionInvMulIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Theorems.Thm_ReciprocityTheory_Aut_adic_exists_approx
import Theorems.Thm_ReciprocityTheory_Aut_adic_valued_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut
noncomputable section
open GlobalTheory GlobalTheory.TSetFin
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => maximalRealSubfield L
namespace GlobalTheory.TSetFin
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L⁺)) :
    ∃ c : v.adicCompletion L⁺ → 𝓞 L⁺ ⧸ v.asIdeal, ∀ y y' : v.adicCompletion L⁺, Valued.v y ≤ 1 → Valued.v y' ≤ 1 →
      c y = c y' → Valued.v (y - y') < 1 := by
  classical
  refine ⟨fun y => if h : Valued.v y ≤ 1 then Ideal.Quotient.mk _ (adic_exists_approx v y h).choose else 0, ?_⟩
  intro y y' hy hy' hc
  simp only [dif_pos hy, dif_pos hy'] at hc
  have ha := (adic_exists_approx v y hy).choose_spec
  have ha' := (adic_exists_approx v y' hy').choose_spec
  set a := (adic_exists_approx v y hy).choose
  set a' := (adic_exists_approx v y' hy').choose
  rw [Ideal.Quotient.eq] at hc
  have h3 : Valued.v (algebraMap (𝓞 L⁺) (v.adicCompletion L⁺) (a - a')) < 1 := by
    show Valued.v (algebraMap L⁺ (v.adicCompletion L⁺) (algebraMap (𝓞 L⁺) L⁺ (a - a'))) < 1
    rw [adic_valued_algebraMap]
    exact (v.valuation_lt_one_iff_mem (K := L⁺) _).2 hc
  have e : y - y' = (y - algebraMap (𝓞 L⁺) (v.adicCompletion L⁺) a) -
      (y' - algebraMap (𝓞 L⁺) (v.adicCompletion L⁺) a') + algebraMap (𝓞 L⁺) (v.adicCompletion L⁺) (a - a') := by
    rw [map_sub]; ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ha ha')) h3)
end GlobalTheory.TSetFin
