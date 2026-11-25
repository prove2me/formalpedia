-- Prove2me | solution 1 for GlobalTheory.RowChartCounterexample.em_int_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:41:50.081851+00:00
-- url     : https://prove2.me/submissions/bccc50ea-2c2f-45a4-bd1f-aca9c843cfee

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_HostTraceIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_ImaginaryRootConj
import Theorems.Thm_GlobalTheory_RowChartCounterexample_vV_nonneg
import Theorems.Thm_GlobalTheory_RowChartCounterexample_embOK_eOf
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowChartCounterexample
open Formalism.L2.FormalSeriesBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {C : Type} [Field C]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {l : Level H} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {ι : T.Fr →+* C} {V : VF C}
variable {Orb : Type} {d : ℕ}
namespace GlobalTheory.RowChartCounterexample
theorem _root_.solution (τ : E →+* ℂ) (x : 𝓞 E) (h : EmbOK T V ι) : V.Ge 0 (emA3 io ι τ x) := by
  have hx : IsIntegral ℤ (io (embK c τ x)) :=
    (Algebra.IsIntegral.isIntegral (R := ℤ) x).map_of_comp_eq (RingHom.id ℤ) (io.comp (embK c τ)) (Subsingleton.elim _ _)
  have hx' : IsIntegral T.V (io (embK c τ x)) := hx.tower_top
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (K := T.Fr)).1 hx'
  show V.Ge 0 (ι (io (embK c τ x)))
  rw [← hz]
  by_cases h0 : algebraMap T.V T.Fr z = 0
  · rw [h0, map_zero]; exact VF.Ge.zero 0
  unfold VF.Ge
  rw [h _ h0, ← (embOK_eOf h).2]
  have := vV_nonneg T z
  exact WithTop.coe_le_coe.2 (div_nonneg (by exact_mod_cast this) (by positivity))
end GlobalTheory.RowChartCounterexample
