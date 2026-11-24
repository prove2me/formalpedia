-- Prove2me | solution 1 for GlobalTheory.GLDoubling.pairwise_disjoint_cell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:20:33.813938+00:00
-- url     : https://prove2.me/submissions/f2e4c449-b899-4f48-9290-24150a65e1de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Theorems.Thm_GlobalTheory_GLDoubling_val_torusElt
import Theorems.Thm_Formalism_UG_P_cartan_unique_gen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling Formalism.UG
open scoped NNReal Pointwise
open GlobalTheory GlobalTheory.GLDoubling
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n]
variable {k n}
namespace GlobalTheory.GLDoubling
theorem _root_.solution {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) :
    Pairwise (Function.onFun Disjoint fun e : {e : Fin N → ℤ // Antitone e} => cell k (Fin N) ϖ e) := by
  intro a b hab
  refine Set.disjoint_left.2 fun g ha hb => hab (Subtype.ext ?_)
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.1 ha
  obtain ⟨x', hx', y', hy', e⟩ := DoubleCoset.mem_doubleCoset.1 hb
  have e' : x'⁻¹ * x * torusElt k _ ϖ a * (y * y'⁻¹) = torusElt k _ ϖ b := by
    calc _ = x'⁻¹ * (x * torusElt k _ ϖ a * y) * y'⁻¹ := by group
      _ = _ := by rw [e]; group
  refine Formalism.UG.P.cartan_unique_gen 𝒪[k] (valuation k) (fun _ => Iff.rfl) (ϖ : k) ϖ.ne_zero
    (hϖ ▸ uniformizer_lt_one) a.1 b.1 a.2 b.2 (x'⁻¹ * x) (mul_mem (inv_mem hx') hx) (y * y'⁻¹)
    (mul_mem hy (inv_mem hy')) ?_
  rw [← val_torusElt, ← val_torusElt, ← e', Units.val_mul (x'⁻¹ * x * _), Units.val_mul (x'⁻¹ * x)]
end GlobalTheory.GLDoubling
