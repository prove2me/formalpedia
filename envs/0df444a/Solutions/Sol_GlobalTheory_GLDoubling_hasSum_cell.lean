-- Prove2me | solution 1 for GlobalTheory.GLDoubling.hasSum_cell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:52:49.278799+00:00
-- url     : https://prove2.me/submissions/f2a71f8e-0113-49b3-80d6-e9f739b19b88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Theorems.Thm_GlobalTheory_GLDoubling_isOpen_cell
import Theorems.Thm_GlobalTheory_GLDoubling_iUnion_cell
import Theorems.Thm_GlobalTheory_GLDoubling_pairwise_disjoint_cell
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling Formalism.UG
open scoped NNReal Pointwise
open GlobalTheory GlobalTheory.GLDoubling
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n]
variable {k n}
namespace GlobalTheory.GLDoubling
theorem _root_.solution {N : ℕ} [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)]
    (μ : Measure (GL (Fin N) k)) {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {f : GL (Fin N) k → ℂ}
    (hf : Integrable f μ) (hb : ∀ g, ∀ x ∈ KO k (Fin N), ∀ y ∈ KO k (Fin N), f (x * g * y) = f g) :
    HasSum (fun e : {e : Fin N → ℤ // Antitone e} =>
      (μ.real (cell k (Fin N) ϖ e) : ℂ) * f (torusElt k (Fin N) ϖ e)) (∫ g, f g ∂μ) := by
  have := hasSum_integral_iUnion (μ := μ) (f := f)
    (s := fun e : {e : Fin N → ℤ // Antitone e} => cell k (Fin N) ϖ e) (fun e => (isOpen_cell ϖ e.1).measurableSet) (pairwise_disjoint_cell hϖ)
    hf.integrableOn
  rw [iUnion_cell hϖ, Measure.restrict_univ] at this
  refine (funext fun e => ?_ : (fun e : {e : Fin N → ℤ // Antitone e} =>
    (μ.real (cell k (Fin N) ϖ e) : ℂ) * f (torusElt k (Fin N) ϖ e)) = _) ▸ this
  rw [setIntegral_congr_fun (isOpen_cell ϖ e.1).measurableSet (g := fun _ => f (torusElt k (Fin N) ϖ e))
    fun g hg => by
      obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
      exact hb _ x hx y hy]
  simp
end GlobalTheory.GLDoubling
