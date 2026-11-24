-- Prove2me | solution 1 for GlobalTheory.GLDoubling.nabs_unif
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:19.318148+00:00
-- url     : https://prove2.me/submissions/f1a7c1bb-1906-455e-ac40-8f86967d1126

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_properties


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
theorem _root_.solution {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) : nabs k ϖ = (resCard k : ℝ)⁻¹ := by
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  refine (nabs_properties k).2.2.2.2.1 ⟨ϖ, hlt.le⟩ ϖ ?_ rfl
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  ext z
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one,
    Ideal.mem_span_singleton, (Valuation.integer.integers (valuation k)).dvd_iff_le, ← le_uniformizer_iff, ← hϖ]
  rfl
end GlobalTheory.GLDoubling
