-- Prove2me | solution 1 for GlobalTheory.AdLat.mem_range_iff_adele_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:45.806548+00:00
-- url     : https://prove2.me/submissions/286f01e6-41e0-4652-94f3-746e578323b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.AdLat
theorem _root_.solution (x : F) :
    x ∈ (algebraMap (𝓞 F) F).range ↔
      ∀ v, algebraMap F (FiniteAdeleRing (𝓞 F) F) x v ∈ v.adicCompletionIntegers F := by
  simp only [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  constructor
  · rintro ⟨a, rfl⟩ v
    exact v.valuation_le_one a
  · exact HeightOneSpectrum.mem_integers_of_valuation_le_one F x
end GlobalTheory.AdLat
