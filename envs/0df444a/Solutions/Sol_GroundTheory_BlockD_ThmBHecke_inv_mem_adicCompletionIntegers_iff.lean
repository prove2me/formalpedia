-- Prove2me | solution 1 for GroundTheory.BlockD.ThmBHecke.inv_mem_adicCompletionIntegers_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:44:40.730621+00:00
-- url     : https://prove2.me/submissions/a2b3433c-5d3e-490f-8204-0a45c2e53489

import Mathlib
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeTensor
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeIdem
import Theorems.Thm_GroundTheory_Global_coe_mem_adicCompletionIntegers_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped TensorProduct NumberField.AdeleRing
open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GroundTheory.Global GroundTheory.Global.AdeleBaseChange
  GroundTheory.Global.SemiLocal
open GroundTheory GroundTheory.BlockD
open GroundTheory.BlockD.ThmBHecke
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GroundTheory.BlockD.ThmBHecke
theorem _root_.solution (w : HeightOneSpectrum (𝓞 E)) {x : 𝓞 E} (hx : x ≠ 0) :
    algebraMap E (w.adicCompletion E) ((x : E)⁻¹) ∈ w.adicCompletionIntegers E ↔ x ∉ w.asIdeal := by
  have hc : algebraMap E (w.adicCompletion E) ((x : E)⁻¹) = (((x : E)⁻¹ : E) : w.adicCompletion E) := rfl
  rw [hc, coe_mem_adicCompletionIntegers_iff, map_inv₀]
  have hx0 : w.valuation E (x : E) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact_mod_cast hx
  rw [inv_le_one₀ (zero_lt_iff.2 hx0), ← HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E)]
  exact ⟨fun h ↦ le_antisymm (w.valuation_le_one x) h, fun h ↦ h.ge⟩
end GroundTheory.BlockD.ThmBHecke
