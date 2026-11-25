-- Prove2me | solution 1 for GroundTheory.Global.IdeleNorm.exists_norm_eq_of_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:14:16.740592+00:00
-- url     : https://prove2.me/submissions/339d8428-d2c6-49d9-9a29-cf4f66dd848f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNorms
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNorms
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNormGroups
import Theorems.Thm_GroundTheory_Global_mem_valuationInteger_iff
import Theorems.Thm_GroundTheory_Global_ramificationIdx_integer
import Theorems.Thm_GroundTheory_LocalField_IsUnramified_trans
import Theorems.Thm_GroundTheory_LocalField_coe_normIntegerUnits


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField Filter Topology ValuativeRel
open AdeleBaseChange SemiLocal
open scoped NumberField.LiesOver TensorProduct
noncomputable section
open GroundTheory.Global.IdeleNorm
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Global.IdeleNorm
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (he : w.asIdeal.ramificationIdx (𝓞 K) = 1) {u : (v.adicCompletion K)ˣ}
    (hu : u ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units) :
    ∃ y ∈ (Submonoid.ofClass (w.adicCompletionIntegers L)).units,
      Algebra.norm (v.adicCompletion K) (y : w.adicCompletion L) = u := by
  have : LocalField.IsUnramified (v.adicCompletion K) (w.adicCompletion L) :=
    ⟨(ramificationIdx_integer v w).trans he⟩
  rw [Submonoid.mem_units_iff] at hu
  let u' : 𝒪[v.adicCompletion K]ˣ :=
    ⟨⟨u, (mem_valuationInteger_iff v _).2 hu.1⟩, ⟨_, (mem_valuationInteger_iff v _).2 hu.2⟩,
      Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩
  obtain ⟨g, hg⟩ := LocalField.normIntegerUnits_surjective
    (K := v.adicCompletion K) (L := w.adicCompletion L) u'
  refine ⟨LocalField.unitsIncl _ g, (Submonoid.mem_units_iff _ _).2
    ⟨(mem_valuationInteger_iff w _).1 (g : 𝒪[w.adicCompletion L]).2, ?_⟩, ?_⟩
  · rw [← map_inv, LocalField.coe_unitsIncl]
    exact (mem_valuationInteger_iff w _).1 ((g⁻¹ : 𝒪[w.adicCompletion L]ˣ) :
      𝒪[w.adicCompletion L]).2
  · rw [LocalField.coe_unitsIncl, ← LocalField.coe_normIntegerUnits, hg]
end GroundTheory.Global.IdeleNorm
