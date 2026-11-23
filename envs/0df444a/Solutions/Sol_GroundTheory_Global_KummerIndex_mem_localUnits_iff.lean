-- Prove2me | solution 1 for GroundTheory.Global.KummerIndex.mem_localUnits_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:18.292893+00:00
-- url     : https://prove2.me/submissions/a430b9cd-80fd-4d93-a220-c2cb561d15b8

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexProductFormula
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_KummerIndexLemma_HasEnoughRootsOfUnityOfRingHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField GroundTheory.ProfCoh WithZero
open GroundTheory.Global.KummerIndex
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
variable {v}
namespace GroundTheory.Global.KummerIndex
theorem _root_.solution {x : (v.adicCompletion K)ˣ} :
    x ∈ localUnits v ↔ Valued.v (x : v.adicCompletion K) = 1 := by
  have hx : Valued.v (x : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  change (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
      ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K ↔ _
  rw [mem_adicCompletionIntegers, mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀]
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 hx)).1 h2)
  · intro h
    rw [h, inv_one]
    exact ⟨le_rfl, le_rfl⟩
end GroundTheory.Global.KummerIndex
