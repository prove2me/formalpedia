-- Prove2me | solution 1 for GroundTheory.Global.subsingleton_cycTateNegOne_adicCompletionIntegers_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:52:46.68958+00:00
-- url     : https://prove2.me/submissions/111e8cff-7bd6-43d6-97c8-fdbc95c33a3e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNorms
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalHerbrand
import Theorems.Thm_GroundTheory_Global_mem_zpowers_mulEquiv
import Theorems.Thm_GroundTheory_Global_integerUnitsAddEquiv_decomposition
import Theorems.Thm_GroundTheory_Global_isUnramified_adicCompletion
import Theorems.Thm_GroundTheory_LocalField_natCard_tateNegOne_eq
import Theorems.Thm_GroundTheory_LocalField_subsingleton_tateNegOne_integerUnits


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
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.GroupCoh
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
open AdicLiesOver
include v
namespace GroundTheory.Global
theorem _root_.solution
    (he : w.asIdeal.ramificationIdx (𝓞 K) = 1)
    [Fintype (MulAction.stabilizer Gal(L/K) w.asIdeal)]
    (τ : MulAction.stabilizer Gal(L/K) w.asIdeal) (hτ : ∀ σ, σ ∈ Subgroup.zpowers τ) :
    Subsingleton (CycTateNegOne (Representation.ofMulDistribMulAction
      (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.adicCompletionIntegers L)ˣ) τ) := by
  have := isUnramified_adicCompletion v w he
  have hgen := mem_zpowers_mulEquiv (decompositionMulEquiv v w) hτ
  have : IsCyclic Gal(w.adicCompletion L/v.adicCompletion K) :=
    ⟨⟨decompositionMulEquiv v w τ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hgen g)⟩⟩
  have : Subsingleton (GroundTheory.LocalField.TateNegOne Gal(w.adicCompletion L/v.adicCompletion K)
      𝒪[w.adicCompletion L]ˣ) := GroundTheory.LocalField.subsingleton_tateNegOne_integerUnits
  have h1 : Nat.card (GroundTheory.LocalField.TateNegOne Gal(w.adicCompletion L/v.adicCompletion K)
      𝒪[w.adicCompletion L]ˣ) = 1 := Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩
  rw [GroundTheory.LocalField.natCard_tateNegOne_eq hgen, ← Nat.card_congr
    (cycTateNegOneEquivOfMulEquiv (decompositionMulEquiv v w) (integerUnitsAddEquiv w)
      (integerUnitsAddEquiv_decomposition v w) τ).toEquiv] at h1
  exact (Nat.card_eq_one_iff_unique.1 h1).1
end GroundTheory.Global
