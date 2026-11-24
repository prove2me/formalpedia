-- Prove2me | solution 1 for GlobalTheory.PairOp.sum_family_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:19:49.616452+00:00
-- url     : https://prove2.me/submissions/b1a8872c-12f4-4a6d-9ceb-c9072374d61c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Theorems.Thm_GlobalTheory_LatPair_Model_sum_stable_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
open GlobalTheory GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.PairOp
theorem _root_.solution {ι : Type} {φ : Form k n M} (h : φ ∈ Mram k n M) (e : ι → Pair k n)
    (he : Function.Injective e) (S : Finset ι) (hS : ∀ (c : 𝓀[k]ˣ), ∀ i ∈ S, ∃ j ∈ S, e j = c • e i) :
    ∑ i ∈ S, φ (e i) = 0 := by
  classical
  rw [← Finset.sum_image (fun i _ j _ hij => he hij)]
  refine Model.sum_stable_eq_zero h _ fun c P => ?_
  constructor
  · intro hP
    obtain ⟨i, hi, hPi⟩ := Finset.mem_image.mp hP
    obtain ⟨j, hj, hj'⟩ := hS c⁻¹ i hi
    refine Finset.mem_image.mpr ⟨j, hj, ?_⟩
    rw [hj', hPi, inv_smul_smul]
  · intro hP
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨j, hj, hj'⟩ := hS c i hi
    exact Finset.mem_image.mpr ⟨j, hj, hj'⟩
end GlobalTheory.PairOp
