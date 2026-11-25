-- Prove2me | solution 1 for GlobalTheory.exists_laurent_numerator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:57:50.05682+00:00
-- url     : https://prove2.me/submissions/d16c5b29-2dac-475b-90c5-7c9d1ce95b37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LinearIndependentLaurentMonomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanLaurentMonomialEqHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMonomialBasisCechCubePolynomialGrading
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ι : Type} [DecidableEq ι] [Fintype ι] (s : Finset ι)
    (a : ι → ℤ) (ha : ∀ i, i ∉ s → 0 ≤ a i) :
    ∃ (k : ℕ) (m : ι →₀ ℕ), ∀ i, (m i : ℤ) = a i + if i ∈ s then (k : ℤ) else 0 := by
  refine ⟨Finset.univ.sup fun i => (a i).natAbs, Finsupp.equivFunOnFinite.symm fun i =>
    (a i + if i ∈ s then ((Finset.univ.sup fun i => (a i).natAbs : ℕ) : ℤ) else 0).toNat,
    fun i => Int.toNat_of_nonneg ?_⟩
  have hk := Finset.le_sup (f := fun i => (a i).natAbs) (Finset.mem_univ i)
  split_ifs with hi
  · omega
  · simpa using ha i hi
end GlobalTheory
