-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.FourierTest.algMap_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:02.846274+00:00
-- url     : https://prove2.me/submissions/7e4b4cb0-8464-4c4f-9e9d-ac50a5af1ae3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierPreservesTestAdditive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.FourierTest
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.WeilQuad.FourierTest
theorem _root_.solution (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) :
    Function.Injective (algebraMap A.K A.L) := by
  haveI : Nontrivial A.L := ⟨hL.exists_pair_ne⟩
  rw [injective_iff_map_eq_zero]
  intro k hk
  by_contra hne
  obtain ⟨k', hk'⟩ := hK.mul_inv_cancel hne
  have h : algebraMap A.K A.L (k * k') = 0 := by rw [map_mul, hk, zero_mul]
  rw [hk', map_one] at h
  exact one_ne_zero h
end GlobalTheory.JR.WeilQuad.FourierTest
