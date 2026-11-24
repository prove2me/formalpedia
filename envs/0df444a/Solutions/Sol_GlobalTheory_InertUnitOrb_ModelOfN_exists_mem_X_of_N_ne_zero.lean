-- Prove2me | solution 1 for GlobalTheory.InertUnitOrb.ModelOfN.exists_mem_X_of_N_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:45:28.653265+00:00
-- url     : https://prove2.me/submissions/98bb2659-1298-4adf-a81b-1fbdd742d4c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianModelOfNormNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial Matrix
noncomputable section
open GlobalTheory GlobalTheory.InertUnitOrb GlobalTheory.InertUnitOrb.ModelOfN
namespace GlobalTheory.InertUnitOrb.ModelOfN
theorem _root_.solution {K : UQ} (B : InvAlg K) (x : B.A) (hN : B.N x ≠ 0) : ∃ L, L ∈ B.X x := by
  by_contra hne
  push_neg at hne
  apply hN
  haveI : IsEmpty (Orb K.O B.T (B.X x)) := ⟨fun o => by
    induction o using Quot.ind with
    | mk L => exact hne L.1 L.2⟩
  unfold InvAlg.N orbSum
  exact finsum_of_isEmpty _
end GlobalTheory.InertUnitOrb.ModelOfN
