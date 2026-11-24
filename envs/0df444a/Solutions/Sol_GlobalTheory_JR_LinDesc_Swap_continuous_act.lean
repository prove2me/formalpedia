-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.Swap.continuous_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:08:40.580258+00:00
-- url     : https://prove2.me/submissions/8a16d97f-c747-4e21-9ad9-6efa7dfe0e44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearDescentPartialFourierEqFourierDescent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc GlobalTheory.JR.LinDesc.Swap
namespace GlobalTheory.JR.LinDesc.Swap
theorem _root_.solution {F : Type} [NontriviallyNormedField F] (r : ℕ) :
    Continuous (fun z : GL (Fin r) F × Gl r F => act z.1 z.2) := by
  unfold act
  have h1 : Continuous (fun z : GL (Fin r) F × Gl r F => ((z.1 : Matrix (Fin r) (Fin r) F))) :=
    Units.continuous_val.comp continuous_fst
  have h2 : Continuous (fun z : GL (Fin r) F × Gl r F =>
      (((z.1⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F))) :=
    Units.continuous_coe_inv.comp continuous_fst
  exact ((h1.matrix_mul continuous_snd.fst).matrix_mul h2).prodMk
    ((h1.matrix_mulVec continuous_snd.snd.fst).prodMk
      ((continuous_snd.snd.snd.fst.matrix_vecMul h2).prodMk continuous_snd.snd.snd.snd))
end GlobalTheory.JR.LinDesc.Swap
