-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TfLoc.Iw.iwahori_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:41:36.560633+00:00
-- url     : https://prove2.me/submissions/fd1f6b09-09f8-4ef8-a0ca-fa8fecbb8e36

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_mem_unitGL_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel PositivityTheory.Rg.Tf.Loc Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TfLoc GlobalTheory.CompanionTheory.TfLoc.Iw
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {m : ℕ}
namespace GlobalTheory.CompanionTheory.TfLoc.Iw
theorem _root_.solution : iwahori (m := m) F =
    (⋂ i, ⋂ j, (fun g : GL (Fin m) F => (g : Matrix (Fin m) (Fin m) F) i j) ⁻¹'
        {x | valuation F x ≤ 1}) ∩
    (⋂ i, ⋂ j, (fun g : GL (Fin m) F => ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) i j) ⁻¹'
        {x | valuation F x ≤ 1}) ∩
    (⋂ i, ⋂ j, ⋂ _ : j < i, (fun g : GL (Fin m) F => (g : Matrix (Fin m) (Fin m) F) i j) ⁻¹'
        {x | valuation F x < 1}) := by
  ext g
  simp only [iwahori, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq,
    mem_unitGL_iff, and_assoc]
end GlobalTheory.CompanionTheory.TfLoc.Iw
