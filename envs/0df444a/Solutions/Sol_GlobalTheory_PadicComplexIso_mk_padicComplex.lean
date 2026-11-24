-- Prove2me | solution 1 for GlobalTheory.PadicComplexIso.mk_padicComplex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:48:19.817647+00:00
-- url     : https://prove2.me/submissions/fd9675b3-46c4-413c-a8e2-282637d30a9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MkLeContinuumOfDenseRange
import Theorems.Thm_GlobalTheory_PadicComplexIso_mk_le_continuum_of_denseRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open Cardinal
open GlobalTheory GlobalTheory.PadicComplexIso
namespace GlobalTheory.PadicComplexIso
theorem _root_.solution (q : ℕ) [Fact q.Prime] : #ℂ_[q] = 𝔠 := by
  apply le_antisymm
  · have hQp : #ℚ_[q] ≤ 𝔠 :=
      mk_le_continuum_of_denseRange _ (Padic.denseRange_ratCast q)
        (by rw [Cardinal.mkRat]; exact Cardinal.aleph0_le_continuum)
    have hAl : #(PadicAlgCl q) ≤ 𝔠 :=
      (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[q] (PadicAlgCl q)).trans
        (max_le hQp Cardinal.aleph0_le_continuum)
    exact mk_le_continuum_of_denseRange _ (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl q)) hAl
  · obtain ⟨g, -, -, hg⟩ :=
      (PerfectSpace.univ_perfect (α := ℂ_[q])).exists_nat_bool_injection Set.univ_nonempty
    calc 𝔠 = #(ℕ → Bool) := by
          rw [← Cardinal.power_def, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.two_power_aleph0]
      _ ≤ #ℂ_[q] := Cardinal.mk_le_of_injective hg
end GlobalTheory.PadicComplexIso
