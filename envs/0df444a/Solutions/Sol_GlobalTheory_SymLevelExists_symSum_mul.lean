-- Prove2me | solution 1 for GlobalTheory.SymLevelExists.symSum_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:17:28.827693+00:00
-- url     : https://prove2.me/submissions/453ee01e-2eb3-4ef5-b004-593c393ae945

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsSymmetricPositionLevel
import Theorems.Thm_GlobalTheory_SymLevelExists_superSum_mul
import Theorems.Thm_GlobalTheory_SymLevelExists_symSum_eq
import Theorems.Thm_GlobalTheory_RootEx_Model_conj_mem
import Theorems.Thm_GlobalTheory_RootEx_Model_simpleSum_conj
import Theorems.Thm_GlobalTheory_RootEx_Model_simpleSum_mul
import Theorems.Thm_GlobalTheory_RootEx_Radical_conj_mem
import Theorems.Thm_GlobalTheory_RootEx_Radical_simpleSum_conj
import Theorems.Thm_GlobalTheory_RootEx_Radical_simpleSum_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
noncomputable section
open GlobalTheory GlobalTheory.SymLevelExists
variable {F : Type} [Field F] {κ l : ℕ}
namespace GlobalTheory.SymLevelExists
theorem _root_.solution {p : ℕ} {x y : GL (Fin κ ⊕ Fin l) F} (hx : x ∈ symGroup F κ l p) (hy : y ∈ symGroup F κ l p) :
    symSum (x * y) = symSum x + symSum y := by
  obtain ⟨u, hu, γ, hγ, rfl⟩ := hx
  obtain ⟨u', hu', γ', hγ', rfl⟩ := hy
  have e : u * embX l γ * (u' * embX l γ') = u * (embX l γ * u' * (embX l γ)⁻¹) * embX l (γ * γ') := by
    rw [map_mul]; group
  rw [e, symSum_eq (mul_mem hu (Radical.conj_mem γ hu')), symSum_eq hu, symSum_eq hu',
    Radical.simpleSum_mul hu (Radical.conj_mem γ hu'), Radical.simpleSum_conj, Units.val_mul, superSum_mul hγ hγ']
  ring
end GlobalTheory.SymLevelExists
