-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CharPerp.isCompact_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:36:58.200535+00:00
-- url     : https://prove2.me/submissions/3f073d9e-23fb-40a3-9639-cf29b10065b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnnihilatorOpenCompact
import Theorems.Thm_GlobalTheory_CompanionTheory_CharPerp_isClosed_perp
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_exists_box_subset
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_isCompact_box
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_exists_ne_one
import Theorems.Thm_GlobalTheory_SplitWeil_exists_hasConductor_of_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CharPerp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.CharPerp
theorem _root_.solution {n : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (A : AddSubgroup (Fin n → k)) (hAo : IsOpen (A : Set (Fin n → k))) :
    IsCompact (perp ψ A : Set (Fin n → k)) := by
  classical
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  obtain ⟨s, hs⟩ := exists_box_subset (n := Fin n) (hAo.mem_nhds A.zero_mem)
  refine (isCompact_box (n := Fin n) (c * s⁻¹)).of_isClosed_subset (isClosed_perp ψ hψ A) ?_
  intro ξ hξ i _
  by_contra hi
  obtain ⟨t, ht, hne⟩ := hc.exists_ne_one s hi
  have hmem : Pi.single i t ∈ box (Fin n) s := by
    intro j _
    by_cases hj : j = i
    · subst hj; simpa using ht
    · simp [Pi.single_eq_of_ne hj, cball]
  apply hne
  have := hξ _ (hs hmem)
  rwa [dotProduct_single, mul_comm] at this
end GlobalTheory.CompanionTheory.CharPerp
