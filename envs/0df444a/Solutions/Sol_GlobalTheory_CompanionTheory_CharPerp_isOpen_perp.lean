-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CharPerp.isOpen_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:22:54.553881+00:00
-- url     : https://prove2.me/submissions/ffa7ef52-9949-4620-884b-f393f1f451cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnnihilatorOpenCompact
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_continuous_dot
import Theorems.Thm_GlobalTheory_SplitWeil_exists_cball_addChar_eq_one
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball


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
theorem _root_.solution {n : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (A : AddSubgroup (Fin n → k)) (hAc : IsCompact (A : Set (Fin n → k))) :
    IsOpen (perp ψ A : Set (Fin n → k)) := by
  obtain ⟨s, hs⟩ := exists_cball_addChar_eq_one ψ hψ
  have hN : IsOpen ((fun q : (Fin n → k) × (Fin n → k) => q.1 ⬝ᵥ q.2) ⁻¹' cball s) :=
    (isOpen_cball s).preimage continuous_dot
  have hsub : ({0} : Set (Fin n → k)) ×ˢ (A : Set (Fin n → k)) ⊆
      (fun q : (Fin n → k) × (Fin n → k) => q.1 ⬝ᵥ q.2) ⁻¹' cball s := by
    rintro ⟨x, a⟩ ⟨hx, -⟩
    obtain rfl : x = 0 := hx
    simp [cball]
  obtain ⟨u, v, hu, -, h0u, hAv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hAc hN hsub
  refine AddSubgroup.isOpen_of_mem_nhds (perp ψ A) (g := 0) ?_
  refine Filter.mem_of_superset (hu.mem_nhds (h0u rfl)) fun ξ hξ a ha => ?_
  exact hs _ (huv (Set.mk_mem_prod hξ (hAv ha)))
end GlobalTheory.CompanionTheory.CharPerp
