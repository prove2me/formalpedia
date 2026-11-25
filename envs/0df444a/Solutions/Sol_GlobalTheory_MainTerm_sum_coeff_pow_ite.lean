-- Prove2me | solution 1 for GlobalTheory.MainTerm.sum_coeff_pow_ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:59:58.527591+00:00
-- url     : https://prove2.me/submissions/cf9e7e98-c7d7-4259-b14a-a2f78359905c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupCoordinatesPullbackLinearTangentBasisStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffCoordinatesGoodTangentsLtSq
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open Formalism.BaseCaseIdentities (OrdGE)
noncomputable section
open GlobalTheory GlobalTheory.MainTerm
namespace GlobalTheory.MainTerm
theorem _root_.solution {C : Type} [Field C] {I : Type} [Fintype I] {N : ℕ} (em : Fin N ↪ I)
    (g : I → C) {n : ℕ} (hn : n ≠ 0) (μ : Fin N →₀ ℕ) :
    ∑ c, g c * MvPowerSeries.coeff μ
        ((∑ δ : Fin N, if em δ = c then (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) else 0) ^ n) =
      ∑ δ : Fin N, g (em δ) * MvPowerSeries.coeff μ ((MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ n) := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map em)), Finset.sum_map]
  · refine Finset.sum_congr rfl fun δ _ => ?_
    simp
  · intro c _ hc
    have h : ∀ δ, em δ ≠ c := fun δ h => hc (Finset.mem_map.2 ⟨δ, Finset.mem_univ _, h⟩)
    simp [h, hn]
end GlobalTheory.MainTerm
