-- Prove2me | solution 1 for GlobalTheory.LatOrb.exists_cyclicVector_of_separable_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:15:51.663714+00:00
-- url     : https://prove2.me/submissions/9b158b04-b551-4ff2-9ba5-9e06a480e205

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ExistsNeZeroAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCyclicVectorOfSeparableCharpoly
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_base_change_cyclic_vector


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
open GlobalTheory GlobalTheory.LatOrb
namespace GlobalTheory.LatOrb
theorem _root_.solution {K : Type} [Field K] (n : ℕ)
    (γ : Matrix (Fin n) (Fin n) K) (hs : γ.charpoly.Separable) :
    ∃ v₀ : Fin n → K, ∀ u : Fin n → K, ∃ p : K[X], u = aeval γ p *ᵥ v₀ := by
  have hs' : (Matrix.toLin' γ).charpoly.Separable := by rwa [Matrix.charpoly_toLin']
  obtain ⟨e, he⟩ := Formalism.IrreducibleCountingLemmas.Z.base_change_cyclic_vector K (Fin n → K) (Matrix.toLin' γ) hs'
  refine ⟨e, fun u => ?_⟩
  obtain ⟨p, hp⟩ := he u
  refine ⟨p, ?_⟩
  rw [← hp]
  have h : aeval (Matrix.toLin' γ) p = Matrix.toLin' (aeval γ p) := by
    have := (aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).toAlgHom γ p).symm
    exact this.symm
  rw [h, Matrix.toLin'_apply]
end GlobalTheory.LatOrb
