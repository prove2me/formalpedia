-- Prove2me | solution 1 for GlobalTheory.DegCnt.StabInv.smul_inf_rs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:24:11.322738+00:00
-- url     : https://prove2.me/submissions/08c7582a-6502-41d7-b16c-44c48f93b391

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonUnipotentStabiliserPreservesTermsAndDatum
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_apply_mem_smul_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.StabInv
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
omit [StarRing K]
namespace GlobalTheory.DegCnt.StabInv
theorem _root_.solution (s : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) {S : Submodule K V}
    (hS : ∀ x, s x ∈ S ↔ x ∈ S) : s • Λ ⊓ rs (𝓞 K) S = s • (Λ ⊓ rs (𝓞 K) S) := by
  ext x
  obtain ⟨y, rfl⟩ := s.surjective x
  rw [apply_mem_smul_iff, Submodule.mem_inf, Submodule.mem_inf, apply_mem_smul_iff]
  exact and_congr Iff.rfl (hS y)
end GlobalTheory.DegCnt.StabInv
