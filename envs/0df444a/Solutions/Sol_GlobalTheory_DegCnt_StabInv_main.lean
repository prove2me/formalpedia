-- Prove2me | solution 1 for GlobalTheory.DegCnt.StabInv.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:33:08.512954+00:00
-- url     : https://prove2.me/submissions/674e1acb-adcd-448d-865c-7a11eaea778b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonUnipotentStabiliserPreservesTermsAndDatum
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_keeps_of_mem
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_isFrame_smul
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_isAdm_smul
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_isUnimod_smul
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_latL_eq
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_iotaGraph_eq
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_latTh_eq
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_bOne_eq

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
namespace GlobalTheory.DegCnt.StabInv
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ s ∈ N.R, N.IsTerm g (s • Λ) ∧ N.SameDat g Λ (s • Λ) ∧ latTh N.F N.F' (s • Λ) = latTh N.F N.F' Λ ∧ N.bI (s • Λ) = N.bI Λ := by
  intro K V _ _ _ _ _ _ _ _ H _ r N g Λ _ hΛ s hs
  obtain ⟨h, h'⟩ := keeps_of_mem N hs
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hΛ
  exact ⟨⟨⟨isUnimod_smul h.iso h1, isFrame_smul h h2, isFrame_smul h' h3⟩, isAdm_smul h h' h4⟩,
    ⟨latL_eq _ h Λ, latL_eq _ h' Λ, iotaGraph_eq h h' Λ _⟩, latTh_eq h h' Λ, bOne_eq h h' Λ _⟩
end GlobalTheory.DegCnt.StabInv
