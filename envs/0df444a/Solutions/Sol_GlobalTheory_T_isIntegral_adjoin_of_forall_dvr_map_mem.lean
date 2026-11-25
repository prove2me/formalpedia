-- Prove2me | solution 1 for GlobalTheory.T.isIntegral_adjoin_of_forall_dvr_map_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:24:17.329264+00:00
-- url     : https://prove2.me/submissions/8e1758b7-1b58-493a-93c3-fdd0ca5ac419

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralAdjoinOfForallCdvr
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralAdjoinOfForallCdvrStatement
import Theorems.Thm_GlobalTheory_isIntegral_adjoin_of_forall_cdvr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.Pj
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (gens : Finset Ω), Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤ → ∀ x : Ω, (∀ (T : CDVR), Countable (IsLocalRing.ResidueField T.V) → ∀ φ : Ω →+* T.Fr, (∀ k : K, φ (algebraMap K Ω k) ∈ (algebraMap T.V T.Fr).range) → (∀ g ∈ gens, φ g ∈ (algebraMap T.V T.Fr).range) → φ x ∈ (algebraMap T.V T.Fr).range) → IsIntegral (Algebra.adjoin K (gens : Set Ω)) x := by
  first | exact @GlobalTheory.isIntegral_adjoin_of_forall_cdvr | exact GlobalTheory.isIntegral_adjoin_of_forall_cdvr | (intros; apply GlobalTheory.isIntegral_adjoin_of_forall_cdvr <;> assumption)
end _root_.GlobalTheory.T
