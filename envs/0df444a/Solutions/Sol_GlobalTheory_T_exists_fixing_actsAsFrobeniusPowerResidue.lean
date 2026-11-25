-- Prove2me | solution 1 for GlobalTheory.T.exists_fixing_actsAsFrobeniusPowerResidue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:06:13.331245+00:00
-- url     : https://prove2.me/submissions/bb4cb5f9-71a7-42a1-8e39-9294f1196e10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFixingActsAsFrobeniusPowerResidue
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFixingActsAsFrobeniusPowerResidueStatement
import Theorems.Thm_GlobalTheory_GaloisLift_exists_fixing_actsAs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (_h : IsPlaceOver A w)
    (K : IntermediateField E Ω) [FiniteDimensional E K], ∀ d ∈ Dec (F := E) A, ∀ j : ℕ,
      (∀ z ∈ K, A.valuation z ≤ 1 → A.valuation (d z - z ^ (normV w ^ j)) < 1) →
      ∃ ρ : G E Ω, (∀ z ∈ K, ρ z = z) ∧ ActsAs A (normV w) (d * ρ) j 0 := by
  first | exact @GlobalTheory.GaloisLift.exists_fixing_actsAs | exact GlobalTheory.GaloisLift.exists_fixing_actsAs | (intros; apply GlobalTheory.GaloisLift.exists_fixing_actsAs <;> assumption)
end _root_.GlobalTheory.T
