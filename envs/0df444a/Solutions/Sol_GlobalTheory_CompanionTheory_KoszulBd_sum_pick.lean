-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KoszulBd.sum_pick
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:48:31.453153+00:00
-- url     : https://prove2.me/submissions/326ab0a5-c168-4e1c-8d61-9977eb5d5f5e

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CommuteOfUnitaryConjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KoszulBd
open CompanionTheory.D.DSIC
open Formalism.REAL (GlRel)
variable {n : ℕ} {ε : Fin n → Bool}
namespace GlobalTheory.CompanionTheory.KoszulBd
theorem _root_.solution {R : Type} [AddCommGroup R] [Module ℂ R] (f : Fin n → Fin n → R) (a b : Fin n) (P : Prop)
    [Decidable P] (hP : P → ε a = true ∧ ε b = false) (Q : NC ε → Prop) [DecidablePred Q]
    (hQ : ∀ k, Q k ↔ P ∧ k.1.1 = a ∧ k.1.2 = b) :
    ∑ k : NC ε, (if Q k then (1 : ℂ) else 0) • f k.1.1 k.1.2 = if P then f a b else 0 := by
  by_cases hp : P
  · rw [if_pos hp]
    let k0 : NC ε := ⟨(a, b), hP hp⟩
    rw [Finset.sum_eq_single k0]
    · rw [if_pos ((hQ k0).mpr ⟨hp, rfl, rfl⟩), one_smul]
    · intro k _ hk
      rw [if_neg, zero_smul]
      intro hq
      obtain ⟨_, h1, h2⟩ := (hQ k).mp hq
      exact hk (Subtype.ext (Prod.ext h1 h2))
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro k _
    rw [if_neg (fun hq => hp ((hQ k).mp hq).1), zero_smul]
end GlobalTheory.CompanionTheory.KoszulBd
