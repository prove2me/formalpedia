-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Lat.glue_apply_of_inFibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:43:17.75257+00:00
-- url     : https://prove2.me/submissions/949c154d-5854-4643-8a60-d190af560cbd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsGenOfIsVBOne
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StalkClosedPointToToStalk
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_GlueApplyOfNotInFibre
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Lat_not_inFibre_of_coprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory
variable {X X' X'' : Scheme.{0}} {Ω Ω' Ω'' : Type} [Field Ω] [Field Ω'] [Field Ω'']
  {E F : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup F] [Module Ω' F]
variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
  {ξ'' : Spec (CommRingCat.of Ω'') ⟶ X''}
namespace GlobalTheory.CompanionTheory.Ar
namespace Lat
theorem _root_.solution {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) (L₀ : Lat ξ E) (Lq : ℕ → Lat ξ E)
    {q : ℕ} (hq : q ∈ S) {p : Cpt ξ} (hp : InFibre ξ q p) : Lat.glue S L₀ Lq p = Lq q p := by
  have h : ∃ q ∈ S, InFibre ξ q p := ⟨q, hq, hp⟩
  unfold Lat.glue
  rw [dif_pos h]
  by_cases e : h.choose = q
  · rw [e]
  · exact (Lat.not_inFibre_of_coprime p ((Nat.coprime_primes (hS _ h.choose_spec.1) (hS _ hq)).2 e)
      h.choose_spec.2 hp).elim
end Lat
end GlobalTheory.CompanionTheory.Ar
