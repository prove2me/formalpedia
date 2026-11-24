-- Prove2me | solution 1 for GlobalTheory.LevelChars.finite_chars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:36:55.802546+00:00
-- url     : https://prove2.me/submissions/ffe420d7-15fa-4ac3-9b77-e0b762b2612f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteChars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.LevelChars
namespace GlobalTheory.LevelChars
theorem _root_.solution {G : Type} [CommGroup G] (H : Subgroup G) [H.FiniteIndex] :
    {ψ : G →* ℂˣ | H ≤ ψ.ker}.Finite := by
  classical
  haveI : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  haveI : NeZero (Nat.card (G ⧸ H)) := ⟨Nat.card_pos.ne'⟩
  let f : {ψ : G →* ℂˣ | H ≤ ψ.ker} → (G ⧸ H → rootsOfUnity (Nat.card (G ⧸ H)) ℂ) := fun ψ q =>
    ⟨QuotientGroup.lift H ψ.1 ψ.2 q, by
      rw [mem_rootsOfUnity, ← map_pow, pow_card_eq_one', map_one]⟩
  have hf : Function.Injective f := by
    rintro ⟨ψ, hψ⟩ ⟨ψ', hψ'⟩ h
    refine Subtype.ext (MonoidHom.ext fun g => ?_)
    have := congrArg (fun F => ((F (QuotientGroup.mk g) : rootsOfUnity _ ℂ) : ℂˣ)) h
    simpa [f] using this
  exact Set.finite_coe_iff.1 (Finite.of_injective f hf)
end GlobalTheory.LevelChars
