-- Prove2me | solution 1 for GlobalTheory.CMVal.InhabK.splits_of_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:05:26.979946+00:00
-- url     : https://prove2.me/submissions/05dd944a-f909-4d78-aaa3-01a7b5938fb2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFinSetSplitPlacesCoprimeConductor
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.InhabK
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
local notation "cj" => IsCMField.ringOfIntegersComplexConj E
namespace GlobalTheory.CMVal.InhabK
theorem _root_.solution {l : ℕ} (hl : l.Prime) (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (OF E))
    (hv : Over P v) (hN : Ideal.absNorm P.asIdeal = l) (x : 𝓞 E) (hx : x - cj x ∉ P.asIdeal) : Splits v := by
  have := P.isPrime
  let P' : HeightOneSpectrum (𝓞 E) := ⟨P.asIdeal.comap (cj).toRingEquiv.toRingHom, Ideal.comap_isPrime _ _, fun h => by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    have : (cj).symm y ∈ P.asIdeal.comap (cj).toRingEquiv.toRingHom := by
      rw [Ideal.mem_comap]; simpa using hy
    rw [h, Ideal.mem_bot] at this
    exact hy0 (by simpa using this)⟩
  refine ⟨P, P', fun e => hx ?_, hv, ?_⟩
  · haveI : Fact (Nat.card (𝓞 E ⧸ P.asIdeal)).Prime := ⟨by
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hN]; exact hl⟩
    have htop : AddSubgroup.zmultiples (1 : 𝓞 E ⧸ P.asIdeal) = ⊤ := by
      rcases (AddSubgroup.zmultiples (1 : 𝓞 E ⧸ P.asIdeal)).eq_bot_or_eq_top_of_prime_card with h | h
      · exact absurd (AddSubgroup.zmultiples_eq_bot.1 h) one_ne_zero
      · exact h
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 (htop ▸ AddSubgroup.mem_top (Ideal.Quotient.mk P.asIdeal x))
    have h1 : x - n ∈ P.asIdeal := by
      rw [← Ideal.Quotient.eq, ← hn]; simp
    have h2 : x - n ∈ P'.asIdeal := e ▸ h1
    have h3 : cj x - n ∈ P.asIdeal := by
      have : cj (x - n) ∈ P.asIdeal := h2
      simpa using this
    have := P.asIdeal.sub_mem h1 h3
    simpa using this
  · unfold Over at hv ⊢
    rw [← hv]
    ext y
    change cj (algebraMap (OF E) (𝓞 E) y) ∈ P.asIdeal ↔ algebraMap (OF E) (𝓞 E) y ∈ P.asIdeal
    rw [AlgEquiv.commutes]
end GlobalTheory.CMVal.InhabK
