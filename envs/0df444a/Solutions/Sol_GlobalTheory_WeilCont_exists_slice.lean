-- Prove2me | solution 1 for GlobalTheory.WeilCont.exists_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:35:34.47497+00:00
-- url     : https://prove2.me/submissions/db1d82ca-abb4-4c3f-a0e9-d0b0110e1513

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsContOnOfLocal
import Theorems.Thm_GlobalTheory_WeilCont_pureA_adeleJoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped Classical
open GlobalTheory GlobalTheory.WeilCont
variable (F : Type) [Field F] [NumberField F] {κ : Type}
namespace GlobalTheory.WeilCont
theorem _root_.solution [Fintype κ] {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ)
    (y : κ → FiniteAdeleRing (𝓞 F) F) :
    ∃ s : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∀ x, s x = Φ (adeleJoin F x y) := by
  unfold GlobalTheory.WeilM.schA at hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, -, rfl⟩ := h
    exact ⟨g y • f, fun x => by rw [smul_apply, pureA_adeleJoin, smul_eq_mul, mul_comm]⟩
  | zero => exact ⟨0, fun x => by simp⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨s1, hs1⟩ := h1
    obtain ⟨s2, hs2⟩ := h2
    exact ⟨s1 + s2, fun x => by rw [add_apply, hs1, hs2]; rfl⟩
  | smul c Φ _ h =>
    obtain ⟨s, hs⟩ := h
    exact ⟨c • s, fun x => by rw [smul_apply, hs]; rfl⟩
end GlobalTheory.WeilCont
