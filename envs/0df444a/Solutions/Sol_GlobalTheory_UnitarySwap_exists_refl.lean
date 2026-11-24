-- Prove2me | solution 1 for GlobalTheory.UnitarySwap.exists_refl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:16:40.902243+00:00
-- url     : https://prove2.me/submissions/a1ffd593-413e-461e-beff-0a30693daa80

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Theorems.Thm_GlobalTheory_UnitarySwap_inv_one_sub_mem
import Theorems.Thm_GlobalTheory_UnitarySwap_mul_lt_one
import Theorems.Thm_GlobalTheory_UnitarySwap_refl_apply
import Theorems.Thm_GlobalTheory_UnitarySwap_refl_isom
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnitarySwap
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable {V : Type} [AddCommGroup V] [Module L V] {σ : L →+* L}
variable {B : V →ₛₗ[σ] V →ₗ[L] L} {W : Submodule L V} {Λ : Set V}
namespace GlobalTheory.UnitarySwap
theorem _root_.solution (hB : ∀ u v, σ (B u v) = B v u) {τ : L} (hτ : τ ∈ intL L)
    (hτ1 : τ + σ τ = 1) {π : L} (hπ0 : π ≠ 0) (hπ : Valued.v π < 1) (hσπ : σ π = π) {e f : V}
    (hef : B e f = π⁻¹) (he : B e e ∈ intL L) (hf : B f f ∈ intL L) :
    ∃ s : V →ₗ[L] V, (∀ u v, B (s u) (s v) = B u v) ∧ (∀ v, B e v = 0 → B f v = 0 → s v = v) ∧
      ∃ r ∈ intL L, ∃ r' ∈ intL L,
        s e = (-r) • (π • e) + (1 + π * r) • f ∧ s f = (1 + π * r') • e + (-r') • (π • f) := by
  have hfe : B f e = π⁻¹ := by rw [← hB, hef, map_inv₀, hσπ]
  have ht : τ * (B e e + B f f) ∈ intL L := mul_mem hτ (add_mem he hf)
  obtain ⟨h0, hi⟩ := inv_one_sub_mem (mul_lt_one hπ ht)
  set t := τ * (B e e + B f f) with htdef
  have hfix : ∀ v, B e v = 0 → B f v = 0 → refl B (e - f) (-(π⁻¹ * (1 - π * t))) v = v := by
    intro v h1 h2
    rw [refl_apply]
    simp [h1, h2]
  refine ⟨refl B (e - f) (-(π⁻¹ * (1 - π * t))), refl_isom hB _ _ ?_ ?_, hfix,
    (t - B e e) * (1 - π * t)⁻¹, mul_mem (sub_mem ht he) hi,
    (t - B f f) * (1 - π * t)⁻¹, mul_mem (sub_mem ht hf) hi, ?_, ?_⟩
  · exact neg_ne_zero.2 (mul_ne_zero (inv_ne_zero hπ0) h0)
  · have : σ τ = 1 - τ := by rw [← hτ1]; ring
    simp only [htdef, map_sub, LinearMap.sub_apply, hef, hfe, map_neg, map_mul, map_inv₀, hσπ, map_one,
      map_add, hB, this]
    field_simp
    ring
  · rw [refl_apply]
    simp only [map_sub, LinearMap.sub_apply, hfe]
    match_scalars <;> field_simp <;> ring
  · rw [refl_apply]
    simp only [map_sub, LinearMap.sub_apply, hef]
    match_scalars <;> field_simp <;> ring
end GlobalTheory.UnitarySwap
