-- Prove2me | solution 1 for GlobalTheory.MaxLatStruct.finite_field_invol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:31:34.575405+00:00
-- url     : https://prove2.me/submissions/4d9a3987-48dc-4d38-aa14-51a4fcf2d6ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan
import Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_ff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.MaxLatStruct
namespace GlobalTheory.MaxLatStruct
theorem _root_.solution {k : Type*} [Field k] [Finite k] (τ : k →+* k) (hτ : ∀ a, τ (τ a) = a)
    (θ : k) (hθ : θ - τ θ ≠ 0) :
    (∃ q : ℕ, 2 ≤ q ∧ Nat.card k = q ^ 2) ∧ ∀ u, τ u = u → ∃ w, τ w * w = u := by
  let F : Subfield k := RingHom.eqLocusField τ (RingHom.id k)
  have hF : ∀ a, a ∈ F ↔ τ a = a := fun a => Iff.rfl
  constructor
  · refine ⟨Nat.card F, Finite.one_lt_card, ?_⟩
    rw [sq, ← Nat.card_prod]
    symm
    apply Nat.card_congr
    refine Equiv.ofBijective (fun p : F × F => (p.1 : k) + p.2 * θ) ⟨?_, ?_⟩
    · rintro ⟨a, b⟩ ⟨c, d⟩ e
      have ha := (hF _).1 a.2
      have hb := (hF _).1 b.2
      have hc := (hF _).1 c.2
      have hd := (hF _).1 d.2
      have e1 : (a : k) + b * θ = c + d * θ := e
      have e2 := congrArg τ e1
      rw [map_add, map_add, map_mul, map_mul, ha, hb, hc, hd] at e2
      have e3 : ((b : k) - d) * (θ - τ θ) = 0 := by linear_combination e1 - e2
      have e4 : (b : k) = d := sub_eq_zero.1 ((mul_eq_zero.1 e3).resolve_right hθ)
      have e5 : (a : k) = c := by rw [e4] at e1; exact add_right_cancel e1
      exact Prod.ext (Subtype.ext e5) (Subtype.ext e4)
    · intro z
      have hθ' : τ θ - θ ≠ 0 := fun e => hθ (by linear_combination -e)
      have hb : τ ((z - τ z) / (θ - τ θ)) = (z - τ z) / (θ - τ θ) := by
        rw [map_div₀, map_sub, map_sub, hτ, hτ]
        field_simp
        ring
      have ha : τ (z - (z - τ z) / (θ - τ θ) * θ) = z - (z - τ z) / (θ - τ θ) * θ := by
        rw [map_sub, map_mul, hb]
        field_simp
        ring
      exact ⟨(⟨_, (hF _).2 ha⟩, ⟨_, (hF _).2 hb⟩), by simp⟩
  · intro u hu
    have hT : τ (θ + τ θ) = θ + τ θ := by rw [map_add, hτ, add_comm]
    have hN : τ (τ θ * θ) = τ θ * θ := by rw [map_mul, hτ, mul_comm]
    obtain ⟨a, b, hab⟩ := unimodUnramUnique_ff (k := F) ⟨_, (hF _).2 hT⟩ ⟨_, (hF _).2 hN⟩ ⟨u, (hF _).2 hu⟩
      (by
        intro e
        have e1 := congrArg F.subtype e
        rw [map_sub, map_pow, map_mul, map_ofNat, map_zero] at e1
        have e2 : (θ + τ θ) ^ 2 - 4 * (τ θ * θ) = 0 := e1
        apply hθ
        have : (θ - τ θ) ^ 2 = 0 := by linear_combination e2
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this)
    have e1 := congrArg F.subtype hab
    simp only [map_add, map_mul, map_pow] at e1
    have e2 : (a : k) ^ 2 + (θ + τ θ) * a * b + (τ θ * θ) * (b : k) ^ 2 = u := e1
    refine ⟨a + b * θ, ?_⟩
    rw [map_add, map_mul, (hF _).1 a.2, (hF _).1 b.2]
    linear_combination e2
end GlobalTheory.MaxLatStruct
