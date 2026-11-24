-- Prove2me | solution 1 for GlobalTheory.finsupp_eq_zero_of_sum_torsion_characters_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:57:44.136886+00:00
-- url     : https://prove2.me/submissions/68b9ee02-376c-4bd5-a160-252566fdd8b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinsuppEqZeroOfSumTorsionCharactersEqZero
import Theorems.Thm_GlobalTheory_exists_eq_add_nsmul_of_torsion_characters_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k X : Type) [Field k] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (ζ : k), 0 < N → IsPrimitiveRoot ζ N → ∀ (M : Type) [AddCommGroup M] [Module k M] (c : X →₀ M), (∀ α ∈ c.support, ∀ β ∈ c.support, (∃ w, α = β + N • w) → α = β) → (∀ t : Multiplicative X →* kˣ, t ^ N = 1 → c.sum (fun α m => (t (Multiplicative.ofAdd α) : k) • m) = 0) → c = 0 := by
  intro k X _ _ _ _ N ζ hN hζ M _ _ c hc hsum
  classical
  let G : Subgroup (Multiplicative X →* kˣ) := (powMonoidHom N).ker
  let ev : c.support → (G →* k) := fun α =>
    { toFun := fun t => ((t : Multiplicative X →* kˣ) (Multiplicative.ofAdd (α : X)) : k)
      map_one' := by simp
      map_mul' := by
        intro s t
        simp }
  have hinj : Function.Injective ev := by
    intro α β hαβ
    apply Subtype.ext
    refine hc _ α.2 _ β.2
      (exists_eq_add_nsmul_of_torsion_characters_eq k X N ζ hN hζ _ _ fun t ht => ?_)
    exact Units.ext (DFunLike.congr_fun hαβ (⟨t, ht⟩ : G))
  have hli : LinearIndependent k (fun α : c.support => (ev α : G → k)) :=
    (linearIndependent_monoidHom G k).comp ev hinj
  ext α
  by_contra hα
  have hmem : α ∈ c.support := Finsupp.mem_support_iff.mpr hα
  apply hα
  rw [Finsupp.zero_apply, ← Module.forall_dual_apply_eq_zero_iff k]
  intro φ
  refine Fintype.linearIndependent_iff.mp hli (fun β => φ (c β)) ?_ ⟨α, hmem⟩
  funext t
  have h0 := congrArg φ (hsum t t.2)
  rw [Finsupp.sum, map_sum, map_zero, ← Finset.sum_coe_sort] at h0
  rw [Finset.sum_apply, Pi.zero_apply, ← h0]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
  rfl
end GlobalTheory
