-- Prove2me | solution 1 for GlobalTheory.linIndep_intBilinForm_charZero_comb_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:17:21.700499+00:00
-- url     : https://prove2.me/submissions/302b1e65-c1e6-46d7-9b68-768f9128a287

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinIndepIntBilinFormCharZeroCombinationEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    {X : Type} [AddCommGroup X] {m : ℕ} (gam : Fin m → LinearMap.BilinForm ℤ X)
    (k : Type) [Field k] [CharZero k] (a : Fin m → k) :
    LinearIndependent ℤ gam → (∀ y z, ∑ i, a i * (gam i y z : k) = 0) → a = 0 := by
  intro hli hsum

  let L : LinearMap.BilinForm ℤ X →ₗ[ℤ] (X → X → ℚ) :=
    { toFun := fun B y z => ((B y z : ℤ) : ℚ)
      map_add' := by intro B C; funext y z; simp
      map_smul' := by intro n B; funext y z; simp }
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro B hB
    ext y z
    have := congrFun (congrFun hB y) z
    simpa [L] using this
  have hZ : LinearIndependent ℤ (L ∘ gam) := hli.map' L hker
  have hQ : LinearIndependent ℚ (L ∘ gam) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp hZ
  funext j
  by_contra hj
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero ℚ (V := k) hj
  have hrel : ∑ i, ℓ (a i) • (L ∘ gam) i = 0 := by
    funext y z
    have h0 := congrArg ℓ (hsum y z)
    rw [map_sum, map_zero] at h0
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, Pi.zero_apply, smul_eq_mul, L,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (a i), ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]
  have := (Fintype.linearIndependent_iff.mp hQ) _ hrel j
  exact hℓ this
end GlobalTheory
