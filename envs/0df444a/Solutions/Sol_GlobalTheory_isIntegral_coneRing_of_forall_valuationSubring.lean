-- Prove2me | solution 1 for GlobalTheory.isIntegral_coneRing_of_forall_valuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:02:39.52741+00:00
-- url     : https://prove2.me/submissions/dc8f65ac-d2e3-41f1-8e2d-7115bacd11a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralConeRingOfForallValuationSubring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (F K : Type) [Field F] [Field K] (φ : F →+* K) (r e : ℕ) (w : Fin r → K) (τ : K), (∀ V : ValuationSubring K, (∀ c, φ c ∈ V) → ∃ i, w i ≠ 0 ∧ τ / w i ^ e ∈ V) → ∃ (m : ℕ) (b : Fin m → MvPolynomial (Fin r) F), (Polynomial.C τ * Polynomial.X ^ e) ^ m + ∑ k, MvPolynomial.eval₂ (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X) (b k) * (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ) = 0 := by
  intro F K _ _ φ r e w τ h
  classical
  let L := FractionRing (Polynomial K)
  let j : Polynomial K →+* L := algebraMap (Polynomial K) L
  let g : MvPolynomial (Fin r) F →+* Polynomial K :=
    MvPolynomial.eval₂Hom (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X)
  let y : Polynomial K := Polynomial.C τ * Polynomial.X ^ e
  have hjinj : Function.Injective j := IsFractionRing.injective _ _
  have hx : j y ∈ (integralClosure (Subring.closure (Set.range (j.comp g))) L).toSubring := by
    rw [← iInf_valuationSubring_superset, Subring.mem_iInf]
    intro V
    obtain ⟨W, hW⟩ := V
    change j y ∈ W
    let U : ValuationSubring K := W.comap (j.comp Polynomial.C)
    have hU : ∀ c, φ c ∈ U := by
      intro c
      have : j (g (MvPolynomial.C c)) ∈ W := hW ⟨_, rfl⟩
      simpa [g, U] using this
    obtain ⟨i, hi, hτ⟩ := h U hU
    have h1 : j (Polynomial.C (w i) * Polynomial.X) ∈ W := by
      have : j (g (MvPolynomial.X i)) ∈ W := hW ⟨_, rfl⟩
      simpa [g] using this
    have h2 : j (Polynomial.C (τ / w i ^ e)) ∈ W := hτ
    have hy : y = Polynomial.C (τ / w i ^ e) * (Polynomial.C (w i) * Polynomial.X) ^ e := by
      rw [mul_pow, ← mul_assoc, ← Polynomial.C_pow, ← Polynomial.C_mul,
        div_mul_cancel₀ _ (pow_ne_zero _ hi)]
    rw [hy, map_mul, map_pow]
    exact mul_mem h2 (pow_mem h1 _)
  have hcl : Subring.closure (Set.range (j.comp g)) = (j.comp g).range := by
    rw [← RingHom.coe_range]; exact Subring.closure_eq _
  rw [hcl] at hx
  have hint : IsIntegral (j.comp g).range (j y) := hx
  obtain ⟨p, hp, hpx⟩ := hint
  have hb : ∀ k : Fin p.natDegree, ∃ b : MvPolynomial (Fin r) F, j (g b) = (p.coeff k : L) :=
    fun k => (p.coeff k).2
  choose b hb using hb
  refine ⟨p.natDegree, b, hjinj ?_⟩
  have e1 := hpx
  rw [hp.as_sum] at e1
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_finset_sum, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at e1
  rw [Finset.sum_range (fun k => algebraMap (j.comp g).range L (p.coeff k) * j y ^ k)] at e1
  rw [map_zero, ← e1, map_add, map_sum, map_pow]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow]
  exact congrArg (· * j y ^ (k : ℕ)) (hb k)
end GlobalTheory
