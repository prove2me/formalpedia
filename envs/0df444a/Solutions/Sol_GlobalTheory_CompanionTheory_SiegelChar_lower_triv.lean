-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelChar.lower_triv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:55.252193+00:00
-- url     : https://prove2.me/submissions/a66c7dea-5eb2-4b09-8b59-e44409925cb4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SplitQuadraticAlgebraOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelChar
variable {E : Type} [CommRing E] {R : Type} [Ring R] [Algebra E R] {c : E → E} {σ : R →+ R}
  {G : Type} [Group G] {φ : G →* R} {e f : R}
namespace GlobalTheory.CompanionTheory.SiegelChar
theorem _root_.solution (hsm : ∀ (a : E) (x : R), σ (a • x) = c a • σ x) (h1 : σ 1 = 1)
    {i2 i3 : E} (h2 : 2 * i2 = 1) (h3 : 3 * i3 = 1) (c2 : c 2 = 2) (ci2 : c i2 = i2) (ci3 : c i3 = i3)
    (hinj : Function.Injective φ) (hsurj : ∀ x, σ x * x = 1 → ∃ g, φ g = x)
    (hef : e + f = 1) (hee : e * e = e) (hff : f * f = f) (hef0 : e * f = 0) (hfe0 : f * e = 0)
    (hse : σ e = f) (hsf : σ f = e) (lam : G →* ℂˣ) (s : R) (hes : e * s = 0) (hsf0 : s * f = 0) (hs : σ s = -s) :
    ∃ n, φ n = 1 + s ∧ lam n = 1 := by
  have hsfe : ∀ t : R, e * t = 0 → f * t = t := fun t ht => by
    calc f * t = e * t + f * t := by rw [ht, zero_add]
      _ = t := by rw [← add_mul, hef, one_mul]
  have htee : ∀ t : R, t * f = 0 → t * e = t := fun t ht => by
    calc t * e = t * e + t * f := by rw [ht, add_zero]
      _ = t := by rw [← mul_add, hef, mul_one]
  have hsq : ∀ t : R, e * t = 0 → t * f = 0 → t * t = 0 := fun t h1' h2' => by
    calc t * t = (t * e) * (f * t) := by rw [htee t h2', hsfe t h1']
      _ = t * (e * f) * t := by simp only [mul_assoc]
      _ = 0 := by rw [hef0, mul_zero, zero_mul]
  have hpow : ∀ (y : R), y * y = 0 → ∀ k : ℕ, (1 + y) ^ k = 1 + (k : R) * y := by
    intro y hy k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, Nat.cast_succ]
      have hky : (k : R) * y * y = 0 := by rw [mul_assoc, hy, mul_zero]
      calc (1 + (k : R) * y) * (1 + y) = 1 + (k : R) * y + y + (k : R) * y * y := by noncomm_ring
        _ = 1 + ((k : R) + 1) * y := by rw [hky]; noncomm_ring
  have hnat : ∀ (k : ℕ) (a : E) (t : R), (k : R) * (a • t) = ((k : E) * a) • t := by
    intro k a t
    rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul E, smul_smul]
  have hunit : ∀ t : R, σ t = -t → t * t = 0 → σ (1 + t) * (1 + t) = 1 := by
    intro t hts htt
    rw [map_add, h1, hts]
    calc (1 + -t) * (1 + t) = 1 - t * t := by noncomm_ring
      _ = 1 := by rw [htt, sub_zero]
  have h2' : i2 * 2 = 1 := by rw [mul_comm, h2]
  have key : ∀ (t : R), e * t = 0 → t * f = 0 → σ t = -t → ∀ n : G, φ n = 1 + t → lam n ^ 3 = 1 := by
    intro t hte htf hts n hn
    obtain ⟨d, hd⟩ : ∃ d : R, d = (2 : E) • e + i2 • f := ⟨_, rfl⟩
    obtain ⟨d', hd'⟩ : ∃ d' : R, d' = i2 • e + (2 : E) • f := ⟨_, rfl⟩
    have hdd' : d * d' = 1 := by
      rw [hd, hd']
      simp only [add_mul, mul_add, smul_mul_smul_comm, hee, hff, hef0, hfe0, smul_zero, add_zero,
        zero_add, h2, h2', one_smul, hef]
    have hd'd : d' * d = 1 := by
      rw [hd, hd']
      simp only [add_mul, mul_add, smul_mul_smul_comm, hee, hff, hef0, hfe0, smul_zero, add_zero,
        zero_add, h2, h2', one_smul, hef]
    have hσd : σ d * d = 1 := by
      rw [hd, map_add, hsm, hsm, c2, ci2, hse, hsf]
      simp only [add_mul, mul_add, smul_mul_smul_comm, hee, hff, hef0, hfe0, smul_zero, add_zero,
        zero_add, h2, h2', one_smul]
      first
        | exact hef
        | (rw [add_comm]; exact hef)
    obtain ⟨td, htd⟩ := hsurj d hσd
    have htdinv : φ td⁻¹ = d' := by
      have h0 : d * φ td⁻¹ = 1 := by rw [← htd, ← map_mul, mul_inv_cancel, map_one]
      calc φ td⁻¹ = (d' * d) * φ td⁻¹ := by rw [hd'd, one_mul]
        _ = d' := by rw [mul_assoc, h0, mul_one]
    have hdt : d * t = i2 • t := by
      rw [hd, add_mul, smul_mul_assoc, smul_mul_assoc, hte, smul_zero, zero_add, hsfe t hte]
    have htd' : t * d' = i2 • t := by
      rw [hd', mul_add, mul_smul_comm, mul_smul_comm, htf, smul_zero, add_zero, htee t htf]
    have hm : φ (td * n * td⁻¹) = 1 + (i2 * i2) • t := by
      rw [map_mul, map_mul, htd, htdinv, hn, mul_add, mul_one, add_mul, hdd', hdt, smul_mul_assoc,
        htd', smul_smul]
    have hyy : ((i2 * i2) • t) * ((i2 * i2) • t) = 0 := by
      rw [smul_mul_smul_comm, hsq t hte htf, smul_zero]
    have hm4 : (td * n * td⁻¹) ^ 4 = n := by
      apply hinj
      rw [map_pow, hm, hpow _ hyy 4, hn, hnat]
      have h4 : ((4 : ℕ) : E) * (i2 * i2) = 1 := by
        push_cast
        calc (4 : E) * (i2 * i2) = (2 * i2) * (2 * i2) := by ring
          _ = 1 := by rw [h2, one_mul]
      rw [h4, one_smul]
    have hlm : lam (td * n * td⁻¹) = lam n := by
      rw [map_mul, map_mul, map_inv, mul_comm (lam td), mul_assoc, mul_inv_cancel, mul_one]
    have h4 : lam n = lam n ^ 4 := by
      conv_lhs => rw [← hm4]
      rw [map_pow, hlm]
    have h5 : lam n ^ 3 * lam n = 1 * lam n := by
      rw [one_mul, ← pow_succ]
      exact h4.symm
    exact mul_right_cancel h5
  obtain ⟨n, hn⟩ := hsurj (1 + s) (hunit s hs (hsq s hes hsf0))
  have hes' : e * (i3 • s) = 0 := by rw [mul_smul_comm, hes, smul_zero]
  have hsf' : (i3 • s) * f = 0 := by rw [smul_mul_assoc, hsf0, smul_zero]
  have hs' : σ (i3 • s) = -(i3 • s) := by rw [hsm, ci3, hs, smul_neg]
  obtain ⟨n', hn'⟩ := hsurj (1 + i3 • s) (hunit _ hs' (hsq _ hes' hsf'))
  have hn3 : n' ^ 3 = n := by
    apply hinj
    rw [map_pow, hn', hpow _ (hsq _ hes' hsf') 3, hn, hnat]
    have h3' : ((3 : ℕ) : E) * i3 = 1 := by
      push_cast
      exact h3
    rw [h3', one_smul]
  refine ⟨n, hn, ?_⟩
  rw [← hn3, map_pow]
  exact key _ hes' hsf' hs' n' hn'
end GlobalTheory.CompanionTheory.SiegelChar
