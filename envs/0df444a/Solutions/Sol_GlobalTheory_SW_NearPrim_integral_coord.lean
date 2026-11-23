-- Prove2me | solution 1 for GlobalTheory.SW.NearPrim.integral_coord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:23.091496+00:00
-- url     : https://prove2.me/submissions/e783e06b-2d66-4c3d-86c6-98bb0379754b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsBoundedMultipleNearInteger
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.NearPrim
namespace GlobalTheory.SW.NearPrim
theorem _root_.solution {E : Type} [Field E] [NumberField E] {k : ℕ}
    (L : AddSubgroup (Fin k → E))
    (hsm : ∀ y : E, IsIntegral ℤ y → ∀ s ∈ L, y • s ∈ L) (M : ℕ)
    (hM : ∀ x : E, ∃ (m : ℕ) (y : E), 0 < m ∧ m ≤ M ∧ IsIntegral ℤ y ∧
      ‖canonicalEmbedding E (m * x - y)‖ < 1)
    (a : Matrix (Fin k) (Fin k) E) (haL : ∀ i, a i ∈ L) (ha0 : ∀ i j, i < j → a i j = 0)
    (hai : ∀ i, a i i ≠ 0)
    (hmin : ∀ i, ∀ s ∈ L, (∀ j, i < j → s j = 0) → s i ≠ 0 →
        ‖canonicalEmbedding E (a i i)‖ ≤ ‖canonicalEmbedding E (s i)‖) (p : ℕ) (hp : p ≤ k) :
    ∀ t : Fin k → E, (∀ j : Fin k, p ≤ j → t j = 0) → t ᵥ* a ∈ L →
      ∀ i, IsIntegral ℤ (((M.factorial ^ p : ℕ) : E) * t i) := by
  classical
  induction p with
  | zero =>
    intro t ht _ i
    rw [ht i (Nat.zero_le _), mul_zero]
    exact isIntegral_zero
  | succ p ih =>
    intro t ht hL i
    let q : Fin k := ⟨p, hp⟩
    obtain ⟨m, y, hm0, hmM, hy, hlt⟩ := hM (t q)
    set t' : Fin k → E := (m : E) • t - y • Pi.single q 1 with ht'
    have ht'L : t' ᵥ* a ∈ L := by
      rw [ht', sub_vecMul, smul_vecMul, smul_vecMul, single_one_vecMul]
      exact L.sub_mem (hsm _ (isIntegral_natCast m) _ hL) (hsm _ hy _ (haL q))
    have hz : ∀ j, q < j → t' j = 0 := fun j hj => by
      simp [ht', hj.ne', ht j hj]
    have hq : t' q = m * t q - y := by simp [ht']
    have hs : ∀ j, q ≤ j → (t' ᵥ* a) j = t' j * a j j := by
      intro j hj
      rw [vecMul, dotProduct]
      refine Finset.sum_eq_single j (fun l _ hl => ?_) (by simp)
      rcases lt_or_gt_of_ne hl with h | h
      · rw [ha0 l j h, mul_zero]
      · rw [hz l (hj.trans_lt h), zero_mul]
    have hq0 : t' q = 0 := by
      by_contra hne
      have h1 := hmin q _ ht'L (fun j hj => by rw [hs j hj.le, hz j hj, zero_mul])
        (by rw [hs q le_rfl]; exact mul_ne_zero hne (hai q))
      rw [hs q le_rfl, map_mul, hq] at h1
      have h2 : 0 < ‖canonicalEmbedding E (a q q)‖ := by
        rw [norm_pos_iff]
        exact fun h => hai q (canonicalEmbedding_injective E (h.trans (map_zero _).symm))
      have h3 := norm_mul_le (canonicalEmbedding E (m * t q - y)) (canonicalEmbedding E (a q q))
      nlinarith
    have h := ih (by omega) t' (fun j hj => by
      rcases (show q ≤ j from hj).eq_or_lt with rfl | h
      · exact hq0
      · exact hz j h) ht'L i
    obtain ⟨e, he⟩ := Nat.dvd_factorial hm0 hmM
    have hint : IsIntegral ℤ ((Pi.single q 1 : Fin k → E) i) := by
      by_cases h : i = q
      · subst h; simpa using isIntegral_one
      · simpa [h] using isIntegral_zero
    have : ((M.factorial ^ (p + 1) : ℕ) : E) * t i =
        (e : E) * (((M.factorial ^ p : ℕ) : E) * t' i +
          ((M.factorial ^ p : ℕ) : E) * (y * (Pi.single q 1 : Fin k → E) i)) := by
      rw [pow_succ, Nat.cast_mul]
      nth_rewrite 2 [he]
      simp only [ht', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_mul]
      ring
    rw [this]
    exact (isIntegral_natCast e).mul (h.add ((isIntegral_natCast _).mul (hy.mul hint)))
end GlobalTheory.SW.NearPrim
