-- Prove2me | solution 1 for GlobalTheory.monic_splits_of_separable_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:22:48.554075+00:00
-- url     : https://prove2.me/submissions/e9bcd4d1-6690-43e9-90cd-91ecca7b8288

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MonicSplitsValuationSubringOfSeparableReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (Ω : Type) [Field Ω] [IsSepClosed Ω]
    (V : ValuationSubring Ω) (q : Polynomial V) (hq : q.Monic)
    (hs : (q.map (IsLocalRing.residue V)).Separable) :
    ∃ s : Multiset V, q = (s.map fun b => Polynomial.X - Polynomial.C b).prod := by
  have hinj : Function.Injective (algebraMap V Ω) := IsFractionRing.injective V Ω

  have hQ : (q.map (algebraMap V Ω)).Splits := by
    rw [splits_iff_splits]
    right
    intro g hg hgd
    obtain ⟨g₀, hg₀⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd Ω hq hgd
    have hg0 : g ≠ 0 := hg.ne_zero
    have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
    have hmap : g₀.map (algebraMap V Ω) = g * C g.leadingCoeff⁻¹ := by
      set c := g.leadingCoeff with hc
      rw [← hg₀, mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, mul_one]
    have hmapm : (g₀.map (algebraMap V Ω)).Monic := by
      rw [hmap]; exact monic_mul_leadingCoeff_inv hg0
    have hg₀m : g₀.Monic := monic_of_injective hinj hmapm
    have hdvd : g₀ ∣ q := by
      rw [← map_dvd_map (algebraMap V Ω) hinj hg₀m, hmap]
      refine dvd_trans (Dvd.intro (C g.leadingCoeff) ?_) hgd
      rw [mul_assoc, ← C_mul, inv_mul_cancel₀ hlc, C_1, mul_one]
    have hsep₀ : (g₀.map (residue V)).Separable :=
      hs.of_dvd (Polynomial.map_dvd _ hdvd)
    have hdeg : (g₀.map (residue V)).natDegree = g.natDegree := by
      rw [hg₀m.natDegree_map, ← natDegree_map_eq_of_injective hinj, hmap,
        natDegree_mul_C (inv_ne_zero hlc)]
    have hgdeg : g.natDegree ≠ 0 := fun h =>
      hg.not_isUnit (isUnit_iff_degree_eq_zero.mpr ((degree_eq_iff_natDegree_eq hg0).mpr h))
    have hder₀ : derivative (g₀.map (residue V)) ≠ 0 := by
      intro h0
      have hu : IsUnit (g₀.map (residue V)) := by
        have := hsep₀
        rw [Polynomial.Separable, h0, isCoprime_zero_right] at this
        exact this
      exact hgdeg (hdeg ▸ natDegree_eq_zero_of_isUnit hu)
    have hder : derivative g ≠ 0 := by
      intro h0
      apply hder₀
      have h1 : derivative (g₀.map (algebraMap V Ω)) = 0 := by
        rw [hmap, derivative_mul, derivative_C, h0]; simp
      rw [derivative_map] at h1 ⊢
      have h2 : derivative g₀ = 0 := by
        apply Polynomial.map_injective _ hinj
        rw [h1, Polynomial.map_zero]
      rw [h2, Polynomial.map_zero]
    exact IsSepClosed.degree_eq_one_of_irreducible Ω hg
      ((separable_iff_derivative_ne_zero hg).mpr hder)
  have hroots : ∀ a ∈ (q.map (algebraMap V Ω)).roots, a ∈ (algebraMap V Ω).range := by
    intro a ha
    have hne : q.map (algebraMap V Ω) ≠ 0 := (hq.map _).ne_zero
    have hr : aeval a q = 0 := by
      rw [mem_roots hne, IsRoot, eval_map_algebraMap] at ha
      exact ha
    have hint : IsIntegral V a := ⟨q, hq, by rwa [← aeval_def]⟩
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := Ω)).mp hint
    exact ⟨y, hy⟩
  have hqs : q.Splits := Splits.of_splits_map_of_injective hinj hQ hroots
  exact ⟨q.roots, hqs.eq_prod_roots_of_monic hq⟩
end GlobalTheory
