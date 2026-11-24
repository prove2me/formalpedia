-- Prove2me | solution 1 for GlobalTheory.MonicSeparableProduct.exists_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:17:30.852668+00:00
-- url     : https://prove2.me/submissions/38faffd5-5e7d-4fc7-93ec-a8c2068a56ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MonicEqProd
import Theorems.Thm_GlobalTheory_MonicSeparableProduct_monic_eq_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MonicSeparableProduct
open Polynomial
namespace GlobalTheory.MonicSeparableProduct
theorem _root_.solution {F : Type} [Field F] [IsAlgClosed F] (W : ValuationSubring F) (p : W)
    (hp : ∀ a : W, ¬IsUnit a → ∃ n : ℕ, a ^ n ∈ Ideal.span {p})
    (A : Type) [CommRing A] [Algebra W A] [Module.Finite W A] (aug : A →ₐ[W] W)
    (t : A) (ht : aug t = 0) :
    ∃ s b : A, IsUnit (aug s) ∧ s = b * s ^ 2 ∧
      ∀ P : Ideal A, P.IsPrime → algebraMap W A p ∈ P → s ∉ P → t ∈ P := by
  classical
  obtain ⟨f, hf, hft⟩ : IsIntegral W t := Algebra.IsIntegral.isIntegral t
  obtain ⟨M, hM⟩ := monic_eq_prod W _ f hf rfl
  have h0 : (M.map (fun r => t - algebraMap W A r)).prod = 0 := by
    have : aeval t f = 0 := hft
    rw [hM, map_multiset_prod, Multiset.map_map] at this
    simpa using this
  set s : A := ((M.filter (fun r => IsUnit r)).map (fun r => t - algebraMap W A r)).prod with hs
  set g : A := ((M.filter (fun r => ¬ IsUnit r)).map (fun r => t - algebraMap W A r)).prod with hg
  have hsg : s * g = 0 := by
    rw [hs, hg, ← Multiset.prod_add, ← Multiset.map_add, Multiset.filter_add_not, h0]
  have hcop : IsCoprime s g := by
    rw [hs]
    refine Multiset.prod_induction (fun x => IsCoprime x g) _
      (fun a b ha hb => ha.mul_left hb) isCoprime_one_left ?_
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
    have hru : IsUnit r := (Multiset.mem_filter.1 hr).2
    rw [hg]
    refine Multiset.prod_induction (fun y => IsCoprime (t - algebraMap W A r) y) _
      (fun a b ha hb => ha.mul_right hb) isCoprime_one_right ?_
    intro y hy
    obtain ⟨r', hr', rfl⟩ := Multiset.mem_map.1 hy
    have hru' : ¬ IsUnit r' := (Multiset.mem_filter.1 hr').2
    have hd : IsUnit (r - r') := by
      by_contra hnu
      have h1 : r - r' ∈ IsLocalRing.maximalIdeal W := hnu
      have h2 : r' ∈ IsLocalRing.maximalIdeal W := hru'
      have h3 : r ∈ IsLocalRing.maximalIdeal W := by
        simpa using add_mem h1 h2
      exact h3 hru
    obtain ⟨u, hu⟩ := hd.exists_left_inv
    refine ⟨-algebraMap W A u, algebraMap W A u, ?_⟩
    have := congrArg (algebraMap W A) hu
    rw [map_mul, map_sub, map_one] at this
    linear_combination this
  obtain ⟨b, a, hab⟩ := hcop
  refine ⟨s, b, ?_, ?_, ?_⟩
  · rw [hs, map_multiset_prod]
    refine Multiset.prod_induction IsUnit _ (fun a b ha hb => ha.mul hb) isUnit_one ?_
    intro x hx
    rw [Multiset.map_map] at hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
    have hru : IsUnit r := (Multiset.mem_filter.1 hr).2
    have : aug (t - algebraMap W A r) = -r := by
      rw [map_sub, ht, AlgHom.commutes]; simp
    show IsUnit (aug (t - algebraMap W A r))
    rw [this]; exact hru.neg
  · linear_combination (-s) * hab + a * hsg
  · intro P hP hpP hsP
    have hgP : g ∈ P := by
      have : s * g ∈ P := by rw [hsg]; exact P.zero_mem
      exact (hP.mem_or_mem this).resolve_left hsP
    rw [hg] at hgP
    obtain ⟨y, hy, hyP⟩ := (hP.multiset_prod_mem_iff_exists_mem _).1 hgP
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨n, hn⟩ := hp r (Multiset.mem_filter.1 hr).2
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
    have : algebraMap W A r ^ n ∈ P := by
      rw [← map_pow, ← hc, map_mul]
      exact P.mul_mem_left _ hpP
    have h2 := hP.mem_of_pow_mem n this
    simpa using add_mem hyP h2
end GlobalTheory.MonicSeparableProduct
