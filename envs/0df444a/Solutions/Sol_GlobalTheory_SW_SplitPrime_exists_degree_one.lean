-- Prove2me | solution 1 for GlobalTheory.SW.SplitPrime.exists_degree_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:43.448554+00:00
-- url     : https://prove2.me/submissions/3af5fe79-9070-4bff-9ccc-779ff5571af2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsGoodSplitPrimeCmField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
namespace GlobalTheory.SW.SplitPrime
open Polynomial
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
open Polynomial in
private theorem exists_prime_dvd_eval_not_dvd_of_natDegree_pos (h : ℤ[X]) (hh : 0 < h.natDegree) (M : ℤ)
    (hM : M ≠ 0) : ∃ (n : ℤ) (p : ℕ), p.Prime ∧ (p : ℤ) ∣ h.eval n ∧ ¬ (p : ℤ) ∣ M := by
  set c := h.coeff 0 with hcdef
  by_cases hc : c = 0
  · obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (M.natAbs + 1)
    refine ⟨0, p, hp, ?_, fun hd => ?_⟩
    · rw [← coeff_zero_eq_eval_zero, ← hcdef, hc]; exact dvd_zero _
    · have := Int.natAbs_dvd_natAbs.mpr hd
      simp only [Int.natAbs_natCast] at this
      exact absurd (Nat.le_of_dvd (Int.natAbs_pos.mpr hM) this) (by omega)
  obtain ⟨q, hq⟩ := X_dvd_sub_C (p := h)
  rw [← hcdef] at hq
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [mul_zero, sub_eq_zero] at hq
    rw [hq, natDegree_C] at hh; exact lt_irrefl _ hh
  set r : ℤ[X] := q.comp (C (c * M) * X) with hr
  set G : ℤ[X] := 1 + C M * X * r with hG
  have hev : ∀ t : ℤ, h.eval (c * M * t) = c * G.eval t := by
    intro t
    have := congrArg (eval (c * M * t)) hq
    simp only [eval_sub, eval_C, eval_mul, eval_X] at this
    simp only [hG, hr, eval_add, eval_one, eval_mul, eval_C, eval_X, eval_comp]
    linear_combination this
  have hr0 : r ≠ 0 := by
    rw [hr, Ne, comp_eq_zero_iff]
    rintro (h0 | ⟨-, h1⟩)
    · exact hq0 h0
    · have := congrArg (coeff · 1) h1
      simp only [coeff_C_mul_X, coeff_C] at this
      simp at this
      exact this.elim hc hM
  have hG1 : G ≠ C 1 := by
    intro h1
    rw [hG, ← C_1, add_eq_left] at h1
    exact mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hM) X_ne_zero) hr0 h1
  have hG2 : G ≠ C (-1) := by
    intro h1
    have := congrArg (eval 0) h1
    simp [hG] at this
  have hfin : ({t : ℤ | G.eval t = 1} ∪ {t | G.eval t = -1}).Finite := by
    refine Set.Finite.union ?_ ?_ <;> by_contra hinf
    · exact hG1 (eq_of_infinite_eval_eq G (C 1) (by simpa using hinf))
    · exact hG2 (eq_of_infinite_eval_eq G (C (-1)) (by simpa using hinf))
  obtain ⟨t, ht⟩ := hfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or] at ht
  set g := G.eval t with hg
  have hgabs : g.natAbs ≠ 1 := by
    intro h1
    rcases Int.natAbs_eq_iff.mp h1 with h2 | h2
    · exact ht.1 h2
    · exact ht.2 h2
  have hp := Nat.minFac_prime hgabs
  have hpg : (g.natAbs.minFac : ℤ) ∣ g := Int.ofNat_dvd_left.mpr (Nat.minFac_dvd _)
  refine ⟨c * M * t, g.natAbs.minFac, hp, ?_, fun hpM => ?_⟩
  · rw [hev]; exact Dvd.dvd.mul_left hpg c
  · have hg' : g = 1 + M * (t * r.eval t) := by
      simp only [hg, hG, eval_add, eval_one, eval_mul, eval_C, eval_X]; ring
    have h4 : (1 : ℤ) = g - M * (t * r.eval t) := by rw [hg']; ring
    have : (g.natAbs.minFac : ℤ) ∣ 1 := by
      rw [h4]; exact dvd_sub hpg (Dvd.dvd.mul_right hpM _)
    exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
open Polynomial in
private theorem span_prime_sup_span_proper_of_dvd_norm {E : Type} [Field E] [NumberField E] (x : 𝓞 E)
    (p : ℕ) (hp : p.Prime) (hdvd : (p : ℤ) ∣ Algebra.norm ℤ x) :
    Ideal.span {(p : 𝓞 E)} ⊔ Ideal.span {x} ≠ ⊤ := by
  intro htop
  have h1 : (1 : 𝓞 E) ∈ Ideal.span {(p : 𝓞 E)} ⊔ Ideal.span {x} := htop ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  by_cases hx : x = 0
  · subst hx
    rw [Ideal.span_singleton_eq_bot.mpr rfl, Submodule.mem_bot] at hb
    subst hb
    rw [add_zero] at hab
    have hu : IsUnit (Algebra.norm ℤ (algebraMap ℤ (𝓞 E) p)) := by
      rw [map_natCast]; exact (isUnit_iff_exists_inv'.mpr ⟨y, hab⟩).map _
    rw [Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff] at hu
    have := hp.two_le
    rcases hu with h | h <;> omega
  · set I := Ideal.span {x}
    have hcard : Nat.card (𝓞 E ⧸ I) = (Algebra.norm ℤ x).natAbs := by
      rw [← Ideal.absNorm_span_singleton]; exact (Nat.add_zero _).symm
    have hne : (Algebra.norm ℤ x).natAbs ≠ 0 := by
      rw [Int.natAbs_ne_zero, Ne, Algebra.norm_eq_zero_iff]; exact hx
    haveI : Finite (𝓞 E ⧸ I) := Nat.finite_of_card_ne_zero (hcard ▸ hne)
    haveI := Fact.mk hp
    have hpc : p ∣ Nat.card (𝓞 E ⧸ I) := by
      rw [hcard]; simpa using Int.natAbs_dvd_natAbs.mpr hdvd
    obtain ⟨z, hz⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 E ⧸ I) p hpc
    have hpz : (p : 𝓞 E ⧸ I) * z = 0 := by
      rw [← nsmul_eq_mul, ← hz]; exact addOrderOf_nsmul_eq_zero z
    have hunit : (Ideal.Quotient.mk I y) * (p : 𝓞 E ⧸ I) = 1 := by
      have := congrArg (Ideal.Quotient.mk I) hab
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb, add_zero, map_one, map_mul,
        map_natCast] at this
      exact this
    have hz0 : z = 0 := by
      calc z = (Ideal.Quotient.mk I y) * (p : 𝓞 E ⧸ I) * z := by rw [hunit, one_mul]
        _ = 0 := by rw [mul_assoc, hpz, mul_zero]
    rw [hz0, addOrderOf_zero] at hz
    exact hp.one_lt.ne hz
end GlobalTheory.SW.SplitPrime
end

set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SplitPrime
open Polynomial
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real Classical
open Polynomial
namespace GlobalTheory.SW.SplitPrime
namespace _root_.GlobalTheory.SW.SplitPrime
theorem _root_.solution {E : Type} [Field E] [NumberField E] (θ : 𝓞 E)
    (hθ : θ ≠ 0) (d : ℤ) (hd : d ≠ 0) (hden : ∀ a : 𝓞 E, ∃ g : ℤ[X], (d : 𝓞 E) * a = aeval θ g)
    (N : ℤ) (hN : N ≠ 0) :
    ∃ P : Ideal (𝓞 E), P.IsMaximal ∧ (N : 𝓞 E) ∉ P ∧
      Function.Surjective (Int.castRingHom (𝓞 E ⧸ P)) := by
  obtain ⟨n, p, hp, hpn, hpM⟩ := exists_prime_dvd_eval_not_dvd_of_natDegree_pos
    (LinearMap.charpoly (Algebra.lmul ℤ (𝓞 E) θ)) (by
      rw [LinearMap.charpoly_natDegree]; exact Module.finrank_pos) (N * d) (mul_ne_zero hN hd)
  have hnorm : (LinearMap.charpoly (Algebra.lmul ℤ (𝓞 E) θ)).eval n =
      Algebra.norm ℤ ((n : 𝓞 E) - θ) := by
    rw [LinearMap.eval_charpoly, Algebra.norm_apply]
    congr 1
    ext x
    simp [Algebra.smul_def, sub_mul]
  rw [hnorm] at hpn
  obtain ⟨P, hP, hJ⟩ := Ideal.exists_le_maximal _ (span_prime_sup_span_proper_of_dvd_norm _ p hp hpn)
  have hpP : (p : 𝓞 E) ∈ P := hJ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have hxP : (n : 𝓞 E) - θ ∈ P := hJ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hcop : ∀ k : ℤ, ¬ (p : ℤ) ∣ k → ∃ v : ℤ, (v : 𝓞 E) * k - 1 ∈ P := by
    intro k hk
    obtain ⟨u, v, huv⟩ := (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hk
    refine ⟨v, ?_⟩
    have : (v : 𝓞 E) * k - 1 = -((u : 𝓞 E) * (p : 𝓞 E)) := by
      have h2 := congrArg (Int.cast : ℤ → 𝓞 E) huv
      push_cast at h2
      linear_combination h2
    rw [this]
    exact P.neg_mem_iff.mpr (P.mul_mem_left _ hpP)
  have hnot : ∀ k : ℤ, ¬ (p : ℤ) ∣ k → (k : 𝓞 E) ∉ P := by
    intro k hk hkP
    obtain ⟨v, hv⟩ := hcop k hk
    exact hP.ne_top ((Ideal.eq_top_iff_one _).mpr (by
      have := P.sub_mem (P.mul_mem_left (v : 𝓞 E) hkP) hv
      simpa using this))
  refine ⟨P, hP, hnot N (fun h => hpM (Dvd.dvd.mul_right h d)), fun y => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨g, hg⟩ := hden a
  obtain ⟨v, hv⟩ := hcop d (fun h => hpM (Dvd.dvd.mul_left h N))
  refine ⟨v * g.eval n, ?_⟩
  have hθn : Ideal.Quotient.mk P θ = ((n : ℤ) : 𝓞 E ⧸ P) := by
    rw [← map_intCast (Ideal.Quotient.mk P)]
    exact (Ideal.Quotient.eq.mpr (by rw [← P.neg_mem_iff, neg_sub]; exact hxP))
  have hga : Ideal.Quotient.mk P ((d : 𝓞 E) * a) = ((g.eval n : ℤ) : 𝓞 E ⧸ P) := by
    have h3 := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ ℤ P) θ g
    rw [Ideal.Quotient.mkₐ_eq_mk] at h3
    rw [hg, ← h3, hθn, ← eq_intCast (algebraMap ℤ (𝓞 E ⧸ P)),
      aeval_algebraMap_apply_eq_algebraMap_eval, eq_intCast]
  have hv' : Ideal.Quotient.mk P ((v : 𝓞 E) * d) = 1 := by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk P), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hv
  simp only [eq_intCast, Int.cast_mul]
  rw [← hga, ← map_intCast (Ideal.Quotient.mk P) v, ← map_mul, ← mul_assoc, map_mul, hv', one_mul]
end _root_.GlobalTheory.SW.SplitPrime
end GlobalTheory.SW.SplitPrime
