-- Prove2me | solution 1 for MvFormalGroup.coeff_sub_coeff_mem_of_forall_coeff_ghostComponent_eq_logCovector_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/8eaf0f2c-e9be-5471-b050-ac288e9e2251

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Theorems.Thm_MvPowerSeries_exists_wittVector_forall_coeff_ghostComponent_eq_of_forall_natCast_mul_coeff_mem
import Theorems.Thm_MvPowerSeries_le_mul_degree_of_coeff_coeff_ne_zero_of_forall_coeff_ghostComponent_eq
import Theorems.Thm_WittVector_coeff_mem_span_of_ghostComponent_mem_span_pow_of_isReduced
import Theorems.Thm_MvFormalGroup_natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add
import Theorems.Thm_WittVector_add_coeff_sub_coeff_mem_pow_of_forall_coeff_mem_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_coeff_sub_coeff_mem_of_forall_coeff_ghostComponent_eq_logCovector_of_le
p2m_attr_erase "instance" "MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid"
p2m_attr_erase "simp" "MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast"

set_option autoImplicit false

open MvPowerSeries

universe u

namespace MvFormalGroup
p2m_export "MvFormalGroup" "IsComm map linearPart mk toPowerSeries natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add"
namespace FactApC12
p2m_open "MvFormalGroup"

section Series

variable {𝓞 : Type u} [CommRing 𝓞] {d : ℕ}

private theorem natCast_mem_nonZeroDivisors (p : ℕ) (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) :
    ((p : MvPowerSeries (Fin d) 𝓞)) ∈ nonZeroDivisors (MvPowerSeries (Fin d) 𝓞) := by
  have key : ∀ x : MvPowerSeries (Fin d) 𝓞, x * (p : MvPowerSeries (Fin d) 𝓞) = 0 → x = 0 := by
    intro x hx
    ext m
    have h := congrArg (MvPowerSeries.coeff m) hx
    rw [show ((p : MvPowerSeries (Fin d) 𝓞)) = C (p : 𝓞) from (map_natCast (C (σ := Fin d) (R := 𝓞)) p).symm,
      map_zero] at h
    rw [MvPowerSeries.coeff_mul_C] at h
    rw [map_zero]
    exact (mem_nonZeroDivisors_iff.1 hp).2 _ h
  exact mem_nonZeroDivisors_iff.2 ⟨fun x hx => key x (by rwa [mul_comm]), key⟩

private theorem mem_pow_span_X_of_forall_le_degree (e : ℕ) :
    ∀ f : MvPowerSeries (Fin d) 𝓞, (∀ μ : Fin d →₀ ℕ, MvPowerSeries.coeff μ f ≠ 0 → e ≤ μ.degree) →
      f ∈ Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞)) ^ e := by
  classical
  induction e with
  | zero => intro f _; rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  | succ e ih =>
    intro f hf

    let g : Fin d → MvPowerSeries (Fin d) 𝓞 := fun t μ' =>
      if ∀ t' : Fin d, t' < t → μ' t' = 0 then MvPowerSeries.coeff (μ' + Finsupp.single t 1) f else 0
    have hg : ∀ t μ', MvPowerSeries.coeff μ' (g t) =
        if ∀ t' : Fin d, t' < t → μ' t' = 0 then MvPowerSeries.coeff (μ' + Finsupp.single t 1) f else 0 :=
      fun _ _ => rfl
    have hdec : f = ∑ t : Fin d, X t * g t := by
      ext μ
      rw [map_sum]
      have hterm : ∀ t : Fin d, MvPowerSeries.coeff μ (X t * g t) =
          if 1 ≤ μ t ∧ ∀ t' : Fin d, t' < t → μ t' = 0 then MvPowerSeries.coeff μ f else 0 := by
        intro t
        rw [X_def, coeff_monomial_mul, one_mul]
        by_cases h1 : 1 ≤ μ t
        · have hle : Finsupp.single t 1 ≤ μ := Finsupp.single_le_iff.2 h1
          rw [if_pos hle, hg, tsub_add_cancel_of_le hle]
          have hiff : (∀ t' : Fin d, t' < t → (μ - Finsupp.single t 1 : Fin d →₀ ℕ) t' = 0) ↔
              (∀ t' : Fin d, t' < t → μ t' = 0) := by
            refine forall₂_congr fun t' ht' => ?_
            rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (ne_of_lt ht').symm, tsub_zero]
          by_cases hc : ∀ t' : Fin d, t' < t → μ t' = 0
          · rw [if_pos (hiff.2 hc), if_pos ⟨h1, hc⟩]
          · rw [if_neg (fun h => hc (hiff.1 h)), if_neg (fun h => hc h.2)]
        · have hle : ¬ Finsupp.single t 1 ≤ μ := fun h => h1 (Finsupp.single_le_iff.1 h)
          rw [if_neg hle, if_neg (fun h => h1 h.1)]
      simp_rw [hterm]
      by_cases hμ : μ = 0
      · subst hμ
        have h0 : MvPowerSeries.coeff (0 : Fin d →₀ ℕ) f = 0 := by
          by_contra h
          have := hf 0 h
          simp at this
        simp [h0]
      · have hne : μ.support.Nonempty := Finsupp.support_nonempty_iff.2 hμ
        let t₀ := μ.support.min' hne
        have ht₀ : μ t₀ ≠ 0 := Finsupp.mem_support_iff.1 (Finset.min'_mem _ _)
        have hmin : ∀ t' : Fin d, t' < t₀ → μ t' = 0 := by
          intro t' ht'
          by_contra h
          exact absurd (Finset.min'_le μ.support t' (Finsupp.mem_support_iff.2 h)) (not_le.2 ht')
        rw [Finset.sum_eq_single t₀]
        · rw [if_pos ⟨Nat.one_le_iff_ne_zero.2 ht₀, hmin⟩]
        · intro t _ ht
          rw [if_neg]
          rintro ⟨h1, h2⟩
          rcases lt_or_gt_of_ne ht with hlt | hgt
          · exact absurd (hmin t hlt) (Nat.one_le_iff_ne_zero.1 h1)
          · exact ht₀ (h2 t₀ hgt)
        · intro h; exact absurd (Finset.mem_univ t₀) h
    rw [hdec]
    refine Ideal.sum_mem _ fun t _ => ?_
    rw [pow_succ']
    refine Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_range_self t)) (ih (g t) fun μ' hμ' => ?_)
    rw [hg] at hμ'
    split_ifs at hμ' with hcond
    · have := hf _ hμ'
      rw [map_add, Finsupp.degree_single] at this
      omega
    · exact absurd rfl hμ'

private theorem mem_span_X_of_constantCoeff_eq_zero (f : MvPowerSeries (Fin d) 𝓞)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    f ∈ Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞)) := by
  have := mem_pow_span_X_of_forall_le_degree 1 f fun μ hμ => by
    rw [Nat.one_le_iff_ne_zero]
    intro hdeg
    rw [Finsupp.degree_eq_zero_iff] at hdeg
    subst hdeg
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at hμ
    exact hμ hf
  rwa [pow_one] at this

end Series

section Witt

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R]

omit hp in
private theorem coeff_init (n : ℕ) (x : WittVector p R) (i : ℕ) :
    (WittVector.init n x).coeff i = if i < n then x.coeff i else 0 := by
  rw [WittVector.init, WittVector.coeff_select, WittVector.selectPoly]
  split_ifs with h
  · rw [MvPolynomial.aeval_X]
  · rw [map_zero]

private theorem iterate_verschiebung_coeff_lt (x : WittVector p R) :
    ∀ (s i : ℕ), i < s → ((WittVector.verschiebung)^[s] x).coeff i = 0 := by
  intro s
  induction s with
  | zero => intro i hi; omega
  | succ s ih =>
    intro i hi
    rw [Function.iterate_succ_apply']
    cases i with
    | zero => exact WittVector.verschiebung_coeff_zero _
    | succ i => rw [WittVector.verschiebung_coeff_succ]; exact ih i (by omega)

private theorem ghostComponent_iterate_verschiebung (x : WittVector p R) :
    ∀ (s n : ℕ), WittVector.ghostComponent (n + s) ((WittVector.verschiebung)^[s] x) =
      (p : R) ^ s * WittVector.ghostComponent n x := by
  intro s
  induction s with
  | zero => intro n; simp
  | succ s ih =>
    intro n
    rw [Function.iterate_succ_apply', show n + (s + 1) = (n + s) + 1 by omega,
      WittVector.ghostComponent_verschiebung, ih, pow_succ]
    ring

private theorem iterate_verschiebung_add (x y : WittVector p R) (s : ℕ) :
    (WittVector.verschiebung)^[s] (x + y) =
      (WittVector.verschiebung)^[s] x + (WittVector.verschiebung)^[s] y := by
  induction s with
  | zero => rfl
  | succ s ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, map_add]

private theorem add_iterate_verschiebung_coeff (a w : WittVector p R) (s : ℕ)
    (ha : ∀ i, s ≤ i → a.coeff i = 0) (j : ℕ) :
    (a + (WittVector.verschiebung)^[s] w).coeff (j + s) = w.coeff j := by
  rw [WittVector.coeff_add_of_disjoint]
  · rw [ha _ (by omega), zero_add, WittVector.iterate_verschiebung_coeff]
  · intro n
    by_cases hn : n < s
    · exact Or.inr (iterate_verschiebung_coeff_lt w s n hn)
    · exact Or.inl (ha n (by omega))

private theorem add_coeff_eq_init_add_init_coeff (x y : WittVector p R) (n i : ℕ) (hi : i < n) :
    (x + y).coeff i = (WittVector.init n x + WittVector.init n y).coeff i := by
  have h := congrArg (fun z => WittVector.coeff z i) (WittVector.init_add x y n)
  simp only [coeff_init, if_pos hi] at h
  exact h

private theorem add_coeff_sub_coeff_mem (J : Ideal R) (a b : WittVector p R) (M : ℕ)
    (ha : ∀ i, i < M → a.coeff i ∈ J) (k : ℕ) (hk : k < M) :
    (a + b).coeff k - b.coeff k ∈ J := by
  rw [← Ideal.Quotient.eq, ← WittVector.map_coeff, ← WittVector.map_coeff, map_add]
  set a' := WittVector.map (Ideal.Quotient.mk J) a
  set b' := WittVector.map (Ideal.Quotient.mk J) b
  have ha' : a' ∈ RingHom.ker (WittVector.truncate M) := by
    rw [WittVector.mem_ker_truncate]
    intro i hi
    rw [WittVector.map_coeff, Ideal.Quotient.eq_zero_iff_mem]
    exact ha i hi
  have htr : WittVector.truncate M (a' + b') = WittVector.truncate M b' := by
    rw [map_add, (RingHom.mem_ker).1 ha', zero_add]
  have := congrArg (TruncatedWittVector.coeff ⟨k, hk⟩) htr
  rwa [WittVector.coeff_truncate, WittVector.coeff_truncate] at this

private theorem apply_coeff_eq_zero_of_forall_apply_ghostComponent_eq_zero {S : Type*} [CommRing S]
    (κ : R →+* S) (hpS : (p : S) ∈ nonZeroDivisors S) (x : WittVector p R) (N : ℕ)
    (h : ∀ n, n < N → κ (WittVector.ghostComponent n x) = 0) :
    ∀ k, k < N → κ (x.coeff k) = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hg := h k hk
    rw [WittVector.ghostComponent_apply, aeval_wittPolynomial, map_sum,
      Finset.sum_range_succ] at hg
    have hzero : ∑ i ∈ Finset.range k, κ ((p : R) ^ i * x.coeff i ^ p ^ (k - i)) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [map_mul, map_pow, map_pow, ih i hi (by omega), zero_pow (pow_ne_zero _ hp.out.ne_zero), mul_zero]
    rw [hzero, zero_add, Nat.sub_self, pow_zero, pow_one, map_mul, map_pow, map_natCast] at hg
    have hreg : IsRegular ((p : S) ^ k) := (isRegular_iff_mem_nonZeroDivisors.2 hpS).pow k
    exact hreg.left (show (p : S) ^ k * κ (x.coeff k) = (p : S) ^ k * 0 by rw [hg, mul_zero])

end Witt

section Reduced

variable {𝓞 : Type u} [CommRing 𝓞] {d : ℕ}

private theorem isReduced_quotient_span_natCast (p : ℕ) [Fact p.Prime]
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)}) :
    IsReduced (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span {((p : MvPowerSeries (Fin d) 𝓞))}) := by
  classical
  let Φ : MvPowerSeries (Fin d) 𝓞 →+* MvPowerSeries (Fin d) (ZMod p) :=
    MvPowerSeries.map (algebraMap 𝓞 (ZMod p))
  have hsurjO : Function.Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _
  have hΦsurj : Function.Surjective Φ := by
    intro g
    refine ⟨fun m => (hsurjO (MvPowerSeries.coeff m g)).choose, ?_⟩
    ext m
    rw [MvPowerSeries.coeff_map]
    exact (hsurjO (MvPowerSeries.coeff m g)).choose_spec
  have hkerΦ : RingHom.ker Φ = Ideal.span {((p : MvPowerSeries (Fin d) 𝓞))} := by
    ext f
    rw [RingHom.mem_ker, Ideal.mem_span_singleton', MvPowerSeries.ext_iff]
    constructor
    · intro h
      have hc : ∀ m, ∃ a : 𝓞, a * (p : 𝓞) = MvPowerSeries.coeff m f := by
        intro m
        have hm := h m
        rw [MvPowerSeries.coeff_map, map_zero, ← RingHom.mem_ker, hker,
          Ideal.mem_span_singleton'] at hm
        exact hm
      refine ⟨fun m => (hc m).choose, ?_⟩
      ext m
      rw [show ((p : MvPowerSeries (Fin d) 𝓞)) = C (p : 𝓞) from
        (map_natCast (C (σ := Fin d) (R := 𝓞)) p).symm, MvPowerSeries.coeff_mul_C]
      exact (hc m).choose_spec
    · rintro ⟨g, rfl⟩ m
      rw [MvPowerSeries.coeff_map, map_zero,
        show ((p : MvPowerSeries (Fin d) 𝓞)) = C (p : 𝓞) from (map_natCast (C (σ := Fin d) (R := 𝓞)) p).symm,
        MvPowerSeries.coeff_mul_C, map_mul, map_natCast, ZMod.natCast_self, mul_zero]
  have e : (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span {((p : MvPowerSeries (Fin d) 𝓞))}) ≃+*
      MvPowerSeries (Fin d) (ZMod p) :=
    (Ideal.quotEquivOfEq hkerΦ.symm).trans (RingHom.quotientKerEquivOfSurjective hΦsurj)
  exact isReduced_of_injective e e.injective

end Reduced

section Trunc

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [hpp : Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
  {d : ℕ}

include hp in
omit hpp in

private theorem mem_span_pow_of_pow_mul_mem (a b : ℕ) (x : 𝓞)
    (h : (p : 𝓞) ^ a * x ∈ Ideal.span {(p : 𝓞) ^ (a + b)}) : x ∈ Ideal.span {(p : 𝓞) ^ b} := by
  rw [Ideal.mem_span_singleton'] at h ⊢
  obtain ⟨y, hy⟩ := h
  refine ⟨y, ?_⟩
  have hreg : IsRegular ((p : 𝓞) ^ a) := (isRegular_iff_mem_nonZeroDivisors.2 hp).pow a
  apply hreg.left
  show (p : 𝓞) ^ a * (y * (p : 𝓞) ^ b) = (p : 𝓞) ^ a * x
  rw [← hy, pow_add]; ring

variable (φ : MvPowerSeries (Fin d) 𝓞)
  (hLI : ∀ (m : Fin d →₀ ℕ) (t : Fin d), 1 ≤ m t →
    ((m t : ℕ) : 𝓞) * MvPowerSeries.coeff m φ ∈ Ideal.span {(p : 𝓞) ^ (m.degree - 1)})

include hp hLI in

private theorem pow_dvd_coeff_of_degree_le (N : ℕ) (hN : 1 ≤ N) (m : Fin d →₀ ℕ) (hm0 : m ≠ 0)
    (hm : m.degree ≤ p ^ (N - 1)) : (p : 𝓞) ^ (m.degree - N) ∣ MvPowerSeries.coeff m φ := by
  obtain ⟨t, ht⟩ := Finsupp.ne_iff.1 hm0
  simp only [Finsupp.coe_zero, Pi.zero_apply] at ht
  obtain ⟨v, q, hq, hvq⟩ := Nat.exists_eq_pow_mul_and_not_dvd ht p hpp.out.one_lt.ne'
  have hq0 : q ≠ 0 := by rintro rfl; exact ht (by rw [hvq, mul_zero])

  have hv : v ≤ N - 1 := by
    have h1 : p ^ v ≤ m t := by
      rw [hvq]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hq0)
    have h2 : m t ≤ m.degree := Finsupp.le_degree t m
    exact (Nat.pow_le_pow_iff_right hpp.out.one_lt).1 (h1.trans (h2.trans hm))
  have hmem := hLI m t (Nat.one_le_iff_ne_zero.2 ht)
  rw [Ideal.mem_span_singleton] at hmem

  have h1 : (p : 𝓞) ^ (m.degree - 1 - v) ∣ (q : 𝓞) * MvPowerSeries.coeff m φ := by
    have hdeg : v ≤ m.degree - 1 := by
      have e1 : m t ≤ m.degree := Finsupp.le_degree t m
      have e2 : p ^ v ≤ m t := by rw [hvq]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hq0)
      have e3 : v < p ^ v := Nat.lt_pow_self hpp.out.one_lt
      have e4 : v + 1 ≤ m.degree := by
        calc v + 1 ≤ p ^ v := e3
          _ ≤ m t := e2
          _ ≤ m.degree := e1
      omega
    rw [hvq, Nat.cast_mul, Nat.cast_pow, mul_assoc, show m.degree - 1 = v + (m.degree - 1 - v) by omega,
      pow_add] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨c, ?_⟩
    have hreg : IsRegular ((p : 𝓞) ^ v) := (isRegular_iff_mem_nonZeroDivisors.2 hp).pow v
    apply hreg.left
    show (p : 𝓞) ^ v * ((q : 𝓞) * MvPowerSeries.coeff m φ) = (p : 𝓞) ^ v * ((p : 𝓞) ^ (m.degree - 1 - v) * c)
    rw [hc]; ring
  have hcop : IsCoprime ((p : 𝓞) ^ (m.degree - 1 - v)) (q : 𝓞) := by
    have hnat : Nat.Coprime (p ^ (m.degree - 1 - v)) q :=
      (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hpp.out).2 hq))
    have hint := (Nat.isCoprime_iff_coprime.2 hnat).map (Int.castRingHom 𝓞)
    simpa using hint
  have h2 : (p : 𝓞) ^ (m.degree - 1 - v) ∣ MvPowerSeries.coeff m φ :=
    hcop.dvd_of_dvd_mul_left h1
  exact (pow_dvd_pow _ (by omega)).trans h2

variable (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (cN cM : (Fin d →₀ ℕ) → 𝓞)
  (hcN : ∀ m : Fin d →₀ ℕ,
    (m.degree ≤ N → cN m = (p : 𝓞) ^ (N - m.degree) * MvPowerSeries.coeff m φ) ∧
    (N < m.degree → cN m * (p : 𝓞) ^ (m.degree - N) = MvPowerSeries.coeff m φ ∨
      (cN m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ MvPowerSeries.coeff m φ)))
  (hcM : ∀ m : Fin d →₀ ℕ,
    (m.degree ≤ M → cM m = (p : 𝓞) ^ (M - m.degree) * MvPowerSeries.coeff m φ) ∧
    (M < m.degree → cM m * (p : 𝓞) ^ (m.degree - M) = MvPowerSeries.coeff m φ ∨
      (cM m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - M) ∣ MvPowerSeries.coeff m φ)))

include hp hLI hN hNM hcN hcM in

private theorem sub_eq_zero_of_degree_le (m : Fin d →₀ ℕ) (hm : m.degree ≤ p ^ (N - 1)) :
    cM m - (p : 𝓞) ^ (M - N) * cN m = 0 := by
  rcases le_or_gt m.degree N with h1 | h1
  · rw [(hcN m).1 h1, (hcM m).1 (h1.trans hNM), ← mul_assoc, ← pow_add,
      show M - N + (N - m.degree) = M - m.degree by omega, sub_self]
  have hm0 : m ≠ 0 := by rintro rfl; simp at h1
  have hdvdN := pow_dvd_coeff_of_degree_le p hp φ hLI N hN m hm0 hm
  have hN : cN m * (p : 𝓞) ^ (m.degree - N) = MvPowerSeries.coeff m φ := by
    rcases (hcN m).2 h1 with h | ⟨-, h⟩
    · exact h
    · exact absurd hdvdN h
  rcases le_or_gt m.degree M with h2 | h2
  · rw [(hcM m).1 h2, ← hN, sub_eq_zero, mul_comm (cN m), ← mul_assoc, ← pow_add,
      show M - m.degree + (m.degree - N) = M - N by omega]
  · have hdvdM : (p : 𝓞) ^ (m.degree - M) ∣ MvPowerSeries.coeff m φ :=
      (pow_dvd_pow _ (by omega)).trans hdvdN
    have hM : cM m * (p : 𝓞) ^ (m.degree - M) = MvPowerSeries.coeff m φ := by
      rcases (hcM m).2 h2 with h | ⟨-, h⟩
      · exact h
      · exact absurd hdvdM h
    have hreg : IsRegular ((p : 𝓞) ^ (m.degree - M)) := (isRegular_iff_mem_nonZeroDivisors.2 hp).pow _
    apply hreg.right
    show (cM m - (p : 𝓞) ^ (M - N) * cN m) * (p : 𝓞) ^ (m.degree - M) = 0 * (p : 𝓞) ^ (m.degree - M)
    rw [zero_mul, sub_mul, hM, mul_assoc, mul_comm (cN m), ← mul_assoc, ← pow_add,
      show M - N + (m.degree - M) = m.degree - N by omega, mul_comm ((p : 𝓞) ^ (m.degree - N)) (cN m), hN,
      sub_self]

include hp hLI hN hNM hcN hcM in
omit hpp in

private theorem natCast_mul_sub_mem (μ : Fin d →₀ ℕ) (t : Fin d) :
    ((μ t : ℕ) : 𝓞) * (cM μ - (p : 𝓞) ^ (M - N) * cN μ) ∈ Ideal.span {(p : 𝓞) ^ (M - 1)} := by
  rcases Nat.eq_zero_or_pos (μ t) with ht | ht
  · rw [ht, Nat.cast_zero, zero_mul]; exact Ideal.zero_mem _
  have hli := hLI μ t ht
  rcases le_or_gt μ.degree N with h1 | h1
  ·
    rw [(hcN μ).1 h1, (hcM μ).1 (h1.trans hNM), ← mul_assoc ((p : 𝓞) ^ (M - N)), ← pow_add,
      show M - N + (N - μ.degree) = M - μ.degree by omega, sub_self, mul_zero]
    exact Ideal.zero_mem _
  rcases le_or_gt μ.degree M with h2 | h2
  ·
    rw [(hcM μ).1 h2]
    rcases (hcN μ).2 h1 with h | ⟨h, -⟩
    · rw [← h, mul_comm (cN μ), ← mul_assoc, ← pow_add,
        show M - μ.degree + (μ.degree - N) = M - N by omega, sub_self, mul_zero]
      exact Ideal.zero_mem _
    · rw [h, mul_zero, sub_zero, mul_left_comm]
      have : (p : 𝓞) ^ (M - μ.degree) * (((μ t : ℕ) : 𝓞) * MvPowerSeries.coeff μ φ) ∈
          Ideal.span {(p : 𝓞) ^ (M - μ.degree)} * Ideal.span {(p : 𝓞) ^ (μ.degree - 1)} :=
        Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hli
      rw [Ideal.span_singleton_mul_span_singleton, ← pow_add] at this
      exact Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (by omega)) this
  ·
    apply mem_span_pow_of_pow_mul_mem p hp (μ.degree - M) (M - 1)
    have key : (p : 𝓞) ^ (μ.degree - M) * (((μ t : ℕ) : 𝓞) * (cM μ - (p : 𝓞) ^ (M - N) * cN μ)) =
        ((μ t : ℕ) : 𝓞) * (cM μ * (p : 𝓞) ^ (μ.degree - M) - cN μ * (p : 𝓞) ^ (μ.degree - N)) := by
      rw [show μ.degree - N = (M - N) + (μ.degree - M) by omega, pow_add]; ring
    rw [key, show μ.degree - M + (M - 1) = μ.degree - 1 by omega]
    have hM' : cM μ * (p : 𝓞) ^ (μ.degree - M) = MvPowerSeries.coeff μ φ ∨
        cM μ * (p : 𝓞) ^ (μ.degree - M) = 0 := by
      rcases (hcM μ).2 h2 with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr (by rw [h, zero_mul])
    have hN' : cN μ * (p : 𝓞) ^ (μ.degree - N) = MvPowerSeries.coeff μ φ ∨
        cN μ * (p : 𝓞) ^ (μ.degree - N) = 0 := by
      rcases (hcN μ).2 h1 with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr (by rw [h, zero_mul])
    rcases hM' with hM' | hM' <;> rcases hN' with hN' | hN' <;> rw [hM', hN']
    · rw [sub_self, mul_zero]; exact Ideal.zero_mem _
    · rw [sub_zero]; exact hli
    · rw [zero_sub, mul_neg]; exact (Ideal.neg_mem_iff _).2 hli
    · rw [sub_self, mul_zero]; exact Ideal.zero_mem _

end Trunc

end MvFormalGroup.FactApC12

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (i : Fin d) (E w : ℕ) :
    ∃ N₁ : ℕ, ∀ N M : ℕ, N₁ ≤ N → N ≤ M →
      ∀ (cN cM : (Fin d →₀ ℕ) → 𝓞),
      (∀ m : Fin d →₀ ℕ,
        (m.degree ≤ N → cN m = (p : 𝓞) ^ (N - m.degree) * (φ i).coeff m) ∧
        (N < m.degree → cN m * (p : 𝓞) ^ (m.degree - N) = (φ i).coeff m ∨
          (cN m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ (φ i).coeff m))) →
      (∀ m : Fin d →₀ ℕ,
        (m.degree ≤ M → cM m = (p : 𝓞) ^ (M - m.degree) * (φ i).coeff m) ∧
        (M < m.degree → cM m * (p : 𝓞) ^ (m.degree - M) = (φ i).coeff m ∨
          (cM m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - M) ∣ (φ i).coeff m))) →
      ∀ ℓN ℓM : WittVector p (MvPowerSeries (Fin d) 𝓞),
        (∀ n : ℕ, n < N → ∀ m' : Fin d →₀ ℕ,
          (WittVector.ghostComponent n ℓN).coeff m' = cN (p ^ (N - 1 - n) • m')) →
        (∀ n : ℕ, n < M → ∀ m' : Fin d →₀ ℕ,
          (WittVector.ghostComponent n ℓM).coeff m' = cM (p ^ (M - 1 - n) • m')) →
        ∀ j : ℕ, N - w ≤ j → j < N →
          ℓM.coeff (j + (M - N)) - ℓN.coeff j ∈
            Ideal.span {(p : MvPowerSeries (Fin d) 𝓞)} ⊔
              (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞))) ^ E := by
  classical
  have hpp : p.Prime := Fact.out
  refine ⟨E + w + 1, ?_⟩
  intro N M hN1 hNM cN cM hcN hcM ℓN ℓM hℓN hℓM j hjw hjN
  have hN : 1 ≤ N := by omega
  set s := M - N with hs
  have hpS := MvFormalGroup.FactApC12.natCast_mem_nonZeroDivisors (d := d) p hp

  have hLI : ∀ (m : Fin d →₀ ℕ) (t : Fin d), 1 ≤ m t →
      ((m t : ℕ) : 𝓞) * MvPowerSeries.coeff m (φ i) ∈ Ideal.span {(p : 𝓞) ^ (m.degree - 1)} := by
    intro m t ht
    have key := MvFormalGroup.natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add
      p hp F Fp hFp hFp0 φ hφ0 hφ1 hφF i t (m - Finsupp.single t 1)
    have hm : m - Finsupp.single t 1 + Finsupp.single t 1 = m :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.2 ht)
    have hmt : (m - Finsupp.single t 1 : Fin d →₀ ℕ) t + 1 = m t := by
      rw [Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
    have hdeg : (m - Finsupp.single t 1).degree = m.degree - 1 := by
      have h := congrArg Finsupp.degree hm
      rw [map_add, Finsupp.degree_single] at h
      omega
    rw [hm, hmt, hdeg] at key
    exact key

  let P : MvPowerSeries (Fin d) 𝓞 := fun m => cM m - (p : 𝓞) ^ s * cN m
  have hPcoeff : ∀ m, MvPowerSeries.coeff m P = cM m - (p : 𝓞) ^ s * cN m := fun _ => rfl
  have hfrob : ∀ c : 𝓞, c ^ p - c ∈ Ideal.span {(p : 𝓞)} := by
    intro c
    rw [← hker, RingHom.mem_ker, map_sub, map_pow, ZMod.pow_card, sub_self]
  have hPH : ∀ (μ : Fin d →₀ ℕ) (t : Fin d), ((μ t : ℕ) : 𝓞) * MvPowerSeries.coeff μ P ∈
      Ideal.span {(p : 𝓞) ^ (M - 1)} := by
    intro μ t
    rw [hPcoeff]
    exact MvFormalGroup.FactApC12.natCast_mul_sub_mem p hp (φ i) hLI N M hN hNM cN cM hcN hcM μ t
  obtain ⟨u, hu⟩ :=
    MvPowerSeries.exists_wittVector_forall_coeff_ghostComponent_eq_of_forall_natCast_mul_coeff_mem
      p hp hfrob M P hPH
  have hPL : ∀ μ : Fin d →₀ ℕ, MvPowerSeries.coeff μ P ≠ 0 → p ^ (N - 1) + 1 ≤ μ.degree := by
    intro μ hμ
    by_contra hlt
    refine hμ ?_
    rw [hPcoeff]
    exact MvFormalGroup.FactApC12.sub_eq_zero_of_degree_le p hp (φ i) hLI N M hN hNM cN cM hcN hcM μ
      (by omega)

  have hudeep : ∀ i' : ℕ, i' < N → u.coeff (s + i') ∈
      Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞)) ^ (p ^ i' + 1) := by
    intro i' hi'
    refine MvFormalGroup.FactApC12.mem_pow_span_X_of_forall_le_degree _ _ fun μ' hμ' => ?_
    have h := MvPowerSeries.le_mul_degree_of_coeff_coeff_ne_zero_of_forall_coeff_ghostComponent_eq
      p hp M (p ^ (N - 1) + 1) P hPL u hu (s + i') (by omega) μ' hμ'
    rw [show M - 1 - (s + i') = N - 1 - i' by omega] at h
    by_contra hle
    have hle' : μ'.degree ≤ p ^ i' := by omega
    have h2 : p ^ (N - 1 - i') * μ'.degree ≤ p ^ (N - 1 - i') * p ^ i' := Nat.mul_le_mul_left _ hle'
    rw [← pow_add, show N - 1 - i' + i' = N - 1 by omega] at h2
    exact Nat.not_succ_le_self _ (h.trans h2)

  let v : WittVector p (MvPowerSeries (Fin d) 𝓞) := WittVector.mk p fun i' => u.coeff (s + i')
  let ulo : WittVector p (MvPowerSeries (Fin d) 𝓞) :=
    WittVector.mk p fun i' => if i' < s then u.coeff i' else 0
  have hulo : ∀ i', s ≤ i' → ulo.coeff i' = 0 := fun i' hi' => by
    show (if i' < s then u.coeff i' else 0) = 0
    rw [if_neg (by omega)]
  have hdecomp : u = ulo + (WittVector.verschiebung)^[s] v := by
    ext n : 1
    rw [WittVector.coeff_add_of_disjoint]
    · by_cases hn : n < s
      · rw [MvFormalGroup.FactApC12.iterate_verschiebung_coeff_lt v s n hn, add_zero]
        show u.coeff n = if n < s then u.coeff n else 0
        rw [if_pos hn]
      · rw [hulo n (by omega), zero_add, show n = (n - s) + s by omega,
          WittVector.iterate_verschiebung_coeff]
        show u.coeff (n - s + s) = u.coeff (s + (n - s))
        rw [add_comm]
    · intro n
      by_cases hn : n < s
      · exact Or.inr (MvFormalGroup.FactApC12.iterate_verschiebung_coeff_lt v s n hn)
      · exact Or.inl (hulo n (by omega))

  set y := (WittVector.verschiebung)^[s] ℓN with hy
  have e1 : ∀ μ', MvPowerSeries.coeff μ' (WittVector.ghostComponent (M - 1) ℓM) = cM μ' := fun μ' => by
    rw [hℓM (M - 1) (by omega), Nat.sub_self, pow_zero, one_smul]
  have e2 : ∀ μ', MvPowerSeries.coeff μ' (WittVector.ghostComponent (M - 1) u) =
      cM μ' - (p : 𝓞) ^ s * cN μ' := fun μ' => by
    rw [hu (M - 1) (by omega), Nat.sub_self, pow_zero, one_smul]
    exact hPcoeff μ'
  have e3 : ∀ μ', MvPowerSeries.coeff μ' (WittVector.ghostComponent (M - 1) y) =
      (p : 𝓞) ^ s * cN μ' := by
    have hgy : WittVector.ghostComponent (M - 1) y =
        ((p : MvPowerSeries (Fin d) 𝓞)) ^ s * WittVector.ghostComponent (N - 1) ℓN := by
      rw [hy, show M - 1 = (N - 1) + s by omega]
      exact MvFormalGroup.FactApC12.ghostComponent_iterate_verschiebung ℓN s (N - 1)
    intro μ'
    rw [hgy, show ((p : MvPowerSeries (Fin d) 𝓞)) ^ s = C ((p : 𝓞) ^ s) by rw [map_pow, map_natCast],
      MvPowerSeries.coeff_C_mul, hℓN (N - 1) (by omega), Nat.sub_self, pow_zero, one_smul]
  have hz : WittVector.ghostComponent (M - 1) (ℓM - (y + u)) ∈
      Ideal.span {((p : MvPowerSeries (Fin d) 𝓞)) ^ M} := by
    have h0 : WittVector.ghostComponent (M - 1) (ℓM - (y + u)) = 0 := by
      ext μ'
      simp only [map_sub, map_add, map_zero, e1, e2, e3]
      ring
    rw [h0]
    exact Ideal.zero_mem _

  have hred := MvFormalGroup.FactApC12.isReduced_quotient_span_natCast (d := d) p hker
  have hzc := WittVector.coeff_mem_span_of_ghostComponent_mem_span_pow_of_isReduced p hpS hred
    (ℓM - (y + u)) M hz

  have hA : ℓM.coeff (j + s) - (y + u).coeff (j + s) ∈ Ideal.span {((p : MvPowerSeries (Fin d) 𝓞))} := by
    have h := MvFormalGroup.FactApC12.add_coeff_sub_coeff_mem (Ideal.span {((p : MvPowerSeries (Fin d) 𝓞))})
      (ℓM - (y + u)) (y + u) M hzc (j + s) (by omega)
    rwa [sub_add_cancel] at h

  have hB : (y + u).coeff (j + s) = (ℓN + v).coeff j := by
    rw [hdecomp, hy, ← add_assoc, add_comm (((WittVector.verschiebung)^[s]) ℓN) ulo, add_assoc,
      ← MvFormalGroup.FactApC12.iterate_verschiebung_add]
    exact MvFormalGroup.FactApC12.add_iterate_verschiebung_coeff ulo (ℓN + v) s hulo j

  have hC : (ℓN + v).coeff j = (WittVector.init N ℓN + WittVector.init N v).coeff j :=
    MvFormalGroup.FactApC12.add_coeff_eq_init_add_init_coeff ℓN v N j hjN

  have hκ : ∀ n, n < N → MvPowerSeries.constantCoeff (WittVector.ghostComponent n ℓN) = 0 := by
    intro n hn
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hℓN n hn 0, smul_zero, (hcN 0).1 (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ0 i, mul_zero]
  have hx : ∀ i', (WittVector.init N ℓN).coeff i' ∈
      Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞)) := by
    intro i'
    rw [MvFormalGroup.FactApC12.coeff_init]
    split_ifs with hi'
    · exact MvFormalGroup.FactApC12.mem_span_X_of_constantCoeff_eq_zero _
        (MvFormalGroup.FactApC12.apply_coeff_eq_zero_of_forall_apply_ghostComponent_eq_zero
          MvPowerSeries.constantCoeff hp ℓN N hκ i' hi')
    · exact Ideal.zero_mem _
  have hyv : ∀ i', (WittVector.init N v).coeff i' ∈
      Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞)) ^ (p ^ i' + 1) := by
    intro i'
    rw [MvFormalGroup.FactApC12.coeff_init]
    split_ifs with hi'
    · exact hudeep i' hi'
    · exact Ideal.zero_mem _
  have hD := WittVector.add_coeff_sub_coeff_mem_pow_of_forall_coeff_mem_pow p
    (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞))) 1
    (WittVector.init N ℓN) (WittVector.init N v) hx hyv j
  have hE' : (WittVector.init N ℓN).coeff j = ℓN.coeff j := by
    rw [MvFormalGroup.FactApC12.coeff_init, if_pos hjN]
  have hIJ : Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞)) ^ ((p - 1) * j + 1 + 1) ≤
      Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞)) ^ E := by
    apply Ideal.pow_le_pow_right
    have h1 : 1 ≤ p - 1 := by have := hpp.two_le; omega
    have h2 : j ≤ (p - 1) * j := Nat.le_mul_of_pos_left j h1
    omega

  have hfin : ℓM.coeff (j + s) - ℓN.coeff j =
      (ℓM.coeff (j + s) - (y + u).coeff (j + s)) +
        ((WittVector.init N ℓN + WittVector.init N v).coeff j - (WittVector.init N ℓN).coeff j) := by
    rw [hB, hC, hE']
    ring
  rw [hfin]
  exact Submodule.add_mem_sup hA (hIJ hD)

end S_MvFormalGroup_coeff_sub_coeff_mem_of_forall_coeff_ghostComponent_eq_logCovector_of_le
end P2MW
export P2MW.S_MvFormalGroup_coeff_sub_coeff_mem_of_forall_coeff_ghostComponent_eq_logCovector_of_le (solution)
