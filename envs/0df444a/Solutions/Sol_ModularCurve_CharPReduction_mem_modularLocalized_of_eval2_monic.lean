-- Prove2me | solution 1 for ModularCurve.CharPReduction.mem_modularLocalized_of_eval2_monic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/80d01fbe-7fd3-51fc-8058-4303259edb8d

import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_X0
import Mathlib.FieldTheory.Relrank
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.RingTheory.AlgebraTower
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPReduction_mem_modularLocalized_of_eval2_monic

p2m_open "ModularCurve P2MW.S_ModularCurve_CharPReduction_mem_modularLocalized_of_eval2_monic.ModularCurve ModularCurve.CharPReduction"

set_option autoImplicit false

open IsLocalRing

namespace SD2

variable {F : Type*} [Field F]

section LocSubring

variable (R : Subring F) (𝔭 : Ideal R)

private theorem ne_zero_of_notMem_prime {s : R} (hs : s ∉ 𝔭) : (s : F) ≠ 0 := by
  intro h
  apply hs
  have : s = 0 := Subtype.ext h
  rw [this]
  exact Ideal.zero_mem _

variable [𝔭.IsPrime]

private theorem one_notMem_prime : (1 : R) ∉ 𝔭 := fun h =>
  Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).mpr h)

private theorem mul_notMem_prime {s t : R} (hs : s ∉ 𝔭) (ht : t ∉ 𝔭) : s * t ∉ 𝔭 := fun h =>
  (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs ht

private def locSubring : Subring F where
  carrier := {x | ∃ r s : R, s ∉ 𝔭 ∧ x * s = r}
  mul_mem' := by
    rintro x y ⟨r, s, hs, hx⟩ ⟨r', s', hs', hy⟩
    refine ⟨r * r', s * s', mul_notMem_prime R 𝔭 hs hs', ?_⟩
    rw [Subring.coe_mul, Subring.coe_mul, ← hx, ← hy]; ring
  one_mem' := ⟨1, 1, one_notMem_prime R 𝔭, by simp⟩
  add_mem' := by
    rintro x y ⟨r, s, hs, hx⟩ ⟨r', s', hs', hy⟩
    refine ⟨r * s' + r' * s, s * s', mul_notMem_prime R 𝔭 hs hs', ?_⟩
    rw [Subring.coe_mul, Subring.coe_add, Subring.coe_mul, Subring.coe_mul, ← hx, ← hy]; ring
  zero_mem' := ⟨0, 1, one_notMem_prime R 𝔭, by simp⟩
  neg_mem' := by
    rintro x ⟨r, s, hs, hx⟩
    exact ⟨-r, s, hs, by rw [Subring.coe_neg, ← hx]; ring⟩

private theorem mem_locSubring_iff {x : F} :
    x ∈ locSubring R 𝔭 ↔ ∃ r s : R, s ∉ 𝔭 ∧ x * s = r := Iff.rfl

private theorem le_locSubring : R ≤ locSubring R 𝔭 := fun x hx =>
  ⟨⟨x, hx⟩, 1, one_notMem_prime R 𝔭, by simp⟩

private theorem inv_mem_locSubring {x : F} {r s : R} (hr : r ∉ 𝔭) (hx : x * s = r) :
    x⁻¹ ∈ locSubring R 𝔭 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact ne_zero_of_notMem_prime R 𝔭 hr (by rw [← hx, zero_mul])
  exact ⟨s, r, hr, by rw [← hx, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]⟩

private theorem notMem_of_inv_mem_locSubring {x : F} (hx0 : x ≠ 0) {r s : R} (hs : s ∉ 𝔭)
    (hx : x * s = r) (hinv : x⁻¹ ∈ locSubring R 𝔭) : r ∉ 𝔭 := by
  obtain ⟨r', s', hs', hx'⟩ := hinv
  intro hr
  have hss : s * s' = r * r' := by
    apply Subtype.ext
    change (s : F) * s' = r * r'
    rw [← hx, ← hx']
    calc (s : F) * s' = (x * x⁻¹) * s * s' := by rw [mul_inv_cancel₀ hx0, one_mul]
      _ = x * s * (x⁻¹ * s') := by ring
  exact mul_notMem_prime R 𝔭 hs hs' (hss ▸ Ideal.mul_mem_right _ _ hr)

private theorem inv_mem_locSubring_iff {x : F} (hx0 : x ≠ 0) {r s : R} (hs : s ∉ 𝔭)
    (hx : x * s = r) : x⁻¹ ∈ locSubring R 𝔭 ↔ r ∉ 𝔭 :=
  ⟨notMem_of_inv_mem_locSubring R 𝔭 hx0 hs hx, fun hr => inv_mem_locSubring R 𝔭 hr hx⟩

end LocSubring

section Scaling

variable {A : Type*} [CommRing A] [IsDomain A] [ValuationRing A]

private theorem exists_dvd_forall {ι : Type*} (c : ι → A) (s : Finset ι) (hs : s.Nonempty) :
    ∃ i ∈ s, ∀ j ∈ s, c i ∣ c j := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · refine ⟨a, Finset.mem_insert_self _ _, fun j hj => ?_⟩
      rw [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact dvd_rfl
      · exact absurd hj (Finset.notMem_empty _)
    · obtain ⟨i, hi, hmin⟩ := ih hne
      rcases ValuationRing.dvd_total (c a) (c i) with h | h
      · refine ⟨a, Finset.mem_insert_self _ _, fun j hj => ?_⟩
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact dvd_rfl
        · exact h.trans (hmin j hj)
      · refine ⟨i, Finset.mem_insert_of_mem hi, fun j hj => ?_⟩
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact h
        · exact hmin j hj

variable {R : Type*} [CommRing R] (𝔭 : Ideal R) (φ : A →+* R) {ι : Type*} (b : ι → R)

private def IndepModPrime : Prop :=
  ∀ (s : Finset ι) (c : ι → A), (∑ i ∈ s, φ (c i) * b i) ∈ 𝔭 → ∀ i ∈ s, c i ∈ maximalIdeal A

private theorem exists_eq_mul_notMem
    (hspan : ∀ r : R, ∃ (s : Finset ι) (c : ι → A), r = ∑ i ∈ s, φ (c i) * b i)
    (hind : IndepModPrime 𝔭 φ b) {r : R} (hr : r ≠ 0) :
    ∃ (c : A) (r' : R), r' ∉ 𝔭 ∧ r = φ c * r' := by
  classical
  obtain ⟨s, c, rfl⟩ := hspan r

  set s' := s.filter (fun i => c i ≠ 0) with hs'
  have hsum : ∑ i ∈ s, φ (c i) * b i = ∑ i ∈ s', φ (c i) * b i := by
    rw [hs', Finset.sum_filter_of_ne]
    intro i _ hne hci
    apply hne
    rw [hci, map_zero, zero_mul]
  have hne : s'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    apply hr
    rw [hsum, he, Finset.sum_empty]
  obtain ⟨i₀, hi₀, hmin⟩ := exists_dvd_forall c s' hne
  have hci₀ : c i₀ ≠ 0 := (Finset.mem_filter.mp hi₀).2
  choose! d hd using hmin
  refine ⟨c i₀, ∑ j ∈ s', φ (d j) * b j, ?_, ?_⟩
  · intro hmem
    have h1 : d i₀ ∈ maximalIdeal A := hind s' d hmem i₀ hi₀
    have hd1 : d i₀ = 1 := by
      apply mul_left_cancel₀ hci₀
      rw [mul_one]
      exact (hd i₀ hi₀).symm
    rw [hd1] at h1
    exact (maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  · rw [hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hd j hj, map_mul, mul_assoc]

end Scaling

section Valuation

variable {A : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
variable (R : Subring F) (𝔭 : Ideal R) [𝔭.IsPrime] (φ : A →+* R) {ι : Type*} (b : ι → R)
variable (hspan : ∀ r : R, ∃ (s : Finset ι) (c : ι → A), r = ∑ i ∈ s, φ (c i) * b i)
variable (hind : IndepModPrime 𝔭 φ b)

include hspan hind

private theorem mem_or_inv_mem_of_fraction {x : F} {r s : R} (hs : (s : F) ≠ 0)
    (hx : x * s = r) : x ∈ locSubring R 𝔭 ∨ x⁻¹ ∈ locSubring R 𝔭 := by
  by_cases hr0 : r = 0
  · left
    have hx0 : x = 0 := by
      rw [hr0, Subring.coe_zero] at hx
      exact (mul_eq_zero.mp hx).resolve_right hs
    rw [hx0]
    exact Subring.zero_mem _
  have hs0 : s ≠ 0 := fun h => hs (by rw [h]; rfl)
  obtain ⟨c, r', hr', hr⟩ := exists_eq_mul_notMem 𝔭 φ b hspan hind hr0
  obtain ⟨d, s', hs', hs''⟩ := exists_eq_mul_notMem 𝔭 φ b hspan hind hs0
  have hxF : x * ((φ d : R) : F) * s' = (φ c : R) * r' := by
    rw [mul_assoc, ← Subring.coe_mul, ← hs'', hx, hr, Subring.coe_mul]
  rcases ValuationRing.dvd_total c d with ⟨e, rfl⟩ | ⟨e, rfl⟩
  ·
    right
    have hc0 : ((φ c : R) : F) ≠ 0 := by
      intro h0
      apply hr0
      apply Subtype.ext
      change (r : F) = 0
      rw [hr, Subring.coe_mul, h0, zero_mul]
    have hx' : x * ((φ e : R) * s' : R) = r' := by
      apply mul_left_cancel₀ hc0
      rw [← hxF, map_mul, Subring.coe_mul, Subring.coe_mul]
      ring
    exact inv_mem_locSubring R 𝔭 hr' hx'
  ·
    left
    have hd0 : ((φ d : R) : F) ≠ 0 := by
      intro h0
      apply hs
      rw [hs'', Subring.coe_mul, h0, zero_mul]
    have hx' : x * s' = ((φ e : R) * r' : R) := by
      apply mul_left_cancel₀ hd0
      rw [← mul_assoc, mul_comm _ x, hxF, map_mul, Subring.coe_mul, Subring.coe_mul]
      ring
    exact ⟨_, s', hs', hx'⟩

private def locValuationSubring (hfrac : ∀ x : F, ∃ r s : R, (s : F) ≠ 0 ∧ x * s = r) :
    ValuationSubring F :=
  { locSubring R 𝔭 with
    mem_or_inv_mem' := fun x => by
      obtain ⟨r, s, hs, hx⟩ := hfrac x
      exact mem_or_inv_mem_of_fraction R 𝔭 φ b hspan hind hs hx }

private theorem mem_locValuationSubring_iff (hfrac : ∀ x : F, ∃ r s : R, (s : F) ≠ 0 ∧ x * s = r)
    {x : F} : x ∈ locValuationSubring R 𝔭 φ b hspan hind hfrac ↔
      ∃ r s : R, s ∉ 𝔭 ∧ x * s = r := Iff.rfl

private theorem exists_eq_mul_of_numerator_mem {x : F} {r s : R} (hs : s ∉ 𝔭) (hx : x * s = r)
    (hr : r ∈ 𝔭) :
    ∃ m ∈ maximalIdeal A, ∃ y ∈ locSubring R 𝔭, x = ((φ m : R) : F) * y := by
  by_cases hr0 : r = 0
  · refine ⟨0, Ideal.zero_mem _, 0, Subring.zero_mem _, ?_⟩
    have : x = 0 := by
      rw [hr0, Subring.coe_zero] at hx
      exact (mul_eq_zero.mp hx).resolve_right (ne_zero_of_notMem_prime R 𝔭 hs)
    rw [this, mul_zero]
  obtain ⟨c, r', hr', hr⟩ := exists_eq_mul_notMem 𝔭 φ b hspan hind hr0
  have hc : c ∈ maximalIdeal A := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hr'
    have : r' = φ (hu.unit⁻¹ : Aˣ) * r := by
      rw [hr, ← mul_assoc, ← map_mul, hu.val_inv_mul, map_one, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ ‹r ∈ 𝔭›
  refine ⟨c, hc, r' / s, ⟨r', s, hs, ?_⟩, ?_⟩
  · rw [div_mul_cancel₀ _ (ne_zero_of_notMem_prime R 𝔭 hs)]
  · rw [mul_div_assoc', ← Subring.coe_mul, ← hr, ← hx,
      mul_div_cancel_right₀ _ (ne_zero_of_notMem_prime R 𝔭 hs)]

omit hspan hind in

private theorem dvd_of_fraction_mem (hφ : Function.Injective φ)
    (h𝔪 : ∀ m ∈ maximalIdeal A, φ m ∈ 𝔭) {a d : A} {x : F}
    (hx : x * (φ d : R) = (φ a : R)) (hd : d ≠ 0) (hmem : x ∈ locSubring R 𝔭) : d ∣ a := by
  by_cases ha : a = 0
  · rw [ha]; exact dvd_zero _
  rcases ValuationRing.dvd_total d a with h | ⟨e, rfl⟩
  · exact h

  by_cases he : IsUnit e
  · exact ⟨(he.unit⁻¹ : Aˣ), by rw [mul_assoc, he.mul_val_inv, mul_one]⟩
  exfalso
  obtain ⟨r, s, hs, hxs⟩ := hmem
  have hφa : ((φ a : R) : F) ≠ 0 := by
    intro h0
    apply ha
    apply hφ
    rw [map_zero]
    exact Subtype.ext h0
  have hφd : ((φ (a * e) : R) : F) ≠ 0 := by
    intro h0
    apply hd
    apply hφ
    rw [map_zero]
    exact Subtype.ext h0

  have hkey : s = φ e * r := by
    apply Subtype.ext
    change (s : F) = ((φ e * r : R) : F)
    apply mul_left_cancel₀ hφa
    calc ((φ a : R) : F) * s = x * ((φ (a * e) : R) : F) * s := by rw [hx]
      _ = (x * s) * ((φ (a * e) : R) : F) := by ring
      _ = (r : F) * (((φ a : R) * (φ e : R) : R) : F) := by rw [hxs, map_mul]
      _ = ((φ a : R) : F) * ((φ e * r : R) : F) := by rw [Subring.coe_mul, Subring.coe_mul]; ring
  apply hs
  rw [hkey]
  exact Ideal.mul_mem_right _ _ (h𝔪 e (by rwa [mem_maximalIdeal, mem_nonunits_iff]))

end Valuation

section Local

variable (R : Subring F) (𝔭 : Ideal R) [𝔭.IsPrime]

private theorem isUnit_locSubring_iff {x : F} (hx : x ∈ locSubring R 𝔭) {r s : R} (hs : s ∉ 𝔭)
    (hxs : x * s = r) : IsUnit (⟨x, hx⟩ : locSubring R 𝔭) ↔ r ∉ 𝔭 := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 : x * (((u⁻¹ : (locSubring R 𝔭)ˣ) : locSubring R 𝔭) : F) = 1 := by
      have := congrArg (fun y : locSubring R 𝔭 => (y : F)) u.mul_inv
      simpa [hu] using this
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_mul] at h1
      exact zero_ne_one h1
    have hinv : x⁻¹ ∈ locSubring R 𝔭 := by
      rw [inv_eq_of_mul_eq_one_right h1]
      exact SetLike.coe_mem _
    exact notMem_of_inv_mem_locSubring R 𝔭 hx0 hs hxs hinv
  · intro hr
    have hinv := inv_mem_locSubring R 𝔭 hr hxs
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact ne_zero_of_notMem_prime R 𝔭 hr (by rw [← hxs, zero_mul])
    exact ⟨⟨⟨x, hx⟩, ⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0),
      Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

private theorem locSubring_isLocalRing : IsLocalRing (locSubring R 𝔭) := by
  apply IsLocalRing.of_nonunits_add
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hna hnb
  obtain ⟨r, s, hs, has⟩ := ha
  obtain ⟨r', s', hs', hbs⟩ := hb
  have hr : r ∈ 𝔭 := by
    by_contra h
    exact hna ((isUnit_locSubring_iff R 𝔭 ⟨r, s, hs, has⟩ hs has).mpr h)
  have hr' : r' ∈ 𝔭 := by
    by_contra h
    exact hnb ((isUnit_locSubring_iff R 𝔭 ⟨r', s', hs', hbs⟩ hs' hbs).mpr h)
  have hab : a + b ∈ locSubring R 𝔭 := Subring.add_mem _ ⟨r, s, hs, has⟩ ⟨r', s', hs', hbs⟩
  have hsum : (a + b) * ((s * s' : R) : F) = ((r * s' + r' * s : R) : F) := by
    rw [Subring.coe_mul, Subring.coe_add, Subring.coe_mul, Subring.coe_mul, ← has, ← hbs]
    ring
  intro hu
  have := (isUnit_locSubring_iff R 𝔭 hab (mul_notMem_prime R 𝔭 hs hs') hsum).mp hu
  exact this (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hr) (Ideal.mul_mem_right _ _ hr'))

private theorem mem_maximalIdeal_locSubring_iff {x : F} (hx : x ∈ locSubring R 𝔭) {r s : R}
    (hs : s ∉ 𝔭) (hxs : x * s = r) :
    haveI := locSubring_isLocalRing R 𝔭
    (⟨x, hx⟩ : locSubring R 𝔭) ∈ maximalIdeal (locSubring R 𝔭) ↔ r ∈ 𝔭 := by
  haveI := locSubring_isLocalRing R 𝔭
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_locSubring_iff R 𝔭 hx hs hxs, not_not]

end Local

end SD2

set_option autoImplicit false

open IsLocalRing IntermediateField

namespace SD2

section H1

variable {A : Type*} [CommRing A] [IsLocalRing A]
variable {R : Type*} [CommRing R] {k : Type*} [Field k] {S : Type*} [CommRing S] [Algebra k S]
variable (φ : A →+* R) (red : A →+* k) (red₀ : R →+* S)

private theorem mem_maximalIdeal_of_map_eq_zero {a : A} (ha : red a = 0) : a ∈ maximalIdeal A := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact (hu.map red).ne_zero ha

private theorem indepModKer_of_linearIndependent {ι : Type*} (b : ι → R)
    (hcompat : ∀ a, red₀ (φ a) = algebraMap k S (red a))
    (hli : LinearIndependent k (fun i => red₀ (b i))) :
    ∀ (s : Finset ι) (c : ι → A), (∑ i ∈ s, φ (c i) * b i) ∈ RingHom.ker red₀ →
      ∀ i ∈ s, c i ∈ maximalIdeal A := by
  intro s c hmem i hi
  apply mem_maximalIdeal_of_map_eq_zero red
  rw [RingHom.mem_ker, map_sum] at hmem
  have hsum : ∑ j ∈ s, red (c j) • red₀ (b j) = 0 := by
    rw [← hmem]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hcompat, Algebra.smul_def]
  exact linearIndependent_iff'.mp hli s (fun j => red (c j)) hsum i hi

end H1

section H2

variable {k E : Type*} [Field k] [Field E] [Algebra k E]

private theorem linearIndependent_pow_of_transcendental {x : E} (hx : Transcendental k x) :
    LinearIndependent k (fun a : ℕ => x ^ a) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have hinj := transcendental_iff_injective.mp hx
  set p : Polynomial k := ∑ a ∈ s, Polynomial.monomial a (g a) with hp
  have hp0 : Polynomial.aeval x p = 0 := by
    rw [hp, map_sum, ← hsum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Polynomial.aeval_monomial, Algebra.smul_def]
  have hpz : p = 0 := hinj (by rw [hp0, map_zero])
  have hc : p.coeff i = g i := by
    rw [hp, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' s i g, if_pos hi]
  rw [hpz, Polynomial.coeff_zero] at hc
  exact hc.symm

private theorem linearIndependent_pow_fin_of_relfinrank (x y : E) {n : ℕ} (hn : 0 < n)
    (hdeg : relfinrank k⟮x⟯ (adjoin k {x, y}) = n) :
    LinearIndependent k⟮x⟯ (fun i : Fin n => y ^ (i : ℕ)) := by
  have hle : k⟮x⟯ ≤ adjoin k {x, y} := adjoin.mono k _ _ (by simp)
  have hKy : extendScalars hle = k⟮x⟯⟮y⟯ := by
    rw [extendScalars_adjoin hle]
    apply le_antisymm
    · rw [adjoin_le_iff]
      intro z hz
      rcases hz with rfl | hz
      · have := IntermediateField.algebraMap_mem k⟮z⟯⟮y⟯ (AdjoinSimple.gen k z)
        rwa [AdjoinSimple.algebraMap_gen] at this
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        exact mem_adjoin_simple_self _ z
    · exact adjoin.mono _ _ _ (by simp)
  have hfin : Module.finrank k⟮x⟯ k⟮x⟯⟮y⟯ = n := by
    rw [← hdeg, relfinrank_eq_finrank_of_le hle, hKy]
  haveI : FiniteDimensional k⟮x⟯ k⟮x⟯⟮y⟯ := Module.finite_of_finrank_pos (by omega)
  have hint : IsIntegral k⟮x⟯ y := by
    have h1 : IsIntegral k⟮x⟯ (AdjoinSimple.gen k⟮x⟯ y) := Algebra.IsIntegral.isIntegral _
    have h2 := isIntegral_iff.mp h1
    rwa [AdjoinSimple.coe_gen] at h2
  have hnat : (minpoly k⟮x⟯ y).natDegree = n := by
    rw [← adjoin.finrank hint, hfin]
  set pb := adjoin.powerBasis hint with hpb
  have hdim : pb.dim = n := by rw [hpb, adjoin.powerBasis_dim, hnat]
  have hli : LinearIndependent k⟮x⟯ (fun i : Fin pb.dim => y ^ (i : ℕ)) := by
    have h0 : LinearIndependent k⟮x⟯ pb.basis := pb.basis.linearIndependent
    have h1 := h0.map' (k⟮x⟯⟮y⟯.val).toLinearMap
      (LinearMap.ker_eq_bot.mpr (k⟮x⟯⟮y⟯.val).toRingHom.injective)
    convert h1 using 1
    · ext i
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply, PowerBasis.basis_eq_pow, hpb,
        adjoin.powerBasis_gen, map_pow]
      rfl
    all_goals rfl
  subst hdim
  exact hli

private theorem linearIndependent_monomial_of_relfinrank (x y : E) {n : ℕ} (hn : 0 < n)
    (hx : Transcendental k x) (hdeg : relfinrank k⟮x⟯ (adjoin k {x, y}) = n) :
    LinearIndependent k (fun p : ℕ × Fin n => x ^ p.1 * y ^ (p.2 : ℕ)) := by
  have hb : LinearIndependent k (fun a : ℕ => (AdjoinSimple.gen k x) ^ a) := by
    apply LinearIndependent.of_comp (k⟮x⟯.val).toLinearMap
    convert linearIndependent_pow_of_transcendental hx using 1
    all_goals rfl
  have hc := linearIndependent_pow_fin_of_relfinrank x y hn hdeg
  convert linearIndependent_smul hb hc using 1
  all_goals rfl

end H2

section Dock

variable {A : Type*} [CommRing A] [IsLocalRing A]
variable {R : Type*} [CommRing R] {k E : Type*} [Field k] [Field E] [Algebra k E]
variable (φ : A →+* R) (red : A →+* k) (red₀ : R →+* E)

private theorem indepModKer_monomial (hcompat : ∀ a, red₀ (φ a) = algebraMap k E (red a))
    (X Y : R) {n : ℕ} (hn : 0 < n) (hx : Transcendental k (red₀ X))
    (hdeg : relfinrank k⟮red₀ X⟯ (adjoin k {red₀ X, red₀ Y}) = n) :
    ∀ (s : Finset (ℕ × Fin n)) (c : ℕ × Fin n → A),
      (∑ p ∈ s, φ (c p) * (X ^ p.1 * Y ^ (p.2 : ℕ))) ∈ RingHom.ker red₀ →
        ∀ p ∈ s, c p ∈ maximalIdeal A := by
  apply indepModKer_of_linearIndependent φ red red₀ (fun p : ℕ × Fin n => X ^ p.1 * Y ^ (p.2 : ℕ))
    hcompat
  convert linearIndependent_monomial_of_relfinrank (red₀ X) (red₀ Y) hn hx hdeg using 1
  ext p
  simp only [map_mul, map_pow]

end Dock

end SD2

set_option autoImplicit false

namespace SD2

private theorem exists_sum_monomial_of_mem_closure {A E : Type*} [CommRing A] [CommRing E]
    (φ : A →+* E) (X Y : E) {P : Polynomial (Polynomial A)} (hP : P.Monic)
    (hrel : P.eval₂ (Polynomial.eval₂RingHom φ X) Y = 0)
    {r : E} (hr : r ∈ Subring.closure (Set.range φ ∪ {X, Y})) :
    ∃ (s : Finset (ℕ × Fin P.natDegree)) (c : ℕ × Fin P.natDegree → A),
      r = ∑ p ∈ s, φ (c p) * (X ^ p.1 * Y ^ (p.2 : ℕ)) := by
  classical
  set f : Polynomial A →+* E := Polynomial.eval₂RingHom φ X with hf
  set Ψ : Polynomial (Polynomial A) →+* E := Polynomial.eval₂RingHom f Y with hΨ

  have hle : Subring.closure (Set.range φ ∪ {X, Y}) ≤ Ψ.range := by
    rw [Subring.closure_le]
    rintro z (⟨a, rfl⟩ | hz)
    · exact ⟨Polynomial.C (Polynomial.C a), by simp [hΨ, hf]⟩
    · rcases hz with rfl | hz
      · exact ⟨Polynomial.C Polynomial.X, by simp [hΨ, hf]⟩
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        exact ⟨Polynomial.X, by simp [hΨ]⟩
  obtain ⟨G, rfl⟩ := hle hr
  by_cases hP1 : P = 1
  ·
    have h10 : (1 : E) = 0 := by
      have : Ψ P = 0 := hrel
      rwa [hP1, map_one] at this
    refine ⟨∅, fun _ => 0, ?_⟩
    rw [Finset.sum_empty, ← mul_one (Ψ G), h10, mul_zero]
  have hΨP : Ψ P = 0 := hrel
  set Rm := G %ₘ P with hRm
  have hG : Ψ G = Ψ Rm := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div G P]
    rw [map_add, map_mul, hΨP, zero_mul, add_zero]
  have hdeg : Rm.natDegree < P.natDegree := Polynomial.natDegree_modByMonic_lt G hP hP1
  set n := P.natDegree with hn
  set D := (Finset.range n).sup (fun i => (Rm.coeff i).natDegree) + 1 with hD
  have hDi : ∀ i ∈ Finset.range n, (Rm.coeff i).natDegree < D := fun i hi =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (Rm.coeff i).natDegree) hi)
  refine ⟨(Finset.range D) ×ˢ (Finset.univ : Finset (Fin n)),
    fun p => (Rm.coeff (p.2 : ℕ)).coeff p.1, ?_⟩
  rw [hG, Finset.sum_product, Finset.sum_comm]
  rw [show Ψ Rm = Rm.eval₂ f Y from rfl, Polynomial.eval₂_eq_sum_range' f hdeg Y,
    ← Fin.sum_univ_eq_sum_range (fun i => f (Rm.coeff i) * Y ^ i) n]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show f (Rm.coeff i) = (Rm.coeff i).eval₂ φ X from rfl,
    Polynomial.eval₂_eq_sum_range' φ (hDi i (by simp)) X, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end SD2

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "algebraMap_laurentSeries_eq_single jqModC jqNModC jqNModC_one jqModC_eq_map_intCast modularFunctionFieldC qExpand_coeff_mul qExpand_coeff_of_not_dvd dedekindPsi ModularPolynomialData transcendental_jqModC"
p2m_open "ModularCurve"
namespace CharpSD2

section Modular

variable (N : ℕ) [NeZero N]
variable {L : Type*} [Field L]
variable (A : Subring L) {k : Type*} [Field k] (red : A →+* k)

private theorem constSeries_apply (a : A) :
    constSeries A a = HahnSeries.single 0 (a : L) := by
  show algebraMap L (LaurentSeries L) (a : L) = HahnSeries.single 0 (a : L)
  ext m
  rw [HahnSeries.algebraMap_apply', show algebraMap L (PowerSeries L) (a : L)
    = PowerSeries.C (a : L) from by simp, HahnSeries.ofPowerSeries_C]
  rfl

private theorem coeffRed_jqModC :
    coeffRed A red ⟨jqModC L, jqModC_mem_integralCoeffs A⟩ = jqModC k := by
  ext n
  rw [coeffRed_coeff]
  have hL : (⟨(jqModC L).coeff n, jqModC_mem_integralCoeffs A n⟩ : A)
      = (((jqModC ℤ).coeff n : ℤ) : A) := by
    ext
    push_cast
    rw [jqModC_eq_map_intCast, HahnSeries.map_coeff]
    rfl
  rw [hL, map_intCast]
  conv_rhs => rw [jqModC_eq_map_intCast]
  rw [HahnSeries.map_coeff]
  rfl

private theorem coeffRed_jqNModC :
    coeffRed A red ⟨jqNModC L N, jqNModC_mem_integralCoeffs N A⟩ = jqNModC k N := by
  have hqk : ∀ m : ℤ, (jqNModC k N).coeff ((N : ℤ) * m) = (jqModC k).coeff m := fun m => by
    rw [jqNModC, qExpand_coeff_mul]
  have hqk0 : ∀ {n : ℤ}, ¬ ((N : ℕ) : ℤ) ∣ n → (jqNModC k N).coeff n = 0 := fun h => by
    rw [jqNModC]
    exact qExpand_coeff_of_not_dvd _ _ h
  have hqL : ∀ m : ℤ, (jqNModC L N).coeff ((N : ℤ) * m) = (jqModC L).coeff m := fun m => by
    rw [jqNModC, qExpand_coeff_mul]
  have hqL0 : ∀ {n : ℤ}, ¬ ((N : ℕ) : ℤ) ∣ n → (jqNModC L N).coeff n = 0 := fun h => by
    rw [jqNModC]
    exact qExpand_coeff_of_not_dvd _ _ h
  ext n
  rw [coeffRed_coeff]
  by_cases h : ((N : ℕ) : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    have hL : (⟨(jqNModC L N).coeff ((N : ℤ) * m), jqNModC_mem_integralCoeffs N A _⟩ : A)
        = (((jqModC ℤ).coeff m : ℤ) : A) := by
      ext
      push_cast
      rw [hqL, jqModC_eq_map_intCast, HahnSeries.map_coeff]
      rfl
    rw [hL, map_intCast, hqk]
    conv_rhs => rw [jqModC_eq_map_intCast]
    rw [HahnSeries.map_coeff]
    rfl
  · have hL : (⟨(jqNModC L N).coeff n, jqNModC_mem_integralCoeffs N A n⟩ : A) = 0 := by
      ext
      push_cast
      exact hqL0 h
    rw [hL, map_zero, hqk0 h]

private theorem coeffRed_constSeries (a : A) :
    coeffRed A red ⟨constSeries A a, constSeries_mem_integralCoeffs A a⟩
      = algebraMap k (LaurentSeries k) (red a) := by
  ext n
  rw [coeffRed_coeff, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single]
  by_cases h : n = 0
  · subst h
    have hL : (⟨(constSeries A a).coeff 0, constSeries_mem_integralCoeffs A a 0⟩ : A) = a := by
      ext
      push_cast
      rw [constSeries_apply, HahnSeries.coeff_single]
      simp
    rw [hL, if_pos rfl]
  · have hL : (⟨(constSeries A a).coeff n, constSeries_mem_integralCoeffs A a n⟩ : A) = 0 := by
      ext
      push_cast
      rw [constSeries_apply, HahnSeries.coeff_single]
      simp [h]
    rw [hL, map_zero, if_neg h]

end Modular

section Fractions

variable (N : ℕ) [NeZero N]
variable {L : Type*} [Field L] (A : ValuationSubring L)

private theorem exists_fraction_of_mem_adjoin {f : LaurentSeries L}
    (hf : f ∈ IntermediateField.adjoin L {jqModC L, jqNModC L N}) :
    ∃ r s : modularRing N A.toSubring,
      (s : LaurentSeries L) ≠ 0 ∧ f * s = r := by
  induction hf using IntermediateField.adjoin_induction with
  | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨⟨jqModC L, jqModC_mem_modularRing N A.toSubring⟩, 1,
          by simp, by simp⟩
      · exact ⟨⟨jqNModC L N, jqNModC_mem_modularRing N A.toSubring⟩, 1,
          by simp, by simp⟩
  | algebraMap c =>
      by_cases hc0 : c = 0
      · subst hc0
        exact ⟨0, 1, by simp, by simp⟩
      · rcases A.mem_or_inv_mem c with hc | hc
        · have h1 : (constSeries A.toSubring ⟨c, hc⟩ : LaurentSeries L)
              = algebraMap L (LaurentSeries L) c := by
            rw [constSeries_apply, algebraMap_laurentSeries_eq_single]
          refine ⟨⟨constSeries A.toSubring ⟨c, hc⟩,
            constSeries_mem_modularRing N A.toSubring ⟨c, hc⟩⟩, 1, by simp, ?_⟩
          show algebraMap L (LaurentSeries L) c
              * ((1 : modularRing N A.toSubring) : LaurentSeries L)
            = constSeries A.toSubring ⟨c, hc⟩
          rw [h1, OneMemClass.coe_one, mul_one]
        · have h1 : (constSeries A.toSubring ⟨c⁻¹, hc⟩ : LaurentSeries L)
              = algebraMap L (LaurentSeries L) c⁻¹ := by
            rw [constSeries_apply, algebraMap_laurentSeries_eq_single]
          refine ⟨1, ⟨constSeries A.toSubring ⟨c⁻¹, hc⟩,
            constSeries_mem_modularRing N A.toSubring ⟨c⁻¹, hc⟩⟩, ?_, ?_⟩
          · show (constSeries A.toSubring ⟨c⁻¹, hc⟩ : LaurentSeries L) ≠ 0
            rw [h1]
            exact fun h => inv_ne_zero hc0
              ((map_eq_zero_iff _ (algebraMap L (LaurentSeries L)).injective).mp h)
          · show algebraMap L (LaurentSeries L) c * constSeries A.toSubring ⟨c⁻¹, hc⟩
              = ((1 : modularRing N A.toSubring) : LaurentSeries L)
            rw [h1, ← map_mul, mul_inv_cancel₀ hc0, map_one, OneMemClass.coe_one]
  | add x y hx hy ihx ihy =>
      obtain ⟨r, s, hs, hr⟩ := ihx
      obtain ⟨u, t, ht, hu⟩ := ihy
      refine ⟨r * t + u * s, s * t, by push_cast; exact mul_ne_zero hs ht, ?_⟩
      push_cast
      calc (x + y) * ((s : LaurentSeries L) * t)
          = x * s * t + y * t * s := by ring
        _ = (r : LaurentSeries L) * t + (u : LaurentSeries L) * s := by rw [hr, hu]
  | mul x y hx hy ihx ihy =>
      obtain ⟨r, s, hs, hr⟩ := ihx
      obtain ⟨u, t, ht, hu⟩ := ihy
      refine ⟨r * u, s * t, by push_cast; exact mul_ne_zero hs ht, ?_⟩
      push_cast
      calc x * y * ((s : LaurentSeries L) * t)
          = (x * s) * (y * t) := by ring
        _ = (r : LaurentSeries L) * u := by rw [hr, hu]
  | inv x hx ihx =>
      obtain ⟨r, s, hs, hr⟩ := ihx
      by_cases hx0 : x = 0
      · exact ⟨0, 1, by simp, by simp [hx0]⟩
      · have hr0 : (r : LaurentSeries L) ≠ 0 := by
          rw [← hr]
          exact mul_ne_zero hx0 hs
        refine ⟨s, r, hr0, ?_⟩
        rw [← hr, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]

end Fractions

section IntegralMembers

variable {L : Type*} [Field L] {k : Type*} [Field k]
variable {A : Subring L} {red : A →+* k}
variable {R : Subring (LaurentSeries L)} {hR : R ≤ integralCoeffs A}

private theorem mem_localizedAtKer_of_eval₂_monic
    {x : LaurentSeries L}
    (hx : x = 0 ∨ x ∈ localizedAtKer A red R hR ∨ x⁻¹ ∈ localizedAtKer A red R hR)
    {p : Polynomial (localizedAtKer A red R hR)} (hp : p.Monic)
    (hev : Polynomial.eval₂ (localizedAtKer A red R hR).subtype x p = 0) :
    x ∈ localizedAtKer A red R hR := by
  rcases hx with rfl | hx | hinv
  · exact Subring.zero_mem _
  · exact hx
  · by_cases hx0 : x = 0
    · subst hx0
      exact Subring.zero_mem _

    obtain ⟨m, hm⟩ : ∃ m, p.natDegree = m + 1 := by
      rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
      · exfalso
        have hp1 : p = 1 := hp.natDegree_eq_zero.mp h0
        rw [hp1, Polynomial.eval₂_one] at hev
        exact one_ne_zero hev
      · exact ⟨p.natDegree - 1, (Nat.succ_pred_eq_of_pos hpos).symm⟩

    have heval : ∑ i ∈ Finset.range (m + 1 + 1),
        (localizedAtKer A red R hR).subtype (p.coeff i) * x ^ i = 0 := by
      rw [← Polynomial.eval₂_eq_sum_range' _ (by rw [hm]; exact Nat.lt_succ_self _) x, hev]
    rw [Finset.sum_range_succ] at heval
    have hc1 : p.coeff (m + 1) = 1 := by
      have h := hp.coeff_natDegree
      rwa [hm] at h
    rw [hc1, map_one, one_mul] at heval
    have hxn : x ^ (m + 1)
        = -∑ i ∈ Finset.range (m + 1),
            (localizedAtKer A red R hR).subtype (p.coeff i) * x ^ i :=
      eq_neg_of_add_eq_zero_right heval

    have hkey : x = -∑ i ∈ Finset.range (m + 1),
        (localizedAtKer A red R hR).subtype (p.coeff i) * (x⁻¹) ^ (m - i) := by
      have hpow : ∀ i ∈ Finset.range (m + 1), (x⁻¹) ^ m * x ^ i = (x⁻¹) ^ (m - i) := by
        intro i hi
        have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h1 : (x⁻¹) ^ m = (x⁻¹) ^ (m - i) * (x⁻¹) ^ i := by
          rw [← pow_add, Nat.sub_add_cancel hi']
        have h2 : (x⁻¹) ^ i * x ^ i = 1 := by
          rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero i hx0)]
        rw [h1, mul_assoc, h2, mul_one]
      calc x = (x⁻¹) ^ m * x ^ (m + 1) := by
            rw [pow_succ, ← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero m hx0), one_mul]
        _ = (x⁻¹) ^ m * -∑ i ∈ Finset.range (m + 1),
              (localizedAtKer A red R hR).subtype (p.coeff i) * x ^ i := by rw [hxn]
        _ = -∑ i ∈ Finset.range (m + 1),
              (localizedAtKer A red R hR).subtype (p.coeff i) * ((x⁻¹) ^ m * x ^ i) := by
            rw [mul_neg, Finset.mul_sum]
            congr 1
            refine Finset.sum_congr rfl fun i _ => by ring
        _ = -∑ i ∈ Finset.range (m + 1),
              (localizedAtKer A red R hR).subtype (p.coeff i) * (x⁻¹) ^ (m - i) := by
            congr 1
            exact Finset.sum_congr rfl fun i hi => by rw [hpow i hi]
    rw [hkey]
    exact Subring.neg_mem _ (Subring.sum_mem _ fun i _ =>
      Subring.mul_mem _ (p.coeff i).2 (Subring.pow_mem _ hinv _))

end IntegralMembers

section Instantiation

variable (N : ℕ) [NeZero N]
variable {L : Type*} [Field L] (A : ValuationSubring L)
variable {k : Type*} [Field k] (red : A.toSubring →+* k)

private local instance : ValuationRing A.toSubring := inferInstanceAs (ValuationRing A)

private theorem dedekindPsi_pos : 0 < dedekindPsi N := by
  rw [dedekindPsi]
  refine Finset.sum_pos' (fun d _ => Nat.zero_le _) ⟨1, ?_, ?_⟩
  · rw [Finset.mem_filter]
    exact ⟨Nat.one_mem_divisors.mpr (NeZero.ne N), squarefree_one⟩
  · simpa using Nat.pos_of_ne_zero (NeZero.ne N)

private def constToModular : A.toSubring →+* modularRing N A.toSubring :=
  (constSeries A.toSubring).codRestrict (modularRing N A.toSubring)
    (constSeries_mem_modularRing N A.toSubring)

@[scoped simp]
private theorem coe_constToModular (a : A.toSubring) :
    ((constToModular N A a : modularRing N A.toSubring) : LaurentSeries L)
      = constSeries A.toSubring a :=
  rfl

private def jR : modularRing N A.toSubring :=
  ⟨jqModC L, jqModC_mem_modularRing N A.toSubring⟩

private def jNR : modularRing N A.toSubring :=
  ⟨jqNModC L N, jqNModC_mem_modularRing N A.toSubring⟩

private theorem localizedAtKer_eq_locSubring
    [(redKer A.toSubring red (modularRing N A.toSubring)
      (modularRing_le_integralCoeffs N A.toSubring)).IsPrime] :
    localizedAtKer A.toSubring red (modularRing N A.toSubring)
        (modularRing_le_integralCoeffs N A.toSubring)
      = SD2.locSubring (modularRing N A.toSubring)
          (redKer A.toSubring red (modularRing N A.toSubring)
            (modularRing_le_integralCoeffs N A.toSubring)) :=
  Subring.ext fun _ => Iff.rfl

private theorem redRes_constToModular (a : A.toSubring) :
    redRes A.toSubring red (modularRing N A.toSubring)
        (modularRing_le_integralCoeffs N A.toSubring) (constToModular N A a)
      = algebraMap k (LaurentSeries k) (red a) :=
  coeffRed_constSeries A.toSubring red a

private theorem redRes_jR :
    redRes A.toSubring red (modularRing N A.toSubring)
        (modularRing_le_integralCoeffs N A.toSubring) (jR N A)
      = jqModC k :=
  coeffRed_jqModC A.toSubring red

private theorem redRes_jNR :
    redRes A.toSubring red (modularRing N A.toSubring)
        (modularRing_le_integralCoeffs N A.toSubring) (jNR N A)
      = jqNModC k N :=
  coeffRed_jqNModC N A.toSubring red

private theorem hrel_modular (data : ModularPolynomialData N) :
    (data.Φ.map (Polynomial.mapRingHom (Int.castRingHom A.toSubring))).eval₂
      (Polynomial.eval₂RingHom (constSeries A.toSubring) (jqModC L)) (jqNModC L N) = 0 := by
  have h := data.eval_jqNModC_mul_eq_zero L 1
  simp only [jqNModC_one, one_mul] at h
  rw [Polynomial.eval₂_map]
  convert h using 2
  · rfl
  apply Polynomial.ringHom_ext
  · intro a
    simp [constSeries]
  · simp

private theorem natDegree_map_phi (data : ModularPolynomialData N) :
    (data.Φ.map (Polynomial.mapRingHom (Int.castRingHom A.toSubring))).natDegree
      = dedekindPsi N := by
  rw [data.monic.natDegree_map, data.natDegree_eq]

private theorem hspan_modular (data : ModularPolynomialData N) :
    ∀ r : modularRing N A.toSubring,
      ∃ (s : Finset (ℕ × Fin (dedekindPsi N))) (c : ℕ × Fin (dedekindPsi N) → A.toSubring),
        r = ∑ p ∈ s, constToModular N A (c p) * (jR N A ^ p.1 * jNR N A ^ (p.2 : ℕ)) := by
  intro r
  have h := SD2.exists_sum_monomial_of_mem_closure (constSeries A.toSubring)
    (jqModC L) (jqNModC L N) (data.monic.map _) (hrel_modular N A data) r.2
  rw [natDegree_map_phi] at h
  obtain ⟨s, c, hc⟩ := h
  refine ⟨s, c, Subtype.ext ?_⟩
  rw [hc]
  push_cast
  rfl

private theorem hind_modular
    (hdeg : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
      (modularFunctionFieldC k N) = dedekindPsi N) :
    SD2.IndepModPrime
      (redKer A.toSubring red (modularRing N A.toSubring)
        (modularRing_le_integralCoeffs N A.toSubring))
      (constToModular N A)
      (fun p : ℕ × Fin (dedekindPsi N) => jR N A ^ p.1 * jNR N A ^ (p.2 : ℕ)) := by
  intro s c hmem
  refine SD2.indepModKer_monomial (constToModular N A) red
    (redRes A.toSubring red (modularRing N A.toSubring)
      (modularRing_le_integralCoeffs N A.toSubring))
    (redRes_constToModular N A red) (jR N A) (jNR N A) (dedekindPsi_pos N)
    ?_ ?_ s c hmem
  · rw [redRes_jR]
    exact transcendental_jqModC k
  · rw [redRes_jR, redRes_jNR]
    exact hdeg

private theorem mem_or_inv_mem_of_mem_adjoin (data : ModularPolynomialData N)
    (hdeg : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
      (modularFunctionFieldC k N) = dedekindPsi N)
    {f : LaurentSeries L}
    (hf : f ∈ IntermediateField.adjoin L {jqModC L, jqNModC L N}) :
    f ∈ localizedAtKer A.toSubring red (modularRing N A.toSubring)
        (modularRing_le_integralCoeffs N A.toSubring)
      ∨ f⁻¹ ∈ localizedAtKer A.toSubring red (modularRing N A.toSubring)
          (modularRing_le_integralCoeffs N A.toSubring) := by
  haveI := redKer_isPrime A.toSubring red (modularRing N A.toSubring)
    (modularRing_le_integralCoeffs N A.toSubring)
  obtain ⟨r, s, hs0, hfs⟩ := exists_fraction_of_mem_adjoin N A hf
  rw [localizedAtKer_eq_locSubring]
  exact SD2.mem_or_inv_mem_of_fraction _ _ (constToModular N A)
    (fun p : ℕ × Fin (dedekindPsi N) => jR N A ^ p.1 * jNR N A ^ (p.2 : ℕ))
    (hspan_modular N A data) (hind_modular N A red hdeg) hs0 hfs

private theorem mem_localizedAtKer_of_isIntegral (data : ModularPolynomialData N)
    (hdeg : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
      (modularFunctionFieldC k N) = dedekindPsi N)
    {x : LaurentSeries L}
    (hx : x ∈ IntermediateField.adjoin L {jqModC L, jqNModC L N})
    {p : Polynomial (localizedAtKer A.toSubring red (modularRing N A.toSubring)
      (modularRing_le_integralCoeffs N A.toSubring))}
    (hp : p.Monic)
    (hev : Polynomial.eval₂ (localizedAtKer A.toSubring red (modularRing N A.toSubring)
      (modularRing_le_integralCoeffs N A.toSubring)).subtype x p = 0) :
    x ∈ localizedAtKer A.toSubring red (modularRing N A.toSubring)
      (modularRing_le_integralCoeffs N A.toSubring) := by
  refine mem_localizedAtKer_of_eval₂_monic ?_ hp hev
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  · exact Or.inr (mem_or_inv_mem_of_mem_adjoin N A red data hdeg hx)

end Instantiation

end CharpSD2
p2m_reactivate "P2MW.S_ModularCurve_CharPReduction_mem_modularLocalized_of_eval2_monic.ModularCurve.CharpSD2"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPReduction_mem_modularLocalized_of_eval2_monic.ModularCurve.CharpSD2 P2MW.S_ModularCurve_CharPReduction_mem_modularLocalized_of_eval2_monic.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_CharPReduction_mem_modularLocalized_of_eval2_monic.ModularCurve.CharpSD2 P2MW.S_ModularCurve_CharPReduction_mem_modularLocalized_of_eval2_monic.ModularCurve"

theorem solution {L : Type*} [Field L] (A : ValuationSubring L)
    {k : Type*} [Field k] (red : A.toSubring →+* k) (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N)
    (hdeg : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
      (modularFunctionFieldC k N) = dedekindPsi N)
    {x : LaurentSeries L}
    (hx : x ∈ IntermediateField.adjoin L {jqModC L, jqNModC L N})
    {p : Polynomial (modularLocalized N A.toSubring red)} (hp : p.Monic)
    (hev : Polynomial.eval₂ (modularLocalized N A.toSubring red).subtype x p = 0) :
    x ∈ modularLocalized N A.toSubring red:=
  ModularCurve.CharpSD2.mem_localizedAtKer_of_isIntegral N A red data hdeg hx hp hev

end S_ModularCurve_CharPReduction_mem_modularLocalized_of_eval2_monic
end P2MW
export P2MW.S_ModularCurve_CharPReduction_mem_modularLocalized_of_eval2_monic (solution)
