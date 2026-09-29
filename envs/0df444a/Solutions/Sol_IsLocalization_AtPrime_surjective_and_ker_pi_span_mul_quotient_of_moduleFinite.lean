-- Prove2me | solution 1 for IsLocalization.AtPrime.surjective_and_ker_pi_span_mul_quotient_of_moduleFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/1d534847-3938-57b1-8515-3721458332bd

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalization_AtPrime_surjective_and_ker_pi_span_mul_quotient_of_moduleFinite

set_option autoImplicit false

universe u

open scoped Pointwise

namespace FinQuotLG

section Loc

variable {A : Type u} [CommRing A] [IsDomain A] {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
  (R : Type u) [CommRing R] [Algebra R K] [Algebra A R] [IsScalarTower A R K]
  (m : Ideal A) [m.IsMaximal] [IsLocalization.AtPrime R m]

theorem mem_range_iff (x : K) :
    x ∈ Set.range (algebraMap R K) ↔ ∃ a s : A, s ∉ m ∧ x = algebraMap A K a * (algebraMap A K s)⁻¹ := by
  constructor
  · rintro ⟨r, rfl⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective m.primeCompl r
    refine ⟨a, s, s.2, ?_⟩
    have hs : algebraMap A K s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero fun h => s.2 (h ▸ m.zero_mem))
    rw [eq_mul_inv_iff_mul_eq₀ hs, IsScalarTower.algebraMap_apply A R K s, ← map_mul,
      IsLocalization.mk'_spec, ← IsScalarTower.algebraMap_apply]
  · rintro ⟨a, s, hs, rfl⟩
    refine ⟨IsLocalization.mk' R a (⟨s, hs⟩ : m.primeCompl), ?_⟩
    have hs' : algebraMap A K s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero fun h => hs (h ▸ m.zero_mem))
    rw [eq_mul_inv_iff_mul_eq₀ hs', IsScalarTower.algebraMap_apply A R K s, ← map_mul]
    show algebraMap R K (IsLocalization.mk' R a (⟨s, hs⟩ : m.primeCompl) * algebraMap A R ((⟨s, hs⟩ : m.primeCompl) : A)) = _
    rw [IsLocalization.mk'_spec, ← IsScalarTower.algebraMap_apply]

end Loc

section Sets

variable (k : Type u) [Field k] {A : Type u} [CommRing A] [IsDomain A] [Algebra k A]
  {K : Type u} [Field K] [Algebra k K] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K]
  (m : Ideal A) [hm : m.IsMaximal] (B : Subalgebra A K)

omit hm in
theorem algebraMap_ne_zero {s : A} (hs : s ∉ m) : algebraMap A K s ≠ 0 :=
  IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero fun h => hs (h ▸ m.zero_mem))

def locSub : Submodule k K where
  carrier := {x | ∃ a s : A, s ∉ m ∧ x = algebraMap A K a * (algebraMap A K s)⁻¹}
  add_mem' := by
    rintro _ _ ⟨a, s, hs, rfl⟩ ⟨a', s', hs', rfl⟩
    refine ⟨a * s' + a' * s, s * s', fun h => (hm.isPrime.mem_or_mem h).elim hs hs', ?_⟩
    have := algebraMap_ne_zero (K := K) m hs
    have := algebraMap_ne_zero (K := K) m hs'
    simp only [map_add, map_mul]
    field_simp
  zero_mem' := ⟨0, 1, fun h => hm.ne_top ((Ideal.eq_top_iff_one m).mpr h), by simp⟩
  smul_mem' := by
    rintro c _ ⟨a, s, hs, rfl⟩
    refine ⟨algebraMap k A c * a, s, hs, ?_⟩
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, mul_assoc]

theorem mem_locSub_iff (x : K) :
    x ∈ locSub k m ↔ ∃ a s : A, s ∉ m ∧ x = algebraMap A K a * (algebraMap A K s)⁻¹ := Iff.rfl

def locBSub : Submodule k K where
  carrier := {x | ∃ b : K, b ∈ B ∧ ∃ s : A, s ∉ m ∧ x = b * (algebraMap A K s)⁻¹}
  add_mem' := by
    rintro _ _ ⟨b, hb, s, hs, rfl⟩ ⟨b', hb', s', hs', rfl⟩
    refine ⟨algebraMap A K s' * b + algebraMap A K s * b', B.add_mem (B.mul_mem (B.algebraMap_mem s') hb)
      (B.mul_mem (B.algebraMap_mem s) hb'), s * s', fun h => (hm.isPrime.mem_or_mem h).elim hs hs', ?_⟩
    have := algebraMap_ne_zero (K := K) m hs
    have := algebraMap_ne_zero (K := K) m hs'
    simp only [map_mul]
    field_simp
  zero_mem' := ⟨0, B.zero_mem, 1, fun h => hm.ne_top ((Ideal.eq_top_iff_one m).mpr h), by simp⟩
  smul_mem' := by
    rintro c _ ⟨b, hb, s, hs, rfl⟩
    refine ⟨c • b, ?_, s, hs, by rw [smul_mul_assoc]⟩
    rw [← IsScalarTower.algebraMap_smul A c b]
    exact B.smul_mem hb _

theorem mem_locBSub_iff (x : K) :
    x ∈ locBSub k m B ↔ ∃ b : K, b ∈ B ∧ ∃ s : A, s ∉ m ∧ x = b * (algebraMap A K s)⁻¹ := Iff.rfl

theorem locSub_le_locBSub : locSub k m ≤ locBSub k m B := by
  rintro _ ⟨a, s, hs, rfl⟩
  exact ⟨_, B.algebraMap_mem a, s, hs, rfl⟩

theorem le_locBSub : (Submodule.span k (B : Set K)) ≤ locBSub k m B := by
  rw [Submodule.span_le]
  intro b hb
  exact ⟨b, hb, 1, fun h => hm.ne_top ((Ideal.eq_top_iff_one m).mpr h), by simp⟩

variable (R : Type u) [CommRing R] [Algebra R K] [Algebra A R] [IsScalarTower A R K] [IsLocalization.AtPrime R m]

theorem span_range_eq_locSub : Submodule.span k (Set.range (algebraMap R K)) = locSub k m := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact (mem_range_iff R m x).mp hx
  · intro x hx
    exact Submodule.subset_span ((mem_range_iff R m x).mpr hx)

theorem span_mul_range_eq_locBSub :
    Submodule.span k ((B : Set K) * Set.range (algebraMap R K)) = locBSub k m B := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨b, hb, x, hx, rfl⟩
    obtain ⟨a, s, hs, rfl⟩ := (mem_range_iff R m x).mp hx
    refine ⟨b * algebraMap A K a, B.mul_mem hb (B.algebraMap_mem a), s, hs, by rw [mul_assoc]⟩
  · rintro _ ⟨b, hb, s, hs, rfl⟩
    apply Submodule.subset_span
    refine Set.mem_mul.mpr ⟨b, hb, (algebraMap A K s)⁻¹, (mem_range_iff R m _).mpr ⟨1, s, hs, by simp⟩, rfl⟩

end Sets

end FinQuotLG

namespace FinQuotLG

section Denominator

variable {A : Type u} [CommRing A] [IsDomain A] {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
  (B : Subalgebra A K)

theorem exists_denominator (hB : Module.Finite A B) :
    ∃ d : A, d ≠ 0 ∧ ∀ b : K, b ∈ B → ∃ a : A, algebraMap A K d * b = algebraMap A K a := by
  classical
  obtain ⟨S, hS⟩ := hB.fg_top
  have hden : ∀ g : ↥B, ∃ s : A, s ≠ 0 ∧ ∃ a : A, algebraMap A K s * (g : K) = algebraMap A K a := by
    intro g
    obtain ⟨a, s, hs, e⟩ := IsFractionRing.div_surjective (A := A) (g : K)
    refine ⟨s, nonZeroDivisors.ne_zero hs, a, ?_⟩
    rw [← e, mul_div_cancel₀ _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs)]
  choose den hden0 num hnum using hden
  refine ⟨∏ g ∈ S, den g, Finset.prod_ne_zero_iff.mpr (fun g _ => hden0 g), ?_⟩
  intro b hb
  have hmem : (⟨b, hb⟩ : ↥B) ∈ Submodule.span A (S : Set ↥B) := by rw [hS]; trivial
  suffices h : ∀ x : ↥B, x ∈ Submodule.span A (S : Set ↥B) →
      ∃ a : A, algebraMap A K (∏ g ∈ S, den g) * (x : K) = algebraMap A K a from h _ hmem
  intro x hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    refine ⟨(∏ g' ∈ S.erase g, den g') * num g, ?_⟩
    rw [← Finset.mul_prod_erase S den (Finset.mem_coe.mp hg), map_mul, map_mul, mul_comm (algebraMap A K (den g)),
      mul_assoc, hnum]
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨a', ha'⟩ := hy
    refine ⟨a + a', ?_⟩
    rw [Subalgebra.coe_add, mul_add, ha, ha', map_add]
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨c * a, ?_⟩
    rw [Subalgebra.coe_smul, Algebra.smul_def, mul_left_comm, ha, ← map_mul]

end Denominator

section Support

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]

omit [IsDomain A] in

theorem finite_setOf_isMaximal_mem (hdim : ∀ p : Ideal A, p.IsPrime → p ≠ ⊥ → p.IsMaximal) {d : A} (hd : d ≠ 0) :
    {m : Ideal A | m.IsMaximal ∧ d ∈ m}.Finite := by
  apply (Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {d})).subset
  rintro m ⟨hm, hdm⟩
  refine ⟨⟨hm.isPrime, (Ideal.span_singleton_le_iff_mem _).mpr hdm⟩, ?_⟩
  rintro q ⟨hq, hdq⟩ hqm
  have hqne : q ≠ ⊥ := by
    rintro rfl
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_bot] at hdq
    exact hd hdq
  exact ((hdim q hq hqne).eq_of_le hm.ne_top hqm).ge

theorem exists_pow_forall_mul_mem (hdim : ∀ p : Ideal A, p.IsPrime → p ≠ ⊥ → p.IsMaximal)
    (m : Ideal A) [hm : m.IsMaximal] {d : A} (hd : d ≠ 0) :
    ∃ N : ℕ, ∀ x ∈ m ^ N, ∃ a s : A, s ∉ m ∧ s * x = d * a := by
  let L := Localization.AtPrime m
  have hrad : IsLocalRing.maximalIdeal L ≤ (Ideal.span {algebraMap A L d}).radical := by
    rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro P ⟨hdP, hP⟩
    have h1 : P.comap (algebraMap A L) ≠ ⊥ := fun h => by
      have : algebraMap A L d ∈ P := hdP (Ideal.subset_span rfl)
      have : d ∈ P.comap (algebraMap A L) := this
      rw [h, Ideal.mem_bot] at this
      exact hd this
    have h2 : P.comap (algebraMap A L) ≤ m := by
      intro x hx
      by_contra hxm
      apply hP.ne_top
      apply Ideal.eq_top_of_isUnit_mem P hx
      exact IsLocalization.map_units L (⟨x, hxm⟩ : m.primeCompl)
    have h3 : P.comap (algebraMap A L) = m :=
      (hdim _ (Ideal.comap_isPrime _ P) h1).eq_of_le hm.ne_top h2
    calc IsLocalRing.maximalIdeal L = m.map (algebraMap A L) := (IsLocalization.AtPrime.map_eq_maximalIdeal m L).symm
      _ = (P.comap (algebraMap A L)).map (algebraMap A L) := by rw [h3]
      _ ≤ P := Ideal.map_comap_le
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  refine ⟨N, fun x hx => ?_⟩
  have hx' : algebraMap A L x ∈ Ideal.span {algebraMap A L d} := by
    apply hN
    have : algebraMap A L x ∈ (m.map (algebraMap A L)) ^ N := by
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hx
    rwa [IsLocalization.AtPrime.map_eq_maximalIdeal m L] at this
  obtain ⟨ℓ, hℓ⟩ := Ideal.mem_span_singleton'.mp hx'
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective m.primeCompl ℓ
  refine ⟨a, s, s.2, ?_⟩
  have h := congrArg (fun y => algebraMap A L (s : A) * y) hℓ
  simp only at h
  rw [← mul_assoc, IsLocalization.mk'_spec', ← map_mul, ← map_mul] at h
  have := IsLocalization.injective L m.primeCompl_le_nonZeroDivisors h
  linear_combination -this

end Support

section KeyEstimate

variable (k : Type u) [Field k] {A : Type u} [CommRing A] [IsDomain A] [Algebra k A]
  {K : Type u} [Field K] [Algebra k K] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K]
  (m : Ideal A) [hm : m.IsMaximal] (B : Subalgebra A K)

include hm in
theorem mul_mem_locSub_of {d : A} (hdB : ∀ b : K, b ∈ B → ∃ a : A, algebraMap A K d * b = algebraMap A K a)
    {N : ℕ} (hN : ∀ x ∈ m ^ N, ∃ a s : A, s ∉ m ∧ s * x = d * a)
    {x : A} (hx : x ∈ m ^ N) {b : K} (hb : b ∈ B) :
    algebraMap A K x * b ∈ locSub k m (K := K) := by
  obtain ⟨a, s, hs, hsx⟩ := hN x hx
  obtain ⟨c, hc⟩ := hdB b hb
  refine ⟨a * c, s, hs, ?_⟩
  have hs0 := algebraMap_ne_zero (K := K) m hs
  rw [eq_mul_inv_iff_mul_eq₀ hs0, map_mul, mul_assoc, ← hc]
  calc algebraMap A K x * (b * algebraMap A K s) = algebraMap A K (s * x) * b := by rw [map_mul]; ring
    _ = algebraMap A K a * (algebraMap A K d * b) := by rw [hsx, map_mul]; ring

end KeyEstimate

end FinQuotLG

namespace FinQuotLG

open Ideal

theorem exists_algebraMap_add_mem {k A : Type u} [Field k] [CommRing A] [Algebra k A] (m : Ideal A)
    (hres : Function.Surjective (algebraMap k (A ⧸ m))) (a : A) :
    ∃ (c : k) (n : A), n ∈ m ∧ a = algebraMap k A c + n := by
  obtain ⟨c, hc⟩ := hres (Ideal.Quotient.mk m a)
  refine ⟨c, a - algebraMap k A c, ?_, by ring⟩
  rw [← Ideal.Quotient.eq, ← hc]
  rfl

theorem finite_quotient_pow (k A : Type u) [Field k] [CommRing A] [IsNoetherianRing A] [Algebra k A]
    (m : Ideal A) [m.IsMaximal] (hres : Function.Surjective (algebraMap k (A ⧸ m))) (N : ℕ) :
    Module.Finite k (A ⧸ m ^ N) := by
  induction N with
  | zero =>
      rw [pow_zero, Ideal.one_eq_top]
      haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
      infer_instance
  | succ N ih =>

      have hle : m ^ (N + 1) ≤ m ^ N := Ideal.pow_le_pow_right (Nat.le_succ N)
      let f : (A ⧸ m ^ (N + 1)) →ₗ[k] (A ⧸ m ^ N) := (Ideal.Quotient.factorₐ k hle).toLinearMap
      have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hle

      obtain ⟨S, hS⟩ := (IsNoetherian.noetherian (m ^ N) : (m ^ N).FG)
      have hker : LinearMap.ker f = Submodule.span k ((Ideal.Quotient.mk (m ^ (N + 1))) '' (S : Set A)) := by
        apply le_antisymm
        · intro x hx
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
          have ha : a ∈ m ^ N := by
            have : Ideal.Quotient.mk (m ^ N) a = 0 := hx
            exact Ideal.Quotient.eq_zero_iff_mem.mp this
          rw [← hS] at ha
          refine Submodule.span_induction (p := fun a _ => Ideal.Quotient.mk (m ^ (N + 1)) a ∈
              Submodule.span k ((Ideal.Quotient.mk (m ^ (N + 1))) '' (S : Set A))) ?_ ?_ ?_ ?_ ha
          · intro s hs
            exact Submodule.subset_span ⟨s, hs, rfl⟩
          · simp
          · intro x y _ _ hx hy
            rw [map_add]; exact Submodule.add_mem _ hx hy
          · intro a x hx hax

            obtain ⟨c, n, hn, rfl⟩ := exists_algebraMap_add_mem m hres a
            have hxN : x ∈ m ^ N := by rw [← hS]; exact hx
            have hnx : Ideal.Quotient.mk (m ^ (N + 1)) (n * x) = 0 := by
              rw [Ideal.Quotient.eq_zero_iff_mem, pow_succ']
              exact Ideal.mul_mem_mul hn hxN
            rw [smul_eq_mul, add_mul, map_add, hnx, add_zero, map_mul, Ideal.Quotient.mk_algebraMap, ← Algebra.smul_def]
            exact Submodule.smul_mem _ c hax
        · rw [Submodule.span_le]
          rintro _ ⟨s, hs, rfl⟩
          have hsN : s ∈ m ^ N := by rw [← hS]; exact Submodule.subset_span hs
          show f (Ideal.Quotient.mk (m ^ (N + 1)) s) = 0
          change Ideal.Quotient.factor hle (Ideal.Quotient.mk (m ^ (N + 1)) s) = 0
          rw [Ideal.Quotient.factor_mk]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr hsN
      have hkerFG : (LinearMap.ker f).FG := by
        rw [hker]
        exact Submodule.fg_span ((S.finite_toSet).image _)
      have htop : (⊤ : Submodule k (A ⧸ m ^ (N + 1))).FG := by
        refine Submodule.fg_of_fg_map_of_fg_inf_ker f ?_ ?_
        · rw [Submodule.map_top, LinearMap.range_eq_top.mpr hf]
          exact Module.Finite.fg_top
        · rw [top_inf_eq]; exact hkerFG
      exact Module.finite_def.mpr htop

theorem finite_of_surjective_of_smul_pow_le {k A : Type u} [Field k] [CommRing A] [IsNoetherianRing A] [Algebra k A]
    (m : Ideal A) [m.IsMaximal] (hres : Function.Surjective (algebraMap k (A ⧸ m))) (N : ℕ)
    {V : Type u} [AddCommGroup V] [Module k V] {ι : Type u} [Finite ι]
    (f : (ι → A) →ₗ[k] V) (hf : Function.Surjective f)
    (hker : ∀ g : ι → A, (∀ i, g i ∈ m ^ N) → f g = 0) :
    Module.Finite k V := by
  haveI := finite_quotient_pow k A m hres N

  let π : (ι → A) →ₗ[k] (ι → A ⧸ m ^ N) := (Ideal.Quotient.mkₐ k (m ^ N)).toLinearMap.compLeft ι
  have hπ : Function.Surjective π := fun g => by
    choose g' hg' using fun i => Ideal.Quotient.mk_surjective (g i)
    exact ⟨g', funext fun i => hg' i⟩
  have hle : LinearMap.ker π ≤ LinearMap.ker f := by
    intro g hg
    refine hker g fun i => ?_
    have : π g i = 0 := by rw [LinearMap.mem_ker.mp hg]; rfl
    exact Ideal.Quotient.eq_zero_iff_mem.mp this

  let fbar : ((ι → A) ⧸ LinearMap.ker π) →ₗ[k] V := (LinearMap.ker π).liftQ f hle
  have hfbar : Function.Surjective fbar := by
    intro v
    obtain ⟨g, rfl⟩ := hf v
    exact ⟨Submodule.Quotient.mk g, rfl⟩
  haveI : Module.Finite k ((ι → A) ⧸ LinearMap.ker π) :=
    Module.Finite.equiv (π.quotKerEquivOfSurjective hπ).symm
  exact Module.Finite.of_surjective fbar hfbar

end FinQuotLG

namespace FinQuotLG

section Aux2

variable (k : Type u) [Field k] {A : Type u} [CommRing A] [IsDomain A] [Algebra k A]
  {K : Type u} [Field K] [Algebra k K] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K]
  (m : Ideal A) [hm : m.IsMaximal]

theorem mul_inv_mem_locSub {x : K} (hx : x ∈ locSub k m (K := K)) {s : A} (hs : s ∉ m) :
    x * (algebraMap A K s)⁻¹ ∈ locSub k m (K := K) := by
  obtain ⟨a, s', hs', rfl⟩ := hx
  refine ⟨a, s' * s, fun h => (hm.isPrime.mem_or_mem h).elim hs' hs, ?_⟩
  rw [map_mul, mul_inv, mul_assoc]

omit [IsDomain A] in

theorem exists_mul_sub_one_mem_pow {s : A} (hs : s ∉ m) (N : ℕ) : ∃ t : A, t * s - 1 ∈ m ^ N := by
  obtain ⟨y, i, hi, e⟩ := hm.exists_inv hs
  have hcop : IsCoprime m (Ideal.span {s}) :=
    Ideal.isCoprime_iff_exists.mpr ⟨i, hi, y * s, Ideal.mem_span_singleton'.mpr ⟨y, rfl⟩, by rw [← e]; ring⟩
  obtain ⟨i', hi', j, hj, e'⟩ := Ideal.isCoprime_iff_exists.mp (hcop.pow_left (m := N))
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hj
  exact ⟨t, by rw [show t * s - 1 = -i' by rw [← e']; ring]; exact neg_mem hi'⟩

end Aux2

end FinQuotLG

open FinQuotLG in
theorem solution
    (k : Type u) [Field k] {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Algebra k A]
    (K : Type u) [Field K] [Algebra k K] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K]
    (hdim : ∀ p : Ideal A, p.IsPrime → p ≠ ⊥ → p.IsMaximal)
    (hres : ∀ m : Ideal A, m.IsMaximal → Function.Surjective (algebraMap k (A ⧸ m)))
    {X : Type u} (P : X → Prop) (R : X → Type u) [∀ z, CommRing (R z)] [∀ z, Algebra (R z) K]
    [∀ z : {z : X // P z}, Algebra A (R z.1)] [∀ z : {z : X // P z}, IsScalarTower A (R z.1) K]
    (𝔪 : {z : X // P z} → Ideal A) [∀ z, (𝔪 z).IsMaximal] (h𝔪 : Function.Injective 𝔪)
    [∀ z : {z : X // P z}, IsLocalization.AtPrime (R z.1) (𝔪 z)]
    (B : Subalgebra A K) (hB : Module.Finite A B) :

    let Bz : X → Submodule k K := fun z =>
      Submodule.span k ((B : Set K) * Set.range (algebraMap (R z) K))
    let Q : X → Type u := fun z =>
      ↥(Bz z) ⧸ (Submodule.span k (Set.range (algebraMap (R z) K))).comap (Bz z).subtype

    let φ : ↥(Submodule.span k (B : Set K)) →ₗ[k] ((z : {z : X // P z}) → Q z.1) :=
      LinearMap.pi fun z => (Submodule.mkQ _).comp (Submodule.inclusion (Submodule.span_mono
        (fun b hb => Set.mem_mul.mpr ⟨b, hb, 1, ⟨1, map_one _⟩, mul_one b⟩)))
    Function.Surjective φ ∧
      LinearMap.ker φ = (⨅ z : {z : X // P z}, Submodule.span k (Set.range (algebraMap (R z.1) K))).comap
        (Submodule.span k (B : Set K)).subtype ∧
      {z : {z : X // P z} | Nontrivial (Q z.1)}.Finite ∧
      ∀ z : {z : X // P z}, FiniteDimensional k (Q z.1) := by
  intro Bz Q φ
  classical
  have hle : ∀ z : X, Submodule.span k (B : Set K) ≤ Bz z := fun z =>
    Submodule.span_mono (fun b hb => Set.mem_mul.mpr ⟨b, hb, 1, ⟨1, map_one _⟩, mul_one b⟩)
  have hBz : ∀ z : {z : X // P z}, Bz z.1 = locBSub k (𝔪 z) B := fun z =>
    span_mul_range_eq_locBSub k (𝔪 z) B (R z.1)
  have hO : ∀ z : {z : X // P z}, Submodule.span k (Set.range (algebraMap (R z.1) K)) = locSub k (𝔪 z) :=
    fun z => span_range_eq_locSub k (𝔪 z) (R z.1)
  have hQeq : ∀ (z : {z : X // P z}) (x y : ↥(Bz z.1)),
      (Submodule.Quotient.mk x : Q z.1) = Submodule.Quotient.mk y ↔ (x : K) - y ∈ locSub k (𝔪 z) (K := K) := by
    intro z x y
    rw [Submodule.Quotient.eq, Submodule.mem_comap, ← hO z]
    rfl
  have hφ : ∀ (b : ↥(Submodule.span k (B : Set K))) (z : {z : X // P z}),
      φ b z = Submodule.Quotient.mk ⟨b, hle z.1 b.2⟩ := fun _ _ => rfl

  obtain ⟨d, hd0, hdB⟩ := exists_denominator B hB
  choose N hN using fun z : {z : X // P z} => exists_pow_forall_mul_mem hdim (𝔪 z) hd0
  have key : ∀ (z : {z : X // P z}) {x : A}, x ∈ 𝔪 z ^ N z → ∀ {b : K}, b ∈ B →
      algebraMap A K x * b ∈ locSub k (𝔪 z) (K := K) :=
    fun z x hx b hb => mul_mem_locSub_of k (𝔪 z) B hdB (hN z) hx hb

  have hT : {z : {z : X // P z} | d ∈ 𝔪 z}.Finite := by
    have hfin := (finite_setOf_isMaximal_mem hdim hd0).preimage (f := 𝔪) h𝔪.injOn
    exact hfin.subset fun z hz => ⟨inferInstance, hz⟩
  have htriv : ∀ z : {z : X // P z}, d ∉ 𝔪 z → ∀ x : ↥(Bz z.1), (x : K) ∈ locSub k (𝔪 z) (K := K) := by
    intro z hz x
    have hx : (x : K) ∈ locBSub k (𝔪 z) B := by rw [← hBz z]; exact x.2
    obtain ⟨b, hb, s, hs, e⟩ := hx
    obtain ⟨c, hc⟩ := hdB b hb
    refine ⟨c, d * s, fun h => ((inferInstance : (𝔪 z).IsMaximal).isPrime.mem_or_mem h).elim hz hs, ?_⟩
    have hd' : algebraMap A K d ≠ 0 := fun h => hd0 ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective A K) d h)
    rw [e, ← hc, map_mul, mul_inv, ← mul_assoc, mul_comm (algebraMap A K d) b, mul_assoc b, mul_inv_cancel₀ hd', mul_one]
  have hsub : ∀ z : {z : X // P z}, d ∉ 𝔪 z → Subsingleton (Q z.1) := by
    intro z hz
    refine ⟨fun x y => ?_⟩
    induction x using Submodule.Quotient.induction_on with | _ x =>
    induction y using Submodule.Quotient.induction_on with | _ y =>
    exact (hQeq z x y).mpr (sub_mem (htriv z hz x) (htriv z hz y))
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro y
    have hrep : ∀ z : {z : X // P z}, ∃ b : K, b ∈ B ∧ ∃ s : A, s ∉ 𝔪 z ∧
        ∃ x : ↥(Bz z.1), Submodule.Quotient.mk x = y z ∧ (x : K) = b * (algebraMap A K s)⁻¹ := by
      intro z
      obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (y z)
      have hx' : (x : K) ∈ locBSub k (𝔪 z) B := by rw [← hBz z]; exact x.2
      obtain ⟨b, hb, s, hs, e⟩ := hx'
      exact ⟨b, hb, s, hs, x, hx, e⟩
    choose bz hbz sz hsz xz hxz hxbs using hrep
    let T : Finset {z : X // P z} := hT.toFinset
    have hTmem : ∀ z, z ∈ T ↔ d ∈ 𝔪 z := fun z => by simp [T]

    have hcop : Pairwise (Function.onFun IsCoprime fun z : ↥T => 𝔪 z.1 ^ N z.1) := by
      intro z w hzw
      have hne : 𝔪 z.1 ≠ 𝔪 w.1 := fun h => hzw (Subtype.ext (h𝔪 h))
      exact (Ideal.isCoprime_iff_add.mpr (by
        rw [Ideal.add_eq_sup, Ideal.one_eq_top]
        exact (inferInstance : (𝔪 z.1).IsMaximal).coprime_of_ne inferInstance hne)).pow
    have he : ∀ z : ↥T, ∃ e : A, ∀ w : ↥T, e - (if w = z then 1 else 0) ∈ 𝔪 w.1 ^ N w.1 :=
      fun z => Ideal.exists_forall_sub_mem_ideal hcop _
    choose e he using he
    choose t ht using fun z : {z : X // P z} => exists_mul_sub_one_mem_pow (𝔪 z) (hsz z) (N z)

    let bsum : K := ∑ z : ↥T, algebraMap A K (e z * t z.1) * bz z.1
    have hbsumB : bsum ∈ B := B.sum_mem fun z _ => B.mul_mem (B.algebraMap_mem _) (hbz z.1)
    refine ⟨⟨bsum, Submodule.subset_span hbsumB⟩, funext fun w => ?_⟩
    rw [hφ, ← hxz w, hQeq]
    by_cases hw : d ∈ 𝔪 w
    · let w' : ↥T := ⟨w, (hTmem w).mpr hw⟩
      have hsplit : bsum - xz w = (∑ z ∈ Finset.univ.erase w', algebraMap A K (e z * t z.1) * bz z.1) +
          (algebraMap A K (e w' * t w * sz w - 1) * bz w * (algebraMap A K (sz w))⁻¹) := by
        have hs0 := algebraMap_ne_zero (K := K) (𝔪 w) (hsz w)
        show (∑ z : ↥T, algebraMap A K (e z * t z.1) * bz z.1) - _ = _
        rw [hxbs w, ← Finset.add_sum_erase _ _ (Finset.mem_univ w')]
        simp only [map_sub, map_mul, map_one]
        field_simp
        ring
      rw [hsplit]
      refine add_mem (Submodule.sum_mem _ fun z hz => ?_) ?_
      · have hzw : z ≠ w' := Finset.ne_of_mem_erase hz
        have hez : e z ∈ 𝔪 w ^ N w := by simpa [if_neg hzw.symm] using he z w'
        rw [map_mul, mul_assoc]
        exact key w hez (B.mul_mem (B.algebraMap_mem _) (hbz z.1))
      · refine mul_inv_mem_locSub k (𝔪 w) (key w ?_ (hbz w)) (hsz w)
        have h1 : e w' - 1 ∈ 𝔪 w ^ N w := by simpa using he w' w'
        have h2 := ht w
        have : e w' * t w * sz w - 1 = (e w' - 1) * (t w * sz w) + (t w * sz w - 1) := by ring
        rw [this]
        exact add_mem (Ideal.mul_mem_right _ _ h1) h2
    · exact sub_mem (htriv w hw ⟨bsum, hle w.1 (Submodule.subset_span hbsumB)⟩) (htriv w hw (xz w))
  ·
    ext b
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.mem_iInf, funext_iff]
    refine forall_congr' fun z => ?_
    rw [Pi.zero_apply, hφ, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    rfl
  ·
    refine hT.subset fun z hz => ?_
    by_contra h
    exact (not_nontrivial_iff_subsingleton.mpr (hsub z h)) hz
  ·
    intro z
    obtain ⟨S, hS⟩ := hB.fg_top

    let Λ : (↥S → A) →ₗ[k] K :=
      ∑ i : ↥S, ((LinearMap.mulRight k ((i : ↥B) : K)).comp ((Algebra.linearMap A K).restrictScalars k)).comp
        (LinearMap.proj i)
    have hΛ : ∀ g : ↥S → A, Λ g = ∑ i : ↥S, algebraMap A K (g i) * ((i : ↥B) : K) := by
      intro g
      simp [Λ, LinearMap.sum_apply]
    have hΛB : ∀ g : ↥S → A, Λ g ∈ B := fun g => by
      rw [hΛ]; exact B.sum_mem fun i _ => B.mul_mem (B.algebraMap_mem _) (i : ↥B).2
    let f : (↥S → A) →ₗ[k] Q z.1 :=
      ((LinearMap.proj z).comp φ).comp (Λ.codRestrict (Submodule.span k (B : Set K)) fun g =>
        Submodule.subset_span (hΛB g))
    have hf : ∀ g : ↥S → A, f g = Submodule.Quotient.mk ⟨Λ g, hle z.1 (Submodule.subset_span (hΛB g))⟩ :=
      fun g => rfl
    refine finite_of_surjective_of_smul_pow_le (𝔪 z) (hres _ inferInstance) (N z) f ?_ ?_
    ·
      intro q
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      have hx : (x : K) ∈ locBSub k (𝔪 z) B := by rw [← hBz z]; exact x.2
      obtain ⟨b, hb, s, hs, e⟩ := hx
      obtain ⟨t, ht⟩ := exists_mul_sub_one_mem_pow (𝔪 z) hs (N z)

      have hrange : Set.range (fun i : ↥S => (i : ↥B)) = (S : Set ↥B) := by ext; simp
      have hsurj := (span_range_eq_top_iff_surjective_fintypeLinearCombination (R := A)
        (v := fun i : ↥S => (i : ↥B))).mp (by rw [hrange]; exact hS)
      obtain ⟨g, hg⟩ := hsurj ⟨b, hb⟩
      have hgb : Λ g = b := by
        have := congrArg Subtype.val hg
        simp only [Fintype.linearCombination_apply, AddSubmonoidClass.coe_finsetSum, Algebra.smul_def] at this
        rw [hΛ]
        exact this
      refine ⟨fun i => t * g i, ?_⟩
      rw [hf, hQeq]
      have hΛt : Λ (fun i => t * g i) = algebraMap A K t * b := by
        rw [← hgb, hΛ, hΛ, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, mul_assoc]
      show Λ (fun i => t * g i) - (x : K) ∈ _
      rw [hΛt, e]
      have hs0 := algebraMap_ne_zero (K := K) (𝔪 z) hs
      have : algebraMap A K t * b - b * (algebraMap A K s)⁻¹ =
          algebraMap A K (t * s - 1) * b * (algebraMap A K s)⁻¹ := by
        simp only [map_sub, map_mul, map_one]
        field_simp
        try ring
      rw [this]
      exact mul_inv_mem_locSub k (𝔪 z) (key z ht hb) hs
    ·
      intro g hg
      rw [hf, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, hO z]
      show Λ g ∈ locSub k (𝔪 z)
      rw [hΛ]
      exact Submodule.sum_mem _ fun i _ => key z (hg i) (i : ↥B).2

#print axioms solution

end S_IsLocalization_AtPrime_surjective_and_ker_pi_span_mul_quotient_of_moduleFinite
end P2MW
export P2MW.S_IsLocalization_AtPrime_surjective_and_ker_pi_span_mul_quotient_of_moduleFinite (solution)
