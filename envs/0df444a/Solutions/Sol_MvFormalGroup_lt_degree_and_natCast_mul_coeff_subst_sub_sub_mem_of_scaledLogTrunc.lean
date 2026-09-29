-- Prove2me | solution 1 for MvFormalGroup.lt_degree_and_natCast_mul_coeff_subst_sub_sub_mem_of_scaledLogTrunc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/10ee2f1e-247e-5fa3-b9f5-458243a760f8

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Theorems.Thm_MvPowerSeries_coeff_sumElim_single_subst_add_sum_X_mul_eq
import Theorems.Thm_MvPowerSeries_coeff_sumElim_zero_subst_add_sum_X_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_lt_degree_and_natCast_mul_coeff_subst_sub_sub_mem_of_scaledLogTrunc

set_option autoImplicit false

universe u

namespace S17D3

open MvPowerSeries

section Rescale

variable {𝓞 : Type*} [CommRing 𝓞] {σ : Type*}

noncomputable def rho (p : ℕ) : MvPowerSeries σ 𝓞 →+* MvPowerSeries σ 𝓞 := rescale (fun _ => (p : 𝓞))

theorem coeff_rho (p : ℕ) (f : MvPowerSeries σ 𝓞) (m : σ →₀ ℕ) :
    coeff m (rho p f) = (p : 𝓞) ^ m.degree * coeff m f := by
  rw [rho, coeff_rescale]
  congr 1
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree]
  rfl

theorem rho_natCast (p n : ℕ) : rho (σ := σ) (𝓞 := 𝓞) p (n : MvPowerSeries σ 𝓞) = n := map_natCast _ n

theorem rho_eq_subst (p : ℕ) (f : MvPowerSeries σ 𝓞) :
    rho p f = subst ((fun _ : σ => (p : 𝓞)) • (X : σ → MvPowerSeries σ 𝓞)) f :=
  rescale_eq_subst _ f

theorem rho_X (p : ℕ) (s : σ) : rho (𝓞 := 𝓞) p (X s) = (p : 𝓞) • X s := by
  rw [rho_eq_subst, subst_X (HasSubst.smul_X _)]
  rfl

theorem rho_subst (p : ℕ) {τ : Type*} {a : τ → MvPowerSeries σ 𝓞} (ha : HasSubst a) (f : MvPowerSeries τ 𝓞) :
    rho p (subst a f) = subst (fun t => rho p (a t)) f := by
  rw [rho_eq_subst, subst_comp_subst_apply ha (HasSubst.smul_X _)]
  congr 1
  funext t
  rw [rho_eq_subst]

theorem subst_smul_family (p : ℕ) {τ : Type*} {a : σ → MvPowerSeries τ 𝓞} (ha : HasSubst a) (f : MvPowerSeries σ 𝓞) :
    subst (fun s => (p : 𝓞) • a s) f = subst a (rho p f) := by
  rw [rho_eq_subst, subst_comp_subst_apply (HasSubst.smul_X _) ha]
  congr 1
  funext s
  show (p : 𝓞) • a s = subst a (((fun _ : σ => (p : 𝓞)) • (X : σ → MvPowerSeries σ 𝓞)) s)
  rw [Pi.smul_apply', subst_smul ha, subst_X ha]

theorem coeff_eq_zero_of_coeff_rho {p : ℕ} (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) {f : MvPowerSeries σ 𝓞}
    {m : σ →₀ ℕ} (h : coeff m (rho p f) = 0) : coeff m f = 0 := by
  rw [coeff_rho] at h
  exact (mem_nonZeroDivisors_iff.1 (pow_mem hp m.degree)).1 _ h

theorem subst_zero_family {τ : Type*} (f : MvPowerSeries σ 𝓞) :
    subst (fun _ : σ => (0 : MvPowerSeries τ 𝓞)) f = C (constantCoeff f) := by
  classical
  ext e
  rw [coeff_subst HasSubst.zero, finsum_eq_single _ (0 : σ →₀ ℕ)]
  · rw [Finsupp.prod_zero_index, coeff_zero_eq_constantCoeff, smul_eq_mul, coeff_one, coeff_C]
    split_ifs <;> simp
  · intro d hd
    obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.2 hd
    rw [Finsupp.prod, Finset.prod_eq_zero hs (by rw [zero_pow (Finsupp.mem_support_iff.1 hs)]),
      map_zero, smul_zero]

end Rescale

section Law
variable {𝓞 : Type*} [CommRing 𝓞] {p : ℕ} {d : ℕ}
  (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞) (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
  (F : MvFormalGroup d 𝓞)
  (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
    (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
include hFp hFp0 in
theorem rho_law (i : Fin d) : rho p (F.toPowerSeries i) = (p : 𝓞) • Fp i := by
  ext m
  rw [coeff_rho, map_smul, smul_eq_mul]
  by_cases hm : m = 0
  · subst hm
    simp only [coeff_zero_eq_constantCoeff, F.constantCoeff_eq_zero, hFp0, mul_zero]
  · rw [← hFp i m hm, mul_comm]
end Law

section Arith

variable {𝓞 : Type*} [CommRing 𝓞] {p : ℕ} [hp : Fact p.Prime] {d : ℕ}

omit hp in
theorem mem_span_pow_of_pow_mul_mem (hpR : (p : 𝓞) ∈ nonZeroDivisors 𝓞) {a : 𝓞} {K e : ℕ} (hKe : K ≤ e)
    (h : (p : 𝓞) ^ K * a ∈ Ideal.span {(p : 𝓞) ^ e}) : a ∈ Ideal.span {(p : 𝓞) ^ (e - K)} := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h
  refine Ideal.mem_span_singleton'.2 ⟨b, ?_⟩
  have h0 : (p : 𝓞) ^ K * (b * (p : 𝓞) ^ (e - K) - a) = 0 := by
    rw [mul_sub, sub_eq_zero, ← hb, mul_comm ((p : 𝓞) ^ K), mul_assoc, ← pow_add, Nat.sub_add_cancel hKe]
  exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 (pow_mem hpR K)).1 _ h0)

theorem mem_span_pow_of_natCast_mul_mem {u : ℕ} (hu : ¬ p ∣ u) {a : 𝓞} {e : ℕ}
    (h : (u : 𝓞) * a ∈ Ideal.span {(p : 𝓞) ^ e}) : a ∈ Ideal.span {(p : 𝓞) ^ e} := by
  have hcop : IsCoprime (u : ℤ) ((p : ℤ) ^ e) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hu).symm)
  obtain ⟨x, y, hxy⟩ := hcop
  have h1 : ((x : 𝓞) * (u : 𝓞) + (y : 𝓞) * (p : 𝓞) ^ e) = 1 := by
    have := congrArg (Int.castRingHom 𝓞) hxy
    simpa using this
  have : a = (x : 𝓞) * ((u : 𝓞) * a) + (p : 𝓞) ^ e * ((y : 𝓞) * a) := by
    calc a = ((x : 𝓞) * (u : 𝓞) + (y : 𝓞) * (p : 𝓞) ^ e) * a := by rw [h1, one_mul]
      _ = _ := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

omit hp in
theorem natCast_mul_coeff_mem (φi : MvPowerSeries (Fin d) 𝓞)
    (hint : ∀ (j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * coeff (m + Finsupp.single j 1) φi ∈ Ideal.span {(p : 𝓞) ^ m.degree})
    (M' : Fin d →₀ ℕ) (i : Fin d) (hi : 1 ≤ M' i) :
    ((M' i : ℕ) : 𝓞) * coeff M' φi ∈ Ideal.span {(p : 𝓞) ^ (M'.degree - 1)} := by
  have hle : Finsupp.single i 1 ≤ M' := Finsupp.single_le_iff.2 hi
  set m := M' - Finsupp.single i 1 with hm
  have hM : m + Finsupp.single i 1 = M' := tsub_add_cancel_of_le hle
  have h1 : m i + 1 = M' i := by
    conv_rhs => rw [← hM]
    simp
  have h2 : m.degree = M'.degree - 1 := by
    conv_rhs => rw [← hM]
    rw [map_add, Finsupp.degree_single]
    simp
  have := hint i m
  rwa [h1, hM, h2] at this

theorem pow_degree_mul_coeff_eq (hpR : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (φi : MvPowerSeries (Fin d) 𝓞)
    (hint : ∀ (j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * coeff (m + Finsupp.single j 1) φi ∈ Ideal.span {(p : 𝓞) ^ m.degree})
    (N : ℕ) (G : MvPowerSeries (Fin d) 𝓞)
    (hG : ∀ m : Fin d →₀ ℕ,
      (m.degree ≤ N → G.coeff m = (p : 𝓞) ^ (N - m.degree) * φi.coeff m) ∧
      (N < m.degree → G.coeff m * (p : 𝓞) ^ (m.degree - N) = φi.coeff m ∨
        (G.coeff m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ φi.coeff m)))
    (m : Fin d →₀ ℕ) (hm : m.degree < p ^ N) :
    (p : 𝓞) ^ m.degree * coeff m G = (p : 𝓞) ^ N * coeff m φi := by
  rcases le_or_gt m.degree N with hle | hlt
  · rw [show coeff m G = G.coeff m from rfl, (hG m).1 hle, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]
  ·
    have hdiv : (p : 𝓞) ^ (m.degree - N) ∣ coeff m φi := by
      have hm0 : m ≠ 0 := by rintro rfl; simp at hlt
      obtain ⟨j, hj⟩ : ∃ j, m j ≠ 0 := by
        by_contra h
        exact hm0 (Finsupp.ext fun j => not_not.1 (not_exists.1 h j))
      obtain ⟨k, u, hu, hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd hj p hp.out.ne_one
      have hu0 : u ≠ 0 := fun h => hj (by rw [hk, h, mul_zero])
      have hkj : p ^ k ≤ m j := by rw [hk]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hu0)
      have hjdeg : m j ≤ m.degree := Finsupp.le_degree j m
      have hkN : k < N := (Nat.pow_lt_pow_iff_right hp.out.one_lt).1 (lt_of_le_of_lt (hkj.trans hjdeg) hm)
      have hkdeg : k < m.degree := lt_of_lt_of_le (Nat.lt_pow_self hp.out.one_lt) (hkj.trans hjdeg)
      have hA := natCast_mul_coeff_mem φi hint m j (Nat.one_le_iff_ne_zero.2 hj)
      rw [hk, Nat.cast_mul, Nat.cast_pow, mul_comm ((p : 𝓞) ^ k) (u : 𝓞), mul_assoc] at hA
      have hB := mem_span_pow_of_pow_mul_mem hpR (by omega) (mem_span_pow_of_natCast_mul_mem hu hA)
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hB
      refine ⟨(p : 𝓞) ^ (m.degree - 1 - k - (m.degree - N)) * b, ?_⟩
      rw [← hb, mul_comm b, ← mul_assoc, ← pow_add, show m.degree - N + (m.degree - 1 - k - (m.degree - N)) =
        m.degree - 1 - k by omega]
    rcases (hG m).2 hlt with h | ⟨-, h⟩
    · obtain ⟨t, ht⟩ : ∃ t, m.degree = N + t := ⟨m.degree - N, by omega⟩
      rw [show coeff m φi = φi.coeff m from rfl, ← h, show G.coeff m = coeff m G from rfl, ht,
        Nat.add_sub_cancel_left, pow_add]
      ring
    · exact absurd hdiv h

end Arith

section Embed

variable {𝓞 : Type*} [CommRing 𝓞] {α β : Type*} [Finite α]

theorem hasSubst_X_comp (e : α → β) : HasSubst (fun a => (X (e a) : MvPowerSeries β 𝓞)) :=
  hasSubst_of_constantCoeff_zero (fun a => constantCoeff_X _)

omit [Finite α] in
theorem prod_X_comp_pow_eq_monomial (e : α → β) (d : α →₀ ℕ) :
    (d.prod fun a n => (X (e a) : MvPowerSeries β 𝓞) ^ n) = monomial (d.mapDomain e) 1 := by
  rw [MvPowerSeries.monomial_one_eq, Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]

theorem coeff_mapDomain_subst_X_comp {e : α → β} (he : Function.Injective e) (f : MvPowerSeries α 𝓞) (d : α →₀ ℕ) :
    coeff (d.mapDomain e) (subst (fun a => (X (e a) : MvPowerSeries β 𝓞)) f) = coeff d f := by
  classical
  rw [coeff_subst (hasSubst_X_comp e), finsum_eq_single _ d]
  · rw [prod_X_comp_pow_eq_monomial, coeff_monomial, if_pos rfl, smul_eq_mul, mul_one]
  · intro d' hd'
    rw [prod_X_comp_pow_eq_monomial, coeff_monomial, if_neg, smul_zero]
    exact fun h => hd' (Finsupp.mapDomain_injective he h).symm

theorem coeff_subst_X_comp_eq_zero (e : α → β) (f : MvPowerSeries α 𝓞) (μ : β →₀ ℕ)
    (hμ : ∀ d : α →₀ ℕ, d.mapDomain e ≠ μ) :
    coeff μ (subst (fun a => (X (e a) : MvPowerSeries β 𝓞)) f) = 0 := by
  classical
  rw [coeff_subst (hasSubst_X_comp e)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d'
  rw [prod_X_comp_pow_eq_monomial, coeff_monomial, if_neg (fun h => hμ d' h.symm), smul_zero]

end Embed

section Chain

variable {R : Type*} [CommRing R]

noncomputable def Dser {σ : Type*} (f : MvPowerSeries σ R) (s : σ) : MvPowerSeries σ R :=
  fun m => ((m s + 1 : ℕ) : R) * coeff (m + Finsupp.single s 1) f

theorem coeff_Dser {σ : Type*} (f : MvPowerSeries σ R) (s : σ) (m : σ →₀ ℕ) :
    coeff m (Dser f s) = ((m s + 1 : ℕ) : R) * coeff (m + Finsupp.single s 1) f := rfl

theorem exists_eq_C_mul_of_forall_coeff_mem {σ : Type*} (f : MvPowerSeries σ R) (c : R)
    (h : ∀ m, coeff m f ∈ Ideal.span {c}) : ∃ q : MvPowerSeries σ R, f = C c * q := by
  choose q hq using fun m => Ideal.mem_span_singleton'.1 (h m)
  refine ⟨fun m => q m, ?_⟩
  ext m
  rw [coeff_C_mul, mul_comm]
  exact (hq m).symm

variable {τ : Type*} [Fintype τ] [DecidableEq τ]

noncomputable def delta (s k : τ) : MvPowerSeries τ R := if s = k then 1 else 0

omit [Fintype τ] [DecidableEq τ] in
theorem subst_one_eq {σ υ : Type*} {a : σ → MvPowerSeries υ R} (ha : HasSubst a) :
    subst a (1 : MvPowerSeries σ R) = 1 := by
  simpa [substAlgHom_apply] using map_one (substAlgHom ha)

omit [Fintype τ] [DecidableEq τ] in
theorem subst_zero_eq {σ υ : Type*} {a : σ → MvPowerSeries υ R} (ha : HasSubst a) :
    subst a (0 : MvPowerSeries σ R) = 0 := by
  simpa [substAlgHom_apply] using map_zero (substAlgHom ha)

omit [DecidableEq τ] in
theorem hasSubst_Xinl' : HasSubst (fun t : τ => (X (Sum.inl t) : MvPowerSeries (τ ⊕ τ) R)) :=
  hasSubst_of_constantCoeff_zero (fun t => constantCoeff_X _)

omit [DecidableEq τ] in
theorem hasSubst_Xplus : HasSubst (fun t : τ => (X (Sum.inl t) + X (Sum.inr t) : MvPowerSeries (τ ⊕ τ) R)) :=
  hasSubst_of_constantCoeff_zero (fun t => by rw [map_add, constantCoeff_X, constantCoeff_X, add_zero])

theorem gfam_X_delta (s : τ) :
    subst (fun t => (X (Sum.inl t) : MvPowerSeries (τ ⊕ τ) R)) (X s : MvPowerSeries τ R) +
      ∑ k' : τ, X (Sum.inr k') * subst (fun t => (X (Sum.inl t) : MvPowerSeries (τ ⊕ τ) R)) (delta s k' : MvPowerSeries τ R) =
    X (Sum.inl s) + X (Sum.inr s) := by
  rw [subst_X hasSubst_Xinl']
  congr 1
  rw [Finset.sum_eq_single s]
  · rw [delta, if_pos rfl, subst_one_eq hasSubst_Xinl', mul_one]
  · intro k' _ hk'
    rw [delta, if_neg (fun h => hk' h.symm), subst_zero_eq hasSubst_Xinl', mul_zero]
  · intro hs; exact absurd (Finset.mem_univ s) hs

theorem natCast_succ_mul_coeff_eq_coeff_shift (H : MvPowerSeries τ R) (ν : τ →₀ ℕ) (t : τ) :
    ((ν t + 1 : ℕ) : R) * coeff (ν + Finsupp.single t 1) H =
      coeff (ν.sumElim (Finsupp.single t 1))
        (subst (fun s => (X (Sum.inl s) + X (Sum.inr s) : MvPowerSeries (τ ⊕ τ) R)) H) := by
  have h := MvPowerSeries.coeff_sumElim_single_subst_add_sum_X_mul_eq (R := R) (σ := τ) (τ := τ) (κ := τ)
    H (Dser H) (fun s m => coeff_Dser H s m) (fun s => X s) (fun s => constantCoeff_X s) delta ν t
  rw [show (fun i => subst (fun t => (X (Sum.inl t) : MvPowerSeries (τ ⊕ τ) R)) (X i : MvPowerSeries τ R) +
      ∑ k' : τ, X (Sum.inr k') * subst (fun t => (X (Sum.inl t) : MvPowerSeries (τ ⊕ τ) R)) (delta i k' : MvPowerSeries τ R)) =
      (fun s => (X (Sum.inl s) + X (Sum.inr s) : MvPowerSeries (τ ⊕ τ) R)) from funext gfam_X_delta] at h
  rw [h, Finset.sum_eq_single t, delta, if_pos rfl, one_mul,
    show subst (fun s => (X s : MvPowerSeries τ R)) (Dser H t) = Dser H t from congrFun subst_self _, coeff_Dser]
  · intro s _ hs; rw [delta, if_neg hs, zero_mul]
  · intro ht; exact absurd (Finset.mem_univ t) ht

noncomputable def Ydeg (μ : (τ ⊕ τ) →₀ ℕ) : ℕ := (μ.comapDomain Sum.inr Sum.inr_injective.injOn).degree

omit [Fintype τ] [DecidableEq τ] in
theorem Ydeg_sumElim (m c : τ →₀ ℕ) : Ydeg (m.sumElim c) = c.degree := by
  rw [Ydeg]
  congr 1
  ext k
  rw [Finsupp.comapDomain_apply, Finsupp.sumElim_inr]

omit [Fintype τ] [DecidableEq τ] in

theorem Ydeg_add (a b : (τ ⊕ τ) →₀ ℕ) : Ydeg (a + b) = Ydeg a + Ydeg b := by
  simp only [Ydeg]
  rw [← map_add]
  congr 1
  ext k
  simp [Finsupp.comapDomain_apply]

def Agree (x x' : MvPowerSeries (τ ⊕ τ) R) : Prop := ∀ μ', Ydeg μ' ≤ 1 → coeff μ' x = coeff μ' x'

omit [Fintype τ] [DecidableEq τ] in
theorem Agree.rfl' (x : MvPowerSeries (τ ⊕ τ) R) : Agree x x := fun _ _ => rfl

omit [Fintype τ] [DecidableEq τ] in
theorem Agree.mul {x x' y y' : MvPowerSeries (τ ⊕ τ) R} (hx : Agree x x') (hy : Agree y y') :
    Agree (x * y) (x' * y') := by
  classical
  intro μ' hμ'
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq' : q.1 + q.2 = μ' := Finset.HasAntidiagonal.mem_antidiagonal.1 hq
  have hs := Ydeg_add q.1 q.2
  rw [hq'] at hs
  rw [hx _ (by omega), hy _ (by omega)]

omit [Fintype τ] [DecidableEq τ] in
theorem Agree.pow {x x' : MvPowerSeries (τ ⊕ τ) R} (hx : Agree x x') (n : ℕ) : Agree (x ^ n) (x' ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact Agree.rfl' _
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hx

omit [Fintype τ] [DecidableEq τ] in
theorem Agree.finsuppProd {σ : Type*} {a a' : σ → MvPowerSeries (τ ⊕ τ) R} (h : ∀ s, Agree (a s) (a' s))
    (d : σ →₀ ℕ) : Agree (d.prod fun s n => a s ^ n) (d.prod fun s n => a' s ^ n) := by
  classical
  unfold Finsupp.prod
  induction d.support using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty]; exact Agree.rfl' _
  | insert s S hs ih => rw [Finset.prod_insert hs, Finset.prod_insert hs]; exact ((h s).pow _).mul ih

omit [Fintype τ] [DecidableEq τ] in

theorem coeff_subst_congr_Ylow {σ : Type*} [Finite σ] {a a' : σ → MvPowerSeries (τ ⊕ τ) R}
    (ha : HasSubst a) (ha' : HasSubst a')
    (hcong : ∀ (j : σ) (μ' : (τ ⊕ τ) →₀ ℕ), Ydeg μ' ≤ 1 → coeff μ' (a j) = coeff μ' (a' j))
    (f : MvPowerSeries σ R) (μ' : (τ ⊕ τ) →₀ ℕ) (hμ' : Ydeg μ' ≤ 1) :
    coeff μ' (subst a f) = coeff μ' (subst a' f) := by
  rw [coeff_subst ha, coeff_subst ha']
  exact finsum_congr fun d' => by rw [Agree.finsuppProd (fun s μ'' h'' => hcong s μ'' h'') d' μ' hμ']

omit [Fintype τ] [DecidableEq τ] in
theorem sumElim_zero_eq_mapDomain (m : τ →₀ ℕ) : m.sumElim (0 : τ →₀ ℕ) = m.mapDomain Sum.inl := by
  ext x
  rcases x with j | k
  · rw [Finsupp.sumElim_inl, Finsupp.mapDomain_apply Sum.inl_injective]
  · rw [Finsupp.sumElim_inr, Finsupp.mapDomain_notin_range _ _ (by rintro ⟨j, hj⟩; cases hj),
      Finsupp.zero_apply]

omit [Fintype τ] [DecidableEq τ] in
theorem degree_le_one_cases (c : τ →₀ ℕ) (hc : c.degree ≤ 1) : c = 0 ∨ ∃ k, c = Finsupp.single k 1 := by
  by_cases h0 : c = 0
  · exact Or.inl h0
  right
  obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.2 h0
  have hk1 : 1 ≤ c k := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hk)
  have hle : Finsupp.single k 1 ≤ c := Finsupp.single_le_iff.2 hk1
  refine ⟨k, ?_⟩
  have hsplit : c = Finsupp.single k 1 + (c - Finsupp.single k 1) := (add_tsub_cancel_of_le hle).symm
  have hdeg : (c - Finsupp.single k 1).degree = 0 := by
    have := congrArg Finsupp.degree hsplit
    rw [map_add, Finsupp.degree_single] at this
    omega
  rw [(Finsupp.degree_eq_zero_iff _).1 hdeg, add_zero] at hsplit
  exact hsplit

omit [Fintype τ] [DecidableEq τ] in
theorem X_eq_monomial' (x : τ ⊕ τ) : (X x : MvPowerSeries (τ ⊕ τ) R) = monomial (Finsupp.single x 1) 1 := rfl

omit [Fintype τ] [DecidableEq τ] in
theorem sumElim_single_sub (m : τ →₀ ℕ) (k : τ) :
    m.sumElim (Finsupp.single k 1) - Finsupp.single (Sum.inr k) 1 = m.sumElim (0 : τ →₀ ℕ) := by
  classical
  ext x
  rcases x with j | k'
  · simp [Finsupp.sumElim_inl]
  · simp [Finsupp.sumElim_inr, Finsupp.single_apply]

theorem coeff_shift_eq_coeff_gfam (f : MvPowerSeries τ R) (μ' : (τ ⊕ τ) →₀ ℕ) (hμ' : Ydeg μ' ≤ 1) :
    coeff μ' (subst (fun s => (X (Sum.inl s) + X (Sum.inr s) : MvPowerSeries (τ ⊕ τ) R)) f) =
      coeff μ' (subst (fun t => (X (Sum.inl t) : MvPowerSeries (τ ⊕ τ) R)) f +
        ∑ k' : τ, X (Sum.inr k') * subst (fun t => (X (Sum.inl t) : MvPowerSeries (τ ⊕ τ) R)) (Dser f k')) := by
  classical
  rw [show (fun s => (X (Sum.inl s) + X (Sum.inr s) : MvPowerSeries (τ ⊕ τ) R)) =
      (fun i => subst (fun t => (X (Sum.inl t) : MvPowerSeries (τ ⊕ τ) R)) (X i : MvPowerSeries τ R) +
        ∑ k' : τ, X (Sum.inr k') * subst (fun t => (X (Sum.inl t) : MvPowerSeries (τ ⊕ τ) R)) (delta i k'))
      from (funext gfam_X_delta).symm]
  obtain ⟨m, c, rfl⟩ : ∃ m c : τ →₀ ℕ, m.sumElim c = μ' :=
    ⟨_, _, Finsupp.comapDomain_sumElim_comapDomain μ'⟩
  rw [Ydeg_sumElim] at hμ'
  rcases degree_le_one_cases c hμ' with rfl | ⟨k, rfl⟩
  ·
    rw [MvPowerSeries.coeff_sumElim_zero_subst_add_sum_X_mul_eq f (fun s => (X s : MvPowerSeries τ R))
        (fun s => constantCoeff_X s) delta m,
      show subst (fun s => (X s : MvPowerSeries τ R)) f = f from congrFun subst_self _,
      map_add, map_sum, sumElim_zero_eq_mapDomain, coeff_mapDomain_subst_X_comp Sum.inl_injective]
    convert (add_zero (coeff m f)).symm
    refine Finset.sum_eq_zero fun k' _ => ?_
    rw [X_eq_monomial', coeff_monomial_mul, if_neg]
    rw [Finsupp.single_le_iff, Finsupp.mapDomain_notin_range _ _ (by rintro ⟨j, hj⟩; cases hj)]
    omega
  ·
    rw [MvPowerSeries.coeff_sumElim_single_subst_add_sum_X_mul_eq f (Dser f) (fun s m => coeff_Dser f s m)
        (fun s => (X s : MvPowerSeries τ R)) (fun s => constantCoeff_X s) delta m k,
      map_add, map_sum]
    rw [Finset.sum_eq_single k (fun s _ hs => by rw [delta, if_neg hs, zero_mul, map_zero])
        (fun hk => absurd (Finset.mem_univ k) hk),
      delta, if_pos rfl, one_mul,
      show subst (fun s => (X s : MvPowerSeries τ R)) (Dser f k) = Dser f k from congrFun subst_self _]
    have hne : ∀ d : τ →₀ ℕ, d.mapDomain Sum.inl ≠ m.sumElim (Finsupp.single k 1) := by
      intro d hd
      have := congrArg (fun g => g (Sum.inr k)) hd
      simp only [Finsupp.mapDomain_notin_range _ _ (show Sum.inr k ∉ Set.range (Sum.inl : τ → τ ⊕ τ) by
        rintro ⟨j, hj⟩; cases hj), Finsupp.sumElim_inr, Finsupp.single_eq_same] at this
      exact absurd this (by norm_num)
    rw [coeff_subst_X_comp_eq_zero Sum.inl f _ hne, zero_add, map_sum, Finset.sum_eq_single k]
    · rw [X_eq_monomial', coeff_monomial_mul, if_pos, one_mul, sumElim_single_sub, sumElim_zero_eq_mapDomain,
        coeff_mapDomain_subst_X_comp Sum.inl_injective]
      rw [Finsupp.single_le_iff, Finsupp.sumElim_inr, Finsupp.single_eq_same]
    · intro k' _ hk'
      rw [X_eq_monomial', coeff_monomial_mul, if_neg]
      rw [Finsupp.single_le_iff, Finsupp.sumElim_inr, Finsupp.single_apply, if_neg (fun h => hk' h.symm)]
      omega
    · intro hk; exact absurd (Finset.mem_univ k) hk

end Chain

section Defect

variable {𝓞 : Type*} [CommRing 𝓞] {p : ℕ} [hp : Fact p.Prime] {d : ℕ}
  (hpR : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (F : MvFormalGroup d 𝓞)
  (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
  (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
    (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
  (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
  (φ : Fin d → MvPowerSeries (Fin d) 𝓞) (hφ0 : ∀ i, (φ i).constantCoeff = 0)
  (hφF : ∀ i, subst Fp (φ i) =
    subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
      subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
  (hint : ∀ (i j : Fin d) (m : Fin d →₀ ℕ),
    ((m j + 1 : ℕ) : 𝓞) * coeff (m + Finsupp.single j 1) (φ i) ∈ Ideal.span {(p : 𝓞) ^ m.degree})
  (M : ℕ) (hM : 1 ≤ M) (i : Fin d) (G : MvPowerSeries (Fin d) 𝓞)
  (hG : ∀ m : Fin d →₀ ℕ,
    (m.degree ≤ M → G.coeff m = (p : 𝓞) ^ (M - m.degree) * (φ i).coeff m) ∧
    (M < m.degree → G.coeff m * (p : 𝓞) ^ (m.degree - M) = (φ i).coeff m ∨
      (G.coeff m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - M) ∣ (φ i).coeff m)))

include hpR hFp hFp0 hφF hint hG in

theorem coeff_defect_eq_zero (μ : (Fin d ⊕ Fin d) →₀ ℕ) (hμ : μ.degree < p ^ M) :
    coeff μ (subst F.toPowerSeries G
      - subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G
      - subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G) = 0 := by
  apply coeff_eq_zero_of_coeff_rho (p := p) hpR
  set T : MvPowerSeries (Fin d) 𝓞 := (p : 𝓞) ^ M • φ i - rho p G with hT
  have hTcoeff : ∀ m' : Fin d →₀ ℕ, m'.degree < p ^ M → coeff m' T = 0 := by
    intro m' hm'
    rw [hT, map_sub, map_smul, smul_eq_mul, coeff_rho, pow_degree_mul_coeff_eq hpR (φ i) (hint i) M G hG m' hm',
      sub_self]
  have hTord : ((p ^ M : ℕ) : ℕ∞) ≤ T.order :=
    nat_le_order fun m' hm' => hTcoeff m' (by exact_mod_cast hm')
  have hFs : HasSubst F.toPowerSeries := F.hasSubst_toPowerSeries
  have hFps : HasSubst Fp := hasSubst_of_constantCoeff_zero hFp0
  have hinl : HasSubst (fun j : Fin d => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) :=
    hasSubst_of_constantCoeff_zero (fun j => constantCoeff_X _)
  have hinr : HasSubst (fun j : Fin d => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) :=
    hasSubst_of_constantCoeff_zero (fun j => constantCoeff_X _)
  have h1 : rho p (subst F.toPowerSeries G) = subst Fp (rho p G) := by
    rw [rho_subst p hFs, show (fun t => rho p (F.toPowerSeries t)) = fun t => (p : 𝓞) • Fp t from
      funext fun t => rho_law Fp hFp0 F hFp t, subst_smul_family p hFps G]
  have h2 : rho p (subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (rho p G) := by
    rw [rho_subst p hinl, show (fun t => rho p (X (Sum.inl t) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) =
      fun t => (p : 𝓞) • (X (Sum.inl t) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞) from funext fun t => rho_X p _,
      subst_smul_family p hinl G]
  have h3 : rho p (subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G) =
      subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (rho p G) := by
    rw [rho_subst p hinr, show (fun t => rho p (X (Sum.inr t) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) =
      fun t => (p : 𝓞) • (X (Sum.inr t) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞) from funext fun t => rho_X p _,
      subst_smul_family p hinr G]
  have hρG : rho p G = (p : 𝓞) ^ M • φ i - T := by rw [hT, sub_sub_cancel]
  have key : rho p (subst F.toPowerSeries G
      - subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G
      - subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G) =
      - subst Fp T + subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) T
        + subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) T := by
    rw [map_sub, map_sub, h1, h2, h3, hρG, subst_sub hFps, subst_sub hinl, subst_sub hinr,
      subst_smul hFps, subst_smul hinl, subst_smul hinr, hφF i, smul_add]
    abel
  have hz : ∀ {a : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞} (ha : HasSubst a)
      (ha0 : ∀ j, (a j).constantCoeff = 0), coeff μ (subst a T) = 0 := by
    intro a ha ha0
    apply coeff_of_lt_order
    have hinf : (1 : ℕ∞) ≤ ⨅ j, (a j).order := by
      refine le_iInf fun j => nat_le_order fun m' hm' => ?_
      have : m' = 0 := (Finsupp.degree_eq_zero_iff m').1 (by exact_mod_cast Nat.lt_one_iff.1 (by exact_mod_cast hm'))
      rw [this, coeff_zero_eq_constantCoeff_apply, ha0]
    calc ((μ.degree : ℕ) : ℕ∞) < (p ^ M : ℕ) := by exact_mod_cast hμ
      _ ≤ T.order := hTord
      _ ≤ (⨅ j, (a j).order) * T.order := le_mul_of_one_le_left (by simp) hinf
      _ ≤ (T.subst a).order := le_order_subst ha T
  rw [key, map_add, map_add, map_neg, hz hFps hFp0, hz hinl (fun j => constantCoeff_X _),
    hz hinr (fun j => constantCoeff_X _), neg_zero, add_zero, add_zero]

omit hp in
include hpR hint hM hG in

theorem natCast_mul_coeff_trunc_mem (m : Fin d →₀ ℕ) (j : Fin d) :
    ((m j : ℕ) : 𝓞) * coeff m G ∈ Ideal.span {(p : 𝓞) ^ (M - 1)} := by
  by_cases hj : m j = 0
  · rw [hj, Nat.cast_zero, zero_mul]; exact zero_mem _
  have hA := natCast_mul_coeff_mem (φ i) (hint i) m j (Nat.one_le_iff_ne_zero.2 hj)
  have hdeg : 1 ≤ m.degree := (Nat.one_le_iff_ne_zero.2 hj).trans (Finsupp.le_degree j m)
  rcases le_or_gt m.degree M with hle | hlt
  · rw [show coeff m G = G.coeff m from rfl, (hG m).1 hle, mul_left_comm]
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hA
    refine Ideal.mem_span_singleton'.2 ⟨b, ?_⟩
    rw [show coeff m (φ i) = (φ i).coeff m from rfl] at hb
    rw [← hb, show M - 1 = (M - m.degree) + (m.degree - 1) by omega, pow_add]
    ring
  · rcases (hG m).2 hlt with h | ⟨h0, -⟩
    · have hx : (p : 𝓞) ^ (m.degree - M) * (((m j : ℕ) : 𝓞) * coeff m G) ∈
          Ideal.span {(p : 𝓞) ^ (m.degree - 1)} := by
        have : (p : 𝓞) ^ (m.degree - M) * (((m j : ℕ) : 𝓞) * coeff m G) =
            ((m j : ℕ) : 𝓞) * (G.coeff m * (p : 𝓞) ^ (m.degree - M)) := by
          rw [show coeff m G = G.coeff m from rfl]; ring
        rw [this, h]
        exact hA
      have := mem_span_pow_of_pow_mul_mem hpR (by omega) hx
      rwa [show m.degree - 1 - (m.degree - M) = M - 1 by omega] at this
    · rw [show coeff m G = G.coeff m from rfl, h0, mul_zero]; exact zero_mem _

omit hp in
include hpR hint hM hG in

theorem natCast_mul_coeff_subst_X_comp_mem {e : Fin d → Fin d ⊕ Fin d} (he : Function.Injective e)
    (μ : (Fin d ⊕ Fin d) →₀ ℕ) (t : Fin d ⊕ Fin d) :
    ((μ t : ℕ) : 𝓞) * coeff μ (subst (fun j => (X (e j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G) ∈
      Ideal.span {(p : 𝓞) ^ (M - 1)} := by
  classical
  by_cases hex : ∃ m : Fin d →₀ ℕ, m.mapDomain e = μ
  · obtain ⟨m, rfl⟩ := hex
    rw [coeff_mapDomain_subst_X_comp he]
    by_cases ht : t ∈ Set.range e
    · obtain ⟨j, rfl⟩ := ht
      rw [Finsupp.mapDomain_apply he]
      exact natCast_mul_coeff_trunc_mem hpR φ hint M hM i G hG m j
    · rw [Finsupp.mapDomain_notin_range _ _ ht, Nat.cast_zero, zero_mul]
      exact zero_mem _
  · have hex' : ∀ m : Fin d →₀ ℕ, m.mapDomain e ≠ μ := fun m hm => hex ⟨m, hm⟩
    rw [coeff_subst_X_comp_eq_zero e G μ hex', mul_zero]
    exact zero_mem _

omit hp in
include hpR hint hM hG in

theorem natCast_mul_coeff_subst_law_mem (μ : (Fin d ⊕ Fin d) →₀ ℕ) (t : Fin d ⊕ Fin d) :
    ((μ t : ℕ) : 𝓞) * coeff μ (subst F.toPowerSeries G) ∈ Ideal.span {(p : 𝓞) ^ (M - 1)} := by
  classical

  by_cases hμt : μ t = 0
  · rw [hμt, Nat.cast_zero, zero_mul]; exact zero_mem _
  obtain ⟨ν, rfl⟩ : ∃ ν : (Fin d ⊕ Fin d) →₀ ℕ, ν + Finsupp.single t 1 = μ :=
    ⟨μ - Finsupp.single t 1, tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hμt))⟩
  have hνt : (ν + Finsupp.single t 1 : (Fin d ⊕ Fin d) →₀ ℕ) t = ν t + 1 := by simp
  rw [hνt]
  have hFs : HasSubst F.toPowerSeries := F.hasSubst_toPowerSeries

  rw [natCast_succ_mul_coeff_eq_coeff_shift]

  rw [subst_comp_subst_apply hFs hasSubst_Xplus]

  have hgf : HasSubst (fun j => subst (fun t => (X (Sum.inl t) : MvPowerSeries ((Fin d ⊕ Fin d) ⊕ (Fin d ⊕ Fin d)) 𝓞)) (F.toPowerSeries j) +
      ∑ k' : Fin d ⊕ Fin d, X (Sum.inr k') *
        subst (fun t => (X (Sum.inl t) : MvPowerSeries ((Fin d ⊕ Fin d) ⊕ (Fin d ⊕ Fin d)) 𝓞)) (Dser (F.toPowerSeries j) k')) := by
    refine hasSubst_of_constantCoeff_zero (fun j => ?_)
    rw [map_add, constantCoeff_subst_eq_zero hasSubst_Xinl' (fun t => constantCoeff_X _) (F.constantCoeff_eq_zero j),
      map_sum, zero_add]
    exact Finset.sum_eq_zero fun k' _ => by rw [map_mul, constantCoeff_X, zero_mul]
  have hsh : HasSubst (fun j => subst (fun s => (X (Sum.inl s) + X (Sum.inr s) : MvPowerSeries ((Fin d ⊕ Fin d) ⊕ (Fin d ⊕ Fin d)) 𝓞))
      (F.toPowerSeries j)) :=
    hasSubst_of_constantCoeff_zero (fun j => constantCoeff_subst_eq_zero hasSubst_Xplus
      (fun s => by rw [map_add, constantCoeff_X, constantCoeff_X, add_zero]) (F.constantCoeff_eq_zero j))
  rw [coeff_subst_congr_Ylow hsh hgf (fun j μ' hμ' => coeff_shift_eq_coeff_gfam (F.toPowerSeries j) μ' hμ') G _
    (by rw [Ydeg_sumElim, Finsupp.degree_single])]

  rw [MvPowerSeries.coeff_sumElim_single_subst_add_sum_X_mul_eq G (Dser G) (fun j m => coeff_Dser G j m)
    F.toPowerSeries F.constantCoeff_eq_zero (fun j k => Dser (F.toPowerSeries j) k) ν t]

  have hDG : ∀ j : Fin d, ∃ q : MvPowerSeries (Fin d) 𝓞, Dser G j = C ((p : 𝓞) ^ (M - 1)) * q := fun j =>
    exists_eq_C_mul_of_forall_coeff_mem _ _ (fun m => by
      have hmj : (m + Finsupp.single j 1 : Fin d →₀ ℕ) j = m j + 1 := by simp
      have key := natCast_mul_coeff_trunc_mem hpR φ hint M hM i G hG (m + Finsupp.single j 1) j
      rw [hmj] at key
      rw [coeff_Dser]
      exact key)
  choose Q hQ using hDG
  have hsum : (∑ j : Fin d, Dser (F.toPowerSeries j) t * subst F.toPowerSeries (Dser G j)) =
      C ((p : 𝓞) ^ (M - 1)) * ∑ j : Fin d, Dser (F.toPowerSeries j) t * subst F.toPowerSeries (Q j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hQ j, subst_mul hFs, subst_C]
    ring
  rw [hsum, coeff_C_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

include hpR hFp hFp0 hφF hint hM hG in

theorem main :
    (∀ μ : (Fin d ⊕ Fin d) →₀ ℕ,
        (subst F.toPowerSeries G
          - subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G
          - subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G).coeff μ ≠ 0 →
        p ^ (M - 1) < μ.degree) ∧
    (∀ (μ : (Fin d ⊕ Fin d) →₀ ℕ) (t : Fin d ⊕ Fin d),
        ((μ t : ℕ) : 𝓞) *
          (subst F.toPowerSeries G
            - subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G
            - subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G).coeff μ ∈
          Ideal.span {(p : 𝓞) ^ (M - 1)}) := by
  refine ⟨fun μ hμ => ?_, fun μ t => ?_⟩
  · by_contra hle
    have hle' : μ.degree ≤ p ^ (M - 1) := not_lt.1 hle
    have hlt : μ.degree < p ^ M :=
      lt_of_le_of_lt hle' (Nat.pow_lt_pow_right hp.out.one_lt (by omega))
    exact hμ (coeff_defect_eq_zero hpR F Fp hFp hFp0 φ hφF hint M i G hG μ hlt)
  · show ((μ t : ℕ) : 𝓞) * coeff μ (subst F.toPowerSeries G
            - subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G
            - subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G) ∈ _
    rw [map_sub, map_sub, mul_sub, mul_sub]
    exact sub_mem (sub_mem (natCast_mul_coeff_subst_law_mem hpR F φ hint M hM i G hG μ t)
      (natCast_mul_coeff_subst_X_comp_mem hpR φ hint M hM i G hG Sum.inl_injective μ t))
      (natCast_mul_coeff_subst_X_comp_mem hpR φ hint M hM i G hG Sum.inr_injective μ t)

end Defect

end S17D3

open MvPowerSeries in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (hφint : ∀ (i j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * (φ i).coeff (m + Finsupp.single j 1) ∈ Ideal.span {(p : 𝓞) ^ m.degree})
    (M : ℕ) (hM : 1 ≤ M) (i : Fin d) (G : MvPowerSeries (Fin d) 𝓞)
    (hG : ∀ m : Fin d →₀ ℕ,
      (m.degree ≤ M → G.coeff m = (p : 𝓞) ^ (M - m.degree) * (φ i).coeff m) ∧
      (M < m.degree → G.coeff m * (p : 𝓞) ^ (m.degree - M) = (φ i).coeff m ∨
        (G.coeff m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - M) ∣ (φ i).coeff m))) :
    (∀ μ : (Fin d ⊕ Fin d) →₀ ℕ,
        (subst F.toPowerSeries G
          - subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G
          - subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G).coeff μ ≠ 0 →
        p ^ (M - 1) < μ.degree) ∧
    (∀ (μ : (Fin d ⊕ Fin d) →₀ ℕ) (t : Fin d ⊕ Fin d),
        ((μ t : ℕ) : 𝓞) *
          (subst F.toPowerSeries G
            - subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G
            - subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) G).coeff μ ∈
          Ideal.span {(p : 𝓞) ^ (M - 1)}) :=
  S17D3.main hp F Fp hFp hFp0 φ hφF hφint M hM i G hG

end S_MvFormalGroup_lt_degree_and_natCast_mul_coeff_subst_sub_sub_mem_of_scaledLogTrunc
end P2MW
export P2MW.S_MvFormalGroup_lt_degree_and_natCast_mul_coeff_subst_sub_sub_mem_of_scaledLogTrunc (solution)
