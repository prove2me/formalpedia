-- Prove2me | solution 1 for MvFormalGroup.exists_coeff_mem_span_pow_sub_log_of_isNilpotent_hasseWitt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/7f9cce52-b571-59d9-b23b-ddda2a0d4749

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Theorems.Thm_MvFormalGroup_natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add
import Theorems.Thm_MvFormalGroup_exists_forall_coeff_nthSeries_pow_mem_span_of_isNilpotent_hasseWitt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_coeff_mem_span_pow_sub_log_of_isNilpotent_hasseWitt
p2m_attr_erase "instance" "MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'"

set_option autoImplicit false

universe u

namespace S17SB

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

noncomputable def Hp (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞) : ℕ → Fin d → MvPowerSeries (Fin d) 𝓞
  | 0 => fun _ => 0
  | n + 1 => fun i => subst (Sum.elim (Hp Fp n) fun j => X j) (Fp i)

variable (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞) (hFp0 : ∀ i, (Fp i).constantCoeff = 0)

theorem Hp_zero : Hp Fp 0 = fun _ => 0 := rfl

theorem Hp_succ (n : ℕ) : Hp Fp (n + 1) = fun i => subst (Sum.elim (Hp Fp n) fun j => X j) (Fp i) := rfl

include hFp0 in
theorem constantCoeff_Hp (n : ℕ) : ∀ i, (Hp Fp n i).constantCoeff = 0 := by
  induction n with
  | zero => intro i; rw [Hp_zero, map_zero]
  | succ n ih =>
    intro i
    rw [Hp_succ]
    exact constantCoeff_subst_eq_zero
      (MvFormalGroup.hasSubst_elim ih (fun j => constantCoeff_X j))
      (fun s => by rcases s with j | j <;> simp [ih j, constantCoeff_X]) (hFp0 i)

include hFp0 in
theorem hasSubst_Hp_elim (n : ℕ) : HasSubst (Sum.elim (Hp Fp n) fun j => (X j : MvPowerSeries (Fin d) 𝓞)) :=
  MvFormalGroup.hasSubst_elim (constantCoeff_Hp Fp hFp0 n) (fun j => constantCoeff_X j)

include hFp0 in
theorem hasSubst_Hp (n : ℕ) : HasSubst (Hp Fp n) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_Hp Fp hFp0 n)

include hFp0 in

theorem subst_Hp_eq_nsmul (φ : Fin d → MvPowerSeries (Fin d) 𝓞) (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (n : ℕ) (i : Fin d) : subst (Hp Fp n) (φ i) = n • φ i := by
  induction n with
  | zero =>
    rw [Hp_zero, zero_smul, subst_zero_family, hφ0, map_zero]
  | succ n ih =>
    have hE := hasSubst_Hp_elim Fp hFp0 n
    have hinl : HasSubst (fun j : Fin d => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) :=
      hasSubst_of_constantCoeff_zero (fun j => constantCoeff_X _)
    have hinr : HasSubst (fun j : Fin d => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) :=
      hasSubst_of_constantCoeff_zero (fun j => constantCoeff_X _)
    rw [Hp_succ, ← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hFp0) hE, hφF, subst_add hE,
      subst_comp_subst_apply hinl hE, subst_comp_subst_apply hinr hE]
    simp only [subst_X hE, Sum.elim_inl, Sum.elim_inr]
    rw [show (fun j => Hp Fp n j) = Hp Fp n from rfl, ih,
      show (fun j => (X j : MvPowerSeries (Fin d) 𝓞)) = X from rfl,
      show subst (X : Fin d → MvPowerSeries (Fin d) 𝓞) (φ i) = φ i from congrFun subst_self (φ i),
      succ_nsmul]

variable (F : MvFormalGroup d 𝓞)
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

include hFp hFp0 in

theorem rho_nthSeries (n : ℕ) (i : Fin d) : rho p (F.nthSeries n i) = (p : 𝓞) • Hp Fp n i := by
  induction n generalizing i with
  | zero => simp [MvFormalGroup.nthSeries_zero, Hp_zero]
  | succ n ih =>
    rw [MvFormalGroup.nthSeries_succ, Hp_succ]
    dsimp only
    have hH : HasSubst (Sum.elim (F.nthSeries n) fun j => (X j : MvPowerSeries (Fin d) 𝓞)) :=
      MvFormalGroup.hasSubst_elim (MvFormalGroup.constantCoeff_nthSeries F n) (fun j => constantCoeff_X j)
    rw [rho_subst p hH]
    have hfam : (fun t => rho p (Sum.elim (F.nthSeries n) (fun j => (X j : MvPowerSeries (Fin d) 𝓞)) t)) =
        fun t => (p : 𝓞) • Sum.elim (Hp Fp n) (fun j => (X j : MvPowerSeries (Fin d) 𝓞)) t := by
      funext t
      rcases t with j | j
      · simp only [Sum.elim_inl, ih j]
      · simp only [Sum.elim_inr, rho_X]
    rw [hfam, subst_smul_family p (hasSubst_Hp_elim Fp hFp0 n), rho_law Fp hFp0 F hFp,
      subst_smul (hasSubst_Hp_elim Fp hFp0 n)]

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

section LowDeg
variable {σ : Type*} [Fintype σ]

open Classical in

noncomputable def lowDeg (σ : Type*) [Fintype σ] (N : ℕ) : Finset (σ →₀ ℕ) :=
  ((Fintype.piFinset fun _ : σ => Finset.range (N + 1)).image fun f => Finsupp.equivFunOnFinite.symm f).filter
    fun n => n.degree ≤ N

theorem mem_lowDeg {N : ℕ} (n : σ →₀ ℕ) : n ∈ lowDeg σ N ↔ n.degree ≤ N := by
  classical
  rw [lowDeg, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨Finset.mem_image.2 ⟨fun s => n s, Fintype.mem_piFinset.2 fun s => Finset.mem_range.2
      (Nat.lt_succ_of_le ((Finsupp.le_degree s n).trans h)), ?_⟩, h⟩
    ext s; simp

end LowDeg

section Weights

variable {𝓞 : Type*} [CommRing 𝓞] {σ : Type*} (p : ℕ)

theorem span_pow_antitone {i j : ℕ} (h : i ≤ j) : Ideal.span {(p : 𝓞) ^ j} ≤ Ideal.span {(p : 𝓞) ^ i} :=
  Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ h)

theorem mul_mem_span_pow {i j : ℕ} {x y : 𝓞} (hx : x ∈ Ideal.span {(p : 𝓞) ^ i}) (hy : y ∈ Ideal.span {(p : 𝓞) ^ j}) :
    x * y ∈ Ideal.span {(p : 𝓞) ^ (i + j)} := by
  rw [pow_add, ← Ideal.span_singleton_mul_span_singleton]
  exact Ideal.mul_mem_mul hx hy

def Wt (c : ℕ) (S : MvPowerSeries σ 𝓞) : Prop := ∀ n : σ →₀ ℕ, coeff n S ∈ Ideal.span {(p : 𝓞) ^ (n.degree - c)}

def OrdGe (D : ℕ) (S : MvPowerSeries σ 𝓞) : Prop := ∀ n : σ →₀ ℕ, n.degree < D → coeff n S = 0

variable {p}

theorem Wt.mul {a b : ℕ} {S T : MvPowerSeries σ 𝓞} (hS : Wt p a S) (hT : Wt p b T) : Wt p (a + b) (S * T) := by
  classical
  intro n
  rw [coeff_mul]
  refine Ideal.sum_mem _ fun x hx => ?_
  have hdeg : x.1.degree + x.2.degree = n.degree := by
    rw [← map_add, Finset.HasAntidiagonal.mem_antidiagonal.1 hx]
  refine span_pow_antitone p ?_ (mul_mem_span_pow p (hS x.1) (hT x.2))
  omega

theorem Wt.one : Wt p 0 (1 : MvPowerSeries σ 𝓞) := by
  classical
  intro n
  rw [coeff_one]
  split_ifs with h
  · rw [h]; simp
  · exact Ideal.zero_mem _

theorem Wt.pow {c : ℕ} {S : MvPowerSeries σ 𝓞} (hS : Wt p c S) (k : ℕ) : Wt p (c * k) (S ^ k) := by
  induction k with
  | zero => rw [mul_zero, pow_zero]; exact Wt.one
  | succ k ih => rw [pow_succ, Nat.mul_succ]; exact ih.mul hS

theorem Wt.prod {ι : Type*} (s : Finset ι) {c : ι → ℕ} {S : ι → MvPowerSeries σ 𝓞} (h : ∀ i ∈ s, Wt p (c i) (S i)) :
    Wt p (∑ i ∈ s, c i) (∏ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact Wt.one
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Wt.natCast_mul {c : ℕ} {S : MvPowerSeries σ 𝓞} (hS : Wt p c S) (k : ℕ) : Wt p c ((k : MvPowerSeries σ 𝓞) * S) := by
  intro n
  rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
  exact Ideal.mul_mem_left _ _ (hS n)

theorem OrdGe.mul {D D' : ℕ} {S T : MvPowerSeries σ 𝓞} (hS : OrdGe D S) (hT : OrdGe D' T) : OrdGe (D + D') (S * T) := by
  classical
  intro n hn
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hdeg : x.1.degree + x.2.degree = n.degree := by
    rw [← map_add, Finset.HasAntidiagonal.mem_antidiagonal.1 hx]
  rcases Nat.lt_or_ge x.1.degree D with h1 | h1
  · rw [hS _ h1, zero_mul]
  · rw [hT _ (by omega), mul_zero]

theorem OrdGe.zero' (S : MvPowerSeries σ 𝓞) : OrdGe 0 S := fun n hn => absurd hn (Nat.not_lt_zero _)

theorem OrdGe.pow {D : ℕ} {S : MvPowerSeries σ 𝓞} (hS : OrdGe D S) (k : ℕ) : OrdGe (D * k) (S ^ k) := by
  induction k with
  | zero => rw [mul_zero]; exact OrdGe.zero' _
  | succ k ih => rw [pow_succ, Nat.mul_succ]; exact ih.mul hS

theorem OrdGe.prod {ι : Type*} (s : Finset ι) {D : ι → ℕ} {S : ι → MvPowerSeries σ 𝓞} (h : ∀ i ∈ s, OrdGe (D i) (S i)) :
    OrdGe (∑ i ∈ s, D i) (∏ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact OrdGe.zero' _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem OrdGe.natCast_mul {D : ℕ} {S : MvPowerSeries σ 𝓞} (hS : OrdGe D S) (k : ℕ) : OrdGe D ((k : MvPowerSeries σ 𝓞) * S) := by
  intro n hn
  rw [← nsmul_eq_mul, map_nsmul, hS n hn, smul_zero]

theorem OrdGe.one_of_constantCoeff {S : MvPowerSeries σ 𝓞} (h : constantCoeff S = 0) : OrdGe 1 S := by
  intro n hn
  have : n = 0 := (Finsupp.degree_eq_zero_iff n).1 (by omega)
  rw [this, coeff_zero_eq_constantCoeff_apply, h]

end Weights

section Expo

theorem log_add_le_log {p : ℕ} (hp : 1 < p) {B n n' : ℕ} (hn' : n' ≠ 0) (h : p ^ B * n' ≤ n) :
    Nat.log p n' + B ≤ Nat.log p n := by
  have h1 : p ^ Nat.log p n' ≤ n' := Nat.pow_log_le_self p hn'
  have h2 : p ^ (Nat.log p n' + B) ≤ n := by
    rw [pow_add, mul_comm]
    exact (Nat.mul_le_mul_left _ h1).trans h
  exact Nat.le_log_of_pow_le hp h2

theorem div_add_le_div {A B L L' : ℕ} (hB : 0 < B) (h : L' + B ≤ L) : A * L' / B + A ≤ A * L / B := by
  have : A * L' + A * B ≤ A * L := by nlinarith
  calc A * L' / B + A = (A * L' + A * B) / B := (Nat.add_mul_div_right _ _ hB).symm
    _ ≤ A * L / B := Nat.div_le_div_right this

end Expo

section Main

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [hp : Fact p.Prime]

omit hp in

theorem eq_of_smul_eq_smul {σ : Type*} (hpR : (p : 𝓞) ∈ nonZeroDivisors 𝓞) {S T : MvPowerSeries σ 𝓞}
    (h : (p : 𝓞) • S = (p : 𝓞) • T) : S = T := by
  ext n
  have := congrArg (coeff n) h
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
  have h0 : (p : 𝓞) * (coeff n S - coeff n T) = 0 := by rw [mul_sub, this, sub_self]
  exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 hpR).1 _ h0)

omit hp in
theorem degree_eq_sum_univ {d : ℕ} (m : Fin d →₀ ℕ) : m.degree = ∑ j, m j := by
  rw [Finsupp.degree_apply]
  exact Finset.sum_subset (Finset.subset_univ _) fun j _ hj => Finsupp.notMem_support_iff.1 hj

def expo (A n : ℕ) : ℕ := ((n - 1) - (A * Nat.log p n) / (A + 1)) - A

omit hp in
theorem expo_step {A n n' : ℕ} (hlog : Nat.log p n' + (A + 1) ≤ Nat.log p n) (hgap : n' + A + 1 ≤ n) :
    A + expo p A n ≤ expo p A n' + (n - n') := by
  have hdiv : A * Nat.log p n' / (A + 1) + A ≤ A * Nat.log p n / (A + 1) := div_add_le_div (B := A + 1) (by omega) hlog
  unfold expo
  generalize A * Nat.log p n' / (A + 1) = X' at *
  generalize A * Nat.log p n / (A + 1) = X at *
  omega

omit hp in
theorem expo_le {A n : ℕ} (h : expo p A n ≠ 0) : A + expo p A n ≤ n := by
  unfold expo at *
  generalize A * Nat.log p n / (A + 1) = X at *
  omega

omit hp in

theorem exists_decomp {d B : ℕ} (T : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hT : ∀ (j : Fin d) (n : Fin d →₀ ℕ), n.degree < p ^ B → coeff n (T j) ∈ Ideal.span {(p : 𝓞)}) :
    ∃ G P : Fin d → MvPowerSeries (Fin d) 𝓞, (∀ j, T j = G j + (p : 𝓞) • P j) ∧ ∀ j, OrdGe (p ^ B) (G j) := by
  classical
  have hc : ∀ (j : Fin d) (n : Fin d →₀ ℕ), ∃ c : 𝓞, n.degree < p ^ B → c * (p : 𝓞) = coeff n (T j) := by
    intro j n
    by_cases h : n.degree < p ^ B
    · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hT j n h); exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose c hc using hc
  refine ⟨fun j n => if n.degree < p ^ B then 0 else coeff n (T j), fun j n => if n.degree < p ^ B then c j n else 0, ?_, ?_⟩
  · intro j; ext n
    rw [map_add, map_smul, smul_eq_mul]
    show coeff n (T j) = (if n.degree < p ^ B then (0 : 𝓞) else coeff n (T j)) + (p : 𝓞) * (if n.degree < p ^ B then c j n else 0)
    split_ifs with h
    · rw [zero_add, mul_comm, hc j n h]
    · rw [mul_zero, add_zero]
  · intro j n hn
    show (if n.degree < p ^ B then (0 : 𝓞) else coeff n (T j)) = 0
    rw [if_pos hn]

variable (hpR : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
  [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
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
  (hHW : IsNilpotent (Matrix.of fun i j : Fin d =>
    algebraMap 𝓞 (ZMod p) ((F.nthSeries p i).coeff (Finsupp.single j p))))

include hpR hker hFp hFp0 hφ0 hφ1 hφF hHW in
theorem main :
    ∃ A B C : ℕ, A < B ∧ ∀ (i : Fin d) (m : Fin d →₀ ℕ), m ≠ 0 →
      (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ ((m.degree - 1) - (A * Nat.log p m.degree) / B - C)} := by
  classical
  obtain ⟨A, hA1, hGform⟩ :=
    MvFormalGroup.exists_forall_coeff_nthSeries_pow_mem_span_of_isNilpotent_hasseWitt p hker F hHW
  refine ⟨A, A + 1, A, Nat.lt_succ_self A, ?_⟩
  have hp1 : 1 < p := hp.out.one_lt
  set B := A + 1 with hB
  have hpB : A + 2 ≤ p ^ B := by
    have h1 : B < 2 ^ B := Nat.lt_two_pow_self
    have h2 : 2 ^ B ≤ p ^ B := Nat.pow_le_pow_left hp.out.two_le B
    omega

  have hint : ∀ (i j : Fin d) (m : Fin d →₀ ℕ), ((m j + 1 : ℕ) : 𝓞) * coeff (m + Finsupp.single j 1) (φ i) ∈
      Ideal.span {(p : 𝓞) ^ m.degree} := fun i j m =>
    MvFormalGroup.natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add p hpR F Fp hFp hFp0 φ hφ0 hφ1 hφF i j m

  obtain ⟨G, P, hTGP, hOG⟩ := exists_decomp p (F.nthSeries (p ^ A)) hGform
  set Gt : Fin d → MvPowerSeries (Fin d) 𝓞 := fun j n => (p : 𝓞) ^ (n.degree - 1) * coeff n (G j) with hGt
  have hcoeffGt : ∀ j n, coeff n (Gt j) = (p : 𝓞) ^ (n.degree - 1) * coeff n (G j) := fun j n => rfl
  have hρG : ∀ j, rho p (G j) = (p : 𝓞) • Gt j := by
    intro j; ext n
    rw [coeff_rho, map_smul, smul_eq_mul, hcoeffGt]
    by_cases hn : n = 0
    · rw [hn, hOG j 0 (by rw [map_zero]; exact pow_pos hp.out.pos _), mul_zero, mul_zero, mul_zero]
    · have h1 : 1 ≤ n.degree := Nat.one_le_iff_ne_zero.2 (fun h => hn ((Finsupp.degree_eq_zero_iff n).1 h))
      obtain ⟨t, ht⟩ : ∃ t, n.degree = t + 1 := ⟨n.degree - 1, by omega⟩
      rw [ht, Nat.add_sub_cancel, pow_succ]; ring
  set H := Hp Fp (p ^ A) with hH
  have hHdec : ∀ j, H j = Gt j + rho p (P j) := by
    intro j
    apply eq_of_smul_eq_smul p hpR
    have hρsmul : ∀ S : MvPowerSeries (Fin d) 𝓞, rho p ((p : 𝓞) • S) = (p : 𝓞) • rho p S := fun S => by
      ext n; simp only [coeff_rho, map_smul, smul_eq_mul]; ring
    rw [hH, ← rho_nthSeries Fp hFp0 F hFp (p ^ A) j, hTGP, map_add, hρG, hρsmul, smul_add]

  have hWG : ∀ j, Wt p 1 (Gt j) := fun j n => by
    rw [hcoeffGt]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hOGt : ∀ j, OrdGe (p ^ B) (Gt j) := fun j n hn => by rw [hcoeffGt, hOG j n hn, mul_zero]
  have hWP : ∀ j, Wt p 0 (rho p (P j)) := fun j n => by
    rw [coeff_rho, Nat.sub_zero]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hOH : ∀ j, OrdGe 1 (H j) := fun j => OrdGe.one_of_constantCoeff (constantCoeff_Hp Fp hFp0 (p ^ A) j)
  have hHs : HasSubst H := hasSubst_Hp Fp hFp0 (p ^ A)

  suffices key : ∀ D : ℕ, ∀ (i : Fin d) (m : Fin d →₀ ℕ), m ≠ 0 → m.degree = D →
      coeff m (φ i) ∈ Ideal.span {(p : 𝓞) ^ expo p A D} by
    intro i m hm
    exact key _ i m hm rfl
  intro D
  induction D using Nat.strong_induction_on with
  | _ D IH =>
  intro i m hm hmD
  by_cases hE0 : expo p A D = 0
  · rw [hE0, pow_zero, Ideal.span_singleton_one]; exact Submodule.mem_top
  have hEle := expo_le p hE0

  have hid : (p : 𝓞) ^ A * coeff m (φ i) = coeff m (subst H (φ i)) := by
    rw [hH, subst_Hp_eq_nsmul Fp hFp0 φ hφ0 hφF, map_nsmul, nsmul_eq_mul, Nat.cast_pow]

  have hsub : coeff m (subst H (φ i)) = ∑ m' ∈ lowDeg (Fin d) D, coeff m' (φ i) * coeff m (m'.prod fun j e => H j ^ e) := by
    rw [coeff_subst hHs, finsum_eq_sum_of_support_subset (s := lowDeg (Fin d) D)]
    · exact Finset.sum_congr rfl fun m' _ => smul_eq_mul _ _
    · intro m' hm'
      rw [Finset.mem_coe, mem_lowDeg]
      by_contra hlt
      apply hm'
      have hO : OrdGe (m'.degree) (m'.prod fun j e => H j ^ e) := by
        rw [Finsupp.prod, Finsupp.degree_apply]
        have := OrdGe.prod m'.support (D := fun j => 1 * m' j) (S := fun j => H j ^ m' j) (fun j _ => (hOH j).pow _)
        simpa using this
      show coeff m' (φ i) • coeff m (m'.prod fun j e => H j ^ e) = 0
      rw [hO m (by omega), smul_zero]

  have hterm : ∀ m' ∈ lowDeg (Fin d) D, coeff m' (φ i) * coeff m (m'.prod fun j e => H j ^ e) ∈
      Ideal.span {(p : 𝓞) ^ (A + expo p A D)} := by
    intro m' hm'S
    have hm'D : m'.degree ≤ D := (mem_lowDeg m').1 hm'S
    by_cases hm'0 : m' = 0
    · rw [hm'0, coeff_zero_eq_constantCoeff_apply, hφ0, zero_mul]; exact Ideal.zero_mem _

    have hprod : (m'.prod fun j e => H j ^ e) =
        ∑ k ∈ Fintype.piFinset (fun j => Finset.range (m' j + 1)),
          ∏ j, (rho p (P j) ^ (k j) * Gt j ^ (m' j - k j) * (Nat.choose (m' j) (k j) : MvPowerSeries (Fin d) 𝓞)) := by
      rw [Finsupp.prod_fintype _ _ (fun j => pow_zero _)]
      simp_rw [hHdec, add_comm (Gt _), add_pow]
      rw [Finset.prod_univ_sum]
    rw [hprod, map_sum, Finset.mul_sum]
    refine Ideal.sum_mem _ fun k hk => ?_
    have hkle : ∀ j, k j ≤ m' j := fun j => Nat.lt_succ_iff.1 (Finset.mem_range.1 (Fintype.mem_piFinset.1 hk j))

    set Q : MvPowerSeries (Fin d) 𝓞 := ∏ j, (rho p (P j) ^ (k j) * Gt j ^ (m' j - k j)) with hQ
    set cc : ℕ := ∏ j, Nat.choose (m' j) (k j) with hcc
    have hsplit : (∏ j, (rho p (P j) ^ (k j) * Gt j ^ (m' j - k j) * (Nat.choose (m' j) (k j) : MvPowerSeries (Fin d) 𝓞))) =
        (cc : MvPowerSeries (Fin d) 𝓞) * Q := by
      rw [hQ, hcc, Nat.cast_prod, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun j _ => by ring
    rw [hsplit, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]

    set s : ℕ := ∑ j, (m' j - k j) with hs
    set t : ℕ := ∑ j, k j with ht
    have hst : s + t = m'.degree := by
      rw [degree_eq_sum_univ, hs, ht, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => Nat.sub_add_cancel (hkle j)
    have hWQ : Wt p s Q := by
      rw [hQ, hs]
      refine Wt.prod _ fun j _ => ?_
      have := ((hWP j).pow (k j)).mul ((hWG j).pow (m' j - k j))
      rwa [zero_mul, one_mul, zero_add] at this
    have hcQ : coeff m Q ∈ Ideal.span {(p : 𝓞) ^ (D - s)} := by rw [← hmD]; exact hWQ m
    by_cases hk0 : ∀ j, k j = 0
    ·
      have hs' : s = m'.degree := by rw [← hst, ht, Finset.sum_eq_zero (fun j _ => hk0 j), add_zero]
      have hOQ : OrdGe (p ^ B * m'.degree) Q := by
        rw [hQ, degree_eq_sum_univ, Finset.mul_sum]
        refine OrdGe.prod _ fun j _ => ?_
        rw [hk0 j, pow_zero, one_mul, Nat.sub_zero]
        exact (hOGt j).pow _
      rcases Nat.lt_or_ge D (p ^ B * m'.degree) with hlt | hge
      · rw [hOQ m (by omega), mul_zero, mul_zero]; exact Ideal.zero_mem _
      ·
        have hm'pos : 1 ≤ m'.degree := Nat.one_le_iff_ne_zero.2 (fun h => hm'0 ((Finsupp.degree_eq_zero_iff m').1 h))
        have hm'lt : m'.degree < D := by nlinarith
        have hIH := IH m'.degree hm'lt i m' hm'0 rfl
        have hlog : Nat.log p m'.degree + (A + 1) ≤ Nat.log p D := log_add_le_log hp1 (by omega) hge
        have hgap : m'.degree + A + 1 ≤ D := by nlinarith
        have hstep := expo_step p hlog hgap
        have hre : coeff m' (φ i) * ((cc : 𝓞) * coeff m Q) = (cc : 𝓞) * (coeff m' (φ i) * coeff m Q) := by ring
        rw [hre]
        refine Ideal.mul_mem_left _ _ (span_pow_antitone p (hstep.trans ?_) (mul_mem_span_pow p hIH hcQ))
        rw [hs']
    ·
      push Not at hk0
      obtain ⟨j₀, hj₀⟩ := hk0
      have hkj₀ : 1 ≤ k j₀ := Nat.one_le_iff_ne_zero.2 hj₀
      have hmj₀ : 1 ≤ m' j₀ := hkj₀.trans (hkle j₀)

      have hI := natCast_mul_coeff_mem (p := p) (φ i) (hint i) m' j₀ hmj₀

      have hbin : k j₀ * Nat.choose (m' j₀) (k j₀) = m' j₀ * Nat.choose (m' j₀ - 1) (k j₀ - 1) := by
        have := Nat.add_one_mul_choose_eq (m' j₀ - 1) (k j₀ - 1)
        rw [Nat.sub_add_cancel hmj₀, Nat.sub_add_cancel hkj₀] at this
        linarith
      have hcc' : cc = Nat.choose (m' j₀) (k j₀) * ∏ j ∈ Finset.univ.erase j₀, Nat.choose (m' j) (k j) := by
        rw [hcc, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j₀)]

      set term := coeff m' (φ i) * ((cc : 𝓞) * coeff m Q) with hterm
      have h1 : ((k j₀ : ℕ) : 𝓞) * term ∈ Ideal.span {(p : 𝓞) ^ ((m'.degree - 1) + (D - s))} := by
        have heq : ((k j₀ : ℕ) : 𝓞) * term = (((m' j₀ : ℕ) : 𝓞) * coeff m' (φ i)) *
            (((Nat.choose (m' j₀ - 1) (k j₀ - 1) * ∏ j ∈ Finset.univ.erase j₀, Nat.choose (m' j) (k j) : ℕ) : 𝓞) * coeff m Q) := by
          rw [hterm, hcc']
          have hcast : ((k j₀ : ℕ) : 𝓞) * ((Nat.choose (m' j₀) (k j₀) * ∏ j ∈ Finset.univ.erase j₀, Nat.choose (m' j) (k j) : ℕ) : 𝓞) =
              ((m' j₀ : ℕ) : 𝓞) * ((Nat.choose (m' j₀ - 1) (k j₀ - 1) * ∏ j ∈ Finset.univ.erase j₀, Nat.choose (m' j) (k j) : ℕ) : 𝓞) := by
            rw [← Nat.cast_mul, ← Nat.cast_mul, ← mul_assoc, ← mul_assoc, hbin]
          linear_combination (coeff m' (φ i) * coeff m Q) * hcast
        rw [heq]
        exact mul_mem_span_pow p hI (Ideal.mul_mem_left _ _ hcQ)

      obtain ⟨v, u, hu, hvu⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.one_le_iff_ne_zero.1 hkj₀) p hp.out.ne_one
      have hvk : v < k j₀ := by
        have h1 : v < p ^ v := Nat.lt_pow_self hp1
        have h2 : p ^ v ≤ k j₀ := by
          rw [hvu]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (fun h => hu (h ▸ dvd_zero p)))
        omega
      rw [hvu, Nat.cast_mul, Nat.cast_pow, mul_comm ((p : 𝓞) ^ v), mul_assoc] at h1
      have h2 := mem_span_pow_of_natCast_mul_mem (p := p) hu h1
      have htk : k j₀ ≤ t := by rw [ht]; exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ j₀)
      have h3 := mem_span_pow_of_pow_mul_mem (p := p) hpR (K := v) (e := (m'.degree - 1) + (D - s)) (by omega) h2
      refine span_pow_antitone p ?_ h3
      omega

  have hsum : (p : 𝓞) ^ A * coeff m (φ i) ∈ Ideal.span {(p : 𝓞) ^ (A + expo p A D)} := by
    rw [hid, hsub]; exact Ideal.sum_mem _ hterm
  have := mem_span_pow_of_pow_mul_mem (p := p) hpR (K := A) (e := A + expo p A D) (by omega) hsum
  rwa [Nat.add_sub_cancel_left] at this

end Main

end S17SB

open MvPowerSeries

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
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (hHW : IsNilpotent (Matrix.of fun i j : Fin d =>
      algebraMap 𝓞 (ZMod p) ((F.nthSeries p i).coeff (Finsupp.single j p)))) :
    ∃ A B C : ℕ, A < B ∧ ∀ (i : Fin d) (m : Fin d →₀ ℕ), m ≠ 0 →
      (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ ((m.degree - 1) - (A * Nat.log p m.degree) / B - C)} :=
  S17SB.main p hp hker F Fp hFp hFp0 φ hφ0 hφ1 hφF hHW

end S_MvFormalGroup_exists_coeff_mem_span_pow_sub_log_of_isNilpotent_hasseWitt
end P2MW
export P2MW.S_MvFormalGroup_exists_coeff_mem_span_pow_sub_log_of_isNilpotent_hasseWitt (solution)
