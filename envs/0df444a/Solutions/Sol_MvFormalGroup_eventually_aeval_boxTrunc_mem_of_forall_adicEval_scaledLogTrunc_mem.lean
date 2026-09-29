-- Prove2me | solution 1 for MvFormalGroup.eventually_aeval_boxTrunc_mem_of_forall_adicEval_scaledLogTrunc_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/7908101f-ecfe-5a4c-b77a-d8463c2bb08e

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_eventually_aeval_boxTrunc_mem_of_forall_adicEval_scaledLogTrunc_mem

set_option autoImplicit false

namespace S17L3

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

section Shadow

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

include hpR hFp hFp0 hφ0 hφF hint in
theorem coeff_shadow_eq_zero (v N : ℕ) (i : Fin d) (G : MvPowerSeries (Fin d) 𝓞)
    (hG : ∀ m : Fin d →₀ ℕ,
      (m.degree ≤ N → G.coeff m = (p : 𝓞) ^ (N - m.degree) * (φ i).coeff m) ∧
      (N < m.degree → G.coeff m * (p : 𝓞) ^ (m.degree - N) = (φ i).coeff m ∨
        (G.coeff m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ (φ i).coeff m)))
    (m : Fin d →₀ ℕ) (hm : m.degree < p ^ N) :
    coeff m (subst (F.nthSeries (p ^ v)) G - (p : MvPowerSeries (Fin d) 𝓞) ^ v * G) = 0 := by
  apply coeff_eq_zero_of_coeff_rho (p := p) hpR

  set T : MvPowerSeries (Fin d) 𝓞 := (p : 𝓞) ^ N • φ i - rho p G with hT
  have hTcoeff : ∀ m' : Fin d →₀ ℕ, m'.degree < p ^ N → coeff m' T = 0 := by
    intro m' hm'
    rw [hT, map_sub, map_smul, smul_eq_mul, coeff_rho, pow_degree_mul_coeff_eq hpR (φ i) (hint i) N G hG m' hm',
      sub_self]
  have hTord : ((p ^ N : ℕ) : ℕ∞) ≤ T.order :=
    nat_le_order fun m' hm' => hTcoeff m' (by exact_mod_cast hm')
  have hH : HasSubst (F.nthSeries (p ^ v)) :=
    hasSubst_of_constantCoeff_zero (MvFormalGroup.constantCoeff_nthSeries F _)
  have hHp := hasSubst_Hp Fp hFp0 (p ^ v)

  have h1 : rho p (subst (F.nthSeries (p ^ v)) G - (p : MvPowerSeries (Fin d) 𝓞) ^ v * G) =
      subst (Hp Fp (p ^ v)) (rho p G) - (p : MvPowerSeries (Fin d) 𝓞) ^ v * rho p G := by
    rw [map_sub, map_mul, map_pow, rho_natCast, rho_subst p hH,
      show (fun t => rho p (F.nthSeries (p ^ v) t)) = fun t => (p : 𝓞) • Hp Fp (p ^ v) t from
        funext fun t => rho_nthSeries Fp hFp0 F hFp _ t,
      subst_smul_family p hHp G]
  have h2 : rho p G = (p : 𝓞) ^ N • φ i - T := by rw [hT, sub_sub_cancel]
  have h3 : rho p (subst (F.nthSeries (p ^ v)) G - (p : MvPowerSeries (Fin d) 𝓞) ^ v * G) =
      (p : MvPowerSeries (Fin d) 𝓞) ^ v * T - subst (Hp Fp (p ^ v)) T := by
    rw [h1, h2, subst_sub hHp, subst_smul hHp, subst_Hp_eq_nsmul Fp hFp0 φ hφ0 hφF, nsmul_eq_mul, Nat.cast_pow,
      mul_sub, mul_smul_comm]
    abel
  rw [h3, map_sub, show ((p : MvPowerSeries (Fin d) 𝓞) ^ v * T) = C ((p : 𝓞) ^ v) * T by
      rw [map_pow, map_natCast], coeff_C_mul, hTcoeff m hm, mul_zero, zero_sub, neg_eq_zero]

  apply coeff_of_lt_order
  have hinf : (1 : ℕ∞) ≤ ⨅ j, (Hp Fp (p ^ v) j).order := by
    refine le_iInf fun j => nat_le_order fun m' hm' => ?_
    have : m' = 0 := (Finsupp.degree_eq_zero_iff m').1 (by exact_mod_cast Nat.lt_one_iff.1 (by exact_mod_cast hm'))
    rw [this, coeff_zero_eq_constantCoeff_apply, constantCoeff_Hp Fp hFp0]
  calc ((m.degree : ℕ) : ℕ∞) < (p ^ N : ℕ) := by exact_mod_cast hm
    _ ≤ T.order := hTord
    _ ≤ (⨅ j, (Hp Fp (p ^ v) j).order) * T.order := le_mul_of_one_le_left (by simp) hinf
    _ ≤ (T.subst (Hp Fp (p ^ v))).order := le_order_subst hHp T

end Shadow

section Rside

variable {𝓞 : Type*} [CommRing 𝓞] {R : Type*} [CommRing R] [Algebra 𝓞 R] {σ : Type*}

noncomputable def psum (x : σ → R) (T : Finset (σ →₀ ℕ)) (S : MvPowerSeries σ 𝓞) : R :=
  ∑ m ∈ T, coeff m S • m.prod fun s e => x s ^ e

theorem hasEval_of_mem_radical [Finite σ] (J : Ideal R) {x : σ → R} (hx : ∀ s, x s ∈ J.radical) :
    letI : TopologicalSpace R := J.adicTopology
    MvPowerSeries.HasEval x := by
  letI : TopologicalSpace R := J.adicTopology
  refine ⟨fun s => ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hx s
    show Filter.Tendsto (x s ^ ·) Filter.atTop (nhds 0)
    rw [(J.hasBasis_nhds_zero_adic).tendsto_right_iff]
    intro n _
    filter_upwards [Filter.eventually_ge_atTop (k * n)] with m hm
    obtain ⟨r, rfl⟩ : ∃ r, m = k * n + r := ⟨m - k * n, by omega⟩
    rw [pow_add, pow_mul]
    exact SetLike.mem_coe.mpr (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hk n))
  · rw [Filter.cofinite_eq_bot]
    exact Filter.tendsto_bot

theorem exists_adicEval_sub_psum_mem [Finite σ] (J : Ideal R) [IsAdicComplete J R] {x : σ → R}
    (hx : ∀ s, x s ∈ J.radical) (S : MvPowerSeries σ 𝓞) (K : ℕ) :
    ∃ T₀ : Finset (σ →₀ ℕ), ∀ T : Finset (σ →₀ ℕ), T₀ ⊆ T →
      MvFormalGroup.adicEval J x S - psum x T S ∈ J ^ K := by
  classical
  letI : UniformSpace 𝓞 := ⊥
  letI : WithIdeal R := ⟨J⟩
  haveI : CompleteSpace R :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J R›).1
  haveI : T2Space R :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J R›).2
  haveI : ContinuousSMul 𝓞 R := DiscreteTopology.instContinuousSMul 𝓞 R
  have ha : MvPowerSeries.HasEval x := hasEval_of_mem_radical J hx
  have heq : MvFormalGroup.adicEval J x S = MvPowerSeries.aeval ha S := by
    rw [← MvFormalGroup.coe_adicEvalAlgHom J hx]
    rfl
  have hsum := MvPowerSeries.hasSum_aeval ha S
  rw [HasSum] at hsum
  have hev := (J.hasBasis_nhds_adic (MvPowerSeries.aeval ha S)).tendsto_right_iff.1 hsum K trivial
  rw [SummationFilter.unconditional_filter, Filter.eventually_atTop] at hev
  obtain ⟨T₀, hT₀⟩ := hev
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  simp only [Set.mem_image, SetLike.mem_coe] at h
  obtain ⟨z, hz, hzT⟩ := h
  rw [heq, show psum x T S = ∑ m ∈ T, coeff m S • m.prod (fun s e => x s ^ e) from rfl, ← hzT,
    sub_add_cancel_left]
  exact (J ^ K).neg_mem_iff.2 hz

theorem adicEval_mem_pow [Finite σ] (J : Ideal R) [IsAdicComplete J R] {x : σ → R}
    (hx : ∀ s, x s ∈ J.radical) (S : MvPowerSeries σ 𝓞) (K : ℕ)
    (h : ∀ m : σ →₀ ℕ, coeff m S = 0 ∨ (m.prod fun s e => x s ^ e) ∈ J ^ K) :
    MvFormalGroup.adicEval J x S ∈ J ^ K := by
  obtain ⟨T₀, hT₀⟩ := exists_adicEval_sub_psum_mem J hx S K
  have h1 := hT₀ T₀ subset_rfl
  have h2 : psum x T₀ S ∈ J ^ K := by
    refine Ideal.sum_mem _ fun m _ => ?_
    rcases h m with h0 | hmem
    · rw [h0, zero_smul]; exact Ideal.zero_mem _
    · rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ hmem
  have := Ideal.add_mem _ h1 h2
  rwa [sub_add_cancel] at this

omit [Algebra 𝓞 R] in

theorem prod_pow_mem_pow {x : σ → R} {J : Ideal R} {e : ℕ} (hxe : ∀ s, x s ^ e ∈ J) (m : σ →₀ ℕ)
    {s : σ} {K : ℕ} (hs : e * K < m s) : (m.prod fun s k => x s ^ k) ∈ J ^ K := by
  classical
  have hsupp : s ∈ m.support := Finsupp.mem_support_iff.2 (by omega)
  rw [Finsupp.prod, ← Finset.mul_prod_erase _ _ hsupp]
  apply Ideal.mul_mem_right
  rw [show m s = e * K + (m s - e * K) by omega, pow_add, pow_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hxe s) K)

omit [Algebra 𝓞 R] [CommRing R] in

theorem exists_lt_apply [Fintype σ] (m : σ →₀ ℕ) (B : ℕ) (h : Fintype.card σ * B < m.degree) : ∃ s, B < m s := by
  by_contra h'
  have h'' : ∀ s, m s ≤ B := fun s => not_lt.1 (not_exists.1 h' s)
  have : m.degree ≤ Fintype.card σ * B := by
    rw [Finsupp.degree_eq_sum]
    calc ∑ i, m i ≤ ∑ _i : σ, B := Finset.sum_le_sum fun i _ => h'' i
      _ = Fintype.card σ * B := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  omega

omit [Algebra 𝓞 R] [CommRing R] in

theorem exists_N1 {q : ℕ} (hq : 2 ≤ q) (A₀ v : ℕ) : ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → A₀ * (N + v) < q ^ N := by
  refine ⟨(A₀ * (v + 1) + 1) ^ 2 + 1, fun N hN => ?_⟩
  set A := A₀ * (v + 1) + 1 with hA
  have hA1 : 1 ≤ A := by omega
  have hAN : A ≤ N := by nlinarith
  obtain ⟨M, rfl⟩ : ∃ M, N = M + A := ⟨N - A, by omega⟩
  have h1 : A + 1 ≤ 2 ^ A := Nat.lt_two_pow_self
  have h2 : M + 1 ≤ 2 ^ M := Nat.lt_two_pow_self
  have hMA : 1 ≤ M + A := by omega
  calc A₀ * (M + A + v) = A₀ * (M + A) + A₀ * v * 1 := by ring
    _ ≤ A₀ * (M + A) + A₀ * v * (M + A) := Nat.add_le_add_left (Nat.mul_le_mul_left _ hMA) _
    _ < A₀ * (M + A) + A₀ * v * (M + A) + (M + A) := by omega
    _ = A * (M + A) := by rw [hA]; ring
    _ ≤ (M + 1) * (A + 1) := by nlinarith
    _ ≤ 2 ^ M * 2 ^ A := Nat.mul_le_mul h2 h1
    _ = 2 ^ (M + A) := (pow_add 2 M A).symm
    _ ≤ q ^ (M + A) := Nat.pow_le_pow_left hq _

theorem eq_zero_of_natCast_mul_eq_zero [Module.Free 𝓞 R] {p : ℕ} (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {a : R} (h : (p : R) * a = 0) : a = 0 := by
  classical
  let b := Module.Free.chooseBasis 𝓞 R
  have hrepr : ∀ i, b.repr a i = 0 := by
    intro i
    have h1 : b.repr ((p : R) * a) i = 0 := by rw [h, map_zero, Finsupp.zero_apply]
    have h2 : (p : R) * a = (p : 𝓞) • a := by rw [Algebra.smul_def, map_natCast]
    rw [h2, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
    exact (mem_nonZeroDivisors_iff.mp hp).1 _ h1
  have : b.repr a = 0 := Finsupp.ext hrepr
  exact b.repr.map_eq_zero_iff.1 this

theorem eq_zero_of_pow_mul_eq_zero [Module.Free 𝓞 R] {p : ℕ} (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) :
    ∀ (k : ℕ) {a : R}, (p : R) ^ k * a = 0 → a = 0
  | 0, a, h => by simpa using h
  | k + 1, a, h => by
    rw [pow_succ, mul_assoc] at h
    exact eq_zero_of_natCast_mul_eq_zero hp (eq_zero_of_pow_mul_eq_zero hp k h)

end Rside

section Point

variable {𝓞 : Type*} [CommRing 𝓞] {Y : Type*} [CommRing Y] [Algebra 𝓞 Y] {d : ℕ}

noncomputable def box (d n : ℕ) : Finset (Fin d →₀ ℕ) :=
  (Finset.univ : Finset (Fin d → Fin n)).image fun f => Finsupp.equivFunOnFinite.symm fun j => (f j : ℕ)

theorem mem_box {n : ℕ} (m : Fin d →₀ ℕ) : m ∈ box d n ↔ ∀ j, m j < n := by
  constructor
  · intro hm j
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 hm
    simp
  · intro h
    refine Finset.mem_image.2 ⟨fun j => ⟨m j, h j⟩, Finset.mem_univ _, ?_⟩
    ext j; simp

theorem exists_subset_box (T : Finset (Fin d →₀ ℕ)) : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → T ⊆ box d n := by
  classical
  refine ⟨T.sup (fun m => (Finset.univ : Finset (Fin d)).sup m) + 1, fun n hn m hm => ?_⟩
  rw [mem_box]
  intro j
  have h1 : m j ≤ (Finset.univ : Finset (Fin d)).sup m := Finset.le_sup (f := m) (Finset.mem_univ j)
  have h2 : (Finset.univ : Finset (Fin d)).sup m ≤ T.sup fun m => (Finset.univ : Finset (Fin d)).sup m :=
    Finset.le_sup (f := fun m : Fin d →₀ ℕ => (Finset.univ : Finset (Fin d)).sup m) hm
  omega

noncomputable def lowDeg (d D : ℕ) : Finset (Fin d →₀ ℕ) := (box d D).filter fun m => m.degree < D

theorem mem_lowDeg {D : ℕ} (m : Fin d →₀ ℕ) : m ∈ lowDeg d D ↔ m.degree < D := by
  rw [lowDeg, Finset.mem_filter, mem_box]
  exact ⟨fun h => h.2, fun h => ⟨fun j => lt_of_le_of_lt (Finsupp.le_degree j m) h, h⟩⟩

theorem aeval_eq_psum_box {n : ℕ} {S : MvPowerSeries (Fin d) 𝓞} (P : MvPolynomial (Fin d) 𝓞)
    (hP : ∀ m : Fin d →₀ ℕ, P.coeff m = if ∀ j, m j < n then coeff m S else 0) (w' : Fin d → Y) :
    MvPolynomial.aeval w' P = psum w' (box d n) S := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, psum]
  have hsupp : P.support ⊆ box d n := by
    intro m hm
    rw [mem_box]
    by_contra h
    rw [MvPolynomial.mem_support_iff, hP, if_neg h] at hm
    exact hm rfl
  rw [← Finset.sum_subset hsupp]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [hP, if_pos ((mem_box m).1 (hsupp hm)), Algebra.smul_def, Finsupp.prod]
  · intro m hmb hm
    have h0 := hP m
    rw [MvPolynomial.notMem_support_iff.1 hm, if_pos ((mem_box m).1 hmb)] at h0
    rw [← h0, zero_smul]

theorem psum_sub_psum_mem {x : Fin d → Y} {S : MvPowerSeries (Fin d) 𝓞} {I : Ideal 𝓞} {B s : Finset (Fin d →₀ ℕ)}
    (hB : B ⊆ s) (h : ∀ m, m ∉ B → coeff m S ∈ I) :
    psum x s S - psum x B S ∈ I.map (algebraMap 𝓞 Y) := by
  classical
  rw [psum, psum, ← Finset.sum_sdiff hB, add_sub_cancel_right]
  refine Ideal.sum_mem _ fun m hm => ?_
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (h m (Finset.mem_sdiff.1 hm).2))

omit [Algebra 𝓞 Y] in
theorem monom_smul (c : Y) (t : Fin d → Y) (m : Fin d →₀ ℕ) :
    (m.prod fun s e => (c * t s) ^ e) = c ^ m.degree * m.prod fun s e => t s ^ e := by
  classical
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_pow_eq_pow_sum, Finsupp.degree]
  rfl

theorem map_span_pow (p v : ℕ) : (Ideal.span {(p : 𝓞) ^ v}).map (algebraMap 𝓞 Y) = Ideal.span {(p : Y) ^ v} := by
  rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast]

end Point

section Pin

variable {𝓞 : Type*} [CommRing 𝓞] (p : ℕ) {d : ℕ}

open Classical in

noncomputable def Gpin (φi : MvPowerSeries (Fin d) 𝓞) (N : ℕ) : MvPowerSeries (Fin d) 𝓞 := fun m =>
  if m.degree ≤ N then (p : 𝓞) ^ (N - m.degree) * coeff m φi
  else if h : (p : 𝓞) ^ (m.degree - N) ∣ coeff m φi then Classical.choose h else 0

theorem Gpin_spec (φi : MvPowerSeries (Fin d) 𝓞) (N : ℕ) (m : Fin d →₀ ℕ) :
    (m.degree ≤ N → (Gpin p φi N).coeff m = (p : 𝓞) ^ (N - m.degree) * φi.coeff m) ∧
    (N < m.degree → (Gpin p φi N).coeff m * (p : 𝓞) ^ (m.degree - N) = φi.coeff m ∨
      ((Gpin p φi N).coeff m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ φi.coeff m)) := by
  classical
  constructor
  · intro h
    show Gpin p φi N m = _
    rw [Gpin, if_pos h]
  · intro h
    have hn : ¬ m.degree ≤ N := not_le.2 h
    by_cases hd : (p : 𝓞) ^ (m.degree - N) ∣ coeff m φi
    · left
      show Gpin p φi N m * _ = _
      rw [Gpin, if_neg hn, dif_pos hd, mul_comm]
      exact (Classical.choose_spec hd).symm
    · right
      refine ⟨?_, hd⟩
      show Gpin p φi N m = 0
      rw [Gpin, if_neg hn, dif_neg hd]

end Pin

section Main

variable {𝓞 : Type*} [CommRing 𝓞] (p : ℕ) [hp : Fact p.Prime] (hpR : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
  {d : ℕ} (F : MvFormalGroup d 𝓞)
  (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
  (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
    (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
  (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
  (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
  (hφ0 : ∀ i, (φ i).constantCoeff = 0)
  (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
  (hφF : ∀ i, subst Fp (φ i) =
    subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
      subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
  (hφint : ∀ (i j : Fin d) (m : Fin d →₀ ℕ),
    ((m j + 1 : ℕ) : 𝓞) * (φ i).coeff (m + Finsupp.single j 1) ∈ Ideal.span {(p : 𝓞) ^ m.degree})
  (v : ℕ) {Y : Type*} [CommRing Y] [Algebra 𝓞 Y] [Module.Free 𝓞 Y]
  [IsAdicComplete (Ideal.span {(p : Y)}) Y]
  (ŷ : Fin d → Y) (hŷ : ∀ j, ŷ j ∈ (Ideal.span {(p : Y)}).radical)
  (w' : Fin d → Y)
  (hw' : ∀ j, MvFormalGroup.adicEval (Ideal.span {(p : Y)}) ŷ (F.nthSeries (p ^ v) j) = (p : Y) * w' j)
  (hG : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (i : Fin d) (G : MvPowerSeries (Fin d) 𝓞),
    (∀ m : Fin d →₀ ℕ,
      (m.degree ≤ N → G.coeff m = (p : 𝓞) ^ (N - m.degree) * (φ i).coeff m) ∧
      (N < m.degree → G.coeff m * (p : 𝓞) ^ (m.degree - N) = (φ i).coeff m ∨
        (G.coeff m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ (φ i).coeff m))) →
    MvFormalGroup.adicEval (Ideal.span {(p : Y)}) ŷ G ∈ Ideal.span {(p : Y) ^ N})

include hpR hFp hFp0 hφ0 hφT hφF hφint hŷ hw' hG in
theorem main :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (i : Fin d) (P : MvPolynomial (Fin d) 𝓞),
      (∀ m : Fin d →₀ ℕ, P.coeff m = if ∀ j, m j < n then (φ i).coeff m else 0) →
        MvPolynomial.aeval w' P ∈ Ideal.span {(p : Y) ^ v} := by
  classical
  set J : Ideal Y := Ideal.span {(p : Y)} with hJ
  obtain ⟨N₀, hN₀⟩ := hG

  have hex : ∃ e : ℕ, ∀ s : Fin d, ŷ s ^ e ∈ J := by
    have h' : ∀ s : Fin d, ∃ n : ℕ, ŷ s ^ n ∈ J := fun s => hŷ s
    choose e he using h'
    refine ⟨Finset.univ.sup e, fun s => ?_⟩
    obtain ⟨t, ht⟩ : ∃ t, Finset.univ.sup e = e s + t :=
      ⟨_, (Nat.add_sub_cancel' (Finset.le_sup (f := e) (Finset.mem_univ s))).symm⟩
    rw [ht, pow_add]
    exact Ideal.mul_mem_right _ _ (he s)
  obtain ⟨e, he⟩ := hex
  obtain ⟨N₁, hN₁⟩ := exists_N1 (Nat.Prime.two_le hp.out) (d * e) v
  obtain ⟨N₂, hN₂⟩ := exists_N1 (Nat.Prime.two_le hp.out) 1 v

  set B : Finset (Fin d →₀ ℕ) := Finset.univ.biUnion fun i =>
    (Filter.eventually_cofinite.1 (hφT v i)).toFinset with hBdef
  have hB : ∀ m, m ∉ B → ∀ i, coeff m (φ i) ∈ Ideal.span {(p : 𝓞) ^ v} := by
    intro m hm i
    by_contra h
    exact hm (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, (Set.Finite.mem_toFinset _).2 h⟩)

  set N : ℕ := max (max N₀ N₁) (max N₂ (B.sup Finsupp.degree)) with hNdef
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have hNN₁ : N₁ ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
  have hNN₂ : N₂ ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
  have hNB : B.sup Finsupp.degree ≤ N := le_trans (le_max_right _ _) (le_max_right _ _)
  have hNv : N + v < p ^ N := by simpa using hN₂ N hNN₂
  have hBT : B ⊆ lowDeg d (p ^ N) := fun m hm => (mem_lowDeg m).2
    (lt_of_le_of_lt ((Finset.le_sup (f := Finsupp.degree) hm).trans hNB) (Nat.lt_pow_self hp.out.one_lt))
  obtain ⟨n₀, hn₀⟩ := exists_subset_box B
  refine ⟨n₀, fun n hn i P hP => ?_⟩
  set T := lowDeg d (p ^ N) with hTdef
  set G := Gpin p (φ i) N with hGdef
  have hGpin := Gpin_spec p (φ i) N

  have h1 : MvPolynomial.aeval w' P - psum w' T (φ i) ∈ Ideal.span {(p : Y) ^ v} := by
    rw [aeval_eq_psum_box P hP w', ← map_span_pow (𝓞 := 𝓞) (Y := Y) p v,
      show psum w' (box d n) (φ i) - psum w' T (φ i) =
        (psum w' (box d n) (φ i) - psum w' B (φ i)) - (psum w' T (φ i) - psum w' B (φ i)) by ring]
    exact Ideal.sub_mem _ (psum_sub_psum_mem (hn₀ n hn) (fun m hm => hB m hm i))
      (psum_sub_psum_mem hBT (fun m hm => hB m hm i))

  set z : Fin d → Y := fun j => MvFormalGroup.adicEval J ŷ (F.nthSeries (p ^ v) j) with hzdef
  have hz : z = fun j => (p : Y) * w' j := funext hw'
  have hzrad : ∀ j, z j ∈ J.radical := fun j => by
    rw [hz]; exact Ideal.le_radical (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have h2 : (p : Y) ^ N * psum w' T (φ i) = psum z T G := by
    rw [psum, psum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    simp only [hz, monom_smul, Algebra.smul_def]
    have key : (algebraMap 𝓞 Y) ((p : 𝓞) ^ m.degree * coeff m G) = (algebraMap 𝓞 Y) ((p : 𝓞) ^ N * coeff m (φ i)) := by
      rw [pow_degree_mul_coeff_eq hpR (φ i) (hφint i) N G hGpin m ((mem_lowDeg m).1 hm)]
    rw [map_mul, map_mul, map_pow, map_pow, map_natCast] at key
    calc (p : Y) ^ N * (algebraMap 𝓞 Y (coeff m (φ i)) * m.prod fun s e => w' s ^ e)
        = ((p : Y) ^ N * algebraMap 𝓞 Y (coeff m (φ i))) * m.prod fun s e => w' s ^ e := by ring
      _ = ((p : Y) ^ m.degree * algebraMap 𝓞 Y (coeff m G)) * m.prod fun s e => w' s ^ e := by rw [key]
      _ = algebraMap 𝓞 Y (coeff m G) * ((p : Y) ^ m.degree * m.prod fun s e => w' s ^ e) := by ring

  have hH : HasSubst (F.nthSeries (p ^ v)) :=
    hasSubst_of_constantCoeff_zero (MvFormalGroup.constantCoeff_nthSeries F _)
  have h3 : MvFormalGroup.adicEval J ŷ (subst (F.nthSeries (p ^ v)) G) - psum z T G ∈ J ^ (N + v) := by
    rw [MvFormalGroup.adicEval_subst J hŷ hH]
    obtain ⟨T₀, hT₀⟩ := exists_adicEval_sub_psum_mem J hzrad G (N + v)
    have h31 := hT₀ (T₀ ∪ T) Finset.subset_union_left
    have h32 : psum z (T₀ ∪ T) G - psum z T G ∈ J ^ (N + v) := by
      rw [psum, psum, ← Finset.sum_sdiff (Finset.subset_union_right : T ⊆ T₀ ∪ T), add_sub_cancel_right]
      refine Ideal.sum_mem _ fun m hm => ?_
      have hdeg : p ^ N ≤ m.degree := not_lt.1 (fun h => (Finset.mem_sdiff.1 hm).2 ((mem_lowDeg m).2 h))
      simp only [hz, monom_smul, Algebra.smul_def]
      refine Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ ?_)
      exact Ideal.pow_le_pow_right (le_of_lt (lt_of_lt_of_le hNv hdeg))
        (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _)
    have := Ideal.add_mem _ h31 h32
    rwa [sub_add_sub_cancel] at this

  have h4 : MvFormalGroup.adicEval J ŷ (subst (F.nthSeries (p ^ v)) G) ∈ J ^ (N + v) := by
    have hsplit : subst (F.nthSeries (p ^ v)) G = (p : MvPowerSeries (Fin d) 𝓞) ^ v * G +
        (subst (F.nthSeries (p ^ v)) G - (p : MvPowerSeries (Fin d) 𝓞) ^ v * G) := by ring
    rw [hsplit, ← MvFormalGroup.coe_adicEvalAlgHom J hŷ, map_add, map_mul, map_pow, map_natCast,
      MvFormalGroup.coe_adicEvalAlgHom J hŷ]
    refine Ideal.add_mem _ ?_ ?_
    · have hGv := hN₀ N hNN₀ i G hGpin
      rw [hJ, Ideal.span_singleton_pow, pow_add, mul_comm ((p : Y) ^ N), ← Ideal.span_singleton_mul_span_singleton]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hGv
    · refine adicEval_mem_pow J hŷ _ (N + v) fun m => ?_
      rcases lt_or_ge m.degree (p ^ N) with hlt | hge
      · exact Or.inl (coeff_shadow_eq_zero hpR F Fp hFp hFp0 φ hφ0 hφF hφint v N i G hGpin m hlt)
      · right
        obtain ⟨s, hs⟩ := exists_lt_apply m (e * (N + v))
          (by rw [Fintype.card_fin, ← mul_assoc]; exact lt_of_lt_of_le (hN₁ N hNN₁) hge)
        exact prod_pow_mem_pow he m hs

  have h5 : (p : Y) ^ N * psum w' T (φ i) ∈ J ^ (N + v) := by
    rw [h2]
    have := Ideal.sub_mem _ h4 h3
    rwa [sub_sub_cancel] at this
  rw [hJ, Ideal.span_singleton_pow] at h5
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h5
  have h6 : psum w' T (φ i) = b * (p : Y) ^ v := by
    have h0 : (p : Y) ^ N * (psum w' T (φ i) - b * (p : Y) ^ v) = 0 := by
      rw [mul_sub, ← hb]; ring
    exact sub_eq_zero.1 (eq_zero_of_pow_mul_eq_zero hpR N h0)
  have h7 : psum w' T (φ i) ∈ Ideal.span {(p : Y) ^ v} := Ideal.mem_span_singleton'.2 ⟨b, h6.symm⟩
  have := Ideal.add_mem _ h1 h7
  rwa [sub_add_cancel] at this

end Main

end S17L3

set_option autoImplicit false

open MvPowerSeries

universe u w

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))

    (hφint : ∀ (i j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * (φ i).coeff (m + Finsupp.single j 1) ∈ Ideal.span {(p : 𝓞) ^ m.degree})
    (v : ℕ)
    (Y : Type w) [CommRing Y] [Algebra 𝓞 Y] [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y]
    [IsAdicComplete (Ideal.span {(p : Y)}) Y]
    (ŷ : Fin d → Y) (hŷ : ∀ j, ŷ j ∈ (Ideal.span {(p : Y)}).radical)
    (w' : Fin d → Y)
    (hw' : ∀ j, MvFormalGroup.adicEval (Ideal.span {(p : Y)}) ŷ (F.nthSeries (p ^ v) j) = (p : Y) * w' j)
    (hG : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (i : Fin d) (G : MvPowerSeries (Fin d) 𝓞),
      (∀ m : Fin d →₀ ℕ,
        (m.degree ≤ N → G.coeff m = (p : 𝓞) ^ (N - m.degree) * (φ i).coeff m) ∧
        (N < m.degree → G.coeff m * (p : 𝓞) ^ (m.degree - N) = (φ i).coeff m ∨
          (G.coeff m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ (φ i).coeff m))) →
      MvFormalGroup.adicEval (Ideal.span {(p : Y)}) ŷ G ∈ Ideal.span {(p : Y) ^ N}) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (i : Fin d) (P : MvPolynomial (Fin d) 𝓞),
      (∀ m : Fin d →₀ ℕ, P.coeff m = if ∀ j, m j < n then (φ i).coeff m else 0) →
        MvPolynomial.aeval w' P ∈ Ideal.span {(p : Y) ^ v} :=
  S17L3.main p hp F Fp hFp hFp0 φ hφ0 hφT hφF hφint v ŷ hŷ w' hw' hG

end S_MvFormalGroup_eventually_aeval_boxTrunc_mem_of_forall_adicEval_scaledLogTrunc_mem
end P2MW
export P2MW.S_MvFormalGroup_eventually_aeval_boxTrunc_mem_of_forall_adicEval_scaledLogTrunc_mem (solution)
