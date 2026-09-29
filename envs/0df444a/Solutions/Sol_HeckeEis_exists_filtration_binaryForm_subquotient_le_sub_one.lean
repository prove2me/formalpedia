-- Prove2me | solution 1 for HeckeEis.exists_filtration_binaryForm_subquotient_le_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/40ce66d7-9711-5d31-bb80-cdc08dccf918

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Theorems.Thm_HeckeEis_exists_binaryForm_eq_mul_of_forall_eval_eq_zero
import Theorems.Thm_HeckeEis_exists_dividedDeriv_binaryFormRep_eq_det_pow_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_filtration_binaryForm_subquotient_le_sub_one

set_option autoImplicit false

namespace ATHRFilt

open MvPolynomial HeckeEis Finset

section Monomials

variable (K : Type*) [Field K]

noncomputable def e (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

@[scoped simp] theorem e_zero (i j : ℕ) : e i j 0 = i := by simp [e]

@[scoped simp] theorem e_one (i j : ℕ) : e i j 1 = j := by simp [e]

theorem e_eq_iff {i j i' j' : ℕ} : e i j = e i' j' ↔ i = i' ∧ j = j' := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun f : Fin 2 →₀ ℕ => f 0) h,
      by simpa using congrArg (fun f : Fin 2 →₀ ℕ => f 1) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem eq_e (d : Fin 2 →₀ ℕ) : d = e (d 0) (d 1) := by
  ext k
  fin_cases k <;> simp

theorem e_le_iff {i j i' j' : ℕ} : e i j ≤ e i' j' ↔ i ≤ i' ∧ j ≤ j' := by
  rw [Finsupp.le_def]
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1⟩
  · rintro ⟨h0, h1⟩ k
    fin_cases k <;> simpa

theorem degree_e (i j : ℕ) : Finsupp.degree (e i j) = i + j := by
  rw [e, map_add, Finsupp.degree_single, Finsupp.degree_single]

theorem monomial_e (i j : ℕ) (c : K) :
    (monomial (e i j) c : MvPolynomial (Fin 2) K) = C c * X 0 ^ i * X 1 ^ j := by
  rw [e, mul_assoc, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, C_mul_monomial, one_mul, mul_one]

theorem isHomogeneous_monomial_e (i j : ℕ) (c : K) :
    ((monomial (e i j) c : MvPolynomial (Fin 2) K)).IsHomogeneous (i + j) :=
  isHomogeneous_monomial _ (degree_e i j)

theorem monomial_e_mem {i j n : ℕ} (h : i + j = n) (c : K) :
    (monomial (e i j) c : MvPolynomial (Fin 2) K) ∈ BinaryForm K n := by
  rw [MvPolynomial.mem_homogeneousSubmodule, ← h]
  exact isHomogeneous_monomial_e K i j c

theorem deg_two {F : MvPolynomial (Fin 2) K} {n : ℕ} (hF : F.IsHomogeneous n) {d : Fin 2 →₀ ℕ}
    (hd : coeff d F ≠ 0) : d 0 + d 1 = n := by
  have hdeg := hF hd
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at hdeg
  simpa only [Pi.one_apply, smul_eq_mul, mul_one, Fin.sum_univ_two] using hdeg

theorem isHomogeneous_coe {n : ℕ} (F : ↥(BinaryForm K n)) :
    (F : MvPolynomial (Fin 2) K).IsHomogeneous n :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mp F.2

theorem eq_sum_monomial {F : MvPolynomial (Fin 2) K} {n : ℕ} (hF : F.IsHomogeneous n) :
    F = ∑ i ∈ range (n + 1), monomial (e i (n - i)) (coeff (e i (n - i)) F) := by
  classical
  ext d
  rw [coeff_sum]
  simp only [coeff_monomial]
  by_cases hd : coeff d F = 0
  · rw [hd]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with h
    · rw [← h] at hd
      exact hd
    · rfl
  · have hdeg := deg_two K hF hd
    rw [Finset.sum_eq_single (d 0)]
    · have h : e (d 0) (n - d 0) = d := by
        conv_rhs => rw [eq_e d]
        rw [e_eq_iff]
        exact ⟨rfl, by omega⟩
      rw [if_pos h, h]
    · intro i _ hne
      rw [if_neg]
      intro h
      apply hne
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
      simpa using this
    · intro h
      exfalso
      simp only [mem_range] at h
      omega

theorem coeff_monomial_e_e (i j i' j' : ℕ) (c : K) :
    coeff (e i' j') (monomial (e i j) c : MvPolynomial (Fin 2) K) = if i = i' ∧ j = j' then c else 0 := by
  classical
  rw [coeff_monomial]
  simp only [e_eq_iff]

end Monomials

section Eval

variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p]

noncomputable def ev (F : MvPolynomial (Fin 2) K) (v : Fin 2 → ZMod p) : K :=
  eval (fun i => ZMod.castHom (dvd_refl p) K (v i)) F

theorem ev_add (F G : MvPolynomial (Fin 2) K) (v : Fin 2 → ZMod p) :
    ev p K (F + G) v = ev p K F v + ev p K G v := by
  simp [ev]

theorem ev_sub (F G : MvPolynomial (Fin 2) K) (v : Fin 2 → ZMod p) :
    ev p K (F - G) v = ev p K F v - ev p K G v := by
  simp [ev]

theorem ev_mul (F G : MvPolynomial (Fin 2) K) (v : Fin 2 → ZMod p) :
    ev p K (F * G) v = ev p K F v * ev p K G v := by
  simp [ev]

theorem ev_smul (c : K) (F : MvPolynomial (Fin 2) K) (v : Fin 2 → ZMod p) :
    ev p K (c • F) v = c * ev p K F v := by
  simp [ev, smul_eval]

theorem ev_zero (v : Fin 2 → ZMod p) : ev p K 0 v = 0 := by simp [ev]

theorem ev_sum {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial (Fin 2) K) (v : Fin 2 → ZMod p) :
    ev p K (∑ i ∈ s, F i) v = ∑ i ∈ s, ev p K (F i) v := by
  simp [ev, map_sum]

theorem ev_monomial (i j : ℕ) (c : K) (v : Fin 2 → ZMod p) :
    ev p K (monomial (e i j) c) v =
      c * (ZMod.castHom (dvd_refl p) K (v 0)) ^ i * (ZMod.castHom (dvd_refl p) K (v 1)) ^ j := by
  rw [monomial_e]
  simp [ev]

theorem ev_binarySubst (M : Matrix (Fin 2) (Fin 2) ℤ) (F : MvPolynomial (Fin 2) K)
    (v : Fin 2 → ZMod p) :
    ev p K (binarySubst K M F) v = ev p K F (fun j => ∑ i : Fin 2, v i * ((M i j : ℤ) : ZMod p)) := by
  unfold ev binarySubst
  rw [MvPolynomial.aeval_eq_bind₁]
  change eval₂Hom (RingHom.id K) _ (bind₁ _ F) = eval₂Hom (RingHom.id K) _ F
  rw [eval₂Hom_bind₁]
  have hfun : (fun j => eval₂Hom (RingHom.id K) (fun i => ZMod.castHom (dvd_refl p) K (v i))
      (∑ i : Fin 2, C ((M i j : ℤ) : K) * X i))
      = fun j => ZMod.castHom (dvd_refl p) K (∑ i : Fin 2, v i * ((M i j : ℤ) : ZMod p)) := by
    funext j
    simp [Fin.sum_univ_two, map_add, map_mul, mul_comm]
  rw [hfun]

theorem castHom_pow_card (x : ZMod p) :
    (ZMod.castHom (dvd_refl p) K x) ^ p = ZMod.castHom (dvd_refl p) K x := by
  rw [← map_pow, ZMod.pow_card]

theorem pow_add_mul_sub_one {x : K} (hx : x ^ p = x) {j : ℕ} (hj : 1 ≤ j) (q : ℕ) :
    x ^ (j + q * (p - 1)) = x ^ j := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.out.one_le
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    calc x ^ (j' + 1 + (q + 1) * (p - 1))
        = x ^ (j' + 1 + q * (p - 1)) * x ^ (p - 1) := by rw [← pow_add]; congr 1; ring
      _ = x ^ j' * (x ^ (p - 1) * x) := by rw [ih]; ring
      _ = x ^ (j' + 1) := by rw [← pow_succ, hp1, hx, pow_succ]

theorem pow_eq_pow_of_dvd_sub {x : K} (hx : x ^ p = x) {m m' : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (h : ((p - 1 : ℕ) : ℤ) ∣ (m : ℤ) - (m' : ℤ)) : x ^ m = x ^ m' := by
  have hmod : m' ≡ m [MOD (p - 1)] := Nat.modEq_iff_dvd.mpr h
  have hmod' : m' - 1 ≡ m - 1 [MOD (p - 1)] := by
    refine Nat.ModEq.add_right_cancel' 1 ?_
    rwa [Nat.sub_add_cancel hm', Nat.sub_add_cancel hm]
  have hred : ∀ k, 1 ≤ k → x ^ k = x ^ (1 + (k - 1) % (p - 1)) := by
    intro k hk
    have hk' : k = 1 + (k - 1) % (p - 1) + (k - 1) / (p - 1) * (p - 1) := by
      have := Nat.div_add_mod' (k - 1) (p - 1)
      omega
    conv_lhs => rw [hk']
    exact pow_add_mul_sub_one p K hx (by omega) _
  rw [hred m hm, hred m' hm']
  congr 2
  exact hmod'.symm

noncomputable def theta : MvPolynomial (Fin 2) K := X 0 ^ p * X 1 - X 0 * X 1 ^ p

theorem theta_eq : theta p K = monomial (e p 1) 1 - monomial (e 1 p) 1 := by
  rw [theta, monomial_e, monomial_e]
  simp

theorem isHomogeneous_theta : (theta p K).IsHomogeneous (p + 1) := by
  rw [theta_eq]
  refine (isHomogeneous_monomial_e K p 1 1).sub ?_
  rw [add_comm]
  exact isHomogeneous_monomial_e K 1 p 1

theorem coeff_theta_e_p_one : coeff (e p 1) (theta p K) = 1 := by
  rw [theta_eq, coeff_sub, coeff_monomial_e_e, coeff_monomial_e_e, if_pos ⟨rfl, rfl⟩, if_neg, sub_zero]
  rintro ⟨h, -⟩
  exact hp.out.one_lt.ne h

theorem theta_ne_zero : theta p K ≠ 0 := by
  intro h
  have := coeff_theta_e_p_one p K
  rw [h, coeff_zero] at this
  exact zero_ne_one this

theorem ev_theta (v : Fin 2 → ZMod p) : ev p K (theta p K) v = 0 := by
  simp only [theta, ev, map_sub, map_mul, map_pow, eval_X, castHom_pow_card]
  ring

theorem binarySubst_theta (M : Matrix (Fin 2) (Fin 2) ℤ) :
    binarySubst K M (theta p K) = ((M.det : ℤ) : K) • theta p K := by
  have hfrob : ∀ m : ℤ, (C ((m : ℤ) : K) : MvPolynomial (Fin 2) K) ^ p = C ((m : ℤ) : K) := by
    intro m
    rw [← map_pow]
    congr 1
    have h := map_intCast (frobenius K p) m
    rwa [frobenius_def] at h
  unfold theta
  simp only [map_sub, map_mul, map_pow, HeckeEis.binarySubst_X, Fin.sum_univ_two]
  rw [add_pow_char, add_pow_char, mul_pow, mul_pow, mul_pow, mul_pow, hfrob, hfrob, hfrob, hfrob,
    Matrix.det_fin_two, MvPolynomial.smul_eq_C_mul]
  simp only [Int.cast_sub, Int.cast_mul, map_sub, map_mul]
  ring

theorem exists_eq_theta_mul {n : ℕ} {F : MvPolynomial (Fin 2) K} (hF : F.IsHomogeneous n)
    (hvan : ∀ v, ev p K F v = 0) :
    ∃ H : MvPolynomial (Fin 2) K, H.IsHomogeneous (n - (p + 1)) ∧ F = theta p K * H := by
  obtain ⟨H, hH, hFH⟩ := HeckeEis.exists_binaryForm_eq_mul_of_forall_eval_eq_zero p K n F
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr hF) hvan
  exact ⟨H, (MvPolynomial.mem_homogeneousSubmodule _ _).mp hH, hFH⟩

def rd (i : ℕ) : ℕ := 1 + (i - 1) % (p - 1)

theorem one_le_rd (i : ℕ) : 1 ≤ rd p i := Nat.le_add_right _ _

theorem rd_le (i : ℕ) : rd p i ≤ p - 1 := by
  have h1 : 0 < p - 1 := by have := hp.out.two_le; omega
  have := Nat.mod_lt (i - 1) h1
  unfold rd
  omega

theorem rd_le_self {i : ℕ} (hi : 1 ≤ i) : rd p i ≤ i := by
  have := Nat.mod_le (i - 1) (p - 1)
  unfold rd
  omega

theorem rd_spec {i : ℕ} (hi : 1 ≤ i) : i = rd p i + (i - 1) / (p - 1) * (p - 1) := by
  have := Nat.div_add_mod' (i - 1) (p - 1)
  unfold rd
  omega

theorem rd_eq_self_of_lt {i : ℕ} (hi : 1 ≤ i) (hip : i < p) : rd p i = i := by
  unfold rd
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem eq_zero_of_ev_eq_zero {n : ℕ} (hn : n ≤ p) {F : MvPolynomial (Fin 2) K} (hF : F.IsHomogeneous n)
    (hvan : ∀ v, ev p K F v = 0) : F = 0 := by
  obtain ⟨H, hH, hFH⟩ := exists_eq_theta_mul p K hF hvan
  by_contra hne
  have h1 : F.IsHomogeneous (p + 1 + (n - (p + 1))) := hFH ▸ (isHomogeneous_theta p K).mul hH
  have := hF.inj_right h1 hne
  omega

end Eval

section Remap

variable (K : Type*) [Field K]

noncomputable def remap (S : Finset ℕ) (n : ℕ) (w : ℕ → K) (g h : ℕ → ℕ) :
    MvPolynomial (Fin 2) K →ₗ[K] MvPolynomial (Fin 2) K :=
  ∑ i ∈ S, (lcoeff K (e i (n - i))).smulRight (monomial (e (g i) (h i)) (w i))

theorem remap_apply (S : Finset ℕ) (n : ℕ) (w : ℕ → K) (g h : ℕ → ℕ) (F : MvPolynomial (Fin 2) K) :
    remap K S n w g h F = ∑ i ∈ S, monomial (e (g i) (h i)) (coeff (e i (n - i)) F * w i) := by
  rw [remap, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smulRight_apply, lcoeff_apply, smul_monomial, smul_eq_mul]

theorem remap_mem {S : Finset ℕ} {n : ℕ} {w : ℕ → K} {g h : ℕ → ℕ} {m : ℕ}
    (hgh : ∀ i ∈ S, g i + h i = m) (F : MvPolynomial (Fin 2) K) :
    remap K S n w g h F ∈ BinaryForm K m := by
  rw [remap_apply]
  exact Submodule.sum_mem _ fun i hi => monomial_e_mem K (hgh i hi) _

theorem remap_monomial (S : Finset ℕ) (n : ℕ) (w : ℕ → K) (g h : ℕ → ℕ) (i : ℕ) :
    remap K S n w g h (monomial (e i (n - i)) 1)
      = if i ∈ S then monomial (e (g i) (h i)) (w i) else 0 := by
  classical
  rw [remap_apply]
  simp only [coeff_monomial_e_e]
  split_ifs with hi
  · rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [if_neg, zero_mul, map_zero]
      rintro ⟨h1, -⟩
      exact hji h1.symm
    · intro h
      exact absurd hi h
  · refine Finset.sum_eq_zero fun j hj => ?_
    rw [if_neg, zero_mul, map_zero]
    rintro ⟨h1, -⟩
    rw [h1] at hi
    exact hi hj

theorem coeff_remap (S : Finset ℕ) (n : ℕ) (w : ℕ → K) (g h : ℕ → ℕ) (F : MvPolynomial (Fin 2) K)
    (s t : ℕ) :
    coeff (e s t) (remap K S n w g h F)
      = ∑ i ∈ S with (g i = s ∧ h i = t), coeff (e i (n - i)) F * w i := by
  classical
  rw [remap_apply, coeff_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_monomial_e_e]

noncomputable def remapB (S : Finset ℕ) (n m : ℕ) (w : ℕ → K) (g h : ℕ → ℕ)
    (hgh : ∀ i ∈ S, g i + h i = m) : ↥(BinaryForm K n) →ₗ[K] ↥(BinaryForm K m) :=
  LinearMap.codRestrict (BinaryForm K m) ((remap K S n w g h).comp (BinaryForm K n).subtype)
    fun F => remap_mem K hgh _

@[scoped simp] theorem coe_remapB (S : Finset ℕ) (n m : ℕ) (w : ℕ → K) (g h : ℕ → ℕ)
    (hgh : ∀ i ∈ S, g i + h i = m) (F : ↥(BinaryForm K n)) :
    ((remapB K S n m w g h hgh F : ↥(BinaryForm K m)) : MvPolynomial (Fin 2) K)
      = remap K S n w g h F :=
  rfl

noncomputable def bm (n i : ℕ) : ↥(BinaryForm K n) :=
  if h : i ≤ n then ⟨monomial (e i (n - i)) 1, monomial_e_mem K (by omega) 1⟩ else 0

theorem coe_bm {n i : ℕ} (h : i ≤ n) :
    ((bm K n i : ↥(BinaryForm K n)) : MvPolynomial (Fin 2) K) = monomial (e i (n - i)) 1 := by
  rw [bm, dif_pos h]

theorem eq_sum_bm {n : ℕ} (F : ↥(BinaryForm K n)) :
    F = ∑ i ∈ range (n + 1), coeff (e i (n - i)) (F : MvPolynomial (Fin 2) K) • bm K n i := by
  refine Subtype.ext ?_
  rw [Submodule.coe_sum]
  conv_lhs => rw [eq_sum_monomial K (isHomogeneous_coe K F)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
  rw [Submodule.coe_smul, coe_bm K hin, smul_monomial, smul_eq_mul, mul_one]

end Remap

section Maps

variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p]

noncomputable def dmap (a : ℕ) : MvPolynomial (Fin 2) K →ₗ[K] MvPolynomial (Fin 2) K :=
  remap K (Ico a p) (a + (p - 1)) (fun i => (i.descFactorial a : K)) (fun i => i - a) (fun i => p - 1 - i)

theorem dmap_mem (a : ℕ) (F : MvPolynomial (Fin 2) K) : dmap p K a F ∈ BinaryForm K (p - 1 - a) :=
  remap_mem K (fun i hi => by simp only [mem_Ico] at hi; omega) F

theorem dmap_monomial (a i : ℕ) :
    dmap p K a (monomial (e i (a + (p - 1) - i)) 1)
      = if a ≤ i ∧ i < p then monomial (e (i - a) (p - 1 - i)) (i.descFactorial a : K) else 0 := by
  rw [dmap, remap_monomial]
  simp only [mem_Ico]

theorem cast_descFactorial_eq_zero {a i : ℕ} (hpi : p ≤ i) (hi : i < p + a) :
    ((i.descFactorial a : ℕ) : K) = 0 := by
  apply (CharP.cast_eq_zero_iff K p _).mpr
  rw [Nat.descFactorial_eq_prod_range]
  have hmem : i - p ∈ range a := by simp; omega
  have h := Finset.dvd_prod_of_mem (fun t => i - t) hmem
  beta_reduce at h
  rwa [show i - (i - p) = p by omega] at h

theorem cast_descFactorial_ne_zero {a i : ℕ} (hai : a ≤ i) (hip : i < p) :
    ((i.descFactorial a : ℕ) : K) ≠ 0 := by
  intro h
  have hdvd := (CharP.cast_eq_zero_iff K p _).mp h
  have h1 : i.descFactorial a ∣ i.factorial := ⟨(i - a).factorial, by
    rw [mul_comm]; exact (Nat.factorial_mul_descFactorial hai).symm⟩
  have := (Nat.Prime.dvd_factorial hp.out).mp (hdvd.trans h1)
  omega

theorem dmap_theta_mul (a : ℕ) (J : MvPolynomial (Fin 2) K) : dmap p K a (theta p K * J) = 0 := by
  rw [dmap, remap_apply]
  refine sum_eq_zero fun i hi => ?_
  simp only [mem_Ico] at hi
  have : coeff (e i (a + (p - 1) - i)) (theta p K * J) = 0 := by
    rw [theta_eq, sub_mul, coeff_sub, coeff_monomial_mul', coeff_monomial_mul', if_neg, if_neg, sub_zero]
    · rw [e_le_iff]; omega
    · rw [e_le_iff]; omega
  rw [this, zero_mul, map_zero]

noncomputable def Dsel (a : ℕ) : ↥(BinaryForm K (a + (p - 1))) →ₗ[K] ↥(BinaryForm K (p - 1 - a)) :=
  Classical.choose (HeckeEis.exists_dividedDeriv_binaryFormRep_eq_det_pow_smul p K a)

theorem coe_Dsel (a : ℕ) (F : ↥(BinaryForm K (a + (p - 1)))) :
    ((Dsel p K a F : ↥(BinaryForm K (p - 1 - a))) : MvPolynomial (Fin 2) K) = dmap p K a F := by
  have h := (Classical.choose_spec (HeckeEis.exists_dividedDeriv_binaryFormRep_eq_det_pow_smul p K a)).1 F
  unfold Dsel
  rw [h, dmap, remap_apply]
  rfl

theorem Dsel_equivar (a : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) (F : ↥(BinaryForm K (a + (p - 1)))) :
    Dsel p K a (binaryFormRep K _ M F) = (((M.det : ℤ) : K) ^ a) • binaryFormRep K _ M (Dsel p K a F) :=
  (Classical.choose_spec (HeckeEis.exists_dividedDeriv_binaryFormRep_eq_det_pow_smul p K a)).2.2 M F

theorem ev_coe_eq_sum {n : ℕ} (F : ↥(BinaryForm K n)) (v : Fin 2 → ZMod p) :
    ev p K F v = ∑ i ∈ range (n + 1), coeff (e i (n - i)) (F : MvPolynomial (Fin 2) K)
      * (ZMod.castHom (dvd_refl p) K (v 0)) ^ i * (ZMod.castHom (dvd_refl p) K (v 1)) ^ (n - i) := by
  conv_lhs => rw [eq_sum_monomial K (isHomogeneous_coe K F)]
  rw [ev_sum]
  simp only [ev_monomial]

theorem ev_remap (S : Finset ℕ) (n : ℕ) (w : ℕ → K) (g h : ℕ → ℕ) (F : MvPolynomial (Fin 2) K)
    (v : Fin 2 → ZMod p) :
    ev p K (remap K S n w g h F) v = ∑ i ∈ S, coeff (e i (n - i)) F * w i
      * (ZMod.castHom (dvd_refl p) K (v 0)) ^ (g i) * (ZMod.castHom (dvd_refl p) K (v 1)) ^ (h i) := by
  rw [remap_apply, ev_sum]
  simp only [ev_monomial]

theorem pow_rd {x : K} (hx : x ^ p = x) {i : ℕ} (hi : 1 ≤ i) : x ^ i = x ^ rd p i := by
  conv_lhs => rw [rd_spec p hi]
  exact pow_add_mul_sub_one p K hx (one_le_rd p i) _

theorem pow_rd_add {x : K} (hx : x ^ p = x) {i : ℕ} (hi : 1 ≤ i) : x ^ i = x ^ (rd p i + (p - 1)) := by
  rw [pow_rd p K hx hi, ← pow_add_mul_sub_one p K hx (one_le_rd p i) 1, one_mul]

theorem pow_sub_eq_pow {y : K} (hy : y ^ p = y) {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    y ^ (n - i) = y ^ (rd p n + (p - 1) - rd p i) := by
  have hrdi := rd_le p i
  have hrdn := one_le_rd p n
  have hp1 : 1 ≤ p := hp.out.one_le
  refine pow_eq_pow_of_dvd_sub p K hy (by omega) (by omega) ?_
  have hn := rd_spec p (show 1 ≤ n by omega)
  have hi' := rd_spec p hi
  set P : ℕ := p - 1 with hP
  set qn := (n - 1) / P
  set qi := (i - 1) / P
  refine ⟨(qn : ℤ) - qi - 1, ?_⟩
  have e1 : ((n - i : ℕ) : ℤ) = (n : ℤ) - (i : ℤ) := Nat.cast_sub hin.le
  have e2 : ((rd p n + P - rd p i : ℕ) : ℤ) = ((rd p n + P : ℕ) : ℤ) - (rd p i : ℤ) := Nat.cast_sub (by omega)
  have e3 : (n : ℤ) = (rd p n : ℤ) + (qn : ℤ) * (P : ℤ) := by exact_mod_cast hn
  have e4 : (i : ℤ) = (rd p i : ℤ) + (qi : ℤ) * (P : ℤ) := by exact_mod_cast hi'
  rw [e1, e2]
  push_cast
  linear_combination e3 - e4

def gR (n i : ℕ) : ℕ := if i = 0 then 0 else if i = n then rd p n + (p - 1) else rd p i

theorem gR_le (n i : ℕ) : gR p n i ≤ rd p n + (p - 1) := by
  unfold gR
  split_ifs
  · exact Nat.zero_le _
  · exact le_rfl
  · have := rd_le p i
    omega

noncomputable def R (n : ℕ) : ↥(BinaryForm K n) →ₗ[K] ↥(BinaryForm K (rd p n + (p - 1))) :=
  remapB K (range (n + 1)) n (rd p n + (p - 1)) (fun _ => 1) (gR p n)
    (fun i => rd p n + (p - 1) - gR p n i) (fun i _ => by have := gR_le p n i; omega)

noncomputable def T (n : ℕ) : ↥(BinaryForm K n) →ₗ[K] ↥(BinaryForm K (p - 1 - rd p n)) :=
  (Dsel p K (rd p n)).comp (R p K n)

def good (n i : ℕ) : Prop := i = 0 ∨ i = n ∨ rd p i < rd p n

scoped instance (n : ℕ) : DecidablePred (good p n) := fun i => by
  unfold good
  infer_instance

def gL (n i : ℕ) : ℕ := if i = 0 then 0 else if i = n then rd p n else rd p i

theorem gL_le {n i : ℕ} (h : good p n i) : gL p n i ≤ rd p n := by
  unfold gL
  unfold good at h
  split_ifs with h0 hn
  · exact Nat.zero_le _
  · exact le_rfl
  · omega

noncomputable def L (n : ℕ) : ↥(BinaryForm K n) →ₗ[K] ↥(BinaryForm K (rd p n)) :=
  remapB K ((range (n + 1)).filter (good p n)) n (rd p n) (fun _ => 1) (gL p n)
    (fun i => rd p n - gL p n i) (fun i hi => by
      have := gL_le p (n := n) (i := i) (Finset.mem_filter.mp hi).2
      omega)

theorem ev_R {n : ℕ} (hn : 1 ≤ n) (F : ↥(BinaryForm K n)) (v : Fin 2 → ZMod p) :
    ev p K (R p K n F : ↥(BinaryForm K _)) v = ev p K F v := by
  have hx := castHom_pow_card p K (v 0)
  have hy := castHom_pow_card p K (v 1)
  rw [R, coe_remapB, ev_remap, ev_coe_eq_sum]
  refine sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
  rw [mul_one]
  unfold gR
  split_ifs with h0 hn'
  · subst h0
    rw [Nat.sub_zero, Nat.sub_zero, ← pow_rd_add p K hy hn]
  · subst hn'
    rw [Nat.sub_self, Nat.sub_self, ← pow_rd_add p K hx hn]
  · rw [← pow_rd p K hx (i := i) (by omega), ← pow_sub_eq_pow p K hy (n := n) (i := i) (by omega) (by omega)]

theorem exists_R_rep_sub {n : ℕ} (hn : 1 ≤ n) (M : Matrix (Fin 2) (Fin 2) ℤ) (F : ↥(BinaryForm K n)) :
    ∃ J : MvPolynomial (Fin 2) K,
      ((R p K n (binaryFormRep K n M F) : ↥(BinaryForm K _)) : MvPolynomial (Fin 2) K)
        - binarySubst K M (R p K n F : ↥(BinaryForm K _)) = theta p K * J := by
  set G : ↥(BinaryForm K (rd p n + (p - 1))) :=
    R p K n (binaryFormRep K n M F) - binaryFormRep K _ M (R p K n F) with hG
  have hGv : ∀ v, ev p K (G : MvPolynomial (Fin 2) K) v = 0 := by
    intro v
    rw [hG, Submodule.coe_sub, ev_sub, binaryFormRep_apply_coe, ev_binarySubst, ev_R p K hn, ev_R p K hn,
      binaryFormRep_apply_coe, ev_binarySubst, sub_self]
  obtain ⟨H, -, hH⟩ := exists_eq_theta_mul p K (isHomogeneous_coe K G) hGv
  exact ⟨H, hH⟩

theorem T_equivar {n : ℕ} (hn : 1 ≤ n) (M : Matrix (Fin 2) (Fin 2) ℤ) (F : ↥(BinaryForm K n)) :
    T p K n (binaryFormRep K n M F) = (((M.det : ℤ) : K) ^ rd p n) • binaryFormRep K _ M (T p K n F) := by
  obtain ⟨J, hJ⟩ := exists_R_rep_sub p K hn M F
  have hmem : theta p K * J ∈ BinaryForm K (rd p n + (p - 1)) := by
    rw [← hJ]
    exact Submodule.sub_mem _ (Subtype.mem _) (binarySubst_mem K M (Subtype.mem _))
  have hsplit : R p K n (binaryFormRep K n M F)
      = binaryFormRep K _ M (R p K n F) + ⟨theta p K * J, hmem⟩ := by
    refine Subtype.ext ?_
    rw [Submodule.coe_add, binaryFormRep_apply_coe]
    linear_combination hJ
  have h0 : Dsel p K (rd p n) ⟨theta p K * J, hmem⟩ = 0 :=
    Subtype.ext (by rw [coe_Dsel, Submodule.coe_zero]; exact dmap_theta_mul p K _ J)
  rw [T, LinearMap.comp_apply, hsplit, map_add, Dsel_equivar, h0, add_zero]
  rfl

theorem coe_T (n : ℕ) (F : ↥(BinaryForm K n)) :
    ((T p K n F : ↥(BinaryForm K _)) : MvPolynomial (Fin 2) K)
      = dmap p K (rd p n) (R p K n F : ↥(BinaryForm K _)) := by
  rw [T, LinearMap.comp_apply, coe_Dsel]

theorem coe_T_bm {n i : ℕ} (hi : i ≤ n) :
    ((T p K n (bm K n i) : ↥(BinaryForm K _)) : MvPolynomial (Fin 2) K)
      = if rd p n ≤ gR p n i ∧ gR p n i < p
        then monomial (e (gR p n i - rd p n) (p - 1 - gR p n i)) ((gR p n i).descFactorial (rd p n) : K)
        else 0 := by
  rw [coe_T, R, coe_remapB, coe_bm K hi, remap_monomial, if_pos (by simp; omega), dmap_monomial]

theorem sum_fiber_eq_zero_of_T_eq_zero {n : ℕ} (F : ↥(BinaryForm K n)) (hT : T p K n F = 0)
    {j : ℕ} (haj : rd p n ≤ j) (hjp : j < p) :
    ∑ i ∈ range (n + 1) with gR p n i = j, coeff (e i (n - i)) (F : MvPolynomial (Fin 2) K) = 0 := by
  have h := congrArg (fun G : ↥(BinaryForm K (p - 1 - rd p n)) =>
    coeff (e (j - rd p n) (p - 1 - j)) (G : MvPolynomial (Fin 2) K)) hT
  simp only [Submodule.coe_zero, coeff_zero] at h
  rw [coe_T, dmap, coeff_remap, Finset.sum_eq_single_of_mem j] at h
  · rw [R, coe_remapB, coeff_remap] at h
    have hne := cast_descFactorial_ne_zero p K haj hjp
    have h' := (mul_eq_zero.mp h).resolve_right hne
    rw [← h']
    refine sum_congr ?_ fun i _ => (mul_one _).symm
    refine Finset.filter_congr fun i _ => ⟨fun h => ⟨h, by rw [h]⟩, fun h => h.1⟩
  · simp [mem_filter, mem_Ico, haj, hjp]
  · intro i hi hij
    exfalso
    simp only [mem_filter, mem_Ico] at hi
    omega

theorem ev_L {n : ℕ} (hn : p ≤ n) (F : ↥(BinaryForm K n)) (hT : T p K n F = 0) (v : Fin 2 → ZMod p) :
    ev p K (L p K n F : ↥(BinaryForm K _)) v = ev p K F v := by
  classical
  have hx := castHom_pow_card p K (v 0)
  have hy := castHom_pow_card p K (v 1)
  have hp2 := hp.out.two_le
  have hn1 : 1 ≤ n := by omega
  have hrdn1 := one_le_rd p n
  set x := ZMod.castHom (dvd_refl p) K (v 0) with hxdef
  set y := ZMod.castHom (dvd_refl p) K (v 1) with hydef
  set c : ℕ → K := fun i => coeff (e i (n - i)) (F : MvPolynomial (Fin 2) K) with hc
  rw [L, coe_remapB, ev_remap, ev_coe_eq_sum, ← sum_filter_add_sum_filter_not (range (n + 1)) (good p n)]
  have hbad : ∑ i ∈ range (n + 1) with ¬ good p n i, c i * x ^ i * y ^ (n - i) = 0 := by
    have h1 : ∑ i ∈ range (n + 1) with ¬ good p n i, c i * x ^ i * y ^ (n - i)
        = ∑ i ∈ range (n + 1) with ¬ good p n i, c i * (x ^ rd p i * y ^ (rd p n + (p - 1) - rd p i)) := by
      refine sum_congr rfl fun i hi => ?_
      simp only [mem_filter, mem_range, good, not_or, not_lt] at hi
      rw [mul_assoc, ← pow_rd p K hx (i := i) (by omega),
        ← pow_sub_eq_pow p K hy (n := n) (i := i) (by omega) (by omega)]
    have hmaps : ∀ i ∈ (range (n + 1)).filter (fun i => ¬ good p n i), rd p i ∈ Ico (rd p n) p := by
      intro i hi
      simp only [mem_filter, mem_range, good, not_or, not_lt] at hi
      simp only [mem_Ico]
      have := rd_le p i
      omega
    rw [h1, ← sum_fiberwise_of_maps_to hmaps]
    refine sum_eq_zero fun j hj => ?_
    rw [Finset.filter_filter]
    have h2 : ∑ i ∈ range (n + 1) with (¬ good p n i ∧ rd p i = j),
        c i * (x ^ rd p i * y ^ (rd p n + (p - 1) - rd p i))
        = (∑ i ∈ range (n + 1) with (¬ good p n i ∧ rd p i = j), c i) * (x ^ j * y ^ (rd p n + (p - 1) - j)) := by
      rw [sum_mul]
      refine sum_congr rfl fun i hi => ?_
      rw [(Finset.mem_filter.mp hi).2.2]
    have h3 : (range (n + 1)).filter (fun i => ¬ good p n i ∧ rd p i = j)
        = (range (n + 1)).filter (fun i => gR p n i = j) := by
      simp only [mem_Ico] at hj
      refine Finset.filter_congr fun i hi => ?_
      simp only [mem_range] at hi
      simp only [good, gR, not_or, not_lt]
      constructor
      · rintro ⟨⟨h0, hn', _⟩, hrd⟩
        rw [if_neg h0, if_neg hn', hrd]
      · intro h
        split_ifs at h with h0 hn'
        · omega
        · omega
        · exact ⟨⟨h0, hn', by omega⟩, h⟩
    rw [h2, h3, sum_fiber_eq_zero_of_T_eq_zero p K F hT (mem_Ico.mp hj).1 (mem_Ico.mp hj).2, zero_mul]
  rw [hbad, add_zero]
  refine sum_congr rfl fun i hi => ?_
  simp only [mem_filter, mem_range] at hi
  obtain ⟨hin, hg⟩ := hi
  rw [mul_one]
  by_cases h0 : i = 0
  · subst h0
    simp only [gL, if_true, pow_zero, Nat.sub_zero, mul_one]
    rw [← pow_rd p K hy hn1]
  by_cases hn' : i = n
  · subst hn'
    simp only [gL, h0, if_false, if_true, Nat.sub_self, pow_zero]
    rw [← pow_rd p K hx hn1]
  · have hlt : rd p i < rd p n := by
      rcases hg with h | h | h
      · exact absurd h h0
      · exact absurd h hn'
      · exact h
    simp only [gL, h0, hn', if_false]
    rw [← pow_rd p K hx (i := i) (by omega), pow_sub_eq_pow p K hy (n := n) (i := i) (by omega) (by omega),
      show rd p n + (p - 1) - rd p i = (rd p n - rd p i) + 1 * (p - 1) by omega,
      pow_add_mul_sub_one p K hy (by omega) 1]

theorem coe_L_bm {n i : ℕ} (hi : i ≤ n) :
    ((L p K n (bm K n i) : ↥(BinaryForm K _)) : MvPolynomial (Fin 2) K)
      = if good p n i then monomial (e (gL p n i) (rd p n - gL p n i)) 1 else 0 := by
  rw [L, coe_remapB, coe_bm K hi, remap_monomial]
  simp only [mem_filter, mem_range, Nat.lt_succ_iff, hi, true_and]

noncomputable def vanSub (n : ℕ) : Submodule K ↥(BinaryForm K n) where
  carrier := {F | ∀ v, ev p K (F : MvPolynomial (Fin 2) K) v = 0}
  add_mem' {F G} hF hG v := by rw [Submodule.coe_add, ev_add, hF v, hG v, add_zero]
  zero_mem' v := by rw [Submodule.coe_zero, ev_zero]
  smul_mem' c F hF v := by rw [Submodule.coe_smul, ev_smul, hF v, mul_zero]

theorem mem_vanSub {n : ℕ} {F : ↥(BinaryForm K n)} :
    F ∈ vanSub p K n ↔ ∀ v, ev p K (F : MvPolynomial (Fin 2) K) v = 0 :=
  Iff.rfl

theorem vanSub_eq_bot {n : ℕ} (hn : n ≤ p) : vanSub p K n = ⊥ := by
  refine eq_bot_iff.mpr fun F hF => ?_
  rw [Submodule.mem_bot]
  exact Subtype.ext (eq_zero_of_ev_eq_zero p K hn (isHomogeneous_coe K F) hF)

noncomputable def thetaMul (m : ℕ) : ↥(BinaryForm K m) →ₗ[K] ↥(BinaryForm K (m + (p + 1))) :=
  LinearMap.codRestrict (BinaryForm K (m + (p + 1)))
    ((LinearMap.mulLeft K (theta p K)).comp (BinaryForm K m).subtype) fun F => by
      rw [MvPolynomial.mem_homogeneousSubmodule, add_comm]
      exact (isHomogeneous_theta p K).mul (isHomogeneous_coe K F)

@[scoped simp] theorem coe_thetaMul (m : ℕ) (F : ↥(BinaryForm K m)) :
    ((thetaMul p K m F : ↥(BinaryForm K _)) : MvPolynomial (Fin 2) K) = theta p K * F :=
  rfl

theorem thetaMul_injective (m : ℕ) : Function.Injective (thetaMul p K m) := fun F G h =>
  Subtype.ext (mul_left_cancel₀ (theta_ne_zero p K) (congrArg Subtype.val h))

theorem thetaMul_equivar (m : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) (F : ↥(BinaryForm K m)) :
    binaryFormRep K _ M (thetaMul p K m F)
      = thetaMul p K m (((M.det : ℤ) : K) • binaryFormRep K m M F) := by
  refine Subtype.ext ?_
  rw [binaryFormRep_apply_coe, coe_thetaMul, coe_thetaMul, map_mul, binarySubst_theta, Submodule.coe_smul,
    binaryFormRep_apply_coe, smul_mul_assoc, mul_smul_comm]

theorem vanSub_eq_range (m : ℕ) : vanSub p K (m + (p + 1)) = LinearMap.range (thetaMul p K m) := by
  ext F
  constructor
  · intro hF
    obtain ⟨H, hH, hFH⟩ := exists_eq_theta_mul p K (isHomogeneous_coe K F) hF
    refine ⟨⟨H, ?_⟩, Subtype.ext hFH.symm⟩
    rw [MvPolynomial.mem_homogeneousSubmodule]
    simpa using hH
  · rintro ⟨H, rfl⟩ v
    rw [coe_thetaMul, ev_mul, ev_theta, zero_mul]

def StepOK (n : ℕ) (U U' : Submodule K ↥(BinaryForm K n)) : Prop :=
  ∃ (a b : ℕ) (π : ↥(BinaryForm K n) →ₗ[K] ↥(BinaryForm K a)),
    a ≤ p - 1 ∧ Submodule.map π U' = ⊤ ∧ U = U' ⊓ LinearMap.ker π ∧
    ∀ (M : Matrix (Fin 2) (Fin 2) ℤ), ¬ (p : ℤ) ∣ M.det → ∀ w ∈ U',
      π (binaryFormRep K n M w) = (((M.det : ℤ) : K) ^ b) • binaryFormRep K a M (π w)

def Stable (n : ℕ) (U : Submodule K ↥(BinaryForm K n)) : Prop :=
  ∀ (M : Matrix (Fin 2) (Fin 2) ℤ), ¬ (p : ℤ) ∣ M.det → Submodule.map (binaryFormRep K n M) U ≤ U

theorem rep_mem_ker_T {n : ℕ} (hn : 1 ≤ n) (M : Matrix (Fin 2) (Fin 2) ℤ) {w : ↥(BinaryForm K n)}
    (hw : w ∈ LinearMap.ker (T p K n)) : binaryFormRep K n M w ∈ LinearMap.ker (T p K n) := by
  rw [LinearMap.mem_ker] at hw ⊢
  rw [T_equivar p K hn, hw, map_zero, smul_zero]

theorem mid_step {n : ℕ} (hn : p ≤ n) : StepOK p K n (vanSub p K n) (LinearMap.ker (T p K n)) := by
  classical
  have hp2 := hp.out.two_le
  have hn1 : 1 ≤ n := by omega
  have hrdn1 := one_le_rd p n
  have hrdle := rd_le p n
  have han : rd p n < n := by omega
  refine ⟨rd p n, 0, L p K n, rd_le p n, ?_, ?_, ?_⟩
  ·
    refine eq_top_iff.mpr fun G _ => ?_
    set pre : ℕ → ↥(BinaryForm K n) := fun t => if t = rd p n then bm K n n else bm K n t with hpre
    have hker : ∀ t, t ≤ rd p n → pre t ∈ LinearMap.ker (T p K n) := by
      intro t ht
      rw [LinearMap.mem_ker]
      refine Subtype.ext ?_
      rw [Submodule.coe_zero, hpre]
      dsimp only
      split_ifs with hta
      · rw [coe_T_bm p K le_rfl, if_neg]
        simp only [gR, show n ≠ 0 by omega, if_false, if_true]
        omega
      · rw [coe_T_bm p K (by omega), if_neg]
        simp only [gR, show t ≠ n by omega, if_false]
        split_ifs with h0
        · omega
        · rw [rd_eq_self_of_lt p (i := t) (by omega) (by omega)]
          omega
    have hL : ∀ t, t ≤ rd p n → L p K n (pre t) = bm K (rd p n) t := by
      intro t ht
      refine Subtype.ext ?_
      rw [coe_bm K ht, hpre]
      dsimp only
      split_ifs with hta
      · rw [coe_L_bm p K le_rfl, if_pos (show good p n n from Or.inr (Or.inl rfl))]
        simp only [gL, show n ≠ 0 by omega, if_false, if_true, hta]
      · rw [coe_L_bm p K (by omega)]
        by_cases h0 : t = 0
        · subst h0
          rw [if_pos (show good p n 0 from Or.inl rfl)]
          simp [gL]
        · have hrd : rd p t = t := rd_eq_self_of_lt p (i := t) (by omega) (by omega)
          rw [if_pos (show good p n t from Or.inr (Or.inr (by omega)))]
          simp only [gL, h0, show t ≠ n by omega, if_false, hrd]
    rw [eq_sum_bm K G]
    refine Submodule.sum_mem _ fun t ht => Submodule.smul_mem _ _ ?_
    have ht' : t ≤ rd p n := by simpa [Nat.lt_succ_iff] using ht
    rw [← hL t ht']
    exact Submodule.mem_map_of_mem (hker t ht')
  ·
    ext F
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, mem_vanSub]
    constructor
    · intro hF
      have hT : T p K n F = 0 := by
        have hRv : ∀ v, ev p K ((R p K n F : ↥(BinaryForm K _)) : MvPolynomial (Fin 2) K) v = 0 :=
          fun v => by rw [ev_R p K hn1, hF v]
        obtain ⟨H, -, hH⟩ := exists_eq_theta_mul p K (isHomogeneous_coe K _) hRv
        refine Subtype.ext ?_
        rw [coe_T, hH, Submodule.coe_zero]
        exact dmap_theta_mul p K _ H
      refine ⟨hT, Subtype.ext ?_⟩
      rw [Submodule.coe_zero]
      refine eq_zero_of_ev_eq_zero p K (by have := rd_le p n; omega) (isHomogeneous_coe K _) fun v => ?_
      rw [ev_L p K hn F hT, hF v]
    · rintro ⟨hT, hL⟩ v
      rw [← ev_L p K hn F hT, hL, Submodule.coe_zero, ev_zero]
  ·
    intro M _ w hw
    rw [pow_zero, one_smul]
    have hMw := rep_mem_ker_T p K hn1 M hw
    rw [LinearMap.mem_ker] at hw hMw
    rw [← sub_eq_zero]
    refine Subtype.ext (eq_zero_of_ev_eq_zero p K (by have := rd_le p n; omega) (isHomogeneous_coe K _)
      fun v => ?_)
    rw [Submodule.coe_sub, ev_sub, ev_L p K hn _ hMw, binaryFormRep_apply_coe, ev_binarySubst,
      binaryFormRep_apply_coe, ev_binarySubst, ev_L p K hn _ hw, sub_self]

theorem top_step {n : ℕ} (hn : p ≤ n) : StepOK p K n (LinearMap.ker (T p K n)) ⊤ := by
  classical
  have hp2 := hp.out.two_le
  have hn1 : 1 ≤ n := by omega
  have ha1 := one_le_rd p n
  have hap := rd_le p n
  refine ⟨p - 1 - rd p n, rd p n, T p K n, by omega, ?_, by rw [top_inf_eq], fun M _ w _ => T_equivar p K hn1 M w⟩
  refine eq_top_iff.mpr fun G _ => ?_
  have hT : ∀ t, t ≤ p - 1 - rd p n →
      bm K (p - 1 - rd p n) t
        = T p K n ((((t + rd p n).descFactorial (rd p n) : ℕ) : K)⁻¹ • bm K n (t + rd p n)) := by
    intro t ht
    have hne := cast_descFactorial_ne_zero p K (a := rd p n) (i := t + rd p n) (by omega) (by omega)
    rw [map_smul]
    refine Subtype.ext ?_
    rw [coe_bm K ht, Submodule.coe_smul, coe_T_bm p K (by omega)]
    have hg : gR p n (t + rd p n) = t + rd p n := by
      simp only [gR, show t + rd p n ≠ 0 by omega, show t + rd p n ≠ n by omega, if_false]
      exact rd_eq_self_of_lt p (by omega) (by omega)
    rw [hg, if_pos ⟨by omega, by omega⟩, smul_monomial, smul_eq_mul, inv_mul_cancel₀ hne,
      show t + rd p n - rd p n = t by omega, show p - 1 - (t + rd p n) = p - 1 - rd p n - t by omega]
  rw [eq_sum_bm K G]
  refine Submodule.sum_mem _ fun t ht => Submodule.smul_mem _ _ ?_
  have ht' : t ≤ p - 1 - rd p n := by simpa [Nat.lt_succ_iff] using ht
  rw [hT t ht']
  exact Submodule.mem_map_of_mem trivial

def FiltTo (n : ℕ) (U : Submodule K ↥(BinaryForm K n)) : Prop :=
  ∃ (r : ℕ) (W : ℕ → Submodule K ↥(BinaryForm K n)), W 0 = ⊥ ∧ (∀ i, r ≤ i → W i = U) ∧
    Monotone W ∧ (∀ i, Stable p K n (W i)) ∧ ∀ i, i < r → StepOK p K n (W i) (W (i + 1))

theorem stable_bot (n : ℕ) : Stable p K n ⊥ := fun M _ => by simp

theorem stable_top (n : ℕ) : Stable p K n ⊤ := fun _ _ => le_top

theorem stable_ker_T {n : ℕ} (hn : 1 ≤ n) : Stable p K n (LinearMap.ker (T p K n)) := by
  rintro M - _ ⟨w, hw, rfl⟩
  exact rep_mem_ker_T p K hn M hw

theorem filtTo_bot (n : ℕ) : FiltTo p K n ⊥ :=
  ⟨0, fun _ => ⊥, rfl, fun _ _ => rfl, fun _ _ _ => le_rfl, fun _ => stable_bot p K n,
    fun i hi => absurd hi (Nat.not_lt_zero _)⟩

theorem filtTo_append {n : ℕ} {U U' : Submodule K ↥(BinaryForm K n)} (h : FiltTo p K n U)
    (hU' : Stable p K n U') (hstep : StepOK p K n U U') : FiltTo p K n U' := by
  obtain ⟨r, W, h0, hr, hmono, hstab, hsteps⟩ := h
  have hUU' : U ≤ U' := by
    obtain ⟨a, b, π, -, -, hUeq, -⟩ := hstep
    rw [hUeq]
    exact inf_le_left
  refine ⟨r + 1, fun i => if i ≤ r then W i else U', ?_, ?_, ?_, ?_, ?_⟩
  · simp [h0]
  · intro i hi
    dsimp only
    rw [if_neg (by omega)]
  · intro i j hij
    dsimp only
    by_cases hi : i ≤ r <;> by_cases hj : j ≤ r
    · rw [if_pos hi, if_pos hj]
      exact hmono hij
    · rw [if_pos hi, if_neg hj]
      calc W i ≤ W (i + r) := hmono (by omega)
        _ = U := hr _ (by omega)
        _ ≤ U' := hUU'
    · exact absurd (hij.trans hj) hi
    · rw [if_neg hi, if_neg hj]
  · intro i
    dsimp only
    split_ifs
    · exact hstab i
    · exact hU'
  · intro i hi
    dsimp only
    by_cases hir : i < r
    · rw [if_pos hir.le, if_pos (by omega)]
      exact hsteps i hir
    · have hi' : i = r := by omega
      subst hi'
      rw [if_pos le_rfl, if_neg (by omega), hr i le_rfl]
      exact hstep

theorem stepOK_push {m : ℕ} {U U' : Submodule K ↥(BinaryForm K m)} (h : StepOK p K m U U') :
    StepOK p K (m + (p + 1)) (U.map (thetaMul p K m)) (U'.map (thetaMul p K m)) := by
  obtain ⟨a, b, π, ha, hsurj, hker, heqv⟩ := h
  obtain ⟨lam, hlam⟩ := LinearMap.exists_leftInverse_of_injective (thetaMul p K m)
    (LinearMap.ker_eq_bot.mpr (thetaMul_injective p K m))
  have hl : ∀ v, lam (thetaMul p K m v) = v := fun v => by
    have := LinearMap.congr_fun hlam v
    simpa using this
  refine ⟨a, b + 1, π.comp lam, ha, ?_, ?_, ?_⟩
  · rw [Submodule.map_comp, ← Submodule.map_comp (thetaMul p K m) lam, hlam, Submodule.map_id, hsurj]
  · ext x
    simp only [Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.comp_apply]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [hker, Submodule.mem_inf, LinearMap.mem_ker] at hu
      exact ⟨⟨u, hu.1, rfl⟩, by rw [hl]; exact hu.2⟩
    · rintro ⟨⟨u, hu, rfl⟩, hx⟩
      rw [hl] at hx
      refine ⟨u, ?_, rfl⟩
      rw [hker, Submodule.mem_inf, LinearMap.mem_ker]
      exact ⟨hu, hx⟩
  · intro M hM w hw
    obtain ⟨u, hu, rfl⟩ := hw
    rw [LinearMap.comp_apply, LinearMap.comp_apply, thetaMul_equivar, hl, hl, map_smul, heqv M hM u hu,
      smul_smul, pow_succ, mul_comm]

theorem stable_map_thetaMul {m : ℕ} {U : Submodule K ↥(BinaryForm K m)} (h : Stable p K m U) :
    Stable p K (m + (p + 1)) (U.map (thetaMul p K m)) := by
  rintro M hM _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  rw [thetaMul_equivar]
  exact ⟨_, U.smul_mem _ (h M hM ⟨u, hu, rfl⟩), rfl⟩

theorem filtTo_push {m : ℕ} (h : FiltTo p K m ⊤) :
    FiltTo p K (m + (p + 1)) (LinearMap.range (thetaMul p K m)) := by
  obtain ⟨r, W, h0, hr, hmono, hstab, hsteps⟩ := h
  exact ⟨r, fun i => (W i).map (thetaMul p K m), by simp [h0],
    fun i hi => by simp only [hr i hi, Submodule.map_top],
    fun i j hij => Submodule.map_mono (hmono hij), fun i => stable_map_thetaMul p K (hstab i),
    fun i hi => stepOK_push p K (hsteps i hi)⟩

theorem filtTo_top (n : ℕ) : FiltTo p K n ⊤ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n p with hnp | hpn
    · refine filtTo_append p K (filtTo_bot p K n) (stable_top p K n)
        ⟨n, 0, LinearMap.id, by omega, ?_, ?_, fun M _ w _ => ?_⟩
      · simp
      · simp
      · simp
    · have hp2 := hp.out.two_le
      have hvan : FiltTo p K n (vanSub p K n) := by
        rcases Nat.lt_or_ge n (p + 1) with h1 | h1
        · rw [vanSub_eq_bot p K (by omega)]
          exact filtTo_bot p K n
        · obtain ⟨m, rfl⟩ : ∃ m, n = m + (p + 1) := ⟨n - (p + 1), by omega⟩
          rw [vanSub_eq_range]
          exact filtTo_push p K (ih m (by omega))
      exact filtTo_append p K (filtTo_append p K hvan (stable_ker_T p K (by omega)) (mid_step p K hpn))
        (stable_top p K n) (top_step p K hpn)

end Maps

end ATHRFilt
p2m_reactivate "P2MW.S_HeckeEis_exists_filtration_binaryForm_subquotient_le_sub_one.ATHRFilt"

theorem solution (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [CharP K p] (n : ℕ) :
    ∃ (r : ℕ) (W : Fin (r + 1) → Submodule K ↥(HeckeEis.BinaryForm K n)),
      W 0 = ⊥ ∧ W (Fin.last r) = ⊤ ∧ Monotone W ∧
      (∀ (i : Fin (r + 1)) (M : Matrix (Fin 2) (Fin 2) ℤ), ¬ (p : ℤ) ∣ M.det →
        Submodule.map (HeckeEis.binaryFormRep K n M) (W i) ≤ W i) ∧
      ∀ i : Fin r, ∃ (a b : ℕ) (π : ↥(HeckeEis.BinaryForm K n) →ₗ[K] ↥(HeckeEis.BinaryForm K a)),
        a ≤ p - 1 ∧ Submodule.map π (W i.succ) = ⊤ ∧ W i.castSucc = W i.succ ⊓ LinearMap.ker π ∧
        ∀ (M : Matrix (Fin 2) (Fin 2) ℤ), ¬ (p : ℤ) ∣ M.det → ∀ w ∈ W i.succ,
          π (HeckeEis.binaryFormRep K n M w)
            = (((M.det : ℤ) : K) ^ b) • HeckeEis.binaryFormRep K a M (π w) := by
  obtain ⟨r, W, h0, hr, hmono, hstab, hsteps⟩ := ATHRFilt.filtTo_top p K n
  refine ⟨r, fun i => W i, h0, hr r le_rfl, fun i j hij => hmono hij, fun i M hM => hstab i M hM,
    fun i => ?_⟩
  exact hsteps i.1 i.2

end S_HeckeEis_exists_filtration_binaryForm_subquotient_le_sub_one
end P2MW
export P2MW.S_HeckeEis_exists_filtration_binaryForm_subquotient_le_sub_one (solution)
