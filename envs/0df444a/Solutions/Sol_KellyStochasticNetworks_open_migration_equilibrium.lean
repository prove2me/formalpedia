-- Prove2me | solution 1 for KellyStochasticNetworks.open_migration_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T00:36:17.735052+00:00
-- url     : https://prove2.me/submissions/28ecb8c2-195c-4add-ad43-10520f339e62

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_KellyStochasticNetworks_Balance

namespace KellyStochasticNetworks

open Finset

/-! ### The transfer operators -/

section Ops

variable {J : ℕ}

@[simp] lemma sn2_Tin_self (k : Fin J) (n : Fin J → ℕ) : Tin k n k = n k + 1 := by simp [Tin]
@[simp] lemma sn2_Tout_self (j : Fin J) (n : Fin J → ℕ) : Tout j n j = n j - 1 := by simp [Tout]
lemma sn2_Tin_ne {k i : Fin J} (h : i ≠ k) (n : Fin J → ℕ) : Tin k n i = n i := by simp [Tin, h]
lemma sn2_Tout_ne {j i : Fin J} (h : i ≠ j) (n : Fin J → ℕ) : Tout j n i = n i := by simp [Tout, h]

lemma sn2_Tjk_eq {j k : Fin J} (hjk : j ≠ k) (n : Fin J → ℕ) : Tjk j k n = Tin k (Tout j n) := by
  funext i; unfold Tjk Tin Tout
  by_cases h1 : i = j
  · subst h1; simp [hjk]
  · by_cases h2 : i = k
    · subst h2; simp [h1]
    · simp [h1, h2]

lemma sn2_Tjj (j : Fin J) (n : Fin J → ℕ) : Tjk j j n = Tout j n := by
  funext i; unfold Tjk Tout; by_cases h : i = j <;> simp [h]

lemma sn2_Tout_Tin (k : Fin J) (n : Fin J → ℕ) : Tout k (Tin k n) = n := by
  funext i; unfold Tout Tin; split_ifs with h <;> simp_all

lemma sn2_Tin_Tout (k : Fin J) (m : Fin J → ℕ) (hm : 1 ≤ m k) : Tin k (Tout k m) = m := by
  funext i; unfold Tout Tin; split_ifs with h <;> simp_all

lemma sn2_Tjk_apply_j {j k : Fin J} (hjk : j ≠ k) (n : Fin J → ℕ) : Tjk j k n j = n j - 1 := by
  simp [Tjk]
lemma sn2_Tjk_apply_k {j k : Fin J} (hjk : j ≠ k) (n : Fin J → ℕ) : Tjk j k n k = n k + 1 := by
  simp [Tjk, Ne.symm hjk]
lemma sn2_Tjk_apply_ne {j k i : Fin J} (hj : i ≠ j) (hk : i ≠ k) (n : Fin J → ℕ) :
    Tjk j k n i = n i := by simp [Tjk, hj, hk]

lemma sn2_Tjk_back {j k : Fin J} (hjk : j ≠ k) (m : Fin J → ℕ) (hm : 1 ≤ m j) :
    Tjk k j (Tjk j k m) = m := by
  funext i
  by_cases h1 : i = j
  · subst h1; rw [sn2_Tjk_apply_k (Ne.symm hjk), sn2_Tjk_apply_j hjk]; omega
  · by_cases h2 : i = k
    · subst h2; rw [sn2_Tjk_apply_j (Ne.symm hjk), sn2_Tjk_apply_k hjk]; omega
    · rw [sn2_Tjk_apply_ne h2 h1, sn2_Tjk_apply_ne h1 h2]

/-- Two genuine transfers from the same state agree only if they are the same transfer. -/
lemma sn2_Tjk_inj {a b c d : Fin J} (hab : a ≠ b) (hcd : c ≠ d) (n : Fin J → ℕ)
    (ha : 1 ≤ n a) (h : Tjk a b n = Tjk c d n) : a = c ∧ b = d := by
  have e1 := congrFun h a
  rw [sn2_Tjk_apply_j hab] at e1
  have hac : a = c := by
    by_contra hne
    by_cases had : a = d
    · subst had; rw [sn2_Tjk_apply_k hcd] at e1; omega
    · rw [sn2_Tjk_apply_ne hne had] at e1; omega
  subst hac
  refine ⟨rfl, ?_⟩
  have e2 := congrFun h b
  rw [sn2_Tjk_apply_k hab] at e2
  by_contra hbd
  rw [sn2_Tjk_apply_ne (Ne.symm hab) hbd] at e2; omega

end Ops


/-! ### Products `∏_{r ≤ m} φ_j(r)` and the product-form weights -/

lemma sn2_phiProd_succ {J : ℕ} (φ : Fin J → ℕ → ℝ) (j : Fin J) (m : ℕ) :
    phiProd φ j (m + 1) = phiProd φ j m * φ j (m + 1) := by
  unfold phiProd
  exact Finset.prod_Icc_succ_top (by omega : 1 ≤ m + 1) _

lemma sn2_phiProd_pos {J : ℕ} (φ : Fin J → ℕ → ℝ) (hφpos : ∀ j r, 1 ≤ r → 0 < φ j r)
    (j : Fin J) (m : ℕ) : 0 < phiProd φ j m := by
  unfold phiProd
  exact Finset.prod_pos (fun r hr => hφpos j r (Finset.mem_Icc.1 hr).1)

/-! ### Summation helpers -/

lemma sn2_hasSum_pi_prod (R : ℕ) : ∀ (f : Fin R → ℕ → ℝ) (a : Fin R → ℝ),
    (∀ i n, 0 ≤ f i n) → (∀ i, HasSum (f i) (a i)) →
    HasSum (fun n : Fin R → ℕ => ∏ i, f i (n i)) (∏ i, a i) := by
  induction R with
  | zero =>
    intro f a _ _
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact hasSum_single default (fun b hb => (hb (Subsingleton.elim b default)).elim)
  | succ R ih =>
    intro f a h0 ha
    set g : (Fin R → ℕ) → ℝ := fun n => ∏ i, f i.succ (n i) with hgdef
    have ih' : HasSum g (∏ i : Fin R, a i.succ) := ih (fun i : Fin R => f i.succ) (fun i : Fin R => a i.succ)
      (fun (i : Fin R) n => h0 _ _) (fun i : Fin R => ha _)
    have hf0 : ∀ n, 0 ≤ f 0 n := fun n => h0 0 n
    have hg0 : ∀ n, 0 ≤ g n := fun n => Finset.prod_nonneg fun i _ => h0 _ _
    have hsum : Summable fun x : ℕ × (Fin R → ℕ) => f 0 x.1 * g x.2 := by
      apply summable_mul_of_summable_norm
      · simpa [Real.norm_eq_abs, abs_of_nonneg (hf0 _)] using (ha 0).summable
      · simpa [Real.norm_eq_abs, abs_of_nonneg (hg0 _)] using ih'.summable
    have hm := HasSum.mul (ha 0) ih' hsum
    have hfun : (fun n : Fin (R + 1) → ℕ => ∏ i, f i (n i)) ∘ (Fin.consEquiv (fun _ => ℕ))
        = fun x : ℕ × (Fin R → ℕ) => f 0 x.1 * g x.2 := by
      funext x
      simp [Fin.consEquiv, Fin.prod_univ_succ, hgdef]
    rw [← (Fin.consEquiv (fun _ : Fin (R + 1) => ℕ)).hasSum_iff, hfun, Fin.prod_univ_succ]
    exact hm


lemma sn2_hasSum_single {S : Type*} [DecidableEq S] (x : S) (P : Prop) [Decidable P] (F : S → ℝ) :
    HasSum (fun m => if m = x ∧ P then F m else 0) (if P then F x else 0) := by
  by_cases hP : P
  · simp only [hP, and_true, if_true]
    have := hasSum_ite_eq x (F x)
    convert this using 1
    funext m; split_ifs with h <;> simp_all
  · simp only [hP, and_false, if_false]; exact hasSum_zero

lemma sn2_hasSum_single' {S : Type*} [DecidableEq S] (x : S) (F : S → ℝ) :
    HasSum (fun m => if m = x then F m else 0) (F x) := by
  have := hasSum_ite_eq x (F x)
  convert this using 1
  funext m; split_ifs with h <;> simp_all

/-- The product-form weights `u_j(m) = c_j α_j^m / ∏_{r ≤ m} φ_j(r)` satisfy the ratio rule. -/
lemma sn2_hu {J : ℕ} (c α : Fin J → ℝ) (φ : Fin J → ℕ → ℝ) (hφpos : ∀ j r, 1 ≤ r → 0 < φ j r)
    (j : Fin J) (m : ℕ) :
    c j * (α j ^ (m + 1) / phiProd φ j (m + 1)) * φ j (m + 1)
      = c j * (α j ^ m / phiProd φ j m) * α j := by
  rw [sn2_phiProd_succ]
  have h1 := sn2_phiProd_pos φ hφpos j m
  have h2 := hφpos j (m + 1) (by omega)
  field_simp
  ring


section Weights

variable {J : ℕ} (u : Fin J → ℕ → ℝ) (α : Fin J → ℝ) (φ : Fin J → ℕ → ℝ)

/-- `P(n) = ∏_j u_j(n_j)`. -/
def sn2P (n : Fin J → ℕ) : ℝ := ∏ j, u j (n j)

lemma sn2P_update (n : Fin J → ℕ) (k : Fin J) (v : ℕ) (m : Fin J → ℕ)
    (hm : ∀ i, i ≠ k → m i = n i) (hk : m k = v) :
    sn2P u m = u k v * ∏ i ∈ univ.erase k, u i (n i) := by
  unfold sn2P
  rw [← Finset.mul_prod_erase univ _ (mem_univ k), hk]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [hm i (Finset.ne_of_mem_erase hi)]

variable (hu : ∀ j m, u j (m + 1) * φ j (m + 1) = u j m * α j)
include hu

lemma sn2P_Tin (n : Fin J → ℕ) (k : Fin J) :
    sn2P u (Tin k n) * φ k (n k + 1) = sn2P u n * α k := by
  rw [sn2P_update u n k (n k + 1) (Tin k n) (fun i hi => sn2_Tin_ne hi n) (sn2_Tin_self k n)]
  rw [sn2P_update u n k (n k) n (fun i _ => rfl) rfl]
  have := hu k (n k)
  calc _ = (u k (n k + 1) * φ k (n k + 1)) * ∏ i ∈ univ.erase k, u i (n i) := by ring
    _ = _ := by rw [this]; ring

lemma sn2P_Tout (n : Fin J → ℕ) (j : Fin J) (hn : 1 ≤ n j) :
    sn2P u (Tout j n) * α j = sn2P u n * φ j (n j) := by
  have h := sn2P_Tin u α φ hu (Tout j n) j
  rw [sn2_Tin_Tout j n hn, sn2_Tout_self, Nat.sub_add_cancel hn] at h
  linarith

lemma sn2P_Tjk (n : Fin J → ℕ) {j k : Fin J} (hjk : j ≠ k) (hn : 1 ≤ n j) :
    sn2P u (Tjk j k n) * φ k (n k + 1) * α j = sn2P u n * φ j (n j) * α k := by
  rw [sn2_Tjk_eq hjk]
  have h1 := sn2P_Tin u α φ hu (Tout j n) k
  rw [sn2_Tout_ne (Ne.symm hjk) n] at h1
  have h2 := sn2P_Tout u α φ hu n j hn
  rw [h1]
  calc sn2P u (Tout j n) * α k * α j = (sn2P u (Tout j n) * α j) * α k := by ring
    _ = _ := by rw [h2]

/-- Partial balance at colony `j`, open network (Theorem 2.8). -/
lemma sn2_partial_a (lam : Fin J → Fin J → ℝ) (mu nu : Fin J → ℝ)
    (hlamdiag : ∀ j, lam j j = 0) (hα : ∀ j, 0 < α j)
    (htraffic : OpenTraffic lam mu nu α) (n : Fin J → ℕ) (j : Fin J) (hn : 1 ≤ n j) :
    sn2P u n * ((∑ k, lam j k * φ j (n j)) + mu j * φ j (n j))
      = (∑ k, sn2P u (Tjk j k n) * (lam k j * φ k (n k + 1))) + sn2P u (Tout j n) * nu j := by
  have hαj : α j ≠ 0 := (hα j).ne'
  have hk : ∀ k, sn2P u (Tjk j k n) * (lam k j * φ k (n k + 1))
      = sn2P u n * φ j (n j) / α j * (α k * lam k j) := by
    intro k
    by_cases hjk : j = k
    · subst hjk; rw [hlamdiag]; ring
    · have := sn2P_Tjk u α φ hu n hjk hn
      field_simp
      linear_combination lam k j * this
  have ho : sn2P u (Tout j n) * nu j = sn2P u n * φ j (n j) / α j * nu j := by
    have := sn2P_Tout u α φ hu n j hn
    field_simp
    linear_combination nu j * this
  rw [Finset.sum_congr rfl (fun k _ => hk k), ho, ← Finset.mul_sum, ← mul_add, add_comm _ (nu j),
    ← htraffic j]
  field_simp
  rw [← Finset.sum_mul]
  ring

/-- Partial balance for the outside world, open network. -/
lemma sn2_partial_b (lam : Fin J → Fin J → ℝ) (mu nu : Fin J → ℝ)
    (htraffic : OpenTraffic lam mu nu α) (n : Fin J → ℕ) :
    sn2P u n * (∑ k, nu k) = ∑ k, sn2P u (Tin k n) * (mu k * φ k (n k + 1)) := by
  have hsum : ∑ k, nu k = ∑ k, α k * mu k := by
    have h := Finset.sum_congr rfl (fun j (_ : j ∈ univ) => htraffic j)
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum] at h
    rw [Finset.sum_comm (f := fun j k => α k * lam k j)] at h
    have e : ∑ y, ∑ x, α y * lam y x = ∑ x, ∑ i, α x * lam x i := rfl
    linarith
  rw [hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k _
  have := sn2P_Tin u α φ hu n k
  linear_combination -(mu k) * this

/-- Partial balance at colony `j`, closed network (Theorem 2.4). -/
lemma sn2_partial_closed (lam : Fin J → Fin J → ℝ)
    (hlamdiag : ∀ j, lam j j = 0) (hα : ∀ j, 0 < α j)
    (htraffic : ∀ j, α j * ∑ k, lam j k = ∑ k, α k * lam k j) (n : Fin J → ℕ) (j : Fin J)
    (hn : 1 ≤ n j) :
    sn2P u n * (∑ k, lam j k * φ j (n j))
      = ∑ k, sn2P u (Tjk j k n) * (lam k j * φ k (n k + 1)) := by
  have hαj : α j ≠ 0 := (hα j).ne'
  have hk : ∀ k, sn2P u (Tjk j k n) * (lam k j * φ k (n k + 1))
      = sn2P u n * φ j (n j) / α j * (α k * lam k j) := by
    intro k
    by_cases hjk : j = k
    · subst hjk; rw [hlamdiag]; ring
    · have := sn2P_Tjk u α φ hu n hjk hn
      field_simp
      linear_combination lam k j * this
  rw [Finset.sum_congr rfl (fun k _ => hk k), ← Finset.mul_sum, ← htraffic j]
  field_simp
  rw [← Finset.sum_mul]
  ring

end Weights

/-! ### Preimages of the transfer operators -/

section Preimage

variable {J : ℕ} (φ : Fin J → ℕ → ℝ) (hφ0 : ∀ j, φ j 0 = 0)
include hφ0

lemma sn2_pre_Tjk (lam : Fin J → Fin J → ℝ) (hlamdiag : ∀ j, lam j j = 0)
    (f : (Fin J → ℕ) → ℝ) (n m : Fin J → ℕ) (j k : Fin J) :
    f m * (if n = Tjk j k m then lam j k * φ j (m j) else 0)
      = if m = Tjk k j n ∧ 1 ≤ n k then f m * (lam j k * φ j (m j)) else 0 := by
  by_cases hjk : j = k
  · subst hjk; simp [hlamdiag]
  by_cases h : m = Tjk k j n ∧ 1 ≤ n k
  · rw [if_pos h, if_pos]
    rw [h.1, sn2_Tjk_back (Ne.symm hjk) n h.2]
  · rw [if_neg h]
    by_cases h2 : n = Tjk j k m
    · rw [if_pos h2]
      by_cases hmj : 1 ≤ m j
      · exfalso; apply h
        refine ⟨?_, ?_⟩
        · rw [h2, sn2_Tjk_back hjk m hmj]
        · rw [h2, sn2_Tjk_apply_k hjk]; omega
      · have : m j = 0 := by omega
        rw [this, hφ0]; ring
    · rw [if_neg h2]; ring

lemma sn2_pre_Tout (mu : Fin J → ℝ) (f : (Fin J → ℕ) → ℝ) (n m : Fin J → ℕ) (j : Fin J) :
    f m * (if n = Tout j m then mu j * φ j (m j) else 0)
      = if m = Tin j n then f m * (mu j * φ j (m j)) else 0 := by
  by_cases h : m = Tin j n
  · rw [if_pos h, if_pos]; rw [h, sn2_Tout_Tin]
  · rw [if_neg h]
    by_cases h2 : n = Tout j m
    · rw [if_pos h2]
      by_cases hmj : 1 ≤ m j
      · exfalso; apply h; rw [h2, sn2_Tin_Tout j m hmj]
      · have : m j = 0 := by omega
        rw [this, hφ0]; ring
    · rw [if_neg h2]; ring

omit hφ0 in
lemma sn2_pre_Tin (nu : Fin J → ℝ) (f : (Fin J → ℕ) → ℝ) (n m : Fin J → ℕ) (k : Fin J) :
    f m * (if n = Tin k m then nu k else 0)
      = if m = Tout k n ∧ 1 ≤ n k then f m * nu k else 0 := by
  by_cases h : m = Tout k n ∧ 1 ≤ n k
  · rw [if_pos h, if_pos]; rw [h.1, sn2_Tin_Tout k n h.2]
  · rw [if_neg h]
    by_cases h2 : n = Tin k m
    · exfalso; apply h
      refine ⟨by rw [h2, sn2_Tout_Tin], by rw [h2, sn2_Tin_self]; omega⟩
    · rw [if_neg h2]; ring

end Preimage

end KellyStochasticNetworks

open KellyStochasticNetworks

theorem solution {J : ℕ} (lam : Fin J → Fin J → ℝ)
    (mu nu α g : Fin J → ℝ) (φ : Fin J → ℕ → ℝ)
    (hlamdiag : ∀ j, lam j j = 0) (hlam : ∀ j k, 0 ≤ lam j k)
    (hmu : ∀ j, 0 ≤ mu j) (hnu : ∀ j, 0 ≤ nu j)
    (hφ0 : ∀ j, φ j 0 = 0) (hφpos : ∀ j r, 1 ≤ r → 0 < φ j r)
    (hα : ∀ j, 0 < α j) (htraffic : OpenTraffic lam mu nu α)
    (hg : ∀ j, HasSum (fun m : ℕ => α j ^ m / phiProd φ j m) (g j)) :
    FullBalance (openMigrationPi α g φ) (openMigrationRates lam mu nu φ)
      ∧ HasSum (openMigrationPi α g φ) 1 := by
  classical
  have hterm : ∀ j m, 0 ≤ α j ^ m / phiProd φ j m := fun j m =>
    div_nonneg (pow_nonneg (hα j).le _) (sn2_phiProd_pos φ hφpos j m).le
  have hg1 : ∀ j, 1 ≤ g j := by
    intro j
    have := le_hasSum (hg j) 0 (fun m _ => hterm j m)
    simpa [phiProd] using this
  set u : Fin J → ℕ → ℝ := fun j m => migrationMarginal α g φ j m with hudef
  have hu : ∀ j m, u j (m + 1) * φ j (m + 1) = u j m * α j :=
    fun j m => sn2_hu (fun j => (g j)⁻¹) α φ hφpos j m
  have hπ : ∀ n, openMigrationPi α g φ n = sn2P u n := fun n => rfl
  constructor
  · intro n
    have hL : HasSum (fun m => openMigrationRates lam mu nu φ n m)
        ((∑ j, ∑ k, lam j k * φ j (n j)) + (∑ j, mu j * φ j (n j)) + ∑ k, nu k) := by
      unfold openMigrationRates closedMigrationRates
      exact ((hasSum_sum (fun j _ => hasSum_sum (fun k _ => hasSum_ite_eq _ _))).add
        (hasSum_sum (fun j _ => hasSum_ite_eq _ _))).add (hasSum_sum (fun k _ => hasSum_ite_eq _ _))
    have hpt : ∀ m, openMigrationPi α g φ m * openMigrationRates lam mu nu φ m n
        = (∑ j, ∑ k, if m = Tjk k j n ∧ 1 ≤ n k then sn2P u m * (lam j k * φ j (m j)) else 0)
          + (∑ j, if m = Tin j n then sn2P u m * (mu j * φ j (m j)) else 0)
          + ∑ k, if m = Tout k n ∧ 1 ≤ n k then sn2P u m * nu k else 0 := by
      intro m
      rw [hπ]
      unfold openMigrationRates closedMigrationRates
      rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      congr 1; congr 1
      · apply Finset.sum_congr rfl; intro j _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
        exact sn2_pre_Tjk φ hφ0 lam hlamdiag (sn2P u) n m j k
      · apply Finset.sum_congr rfl; intro j _
        exact sn2_pre_Tout φ hφ0 mu (sn2P u) n m j
      · apply Finset.sum_congr rfl; intro k _
        exact sn2_pre_Tin nu (sn2P u) n m k
    have hR : HasSum (fun m => openMigrationPi α g φ m * openMigrationRates lam mu nu φ m n)
        ((∑ j, ∑ k, if 1 ≤ n k then sn2P u (Tjk k j n) * (lam j k * φ j (Tjk k j n j)) else 0)
          + (∑ j, sn2P u (Tin j n) * (mu j * φ j (Tin j n j)))
          + ∑ k, if 1 ≤ n k then sn2P u (Tout k n) * nu k else 0) := by
      simp only [hpt]
      exact ((hasSum_sum (fun j _ => hasSum_sum (fun k _ => sn2_hasSum_single _ _ _))).add
        (hasSum_sum (fun j _ => sn2_hasSum_single' _ _))).add
        (hasSum_sum (fun k _ => sn2_hasSum_single _ _ (fun m => sn2P u m * nu k)))
    rw [hL.tsum_eq, hR.tsum_eq, hπ]
    have hper : ∀ k, (∑ j, if 1 ≤ n k then sn2P u (Tjk k j n) * (lam j k * φ j (Tjk k j n j)) else 0)
        + (if 1 ≤ n k then sn2P u (Tout k n) * nu k else 0)
        = sn2P u n * ((∑ j, lam k j * φ k (n k)) + mu k * φ k (n k)) := by
      intro k
      by_cases hk : 1 ≤ n k
      · simp only [hk, if_true]
        rw [sn2_partial_a u α φ hu lam mu nu hlamdiag hα htraffic n k hk]
        congr 1
        apply Finset.sum_congr rfl; intro j _
        by_cases hjk : j = k
        · subst hjk; simp [hlamdiag]
        · rw [sn2_Tjk_apply_k (Ne.symm hjk)]
      · have : n k = 0 := by omega
        simp [hk, this, hφ0]
    have hin : (∑ j, sn2P u (Tin j n) * (mu j * φ j (Tin j n j))) = sn2P u n * ∑ k, nu k := by
      rw [sn2_partial_b u α φ hu lam mu nu htraffic n]
      simp only [sn2_Tin_self]
    have hAC : (∑ j, ∑ k, if 1 ≤ n k then sn2P u (Tjk k j n) * (lam j k * φ j (Tjk k j n j)) else 0)
        + (∑ k, if 1 ≤ n k then sn2P u (Tout k n) * nu k else 0)
        = sn2P u n * ((∑ j, ∑ k, lam j k * φ j (n j)) + ∑ j, mu j * φ j (n j)) := by
      rw [Finset.sum_comm, ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun k _ => hper k),
        ← Finset.mul_sum, Finset.sum_add_distrib]
    linear_combination -hAC - hin
  · have hmarg : ∀ j, HasSum (fun m => migrationMarginal α g φ j m) 1 := by
      intro j
      have := (hg j).mul_left (g j)⁻¹
      rw [inv_mul_cancel₀ (by linarith [hg1 j])] at this
      exact this
    have h := sn2_hasSum_pi_prod J (fun j m => migrationMarginal α g φ j m) (fun _ => 1)
      (fun j m => mul_nonneg (inv_nonneg.2 (by linarith [hg1 j])) (hterm j m)) hmarg
    rw [Finset.prod_const_one] at h
    exact h
