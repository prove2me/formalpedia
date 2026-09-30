-- Prove2me | solution 1 for KellyStochasticNetworks.open_migration_reversed
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T00:36:15.807471+00:00
-- url     : https://prove2.me/submissions/5d16f7e4-5b12-433f-9870-41cd96c34f27

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

lemma sn2P_pos {J : ℕ} (α g : Fin J → ℝ) (φ : Fin J → ℕ → ℝ)
    (hφpos : ∀ j r, 1 ≤ r → 0 < φ j r) (hα : ∀ j, 0 < α j) (hg : ∀ j, 0 < g j)
    (n : Fin J → ℕ) : 0 < openMigrationPi α g φ n := by
  unfold openMigrationPi migrationMarginal
  apply Finset.prod_pos; intro j _
  have := sn2_phiProd_pos φ hφpos j (n j)
  have := hα j
  have := hg j
  positivity

theorem solution {J : ℕ} (lam : Fin J → Fin J → ℝ)
    (mu nu α g : Fin J → ℝ) (φ : Fin J → ℕ → ℝ)
    (hlamdiag : ∀ j, lam j j = 0)
    (hφ0 : ∀ j, φ j 0 = 0) (hφpos : ∀ j r, 1 ≤ r → 0 < φ j r)
    (hα : ∀ j, 0 < α j) (hg : ∀ j, 0 < g j) :
    (∀ (n : Fin J → ℕ) (j k : Fin J), j ≠ k → 1 ≤ n j →
        reversedRates (openMigrationPi α g φ) (openMigrationRates lam mu nu φ) n (Tjk j k n)
          = (α k * lam k j / α j) * φ j (n j))
      ∧ (∀ (n : Fin J → ℕ) (j : Fin J), 1 ≤ n j →
        reversedRates (openMigrationPi α g φ) (openMigrationRates lam mu nu φ) n (Tout j n)
          = (nu j / α j) * φ j (n j))
      ∧ (∀ (n : Fin J → ℕ) (k : Fin J),
        reversedRates (openMigrationPi α g φ) (openMigrationRates lam mu nu φ) n (Tin k n)
          = α k * mu k) := by
  classical
  have hu : ∀ j m, migrationMarginal α g φ j (m + 1) * φ j (m + 1)
      = migrationMarginal α g φ j m * α j :=
    fun j m => sn2_hu (fun j => (g j)⁻¹) α φ hφpos j m
  have hπ : ∀ n, openMigrationPi α g φ n = sn2P (migrationMarginal α g φ) n := fun n => rfl
  -- the three families of indicator terms, rewritten through the preimage lemmas
  have eC : ∀ (n m : Fin J → ℕ) (j' k' : Fin J),
      (if n = Tjk j' k' m then lam j' k' * φ j' (m j') else 0)
        = if m = Tjk k' j' n ∧ 1 ≤ n k' then lam j' k' * φ j' (m j') else 0 := by
    intro n m j' k'
    have := sn2_pre_Tjk φ hφ0 lam hlamdiag (fun _ => (1 : ℝ)) n m j' k'
    simpa using this
  have eO : ∀ (n m : Fin J → ℕ) (j' : Fin J),
      (if n = Tout j' m then mu j' * φ j' (m j') else 0)
        = if m = Tin j' n then mu j' * φ j' (m j') else 0 := by
    intro n m j'
    have := sn2_pre_Tout φ hφ0 mu (fun _ => (1 : ℝ)) n m j'
    simpa using this
  have eI : ∀ (n m : Fin J → ℕ) (k' : Fin J),
      (if n = Tin k' m then nu k' else 0)
        = if m = Tout k' n ∧ 1 ≤ n k' then nu k' else 0 := by
    intro n m k'
    have := sn2_pre_Tin nu (fun _ => (1 : ℝ)) n m k'
    simpa using this
  have hrate : ∀ n m, openMigrationRates lam mu nu φ m n
      = (∑ j', ∑ k', if m = Tjk k' j' n ∧ 1 ≤ n k' then lam j' k' * φ j' (m j') else 0)
        + (∑ j', if m = Tin j' n then mu j' * φ j' (m j') else 0)
        + ∑ k', if m = Tout k' n ∧ 1 ≤ n k' then nu k' else 0 := by
    intro n m
    unfold openMigrationRates closedMigrationRates
    simp only [eC, eO, eI]
  refine ⟨?_, ?_, ?_⟩
  · intro n j k hjk hn
    have hq : openMigrationRates lam mu nu φ (Tjk j k n) n = lam k j * φ k (n k + 1) := by
      rw [hrate]
      have h1 : (∑ j', ∑ k', if Tjk j k n = Tjk k' j' n ∧ 1 ≤ n k'
          then lam j' k' * φ j' (Tjk j k n j') else 0) = lam k j * φ k (n k + 1) := by
        rw [Finset.sum_eq_single k, Finset.sum_eq_single j]
        · rw [if_pos ⟨rfl, hn⟩, sn2_Tjk_apply_k hjk]
        · intro k' _ hk'
          rw [if_neg]
          rintro ⟨h, _⟩
          by_cases hkk : k' = k
          · subst hkk
            have := congrFun h k'
            rw [sn2_Tjk_apply_k hjk, sn2_Tjj, sn2_Tout_self] at this; omega
          · exact hk' (sn2_Tjk_inj hjk hkk n hn h).1.symm
        · simp
        · intro j' _ hj'
          apply Finset.sum_eq_zero; intro k' _
          rw [if_neg]
          rintro ⟨h, hk'⟩
          by_cases hkk : k' = j'
          · subst hkk
            have := congrFun h k
            rw [sn2_Tjk_apply_k hjk, sn2_Tjj] at this
            by_cases hkk' : k = k'
            · subst hkk'; rw [sn2_Tout_self] at this; omega
            · rw [sn2_Tout_ne hkk'] at this; omega
          · exact hj' (sn2_Tjk_inj hjk hkk n hn h).2.symm
        · simp
      have h2 : (∑ j', if Tjk j k n = Tin j' n then mu j' * φ j' (Tjk j k n j') else 0) = 0 := by
        apply Finset.sum_eq_zero; intro j' _
        rw [if_neg]; intro h
        have := congrFun h j
        rw [sn2_Tjk_apply_j hjk] at this
        by_cases hj' : j = j'
        · subst hj'; rw [sn2_Tin_self] at this; omega
        · rw [sn2_Tin_ne hj'] at this; omega
      have h3 : (∑ k', if Tjk j k n = Tout k' n ∧ 1 ≤ n k' then nu k' else 0) = 0 := by
        apply Finset.sum_eq_zero; intro k' _
        rw [if_neg]; rintro ⟨h, _⟩
        have := congrFun h k
        rw [sn2_Tjk_apply_k hjk] at this
        by_cases hk' : k = k'
        · subst hk'; rw [sn2_Tout_self] at this; omega
        · rw [sn2_Tout_ne hk'] at this; omega
      rw [h1, h2, h3]; ring
    unfold reversedRates
    rw [hq]
    have hpos := sn2P_pos α g φ hφpos hα hg n
    have hk := sn2P_Tjk (migrationMarginal α g φ) α φ hu n hjk hn
    rw [← hπ, ← hπ] at hk
    have hαj := hα j
    field_simp
    linear_combination lam k j * hk
  · intro n j hn
    have hq : openMigrationRates lam mu nu φ (Tout j n) n = nu j := by
      rw [hrate]
      have h1 : (∑ j', ∑ k', if Tout j n = Tjk k' j' n ∧ 1 ≤ n k'
          then lam j' k' * φ j' (Tout j n j') else 0) = 0 := by
        apply Finset.sum_eq_zero; intro j' _
        apply Finset.sum_eq_zero; intro k' _
        by_cases hkk : k' = j'
        · subst hkk; simp [hlamdiag]
        · rw [if_neg]; rintro ⟨h, _⟩
          have := congrFun h j'
          rw [sn2_Tjk_apply_k hkk] at this
          by_cases hjj : j' = j
          · subst hjj; rw [sn2_Tout_self] at this; omega
          · rw [sn2_Tout_ne hjj] at this; omega
      have h2 : (∑ j', if Tout j n = Tin j' n then mu j' * φ j' (Tout j n j') else 0) = 0 := by
        apply Finset.sum_eq_zero; intro j' _
        rw [if_neg]; intro h
        have := congrFun h j
        rw [sn2_Tout_self] at this
        by_cases hj' : j = j'
        · subst hj'; rw [sn2_Tin_self] at this; omega
        · rw [sn2_Tin_ne hj'] at this; omega
      have h3 : (∑ k', if Tout j n = Tout k' n ∧ 1 ≤ n k' then nu k' else 0) = nu j := by
        rw [Finset.sum_eq_single j]
        · rw [if_pos ⟨rfl, hn⟩]
        · intro k' _ hk'
          rw [if_neg]; rintro ⟨h, _⟩
          have := congrFun h j
          rw [sn2_Tout_self, sn2_Tout_ne (Ne.symm hk')] at this; omega
        · simp
      rw [h1, h2, h3]; ring
    unfold reversedRates
    rw [hq]
    have hpos := sn2P_pos α g φ hφpos hα hg n
    have hk := sn2P_Tout (migrationMarginal α g φ) α φ hu n j hn
    rw [← hπ, ← hπ] at hk
    have hαj := hα j
    field_simp
    linear_combination nu j * hk
  · intro n k
    have hq : openMigrationRates lam mu nu φ (Tin k n) n = mu k * φ k (n k + 1) := by
      rw [hrate]
      have h1 : (∑ j', ∑ k', if Tin k n = Tjk k' j' n ∧ 1 ≤ n k'
          then lam j' k' * φ j' (Tin k n j') else 0) = 0 := by
        apply Finset.sum_eq_zero; intro j' _
        apply Finset.sum_eq_zero; intro k' _
        by_cases hkk : k' = j'
        · subst hkk; simp [hlamdiag]
        · rw [if_neg]; rintro ⟨h, hk'⟩
          have := congrFun h k'
          rw [sn2_Tjk_apply_j hkk] at this
          by_cases hkk' : k' = k
          · subst hkk'; rw [sn2_Tin_self] at this; omega
          · rw [sn2_Tin_ne hkk'] at this; omega
      have h2 : (∑ j', if Tin k n = Tin j' n then mu j' * φ j' (Tin k n j') else 0)
          = mu k * φ k (n k + 1) := by
        rw [Finset.sum_eq_single k]
        · rw [if_pos rfl, sn2_Tin_self]
        · intro j' _ hj'
          rw [if_neg]; intro h
          have := congrFun h k
          rw [sn2_Tin_self, sn2_Tin_ne (Ne.symm hj')] at this; omega
        · simp
      have h3 : (∑ k', if Tin k n = Tout k' n ∧ 1 ≤ n k' then nu k' else 0) = 0 := by
        apply Finset.sum_eq_zero; intro k' _
        rw [if_neg]; rintro ⟨h, _⟩
        have := congrFun h k
        rw [sn2_Tin_self] at this
        by_cases hk' : k = k'
        · subst hk'; rw [sn2_Tout_self] at this; omega
        · rw [sn2_Tout_ne hk'] at this; omega
      rw [h1, h2, h3]; ring
    unfold reversedRates
    rw [hq]
    have hpos := sn2P_pos α g φ hφpos hα hg n
    have hk := sn2P_Tin (migrationMarginal α g φ) α φ hu n k
    rw [← hπ, ← hπ] at hk
    field_simp
    linear_combination mu k * hk
