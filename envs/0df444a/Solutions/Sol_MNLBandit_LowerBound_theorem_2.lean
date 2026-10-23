-- Prove2me | solution 1 for MNLBandit.LowerBound.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:30:12.968987+00:00
-- url     : https://prove2.me/submissions/597b1945-dc91-48ad-add8-f47939de4859

import Mathlib
import Definitions.Def_MNLBandit_LowerBound_Setting



namespace MNLBandit.LowerBound

open Finset

lemma g57_prefixOf_snoc_castSucc {α : Type*} {s : ℕ} (h : Fin s → α) (x : α) (i : Fin s) :
    prefixOf (Fin.snoc h x : Fin (s+1) → α) (Fin.castSucc i) = prefixOf h i := by
  funext u
  simp only [prefixOf]
  have : (Fin.castLE (Fin.castSucc i).isLt.le u : Fin (s+1)) =
      Fin.castSucc (Fin.castLE i.isLt.le u) := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

lemma g57_prefixOf_snoc_last {α : Type*} {s : ℕ} (h : Fin s → α) (x : α) :
    prefixOf (Fin.snoc h x : Fin (s+1) → α) (Fin.last s) = h := by
  funext u
  simp only [prefixOf]
  have : (Fin.castLE (Fin.last s).isLt.le u : Fin (s+1)) = Fin.castSucc u := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

lemma g57_sum_snoc {X : Type*} [Fintype X] (s : ℕ) (F : (Fin (s+1) → X) → ℝ) :
    ∑ h, F h = ∑ h : Fin s → X, ∑ x, F (Fin.snoc h x) := by
  rw [← (Fin.snocEquiv (fun _ => X)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

lemma g57_tv {ι : Type*} [Fintype ι] (p R f : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hR : ∀ i, 0 < R i)
    (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) (hp1 : ∑ i, p i = 1)
    (hpR : ∑ i, p i * R i = 1) :
    (∑ i, p i * R i * f i - ∑ i, p i * f i) ^ 2 ≤ ∑ i, p i * (-Real.log (R i)) := by
  have e : ∀ i, (√(p i) * (√(R i) - 1)) * (√(p i) * (√(R i) + 1) * (f i - 1/2)) =
      (p i * R i * f i - p i * f i) - 1/2 * (p i * R i - p i) := by
    intro i
    have h1 := Real.mul_self_sqrt (hp i)
    have h2 := Real.mul_self_sqrt (hR i).le
    linear_combination (√(R i) * √(R i) - 1) * (f i - 1/2) * h1 + p i * (f i - 1/2) * h2
  have key : ∑ i, p i * R i * f i - ∑ i, p i * f i =
      ∑ i, (√(p i) * (√(R i) - 1)) * (√(p i) * (√(R i) + 1) * (f i - 1/2)) := by
    simp_rw [e]
    rw [sum_sub_distrib, ← mul_sum, sum_sub_distrib, sum_sub_distrib, hp1, hpR]
    ring
  have hb : ∑ i, (√(p i) * (√(R i) + 1) * (f i - 1/2)) ^ 2 ≤ 1 := by
    have : ∀ i, (√(p i) * (√(R i) + 1) * (f i - 1/2)) ^ 2 ≤ (p i * R i + p i) / 2 := by
      intro i
      rw [mul_pow, mul_pow, Real.sq_sqrt (hp i)]
      have hA : (√(R i) + 1) ^ 2 ≤ 2 * (R i + 1) := by
        nlinarith [sq_nonneg (√(R i) - 1), Real.sq_sqrt (hR i).le]
      have hB : (f i - 1/2) ^ 2 ≤ 1/4 := by nlinarith [hf0 i, hf1 i]
      calc p i * (√(R i) + 1) ^ 2 * (f i - 1/2) ^ 2
          = p i * ((√(R i) + 1) ^ 2 * (f i - 1/2) ^ 2) := by ring
        _ ≤ p i * (2 * (R i + 1) * (1/4)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hA hB (sq_nonneg _) (by linarith [hR i])) (hp i)
        _ = (p i * R i + p i) / 2 := by ring
    calc _ ≤ ∑ i, (p i * R i + p i) / 2 := sum_le_sum fun i _ => this i
      _ = 1 := by rw [← sum_div, sum_add_distrib, hp1, hpR]; norm_num
  have ha : ∑ i, (√(p i) * (√(R i) - 1)) ^ 2 ≤ ∑ i, p i * (-Real.log (R i)) := by
    have e2 : ∀ i, (√(p i) * (√(R i) - 1)) ^ 2 = p i * (2 - 2 * √(R i)) + (p i * R i - p i) := by
      intro i
      rw [mul_pow, Real.sq_sqrt (hp i)]
      have h2 := Real.sq_sqrt (hR i).le
      linear_combination p i * h2
    simp_rw [e2]
    rw [sum_add_distrib, sum_sub_distrib, hp1, hpR, sub_self, add_zero]
    apply sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (hp i)
    have hs : 0 < √(R i) := Real.sqrt_pos.mpr (hR i)
    have := Real.log_le_sub_one_of_pos hs
    rw [Real.log_sqrt (hR i).le] at this
    linarith
  rw [key]
  calc _ ≤ (∑ i, (√(p i) * (√(R i) - 1)) ^ 2) * ∑ i, (√(p i) * (√(R i) + 1) * (f i - 1/2)) ^ 2 :=
        sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (∑ i, (√(p i) * (√(R i) - 1)) ^ 2) * 1 := by
        gcongr
    _ ≤ _ := by rw [mul_one]; exact ha

noncomputable def g57L {X : Type*} (κ : (t : ℕ) → (Fin t → X) → X → ℝ) (s : ℕ)
    (h : Fin s → X) : ℝ :=
  ∏ t : Fin s, κ t (prefixOf h t) (h t)

def g57IsK {X : Type*} [Fintype X] (κ : (t : ℕ) → (Fin t → X) → X → ℝ) : Prop :=
  ∀ t (h : Fin t → X), (∀ x, 0 ≤ κ t h x) ∧ ∑ x, κ t h x = 1

noncomputable def g57E {X : Type*} [Fintype X] (κ : (t : ℕ) → (Fin t → X) → X → ℝ) (t : ℕ)
    (g : X → ℝ) : ℝ :=
  ∑ h : Fin t → X, g57L κ t h * ∑ x, κ t h x * g x

section gen
variable {X : Type*} [Fintype X] (κ : (t : ℕ) → (Fin t → X) → X → ℝ)

lemma g57L_snoc (s : ℕ) (h : Fin s → X) (x : X) :
    g57L κ (s+1) (Fin.snoc h x) = g57L κ s h * κ s h x := by
  unfold g57L
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [g57_prefixOf_snoc_castSucc, Fin.snoc_castSucc]
    rfl
  · rw [g57_prefixOf_snoc_last, Fin.snoc_last]
    rfl

lemma g57L_M2 (s : ℕ) (G : (Fin s → X) → X → ℝ) :
    ∑ h : Fin (s+1) → X, g57L κ (s+1) h * G (Fin.init h) (h (Fin.last s)) =
    ∑ h : Fin s → X, g57L κ s h * ∑ x, κ s h x * G h x := by
  rw [g57_sum_snoc]
  apply sum_congr rfl
  intro h _
  rw [mul_sum]
  apply sum_congr rfl
  intro x _
  rw [g57L_snoc, Fin.init_snoc, Fin.snoc_last]
  ring

variable {κ}

lemma g57L_M1 (hκ : g57IsK κ) (s : ℕ) (F : (Fin s → X) → ℝ) :
    ∑ h : Fin (s+1) → X, g57L κ (s+1) h * F (Fin.init h) =
    ∑ h : Fin s → X, g57L κ s h * F h := by
  have := g57L_M2 κ s (fun h _ => F h)
  rw [this]
  apply sum_congr rfl
  intro h _
  rw [← sum_mul, (hκ s h).2, one_mul]

lemma g57L_sum (hκ : g57IsK κ) : ∀ s, ∑ h : Fin s → X, g57L κ s h = 1
  | 0 => by simp [g57L]
  | s+1 => by
    have := g57L_M1 hκ s (fun _ => 1)
    simp only [mul_one] at this
    rw [this, g57L_sum hκ s]

lemma g57L_nonneg (hκ : g57IsK κ) (s : ℕ) (h : Fin s → X) : 0 ≤ g57L κ s h :=
  prod_nonneg fun t _ => (hκ _ _).1 _

lemma g57L_M3 (hκ : g57IsK κ) (t : ℕ) (F : (Fin t → X) → ℝ) : ∀ s (hts : t ≤ s),
    ∑ h : Fin s → X, g57L κ s h * F (fun u => h (Fin.castLE hts u)) =
    ∑ h : Fin t → X, g57L κ t h * F h := by
  intro s
  induction s with
  | zero =>
    intro hts
    obtain rfl : t = 0 := by omega
    apply sum_congr rfl
    intro h _
    congr 2
  | succ s ih =>
    intro hts
    rcases Nat.lt_or_ge s t with hlt | hle
    · obtain rfl : t = s + 1 := by omega
      apply sum_congr rfl
      intro h _
      congr 2
    · have := g57L_M1 hκ s (fun g => F (fun u => g (Fin.castLE hle u)))
      rw [← ih hle, ← this]
      apply sum_congr rfl
      intro h _
      congr 2

lemma g57L_marg (hκ : g57IsK κ) (T : ℕ) (t : Fin T) (φ : X → ℝ) :
    ∑ h : Fin T → X, g57L κ T h * φ (h t) = g57E κ t φ := by
  have h1 := g57L_M3 hκ (t+1) (fun g => φ (g (Fin.last t))) T t.isLt
  have h2 := g57L_M2 κ t (fun _ x => φ x)
  unfold g57E
  rw [← h2, ← h1]
  apply sum_congr rfl
  intro h _
  congr 3

lemma g57E_last (t : ℕ) (φ : X → ℝ) :
    ∑ h : Fin (t+1) → X, g57L κ (t+1) h * φ (h (Fin.last t)) = g57E κ t φ :=
  g57L_M2 κ t (fun _ x => φ x)

lemma g57E_mono (hκ : g57IsK κ) (t : ℕ) (g1 g2 : X → ℝ)
    (hg : ∀ h : Fin t → X, ∑ x, κ t h x * g1 x ≤ ∑ x, κ t h x * g2 x) :
    g57E κ t g1 ≤ g57E κ t g2 :=
  sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (hg h) (g57L_nonneg hκ t h)

lemma g57E_mono' (hκ : g57IsK κ) (t : ℕ) (g1 g2 : X → ℝ)
    (hg : ∀ (h : Fin t → X) x, 0 < κ t h x → g1 x ≤ g2 x) :
    g57E κ t g1 ≤ g57E κ t g2 := by
  apply g57E_mono hκ
  intro h
  apply sum_le_sum
  intro x _
  rcases ((hκ t h).1 x).lt_or_eq with hp | hp
  · exact mul_le_mul_of_nonneg_left (hg h x hp) hp.le
  · rw [← hp]; simp

lemma g57E_affine (hκ : g57IsK κ) (t : ℕ) (a b : ℝ) (g : X → ℝ) :
    g57E κ t (fun x => a + b * g x) = a + b * g57E κ t g := by
  unfold g57E
  have : ∀ h : Fin t → X, g57L κ t h * ∑ x, κ t h x * (a + b * g x) =
      a * g57L κ t h + b * (g57L κ t h * ∑ x, κ t h x * g x) := by
    intro h
    rw [show (∑ x, κ t h x * (a + b * g x)) = a * ∑ x, κ t h x + b * ∑ x, κ t h x * g x by
      rw [mul_sum, mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun x _ => by ring, (hκ t h).2]
    ring
  rw [sum_congr rfl (fun h _ => this h), sum_add_distrib, ← mul_sum, ← mul_sum, g57L_sum hκ,
    mul_one]

lemma g57E_sum {J : Type*} (Js : Finset J) (t : ℕ) (g : J → X → ℝ) :
    ∑ j ∈ Js, g57E κ t (g j) = g57E κ t (fun x => ∑ j ∈ Js, g j x) := by
  unfold g57E
  rw [sum_comm]
  apply sum_congr rfl
  intro h _
  rw [← mul_sum]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [mul_sum]

lemma g57_change {κ1 : (t : ℕ) → (Fin t → X) → X → ℝ} (hκ : g57IsK κ) (hκ1 : g57IsK κ1)
    (ρ : X → ℝ) (hρ : ∀ x, 0 < ρ x) (hrel : ∀ t h x, κ1 t h x = κ t h x * ρ x)
    (t : ℕ) (g : X → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) :
    (g57E κ1 t g - g57E κ t g) ^ 2 ≤
      ∑ u ∈ range (t+1), g57E κ u (fun x => -Real.log (ρ x)) := by
  have hL : ∀ s (h : Fin s → X), g57L κ1 s h = g57L κ s h * ∏ u, ρ (h u) := by
    intro s h
    unfold g57L
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun u _ => hrel _ _ _
  have tv := g57_tv (g57L κ (t+1)) (fun h => ∏ u, ρ (h u)) (fun h => g (h (Fin.last t)))
    (g57L_nonneg hκ _) (fun h => prod_pos fun u _ => hρ _) (fun h => hg0 _) (fun h => hg1 _)
    (g57L_sum hκ _) (by simp_rw [← hL]; exact g57L_sum hκ1 _)
  have e1 : ∑ h : Fin (t+1) → X, g57L κ (t+1) h * (∏ u, ρ (h u)) * g (h (Fin.last t)) =
      g57E κ1 t g := by
    rw [← g57E_last]
    simp_rw [hL]
  rw [e1, g57E_last] at tv
  refine tv.trans (le_of_eq ?_)
  have hne : ∀ h : Fin (t+1) → X, ∀ u ∈ (univ : Finset (Fin (t+1))), ρ (h u) ≠ 0 :=
    fun h u _ => (hρ _).ne'
  simp_rw [fun h => Real.log_prod (hne h), ← sum_neg_distrib, mul_sum]
  rw [sum_comm, ← Fin.sum_univ_eq_sum_range (fun u => g57E κ u (fun x => -Real.log (ρ x))) (t+1)]
  apply sum_congr rfl
  intro u _
  exact g57L_marg hκ (t+1) u (fun x => -Real.log (ρ x))

end gen

section mnl
variable {n : ℕ}

lemma g57_cp_sum (v₀ : ℝ) (v : Fin n → ℝ) (hv₀ : 0 < v₀) (hv : ∀ i, 0 ≤ v i)
    (S : Finset (Fin n)) : ∑ c, choiceProb v₀ v S c = 1 := by
  have hD : 0 < v₀ + ∑ j ∈ S, v j := by
    have := sum_nonneg fun j (_ : j ∈ S) => hv j; linarith
  rw [Fintype.sum_option]
  simp only [choiceProb]
  rw [sum_ite_mem, univ_inter, ← sum_div, ← add_div, div_self hD.ne']

lemma g57_cp_nonneg (v₀ : ℝ) (v : Fin n → ℝ) (hv₀ : 0 < v₀) (hv : ∀ i, 0 ≤ v i)
    (S : Finset (Fin n)) (c : Option (Fin n)) : 0 ≤ choiceProb v₀ v S c := by
  have hD : 0 < v₀ + ∑ j ∈ S, v j := by
    have := sum_nonneg fun j (_ : j ∈ S) => hv j; linarith
  cases c with
  | none => exact div_nonneg hv₀.le hD.le
  | some i =>
    simp only [choiceProb]
    split_ifs
    · exact div_nonneg (hv i) hD.le
    · exact le_rfl

noncomputable def g57κ (v₀ : ℝ) (v : Fin n → ℝ) (π : BPolicy n) :
    (t : ℕ) → (Fin t → Step n) → Step n → ℝ :=
  fun t h x => π t h x.1 * choiceProb v₀ v x.1 x.2

lemma g57κ_isK {π : BPolicy n} (hπ : IsBPolicy π) (v₀ : ℝ) (v : Fin n → ℝ) (hv₀ : 0 < v₀)
    (hv : ∀ i, 0 ≤ v i) : g57IsK (g57κ v₀ v π) := by
  intro t h
  refine ⟨fun x => mul_nonneg ((hπ t h).1 _) (g57_cp_nonneg v₀ v hv₀ hv _ _), ?_⟩
  rw [Fintype.sum_prod_type]
  have : ∀ S : Finset (Fin n), ∑ c, g57κ v₀ v π t h (S, c) = π t h S := by
    intro S
    simp only [g57κ]
    rw [← mul_sum, g57_cp_sum v₀ v hv₀ hv, mul_one]
  rw [sum_congr rfl (fun S _ => this S)]
  exact (hπ t h).2

lemma g57_regret_eq (I : Instance n) (hI : I.Valid) (K : ℕ) {π : BPolicy n} (hπ : IsBPolicy π)
    (T : ℕ) : regret I K π T =
      ∑ t ∈ range T, (I.optRevenue K - g57E (g57κ I.v₀ I.v π) t (fun x => I.revenue x.1)) := by
  have hK := g57κ_isK hπ I.v₀ I.v hI.1 (fun i => (hI.2.1 i).1)
  unfold regret
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  congr 1
  simp_rw [mul_sum]
  rw [sum_comm, ← Fin.sum_univ_eq_sum_range
    (fun t => g57E (g57κ I.v₀ I.v π) t (fun x => I.revenue x.1)) T]
  apply sum_congr rfl
  intro t _
  exact g57L_marg hK T t (fun x => I.revenue x.1)

noncomputable def g57ρ (v₀ : ℝ) (v0 v1 : Fin n → ℝ) (x : Step n) : ℝ :=
  if choiceProb v₀ v0 x.1 x.2 = 0 then 1 else choiceProb v₀ v1 x.1 x.2 / choiceProb v₀ v0 x.1 x.2

lemma g57_neglog (u : ℝ) (hu : 0 < u) : -Real.log u ≤ u⁻¹ - 1 := by
  rw [← Real.log_inv]; exact Real.log_le_sub_one_of_pos (inv_pos.mpr hu)

lemma g57_pneglog (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * -Real.log (q / p) ≤ p * (p / q - 1) := by
  have := g57_neglog (q / p) (div_pos hq hp)
  rw [inv_div] at this
  exact mul_le_mul_of_nonneg_left this hp.le

section pert
variable {v₀ α ϵ : ℝ} {G : Finset (Fin n)} {v0 v1 : Fin n → ℝ}

lemma g57_D1 (hv1 : ∀ i, v1 i = v0 i + if i ∈ G then ϵ else 0) (S : Finset (Fin n)) :
    ∑ j ∈ S, v1 j = ∑ j ∈ S, v0 j + (S.filter (· ∈ G)).card * ϵ := by
  simp_rw [hv1]
  rw [sum_add_distrib, ← sum_filter, sum_const, nsmul_eq_mul]

lemma g57_v1_nonneg (hϵ : 0 < ϵ) (hv0 : ∀ i, 0 ≤ v0 i)
    (hv1 : ∀ i, v1 i = v0 i + if i ∈ G then ϵ else 0) (i : Fin n) : 0 ≤ v1 i := by
  rw [hv1]; split_ifs <;> linarith [hv0 i]

lemma g57ρ_pos (hv₀ : 0 < v₀) (hϵ : 0 < ϵ) (hv0 : ∀ i, 0 ≤ v0 i)
    (hv1 : ∀ i, v1 i = v0 i + if i ∈ G then ϵ else 0) (x : Step n) :
    0 < g57ρ v₀ v0 v1 x := by
  have hv1n := g57_v1_nonneg hϵ hv0 hv1
  unfold g57ρ
  split_ifs with h
  · norm_num
  have h0 : 0 < choiceProb v₀ v0 x.1 x.2 :=
    lt_of_le_of_ne (g57_cp_nonneg v₀ v0 hv₀ hv0 _ _) (Ne.symm h)
  apply div_pos _ h0
  obtain ⟨S, c⟩ := x
  have hD1 : 0 < v₀ + ∑ j ∈ S, v1 j := by
    have := sum_nonneg fun j (_ : j ∈ S) => hv1n j; linarith
  have hD0 : 0 < v₀ + ∑ j ∈ S, v0 j := by
    have := sum_nonneg fun j (_ : j ∈ S) => hv0 j; linarith
  cases c with
  | none => exact div_pos hv₀ hD1
  | some i =>
    simp only [choiceProb] at h0 ⊢
    split_ifs at h0 ⊢ with hi
    · have : 0 < v0 i := (div_pos_iff_of_pos_right hD0).mp h0
      have : v0 i ≤ v1 i := by rw [hv1]; split_ifs <;> linarith
      exact div_pos (by linarith) hD1
    · exact absurd h0 (lt_irrefl 0)

lemma g57ρ_rel (hv₀ : 0 < v₀) (hα : 0 < α) (hv0 : ∀ i, 0 ≤ v0 i) (hG : ∀ i ∈ G, v0 i = α)
    (hv1 : ∀ i, v1 i = v0 i + if i ∈ G then ϵ else 0) (S : Finset (Fin n))
    (c : Option (Fin n)) :
    choiceProb v₀ v1 S c = choiceProb v₀ v0 S c * g57ρ v₀ v0 v1 (S, c) := by
  have hD0 : 0 < v₀ + ∑ j ∈ S, v0 j := by
    have := sum_nonneg fun j (_ : j ∈ S) => hv0 j; linarith
  unfold g57ρ
  dsimp only
  split_ifs with h
  · rw [h, zero_mul]
    cases c with
    | none =>
      exfalso
      simp only [choiceProb] at h
      exact (div_pos hv₀ hD0).ne' h
    | some i =>
      simp only [choiceProb] at h ⊢
      split_ifs at h ⊢ with hi
      · have h0 : v0 i = 0 := by
          rcases div_eq_zero_iff.mp h with h' | h'
          · exact h'
          · exact absurd h' hD0.ne'
        have hiG : i ∉ G := fun hiG => by rw [hG i hiG] at h0; linarith
        rw [hv1, if_neg hiG, h0, add_zero, zero_div]
      · rfl
  · field_simp

lemma g57_klstep (hv₀ : 0 < v₀) (hα : 0 < α) (hϵ : 0 < ϵ) (hv0 : ∀ i, 0 ≤ v0 i)
    (hG : ∀ i ∈ G, v0 i = α) (hv1 : ∀ i, v1 i = v0 i + if i ∈ G then ϵ else 0)
    (S : Finset (Fin n)) :
    ∑ c, choiceProb v₀ v0 S c * (-Real.log (g57ρ v₀ v0 v1 (S, c))) ≤
      (S.filter (· ∈ G)).card * ϵ ^ 2 / (v₀ * α) := by
  set m : ℝ := ((S.filter (· ∈ G)).card : ℝ) with hm
  set D0 := v₀ + ∑ j ∈ S, v0 j with hD0def
  have hD0 : 0 < D0 := by
    have := sum_nonneg fun j (_ : j ∈ S) => hv0 j; rw [hD0def]; linarith
  have hD1 : v₀ + ∑ j ∈ S, v1 j = D0 + m * ϵ := by rw [g57_D1 hv1 S, hD0def]; ring
  have hm0 : 0 ≤ m := by positivity
  set σ := ∑ j ∈ S.filter (fun j => ¬ j ∈ G), v0 j with hσ
  have hσ0 : 0 ≤ σ := sum_nonneg fun j _ => hv0 j
  have hD0σ : D0 = v₀ + m * α + σ := by
    rw [hD0def, ← sum_filter_add_sum_filter_not S (· ∈ G), hσ]
    rw [sum_congr rfl (fun j hj => hG j (mem_filter.mp hj).2), sum_const, nsmul_eq_mul, hm]
    ring
  set A := α * ϵ * (α * m - D0) / (D0 ^ 2 * (α + ϵ)) with hA
  set B := m * ϵ / D0 ^ 2 with hB
  have hpt : ∀ c, choiceProb v₀ v0 S c * (-Real.log (g57ρ v₀ v0 v1 (S, c))) ≤
      (match c with
       | none => v₀ * B
       | some i => if i ∈ S then (if i ∈ G then A else v0 i * B) else 0) := by
    intro c
    cases c with
    | none =>
      have hc0 : choiceProb v₀ v0 S none ≠ 0 := by
        simp only [choiceProb]; exact (div_pos hv₀ hD0).ne'
      simp only [g57ρ, if_neg hc0]
      refine (g57_pneglog _ _ (div_pos hv₀ hD0) ?_).trans (le_of_eq ?_)
      · simp only [choiceProb]; rw [hD1]; positivity
      · simp only [choiceProb]; rw [hD1, hB]; field_simp; ring
    | some i =>
      by_cases hc : choiceProb v₀ v0 S (some i) = 0
      · simp only [g57ρ, if_pos hc, Real.log_one, neg_zero, mul_zero]
        split_ifs with hi hiG
        · rw [hA]
          have : 0 ≤ D0 - α * m := by rw [hD0σ]; nlinarith
          simp only [choiceProb, if_pos hi] at hc
          rcases div_eq_zero_iff.mp hc with h' | h'
          · rw [hG i hiG] at h'; linarith
          · exact absurd h' (by rw [← hD0def]; exact hD0.ne')
        · exact mul_nonneg (hv0 i) (by positivity)
        · exact le_rfl
      · simp only [g57ρ, if_neg hc]
        have hi : i ∈ S := by
          by_contra hi; simp [choiceProb, hi] at hc
        have hp : 0 < v0 i := by
          simp only [choiceProb, if_pos hi] at hc
          rcases (hv0 i).lt_or_eq with h' | h'
          · exact h'
          · rw [← h', zero_div] at hc; exact absurd rfl hc
        rw [if_pos hi]
        have hpos0 : 0 < choiceProb v₀ v0 S (some i) := by
          simp only [choiceProb, if_pos hi]; exact div_pos hp hD0
        have hv1i : v0 i ≤ v1 i := by rw [hv1]; split_ifs <;> linarith
        have hpos1 : 0 < choiceProb v₀ v1 S (some i) := by
          simp only [choiceProb, if_pos hi]; rw [hD1]
          exact div_pos (by linarith) (by positivity)
        refine (g57_pneglog _ _ hpos0 hpos1).trans (le_of_eq ?_)
        simp only [choiceProb, if_pos hi]
        rw [hD1, ← hD0def]
        split_ifs with hiG
        · rw [hv1, if_pos hiG, hG i hiG, hA]
          field_simp
          ring
        · rw [hv1, if_neg hiG, add_zero, hB]
          field_simp
          ring
  refine (sum_le_sum fun c _ => hpt c).trans ?_
  rw [Fintype.sum_option]
  dsimp only
  rw [sum_ite_mem, univ_inter, sum_ite, sum_const, nsmul_eq_mul, ← hm, ← sum_mul, ← hσ]
  have key : v₀ * B + (m * A + σ * B) = m * ϵ ^ 2 * (D0 - m * α) / (D0 ^ 2 * (α + ϵ)) := by
    rw [hA, hB, hD0σ]
    field_simp
    ring
  rw [key, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 0 ≤ D0 - m * α := by rw [hD0σ]; linarith
  have h2 : D0 - m * α ≤ D0 := by nlinarith
  have h3 : v₀ ≤ D0 := by rw [hD0σ]; nlinarith
  have h4 : (D0 - m * α) * v₀ * α ≤ D0 * D0 * (α + ϵ) := by
    apply mul_le_mul (mul_le_mul h2 h3 hv₀.le hD0.le) (by linarith) hα.le (by positivity)
  have h5 : 0 ≤ m * ϵ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h4 h5]

end pert

end mnl

lemma g57_mnl_change {n : ℕ} {v₀ α ϵ : ℝ} {G : Finset (Fin n)} {v0 v1 : Fin n → ℝ}
    (hv₀ : 0 < v₀) (hα : 0 < α) (hϵ : 0 < ϵ) (hv0 : ∀ i, 0 ≤ v0 i)
    (hG : ∀ i ∈ G, v0 i = α) (hv1 : ∀ i, v1 i = v0 i + if i ∈ G then ϵ else 0)
    {π : BPolicy n} (hπ : IsBPolicy π) (t : ℕ) (g : Step n → ℝ)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) :
    (g57E (g57κ v₀ v1 π) t g - g57E (g57κ v₀ v0 π) t g) ^ 2 ≤
      ϵ ^ 2 / (v₀ * α) * ∑ u ∈ range (t+1),
        g57E (g57κ v₀ v0 π) u (fun x => ((x.1.filter (· ∈ G)).card : ℝ)) := by
  have hK0 := g57κ_isK hπ v₀ v0 hv₀ hv0
  have hK1 := g57κ_isK hπ v₀ v1 hv₀ (g57_v1_nonneg hϵ hv0 hv1)
  refine (g57_change hK0 hK1 (g57ρ v₀ v0 v1) (g57ρ_pos hv₀ hϵ hv0 hv1)
    (fun t h x => by simp only [g57κ]; rw [g57ρ_rel hv₀ hα hv0 hG hv1, mul_assoc])
    t g hg0 hg1).trans ?_
  rw [mul_sum]
  apply sum_le_sum
  intro u _
  have ha := g57E_affine hK0 u 0 (ϵ ^ 2 / (v₀ * α)) (fun x => ((x.1.filter (· ∈ G)).card : ℝ))
  rw [zero_add] at ha
  rw [← ha]
  apply g57E_mono hK0
  intro h
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply sum_le_sum
  intro S _
  simp only [g57κ]
  simp_rw [mul_assoc, ← mul_sum]
  apply mul_le_mul_of_nonneg_left _ ((hπ u h).1 S)
  have := g57_klstep hv₀ hα hϵ hv0 hG hv1 S
  rw [← sum_mul, g57_cp_sum v₀ v0 hv₀ hv0, one_mul, zero_add]
  calc _ ≤ _ := this
    _ = _ := by ring

lemma g57E_const {X : Type*} [Fintype X] {κ : (t : ℕ) → (Fin t → X) → X → ℝ}
    (hκ : g57IsK κ) (t : ℕ) (a : ℝ) : g57E κ t (fun _ => a) = a := by
  have := g57E_affine hκ t a 0 (fun _ => 0)
  simp only [zero_mul, add_zero] at this
  exact this

/-! Case A -/

lemma g57_cardG (n K N : ℕ) (hK : 0 < K) (hNK : N * K ≤ n) (j : Fin N) :
    (univ.filter (fun i : Fin n => (i : ℕ) / K = j)).card = K := by
  have hjK : (j : ℕ) * K + K ≤ n := by
    have : ((j : ℕ) + 1) * K ≤ N * K := Nat.mul_le_mul_right K j.isLt
    linarith [Nat.succ_mul (j : ℕ) K]
  suffices hs : (range K).card = (univ.filter (fun i : Fin n => (i : ℕ) / K = j)).card by
    rw [← hs, card_range]
  apply card_bij (fun a ha => (⟨(j : ℕ) * K + a, by
    have := mem_range.mp ha; omega⟩ : Fin n))
  · intro a ha
    have := mem_range.mp ha
    simp only [mem_filter, mem_univ, true_and]
    rw [show (j : ℕ) * K + a = a + (j : ℕ) * K by ring, Nat.add_mul_div_right _ _ hK,
      Nat.div_eq_of_lt this, zero_add]
  · intro a1 _ a2 _ h
    simp only [Fin.mk.injEq] at h
    omega
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    refine ⟨(b : ℕ) % K, mem_range.mpr (Nat.mod_lt _ hK), ?_⟩
    apply Fin.ext
    simp only
    have := Nat.div_add_mod (b : ℕ) K
    rw [hb] at this
    linarith [mul_comm (j : ℕ) K]

lemma g57_sum_mG (n K N : ℕ) (S : Finset (Fin n)) :
    ∑ j : Fin N, ((S.filter (· ∈ univ.filter (fun i : Fin n => (i : ℕ) / K = j))).card : ℝ)
      ≤ S.card := by
  have : ∀ j : Fin N, ((S.filter (· ∈ univ.filter (fun i : Fin n => (i : ℕ) / K = j))).card : ℝ)
      = ∑ i ∈ S, if (i : ℕ) / K = j then 1 else 0 := by
    intro j
    rw [card_filter]
    push_cast
    apply sum_congr rfl
    intro i _
    simp
  simp_rw [this]
  rw [sum_comm, card_eq_sum_ones]
  push_cast
  apply sum_le_sum
  intro i _
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  have : (univ.filter (fun j : Fin N => (i : ℕ) / K = j)).card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    simp only [mem_filter, mem_univ, true_and] at ha hb
    exact Fin.ext (ha.symm.trans hb)
  exact_mod_cast this

lemma g57_gapA (K x m ϵ : ℝ) (hK : 1 ≤ K) (hϵ : 0 < ϵ) (hϵ2 : ϵ ≤ 1/2) (hm0 : 0 ≤ m)
    (hmK : m ≤ K) (hx0 : 0 ≤ x) (hx : x ≤ K / 2 + m * ϵ) :
    x / (x + K) ≤ (K / 2 + K * ϵ) / ((K / 2 + K * ϵ) + K) - ϵ / 4 * (1 - m / K) := by
  have hxs : 0 < K / 2 + K * ϵ + K := by positivity
  have hxK : 0 < x + K := by linarith
  have e : (K / 2 + K * ϵ) / ((K / 2 + K * ϵ) + K) - x / (x + K) =
      K * ((K / 2 + K * ϵ) - x) / ((K / 2 + K * ϵ + K) * (x + K)) := by
    field_simp; ring
  have h1 : (K - m) * ϵ ≤ (K / 2 + K * ϵ) - x := by nlinarith
  have h2 : (K / 2 + K * ϵ + K) * (x + K) ≤ 4 * K ^ 2 := by
    have a1 : K / 2 + K * ϵ + K ≤ 2 * K := by nlinarith
    have a2 : x + K ≤ 2 * K := by nlinarith
    nlinarith [mul_le_mul a1 a2 hxK.le (by linarith)]
  have h3 : ϵ / 4 * (1 - m / K) = (K - m) * ϵ / (4 * K) := by field_simp
  have h4 : (K - m) * ϵ / (4 * K) ≤ K * ((K / 2 + K * ϵ) - x) / ((K / 2 + K * ϵ + K) * (x + K)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hKm : 0 ≤ (K - m) * ϵ := mul_nonneg (by linarith) hϵ.le
    calc (K - m) * ϵ * ((K / 2 + K * ϵ + K) * (x + K)) ≤ (K - m) * ϵ * (4 * K ^ 2) :=
          mul_le_mul_of_nonneg_left h2 hKm
      _ = K * ((K - m) * ϵ) * (4 * K) := by ring
      _ ≤ K * ((K / 2 + K * ϵ) - x) * (4 * K) := by gcongr
  linarith

lemma g57_pi_pos {n : ℕ} {π : BPolicy n} (hπ : IsBPolicy π) (v₀ : ℝ) (v : Fin n → ℝ) (t : ℕ)
    (h : Fin t → Step n) (x : Step n) (hx : 0 < g57κ v₀ v π t h x) : 0 < π t h x.1 := by
  rcases ((hπ t h).1 x.1).lt_or_eq with h' | h'
  · exact h'
  · simp only [g57κ, ← h', zero_mul] at hx; exact absurd hx (lt_irrefl 0)

def g57GA (n K N : ℕ) (j : Fin N) : Finset (Fin n) :=
  univ.filter (fun i : Fin n => (i : ℕ) / K = j)

noncomputable def g57instA (n K N : ℕ) (ϵ : ℝ) (j : Fin N) : Instance n where
  v₀ := K
  v := fun i => 1/2 + if i ∈ g57GA n K N j then ϵ else 0
  r := fun _ => 1

lemma g57_sumv_A (n K N : ℕ) (ϵ : ℝ) (j : Fin N) (S : Finset (Fin n)) :
    ∑ i ∈ S, (g57instA n K N ϵ j).v i =
      S.card / 2 + (S.filter (· ∈ g57GA n K N j)).card * ϵ := by
  simp only [g57instA]
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← sum_filter, sum_const, nsmul_eq_mul]
  ring

lemma g57_rev_A (n K N : ℕ) (ϵ : ℝ) (j : Fin N) (S : Finset (Fin n)) :
    (g57instA n K N ϵ j).revenue S = (∑ i ∈ S, (g57instA n K N ϵ j).v i) /
      (∑ i ∈ S, (g57instA n K N ϵ j).v i + K) := by
  unfold Instance.revenue ChoiceCDLP.MNL.mnlObjective
  simp only [g57instA, one_mul]

lemma g57_opt_A (n K N : ℕ) (hK : 0 < K) (hNK : N * K ≤ n) (ϵ : ℝ) (j : Fin N) :
    ((K : ℝ) / 2 + K * ϵ) / (((K : ℝ) / 2 + K * ϵ) + K) ≤ (g57instA n K N ϵ j).optRevenue K := by
  have hc := g57_cardG n K N hK hNK j
  have hG : g57GA n K N j ∈ cardFamily n K := by
    simp only [cardFamily, mem_filter, mem_univ, true_and]
    unfold g57GA; omega
  unfold Instance.optRevenue
  refine le_trans (le_of_eq ?_) (le_sup' _ hG)
  rw [g57_rev_A, g57_sumv_A, filter_true_of_mem (fun i hi => hi)]
  unfold g57GA
  rw [hc]

theorem g57_caseA (n K T : ℕ) (hK : 1 ≤ K) (h2K : 2 * K ≤ n) (hnT : n ≤ T) :
    ∃ (m : ℕ) (w : Fin m → ℝ) (inst : Fin m → Instance n),
        (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧ (∀ j, (inst j).Valid) ∧
        (∀ j k, (inst j).v₀ = (inst k).v₀ ∧ (inst j).r = (inst k).r) ∧
        ∀ π : BPolicy n, IsCardinalityK K π →
          1 / 2000 * Real.sqrt ((n : ℝ) * T / K) ≤ ∑ j, w j * regret (inst j) K π T := by
  have hK0 : 0 < K := by omega
  set N := n / K with hNdef
  have hN2 : 2 ≤ N := (Nat.le_div_iff_mul_le hK0).mpr (by linarith)
  have hNK : N * K ≤ n := Nat.div_mul_le_self n K
  have hnlt : n < K * N + K := by
    have h1 := Nat.div_add_mod n K
    have h2 := Nat.mod_lt n hK0
    rw [← hNdef] at h1
    omega
  have hNT : N ≤ T := by nlinarith
  have hNr : (2:ℝ) ≤ N := by exact_mod_cast hN2
  have hTr : (N:ℝ) ≤ T := by exact_mod_cast hNT
  have hT0 : (0:ℝ) < T := by linarith
  have hKr : (1:ℝ) ≤ K := by exact_mod_cast hK
  set ϵ : ℝ := 1 / 10 * Real.sqrt (N / T) with hϵdef
  have hsq : Real.sqrt (N / T) ≤ 1 := Real.sqrt_le_one.mpr ((div_le_one hT0).mpr hTr)
  have hsq0 : 0 < Real.sqrt (N / T) := Real.sqrt_pos.mpr (by positivity)
  have hϵ0 : 0 < ϵ := by positivity
  have hϵ1 : ϵ ≤ 1 / 10 := by rw [hϵdef]; linarith
  have hϵ2 : ϵ ^ 2 * T = N / 100 := by
    rw [hϵdef, mul_pow, Real.sq_sqrt (by positivity)]; field_simp; ring
  refine ⟨N, fun _ => 1 / N, g57instA n K N ϵ, fun _ => by positivity, ?_, ?_, ?_, ?_⟩
  · rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  · intro j
    refine ⟨by simp [g57instA]; omega, fun i => ⟨?_, ?_⟩, fun i => ⟨by simp [g57instA], by simp [g57instA]⟩⟩
    · simp only [g57instA]; split_ifs <;> linarith
    · simp only [g57instA]; split_ifs <;> linarith
  · intro j k; exact ⟨rfl, rfl⟩
  intro π hπ
  have hπB := hπ.1
  set κ0 := g57κ (K : ℝ) (fun _ => (1:ℝ)/2) π with hκ0
  have hK0isK : g57IsK κ0 := g57κ_isK hπB _ _ (by positivity) (fun _ => by norm_num)
  -- m_j and f_j
  set mj : Fin N → Step n → ℝ := fun j x => ((x.1.filter (· ∈ g57GA n K N j)).card : ℝ) with hmj
  have hmj0 : ∀ j x, 0 ≤ mj j x := fun j x => by positivity
  have hmjK : ∀ j x, mj j x ≤ K := by
    intro j x
    simp only [hmj]
    have := card_le_card (filter_subset (· ∈ g57GA n K N j) x.1)
    have h2 : (x.1.filter (· ∈ g57GA n K N j)).card ≤ (g57GA n K N j).card :=
      card_le_card (fun i hi => (mem_filter.mp hi).2)
    rw [show (g57GA n K N j).card = K from g57_cardG n K N hK0 hNK j] at h2
    exact_mod_cast h2
  set Rs : ℝ := ((K : ℝ) / 2 + K * ϵ) / (((K : ℝ) / 2 + K * ϵ) + K) with hRs
  -- Step 1: regret lower bound per j
  have step1 : ∀ j : Fin N, ∑ t ∈ range T, ϵ / 4 * (1 -
      g57E (g57κ (K:ℝ) (g57instA n K N ϵ j).v π) t (fun x => mj j x / K)) ≤
      regret (g57instA n K N ϵ j) K π T := by
    intro j
    have hValid : (g57instA n K N ϵ j).Valid := by
      refine ⟨by simp [g57instA]; omega, fun i => ⟨?_, ?_⟩, fun i => ⟨by simp [g57instA], by simp [g57instA]⟩⟩
      · simp only [g57instA]; split_ifs <;> linarith
      · simp only [g57instA]; split_ifs <;> linarith
    have hKj : g57IsK (g57κ (K:ℝ) (g57instA n K N ϵ j).v π) :=
      g57κ_isK hπB _ _ (by positivity) (fun i => (hValid.2.1 i).1)
    rw [g57_regret_eq _ hValid K hπB T]
    apply sum_le_sum
    intro t _
    have hopt := g57_opt_A n K N hK0 hNK ϵ j
    have hE : g57E (g57κ (K:ℝ) (g57instA n K N ϵ j).v π) t
        (fun x => (g57instA n K N ϵ j).revenue x.1) ≤
        (Rs - ϵ / 4) + ϵ / 4 * g57E (g57κ (K:ℝ) (g57instA n K N ϵ j).v π) t
          (fun x => mj j x / K) := by
      rw [← g57E_affine hKj]
      apply g57E_mono' hKj
      intro h x hx
      have hpos := g57_pi_pos hπB _ _ t h x hx
      have hcard := hπ.2 t h x.1 hpos
      rw [g57_rev_A, g57_sumv_A]
      have hS : ((x.1.card : ℝ)) ≤ K := by exact_mod_cast hcard
      have := g57_gapA K (x.1.card / 2 + mj j x * ϵ) (mj j x) ϵ hKr hϵ0 (by linarith)
        (hmj0 j x) (hmjK j x) (by have := hmj0 j x; positivity) (by linarith)
      simp only [hmj] at this ⊢
      rw [hRs]
      linarith
    have hv0 : (g57instA n K N ϵ j).v₀ = (K:ℝ) := rfl
    rw [hv0]
    linarith
  have step3 : ∀ u, ∑ j, g57E κ0 u (mj j) ≤ K := by
    intro u
    rw [g57E_sum univ u mj]
    calc _ ≤ g57E κ0 u (fun _ => (K:ℝ)) := g57E_mono' hK0isK u _ _ (fun h x hx => by
            have hpos := g57_pi_pos hπB _ _ u h x hx
            have hcard := hπ.2 u h x.1 hpos
            have h1 := g57_sum_mG n K N x.1
            have h2 : (x.1.card : ℝ) ≤ K := by exact_mod_cast hcard
            exact le_trans h1 h2)
      _ = K := g57E_const hK0isK u K
  have hz : ∀ j t, g57E κ0 t (fun x => mj j x / K) = g57E κ0 t (mj j) / K := by
    intro j t
    have := g57E_affine hK0isK t 0 (1/K) (mj j)
    rw [show (fun x => mj j x / K) = (fun x => 0 + 1/K * mj j x) by funext x; ring, this]
    ring
  have step2 : ∀ j t, g57E (g57κ (K:ℝ) (g57instA n K N ϵ j).v π) t (fun x => mj j x / K) ≤
      g57E κ0 t (mj j) / K + 1/4 +
        ϵ ^ 2 / (K * (1/2)) * ∑ u ∈ range (t+1), g57E κ0 u (mj j) := by
    intro j t
    have hc := g57_mnl_change (v₀ := (K:ℝ)) (α := 1/2) (ϵ := ϵ) (G := g57GA n K N j)
      (v0 := fun _ => (1:ℝ)/2) (v1 := (g57instA n K N ϵ j).v) (by positivity) (by norm_num) hϵ0
      (fun _ => by norm_num) (fun _ _ => rfl) (fun i => rfl) hπB t (fun x => mj j x / K)
      (fun x => div_nonneg (hmj0 j x) (by positivity))
      (fun x => (div_le_one (by positivity)).mpr (hmjK j x))
    have hc' : (g57E (g57κ (K:ℝ) (g57instA n K N ϵ j).v π) t (fun x => mj j x / K) -
        g57E κ0 t (fun x => mj j x / K)) ^ 2 ≤
        ϵ ^ 2 / (K * (1/2)) * ∑ u ∈ range (t+1), g57E κ0 u (mj j) := hc
    rw [hz] at hc'
    nlinarith [sq_nonneg (g57E (g57κ (K:ℝ) (g57instA n K N ϵ j).v π) t (fun x => mj j x / K) -
        g57E κ0 t (mj j) / K - 1/2)]
  have hsum_e : ∀ t ∈ range T, ∑ j, g57E (g57κ (K:ℝ) (g57instA n K N ϵ j).v π) t
      (fun x => mj j x / K) ≤ 1 + N / 4 + N / 50 := by
    intro t ht
    have htT : ((t:ℝ) + 1) ≤ T := by
      have := mem_range.mp ht; exact_mod_cast this
    have hc0 : 0 ≤ ϵ ^ 2 / (K * (1/2)) := by positivity
    have hA : ∑ j, g57E κ0 t (mj j) / K ≤ 1 := by
      rw [← sum_div, div_le_one (by positivity)]; exact step3 t
    have hB : ∑ j, ∑ u ∈ range (t+1), g57E κ0 u (mj j) ≤ (t + 1) * K := by
      rw [sum_comm]
      calc _ ≤ ∑ u ∈ range (t+1), (K:ℝ) := sum_le_sum fun u _ => step3 u
        _ = (t + 1) * K := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
    calc _ ≤ ∑ j, (g57E κ0 t (mj j) / K + 1/4 +
            ϵ ^ 2 / (K * (1/2)) * ∑ u ∈ range (t+1), g57E κ0 u (mj j)) :=
          sum_le_sum fun j _ => step2 j t
      _ = ∑ j, g57E κ0 t (mj j) / K + N / 4 +
            ϵ ^ 2 / (K * (1/2)) * ∑ j, ∑ u ∈ range (t+1), g57E κ0 u (mj j) := by
          rw [sum_add_distrib, sum_add_distrib, ← mul_sum, sum_const, card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ 1 + N / 4 + ϵ ^ 2 / (K * (1/2)) * ((t + 1) * K) := by
          gcongr
      _ ≤ 1 + N / 4 + N / 50 := by
          have e : ϵ ^ 2 / (K * (1/2)) * ((t + 1) * K) = 2 * ϵ ^ 2 * (t + 1) := by
            field_simp
          rw [e]
          nlinarith [sq_nonneg ϵ]
  rw [← mul_sum]
  have hmain : T * ϵ * N / 20 ≤ ∑ j, ∑ t ∈ range T, ϵ / 4 * (1 -
      g57E (g57κ (K:ℝ) (g57instA n K N ϵ j).v π) t (fun x => mj j x / K)) := by
    rw [sum_comm]
    have : ∀ t ∈ range T, ϵ * N / 20 ≤ ∑ j, ϵ / 4 * (1 -
        g57E (g57κ (K:ℝ) (g57instA n K N ϵ j).v π) t (fun x => mj j x / K)) := by
      intro t ht
      rw [← mul_sum, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]
      nlinarith [hsum_e t ht]
    calc T * ϵ * N / 20 = ∑ t ∈ range T, ϵ * N / 20 := by
          rw [sum_const, card_range, nsmul_eq_mul]; ring
      _ ≤ _ := sum_le_sum this
  have hsqrt : Real.sqrt ((n : ℝ) * T / K) ≤ 10 * T * Real.sqrt (N / T) := by
    rw [show 10 * (T:ℝ) * Real.sqrt (N / T) = Real.sqrt ((10 * T) ^ 2 * (N / T)) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by positivity)]
    have hn : (n:ℝ) ≤ K * N + K := by exact_mod_cast hnlt.le
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hn (show (0:ℝ) ≤ T by positivity)]
  calc 1 / 2000 * Real.sqrt ((n : ℝ) * T / K) ≤ T * ϵ / 20 := by
        rw [hϵdef]; nlinarith
    _ = 1 / N * (T * ϵ * N / 20) := by field_simp
    _ ≤ 1 / N * ∑ j, ∑ t ∈ range T, ϵ / 4 * (1 -
          g57E (g57κ (K:ℝ) (g57instA n K N ϵ j).v π) t (fun x => mj j x / K)) := by
        gcongr
    _ ≤ 1 / N * ∑ j, regret (g57instA n K N ϵ j) K π T := by
        gcongr with j
        exact step1 j

/-! Case B -/

def g57GB (n : ℕ) : Finset (Fin n) := univ.filter (fun i : Fin n => (i : ℕ) = 0)

noncomputable def g57vB (n : ℕ) (ϵ : ℝ) (b : Fin 2) : Fin n → ℝ :=
  fun i => (if (i : ℕ) ≤ 1 then 1/2 else 0) + if (b : ℕ) = 1 ∧ i ∈ g57GB n then ϵ else 0

noncomputable def g57rB (n : ℕ) (ϵ : ℝ) : Fin n → ℝ :=
  fun i => if (i : ℕ) = 0 then 1 else if (i : ℕ) = 1 then (1 + ϵ) / (3 + 2 * ϵ) else 0

noncomputable def g57instB (n : ℕ) (ϵ : ℝ) (b : Fin 2) : Instance n where
  v₀ := 1
  v := g57vB n ϵ b
  r := g57rB n ϵ

lemma g57_sum2 {n : ℕ} (hn : 2 ≤ n) (g : Fin n → ℝ) (hg : ∀ i : Fin n, 2 ≤ (i : ℕ) → g i = 0)
    (S : Finset (Fin n)) :
    ∑ i ∈ S, g i = (if (⟨0, by omega⟩ : Fin n) ∈ S then (1:ℝ) else 0) * g ⟨0, by omega⟩ +
      (if (⟨1, by omega⟩ : Fin n) ∈ S then (1:ℝ) else 0) * g ⟨1, by omega⟩ := by
  have hpt : ∀ i : Fin n, g i = (if i = ⟨0, by omega⟩ then g i else 0) +
      (if i = ⟨1, by omega⟩ then g i else 0) := by
    intro i
    by_cases h0 : (i : ℕ) = 0
    · have : i = ⟨0, by omega⟩ := Fin.ext h0
      rw [if_pos this, if_neg (fun h => by have := congrArg Fin.val h; simp only at this; omega)]
      ring
    by_cases h1 : (i : ℕ) = 1
    · have : i = ⟨1, by omega⟩ := Fin.ext h1
      rw [if_pos this, if_neg (fun h => by have := congrArg Fin.val h; simp only at this; omega)]
      ring
    have hi0 : i ≠ ⟨0, by omega⟩ := fun h => h0 (by rw [h])
    have hi1 : i ≠ ⟨1, by omega⟩ := fun h => h1 (by rw [h])
    rw [if_neg hi0, if_neg hi1, hg i (by omega)]; ring
  rw [sum_congr rfl (fun i _ => hpt i), sum_add_distrib, sum_ite_eq', sum_ite_eq']
  split_ifs <;> simp

lemma g57_gapB0 (ϵ a0 a1 : ℝ) (hϵ : 0 < ϵ) (hϵ1 : ϵ ≤ 1/10) (ha0 : a0 = 0 ∨ a0 = 1)
    (ha1 : a1 = 0 ∨ a1 = 1) :
    (a0 * (1 * (1/2)) + a1 * ((1 + ϵ) / (3 + 2 * ϵ) * (1/2))) / (a0 * (1/2) + a1 * (1/2) + 1)
      ≤ (1/2 + (1 + ϵ) / (3 + 2 * ϵ) * (1/2)) / (1/2 + 1/2 + 1) + (-(ϵ / 48) + ϵ / 48 * a1) := by
  set ρ := (1 + ϵ) / (3 + 2 * ϵ) with hρ
  have hρe : ρ * (3 + 2 * ϵ) = 1 + ϵ := by rw [hρ]; field_simp
  have hρ1 : ρ ≤ 1/2 := by nlinarith
  have hρ0 : 0 ≤ ρ := by positivity
  have h3 : ϵ / 4 ≤ 3 * ρ - 1 := by nlinarith
  rcases ha0 with rfl | rfl <;> rcases ha1 with rfl | rfl <;> norm_num
  · nlinarith
  · nlinarith
  · nlinarith

lemma g57_gapB1 (ϵ a0 a1 : ℝ) (hϵ : 0 < ϵ) (hϵ1 : ϵ ≤ 1/10) (ha0 : a0 = 0 ∨ a0 = 1)
    (ha1 : a1 = 0 ∨ a1 = 1) :
    (a0 * (1 * (1/2 + ϵ)) + a1 * ((1 + ϵ) / (3 + 2 * ϵ) * (1/2))) /
        (a0 * (1/2 + ϵ) + a1 * (1/2) + 1)
      ≤ (1/2 + ϵ) / (1/2 + ϵ + 1) + (-(ϵ / 48)) * a1 := by
  set ρ := (1 + ϵ) / (3 + 2 * ϵ) with hρ
  have hρe : ρ * (3 + 2 * ϵ) = 1 + ϵ := by rw [hρ]; field_simp
  have hρ1 : ρ ≤ 1/2 := by nlinarith
  have hρ0 : 0 ≤ ρ := by positivity
  rcases ha0 with rfl | rfl <;> rcases ha1 with rfl | rfl <;> norm_num
  · positivity
  · rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
    nlinarith
  · rw [div_add' _ _ _ (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hρe, mul_pos hϵ hϵ, mul_pos (mul_pos hϵ hϵ) hϵ,
      mul_le_mul_of_nonneg_left hϵ1 (mul_pos hϵ hϵ).le, mul_le_mul_of_nonneg_left hϵ1 hϵ.le]

lemma g57_revB {n : ℕ} (hn : 2 ≤ n) (ϵ : ℝ) (b : Fin 2) (S : Finset (Fin n)) :
    (g57instB n ϵ b).revenue S =
      ((if (⟨0, by omega⟩ : Fin n) ∈ S then (1:ℝ) else 0) *
          (1 * (1/2 + if (b:ℕ) = 1 then ϵ else 0)) +
        (if (⟨1, by omega⟩ : Fin n) ∈ S then (1:ℝ) else 0) * ((1 + ϵ) / (3 + 2 * ϵ) * (1/2))) /
      ((if (⟨0, by omega⟩ : Fin n) ∈ S then (1:ℝ) else 0) * (1/2 + if (b:ℕ) = 1 then ϵ else 0) +
        (if (⟨1, by omega⟩ : Fin n) ∈ S then (1:ℝ) else 0) * (1/2) + 1) := by
  have hz : ∀ i : Fin n, 2 ≤ (i:ℕ) → g57vB n ϵ b i = 0 := fun i hi => by
    simp only [g57vB, g57GB, mem_filter, mem_univ, true_and]
    rw [if_neg (by omega), if_neg (by omega)]; ring
  have h1 := g57_sum2 hn (fun i => g57rB n ϵ i * g57vB n ϵ b i)
    (fun i hi => by rw [hz i hi, mul_zero]) S
  have h2 := g57_sum2 hn (g57vB n ϵ b) hz S
  unfold Instance.revenue ChoiceCDLP.MNL.mnlObjective
  simp only [g57instB]
  rw [h1, h2]
  simp [g57vB, g57rB, g57GB]

theorem g57_caseB (n K T : ℕ) (hn : 2 ≤ n) (hK : 1 ≤ K) (hKn : n < 2 * K) (hnT : n ≤ T) :
    ∃ (m : ℕ) (w : Fin m → ℝ) (inst : Fin m → Instance n),
        (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧ (∀ j, (inst j).Valid) ∧
        (∀ j k, (inst j).v₀ = (inst k).v₀ ∧ (inst j).r = (inst k).r) ∧
        ∀ π : BPolicy n, IsCardinalityK K π →
          1 / 2000 * Real.sqrt ((n : ℝ) * T / K) ≤ ∑ j, w j * regret (inst j) K π T := by
  have hK2 : 2 ≤ K := by omega
  have hTr : (1:ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
  have hT0 : (0:ℝ) < T := by linarith
  have hsT : 1 ≤ Real.sqrt T := by
    have := Real.sqrt_le_sqrt hTr; rwa [Real.sqrt_one] at this
  set ϵ : ℝ := 1 / (10 * Real.sqrt T) with hϵdef
  have hϵ0 : 0 < ϵ := by positivity
  have hϵ1 : ϵ ≤ 1 / 10 := by
    rw [hϵdef, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hϵT : ϵ ^ 2 * T = 1 / 100 := by
    rw [hϵdef, div_pow, mul_pow, Real.sq_sqrt hT0.le]; field_simp; ring
  have hTϵ : T * ϵ = Real.sqrt T / 10 := by
    rw [hϵdef]
    have := Real.mul_self_sqrt hT0.le
    field_simp
    linarith
  have hρ0 : 0 ≤ (1 + ϵ) / (3 + 2 * ϵ) := by positivity
  have hρ1 : (1 + ϵ) / (3 + 2 * ϵ) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hValid : ∀ b, (g57instB n ϵ b).Valid := by
    intro b
    refine ⟨by simp [g57instB], fun i => ⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩⟩
    · simp only [g57instB, g57vB]; split_ifs <;> linarith
    · simp only [g57instB, g57vB]; split_ifs <;> linarith
    · simp only [g57instB, g57rB]; split_ifs <;> linarith
    · simp only [g57instB, g57rB]; split_ifs <;> linarith
  refine ⟨2, fun _ => 1 / 2, g57instB n ϵ, fun _ => by norm_num, by simp, hValid,
    fun j k => ⟨rfl, rfl⟩, ?_⟩
  intro π hπ
  have hπB := hπ.1
  have hv0 : ∀ i, 0 ≤ g57vB n ϵ 0 i := fun i => by
    simp only [g57vB]; split_ifs <;> linarith
  have hG : ∀ i ∈ g57GB n, g57vB n ϵ 0 i = 1 / 2 := by
    intro i hi
    simp only [g57GB, mem_filter, mem_univ, true_and] at hi
    simp [g57vB, hi]
  have hv1 : ∀ i, g57vB n ϵ 1 i = g57vB n ϵ 0 i + if i ∈ g57GB n then ϵ else 0 := by
    intro i; simp [g57vB]
  have hK0 : g57IsK (g57κ 1 (g57vB n ϵ 0) π) := g57κ_isK hπB _ _ one_pos hv0
  have hK1 : g57IsK (g57κ 1 (g57vB n ϵ 1) π) := g57κ_isK hπB _ _ one_pos (fun i => (hValid 1).2.1 i |>.1)
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  set f : Step n → ℝ := fun x => if i1 ∈ x.1 then 1 else 0 with hf
  have hf0 : ∀ x, 0 ≤ f x := fun x => by simp only [hf]; split_ifs <;> norm_num
  have hf1 : ∀ x, f x ≤ 1 := fun x => by simp only [hf]; split_ifs <;> norm_num
  have hA01 : ∀ (P : Prop) [Decidable P], ((if P then (1:ℝ) else 0) = 0 ∨ (if P then (1:ℝ) else 0) = 1) := by
    intro P _; split_ifs <;> simp
  set R0 : ℝ := (1/2 + (1 + ϵ) / (3 + 2 * ϵ) * (1/2)) / (1/2 + 1/2 + 1) with hR0
  set R1 : ℝ := (1/2 + ϵ) / (1/2 + ϵ + 1) with hR1
  have hS01 : ({⟨0, by omega⟩, i1} : Finset (Fin n)) ∈ cardFamily n K := by
    simp only [cardFamily, mem_filter, mem_univ, true_and]
    exact (card_le_two).trans hK2
  have hS0 : ({⟨0, by omega⟩} : Finset (Fin n)) ∈ cardFamily n K := by
    simp only [cardFamily, mem_filter, mem_univ, true_and, card_singleton]; omega
  have hopt0 : R0 ≤ (g57instB n ϵ 0).optRevenue K := by
    refine le_trans (le_of_eq ?_) (le_sup' _ hS01)
    rw [g57_revB hn]
    have : (⟨0, by omega⟩ : Fin n) ≠ i1 := by simp [hi1, Fin.ext_iff]
    simp [hi1, hR0]
  have hopt1 : R1 ≤ (g57instB n ϵ 1).optRevenue K := by
    refine le_trans (le_of_eq ?_) (le_sup' _ hS0)
    rw [g57_revB hn]
    have : i1 ∉ ({⟨0, by omega⟩} : Finset (Fin n)) := by simp [hi1, Fin.ext_iff]
    simp [hR1]
  have reg0 : ∑ t ∈ range T, ϵ / 48 * (1 - g57E (g57κ 1 (g57vB n ϵ 0) π) t f) ≤
      regret (g57instB n ϵ 0) K π T := by
    rw [g57_regret_eq _ (hValid 0) K hπB T]
    apply sum_le_sum
    intro t _
    have hE : g57E (g57κ 1 (g57vB n ϵ 0) π) t (fun x => (g57instB n ϵ 0).revenue x.1) ≤
        (R0 - ϵ / 48) + ϵ / 48 * g57E (g57κ 1 (g57vB n ϵ 0) π) t f := by
      rw [← g57E_affine hK0]
      apply g57E_mono' hK0
      intro h x _
      rw [g57_revB hn]
      have := g57_gapB0 ϵ _ _ hϵ0 hϵ1 (hA01 ((⟨0, by omega⟩ : Fin n) ∈ x.1)) (hA01 (i1 ∈ x.1))
      simp only [hf]
      norm_num at this ⊢
      linarith
    have : (g57instB n ϵ 0).v₀ = 1 := rfl
    rw [this]
    change _ ≤ (g57instB n ϵ 0).optRevenue K - g57E (g57κ 1 (g57vB n ϵ 0) π) t
      (fun x => (g57instB n ϵ 0).revenue x.1)
    linarith
  have reg1 : ∑ t ∈ range T, ϵ / 48 * g57E (g57κ 1 (g57vB n ϵ 1) π) t f ≤
      regret (g57instB n ϵ 1) K π T := by
    rw [g57_regret_eq _ (hValid 1) K hπB T]
    apply sum_le_sum
    intro t _
    have hE : g57E (g57κ 1 (g57vB n ϵ 1) π) t (fun x => (g57instB n ϵ 1).revenue x.1) ≤
        R1 + (-(ϵ / 48)) * g57E (g57κ 1 (g57vB n ϵ 1) π) t f := by
      rw [← g57E_affine hK1]
      apply g57E_mono' hK1
      intro h x _
      rw [g57_revB hn]
      have := g57_gapB1 ϵ _ _ hϵ0 hϵ1 (hA01 ((⟨0, by omega⟩ : Fin n) ∈ x.1)) (hA01 (i1 ∈ x.1))
      simp only [hf]
      norm_num at this ⊢
      linarith
    change _ ≤ (g57instB n ϵ 1).optRevenue K - g57E (g57κ 1 (g57vB n ϵ 1) π) t
      (fun x => (g57instB n ϵ 1).revenue x.1)
    linarith
  have hmB : ∀ u, g57E (g57κ 1 (g57vB n ϵ 0) π) u
      (fun x => ((x.1.filter (· ∈ g57GB n)).card : ℝ)) ≤ 1 := by
    intro u
    calc _ ≤ g57E (g57κ 1 (g57vB n ϵ 0) π) u (fun _ => (1:ℝ)) := by
          apply g57E_mono' hK0
          intro h x _
          have h1 : (x.1.filter (· ∈ g57GB n)).card ≤ (g57GB n).card :=
            card_le_card (fun i hi => (mem_filter.mp hi).2)
          have h2 : (g57GB n).card ≤ 1 := by
            apply card_le_one.mpr
            intro a ha b hb
            simp only [g57GB, mem_filter, mem_univ, true_and] at ha hb
            exact Fin.ext (ha.trans hb.symm)
          exact_mod_cast h1.trans h2
      _ = 1 := g57E_const hK0 u 1
  have hdiff : ∀ t ∈ range T, g57E (g57κ 1 (g57vB n ϵ 0) π) t f -
      g57E (g57κ 1 (g57vB n ϵ 1) π) t f ≤ 3 / 20 := by
    intro t ht
    have htT : ((t:ℝ) + 1) ≤ T := by
      have := mem_range.mp ht; exact_mod_cast this
    have hc := g57_mnl_change (v₀ := 1) (α := 1/2) (ϵ := ϵ) (G := g57GB n)
      one_pos (by norm_num) hϵ0 hv0 hG hv1 hπB t f hf0 hf1
    have hs : ∑ u ∈ range (t+1), g57E (g57κ 1 (g57vB n ϵ 0) π) u
        (fun x => ((x.1.filter (· ∈ g57GB n)).card : ℝ)) ≤ t + 1 := by
      calc _ ≤ ∑ u ∈ range (t+1), (1:ℝ) := sum_le_sum fun u _ => hmB u
        _ = t + 1 := by simp
    have hc2 : (g57E (g57κ 1 (g57vB n ϵ 1) π) t f - g57E (g57κ 1 (g57vB n ϵ 0) π) t f) ^ 2
        ≤ 1 / 50 := by
      refine hc.trans ?_
      calc ϵ ^ 2 / (1 * (1/2)) * _ ≤ ϵ ^ 2 / (1 * (1/2)) * (t + 1) :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = 2 * (ϵ ^ 2 * (t + 1)) := by ring
        _ ≤ 2 * (ϵ ^ 2 * T) := by gcongr
        _ = 1 / 50 := by rw [hϵT]; norm_num
    nlinarith
  rw [Fin.sum_univ_two]
  have hsqrt : Real.sqrt ((n : ℝ) * T / K) ≤ 3 / 2 * Real.sqrt T := by
    rw [show 3 / 2 * Real.sqrt T = Real.sqrt ((3/2) ^ 2 * T) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    have hKr : (0:ℝ) < K := by positivity
    rw [div_le_iff₀ hKr]
    have : (n:ℝ) ≤ 2 * K := by exact_mod_cast hKn.le
    nlinarith
  have hsum : T * (ϵ / 48 * (17 / 20)) ≤ ∑ t ∈ range T, ϵ / 48 * (1 - g57E (g57κ 1 (g57vB n ϵ 0) π) t f) +
      ∑ t ∈ range T, ϵ / 48 * g57E (g57κ 1 (g57vB n ϵ 1) π) t f := by
    rw [← sum_add_distrib]
    calc T * (ϵ / 48 * (17 / 20)) = ∑ t ∈ range T, ϵ / 48 * (17 / 20) := by
          rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ _ := by
          apply sum_le_sum
          intro t ht
          have := hdiff t ht
          nlinarith
  have hfin : 1 / 2000 * Real.sqrt ((n : ℝ) * T / K) ≤ 1 / 2 * (T * (ϵ / 48 * (17 / 20))) := by
    have e : 1 / 2 * (T * (ϵ / 48 * (17 / 20))) = 17 / 1920 * (T * ϵ) := by ring
    rw [e, hTϵ]
    nlinarith [Real.sqrt_nonneg (T:ℝ)]
  linarith

theorem theorem_2_core :
    ∃ C : ℝ, 0 < C ∧ ∀ (n K T : ℕ), 2 ≤ n → 1 ≤ K → K ≤ n → n ≤ T →
      ∃ (m : ℕ) (w : Fin m → ℝ) (inst : Fin m → Instance n),
        (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧ (∀ j, (inst j).Valid) ∧
        (∀ j k, (inst j).v₀ = (inst k).v₀ ∧ (inst j).r = (inst k).r) ∧
        ∀ π : BPolicy n, IsCardinalityK K π →
          C * Real.sqrt ((n : ℝ) * T / K) ≤ ∑ j, w j * regret (inst j) K π T := by
  refine ⟨1 / 2000, by norm_num, ?_⟩
  intro n K T hn hK _ hnT
  by_cases h : 2 * K ≤ n
  · exact g57_caseA n K T hK h hnT
  · exact g57_caseB n K T hn hK (by omega) hnT

end MNLBandit.LowerBound

open MNLBandit.LowerBound


theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (n K T : ℕ), 2 ≤ n → 1 ≤ K → K ≤ n → n ≤ T →
      ∃ (m : ℕ) (w : Fin m → ℝ) (inst : Fin m → Instance n),
        (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧ (∀ j, (inst j).Valid) ∧
        (∀ j k, (inst j).v₀ = (inst k).v₀ ∧ (inst j).r = (inst k).r) ∧
        ∀ π : BPolicy n, IsCardinalityK K π →
          C * Real.sqrt ((n : ℝ) * T / K) ≤ ∑ j, w j * regret (inst j) K π T := by
  exact theorem_2_core
