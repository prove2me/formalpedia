-- Prove2me | solution 1 for KellyReversibility.MarkovFields.general_spatial_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T07:29:44.758464+00:00
-- url     : https://prove2.me/submissions/b94ed516-9eb4-4221-80a5-7372e085b03e

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_MarkovFields_GeneralSpatialProcess

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GSE88

open KellyReversibility.MarkovFields

variable {V : Type*} [Fintype V] [DecidableEq V]
    {N : V → Type*} [∀ j, Fintype (N j)] [∀ j, DecidableEq (N j)]

lemma slice_sum (n : (j : V) → N j) (j : V) (h : ((k : V) → N k) → ℝ) :
    ∑ n' : (k : V) → N k, (if n' ≠ n ∧ ∀ k, k ≠ j → n' k = n k then h n' else 0)
      = ∑ m : N j, (if m = n j then 0 else h (Function.update n j m)) := by
  have hsub : ∑ n' ∈ (Finset.univ.image (Function.update n j)),
      (if n' ≠ n ∧ ∀ k, k ≠ j → n' k = n k then h n' else 0)
      = ∑ n' : (k : V) → N k, (if n' ≠ n ∧ ∀ k, k ≠ j → n' k = n k then h n' else 0) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    rw [if_neg]
    rintro ⟨-, hc⟩
    apply hx
    refine Finset.mem_image.2 ⟨x j, Finset.mem_univ _, ?_⟩
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · rw [Function.update_of_ne hk]; exact (hc k hk).symm
  rw [← hsub, Finset.sum_image (fun a _ b _ hab => Function.update_injective n j hab)]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : m = n j
  · subst hm; simp
  · rw [if_neg hm, if_pos]
    refine ⟨fun he => hm ?_, fun k hk => Function.update_of_ne hk _ _⟩
    simpa using congrFun he j

lemma rate_update (lam : (j : V) → N j → N j → ℝ) (Φ : ((j : V) → N j) → ℝ)
    (Φm : (j : V) → ((k : {k : V // k ≠ j}) → N k) → ℝ) (n : (j : V) → N j) (j : V) (m : N j) :
    generalSpatialRates lam Φ Φm n (Function.update n j m) =
      if m = n j then 0 else lam j (n j) m * Φ n / Φm j (fun k => n k.1) := by
  unfold generalSpatialRates
  by_cases hm : m = n j
  · subst hm; simp
  · rw [if_neg hm, Finset.sum_eq_single j]
    · have hc : Function.update n j m ≠ n ∧ ∀ k, k ≠ j → Function.update n j m k = n k :=
        ⟨fun he => hm (by simpa using congrFun he j), fun k hk => Function.update_of_ne hk _ _⟩
      rw [if_pos hc, Function.update_self]
    · intro i _ hi
      rw [if_neg]
      rintro ⟨-, hc⟩
      exact hm (by simpa using hc j (Ne.symm hi))
    · simp

lemma rate_update_rev (lam : (j : V) → N j → N j → ℝ) (Φ : ((j : V) → N j) → ℝ)
    (Φm : (j : V) → ((k : {k : V // k ≠ j}) → N k) → ℝ) (n : (j : V) → N j) (j : V) (m : N j) :
    generalSpatialRates lam Φ Φm (Function.update n j m) n =
      if m = n j then 0 else lam j m (n j) * Φ (Function.update n j m) / Φm j (fun k => n k.1) := by
  have h := rate_update lam Φ Φm (Function.update n j m) j (n j)
  rw [Function.update_idem, Function.update_eq_self, Function.update_self] at h
  have hres : (fun k : {k : V // k ≠ j} => Function.update n j m k.1) = fun k : {k : V // k ≠ j} => n k.1 := by
    funext k; exact Function.update_of_ne k.2 _ _
  rw [h, hres]
  by_cases hm : m = n j
  · simp [hm]
  · rw [if_neg (Ne.symm hm), if_neg hm]

lemma prod_update (α : (j : V) → N j → ℝ) (n : (j : V) → N j) (j : V) (m : N j) :
    (∏ i, α i (Function.update n j m i)) * α j (n j) = (∏ i, α i (n i)) * α j m := by
  rw [Fintype.prod_eq_mul_prod_compl j, Fintype.prod_eq_mul_prod_compl j (fun i => α i (n i)),
    Function.update_self]
  have : ∏ i ∈ ({j}ᶜ : Finset V), α i (Function.update n j m i)
      = ∏ i ∈ ({j}ᶜ : Finset V), α i (n i) :=
    Finset.prod_congr rfl fun i hi => by
      have hij : i ≠ j := by simpa using hi
      rw [Function.update_of_ne hij]
  rw [this]; ring

lemma q_nonneg (lam : (j : V) → N j → N j → ℝ) (Φ : ((j : V) → N j) → ℝ)
    (Φm : (j : V) → ((k : {k : V // k ≠ j}) → N k) → ℝ)
    (hlam : ∀ j a m, 0 ≤ lam j a m) (hΦ : ∀ n, 0 < Φ n) (hΦm : ∀ j x, 0 < Φm j x)
    (a b : (j : V) → N j) : 0 ≤ generalSpatialRates lam Φ Φm a b := by
  unfold generalSpatialRates
  refine Finset.sum_nonneg fun j _ => ?_
  split_ifs
  · exact div_nonneg (mul_nonneg (hlam _ _ _) (hΦ _).le) (hΦm _ _).le
  · exact le_rfl

lemma weight_pos (α : (j : V) → N j → ℝ) (Φ : ((j : V) → N j) → ℝ)
    (hΦ : ∀ n, 0 < Φ n) (hα : ∀ j a, 0 < α j a) (x : (j : V) → N j) :
    0 < generalSpatialWeight α Φ x :=
  div_pos (Finset.prod_pos fun i _ => hα i (x i)) (hΦ x)

lemma pi_pos [∀ j, Nonempty (N j)] (α : (j : V) → N j → ℝ) (Φ : ((j : V) → N j) → ℝ)
    (hΦ : ∀ n, 0 < Φ n) (hα : ∀ j a, 0 < α j a) (x : (j : V) → N j) :
    0 < generalSpatialPi α Φ x :=
  mul_pos (inv_pos.2 (Finset.sum_pos (fun y _ => weight_pos α Φ hΦ hα y) Finset.univ_nonempty))
    (weight_pos α Φ hΦ hα x)

lemma pi_sum [∀ j, Nonempty (N j)] (α : (j : V) → N j → ℝ) (Φ : ((j : V) → N j) → ℝ)
    (hΦ : ∀ n, 0 < Φ n) (hα : ∀ j a, 0 < α j a) :
    ∑ x, generalSpatialPi α Φ x = 1 := by
  unfold generalSpatialPi
  rw [← Finset.mul_sum]
  exact inv_mul_cancel₀ (ne_of_gt
    (Finset.sum_pos (fun y _ => weight_pos α Φ hΦ hα y) Finset.univ_nonempty))

lemma out_rate (lam : (j : V) → N j → N j → ℝ) (Φ : ((j : V) → N j) → ℝ)
    (Φm : (j : V) → ((k : {k : V // k ≠ j}) → N k) → ℝ) (n : (j : V) → N j) :
    ∑ n', generalSpatialRates lam Φ Φm n n'
      = ∑ j, ∑ m : N j, generalSpatialRates lam Φ Φm n (Function.update n j m) := by
  have e : ∀ n', generalSpatialRates lam Φ Φm n n' = ∑ j, (if n' ≠ n ∧ ∀ k, k ≠ j → n' k = n k then
      lam j (n j) (n' j) * Φ n / Φm j (fun k => n k.1) else 0) := fun n' => rfl
  rw [Finset.sum_congr rfl fun n' _ => e n', Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (slice_sum n j (fun n' => lam j (n j) (n' j) * Φ n / Φm j (fun k => n k.1))).trans ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [rate_update]
  simp only [Function.update_self]

lemma in_flow (lam : (j : V) → N j → N j → ℝ) (Φ : ((j : V) → N j) → ℝ)
    (Φm : (j : V) → ((k : {k : V // k ≠ j}) → N k) → ℝ) (π : ((j : V) → N j) → ℝ)
    (n : (j : V) → N j) :
    ∑ n', π n' * generalSpatialRates lam Φ Φm n' n
      = ∑ j, ∑ m : N j, π (Function.update n j m) *
          generalSpatialRates lam Φ Φm (Function.update n j m) n := by
  have e : ∀ n', π n' * generalSpatialRates lam Φ Φm n' n = ∑ j, (if n' ≠ n ∧ ∀ k, k ≠ j → n' k = n k
      then π n' * (lam j (n' j) (n j) * Φ n' / Φm j (fun k => n' k.1)) else 0) := by
    intro n'
    unfold generalSpatialRates
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_ite, mul_zero]
    exact if_congr ⟨fun ⟨a, b⟩ => ⟨Ne.symm a, fun k hk => (b k hk).symm⟩,
      fun ⟨a, b⟩ => ⟨Ne.symm a, fun k hk => (b k hk).symm⟩⟩ rfl rfl
  rw [Finset.sum_congr rfl fun n' _ => e n', Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (slice_sum n j (fun n' => π n' * (lam j (n' j) (n j) * Φ n' / Φm j (fun k => n' k.1)))).trans ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [rate_update_rev]
  have hres : (fun k : {k : V // k ≠ j} => Function.update n j m k.1) = fun k : {k : V // k ≠ j} => n k.1 := by
    funext k; exact Function.update_of_ne k.2 _ _
  by_cases hm : m = n j
  · simp [hm]
  · rw [if_neg hm, if_neg hm]
    rw [Function.update_self, hres]

lemma partial_balance (lam : (j : V) → N j → N j → ℝ) (Φ : ((j : V) → N j) → ℝ)
    (Φm : (j : V) → ((k : {k : V // k ≠ j}) → N k) → ℝ) (α : (j : V) → N j → ℝ)
    (hΦ : ∀ n, 0 < Φ n) (hΦm : ∀ j x, 0 < Φm j x) (hα : ∀ j a, 0 < α j a)
    (h916 : ∀ (j : V) (a : N j), α j a * ∑ m : N j, lam j a m = ∑ m : N j, α j m * lam j m a)
    (j : V) (n : (k : V) → N k) :
    generalSpatialPi α Φ n * ∑ m : N j, generalSpatialRates lam Φ Φm n (Function.update n j m) =
      ∑ m : N j, generalSpatialPi α Φ (Function.update n j m) *
        generalSpatialRates lam Φ Φm (Function.update n j m) n := by
  have hπ : ∀ x, generalSpatialPi α Φ x =
      (∑ n', generalSpatialWeight α Φ n')⁻¹ * ((∏ i, α i (x i)) / Φ x) := fun x => rfl
  generalize (∑ n', generalSpatialWeight α Φ n')⁻¹ = B at hπ
  have hΦn : Φ n ≠ 0 := (hΦ n).ne'
  have hΨ0 : Φm j (fun k => n k.1) ≠ 0 := (hΦm _ _).ne'
  have ha0 : α j (n j) ≠ 0 := (hα _ _).ne'
  have hL : ∀ m : N j, generalSpatialPi α Φ n * generalSpatialRates lam Φ Φm n (Function.update n j m)
      = (B * (∏ i, α i (n i)) / Φm j (fun k => n k.1)) *
          (if m = n j then 0 else lam j (n j) m) := by
    intro m
    rw [rate_update, hπ]
    split_ifs
    · simp
    · field_simp
  have hR : ∀ m : N j, generalSpatialPi α Φ (Function.update n j m) *
        generalSpatialRates lam Φ Φm (Function.update n j m) n
      = (B * (∏ i, α i (n i)) / Φm j (fun k => n k.1) / α j (n j)) *
          (if m = n j then 0 else α j m * lam j m (n j)) := by
    intro m
    rw [rate_update_rev, hπ]
    split_ifs
    · simp
    · have h4 := prod_update α n j m
      have hΦu : Φ (Function.update n j m) ≠ 0 := (hΦ _).ne'
      have hPu : ∏ i, α i (Function.update n j m i) = (∏ i, α i (n i)) * α j m / α j (n j) := by
        rw [eq_div_iff ha0, h4]
      rw [hPu]
      field_simp
  rw [Finset.sum_congr rfl fun m _ => hR m, Finset.mul_sum, Finset.sum_congr rfl fun m _ => hL m,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have key : α j (n j) * ∑ m : N j, (if m = n j then 0 else lam j (n j) m)
      = ∑ m : N j, (if m = n j then 0 else α j m * lam j m (n j)) := by
    have h := h916 j (n j)
    rw [Fintype.sum_eq_add_sum_compl (n j)] at h ⊢
    rw [Fintype.sum_eq_add_sum_compl (n j)] at h ⊢
    rw [if_pos rfl, if_pos rfl]
    rw [Finset.sum_congr rfl (fun m (hm : m ∈ ({n j}ᶜ : Finset (N j))) =>
          if_neg (show m ≠ n j by simpa using hm)),
        Finset.sum_congr rfl (fun m (hm : m ∈ ({n j}ᶜ : Finset (N j))) =>
          if_neg (show m ≠ n j by simpa using hm))]
    linear_combination h
  rw [← key, ← mul_assoc, div_mul_cancel₀ _ ha0]

lemma full_balance (lam : (j : V) → N j → N j → ℝ) (Φ : ((j : V) → N j) → ℝ)
    (Φm : (j : V) → ((k : {k : V // k ≠ j}) → N k) → ℝ) (α : (j : V) → N j → ℝ)
    (hΦ : ∀ n, 0 < Φ n) (hΦm : ∀ j x, 0 < Φm j x) (hα : ∀ j a, 0 < α j a)
    (h916 : ∀ (j : V) (a : N j), α j a * ∑ m : N j, lam j a m = ∑ m : N j, α j m * lam j m a)
    (n : (k : V) → N k) :
    generalSpatialPi α Φ n * ∑ n', generalSpatialRates lam Φ Φm n n' =
      ∑ n', generalSpatialPi α Φ n' * generalSpatialRates lam Φ Φm n' n := by
  rw [out_rate, in_flow, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => partial_balance lam Φ Φm α hΦ hΦm hα h916 j n

lemma unique_of_irr {S : Type*} [Fintype S] [Nonempty S] (q : S → S → ℝ)
    (hq : ∀ a b, 0 ≤ q a b)
    (hirr : ∀ a b, Relation.ReflTransGen (fun a b => 0 < q a b) a b)
    (p π : S → ℝ) (hπ : ∀ n, 0 < π n) (hps : ∑ n, p n = 1) (hπs : ∑ n, π n = 1)
    (hpb : ∀ n, p n * ∑ n', q n n' = ∑ n', p n' * q n' n)
    (hπb : ∀ n, π n * ∑ n', q n n' = ∑ n', π n' * q n' n) : p = π := by
  obtain ⟨n0, hn0⟩ := Finite.exists_max (fun n => p n / π n)
  set c := p n0 / π n0 with hc
  have hle : ∀ n, p n ≤ c * π n := fun n => (div_le_iff₀ (hπ n)).1 (hn0 n)
  have closure : ∀ a b, 0 < q b a → p a = c * π a → p b = c * π b := by
    intro a b hba ha
    have hsum : ∑ n', (c * π n' - p n') * q n' a = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
      rw [← hπb, ← hpb, ha]; ring
    have hnn : ∀ n' ∈ (Finset.univ : Finset S), 0 ≤ (c * π n' - p n') * q n' a :=
      fun n' _ => mul_nonneg (sub_nonneg.2 (hle n')) (hq _ _)
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum b (Finset.mem_univ _)
    rcases mul_eq_zero.1 h0 with h | h
    · linarith
    · exact absurd h (ne_of_gt hba)
  have hall : ∀ a, p a = c * π a := by
    intro a
    have h := hirr a n0
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact (div_mul_cancel₀ _ (hπ n0).ne').symm
    | head hab _ ih => exact closure _ _ hab ih
  have hc1 : c = 1 := by
    have h : ∑ n, p n = c * ∑ n, π n := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => hall n
    rw [hps, hπs, mul_one] at h; exact h.symm
  funext n; rw [hall n, hc1, one_mul]

end GSE88

open KellyReversibility.MarkovFields in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {N : V → Type*} [∀ j, Fintype (N j)] [∀ j, Nonempty (N j)] [∀ j, DecidableEq (N j)]
    (lam : (j : V) → N j → N j → ℝ) (Φ : ((j : V) → N j) → ℝ)
    (Φm : (j : V) → ((k : {k : V // k ≠ j}) → N k) → ℝ) (α : (j : V) → N j → ℝ)
    (hlam : ∀ j a m, 0 ≤ lam j a m) (hΦ : ∀ n, 0 < Φ n) (hΦm : ∀ j x, 0 < Φm j x)
    (hα : ∀ j a, 0 < α j a)
    (h916 : ∀ (j : V) (a : N j), α j a * ∑ m : N j, lam j a m = ∑ m : N j, α j m * lam j m a)
    (hirr : ∀ n n' : (k : V) → N k, Relation.ReflTransGen
      (fun a b => 0 < generalSpatialRates lam Φ Φm a b) n n') :
    let q := generalSpatialRates lam Φ Φm
    let π := generalSpatialPi α Φ
    (∀ n, 0 < π n) ∧ (∑ n, π n = 1) ∧
    (∀ (j : V) (n : (k : V) → N k),
      π n * ∑ m : N j, q n (Function.update n j m) =
        ∑ m : N j, π (Function.update n j m) * q (Function.update n j m) n) ∧
    KellyStochasticNetworks.FullBalance π q ∧
    (∀ p : ((j : V) → N j) → ℝ, (∀ n, 0 < p n) → ∑ n, p n = 1 →
      KellyStochasticNetworks.FullBalance p q → p = π) := by
  intro q π
  have hfb : ∀ n, π n * ∑ n', q n n' = ∑ n', π n' * q n' n :=
    GSE88.full_balance lam Φ Φm α hΦ hΦm hα h916
  refine ⟨GSE88.pi_pos α Φ hΦ hα, GSE88.pi_sum α Φ hΦ hα,
    GSE88.partial_balance lam Φ Φm α hΦ hΦm hα h916, ?_, ?_⟩
  · intro n
    simp only [tsum_fintype]
    exact hfb n
  · intro p _ hs hb
    refine GSE88.unique_of_irr q (GSE88.q_nonneg lam Φ Φm hlam hΦ hΦm) hirr p π
      (GSE88.pi_pos α Φ hΦ hα) hs (GSE88.pi_sum α Φ hΦ hα) ?_ hfb
    intro n
    have h := hb n
    simp only [tsum_fintype] at h
    exact h
