-- Prove2me | solution 1 for JohnsonApprox.SetCover.fig1_run
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T18:36:25.683998+00:00
-- url     : https://prove2.me/submissions/b699bca1-b7ab-4594-9895-ca8973dc6cfb

import Mathlib
import Definitions.Def_JohnsonApprox_SetCover_Problem
import Definitions.Def_JohnsonApprox_SetCover_C1
import Definitions.Def_JohnsonApprox_SetCover_Fig1



namespace JohnsonApprox.SetCover

open Finset

section general
variable {ι α : Type} [Fintype ι] [DecidableEq α] [DecidableEq ι]

/-- State after choosing the indices in `D`. -/
def stD (S : ι → Finset α) (D : Finset ι) : State ι α :=
  ⟨D.image S, ground S \ D.biUnion S, fun i => S i \ D.biUnion S⟩

lemma init_eq_stD (S : ι → Finset α) : init S = stD S ∅ := by
  unfold init stD; simp

lemma step_stD (S : ι → Finset α) (D : Finset ι) (j : ι)
    (hne : ¬ Halts (stD S D))
    (hmax : ∀ i, (S i \ D.biUnion S).card ≤ (S j \ D.biUnion S).card) :
    Step S (stD S D) (stD S (insert j D)) := by
  refine ⟨j, hne, hmax, ?_⟩
  unfold stD
  simp only [image_insert, biUnion_insert, State.mk.injEq, true_and]
  constructor
  · ext x; simp only [mem_sdiff, mem_union]; tauto
  · funext i; ext x; simp only [mem_sdiff, mem_union]; tauto

end general

variable (k : ℕ)

lemma fact_dvd (t : Fin k) : (t.val + 1) ∣ k.factorial := Nat.dvd_factorial (by omega) t.2

lemma blk_lt (t : Fin k) (q : Fin k.factorial) :
    q.val / (t.val + 1) < k.factorial / (t.val + 1) := by
  obtain ⟨m, hm⟩ := fact_dvd k t
  have hq : q.val < k.factorial := q.2
  rw [show k.factorial / (t.val + 1) = m by rw [hm]; exact Nat.mul_div_cancel_left _ (by omega),
    Nat.div_lt_iff_lt_mul (by omega)]
  calc (q : ℕ) < k.factorial := hq
    _ = _ := by rw [hm, mul_comm]

def inD (u c : ℕ) : Fig1Index k → Bool
  | .inl _ => false
  | .inr p => decide (u ≤ p.1.val ∨ (p.1.val + 1 = u ∧ p.2.val < c))

def D (u c : ℕ) : Finset (Fig1Index k) := univ.filter (fun i => inD k u c i = true)

@[simp] lemma mem_D_inl (u c : ℕ) (q : Fin k.factorial) : Sum.inl q ∉ D k u c := by
  simp [D, inD]

@[simp] lemma mem_D_inr (u c : ℕ) (p : Σ s : Fin k, Fin (k.factorial / (s.val + 1))) :
    Sum.inr p ∈ D k u c ↔ (u ≤ p.1.val ∨ (p.1.val + 1 = u ∧ p.2.val < c)) := by
  simp [D, inD]

lemma mem_U (u c : ℕ) (x : Fig1Point k) :
    x ∈ (D k u c).biUnion (fig1 k) ↔
      (u ≤ x.1.val ∨ (x.1.val + 1 = u ∧ x.2.val / (x.1.val + 1) < c)) := by
  simp only [mem_biUnion]
  constructor
  · rintro ⟨i, hi, hx⟩
    rcases i with q | ⟨t, b⟩
    · simp at hi
    · simp only [mem_D_inr] at hi
      simp only [fig1, mem_filter, mem_univ, true_and] at hx
      obtain ⟨rfl, hb⟩ := hx
      rw [hb]; exact hi
  · intro h
    refine ⟨.inr ⟨x.1, ⟨x.2.val / (x.1.val + 1), blk_lt k x.1 x.2⟩⟩, ?_, ?_⟩
    · simp only [mem_D_inr]; exact h
    · simp [fig1]

lemma D_top : D k k 0 = ∅ := by
  ext i; rcases i with q | ⟨t, b⟩ <;> simp

lemma D_bot : (D k 0 0).image (fig1 k) = fig1F₁ k := by
  ext A; simp only [mem_image, mem_univ, true_and, fig1F₁]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases i with q | p
    · simp at hi
    · exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩; exact ⟨.inr p, by simp, rfl⟩

lemma D_next (u : ℕ) (hu : 1 ≤ u) : D k u (k.factorial / u) = D k (u - 1) 0 := by
  ext i; rcases i with q | ⟨t, b⟩
  · simp
  · simp only [mem_D_inr]
    have hb := b.2
    constructor
    · rintro (h | ⟨h1, _⟩) <;> omega
    · intro h
      rcases h with h | h
      · rcases Nat.lt_or_ge t.val u with h' | h'
        · right; refine ⟨by omega, ?_⟩
          have : t.val + 1 = u := by omega
          rw [← this]; exact hb
        · left; exact h'
      · omega

lemma D_succ (u c : ℕ) (hu : 1 ≤ u) (huk : u ≤ k) (hc : c < k.factorial / u) :
    insert (Sum.inr ⟨⟨u - 1, by omega⟩, ⟨c, by rw [show u - 1 + 1 = u by omega]; exact hc⟩⟩)
      (D k u c) = D k u (c + 1) := by
  ext i; rcases i with q | ⟨t, b⟩
  · simp
  · simp only [mem_insert, mem_D_inr]
    constructor
    · rintro (h | h)
      · simp only [Sum.inr.injEq, Sigma.mk.inj_iff] at h
        obtain ⟨rfl, h2⟩ := h
        have := (Fin.heq_ext_iff (by simp)).1 h2
        simp at this; right; exact ⟨by simp only [Fin.val_mk]; omega, by omega⟩
      · omega
    · rintro (h | ⟨h1, h2⟩)
      · right; left; exact h
      · rcases Nat.lt_or_ge b.val c with h3 | h3
        · right; right; exact ⟨h1, h3⟩
        · left
          rw [Sum.inr.injEq]
          exact Sigma.ext (Fin.ext (by simp only [Fin.val_mk]; omega))
            ((Fin.heq_ext_iff (by simp only [Fin.val_mk]; rw [show u - 1 + 1 = t.val + 1 by omega])).2
              (by simp only [Fin.val_mk]; omega))


lemma cu_lt (u c : ℕ) (hc : c < k.factorial / u) (r : ℕ) (hr : r < u) :
    c * u + r < k.factorial := by
  have h1 : (c + 1) * u ≤ k.factorial / u * u := Nat.mul_le_mul_right _ hc
  have h2 := Nat.div_mul_le_self k.factorial u
  nlinarith

lemma cu_div (u c r : ℕ) (hr : r < u) : (c * u + r) / u = c := by
  rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, add_zero]

lemma ground_fig1 : ground (fig1 k) = univ := by
  ext x; simp only [ground, mem_biUnion, mem_univ, true_and, iff_true]
  exact ⟨.inl x.2, by simp [fig1]⟩

lemma inl_card_le (q : Fin k.factorial) : (fig1 k (.inl q)).card ≤ k := by
  have := card_le_card_of_injOn (fun x : Fig1Point k => x.1.val) (s := fig1 k (.inl q))
    (t := range k) (fun x _ => by simp) (by
      intro x hx y hy hxy
      simp only [fig1, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx hy
      exact Prod.ext (Fin.ext hxy) (hx.trans hy.symm))
  simpa using this

lemma inr_card_le (t : Fin k) (b : Fin (k.factorial / (t.val + 1))) :
    (fig1 k (.inr ⟨t, b⟩)).card ≤ t.val + 1 := by
  have := card_le_card_of_injOn (fun x : Fig1Point k => x.2.val) (s := fig1 k (.inr ⟨t, b⟩))
    (t := Ico (b.val * (t.val + 1)) (b.val * (t.val + 1) + (t.val + 1))) (by
      intro x hx
      simp only [fig1, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx
      simp only [coe_Ico, Set.mem_Ico]
      rw [← hx.2]
      exact ⟨Nat.div_mul_le_self _ _, Nat.lt_div_mul_add (by omega)⟩) (by
      intro x hx y hy hxy
      simp only [fig1, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx hy
      exact Prod.ext (hx.1.trans hy.1.symm) (Fin.ext hxy))
  simpa using this

lemma inSC_fig1 : InSC k (fig1 k) := by
  intro i; rcases i with q | ⟨t, b⟩
  · exact inl_card_le k q
  · exact (inr_card_le k t b).trans (by omega)

lemma other_card (u c : ℕ) (i : Fig1Index k) :
    (fig1 k i \ (D k u c).biUnion (fig1 k)).card ≤ u := by
  rcases i with q | ⟨t, b⟩
  · have := card_le_card_of_injOn (fun x : Fig1Point k => x.1.val)
      (s := fig1 k (.inl q) \ (D k u c).biUnion (fig1 k)) (t := range u) (by
        intro x hx
        simp only [coe_sdiff, Set.mem_diff, mem_coe, mem_U] at hx
        simp only [coe_range, Set.mem_Iio]; omega) (by
        intro x hx y hy hxy
        simp only [coe_sdiff, Set.mem_diff, mem_coe, fig1, mem_filter, mem_univ, true_and] at hx hy
        exact Prod.ext (Fin.ext hxy) (hx.1.trans hy.1.symm))
    simpa using this
  · rcases Nat.lt_or_ge t.val u with h | h
    · exact (card_le_card sdiff_subset).trans ((inr_card_le k t b).trans (by omega))
    · have : fig1 k (.inr ⟨t, b⟩) \ (D k u c).biUnion (fig1 k) = ∅ := by
        rw [sdiff_eq_empty_iff_subset]; intro x hx
        simp only [fig1, mem_filter, mem_univ, true_and] at hx
        rw [mem_U]; left; rw [hx.1]; exact h
      rw [this]; simp

/-- the index chosen in state `(u, c)` -/
def jdx (u c : ℕ) (hu : 1 ≤ u) (huk : u ≤ k) (hc : c < k.factorial / u) : Fig1Index k :=
  Sum.inr ⟨⟨u - 1, by omega⟩, ⟨c, by rw [show u - 1 + 1 = u by omega]; exact hc⟩⟩

lemma j_card (u c : ℕ) (hu : 1 ≤ u) (huk : u ≤ k) (hc : c < k.factorial / u) :
    u ≤ (fig1 k (jdx k u c hu huk hc) \ (D k u c).biUnion (fig1 k)).card := by
  have hfp := Nat.factorial_pos k
  let f : ℕ → Fig1Point k := fun r =>
    (⟨u - 1, by omega⟩, ⟨(c * u + r) % k.factorial, Nat.mod_lt _ hfp⟩)
  have := card_le_card_of_injOn f (s := range u)
    (t := fig1 k (jdx k u c hu huk hc) \ (D k u c).biUnion (fig1 k)) (by
      intro r hr
      simp only [coe_range, Set.mem_Iio] at hr
      have hm : (c * u + r) % k.factorial = c * u + r := Nat.mod_eq_of_lt (cu_lt k u c hc r hr)
      simp only [coe_sdiff, Set.mem_diff, mem_coe, mem_U, jdx, fig1, mem_filter, mem_univ,
        true_and, f, hm, Fin.val_mk, show u - 1 + 1 = u by omega, cu_div u c r hr]
      omega) (by
      intro r1 hr1 r2 hr2 h
      simp only [coe_range, Set.mem_Iio] at hr1 hr2
      simp only [f, Prod.mk.injEq, Fin.mk.injEq, true_and] at h
      rw [Nat.mod_eq_of_lt (cu_lt k u c hc r1 hr1), Nat.mod_eq_of_lt (cu_lt k u c hc r2 hr2)] at h
      omega)
  simpa using this

lemma reach_c (u : ℕ) (hu : 1 ≤ u) (huk : u ≤ k) :
    ∀ c ≤ k.factorial / u, Relation.ReflTransGen (Step (fig1 k))
      (stD (fig1 k) (D k u 0)) (stD (fig1 k) (D k u c)) := by
  intro c
  induction c with
  | zero => intro _; exact Relation.ReflTransGen.refl
  | succ c ih =>
    intro hc
    have hc' : c < k.factorial / u := by omega
    refine (ih (by omega)).tail ?_
    rw [← D_succ k u c hu huk hc']
    have hj := j_card k u c hu huk hc'
    apply step_stD
    · intro hh
      unfold Halts stD at hh
      simp only at hh
      obtain ⟨x, hx⟩ := card_pos.1 (by omega : 0 < (fig1 k (jdx k u c hu huk hc') \
        (D k u c).biUnion (fig1 k)).card)
      rw [mem_sdiff] at hx
      have : x ∈ ground (fig1 k) \ (D k u c).biUnion (fig1 k) := by
        rw [ground_fig1]; exact mem_sdiff.2 ⟨mem_univ _, hx.2⟩
      rw [hh] at this; simp at this
    · intro i; exact (other_card k u c i).trans hj

lemma reach_all : ∀ m ≤ k, Relation.ReflTransGen (Step (fig1 k)) (init (fig1 k))
    (stD (fig1 k) (D k (k - m) 0)) := by
  intro m
  induction m with
  | zero => intro _; rw [Nat.sub_zero, D_top, init_eq_stD]
  | succ m ih =>
    intro hm
    have h1 := reach_c k (k - m) (by omega) (by omega) _ le_rfl
    rw [D_next k (k - m) (by omega), show k - m - 1 = k - (m + 1) by omega] at h1
    exact (ih (by omega)).trans h1

lemma choosable_fig1 : Choosable (fig1 k) (fig1F₁ k) := by
  refine ⟨_, by simpa using reach_all k k le_rfl, ?_, D_bot k⟩
  unfold Halts stD; simp only
  rw [sdiff_eq_empty_iff_subset]; intro x _; rw [mem_U]; left; exact Nat.zero_le _

lemma F0_mem : fig1F₀ k ∈ subcovers (fig1 k) := by
  unfold subcovers; rw [mem_filter, mem_powerset]
  refine ⟨fun A hA => ?_, ?_⟩
  · unfold fig1F₀ at hA; obtain ⟨q, _, rfl⟩ := mem_image.1 hA
    unfold family; exact mem_image.2 ⟨.inl q, mem_univ _, rfl⟩
  · rw [ground_fig1]; ext x; simp only [mem_biUnion, mem_univ, iff_true, id]
    exact ⟨_, mem_image.2 ⟨x.2, mem_univ _, rfl⟩, by simp [fig1]⟩

lemma opt_fig1 (hk : 1 ≤ k) : opt (fig1 k) = k.factorial := by
  apply le_antisymm
  · refine (inf'_le _ (F0_mem k)).trans ?_
    unfold fig1F₀; exact card_image_le.trans (by simp)
  · apply le_inf'
    intro F' hF'
    unfold subcovers at hF'; rw [mem_filter, mem_powerset, ground_fig1] at hF'
    obtain ⟨hsub, hcov⟩ := hF'
    have h1 : (univ : Finset (Fig1Point k)).card ≤ ∑ A ∈ F', A.card := by
      rw [← hcov]; exact card_biUnion_le
    have h2 : ∑ A ∈ F', A.card ≤ F'.card * k := by
      rw [← smul_eq_mul, ← sum_const]
      apply sum_le_sum; intro A hA
      have := hsub hA; unfold family at this; obtain ⟨i, _, rfl⟩ := mem_image.1 this
      exact inSC_fig1 k i
    simp only [card_univ, Fintype.card_prod, Fintype.card_fin] at h1
    have : k * k.factorial ≤ k * F'.card := by linarith [mul_comm F'.card k]
    exact Nat.le_of_mul_le_mul_left this (by omega)

lemma F1_card : ((fig1F₁ k).card : ℚ) = k.factorial * harmonic k := by
  have hinj : Function.Injective
      (fun i : (Σ s : Fin k, Fin (k.factorial / (s.val + 1))) => fig1 k (Sum.inr i)) := by
    rintro ⟨t, b⟩ ⟨t', b'⟩ h
    have hlt := cu_lt k (t.val + 1) b.val b.2 0 (by omega)
    have hp : ((t, ⟨b.val * (t.val + 1) + 0, hlt⟩) : Fig1Point k) ∈ fig1 k (.inr ⟨t, b⟩) := by
      simp only [fig1, mem_filter, mem_univ, true_and, Fin.val_mk]
      first | exact ⟨rfl, cu_div _ _ _ (by omega)⟩ | exact cu_div _ _ _ (by omega)
    simp only at h
    rw [h] at hp
    simp only [fig1, mem_filter, mem_univ, true_and, Fin.val_mk] at hp
    obtain ⟨rfl, hb⟩ := hp
    rw [cu_div _ _ _ (by omega)] at hb
    rw [Sigma.mk.inj_iff]; exact ⟨rfl, heq_of_eq (Fin.ext hb)⟩
  unfold fig1F₁
  rw [card_image_of_injective _ hinj, card_univ, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  push_cast
  rw [Fin.sum_univ_eq_sum_range (fun s => ((k.factorial / (s + 1) : ℕ) : ℚ)), harmonic, mul_sum]
  apply sum_congr rfl; intro s hs
  rw [mem_range] at hs
  rw [Nat.cast_div (Nat.dvd_factorial (by omega) hs) (by positivity)]
  push_cast; ring

theorem fig1_run (hk : 1 ≤ k) :
    InSC k (fig1 k) ∧ fig1F₀ k ∈ subcovers (fig1 k) ∧ opt (fig1 k) = k.factorial ∧
      Choosable (fig1 k) (fig1F₁ k) ∧
      ((fig1F₁ k).card : ℚ) = k.factorial * harmonic k :=
  ⟨inSC_fig1 k, F0_mem k, opt_fig1 k hk, choosable_fig1 k, F1_card k⟩

end JohnsonApprox.SetCover

open JohnsonApprox.SetCover

theorem solution (k : ℕ) (hk : 1 ≤ k) :
    InSC k (fig1 k) ∧ fig1F₀ k ∈ subcovers (fig1 k) ∧ opt (fig1 k) = k.factorial ∧
      Choosable (fig1 k) (fig1F₁ k) ∧
      ((fig1F₁ k).card : ℚ) = k.factorial * harmonic k := by
  exact JohnsonApprox.SetCover.fig1_run k hk
