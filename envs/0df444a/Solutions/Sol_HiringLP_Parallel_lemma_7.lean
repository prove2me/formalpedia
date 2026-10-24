-- Prove2me | solution 1 for HiringLP.Parallel.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T17:31:10.855527+00:00
-- url     : https://prove2.me/submissions/f6598a05-cab2-4398-aebf-1550c9f6d642

import Mathlib
import Definitions.Def_HiringLP_Parallel_Model

open HiringLP.Parallel Finset

namespace HLP2L7

variable {n : ℕ}

noncomputable def vmax (v : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  if h : S.Nonempty then S.sup' h v else 0

lemma vmax_empty (v : Fin n → ℝ) : vmax v ∅ = 0 := by simp [vmax]

lemma vmax_eq_of (v : Fin n → ℝ) (S : Finset (Fin n)) (a : Fin n) (ha : a ∈ S)
    (hmax : ∀ i ∈ S, v i ≤ v a) : vmax v S = v a := by
  unfold vmax
  rw [dif_pos ⟨a, ha⟩]
  exact le_antisymm (Finset.sup'_le _ _ hmax) (Finset.le_sup' v ha)

/-- Layer decomposition at the minimum `b` of `U`. -/
lemma vmax_split (v : Fin n → ℝ) (U : Finset (Fin n)) (b : Fin n) (hbU : b ∈ U)
    (hb : ∀ i ∈ U, v b ≤ v i) (S : Finset (Fin n)) :
    vmax v (S ∩ U) = v b * (if S ∩ U = ∅ then 0 else 1) +
      vmax (fun i => v i - v b) (S ∩ U.erase b) := by
  by_cases h1 : S ∩ U = ∅
  · have h2 : S ∩ U.erase b = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem] at h1 ⊢
      intro i hi; exact h1 i (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).1,
        Finset.mem_of_mem_erase (Finset.mem_inter.mp hi).2⟩)
    rw [h1, h2, vmax_empty, vmax_empty, if_pos rfl]; ring
  · rw [if_neg h1]
    by_cases h2 : (S ∩ U.erase b).Nonempty
    · obtain ⟨a, haS, hamax⟩ := Finset.exists_max_image _ v h2
      have haS' := Finset.mem_inter.mp haS
      rw [vmax_eq_of (fun i => v i - v b) _ a haS (fun i hi => by
          show v i - v b ≤ v a - v b; linarith [hamax i hi])]
      rw [vmax_eq_of v _ a (Finset.mem_inter.mpr ⟨haS'.1, Finset.mem_of_mem_erase haS'.2⟩)]
      · ring
      · intro i hi
        have hi' := Finset.mem_inter.mp hi
        by_cases hib : i = b
        · rw [hib]; exact hb a (Finset.mem_of_mem_erase haS'.2)
        · exact hamax i (Finset.mem_inter.mpr ⟨hi'.1, Finset.mem_erase.mpr ⟨hib, hi'.2⟩⟩)
    · have h2' : S ∩ U.erase b = ∅ := Finset.not_nonempty_iff_eq_empty.mp h2
      rw [h2', vmax_empty]
      obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr h1
      have hcb : ∀ i ∈ S ∩ U, i = b := by
        intro i hi
        by_contra hib
        have hi' := Finset.mem_inter.mp hi
        have : i ∈ S ∩ U.erase b :=
          Finset.mem_inter.mpr ⟨hi'.1, Finset.mem_erase.mpr ⟨hib, hi'.2⟩⟩
        rw [h2'] at this; simp at this
      have hbSU : b ∈ S ∩ U := by rw [← hcb c hc]; exact hc
      rw [vmax_eq_of v _ b hbSU (fun i hi => by rw [hcb i hi])]
      ring

/-- Comparison: if `D₁` avoids every set `T` with no larger probability than `D₂`, then
`E v*(D₁) ≥ E v*(D₂)` for nonnegative values. -/
lemma compare {Ω₁ Ω₂ : Type} [Fintype Ω₁] [Fintype Ω₂]
    (π₁ : Ω₁ → ℝ) (D₁ : Ω₁ → Finset (Fin n)) (π₂ : Ω₂ → ℝ) (D₂ : Ω₂ → Finset (Fin n))
    (hsum : ∑ ω, π₁ ω = ∑ ω, π₂ ω)
    (hT : ∀ T : Finset (Fin n), ∑ ω, π₁ ω * (if D₁ ω ∩ T = ∅ then 1 else 0) ≤
      ∑ ω, π₂ ω * (if D₂ ω ∩ T = ∅ then 1 else 0)) :
    ∀ (m : ℕ) (U : Finset (Fin n)), U.card = m → ∀ v : Fin n → ℝ, (∀ i ∈ U, 0 ≤ v i) →
      ∑ ω, π₂ ω * vmax v (D₂ ω ∩ U) ≤ ∑ ω, π₁ ω * vmax v (D₁ ω ∩ U) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro U hU v hv
  rcases U.eq_empty_or_nonempty with hU0 | hUne
  · subst hU0; simp [vmax_empty]
  obtain ⟨b, hbU, hbmin⟩ := Finset.exists_min_image U v hUne
  have hsplit : ∀ {Ω : Type} [Fintype Ω] (π : Ω → ℝ) (D : Ω → Finset (Fin n)),
      ∑ ω, π ω * vmax v (D ω ∩ U) = v b * (∑ ω, π ω - ∑ ω, π ω * (if D ω ∩ U = ∅ then 1 else 0))
        + ∑ ω, π ω * vmax (fun i => v i - v b) (D ω ∩ U.erase b) := by
    intro Ω _ π D
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    rw [vmax_split v U b hbU hbmin (D ω)]
    split_ifs <;> ring
  rw [hsplit π₁ D₁, hsplit π₂ D₂]
  have hcard : (U.erase b).card < m := by
    rw [← hU]; exact Finset.card_erase_lt_of_mem hbU
  have hih := ih _ hcard (U.erase b) rfl (fun i => v i - v b) (fun i hi => by
    show 0 ≤ v i - v b; linarith [hbmin i (Finset.mem_of_mem_erase hi)])
  have hvb : 0 ≤ v b := hv b hbU
  have := hT U
  have : v b * (∑ ω, π₂ ω - ∑ ω, π₂ ω * (if D₂ ω ∩ U = ∅ then 1 else 0)) ≤
      v b * (∑ ω, π₁ ω - ∑ ω, π₁ ω * (if D₁ ω ∩ U = ∅ then 1 else 0)) :=
    mul_le_mul_of_nonneg_left (by linarith) hvb
  linarith

/-! ### Independent side -/

def w (x : Fin n → ℝ) (U S : Finset (Fin n)) : ℝ :=
  ∏ i ∈ U, if i ∈ S then x i else 1 - x i

lemma w_insert_out (x : Fin n → ℝ) (a : Fin n) (U S : Finset (Fin n)) (ha : a ∉ U)
    (hS : S ⊆ U) : w x (insert a U) S = (1 - x a) * w x U S := by
  unfold w
  rw [Finset.prod_insert ha, if_neg (fun h => ha (hS h))]

lemma w_insert_in (x : Fin n → ℝ) (a : Fin n) (U S : Finset (Fin n)) (ha : a ∉ U) :
    w x (insert a U) (insert a S) = x a * w x U S := by
  unfold w
  rw [Finset.prod_insert ha, if_pos (Finset.mem_insert_self a S)]
  congr 1
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hne : i ≠ a := fun h => ha (h ▸ hi)
  simp [Finset.mem_insert, hne]

lemma sum_insert_split (a : Fin n) (U : Finset (Fin n)) (ha : a ∉ U)
    (g : Finset (Fin n) → ℝ) :
    ∑ S ∈ (insert a U).powerset, g S =
      ∑ S ∈ U.powerset, g S + ∑ S ∈ U.powerset, g (insert a S) := by
  rw [Finset.powerset_insert, Finset.sum_union]
  · rw [Finset.sum_image]
    intro S hS T hT h
    have hS' : a ∉ S := fun h' => ha (Finset.mem_powerset.mp hS h')
    have hT' : a ∉ T := fun h' => ha (Finset.mem_powerset.mp hT h')
    have := congrArg (fun Z => Z.erase a) h
    simpa [Finset.erase_insert hS', Finset.erase_insert hT'] using this
  · rw [Finset.disjoint_left]
    intro S hS hS2
    obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hS2
    exact ha (Finset.mem_powerset.mp hS (Finset.mem_insert_self a T))

lemma w_avoid (x : Fin n → ℝ) (T : Finset (Fin n)) (U : Finset (Fin n)) :
    ∑ S ∈ U.powerset, w x U S * (if S ∩ T = ∅ then 1 else 0) =
      ∏ i ∈ U, (if i ∈ T then 1 - x i else 1) := by
  induction U using Finset.induction_on with
  | empty => simp [w, Finset.filter_singleton]
  | insert a U ha ih =>
    rw [sum_insert_split a U ha, Finset.prod_insert ha, ← ih]
    have e1 : ∀ S ∈ U.powerset, w x (insert a U) S * (if S ∩ T = ∅ then (1:ℝ) else 0)
        = (1 - x a) * (w x U S * (if S ∩ T = ∅ then 1 else 0)) := by
      intro S hS; rw [w_insert_out x a U S ha (Finset.mem_powerset.mp hS)]; ring
    have e2 : ∀ S ∈ U.powerset,
        w x (insert a U) (insert a S) * (if insert a S ∩ T = ∅ then (1:ℝ) else 0)
        = (if a ∈ T then 0 else x a) * (w x U S * (if S ∩ T = ∅ then 1 else 0)) := by
      intro S _
      rw [w_insert_in x a U S ha]
      by_cases haT : a ∈ T
      · rw [if_pos haT]
        rw [if_neg (Finset.ne_empty_of_mem (Finset.mem_inter.mpr
          ⟨Finset.mem_insert_self a S, haT⟩))]
        ring
      · rw [if_neg haT]
        have : insert a S ∩ T = S ∩ T := by
          ext i; simp only [Finset.mem_inter, Finset.mem_insert]
          constructor
          · rintro ⟨h1 | h1, h2⟩
            · exact absurd (h1 ▸ h2) haT
            · exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
        rw [this]; ring
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.mul_sum, ← Finset.mul_sum]
    split_ifs <;> ring

lemma w_sum_one (x : Fin n → ℝ) (U : Finset (Fin n)) :
    ∑ S ∈ U.powerset, w x U S = 1 := by
  have := w_avoid x ∅ U
  simpa using this

/-! ### Dependent side -/

variable {k : ℕ}

/-- `D_j` for the rounded set `Y` and the acceptance profile `A`. -/
def Dset (j : Fin k) (Y : Finset (Fin n × Fin k)) (A : Fin n → Finset (Fin k)) :
    Finset (Fin n) :=
  univ.filter (fun i => (i, j) ∈ Y ∧ j ∈ A i)

lemma acc_factor (I : Instance n k) (acc : Fin n → Finset (Fin k) → ℝ) (hacc : AccLaw I acc)
    (j : Fin k) (Y : Finset (Fin n × Fin k)) (T : Finset (Fin n)) :
    ∑ A : Fin n → Finset (Fin k), accProb acc A * (if Dset j Y A ∩ T = ∅ then 1 else 0) =
      ∏ i, (if i ∈ T ∧ (i, j) ∈ Y then 1 - I.p i j else 1) := by
  have hind : ∀ A : Fin n → Finset (Fin k), (if Dset j Y A ∩ T = ∅ then (1:ℝ) else 0) =
      ∏ i, (if ¬ (i ∈ T ∧ (i, j) ∈ Y ∧ j ∈ A i) then 1 else 0) := by
    intro A
    rw [Fintype.prod_boole]
    congr 1
    apply propext
    rw [Finset.eq_empty_iff_forall_notMem]
    constructor
    · intro h i hi
      exact h i (Finset.mem_inter.mpr ⟨by simp [Dset, hi.2.1, hi.2.2], hi.1⟩)
    · intro h i hi
      have hi' := Finset.mem_inter.mp hi
      have : (i, j) ∈ Y ∧ j ∈ A i := by simpa [Dset] using hi'.1
      exact h i ⟨hi'.2, this.1, this.2⟩
  simp_rw [hind]
  unfold accProb
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i B => acc i B * (if ¬ (i ∈ T ∧ (i, j) ∈ Y ∧ j ∈ B) then 1 else 0))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  by_cases h : i ∈ T ∧ (i, j) ∈ Y
  · rw [if_pos h]
    have h1 := hacc.2.1 i
    have h2 := hacc.2.2 i j
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun A : Finset (Fin k) => j ∈ A)] at h1
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun A : Finset (Fin k) => j ∈ A)]
    have e1 : ∑ B ∈ univ.filter (fun B : Finset (Fin k) => j ∈ B),
        acc i B * (if ¬ (i ∈ T ∧ (i, j) ∈ Y ∧ j ∈ B) then (1:ℝ) else 0) = 0 := by
      refine Finset.sum_eq_zero (fun B hB => ?_)
      have : j ∈ B := (Finset.mem_filter.mp hB).2
      rw [if_neg (not_not.mpr ⟨h.1, h.2, this⟩)]; ring
    have e2 : ∑ B ∈ univ.filter (fun B : Finset (Fin k) => ¬ j ∈ B),
        acc i B * (if ¬ (i ∈ T ∧ (i, j) ∈ Y ∧ j ∈ B) then (1:ℝ) else 0) =
        ∑ B ∈ univ.filter (fun B : Finset (Fin k) => ¬ j ∈ B), acc i B := by
      refine Finset.sum_congr rfl (fun B hB => ?_)
      have : ¬ j ∈ B := (Finset.mem_filter.mp hB).2
      rw [if_pos (fun h' => this h'.2.2)]; ring
    rw [e1, e2]; linarith
  · rw [if_neg h]
    calc _ = ∑ B, acc i B := Finset.sum_congr rfl (fun B _ => by
            rw [if_pos (fun h' => h ⟨h'.1, h'.2.1⟩)]; ring)
      _ = 1 := hacc.2.1 i

lemma probAll_single_false (y : Fin n → Fin k → ℝ) (μ : Finset (Fin n × Fin k) → ℝ)
    (hμ : IsGKPS y μ) (i : Fin n) (j : Fin k) :
    probAll μ {(i, j)} false = 1 - y i j := by
  unfold probAll
  have h1 := hμ.sum_one
  have h2 := hμ.marginal i j
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun Y : Finset (Fin n × Fin k) => (i, j) ∈ Y)]
    at h1
  have : univ.filter (fun Y : Finset (Fin n × Fin k) =>
      ∀ e ∈ ({(i, j)} : Finset (Fin n × Fin k)), decide (e ∈ Y) = false) =
      univ.filter (fun Y : Finset (Fin n × Fin k) => ¬ (i, j) ∈ Y) := by
    ext Y; simp
  rw [this]; linarith

lemma dep_avoid (I : Instance n k) (hI : I.Valid) (acc : Fin n → Finset (Fin k) → ℝ)
    (hacc : AccLaw I acc) (y : Fin n → Fin k → ℝ) (hy : LPFeasible I y)
    (μ : Finset (Fin n × Fin k) → ℝ) (hμ : IsGKPS y μ) (j : Fin k) (T : Finset (Fin n)) :
    ∑ Y, μ Y * ∑ A : Fin n → Finset (Fin k), accProb acc A *
      (if Dset j Y A ∩ T = ∅ then 1 else 0) ≤ ∏ i ∈ T, (1 - y i j * I.p i j) := by
  simp_rw [acc_factor I acc hacc j]
  -- rewrite the product as a product over `T`
  have hprod : ∀ Y : Finset (Fin n × Fin k),
      ∏ i, (if i ∈ T ∧ (i, j) ∈ Y then 1 - I.p i j else 1) =
      ∑ R ∈ T.powerset, ((∏ i ∈ R, I.p i j) * ∏ i ∈ T \ R, (1 - I.p i j)) *
        (if ∀ i ∈ R, (i, j) ∉ Y then 1 else 0) := by
    intro Y
    have : ∏ i, (if i ∈ T ∧ (i, j) ∈ Y then 1 - I.p i j else 1) =
        ∏ i ∈ T, (I.p i j * (if (i, j) ∉ Y then 1 else 0) + (1 - I.p i j)) := by
      have e : ∀ i, (if i ∈ T ∧ (i, j) ∈ Y then 1 - I.p i j else 1) =
          (if i ∈ T then (I.p i j * (if (i, j) ∉ Y then 1 else 0) + (1 - I.p i j)) else 1) := by
        intro i
        by_cases h1 : i ∈ T <;> by_cases h2 : (i, j) ∈ Y <;> simp [h1, h2]
      simp_rw [e]
      rw [Finset.prod_ite_mem univ T, Finset.univ_inter]
    rw [this, Finset.prod_add]
    refine Finset.sum_congr rfl (fun R _ => ?_)
    rw [Finset.prod_mul_distrib, Finset.prod_boole]
    ring_nf
  simp_rw [hprod, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hp := fun i => hI.2.2.2.1 i j
  have hP : ∀ R : Finset (Fin n),
      ∑ Y, μ Y * (((∏ i ∈ R, I.p i j) * ∏ i ∈ T \ R, (1 - I.p i j)) *
        (if ∀ i ∈ R, (i, j) ∉ Y then 1 else 0)) =
      ((∏ i ∈ R, I.p i j) * ∏ i ∈ T \ R, (1 - I.p i j)) *
        probAll μ (R.image (fun i => (i, j))) false := by
    intro R
    unfold probAll
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Y _ => ?_)
    have hc : (∀ i ∈ R, (i, j) ∉ Y) ↔
        (∀ e ∈ R.image (fun i => (i, j)), decide (e ∈ Y) = false) := by
      simp
    by_cases h : ∀ i ∈ R, (i, j) ∉ Y
    · rw [if_pos h, if_pos (hc.mp h)]; ring
    · rw [if_neg h, if_neg (fun h' => h (hc.mpr h'))]; ring
  simp_rw [hP]
  have hNC : ∀ R : Finset (Fin n), probAll μ (R.image (fun i => (i, j))) false ≤
      ∏ i ∈ R, (1 - y i j) := by
    intro R
    have := hμ.negcorr_right j (R.image (fun i => (i, j))) (by
      intro e he; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he; rfl) false
    rw [Finset.prod_image (fun a _ b _ h => by simpa using h)] at this
    simp_rw [probAll_single_false y μ hμ] at this
    exact this
  calc ∑ R ∈ T.powerset, ((∏ i ∈ R, I.p i j) * ∏ i ∈ T \ R, (1 - I.p i j)) *
        probAll μ (R.image (fun i => (i, j))) false
      ≤ ∑ R ∈ T.powerset, ((∏ i ∈ R, I.p i j) * ∏ i ∈ T \ R, (1 - I.p i j)) *
          ∏ i ∈ R, (1 - y i j) := by
        refine Finset.sum_le_sum (fun R _ => mul_le_mul_of_nonneg_left (hNC R) ?_)
        exact mul_nonneg (Finset.prod_nonneg (fun i _ => (hp i).1))
          (Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (hp i).2))
    _ = ∏ i ∈ T, (I.p i j * (1 - y i j) + (1 - I.p i j)) := by
        rw [Finset.prod_add]
        refine Finset.sum_congr rfl (fun R _ => ?_)
        rw [Finset.prod_mul_distrib]; ring
    _ = ∏ i ∈ T, (1 - y i j * I.p i j) := by
        refine Finset.prod_congr rfl (fun i _ => ?_); ring

end HLP2L7

open HLP2L7 in
theorem solution {n k : ℕ} (I : Instance n k) (hI : I.Valid)
    (acc : Fin n → Finset (Fin k) → ℝ) (hacc : AccLaw I acc)
    (y : Fin n → Fin k → ℝ) (hy : LPFeasible I y)
    (μ : Finset (Fin n × Fin k) → ℝ) (hμ : IsGKPS y μ) (j : Fin k) :
    EvDtilde I y j ≤ EvD I acc μ j := by
  classical
  set x : Fin n → ℝ := fun i => y i j * I.p i j with hxdef
  set v : Fin n → ℝ := fun i => I.v i j with hvdef
  let π₁ : Finset (Fin n × Fin k) × (Fin n → Finset (Fin k)) → ℝ :=
    fun ω => μ ω.1 * accProb acc ω.2
  let D₁ : Finset (Fin n × Fin k) × (Fin n → Finset (Fin k)) → Finset (Fin n) :=
    fun ω => Dset j ω.1 ω.2
  let π₂ : Finset (Fin n) → ℝ := fun S => w x univ S
  let D₂ : Finset (Fin n) → Finset (Fin n) := fun S => S
  have hA1 : ∑ A : Fin n → Finset (Fin k), accProb acc A = 1 := by
    unfold accProb
    rw [← Fintype.prod_sum (fun i B => acc i B)]
    exact Finset.prod_eq_one (fun i _ => hacc.2.1 i)
  have hs1 : ∑ ω, π₁ ω = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [π₁]
    simp_rw [← Finset.mul_sum, hA1, mul_one]
    exact hμ.sum_one
  have hs2 : ∑ ω, π₂ ω = 1 := by
    simp only [π₂]
    rw [← Finset.powerset_univ]; exact w_sum_one x univ
  have hT : ∀ T : Finset (Fin n), ∑ ω, π₁ ω * (if D₁ ω ∩ T = ∅ then 1 else 0) ≤
      ∑ ω, π₂ ω * (if D₂ ω ∩ T = ∅ then 1 else 0) := by
    intro T
    have e1 : ∑ ω, π₁ ω * (if D₁ ω ∩ T = ∅ then 1 else 0) =
        ∑ Y, μ Y * ∑ A : Fin n → Finset (Fin k), accProb acc A *
          (if Dset j Y A ∩ T = ∅ then 1 else 0) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun Y _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun A _ => ?_)
      simp only [π₁, D₁]; ring
    have e2 : ∑ ω, π₂ ω * (if D₂ ω ∩ T = ∅ then 1 else 0) = ∏ i ∈ T, (1 - y i j * I.p i j) := by
      simp only [π₂, D₂]
      rw [← Finset.powerset_univ, w_avoid x T univ, Finset.prod_ite_mem, Finset.univ_inter]
    rw [e1, e2]
    exact dep_avoid I hI acc hacc y hy μ hμ j T
  have hv : ∀ i ∈ (univ : Finset (Fin n)), 0 ≤ v i := fun i _ => hI.2.2.2.2 i j
  have hcmp := compare π₁ D₁ π₂ D₂ (by rw [hs1, hs2]) hT _ univ rfl v hv
  have hL : EvDtilde I y j = ∑ ω, π₂ ω * vmax v (D₂ ω ∩ univ) := by
    unfold EvDtilde
    refine Finset.sum_congr rfl (fun S _ => ?_)
    simp only [π₂, D₂, Finset.inter_univ]
    rfl
  have hR : EvD I acc μ j = ∑ ω, π₁ ω * vmax v (D₁ ω ∩ univ) := by
    unfold EvD
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun Y _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    simp only [π₁, D₁, Finset.inter_univ]
    rw [mul_assoc]
    rfl
  rw [hL, hR]; exact hcmp
