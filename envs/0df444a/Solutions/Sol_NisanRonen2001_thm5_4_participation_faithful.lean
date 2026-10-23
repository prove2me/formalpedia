-- Prove2me | solution 1 for NisanRonen2001.thm5_4_participation_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:53:06.162981+00:00
-- url     : https://prove2.me/submissions/fc6d11f7-8ffc-4d66-8cbf-61446808a693

import Mathlib
import Definitions.Def_AlgMechDesign_CompBonus_Model

open AlgMechDesign.CompBonus Finset

namespace NR85

variable {n k : ℕ} [NeZero n]

theorem le_makespan (t : Fin n → Fin k → ℝ) (x : Fin k → Fin n) (l : Fin n) :
    load t x l ≤ makespan t x := Finset.le_sup' (load t x) (mem_univ l)

theorem makespan_le {t : Fin n → Fin k → ℝ} {x : Fin k → Fin n} {B : ℝ}
    (h : ∀ l, load t x l ≤ B) : makespan t x ≤ B :=
  Finset.sup'_le _ _ (fun l _ => h l)

theorem gT_mono {x : Fin k → Fin n} {τ σ : Fin k → ℝ} (h : ∀ j, τ j ≤ σ j) :
    gT x τ ≤ gT x σ := by
  unfold gT
  apply Finset.sup'_le; intro l _
  refine le_trans ?_ (Finset.le_sup' (fun l => ∑ j ∈ univ.filter (fun j => x j = l), σ j) (mem_univ l))
  exact Finset.sum_le_sum (fun j _ => h j)

theorem gT_eq (x : Fin k → Fin n) (e : Fin n → Fin k → ℝ) :
    gT x (fun j => e (x j) j) = makespan e x := by
  unfold gT makespan load
  congr 1; funext l
  apply Finset.sum_congr rfl
  intro j hj; show e (x j) j = e l j; rw [(Finset.mem_filter.mp hj).2]

theorem le_gT (x : Fin k → Fin n) (τ : Fin k → ℝ) (l : Fin n) :
    ∑ j ∈ univ.filter (fun j => x j = l), τ j ≤ gT x τ :=
  Finset.le_sup' (fun l => ∑ j ∈ univ.filter (fun j => x j = l), τ j) (mem_univ l)

theorem le_gT_single (x : Fin k → Fin n) (τ : Fin k → ℝ) (hτ : ∀ j, 0 ≤ τ j) (j : Fin k) :
    τ j ≤ gT x τ := by
  refine le_trans ?_ (le_gT x τ (x j))
  exact Finset.single_le_sum (f := τ) (fun j _ => hτ j) (by simp)

theorem single_le_load (t : Fin n → Fin k → ℝ) (ht : ∀ l j, 0 ≤ t l j) (x : Fin k → Fin n)
    (j : Fin k) : t (x j) j ≤ load t x (x j) := by
  unfold load
  exact Finset.single_le_sum (f := fun j' => t (x j) j') (fun j' _ => ht _ _) (by simp)

theorem load_le_card {t : Fin n → Fin k → ℝ} {x : Fin k → Fin n} {l : Fin n} {B : ℝ}
    (hB : ∀ j, x j = l → t l j ≤ B) (hB0 : 0 ≤ B) : load t x l ≤ k * B := by
  unfold load
  calc ∑ j ∈ univ.filter (fun j => x j = l), t l j
      ≤ (univ.filter (fun j => x j = l)).card • B :=
        Finset.sum_le_card_nsmul _ _ _ (fun j hj => hB j (Finset.mem_filter.mp hj).2)
    _ ≤ k * B := by
        rw [nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ hB0
        have := Finset.card_filter_le (univ : Finset (Fin k)) (fun j => x j = l)
        simp only [card_univ, Fintype.card_fin] at this
        exact_mod_cast this

theorem load_empty {t : Fin n → Fin k → ℝ} {x : Fin k → Fin n} {l : Fin n}
    (h : ∀ j, x j ≠ l) : load t x l = 0 := by
  unfold load
  rw [Finset.sum_eq_zero]; intro j hj; exact absurd (Finset.mem_filter.mp hj).2 (h j)

theorem exists_opt (d : Fin n → Fin k → ℝ) :
    ∃ x : Fin k → Fin n, ∀ y, makespan d x ≤ makespan d y := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  exact Finite.exists_min (fun x => makespan d x)

noncomputable def alloc (d : Fin n → Fin k → ℝ) : Fin k → Fin n :=
  Classical.choose (exists_opt d)

theorem alloc_opt (d : Fin n → Fin k → ℝ) (y : Fin k → Fin n) :
    makespan d (alloc d) ≤ makespan d y :=
  Classical.choose_spec (exists_opt d) y

/-- another agent -/
def oth (hn : 2 ≤ n) (i : Fin n) : Fin n :=
  if (i : ℕ) = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩

theorem oth_ne (hn : 2 ≤ n) (i : Fin n) : oth hn i ≠ i := by
  unfold oth; split_ifs with h <;> intro e <;> rw [← e] at h <;> simp at h

noncomputable def pay (hn : 2 ≤ n) (d : Fin n → Fin k → ℝ) (tt : Fin k → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ univ.filter (fun j => alloc d j = i), tt j + makespan d (fun _ => oth hn i)
    - gT (alloc d) (corr i (alloc d) d tt)

theorem utility_eq (hn : 2 ≤ n) (d : Fin n → Fin k → ℝ) (E : Fin n → ExecPlan n k) (i : Fin n) :
    utility alloc (pay hn) d E i = makespan d (fun _ => oth hn i)
      - gT (alloc d) (corr i (alloc d) d (actualTimes alloc d E)) := by
  unfold utility pay; ring

theorem makespan_avoid (d : Fin n → Fin k → ℝ) (i : Fin n) (a : Fin k → ℝ) (y : Fin k → Fin n)
    (hy : ∀ j, y j ≠ i) : makespan (Function.update d i a) y = makespan d y := by
  unfold makespan load
  congr 1; funext l
  apply Finset.sum_congr rfl
  intro j hj
  have hl : l ≠ i := by rw [← (Finset.mem_filter.mp hj).2]; exact hy j
  rw [Function.update_of_ne hl]

/-- the minimal execution plan -/
def emin (ti : Fin k → ℝ) : ExecPlan n k := fun _ j => ti j

theorem gT_ge (d : Fin n → Fin k → ℝ) (E : Fin n → ExecPlan n k) (i : Fin n)
    (ti di' : Fin k → ℝ) (e' : ExecPlan n k) (hfe : FeasibleExec i ti e') :
    makespan (Function.update d i ti) (alloc (Function.update d i di')) ≤
      gT (alloc (Function.update d i di')) (corr i (alloc (Function.update d i di'))
        (Function.update d i di') (actualTimes alloc (Function.update d i di')
          (Function.update E i e'))) := by
  set x := alloc (Function.update d i di')
  rw [← gT_eq]
  apply gT_mono; intro j
  unfold corr actualTimes
  by_cases hj : x j = i
  · rw [if_pos hj]
    change Function.update d i ti (x j) j ≤ Function.update E i e' (x j) x j
    rw [hj, Function.update_self, Function.update_self]
    exact hfe _ j hj
  · rw [if_neg hj, Function.update_of_ne hj, Function.update_of_ne hj]

theorem gT_truth (d : Fin n → Fin k → ℝ) (E : Fin n → ExecPlan n k) (i : Fin n)
    (ti : Fin k → ℝ) (e : ExecPlan n k) (he : ∀ x j, x j = i → e x j = ti j) :
    gT (alloc (Function.update d i ti)) (corr i (alloc (Function.update d i ti))
        (Function.update d i ti) (actualTimes alloc (Function.update d i ti)
          (Function.update E i e))) =
      makespan (Function.update d i ti) (alloc (Function.update d i ti)) := by
  set x := alloc (Function.update d i ti)
  rw [← gT_eq]
  congr 1; funext j
  unfold corr actualTimes
  by_cases hj : x j = i
  · rw [if_pos hj]
    change Function.update E i e (x j) x j = Function.update d i ti (x j) j
    rw [hj, Function.update_self, Function.update_self]
    exact he _ j hj
  · rw [if_neg hj]

theorem dominant_truth (hn : 2 ≤ n) (i : Fin n) (ti : Fin k → ℝ) (hti : IsAgentType ti) :
    Dominant alloc (pay hn) i ti ti (emin ti) := by
  refine ⟨hti, fun x j _ => le_rfl, ?_⟩
  intro d _ E di' _ ei' hfe
  rw [utility_eq, utility_eq, makespan_avoid _ _ _ _ (fun j => oth_ne hn i),
    makespan_avoid _ _ _ _ (fun j => oth_ne hn i), gT_truth d E i ti (emin ti) (fun _ _ _ => rfl)]
  have h1 := gT_ge d E i ti di' ei' hfe
  have h2 := alloc_opt (Function.update d i ti) (alloc (Function.update d i di'))
  linarith

/-- consequence of dominance used for strong truthfulness -/
theorem dom_key (hn : 2 ≤ n) {i : Fin n} {ti di : Fin k → ℝ} {ei : ExecPlan n k}
    (hti : IsAgentType ti) (hd : Dominant alloc (pay hn) i ti di ei)
    (d : Fin n → Fin k → ℝ) (hdT : IsType d) (E : Fin n → ExecPlan n k) :
    gT (alloc (Function.update d i di)) (corr i (alloc (Function.update d i di))
        (Function.update d i di) (actualTimes alloc (Function.update d i di)
          (Function.update E i ei))) ≤
      makespan (Function.update d i ti) (alloc (Function.update d i ti)) := by
  have := hd.2.2 d hdT E ti hti (emin ti) (fun x j _ => le_rfl)
  rw [utility_eq, utility_eq, makespan_avoid _ _ _ _ (fun j => oth_ne hn i),
    makespan_avoid _ _ _ _ (fun j => oth_ne hn i), gT_truth d E i ti (emin ti) (fun _ _ _ => rfl)]
    at this
  linarith

theorem corr_nonneg {i : Fin n} {ti di : Fin k → ℝ} {ei : ExecPlan n k}
    (hti : IsAgentType ti) (hfe : FeasibleExec i ti ei) (hdi : IsAgentType di)
    (d : Fin n → Fin k → ℝ) (hdT : IsType d) (E : Fin n → ExecPlan n k) (j : Fin k) :
    0 ≤ corr i (alloc (Function.update d i di)) (Function.update d i di)
      (actualTimes alloc (Function.update d i di) (Function.update E i ei)) j := by
  unfold corr actualTimes
  split_ifs with hj
  · rw [hj, Function.update_self]; exact (hti j).le.trans (hfe _ j hj)
  · rw [Function.update_of_ne hj]; exact (hdT _ _).le

end NR85
namespace NR85

variable {n k : ℕ} [NeZero n]

theorem sum_ite_le (s : Finset (Fin k)) (j : Fin k) {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε) :
    ∑ j' ∈ s, (if j' = j then c else ε) ≤ c + k * ε := by
  calc ∑ j' ∈ s, (if j' = j then c else ε) ≤ ∑ j', (if j' = j then c else ε) :=
        Finset.sum_le_sum_of_subset_of_nonneg (subset_univ s)
          (fun j' _ _ => by split_ifs <;> assumption)
    _ ≤ ∑ j', ((if j' = j then c else 0) + ε) := by
        apply Finset.sum_le_sum; intro j' _; split_ifs <;> linarith
    _ = c + k * ε := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq']; simp

theorem ms_y0 (e : Fin n → Fin k → ℝ) (l0 : Fin n) (j : Fin k) {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hrow : ∀ j', e l0 j' = if j' = j then c else ε) :
    makespan e (fun _ => l0) ≤ c + k * ε := by
  apply makespan_le; intro l
  by_cases hl : l = l0
  · subst hl; unfold load; simp_rw [hrow]; exact sum_ite_le _ j hc hε
  · rw [load_empty (fun j' => Ne.symm hl)]; positivity

theorem ms_y1 (e : Fin n → Fin k → ℝ) (i l0 : Fin n) (hne : l0 ≠ i) (j : Fin k) {c ε B : ℝ}
    (hε : 0 ≤ ε) (hrow : ∀ j', e l0 j' = if j' = j then c else ε) (hv : e i j ≤ B)
    (hkε : k * ε ≤ B) (hB : 0 ≤ B) :
    makespan e (fun j' => if j' = j then i else l0) ≤ B := by
  apply makespan_le; intro l
  by_cases hl : l = i
  · subst hl
    unfold load
    have : univ.filter (fun j' => (if j' = j then l else l0) = l) = {j} := by
      ext j'; simp only [mem_filter, mem_univ, true_and, mem_singleton]
      split_ifs with h <;> simp [h, hne]
    rw [this, sum_singleton]; exact hv
  by_cases hl0 : l = l0
  · subst hl0
    refine le_trans (load_le_card (B := ε) ?_ hε) hkε
    intro j' hj'
    have : j' ≠ j := by intro h; rw [if_pos h] at hj'; exact hne hj'.symm
    rw [hrow, if_neg this]
  · rw [load_empty]; · exact hB
    intro j'; split_ifs
    · exact Ne.symm hl
    · exact Ne.symm hl0

/-- dominant strategies declare the truth -/
theorem decl_eq (hn : 2 ≤ n) {i : Fin n} {ti di : Fin k → ℝ} {ei : ExecPlan n k}
    (hti : IsAgentType ti) (hd : Dominant alloc (pay hn) i ti di ei) : di = ti := by
  by_contra hne
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  have ha : 0 < di j := hd.1 j
  have hb : 0 < ti j := hti j
  set a := di j with ha_def
  set b := ti j with hb_def
  set l0 := oth hn i
  have hl0 : l0 ≠ i := oth_ne hn i
  set c := (a + b) / 2
  have hab : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr hj)
  set ε := |a - b| / (4 * (k + 1))
  have hε : 0 < ε := by positivity
  have hkε : k * ε < |a - b| / 4 := by
    have : k * ε = |a - b| / 4 * (k / (k + 1)) := by simp only [ε]; field_simp
    rw [this]
    have : (k : ℝ) / (k + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith
  set M := a + b + 1
  let d : Fin n → Fin k → ℝ := fun l j' =>
    if l = i then ti j' else if l = l0 then (if j' = j then c else ε) else M
  have hdT : IsType d := by
    intro l j'; simp only [d]; split_ifs
    · exact hti j'
    · positivity
    · positivity
    · positivity
  have key := dom_key hn hti hd d hdT (fun _ => emin ti)
  set D' := Function.update d i di
  set D'' := Function.update d i ti
  set x := alloc D'
  have hD'i : D' i = di := Function.update_self _ _ _
  have hD''i : D'' i = ti := Function.update_self _ _ _
  have hD'l0 : ∀ j', D' l0 j' = if j' = j then c else ε := by
    intro j'; simp only [D', Function.update_of_ne hl0, d, if_neg hl0, if_true]
  have hD''l0 : ∀ j', D'' l0 j' = if j' = j then c else ε := by
    intro j'; simp only [D'', Function.update_of_ne hl0, d, if_neg hl0, if_true]
  have hD'M : ∀ l, l ≠ i → l ≠ l0 → D' l j = M := by
    intro l h1 h2; simp only [D', Function.update_of_ne h1, d, if_neg h1, if_neg h2]
  have hD'pos : ∀ l j', 0 ≤ D' l j' := by
    intro l j'; by_cases h : l = i
    · subst h; rw [hD'i]; exact (hd.1 j').le
    · simp only [D', Function.update_of_ne h]; exact (hdT l j').le
  have hgT := le_gT_single x _ (corr_nonneg hti hd.2.1 hd.1 d hdT (fun _ => emin ti)) j
  have hopt := alloc_opt D'
  have hopt'' := alloc_opt D''
  have hMx : D' (x j) j ≤ makespan D' x :=
    (single_le_load D' hD'pos x j).trans (le_makespan _ _ _)
  rcases lt_or_gt_of_ne hj with hlt | hgt
  · -- a < b
    have habs : |a - b| = b - a := by rw [abs_sub_comm]; exact abs_of_pos (by linarith)
    have hy1 : makespan D' (fun j' => if j' = j then i else l0) ≤ max a (k * ε) :=
      ms_y1 D' i l0 hl0 j hε.le hD'l0 (by rw [hD'i]; exact le_max_left _ _) (le_max_right _ _)
        (le_max_of_le_left ha.le)
    have hmax : max a (k * ε) < c := max_lt (by simp only [c]; linarith) (by simp only [c]; linarith)
    have hxj : x j = i := by
      by_contra h
      have := hMx.trans (hopt _) |>.trans hy1
      by_cases h0 : x j = l0
      · rw [h0, hD'l0, if_pos rfl] at this; linarith
      · rw [hD'M _ h h0] at this
        have : max a (k * ε) < M := hmax.trans (by simp only [c, M]; linarith)
        linarith
    have hcj : b ≤ corr i x D' (actualTimes alloc D' (Function.update (fun _ => emin ti) i ei)) j := by
      unfold corr actualTimes
      rw [if_pos hxj]
      change ti j ≤ Function.update (fun _ => emin ti) i ei (x j) x j
      rw [hxj, Function.update_self]
      exact hd.2.1 x j hxj
    have hy0 := ms_y0 D'' l0 j (by positivity) hε.le hD''l0
    have := (hcj.trans hgT).trans (key.trans ((hopt'' _).trans hy0))
    simp only [c] at this
    linarith
  · -- a > b
    have habs : |a - b| = a - b := abs_of_pos (by linarith)
    have hy0 := ms_y0 D' l0 j (by positivity) hε.le hD'l0
    have hxj : x j = l0 := by
      by_contra h
      have := hMx.trans (hopt _) |>.trans hy0
      by_cases h0 : x j = i
      · rw [h0, hD'i] at this; simp only [c] at this; linarith
      · rw [hD'M _ h0 h] at this; simp only [c, M] at this; linarith
    have hcj : c ≤ corr i x D' (actualTimes alloc D' (Function.update (fun _ => emin ti) i ei)) j := by
      unfold corr
      rw [if_neg (by rw [hxj]; exact hl0), hxj, hD'l0, if_pos rfl]
    have hy1 : makespan D'' (fun j' => if j' = j then i else l0) ≤ max b (k * ε) :=
      ms_y1 D'' i l0 hl0 j hε.le hD''l0 (by rw [hD''i]; exact le_max_left _ _) (le_max_right _ _)
        (le_max_of_le_left hb.le)
    have hmax : max b (k * ε) < c := max_lt (by simp only [c]; linarith) (by simp only [c]; linarith)
    have := (hcj.trans hgT).trans (key.trans ((hopt'' _).trans hy1))
    linarith

/-- dominant strategies execute in minimal time -/
theorem exec_eq (hn : 2 ≤ n) {i : Fin n} {ti : Fin k → ℝ} {ei : ExecPlan n k}
    (hti : IsAgentType ti) (hd : Dominant alloc (pay hn) i ti ti ei) :
    ∀ (x : Fin k → Fin n) (j : Fin k), x j = i → ei x j = ti j := by
  intro x j hxj
  by_contra hne
  have hgt : ti j < ei x j := lt_of_le_of_ne (hd.2.1 x j hxj) (Ne.symm hne)
  set L := ∑ j' ∈ univ.filter (fun j' => x j' = i), ti j'
  have hL : ti j ≤ L :=
    Finset.single_le_sum (f := ti) (fun j' _ => (hti j').le) (by simp [hxj])
  have hL0 : 0 < L := (hti j).trans_le hL
  set δ := L / (k + 1)
  have hδ : 0 < δ := by positivity
  have hkδ : k * δ ≤ L := by
    have : k * δ = L * (k / (k + 1)) := by simp only [δ]; field_simp
    rw [this]
    have : (k : ℝ) / (k + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith
  set M := L + 1
  let d : Fin n → Fin k → ℝ := fun l j' =>
    if l = i then ti j' else if x j' = l then δ else M
  have hdT : IsType d := by
    intro l j'; simp only [d]; split_ifs
    · exact hti j'
    · positivity
    · positivity
  have key := dom_key hn hti hd d hdT (fun _ => emin ti)
  have hdi : d i = ti := by funext j'; simp [d]
  have hU : Function.update d i ti = d := by rw [← hdi]; exact Function.update_eq_self i d
  rw [hU] at key
  have hdpos : ∀ l j', 0 ≤ d l j' := fun l j' => (hdT l j').le
  have hmx : makespan d x ≤ L := by
    apply makespan_le; intro l
    by_cases hl : l = i
    · subst hl; unfold load; rw [hdi]
    · refine le_trans (load_le_card (B := δ) ?_ hδ.le) hkδ
      intro j' hj'; simp [d, hl, hj']
  have hax : alloc d = x := by
    set y := alloc d
    have hy : makespan d y ≤ L := (alloc_opt d x).trans hmx
    have hmis : ∀ j', y j' ≠ x j' → y j' = i := by
      intro j' hne'
      by_contra hyi
      have h1 := (single_le_load d hdpos y j').trans (le_makespan d y (y j'))
      have : d (y j') j' = M := by simp [d, hyi, Ne.symm hne']
      rw [this] at h1
      simp only [M] at h1; linarith
    funext j'
    by_contra hne'
    have hyi := hmis j' hne'
    have hsub : insert j' (univ.filter (fun j'' => x j'' = i)) ⊆ univ.filter (fun j'' => y j'' = i) := by
      intro j'' hj''
      rw [Finset.mem_insert] at hj''
      simp only [mem_filter, mem_univ, true_and] at hj'' ⊢
      rcases hj'' with h | h
      · rw [h]; exact hyi
      · by_contra hy''
        exact hy'' (hmis j'' (by rw [h]; exact hy''))
    have hnot : j' ∉ univ.filter (fun j'' => x j'' = i) := by
      simp only [mem_filter, mem_univ, true_and]; intro h; exact hne' (by rw [hyi, h])
    have h2 : L + ti j' ≤ load d y i := by
      unfold load; rw [hdi]
      calc L + ti j' = ∑ j'' ∈ insert j' (univ.filter (fun j'' => x j'' = i)), ti j'' := by
            rw [Finset.sum_insert hnot]; ring
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j'' _ _ => (hti j'').le)
    have := h2.trans ((le_makespan d y i).trans hy)
    linarith [hti j']
  rw [hax] at key
  have hlow := le_gT x (corr i x d (actualTimes alloc d (Function.update (fun _ => emin ti) i ei))) i
  have hstrict : L < ∑ j' ∈ univ.filter (fun j' => x j' = i),
      corr i x d (actualTimes alloc d (Function.update (fun _ => emin ti) i ei)) j' := by
    apply Finset.sum_lt_sum
    · intro j' hj'
      have hxj' := (Finset.mem_filter.mp hj').2
      unfold corr actualTimes
      rw [if_pos hxj', hax, hxj', Function.update_self]
      exact hd.2.1 x j' hxj'
    · refine ⟨j, by simp [hxj], ?_⟩
      unfold corr actualTimes
      rw [if_pos hxj, hax, hxj, Function.update_self]
      exact hgt
  linarith

theorem strongly (hn : 2 ≤ n) : StronglyTruthful (alloc (n := n) (k := k)) (pay hn) := by
  refine ⟨fun i ti hti => ⟨emin ti, dominant_truth hn i ti hti⟩, ?_⟩
  intro i ti hti di ei hd
  have h1 := decl_eq hn hti hd
  subst h1
  exact ⟨rfl, exec_eq hn hti hd⟩

end NR85

open NR85 in
theorem solution {n k : ℕ} [NeZero n] (hn : 2 ≤ n) :
    ∃ (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
      (pay : (Fin n → Fin k → ℝ) → (Fin k → ℝ) → Fin n → ℝ),
      IsOptimalAlloc alloc ∧ StronglyTruthful alloc pay ∧ ImplementsOptimum alloc pay ∧
        Participation alloc pay := by
  refine ⟨NR85.alloc, NR85.pay hn, fun d _ y => alloc_opt d y, strongly hn, ?_, ?_⟩
  · intro t ht D E hD y
    have hDt : D = t := funext fun l => decl_eq hn (ht l) (hD l)
    subst hDt
    have hE : actualTimes NR85.alloc D E = fun j => D (NR85.alloc D j) j := by
      funext j; unfold actualTimes
      exact exec_eq hn (ht _) (hD _) _ j rfl
    rw [hE, gT_eq]
    exact alloc_opt D y
  · intro t ht tt i htt
    have : corr i (NR85.alloc t) t tt = fun j => t (NR85.alloc t j) j := by
      funext j; unfold corr; split_ifs with h
      · rw [htt j h, h]
      · rfl
    unfold pay
    rw [this, gT_eq]
    have := alloc_opt t (fun _ => oth hn i)
    linarith
