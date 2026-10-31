-- Prove2me | solution 1 for LiquidDemocracy.Upward.urn_coupling
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T12:10:11.28324+00:00
-- url     : https://prove2.me/submissions/6eb8bdc7-befd-4639-bc81-a3efe0e44b37

import Mathlib
import Definitions.Def_LiquidDemocracy_Upward_Setting
import Definitions.Def_LiquidDemocracy_Upward_Urn

open MeasureTheory Filter Topology LiquidDemocracy.Upward
open scoped Classical

/-! ## Part 1: the urn step on multisets of bin sizes -/

/-- The urn step as an operator on functions of the multiset of bin sizes (time `t`). -/
noncomputable def LU_T (p : ℝ) (t : ℕ) (F : Multiset ℕ → ENNReal) (m : Multiset ℕ) : ENNReal :=
  ENNReal.ofReal (1 - p) * F (1 ::ₘ m) +
    (m.map fun x : ℕ => ENNReal.ofReal (p * x / t) * F ((x + 1) ::ₘ m.erase x)).sum

theorem LU_coe_modify (s : List ℕ) (k : ℕ) (hk : k < s.length) :
    ((s.modify k (· + 1) : List ℕ) : Multiset ℕ) =
      (s[k] + 1) ::ₘ ((s : Multiset ℕ).erase s[k]) := by
  have h1 : s.modify k (· + 1) = s.take k ++ (s[k] + 1) :: s.drop (k + 1) :=
    List.modify_eq_take_cons_drop hk
  have h2 : s = s.take k ++ s[k] :: s.drop (k + 1) := by
    conv_lhs => rw [← List.take_append_drop k s]
    rw [List.drop_eq_getElem_cons hk]
  have h3 : (s : Multiset ℕ) = s[k] ::ₘ ((s.take k ++ s.drop (k + 1) : List ℕ) : Multiset ℕ) := by
    conv_lhs => rw [h2]
    rw [Multiset.cons_coe]
    exact Multiset.coe_eq_coe.mpr List.perm_middle
  rw [h3, Multiset.erase_cons_head, h1, Multiset.cons_coe]
  exact Multiset.coe_eq_coe.mpr List.perm_middle

theorem LU_sum_get (s : List ℕ) (G : ℕ → ENNReal) :
    ∑ k : Fin s.length, G (s.get k) = ((s : Multiset ℕ).map G).sum := by
  rw [Multiset.map_coe, Multiset.sum_coe, ← List.sum_ofFn]
  congr 1
  conv_rhs => rw [← List.ofFn_get s]
  rw [List.map_ofFn]
  rfl

theorem LU_step_lintegral (p : ℝ) (t : ℕ) (F : Multiset ℕ → ENNReal) (s : List ℕ) :
    ∫⁻ s', F (s' : Multiset ℕ) ∂(urnStep p t s) = LU_T p t F (s : Multiset ℕ) := by
  have hF : Measurable fun s' : List ℕ => F (s' : Multiset ℕ) := measurable_from_top
  unfold urnStep
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_dirac' _ hF,
    lintegral_finsetSum_measure]
  unfold LU_T
  congr 1
  · congr 2
    exact Multiset.coe_eq_coe.mpr (List.perm_append_singleton 1 s)
  · rw [← LU_sum_get s (fun x : ℕ => ENNReal.ofReal (p * x / t) *
      F ((x + 1) ::ₘ (s : Multiset ℕ).erase x))]
    apply Finset.sum_congr rfl
    intro k _
    rw [lintegral_smul_measure, lintegral_dirac' _ hF, smul_eq_mul]
    congr 2
    have := LU_coe_modify s k k.2
    simpa using this

theorem LU_urn_succ (p : ℝ) (t : ℕ) (ht : 1 ≤ t) (F : Multiset ℕ → ENNReal) :
    ∫⁻ s, F (s : Multiset ℕ) ∂(urnLaw p (t + 1)) =
      ∫⁻ s, LU_T p t F (s : Multiset ℕ) ∂(urnLaw p t) := by
  obtain ⟨r, rfl⟩ : ∃ r, t = r + 1 := ⟨t - 1, by omega⟩
  simp only [urnLaw]
  rw [Measure.lintegral_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  apply lintegral_congr
  intro s
  exact LU_step_lintegral p (r + 1) F s

/-! ## Part 2: upward delegation restricted to a voter set `V` -/

section Restricted
variable {n : ℕ} (p : ℝ) (c : Fin n → ℝ)

/-- Voters of `V` strictly more competent than `j`. -/
noncomputable def LU_above (V : Finset (Fin n)) (j : Fin n) : Finset (Fin n) := V.filter fun k => c j < c k

noncomputable def LU_P (V : Finset (Fin n)) (j k : Fin n) : ℝ :=
  if LU_above c V j = ∅ then (if k = j then 1 else 0)
  else if k = j then 1 - p
  else if k ∈ LU_above c V j then p / (LU_above c V j).card else 0

noncomputable def LU_W (V : Finset (Fin n)) (g : Fin n → Fin n) : ℝ :=
  (∏ j ∈ V, LU_P p c V j (g j)) * ∏ j ∈ Vᶜ, (if g j = j then (1 : ℝ) else 0)

def LU_dir (V : Finset (Fin n)) (g : Fin n → Fin n) : Finset (Fin n) := V.filter fun i => g i = i

noncomputable def LU_size (V : Finset (Fin n)) (g : Fin n → Fin n) (i : Fin n) : ℕ :=
  (V.filter fun j => root g j = i).card

noncomputable def LU_cs (V : Finset (Fin n)) (g : Fin n → Fin n) : Multiset ℕ :=
  (LU_dir V g).val.map (LU_size V g)

theorem LU_P_nonneg (hp : p ∈ Set.Icc (0 : ℝ) 1) (V : Finset (Fin n)) (j k : Fin n) :
    0 ≤ LU_P p c V j k := by
  unfold LU_P
  have := hp.1; have := hp.2
  split_ifs <;> first | positivity | linarith

theorem LU_W_nonneg (hp : p ∈ Set.Icc (0 : ℝ) 1) (V : Finset (Fin n)) (g : Fin n → Fin n) :
    0 ≤ LU_W p c V g := by
  unfold LU_W
  apply mul_nonneg
  · exact Finset.prod_nonneg fun j _ => LU_P_nonneg p c hp V j (g j)
  · exact Finset.prod_nonneg fun j _ => by split_ifs <;> norm_num

variable {p c}

theorem LU_above_erase (V : Finset (Fin n)) (m : Fin n) (hmin : ∀ k ∈ V, k ≠ m → c m < c k)
    (j : Fin n) (hj : j ∈ V.erase m) : LU_above c V j = LU_above c (V.erase m) j := by
  ext k
  simp only [LU_above, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hk, hjk⟩
    refine ⟨⟨?_, hk⟩, hjk⟩
    rintro rfl
    have := hmin j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
    linarith
  · rintro ⟨⟨_, hk⟩, hjk⟩; exact ⟨hk, hjk⟩

theorem LU_above_min (V : Finset (Fin n)) (m : Fin n) (hmin : ∀ k ∈ V, k ≠ m → c m < c k) :
    LU_above c V m = V.erase m := by
  ext k
  simp only [LU_above, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hk, hmk⟩
    exact ⟨fun h => by rw [h] at hmk; exact lt_irrefl _ hmk, hk⟩
  · rintro ⟨hkm, hk⟩; exact ⟨hk, hmin k hk hkm⟩

theorem LU_W_update (V : Finset (Fin n)) (m : Fin n) (hm : m ∈ V)
    (hmin : ∀ k ∈ V, k ≠ m → c m < c k) (g' : Fin n → Fin n) (hg' : g' m = m) (k : Fin n) :
    LU_W p c V (Function.update g' m k) = LU_P p c V m k * LU_W p c (V.erase m) g' := by
  unfold LU_W
  rw [← Finset.mul_prod_erase V _ hm]
  simp only [Function.update_self]
  have h1 : ∏ j ∈ V.erase m, LU_P p c V j (Function.update g' m k j) =
      ∏ j ∈ V.erase m, LU_P p c (V.erase m) j (g' j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    unfold LU_P
    rw [LU_above_erase V m hmin j hj]
  have h2 : ∏ j ∈ Vᶜ, (if Function.update g' m k j = j then (1 : ℝ) else 0) =
      ∏ j ∈ (V.erase m)ᶜ, (if g' j = j then (1 : ℝ) else 0) := by
    have hc : (V.erase m)ᶜ = insert m Vᶜ := by
      ext x; simp only [Finset.mem_compl, Finset.mem_erase, Finset.mem_insert]
      constructor
      · intro h; by_cases hx : x = m
        · left; exact hx
        · right; exact fun hv => h ⟨hx, hv⟩
      · rintro (h | h)
        · rintro ⟨hx, _⟩; exact hx h
        · rintro ⟨_, hv⟩; exact h hv
    rw [hc, Finset.prod_insert (by simp [hm]), if_pos hg', one_mul]
    apply Finset.prod_congr rfl
    intro j hj
    have : j ≠ m := by rintro rfl; exact (Finset.mem_compl.mp hj) hm
    rw [Function.update_of_ne this]
  rw [h1, h2]
  ring

theorem LU_W_support (V : Finset (Fin n)) (g : Fin n → Fin n) (hW : LU_W p c V g ≠ 0) :
    (∀ j ∉ V, g j = j) ∧ ∀ j ∈ V, g j = j ∨ (g j ∈ V ∧ c j < c (g j)) := by
  unfold LU_W at hW
  have h1 := left_ne_zero_of_mul hW
  have h2 := right_ne_zero_of_mul hW
  rw [Finset.prod_ne_zero_iff] at h1 h2
  constructor
  · intro j hj
    have := h2 j (Finset.mem_compl.mpr hj)
    by_contra hne; rw [if_neg hne] at this; exact this rfl
  · intro j hj
    have := h1 j hj
    by_cases hgj : g j = j
    · left; exact hgj
    · right
      unfold LU_P at this
      by_cases ha : LU_above c V j = ∅
      · rw [if_pos ha, if_neg hgj] at this; exact absurd rfl this
      · rw [if_neg ha, if_neg hgj] at this
        by_cases hk : g j ∈ LU_above c V j
        · simp only [LU_above, Finset.mem_filter] at hk
          exact hk
        · rw [if_neg hk] at this; exact absurd rfl this

end Restricted

/-! ## Part 3: roots and component sizes when the least competent voter is added -/

theorem LU_root_fixed {n : ℕ} (c : Fin n → ℝ) (g : DelegGraph n) (hup : ∀ j, g j ≠ j → c j < c (g j)) (j : Fin n) :
    g (root g j) = root g j := by
  by_contra h
  have hstep : ∀ m ≤ n, g (g^[m] j) ≠ g^[m] j := by
    intro m hm hfix
    apply h
    have key : ∀ d, g^[d + m] j = g^[m] j := fun d => by
      rw [Function.iterate_add_apply, Function.iterate_fixed hfix]
    have : g^[n] j = g^[m] j := by
      have := key (n - m); rwa [Nat.sub_add_cancel hm] at this
    unfold root; rw [this]; exact hfix
  have hlt : ∀ a d : ℕ, a + d + 1 ≤ n → c (g^[a] j) < c (g^[a + d + 1] j) := by
    intro a d
    induction d with
    | zero =>
      intro had
      rw [show a + 0 + 1 = a + 1 by ring, Function.iterate_succ_apply']
      exact hup _ (hstep a (by omega))
    | succ d ih =>
      intro had
      refine (ih (by omega)).trans ?_
      have e : g^[a + d + 1 + 1] j = g (g^[a + d + 1] j) := Function.iterate_succ_apply' g _ j
      rw [show a + (d + 1) + 1 = a + d + 1 + 1 by ring, e]
      exact hup _ (hstep _ (by omega))
  have hinj : Function.Injective (fun k : Fin (n + 1) => g^[k] j) := by
    intro x y hxy
    simp only at hxy
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_injective.ne hne) with hl | hl
    · have := hlt x (y - x - 1) (by omega)
      rw [show (x : ℕ) + (y - x - 1) + 1 = y by omega, ← hxy] at this
      exact lt_irrefl _ this
    · have := hlt y (x - y - 1) (by omega)
      rw [show (y : ℕ) + (x - y - 1) + 1 = x by omega, hxy] at this
      exact lt_irrefl _ this
  have := Fintype.card_le_of_injective _ hinj
  simp at this


theorem LU_multiset_bump {ι : Type*} [DecidableEq ι] (d : Finset ι) (f : ι → ℕ) (r : ι) (hr : r ∈ d) :
    d.val.map (fun i => f i + if i = r then 1 else 0) = (f r + 1) ::ₘ (d.val.map f).erase (f r) := by
  have hd : d.val = r ::ₘ (d.erase r).val := by
    rw [← Finset.insert_val_of_notMem (Finset.notMem_erase r d), Finset.insert_erase hr]
  rw [hd, Multiset.map_cons, Multiset.map_cons, Multiset.erase_cons_head, if_pos rfl]
  congr 1
  apply Multiset.map_congr rfl
  intro i hi
  rw [if_neg (Finset.ne_of_mem_erase (Finset.mem_val.mp hi)), add_zero]

section Roots
variable {n : ℕ} {c : Fin n → ℝ} (V : Finset (Fin n)) (m : Fin n) (hm : m ∈ V)
  (g' : Fin n → Fin n)
  (H1 : ∀ j ∉ V.erase m, g' j = j)
  (H2 : ∀ j ∈ V.erase m, g' j = j ∨ (g' j ∈ V.erase m ∧ c j < c (g' j)))
include hm H1 H2

theorem LU_hup' : ∀ j, g' j ≠ j → c j < c (g' j) := by
  intro j hj
  by_cases hjV : j ∈ V.erase m
  · rcases H2 j hjV with h | h
    · exact absurd h hj
    · exact h.2
  · exact absurd (H1 j hjV) hj

theorem LU_iter_stay (j : Fin n) (hj : j ∈ V.erase m) (i : ℕ) : g'^[i] j ∈ V.erase m := by
  induction i with
  | zero => simpa using hj
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    rcases H2 _ ih with h | h
    · rw [h]; exact ih
    · exact h.1

theorem LU_iter_eq (k : Fin n) (j : Fin n) (hj : j ∈ V.erase m) (i : ℕ) :
    (Function.update g' m k)^[i] j = g'^[i] j := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      Function.update_of_ne (Finset.ne_of_mem_erase (LU_iter_stay V m hm g' H1 H2 j hj i))]

theorem LU_root_eq (k : Fin n) (j : Fin n) (hj : j ∈ V.erase m) :
    root (Function.update g' m k) j = root g' j := by
  unfold root; exact LU_iter_eq V m hm g' H1 H2 k j hj n

theorem LU_root_mem (j : Fin n) (hj : j ∈ V.erase m) : root g' j ∈ V.erase m := by
  unfold root; exact LU_iter_stay V m hm g' H1 H2 j hj n

theorem LU_root_fix' (j : Fin n) : g' (root g' j) = root g' j :=
  LU_root_fixed c g' (LU_hup' V m hm g' H1 H2) j

theorem LU_hup (k : Fin n) (hk : k ∈ V.erase m) (hmk : c m < c k) :
    ∀ j, Function.update g' m k j ≠ j → c j < c (Function.update g' m k j) := by
  intro j hj
  by_cases hjm : j = m
  · subst hjm; rw [Function.update_self]; exact hmk
  · rw [Function.update_of_ne hjm] at hj ⊢
    exact LU_hup' V m hm g' H1 H2 j hj

theorem LU_root_m (k : Fin n) (hk : k ∈ V.erase m) (hmk : c m < c k) :
    root (Function.update g' m k) m = root g' k := by
  set g := Function.update g' m k with hg
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact m.elim0)
  have e1 : g^[n] m = g^[(n - 1) + 1] m := congrArg (fun i => g^[i] m) (by omega)
  have e2 : g^[(n - 1) + 1] m = g^[n - 1] k := by
    rw [Function.iterate_succ_apply, hg, Function.update_self]
  have e3 : g^[n - 1] k = g'^[n - 1] k := LU_iter_eq V m hm g' H1 H2 k k hk (n - 1)
  set x := g'^[n - 1] k with hx
  have hxV : x ∈ V.erase m := LU_iter_stay V m hm g' H1 H2 k hk (n - 1)
  have hfix : g (root g m) = root g m := LU_root_fixed c g (LU_hup V m hm g' H1 H2 k hk hmk) m
  have hrx : root g m = x := by unfold root; rw [e1, e2, e3]
  rw [hrx] at hfix
  have hg'x : g' x = x := by
    rw [hg, Function.update_of_ne (Finset.ne_of_mem_erase hxV)] at hfix; exact hfix
  rw [hrx]
  unfold root
  have e4 : g'^[n] k = g'^[(n - 1) + 1] k := congrArg (fun i => g'^[i] k) (by omega)
  rw [e4, Function.iterate_succ_apply', ← hx, hg'x]

theorem LU_size_eq (k : Fin n) (i : Fin n) (hi : i ∈ V.erase m) :
    LU_size V (Function.update g' m k) i =
      LU_size (V.erase m) g' i + if root (Function.update g' m k) m = i then 1 else 0 := by
  unfold LU_size
  conv_lhs => rw [← Finset.insert_erase hm]
  rw [Finset.filter_insert]
  have hfil : (V.erase m).filter (fun j => root (Function.update g' m k) j = i) =
      (V.erase m).filter (fun j => root g' j = i) :=
    Finset.filter_congr fun j hj => by rw [LU_root_eq V m hm g' H1 H2 k j hj]
  rw [hfil]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    simp
  · rfl

theorem LU_cs_self (hg' : g' m = m) :
    LU_cs V g' = 1 ::ₘ LU_cs (V.erase m) g' := by
  have hupd : Function.update g' m m = g' := by
    funext j
    by_cases hj : j = m
    · subst hj; rw [Function.update_self, hg']
    · rw [Function.update_of_ne hj]
  have hdir : LU_dir V g' = insert m (LU_dir (V.erase m) g') := by
    unfold LU_dir
    conv_lhs => rw [← Finset.insert_erase hm]
    rw [Finset.filter_insert, if_pos hg']
  have hnot : m ∉ LU_dir (V.erase m) g' := by
    unfold LU_dir; simp
  have hrootm : root g' m = m := by
    unfold root; exact Function.iterate_fixed hg' n
  unfold LU_cs
  rw [hdir, Finset.insert_val_of_notMem hnot, Multiset.map_cons]
  congr 1
  · -- the singleton component of `m`
    unfold LU_size
    rw [Finset.card_eq_one]
    refine ⟨m, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hj, hr⟩
      by_contra hjm
      have hjV : j ∈ V.erase m := Finset.mem_erase.mpr ⟨hjm, hj⟩
      have := LU_root_mem V m hm g' H1 H2 j hjV
      rw [hr] at this
      exact (Finset.notMem_erase m V) this
    · rintro rfl; exact ⟨hm, hrootm⟩
  · apply Multiset.map_congr rfl
    intro i hi
    have hiV : i ∈ V.erase m := (Finset.mem_filter.mp (Finset.mem_val.mp hi)).1
    have := LU_size_eq V m hm g' H1 H2 m i hiV
    rw [hupd] at this
    rw [this, hrootm, if_neg (Finset.ne_of_mem_erase hiV).symm, add_zero]

theorem LU_cs_bump (k : Fin n) (hk : k ∈ V.erase m) (hmk : c m < c k) :
    LU_cs V (Function.update g' m k) =
      (LU_size (V.erase m) g' (root g' k) + 1) ::ₘ
        (LU_cs (V.erase m) g').erase (LU_size (V.erase m) g' (root g' k)) := by
  have hkm : k ≠ m := Finset.ne_of_mem_erase hk
  have hdir : LU_dir V (Function.update g' m k) = LU_dir (V.erase m) g' := by
    unfold LU_dir
    conv_lhs => rw [← Finset.insert_erase hm]
    rw [Finset.filter_insert, Function.update_self, if_neg hkm]
    apply Finset.filter_congr
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hr : root g' k ∈ LU_dir (V.erase m) g' := by
    unfold LU_dir
    exact Finset.mem_filter.mpr ⟨LU_root_mem V m hm g' H1 H2 k hk, LU_root_fix' V m hm g' H1 H2 k⟩
  unfold LU_cs
  rw [hdir, ← LU_multiset_bump _ _ _ hr]
  apply Multiset.map_congr rfl
  intro i hi
  have hiV : i ∈ V.erase m := (Finset.mem_filter.mp (Finset.mem_val.mp hi)).1
  rw [LU_size_eq V m hm g' H1 H2 k i hiV, LU_root_m V m hm g' H1 H2 k hk hmk]
  congr 1
  by_cases h : root g' k = i
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

end Roots

/-! ## Part 4: one voter at a time — the graph side satisfies the urn recursion -/

theorem LU_reindex {n : ℕ} (H : (Fin n → Fin n) → ENNReal) (m : Fin n) :
    ∑ g, H g = ∑ g' : Fin n → Fin n, ∑ k, (if g' m = m then H (Function.update g' m k) else 0) := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_filter]
  have hk : ∀ k : Fin n, ∑ g' ∈ Finset.univ.filter (fun g' : Fin n → Fin n => g' m = m),
      H (Function.update g' m k) = ∑ g ∈ Finset.univ.filter (fun g : Fin n → Fin n => g m = k), H g := by
    intro k
    apply Finset.sum_nbij' (fun g' => Function.update g' m k) (fun g => Function.update g m m)
    · intro g' _; simp
    · intro g _; simp
    · intro g' hg'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg'
      funext j
      by_cases hj : j = m
      · subst hj; simp [hg']
      · simp [Function.update_of_ne hj]
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
      funext j
      by_cases hj : j = m
      · subst hj; simp [hg]
      · simp [Function.update_of_ne hj]
    · intro g' _; rfl
  simp_rw [hk]
  exact (Finset.sum_fiberwise Finset.univ (fun g : Fin n → Fin n => g m) H).symm

theorem LU_k_sum {n : ℕ} (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (c : Fin n → ℝ)
    (V : Finset (Fin n)) (m : Fin n) (hm : m ∈ V) (hmin : ∀ k ∈ V, k ≠ m → c m < c k)
    (hne : (V.erase m).Nonempty) (F : Multiset ℕ → ENNReal) (g' : Fin n → Fin n)
    (H1 : ∀ j ∉ V.erase m, g' j = j)
    (H2 : ∀ j ∈ V.erase m, g' j = j ∨ (g' j ∈ V.erase m ∧ c j < c (g' j))) :
    ∑ k, ENNReal.ofReal (LU_P p c V m k) * F (LU_cs V (Function.update g' m k)) =
      LU_T p (V.erase m).card F (LU_cs (V.erase m) g') := by
  set V' := V.erase m with hV'
  set t := V'.card with ht
  have hg'm : g' m = m := H1 m (Finset.notMem_erase m V)
  have habove := LU_above_min V m hmin
  have hne' : LU_above c V m ≠ ∅ := by rw [habove]; exact hne.ne_empty
  have hP : ∀ k, LU_P p c V m k = if k = m then 1 - p else if k ∈ V' then p / t else 0 := by
    intro k
    unfold LU_P
    rw [if_neg hne', habove]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m)]
  have hupd : Function.update g' m m = g' := by
    funext j
    by_cases hj : j = m
    · subst hj; rw [Function.update_self, hg'm]
    · rw [Function.update_of_ne hj]
  rw [hP m, if_pos rfl, hupd, LU_cs_self V m hm g' H1 H2 hg'm]
  unfold LU_T
  congr 1
  have hrest : ∀ k ∈ Finset.univ.erase m, ENNReal.ofReal (LU_P p c V m k) *
      F (LU_cs V (Function.update g' m k)) =
      if k ∈ V' then ENNReal.ofReal (p / t) * F (LU_cs V (Function.update g' m k)) else 0 := by
    intro k hk
    rw [hP k, if_neg (Finset.ne_of_mem_erase hk)]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hrest, Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr (fun x hx => Finset.mem_erase.mpr
      ⟨Finset.ne_of_mem_erase hx, Finset.mem_univ x⟩)]
  -- bump formula for each `k ∈ V'`
  set s := LU_size V' g' with hs
  set cs' := LU_cs V' g' with hcs'
  have hbump : ∀ k ∈ V', ENNReal.ofReal (p / t) * F (LU_cs V (Function.update g' m k)) =
      ENNReal.ofReal (p / t) * F ((s (root g' k) + 1) ::ₘ cs'.erase (s (root g' k))) := by
    intro k hk
    rw [LU_cs_bump V m hm g' H1 H2 k hk (hmin k (Finset.mem_of_mem_erase hk)
      (Finset.ne_of_mem_erase hk))]
  rw [Finset.sum_congr rfl hbump]
  have hmaps : ∀ k ∈ V', root g' k ∈ LU_dir V' g' := by
    intro k hk
    unfold LU_dir
    exact Finset.mem_filter.mpr ⟨LU_root_mem V m hm g' H1 H2 k hk, LU_root_fix' V m hm g' H1 H2 k⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ r ∈ LU_dir V' g', ∑ k ∈ V' with root g' k = r,
      ENNReal.ofReal (p / t) * F ((s (root g' k) + 1) ::ₘ cs'.erase (s (root g' k))) =
      ENNReal.ofReal (p * (s r : ℕ) / t) * F ((s r + 1) ::ₘ cs'.erase (s r)) := by
    intro r _
    rw [Finset.sum_congr rfl (fun k hk => by rw [(Finset.mem_filter.mp hk).2]),
      Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
    congr 1
    have hcard : (V'.filter fun k => root g' k = r).card = s r := rfl
    rw [hcard, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1; ring
  rw [Finset.sum_congr rfl hfib, Finset.sum_eq_multiset_sum, hcs']
  unfold LU_cs
  rw [Multiset.map_map]
  rfl

theorem LU_graph_step {n : ℕ} (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (c : Fin n → ℝ)
    (V : Finset (Fin n)) (m : Fin n) (hm : m ∈ V) (hmin : ∀ k ∈ V, k ≠ m → c m < c k)
    (hne : (V.erase m).Nonempty) (F : Multiset ℕ → ENNReal) :
    ∑ g, ENNReal.ofReal (LU_W p c V g) * F (LU_cs V g) =
      ∑ g', ENNReal.ofReal (LU_W p c (V.erase m) g') *
        LU_T p (V.erase m).card F (LU_cs (V.erase m) g') := by
  rw [LU_reindex _ m]
  apply Finset.sum_congr rfl
  intro g' _
  by_cases hg'm : g' m = m
  · simp only [if_pos hg'm]
    simp_rw [LU_W_update V m hm hmin g' hg'm,
      ENNReal.ofReal_mul (LU_P_nonneg p c hp V m _)]
    by_cases hW : LU_W p c (V.erase m) g' = 0
    · simp [hW]
    · obtain ⟨H1, H2⟩ := LU_W_support (V.erase m) g' hW
      rw [← LU_k_sum p hp c V m hm hmin hne F g' H1 H2, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
  · simp only [if_neg hg'm, Finset.sum_const_zero]
    have : LU_W p c (V.erase m) g' = 0 := by
      unfold LU_W
      apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero (i := m) (by simp)
      rw [if_neg hg'm]
    rw [this, ENNReal.ofReal_zero, zero_mul]

/-! ## Kernel form of the instance law -/

theorem LUI_meas_choice (M : Model) (hqm : Measurable M.q)
    (hφm : Measurable (Function.uncurry M.φ)) {n : ℕ} (i j : Fin n) :
    Measurable fun c : Fin n → ℝ => choiceProb M c i j := by
  have hφk : ∀ k : Fin n, Measurable fun c : Fin n → ℝ => M.φ (c i) (c k) := by
    intro k
    change Measurable (Function.uncurry M.φ ∘ fun c : Fin n → ℝ => (c i, c k))
    exact hφm.comp (by fun_prop)
  have hS : Measurable fun c : Fin n → ℝ => ∑ k ∈ Finset.univ.filter (· ≠ i), M.φ (c i) (c k) :=
    Finset.measurable_sum _ fun k _ => hφk k
  have hqi : Measurable fun c : Fin n → ℝ => M.q (c i) := hqm.comp (measurable_pi_apply i)
  unfold choiceProb
  refine Measurable.ite (measurableSet_eq_fun hS measurable_const) measurable_const ?_
  split_ifs
  · exact measurable_const.sub hqi
  · exact (hqi.mul (hφk j)).div hS


theorem LUI_kernel (D : Measure ℝ) (M : Model) (hqm : Measurable M.q)
    (hφm : Measurable (Function.uncurry M.φ)) (n : ℕ)
    (S : Set ((Fin n → ℝ) × DelegGraph n)) (hS : MeasurableSet S) :
    instanceLaw D M n S = ∫⁻ c, ∑ g : DelegGraph n, ({c' | (c', g) ∈ S}.indicator
      (fun c' => ENNReal.ofReal (∏ i, choiceProb M c' i (g i))) c) ∂(Measure.pi fun _ : Fin n => D) := by
  have hdens : ∀ g : DelegGraph n, Measurable fun c : Fin n → ℝ =>
      ENNReal.ofReal (∏ i, choiceProb M c i (g i)) := by
    intro g
    exact ENNReal.measurable_ofReal.comp
      (Finset.measurable_prod _ fun i _ => LUI_meas_choice M hqm hφm i (g i))
  have hpre : ∀ g : DelegGraph n, MeasurableSet {c' : Fin n → ℝ | (c', g) ∈ S} :=
    fun g => (by fun_prop : Measurable fun c : Fin n → ℝ => (c, g)) hS
  rw [lintegral_finsetSum _ fun g _ => (hdens g).indicator (hpre g)]
  unfold instanceLaw
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro g _
  rw [Measure.map_apply (by fun_prop : Measurable fun c : Fin n → ℝ => (c, g)) hS,
    show ((fun c : Fin n → ℝ => (c, g)) ⁻¹' S) = {c' | (c', g) ∈ S} from rfl,
    withDensity_apply _ (hpre g), lintegral_indicator (hpre g)]


theorem LUI_mset_top (A : Set (List ℕ)) : MeasurableSet A := MeasurableSpace.measurableSet_top

/-! ## Part 5: induction over the voter set -/

theorem LU_main {n : ℕ} (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (c : Fin n → ℝ) (t : ℕ) :
    ∀ V : Finset (Fin n), V.card = t + 1 → Set.InjOn c V → ∀ F : Multiset ℕ → ENNReal,
      ∑ g, ENNReal.ofReal (LU_W p c V g) * F (LU_cs V g) =
        ∫⁻ s, F (s : Multiset ℕ) ∂(urnLaw p (t + 1)) := by
  induction t with
  | zero =>
    intro V hV _ F
    obtain ⟨m, rfl⟩ := Finset.card_eq_one.mp hV
    simp only [zero_add, urnLaw]
    rw [lintegral_dirac' _ measurable_from_top]
    have hW : ∀ g : Fin n → Fin n, g ≠ id → LU_W p c {m} g = 0 := by
      intro g hg
      obtain ⟨j, hj⟩ : ∃ j, g j ≠ j := by
        by_contra h; push Not at h; exact hg (funext h)
      unfold LU_W
      by_cases hjm : j = m
      · subst hjm
        apply mul_eq_zero_of_left
        apply Finset.prod_eq_zero (Finset.mem_singleton_self j)
        unfold LU_P
        have : LU_above c {j} j = ∅ := by
          ext k; simp only [LU_above, Finset.mem_filter, Finset.mem_singleton,
            Finset.notMem_empty, iff_false, not_and]
          rintro rfl; exact lt_irrefl _
        rw [if_pos this, if_neg hj]
      · apply mul_eq_zero_of_right
        apply Finset.prod_eq_zero (i := j) (by simp [hjm])
        rw [if_neg hj]
    rw [Finset.sum_eq_single id (fun g _ hg => by rw [hW g hg, ENNReal.ofReal_zero, zero_mul])
      (by simp)]
    have hW1 : LU_W p c {m} id = 1 := by
      unfold LU_W
      have : LU_above c {m} m = ∅ := by
        ext k; simp only [LU_above, Finset.mem_filter, Finset.mem_singleton,
          Finset.notMem_empty, iff_false, not_and]
        rintro rfl; exact lt_irrefl _
      rw [Finset.prod_singleton]
      unfold LU_P
      rw [if_pos this]
      simp
    have hcs : LU_cs {m} id = {1} := by
      unfold LU_cs LU_dir LU_size
      have h1 : ({m} : Finset (Fin n)).filter (fun i => id i = i) = {m} := by
        ext; simp
      rw [h1]
      have h2 : ({m} : Finset (Fin n)).filter (fun j => root id j = m) = {m} := by
        ext j; simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · exact fun h => h.1
        · rintro rfl; exact ⟨rfl, by unfold root; simp⟩
      simp [h2]
    rw [hW1, hcs, ENNReal.ofReal_one, one_mul]
    rfl
  | succ t ih =>
    intro V hV hinj F
    have hVne : V.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨m, hm, hmle⟩ := Finset.exists_min_image V c hVne
    have hmin : ∀ k ∈ V, k ≠ m → c m < c k := by
      intro k hk hkm
      exact lt_of_le_of_ne (hmle k hk) (fun h => hkm (hinj hk hm h.symm))
    have hcard : (V.erase m).card = t + 1 := by rw [Finset.card_erase_of_mem hm, hV]; rfl
    have hne : (V.erase m).Nonempty := Finset.card_pos.mp (by omega)
    rw [LU_graph_step p hp c V m hm hmin hne F, hcard,
      ih (V.erase m) hcard (hinj.mono (Finset.erase_subset m V)) (LU_T p (t + 1) F),
      LU_urn_succ p (t + 1) (by omega) F]

/-! ## Part 6: back to the instance law -/

theorem LU_choice_eq {n : ℕ} (p : ℝ) (c : Fin n → ℝ) (i j : Fin n) :
    choiceProb (upward p) c i j = LU_P p c Finset.univ i j := by
  have hS : (∑ k ∈ Finset.univ.filter (· ≠ i), (upward p).φ (c i) (c k)) =
      ((LU_above c Finset.univ i).card : ℝ) := by
    simp only [upward]
    rw [Finset.sum_boole, Finset.filter_filter]
    congr 2
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, LU_above]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨fun hki => by rw [hki] at h; exact lt_irrefl _ h, h⟩
  unfold choiceProb LU_P
  rw [hS]
  by_cases ha : LU_above c Finset.univ i = ∅
  · rw [if_pos ha, ha]; simp
  · rw [if_neg ha, if_neg (by
      rw [Nat.cast_eq_zero, Finset.card_eq_zero]; exact ha)]
    by_cases hji : j = i
    · rw [if_pos hji, if_pos hji]; rfl
    · rw [if_neg hji, if_neg hji]
      simp only [upward, LU_above, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> simp

theorem LU_W_univ {n : ℕ} (p : ℝ) (c : Fin n → ℝ) (g : Fin n → Fin n) :
    LU_W p c Finset.univ g = ∏ i, choiceProb (upward p) c i (g i) := by
  unfold LU_W
  rw [Finset.compl_univ, Finset.prod_empty, mul_one]
  exact Finset.prod_congr rfl fun i _ => (LU_choice_eq p c i (g i)).symm

theorem LU_cs_univ {n : ℕ} (g : Fin n → Fin n) : LU_cs Finset.univ g = compSizes g := by
  unfold LU_cs compSizes LU_dir
  apply Multiset.map_congr rfl
  intro i hi
  have hgi : g i = i := (Finset.mem_filter.mp (Finset.mem_val.mp hi)).2
  unfold LU_size weight
  rw [if_pos hgi]

theorem LU_diag_null (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D] {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) : (Measure.pi fun _ : Fin n => D) {c | c i = c j} = 0 := by
  set φ : (Fin n → ℝ) → ℝ × ℝ := fun c => (c i, c j) with hφ
  have hφm : Measurable φ := by fun_prop
  have hmap : (Measure.pi fun _ : Fin n => D).map φ = D.prod D := by
    refine (Measure.prod_eq ?_).symm
    intro s t hs ht
    rw [Measure.map_apply hφm (hs.prod ht)]
    have hpre : φ ⁻¹' (s ×ˢ t) =
        Set.pi Set.univ (fun l => if l = i then s else if l = j then t else Set.univ) := by
      ext c
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_imp_iff, hφ]
      constructor
      · rintro ⟨h1, h2⟩ l
        split_ifs with h3 h4
        · subst h3; exact h1
        · subst h4; exact h2
        · trivial
      · intro h
        refine ⟨?_, ?_⟩
        · have := h i; rwa [if_pos rfl] at this
        · have := h j; rwa [if_neg (Ne.symm hij), if_pos rfl] at this
    rw [hpre, Measure.pi_pi]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl,
      ← Finset.mul_prod_erase (Finset.univ.erase i) _
        (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩),
      if_neg (Ne.symm hij), if_pos rfl]
    rw [Finset.prod_eq_one]
    · ring
    · intro l hl
      have hlj := Finset.ne_of_mem_erase hl
      have hli := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl)
      rw [if_neg hli, if_neg hlj, measure_univ]
  have hdiag : {c : Fin n → ℝ | c i = c j} = φ ⁻¹' {x | x.1 = x.2} := by
    ext c; simp [hφ]
  have hdm : MeasurableSet {x : ℝ × ℝ | x.1 = x.2} := measurableSet_eq_fun measurable_fst measurable_snd
  rw [hdiag, ← Measure.map_apply hφm hdm, hmap, Measure.prod_apply hdm]
  have : ∀ x : ℝ, D (Prod.mk x ⁻¹' {x : ℝ × ℝ | x.1 = x.2}) = 0 := by
    intro x
    have : Prod.mk x ⁻¹' {x : ℝ × ℝ | x.1 = x.2} = {x} := by
      ext y; simp [eq_comm]
    rw [this, measure_singleton]
  simp [this]

theorem LU_inj_ae (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D] (n : ℕ) :
    ∀ᵐ c ∂(Measure.pi fun _ : Fin n => D), Function.Injective c := by
  rw [ae_iff]
  have : {c : Fin n → ℝ | ¬ Function.Injective c} ⊆
      ⋃ i : Fin n, ⋃ j : Fin n, (if i = j then ∅ else {c | c i = c j}) := by
    intro c hc
    simp only [Function.Injective, not_forall] at hc
    obtain ⟨i, j, hcij, hij⟩ := hc
    simp only [Set.mem_iUnion]
    exact ⟨i, j, by rw [if_neg hij]; exact hcij⟩
  apply measure_mono_null this
  rw [measure_iUnion_null_iff]
  intro i
  rw [measure_iUnion_null_iff]
  intro j
  split_ifs with hij
  · exact measure_empty
  · exact LU_diag_null D i j hij

theorem LU_maxWeight_iff {n : ℕ} (g : DelegGraph n) (x : ℕ) :
    maxWeight g ≤ x ↔ ∀ y ∈ compSizes g, y ≤ x := by
  unfold maxWeight compSizes
  rw [Finset.sup_le_iff]
  constructor
  · intro h y hy
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hy
    exact h i (Finset.mem_univ i)
  · intro h i _
    by_cases hgi : g i = i
    · exact h _ (Multiset.mem_map.mpr ⟨i, Finset.mem_val.mpr (by simp [hgi]), rfl⟩)
    · unfold weight; rw [if_neg hgi]; exact Nat.zero_le _

theorem LU_maxBin_iff (s : List ℕ) (x : ℕ) :
    maxBin s ≤ x ↔ ∀ y ∈ (s : Multiset ℕ), y ≤ x := by
  induction s with
  | nil => simp [maxBin]
  | cons a l ih =>
    have h : maxBin (a :: l) = max a (maxBin l) := rfl
    rw [h, max_le_iff, ih]
    simp [Multiset.mem_coe]

theorem solution (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (D : Measure ℝ) (hD : D ∈ ContClass)
    (n : ℕ) (hn : 1 ≤ n) :
    (∀ S : Set (Multiset ℕ), (instanceLaw D (upward p) n).real {ω | compSizes ω.2 ∈ S} =
        (urnLaw p n).real {s | (s : Multiset ℕ) ∈ S}) ∧
      ∀ x : ℕ, (instanceLaw D (upward p) n).real {ω | maxWeight ω.2 ≤ x} =
        (urnLaw p n).real {s | maxBin s ≤ x} := by
  obtain ⟨hP, hS, hN⟩ := hD
  have hpI : p ∈ Set.Icc (0 : ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
  have hqm : Measurable (upward p).q := measurable_const
  have hφm : Measurable (Function.uncurry (upward p).φ) := by
    simp only [upward]
    change Measurable fun z : ℝ × ℝ => if z.1 < z.2 then (1 : ℝ) else 0
    exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      measurable_const measurable_const
  have part1 : ∀ S : Set (Multiset ℕ), (instanceLaw D (upward p) n) {ω | compSizes ω.2 ∈ S} =
      (urnLaw p n) {s | (s : Multiset ℕ) ∈ S} := by
    intro S
    have hA : MeasurableSet {ω : (Fin n → ℝ) × DelegGraph n | compSizes ω.2 ∈ S} :=
      measurable_snd (MeasurableSet.of_discrete (s := {g : DelegGraph n | compSizes g ∈ S}))
    rw [LUI_kernel D (upward p) hqm hφm n _ hA]
    set F : Multiset ℕ → ENNReal := S.indicator 1 with hF
    have hpt : ∀ᵐ c ∂(Measure.pi fun _ : Fin n => D),
        ∑ g : DelegGraph n, ({c' | (c', g) ∈ {ω : (Fin n → ℝ) × DelegGraph n |
          compSizes ω.2 ∈ S}}.indicator
          (fun c' => ENNReal.ofReal (∏ i, choiceProb (upward p) c' i (g i))) c) =
        ∫⁻ s, F (s : Multiset ℕ) ∂(urnLaw p n) := by
      filter_upwards [LU_inj_ae D n] with c hc
      have hterm : ∀ g : DelegGraph n, ({c' : Fin n → ℝ | compSizes g ∈ S}.indicator
          (fun c' => ENNReal.ofReal (∏ i, choiceProb (upward p) c' i (g i))) c) =
          ENNReal.ofReal (LU_W p c Finset.univ g) * F (LU_cs Finset.univ g) := by
        intro g
        rw [LU_W_univ, LU_cs_univ, hF]
        by_cases hg : compSizes g ∈ S
        · rw [Set.indicator_of_mem (show c ∈ {c' : Fin n → ℝ | compSizes g ∈ S} from hg),
            Set.indicator_of_mem hg, Pi.one_apply, mul_one]
        · rw [Set.indicator_of_notMem (show c ∉ {c' : Fin n → ℝ | compSizes g ∈ S} from hg),
            Set.indicator_of_notMem hg, mul_zero]
      rw [Finset.sum_congr rfl (fun g _ => hterm g)]
      obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
      exact LU_main p hpI c t Finset.univ (by simp) (hc.injOn) F
    rw [lintegral_congr_ae hpt, lintegral_const, measure_univ, mul_one]
    rw [← lintegral_indicator_one (LUI_mset_top _)]
    rfl
  refine ⟨fun S => by rw [measureReal_def, measureReal_def, part1], fun x => ?_⟩
  have h1 : {ω : (Fin n → ℝ) × DelegGraph n | maxWeight ω.2 ≤ x} =
      {ω | compSizes ω.2 ∈ {m : Multiset ℕ | ∀ y ∈ m, y ≤ x}} := by
    ext ω; simp only [Set.mem_setOf_eq]; exact LU_maxWeight_iff ω.2 x
  have h2 : {s : List ℕ | maxBin s ≤ x} =
      {s : List ℕ | ((s : List ℕ) : Multiset ℕ) ∈ {m : Multiset ℕ | ∀ y ∈ m, y ≤ x}} := by
    ext s; simp only [Set.mem_setOf_eq]; exact LU_maxBin_iff s x
  rw [h1, h2, measureReal_def, measureReal_def, part1]
