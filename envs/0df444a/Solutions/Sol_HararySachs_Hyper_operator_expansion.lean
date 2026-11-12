-- Prove2me | solution 1 for HararySachs.Hyper.operator_expansion
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-12T05:02:20.350776+00:00
-- url     : https://prove2.me/submissions/2163eaf7-51db-4cf9-8168-73e385032836

import Mathlib
import Definitions.Def_HararySachs_Hyper_Operators
import Definitions.Def_HararySachs_Hyper_Veblen

open HararySachs.Hyper MvPolynomial Finset

set_option linter.unusedSectionVars false

namespace OpExpAux

variable {n : ℕ}

/-- apply the partial derivatives of a list of variables -/
noncomputable def opL (l : List (Fin n × Fin n)) (p : AuxPoly n) : AuxPoly n :=
  l.foldr (fun a q => pderiv a q) p

lemma pderiv_comm (a b : Fin n × Fin n) (p : AuxPoly n) :
    pderiv a (pderiv b p) = pderiv b (pderiv a p) := by
  ext s
  rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_pderiv]
  by_cases hab : a = b
  · subst hab; rfl
  · have h1 : (s + Finsupp.single a 1 : (Fin n × Fin n) →₀ ℕ) b = s b := by
      simp [hab]
    have h2 : (s + Finsupp.single b 1 : (Fin n × Fin n) →₀ ℕ) a = s a := by
      simp [Ne.symm hab]
    rw [h1, h2, add_right_comm s]
    ring

lemma opL_perm {l l' : List (Fin n × Fin n)} (h : l.Perm l') (p : AuxPoly n) :
    opL l p = opL l' p :=
  h.foldr_eq' (fun x _ y _ z => pderiv_comm y x z) p

lemma opL_append (l l' : List (Fin n × Fin n)) (p : AuxPoly n) :
    opL (l ++ l') p = opL l (opL l' p) := by
  simp [opL, List.foldr_append]

lemma opL_sum {ι : Type*} (s : Finset ι) (l : List (Fin n × Fin n)) (f : ι → AuxPoly n) :
    opL l (∑ i ∈ s, f i) = ∑ i ∈ s, opL l (f i) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [opL, List.foldr_cons] at ih ⊢; rw [ih, map_sum]

lemma opL_smul (l : List (Fin n × Fin n)) (c : ℚ) (p : AuxPoly n) :
    opL l (c • p) = c • opL l p := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [opL, List.foldr_cons] at ih ⊢; rw [ih, Derivation.map_smul]

lemma iterate_eq_opL (a : Fin n × Fin n) (c : ℕ) (p : AuxPoly n) :
    (pderiv a)^[c] p = opL (List.replicate c a) p := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [Function.iterate_succ_apply', ih, List.replicate_succ]
    rfl

lemma diffMonomial_eq_opL (m : ArcMult n) (p : AuxPoly n) :
    diffMonomial m p = opL ((Finset.univ : Finset (Fin n × Fin n)).toList.reverse.flatMap
      (fun a => List.replicate (m a.1 a.2) a)) p := by
  unfold diffMonomial
  generalize (Finset.univ : Finset (Fin n × Fin n)).toList = L
  induction L generalizing p with
  | nil => rfl
  | cons a L ih =>
    rw [List.foldl_cons, ih, iterate_eq_opL, List.reverse_cons, List.flatMap_append,
      opL_append]
    simp

/-- any list with the right arc counts realises `diffMonomial` -/
lemma opL_eq_diffMonomial (l : List (Fin n × Fin n)) (m : ArcMult n)
    (h : ∀ x : Fin n × Fin n, l.count x = m x.1 x.2) (p : AuxPoly n) :
    opL l p = diffMonomial m p := by
  rw [diffMonomial_eq_opL]
  apply opL_perm
  rw [List.perm_iff_count]
  intro x
  rw [h, List.count_flatMap, List.map_reverse, List.sum_reverse]
  simp only [Function.comp_def, List.count_replicate]
  rw [Finset.sum_map_toList]
  simp

variable {k : ℕ}

lemma fhat_eq (E : Finset (Finset (Fin n))) (i : Fin n) (p : AuxPoly n) :
    fhat (k := k) E i p = ∑ t : Fin (k - 1) → Fin n,
      adjEntry E (Fin.cons i t : Fin (k - 1 + 1) → Fin n) •
        opL ((List.ofFn t).map (fun j => (i, j))) p := by
  unfold fhat opL
  refine sum_congr rfl fun t _ => ?_
  rw [List.foldr_map]

/-- arcs produced by a family of tuples rooted along `ρ` -/
def arcL {d : ℕ} (ρ : Fin d → Fin n) (τ : Fin d → Fin (k - 1) → Fin n) :
    List (Fin n × Fin n) :=
  (List.ofFn (fun x => (List.ofFn (τ x)).map (fun j => (ρ x, j)))).flatten

/-- weight of a family of tuples -/
noncomputable def wt (E : Finset (Finset (Fin n))) {d : ℕ} (ρ : Fin d → Fin n)
    (τ : Fin d → Fin (k - 1) → Fin n) : ℚ :=
  ∏ x, adjEntry E (Fin.cons (ρ x) (τ x) : Fin (k - 1 + 1) → Fin n)

lemma expand (E : Finset (Finset (Fin n))) : ∀ (d : ℕ) (ρ : Fin d → Fin n) (P : AuxPoly n),
    (List.ofFn ρ).foldl (fun q i => fhat (k := k) E i q) P =
      ∑ τ : Fin d → Fin (k - 1) → Fin n, wt E ρ τ • opL (arcL ρ τ) P := by
  intro d
  induction d with
  | zero =>
    intro ρ P
    simp [wt, arcL, opL]
  | succ d ih =>
    intro ρ P
    rw [List.ofFn_succ, List.foldl_cons, ih, fhat_eq]
    rw [← (Fin.consEquiv (fun _ => Fin (k - 1) → Fin n)).sum_comp, Fintype.sum_prod_type,
      sum_comm]
    refine sum_congr rfl fun τ _ => ?_
    rw [opL_sum, smul_sum]
    refine sum_congr rfl fun t _ => ?_
    rw [opL_smul, smul_smul]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk]
    congr 1
    · rw [wt, wt, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      ring
    · rw [← opL_append]
      apply opL_perm
      rw [arcL, arcL, List.ofFn_succ, List.flatten_cons]
      simp only [Fin.cons_zero, Fin.cons_succ]
      exact List.perm_append_comm

lemma image_cons {m : ℕ} (i : Fin n) (t : Fin m → Fin n) :
    univ.image (Fin.cons i t : Fin (m + 1) → Fin n) = insert i (univ.image t) := by
  ext v
  simp only [mem_image, mem_univ, true_and, mem_insert, Fin.exists_fin_succ, Fin.cons_zero,
    Fin.cons_succ]
  tauto

lemma tuple_props (hk : 2 ≤ k) {e : Finset (Fin n)} (he : e.card = k) {i : Fin n}
    {t : Fin (k - 1) → Fin n} (h : univ.image (Fin.cons i t : Fin (k - 1 + 1) → Fin n) = e) :
    Function.Injective t ∧ univ.image t = e.erase i ∧ i ∈ e := by
  rw [image_cons] at h
  have hi : i ∈ e := h ▸ mem_insert_self _ _
  have hle : (univ.image t).card ≤ k - 1 := by
    have := card_image_le (s := (univ : Finset (Fin (k - 1)))) (f := t)
    simpa using this
  have hnot : i ∉ univ.image t := by
    intro hm
    rw [insert_eq_of_mem hm] at h
    rw [h] at hle; omega
  have hcard : (univ.image t).card = k - 1 := by
    have := card_insert_of_notMem hnot
    rw [h, he] at this; omega
  have himg : univ.image t = e.erase i := by
    rw [← h, erase_insert hnot]
  refine ⟨?_, himg, hi⟩
  have := card_image_iff.mp (by rw [hcard]; simp : (univ.image t).card = (univ : Finset (Fin (k - 1))).card)
  exact fun x y hxy => this (mem_coe.mpr (mem_univ x)) (mem_coe.mpr (mem_univ y)) hxy

lemma card_tuples (hk : 2 ≤ k) {e : Finset (Fin n)} (he : e.card = k) {i : Fin n} (hi : i ∈ e) :
    (univ.filter (fun t : Fin (k - 1) → Fin n =>
      univ.image (Fin.cons i t : Fin (k - 1 + 1) → Fin n) = e)).card = (k - 1).factorial := by
  classical
  have hce : (e.erase i).card = k - 1 := by rw [card_erase_of_mem hi, he]
  rw [← Fintype.card_subtype]
  have eqv : {t : Fin (k - 1) → Fin n //
      univ.image (Fin.cons i t : Fin (k - 1 + 1) → Fin n) = e} ≃ (Fin (k - 1) ≃ (e.erase i)) :=
    { toFun := fun t => Equiv.ofBijective (fun x => ⟨t.1 x, by
          rw [← (tuple_props hk he t.2).2.1]; simp⟩) (by
        rw [Fintype.bijective_iff_injective_and_card]
        refine ⟨fun x y hxy => (tuple_props hk he t.2).1 (congrArg Subtype.val hxy), ?_⟩
        rw [Fintype.card_fin, Fintype.card_coe, hce])
      invFun := fun f => ⟨fun x => (f x).1, by
        rw [image_cons]
        have : univ.image (fun x => (f x).1) = e.erase i := by
          ext v
          simp only [mem_image, mem_univ, true_and]
          constructor
          · rintro ⟨x, rfl⟩; exact (f x).2
          · intro hv; exact ⟨f.symm ⟨v, hv⟩, by simp⟩
        rw [this, insert_erase hi]⟩
      left_inv := fun t => by ext x; simp
      right_inv := fun f => by ext x; simp }
  rw [Fintype.card_congr eqv, Fintype.card_equiv (Fintype.equivOfCardEq (by rw [Fintype.card_fin, Fintype.card_coe, hce]))]
  simp

lemma sum_adj (hk : 2 ≤ k) (E : Finset (Finset (Fin n))) (hE : ∀ e ∈ E, e.card = k)
    (i : Fin n) (e : Finset (Fin n)) :
    (∑ t : Fin (k - 1) → Fin n,
      if univ.image (Fin.cons i t : Fin (k - 1 + 1) → Fin n) = e then
        adjEntry E (Fin.cons i t : Fin (k - 1 + 1) → Fin n) else 0) =
      if e ∈ E ∧ i ∈ e then 1 else 0 := by
  classical
  by_cases heE : e ∈ E
  · by_cases hi : i ∈ e
    · rw [if_pos ⟨heE, hi⟩]
      have h1 : ∀ t : Fin (k - 1) → Fin n,
          (if univ.image (Fin.cons i t : Fin (k - 1 + 1) → Fin n) = e then
            adjEntry E (Fin.cons i t : Fin (k - 1 + 1) → Fin n) else 0) =
          if univ.image (Fin.cons i t : Fin (k - 1 + 1) → Fin n) = e then
            1 / ((k - 1).factorial : ℚ) else 0 := by
        intro t
        split_ifs with h
        · rw [adjEntry, if_pos (h ▸ heE)]; simp
        · rfl
      rw [sum_congr rfl fun t _ => h1 t, sum_ite, sum_const_zero, add_zero, sum_const,
        card_tuples hk (hE e heE) hi, nsmul_eq_mul]
      have : ((k - 1).factorial : ℚ) ≠ 0 := by positivity
      field_simp
    · rw [if_neg (fun h => hi h.2)]
      apply sum_eq_zero
      intro t _
      rw [if_neg]
      intro h
      exact hi ((tuple_props hk (hE e heE) h).2.2)
  · rw [if_neg (fun h => heE h.1)]
    apply sum_eq_zero
    intro t _
    split_ifs with h
    · rw [adjEntry, if_neg (by rw [h]; exact heE)]
    · rfl

/-- arc multiplicities of an edge sequence `g` rooted along `ρ` -/
def arcsOf {d : ℕ} (ρ : Fin d → Fin n) (g : Fin d → Finset (Fin n)) : ArcMult n :=
  fun u v => (univ.filter (fun x => ρ x = u ∧ v ∈ g x ∧ v ≠ u)).card

lemma count_tuple {i : Fin n} {e : Finset (Fin n)} {t : Fin (k - 1) → Fin n}
    (ht : Function.Injective t ∧ univ.image t = e.erase i) (u v : Fin n) :
    ((List.ofFn t).map (fun j => (i, j))).count (u, v) =
      if i = u ∧ v ∈ e ∧ v ≠ u then 1 else 0 := by
  by_cases hiu : i = u
  · subst hiu
    rw [List.count_map_of_injective _ (fun j => (i, j)) (fun a b h => (Prod.mk.inj h).2)]
    have hmem : v ∈ List.ofFn t ↔ v ∈ e.erase i := by
      rw [List.mem_ofFn, ← ht.2]; simp
    by_cases hv : v ∈ e ∧ v ≠ i
    · rw [if_pos ⟨rfl, hv⟩]
      exact List.count_eq_one_of_mem (List.nodup_ofFn.mpr ht.1)
        (hmem.mpr (mem_erase.mpr ⟨hv.2, hv.1⟩))
    · rw [if_neg (fun h => hv h.2)]
      apply List.count_eq_zero_of_not_mem
      rw [hmem, mem_erase]; tauto
  · rw [if_neg (fun h => hiu h.1)]
    apply List.count_eq_zero_of_not_mem
    simp [hiu]

lemma opL_arcL (hk : 2 ≤ k) {d : ℕ} (ρ : Fin d → Fin n) (τ : Fin d → Fin (k - 1) → Fin n)
    (g : Fin d → Finset (Fin n)) (hg : ∀ x, (g x).card = k)
    (hτ : ∀ x, univ.image (Fin.cons (ρ x) (τ x) : Fin (k - 1 + 1) → Fin n) = g x)
    (P : AuxPoly n) : opL (arcL ρ τ) P = diffMonomial (arcsOf ρ g) P := by
  apply opL_eq_diffMonomial
  rintro ⟨u, v⟩
  rw [arcL, List.count_flatten, List.map_ofFn, List.sum_ofFn, arcsOf, card_filter]
  refine sum_congr rfl fun x _ => ?_
  have := tuple_props hk (hg x) (hτ x)
  exact count_tuple ⟨this.1, this.2.1⟩ u v

lemma lhs_regroup (hk : 2 ≤ k) (E : Finset (Finset (Fin n))) (hE : ∀ e ∈ E, e.card = k)
    {d : ℕ} (ρ : Fin d → Fin n) (P : AuxPoly n) :
    ∑ τ : Fin d → Fin (k - 1) → Fin n, wt E ρ τ • opL (arcL ρ τ) P =
      ∑ g : Fin d → Finset (Fin n),
        if ∀ x, g x ∈ E ∧ ρ x ∈ g x then diffMonomial (arcsOf ρ g) P else 0 := by
  classical
  set G : (Fin d → Fin (k - 1) → Fin n) → Fin d → Finset (Fin n) :=
    fun τ x => univ.image (Fin.cons (ρ x) (τ x) : Fin (k - 1 + 1) → Fin n) with hG
  have h1 : ∀ τ, wt E ρ τ • opL (arcL ρ τ) P =
      wt E ρ τ • diffMonomial (arcsOf ρ (G τ)) P := by
    intro τ
    by_cases hw : wt E ρ τ = 0
    · rw [hw, zero_smul, zero_smul]
    · congr 1
      apply opL_arcL hk ρ τ (G τ) _ (fun x => rfl)
      intro x
      apply hE
      have := prod_ne_zero_iff.mp hw x (mem_univ _)
      unfold adjEntry at this
      by_contra hn
      exact this (if_neg hn)
  rw [sum_congr rfl fun τ _ => h1 τ, ← sum_fiberwise univ G]
  refine sum_congr rfl fun g _ => ?_
  rw [sum_congr rfl fun τ hτ => by rw [(mem_filter.mp hτ).2], ← sum_smul]
  have h2 : (∑ τ ∈ univ.filter (fun τ => G τ = g), wt E ρ τ) =
      if ∀ x, g x ∈ E ∧ ρ x ∈ g x then 1 else 0 := by
    rw [sum_filter]
    have h3 : ∀ τ : Fin d → Fin (k - 1) → Fin n, (if G τ = g then wt E ρ τ else 0) =
        ∏ x, (if univ.image (Fin.cons (ρ x) (τ x) : Fin (k - 1 + 1) → Fin n) = g x then
          adjEntry E (Fin.cons (ρ x) (τ x) : Fin (k - 1 + 1) → Fin n) else 0) := by
      intro τ
      rw [prod_ite_zero, wt]
      congr 1
      simp only [mem_univ, true_implies, hG]
      exact propext ⟨fun h x => congrFun h x, fun h => funext h⟩
    rw [sum_congr rfl fun τ _ => h3 τ]
    rw [← Fintype.prod_sum (fun x (t : Fin (k - 1) → Fin n) =>
      if univ.image (Fin.cons (ρ x) t : Fin (k - 1 + 1) → Fin n) = g x then
        adjEntry E (Fin.cons (ρ x) t : Fin (k - 1 + 1) → Fin n) else 0)]
    rw [prod_congr rfl fun x _ => sum_adj hk E hE (ρ x) (g x), prod_boole]
    simp
  rw [h2]
  split_ifs <;> simp

lemma card_eq_count {α : Type*} [DecidableEq α] : ∀ {m : ℕ} (f : Fin m → α) (v : α),
    (univ.filter (fun x => f x = v)).card = (List.ofFn f).count v := by
  intro m
  induction m with
  | zero => intro f v; simp
  | succ m ih =>
    intro f v
    rw [card_filter, Fin.sum_univ_succ, ← card_filter, ih, List.ofFn_succ, List.count_cons]
    simp only [beq_iff_eq]
    split_ifs <;> omega

/-- the down-set `{x | f x < v}` of a monotone map is an initial segment -/
lemma mono_lt_iff {m : ℕ} {f : Fin m → Fin n} (hf : Monotone f) (v : Fin n) (x : Fin m) :
    f x < v ↔ x.val < (univ.filter (fun y => f y < v)).card := by
  constructor
  · intro hx
    have hsub : Iic x ⊆ univ.filter (fun y => f y < v) := by
      intro y hy
      simp only [mem_filter, mem_univ, true_and]
      exact lt_of_le_of_lt (hf (mem_Iic.mp hy)) hx
    have := card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hx
    by_contra hn
    push Not at hn
    have hsub : univ.filter (fun y => f y < v) ⊆ Iio x := by
      intro y hy
      simp only [mem_filter, mem_univ, true_and] at hy
      rw [mem_Iio]
      by_contra hy'
      push Not at hy'
      exact absurd (lt_of_le_of_lt (hf hy') hy) (not_lt.mpr hn)
    have := card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

lemma mono_unique {m : ℕ} {f g : Fin m → Fin n} (hf : Monotone f) (hg : Monotone g)
    (h : ∀ v, (univ.filter (fun x => f x = v)).card = (univ.filter (fun x => g x = v)).card) :
    f = g := by
  have hlt : ∀ v, (univ.filter (fun y => f y < v)).card = (univ.filter (fun y => g y < v)).card := by
    intro v
    rw [card_eq_sum_card_fiberwise (f := f) (t := univ.filter (· < v)) (by intro y hy; simpa using hy),
      card_eq_sum_card_fiberwise (f := g) (t := univ.filter (· < v)) (by intro y hy; simpa using hy)]
    refine sum_congr rfl fun u hu => ?_
    simp only [mem_filter, mem_univ, true_and] at hu
    rw [filter_filter, filter_filter]
    have e1 : univ.filter (fun y => f y < v ∧ f y = u) = univ.filter (fun y => f y = u) := by
      ext y; simp only [mem_filter, mem_univ, true_and]; constructor
      · exact fun h => h.2
      · intro h; exact ⟨h ▸ hu, h⟩
    have e2 : univ.filter (fun y => g y < v ∧ g y = u) = univ.filter (fun y => g y = u) := by
      ext y; simp only [mem_filter, mem_univ, true_and]; constructor
      · exact fun h => h.2
      · intro h; exact ⟨h ▸ hu, h⟩
    rw [e1, e2, h]
  funext x
  have key : ∀ v, f x < v ↔ g x < v := fun v => by
    rw [mono_lt_iff hf, mono_lt_iff hg, hlt]
  rcases lt_trichotomy (f x) (g x) with h1 | h1 | h1
  · exact absurd ((key (g x)).mp h1) (lt_irrefl _)
  · exact h1
  · exact absurd ((key (f x)).mpr h1) (lt_irrefl _)

lemma sum_cast {β : Type*} [AddCommMonoid β] {X : Type*} [Fintype X] [DecidableEq X]
    {m m' : ℕ} (h : m = m') (H : ∀ j, (Fin j → X) → β) :
    ∑ R : Fin m → X, H m R = ∑ R : Fin m' → X, H m' R := by
  subst h; rfl

/-- arc multiplicities of a rooted edge sequence of any length -/
def rArcs {m : ℕ} (R : Fin m → Fin n × Finset (Fin n)) : ArcMult n :=
  fun u v => (Finset.univ.filter (fun i => (R i).1 = u ∧ v ∈ (R i).2 ∧ v ≠ u)).card

lemma mem_allMultisets {d : ℕ} (E : Finset (Finset (Fin n))) (g : Fin d → Finset (Fin n)) :
    ((List.ofFn g : List (Finset (Fin n))) : Multiset (Finset (Fin n))) ∈ allMultisets E d ↔
      ∀ x, g x ∈ E := by
  unfold allMultisets
  rw [mem_image]
  constructor
  · rintro ⟨f, _, hf⟩ x
    have hx : g x ∈ ((List.ofFn g : List (Finset (Fin n))) : Multiset (Finset (Fin n))) := by
      rw [Multiset.mem_coe, List.mem_ofFn]; exact ⟨x, rfl⟩
    rw [← hf, Multiset.mem_coe, List.mem_ofFn] at hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy]; exact (f y).2
  · intro h
    exact ⟨fun x => ⟨g x, h x⟩, mem_univ _, rfl⟩

lemma card_of_mem_allMultisets {d : ℕ} {E : Finset (Finset (Fin n))} {S : MultiGraph n}
    (hS : S ∈ allMultisets E d) : S.card = d := by
  unfold allMultisets at hS
  obtain ⟨f, _, rfl⟩ := mem_image.mp hS
  simp

open Classical in
/-- the summand of the right-hand side, for edge sequences of any length -/
noncomputable def Hf {d : ℕ} (S : MultiGraph n) (a : Fin n → Fin (d + 1)) (P : AuxPoly n) (j : ℕ)
    (R : Fin j → Fin n × Finset (Fin n)) : AuxPoly n :=
  if (((∀ i, (R i).1 ∈ (R i).2) ∧ Monotone (fun i => (R i).1) ∧
      ((List.ofFn (fun i => (R i).2) : List (Finset (Fin n))) :
        Multiset (Finset (Fin n))) = S) ∧
      ∀ v, (Finset.univ.filter (fun i => (R i).1 = v)).card = (a v).val)
  then diffMonomial (rArcs R) P else 0

open Classical in
lemma rhs_reshape {d : ℕ} (E : Finset (Finset (Fin n))) (a : Fin n → Fin (d + 1))
    (ρ : Fin d → Fin n) (hmono : Monotone ρ)
    (hcnt : ∀ v, (univ.filter (fun x => ρ x = v)).card = (a v).val) (P : AuxPoly n) :
    (∑ S ∈ allMultisets E d,
        ∑ R : Fin S.card → Fin n × Finset (Fin n),
          if IsRooting S R ∧
              ∀ v, (Finset.univ.filter (fun i => (R i).1 = v)).card = (a v).val
          then diffMonomial (rootedArcs R) P else 0) =
      ∑ g : Fin d → Finset (Fin n),
        if ∀ x, g x ∈ E ∧ ρ x ∈ g x then diffMonomial (arcsOf ρ g) P else 0 := by
  have step1 : ∀ S ∈ allMultisets E d,
      (∑ R : Fin S.card → Fin n × Finset (Fin n),
          if IsRooting S R ∧
              ∀ v, (Finset.univ.filter (fun i => (R i).1 = v)).card = (a v).val
          then diffMonomial (rootedArcs R) P else 0) =
      ∑ R : Fin d → Fin n × Finset (Fin n),
        if (((∀ i, (R i).1 ∈ (R i).2) ∧ Monotone (fun i => (R i).1) ∧
            ((List.ofFn (fun i => (R i).2) : List (Finset (Fin n))) :
              Multiset (Finset (Fin n))) = S) ∧
            ∀ v, (Finset.univ.filter (fun i => (R i).1 = v)).card = (a v).val)
        then diffMonomial (rArcs R) P else 0 := by
    intro S hS
    calc _ = ∑ R : Fin S.card → Fin n × Finset (Fin n), Hf S a P S.card R := by
            refine sum_congr rfl fun R _ => ?_
            unfold Hf
            split_ifs with h1 h2 h2
            · rfl
            · exact absurd h1 h2
            · exact absurd h2 h1
            · rfl
      _ = ∑ R : Fin d → Fin n × Finset (Fin n), Hf S a P d R :=
            sum_cast (card_of_mem_allMultisets hS) (Hf S a P)
      _ = _ := rfl
  rw [sum_congr rfl step1, sum_comm]
  have step2 : ∀ R : Fin d → Fin n × Finset (Fin n),
      (∑ S ∈ allMultisets E d,
        if (((∀ i, (R i).1 ∈ (R i).2) ∧ Monotone (fun i => (R i).1) ∧
            ((List.ofFn (fun i => (R i).2) : List (Finset (Fin n))) :
              Multiset (Finset (Fin n))) = S) ∧
            ∀ v, (Finset.univ.filter (fun i => (R i).1 = v)).card = (a v).val)
        then diffMonomial (rArcs R) P else 0) =
      if (∀ i, (R i).2 ∈ E) ∧ (∀ i, (R i).1 ∈ (R i).2) ∧ Monotone (fun i => (R i).1) ∧
          ∀ v, (Finset.univ.filter (fun i => (R i).1 = v)).card = (a v).val
        then diffMonomial (rArcs R) P else 0 := by
    intro R
    have : ∀ S : MultiGraph n,
        (if (((∀ i, (R i).1 ∈ (R i).2) ∧ Monotone (fun i => (R i).1) ∧
            ((List.ofFn (fun i => (R i).2) : List (Finset (Fin n))) :
              Multiset (Finset (Fin n))) = S) ∧
            ∀ v, (Finset.univ.filter (fun i => (R i).1 = v)).card = (a v).val)
          then diffMonomial (rArcs R) P else 0) =
        if ((List.ofFn (fun i => (R i).2) : List (Finset (Fin n))) :
              Multiset (Finset (Fin n))) = S then
          (if (∀ i, (R i).1 ∈ (R i).2) ∧ Monotone (fun i => (R i).1) ∧
            ∀ v, (Finset.univ.filter (fun i => (R i).1 = v)).card = (a v).val
          then diffMonomial (rArcs R) P else 0) else 0 := by
      intro S
      by_cases h1 : ((List.ofFn (fun i => (R i).2) : List (Finset (Fin n))) :
              Multiset (Finset (Fin n))) = S
      · rw [if_pos h1]
        apply if_congr _ rfl rfl
        tauto
      · rw [if_neg h1, if_neg]
        tauto
    rw [sum_congr rfl fun S _ => this S, sum_ite_eq]
    by_cases h1 : ∀ i, (R i).2 ∈ E
    · rw [if_pos ((mem_allMultisets E _).mpr h1)]
      apply if_congr _ rfl rfl
      tauto
    · rw [if_neg (fun h => h1 ((mem_allMultisets E _).mp h)), if_neg]
      tauto
  rw [sum_congr rfl fun R _ => step2 R]
  rw [← (Equiv.arrowProdEquivProdArrow _ (fun _ => Fin n) (fun _ => Finset (Fin n))).symm.sum_comp,
    Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun g _ => ?_
  rw [sum_eq_single ρ]
  · simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]
    apply if_congr _ rfl rfl
    constructor
    · rintro ⟨h1, h2, _, _⟩ x; exact ⟨h1 x, h2 x⟩
    · intro h
      exact ⟨fun x => (h x).1, fun x => (h x).2, hmono, hcnt⟩
  · intro r _ hr
    simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]
    apply if_neg
    rintro ⟨_, _, hm, hc⟩
    exact hr (mono_unique hm hmono (fun v => (hc v).trans (hcnt v).symm))
  · simp

lemma foldl_replicate_fhat (E : Finset (Finset (Fin n))) (i : Fin n) (c : ℕ) (q : AuxPoly n) :
    (List.replicate c i).foldl (fun q j => fhat (k := k) E j q) q = fhatPow (k := k) E i c q := by
  induction c generalizing q with
  | zero => rfl
  | succ c ih =>
    rw [List.replicate_succ, List.foldl_cons, ih]
    unfold fhatPow
    rw [Function.iterate_succ_apply]

end OpExpAux

open OpExpAux Finset Classical in
theorem solution {n k d : ℕ} (hk : 2 ≤ k)
    (E : Finset (Finset (Fin n))) (hE : ∀ e ∈ E, e.card = k)
    (a : Fin n → Fin (d + 1)) (ha : (∑ i, (a i).val) = d) (P : AuxPoly n) :
    applyAll (k := k) E a P =
      ∑ S ∈ allMultisets E d,
        ∑ R : Fin S.card → Fin n × Finset (Fin n),
          if IsRooting S R ∧
              ∀ v, (Finset.univ.filter (fun i => (R i).1 = v)).card = (a v).val
          then diffMonomial (rootedArcs R) P else 0 := by
  set L := (List.ofFn (fun i : Fin n => List.replicate (a i).val i)).flatten with hL
  have hlen : L.length = d := by
    rw [hL, List.length_flatten, List.map_ofFn, List.sum_ofFn]
    simp [ha]
  set ρ : Fin d → Fin n := fun x => L[x.val]'(by rw [hlen]; exact x.2) with hρ
  have hofFn : List.ofFn ρ = L := List.ext_get (by simp [hlen]) (fun i h1 h2 => by simp [hρ])
  have happ : applyAll (k := k) E a P = L.foldl (fun q i => fhat (k := k) E i q) P := by
    rw [hL, List.foldl_flatten]
    unfold applyAll
    rw [show (List.ofFn (fun i : Fin n => List.replicate (a i).val i)) =
      (List.ofFn (fun i : Fin n => i)).map (fun i => List.replicate (a i).val i) by
        rw [List.map_ofFn]; rfl, List.foldl_map]
    congr 1
    funext q i
    exact (foldl_replicate_fhat E i _ q).symm
  have hpw : L.Pairwise (· ≤ ·) := by
    rw [hL, List.pairwise_flatten]
    constructor
    · intro l hl
      rw [List.mem_ofFn] at hl
      obtain ⟨i, rfl⟩ := hl
      exact List.pairwise_replicate.mpr (Or.inr le_rfl)
    · rw [List.pairwise_ofFn]
      intro i j hij x hx y hy
      rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]
      exact le_of_lt hij
  have hmono : Monotone ρ := by
    rw [← hofFn, List.pairwise_ofFn] at hpw
    intro x y hxy
    rcases eq_or_lt_of_le hxy with h | h
    · rw [h]
    · exact hpw h
  have hcnt : ∀ v, (univ.filter (fun x => ρ x = v)).card = (a v).val := by
    intro v
    rw [card_eq_count, hofFn, hL, List.count_flatten, List.map_ofFn, List.sum_ofFn]
    simp [List.count_replicate]
  rw [happ, ← hofFn, OpExpAux.expand, lhs_regroup hk E hE, rhs_reshape E a ρ hmono hcnt P]
