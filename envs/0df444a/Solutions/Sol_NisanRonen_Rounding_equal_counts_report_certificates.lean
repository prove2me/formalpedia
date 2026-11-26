-- Prove2me | solution 1 for NisanRonen.Rounding.equal_counts_report_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:00:30.391093+00:00
-- url     : https://prove2.me/submissions/19db6588-b986-4732-abae-1840ebf14b17

import Theorems.Thm_NisanRonen_Rounding_bundle_report_bound_with_reserved_machine
import Theorems.Thm_NisanRonen_Rounding_rounding_error_bound

open NisanRonen.Rounding

set_option autoImplicit false

private noncomputable def jobLoad {n k : ℕ} (δ : ℝ) (x : Fin k → Fin n)
    (d : Fin n → Fin k → ℝ) (l : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => x j = l), roundUp δ (d l j)

private noncomputable def span {n k : ℕ} [NeZero n] (δ : ℝ)
    (x : Fin k → Fin n) (d : Fin n → Fin k → ℝ) : ℝ :=
  roundedMakespan δ x (corrStar x d)

private theorem span_eq {n k : ℕ} [NeZero n] (δ : ℝ) (x : Fin k → Fin n)
    (d : Fin n → Fin k → ℝ) :
    span δ x d = Finset.univ.sup' Finset.univ_nonempty (jobLoad δ x d) := by
  unfold span roundedMakespan makespan
  congr 1
  funext l
  unfold jobLoad load
  apply Finset.sum_congr rfl
  intro j hj
  simp [corrStar, (Finset.mem_filter.1 hj).2]

private theorem load_le_span {n k : ℕ} [NeZero n] {δ : ℝ}
    (x : Fin k → Fin n) (d : Fin n → Fin k → ℝ) (l : Fin n) :
    jobLoad δ x d l ≤ span δ x d := by
  rw [span_eq]
  exact Finset.le_sup' _ (Finset.mem_univ l)

private theorem ru_ge {δ u : ℝ} (hδ : 0 < δ) : u ≤ roundUp δ u := by
  have hm := mul_le_mul_of_nonneg_left (Int.le_ceil (u / δ)) hδ.le
  rw [mul_comm δ (u / δ), div_mul_cancel₀ _ hδ.ne'] at hm
  exact hm

private theorem ru_lt {δ u : ℝ} (hδ : 0 < δ) : roundUp δ u < u + δ := by
  have hm := mul_lt_mul_of_pos_left (Int.ceil_lt_add_one (u / δ)) hδ
  rw [mul_add, mul_one, mul_comm δ (u / δ), div_mul_cancel₀ _ hδ.ne'] at hm
  exact hm

private theorem ru_mono {δ : ℝ} (hδ : 0 < δ) {u v : ℝ} (h : u ≤ v) :
    roundUp δ u ≤ roundUp δ v := by
  unfold roundUp
  exact mul_le_mul_of_nonneg_left
    (by exact_mod_cast Int.ceil_mono (div_le_div_of_nonneg_right h hδ.le)) hδ.le

private theorem ru_grid {δ : ℝ} (hδ : 0 < δ) (z : ℤ) :
    roundUp δ (δ * (z : ℝ)) = δ * (z : ℝ) := by
  simp [roundUp, mul_div_cancel_left₀ _ hδ.ne']

private theorem task_le {n k : ℕ} [NeZero n] {δ : ℝ}
    (x : Fin k → Fin n) (d : Fin n → Fin k → ℝ)
    (h : ∀ l j, 0 ≤ roundUp δ (d l j)) (j : Fin k) : roundUp δ (d (x j) j) ≤ span δ x d := by
  refine le_trans ?_ (load_le_span x d (x j))
  exact Finset.single_le_sum (f := fun l => roundUp δ (d (x j) l))
    (fun l _ => h _ l) (by simp)

private theorem pair_le {n k : ℕ} [NeZero n] {δ : ℝ}
    (x : Fin k → Fin n) (d : Fin n → Fin k → ℝ)
    (h : ∀ l j, 0 ≤ roundUp δ (d l j)) (l : Fin n) (j j' : Fin k)
    (hne : j ≠ j') (hj : x j = l) (hj' : x j' = l) :
    roundUp δ (d l j) + roundUp δ (d l j') ≤ span δ x d := by
  refine le_trans ?_ (load_le_span x d l)
  have hs : ({j, j'} : Finset (Fin k)) ⊆ Finset.univ.filter (fun u => x u = l) := by
    intro u hu
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl <;> assumption
  have hh := Finset.sum_le_sum_of_subset_of_nonneg (f := fun j => roundUp δ (d l j))
    hs (fun j _ _ => h l j)
  have hj_not : j ∉ ({j'} : Finset (Fin k)) := by simpa using hne
  rw [Finset.sum_insert hj_not, Finset.sum_singleton] at hh
  exact hh

private theorem injective_span {n k : ℕ} [NeZero n] {δ C : ℝ}
    (x : Fin k → Fin n) (hx : Function.Injective x)
    (d : Fin n → Fin k → ℝ) (hC : 0 ≤ C) (h : ∀ j, roundUp δ (d (x j) j) ≤ C) :
    span δ x d ≤ C := by
  rw [span_eq]
  apply Finset.sup'_le
  intro l _
  classical
  by_cases hl : ∃ j, x j = l
  · obtain ⟨j, hj⟩ := hl
    have hset : Finset.univ.filter (fun j => x j = l) = {j} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, ← hj]
      exact hx.eq_iff
    rw [jobLoad, hset, Finset.sum_singleton, ← hj]
    exact h j
  · push Not at hl
    simpa [jobLoad, hl] using hC

private theorem split_off_permutation {n : ℕ} (hn : 3 ≤ n) (i : Fin n)
    (x : Fin n → Fin n) (hx : Function.Injective x) (j₀ : Fin n) (hj₀ : x j₀ = i) :
    ∃ y : Fin n → Fin n, Function.Injective y ∧ y j₀ = i ∧ y ≠ x := by
  classical
  have hpair : ∃ l l' : Fin n, l ≠ i ∧ l' ≠ i ∧ l ≠ l' := by
    cases n with
    | zero => omega
    | succ n =>
      have h1 : 1 < n := by omega
      have h0 : 0 < n := by omega
      let j0 : Fin n := ⟨0, h0⟩
      let j1 : Fin n := ⟨1, h1⟩
      exact ⟨i.succAbove j0, i.succAbove j1, i.succAbove_ne _, i.succAbove_ne _,
        fun e => (by decide : (0 : ℕ) ≠ 1) (congrArg Fin.val (Fin.succAbove_right_injective e))⟩
  obtain ⟨l, l', hl, hl', hne⟩ := hpair
  let y := (Equiv.swap l l') ∘ x
  have hy := (Equiv.swap l l').injective.comp hx
  have hyj : y j₀ = i := by simp [y, hj₀, Equiv.swap_apply_of_ne_of_ne (Ne.symm hl) (Ne.symm hl')]
  refine ⟨y, hy, hyj, ?_⟩
  intro he
  obtain ⟨j, hxj⟩ := Finite.surjective_of_injective hx l
  have h := congrFun he j
  simp [y, hxj, Ne.symm hne] at h

private theorem set_probe_bound {n : ℕ} [NeZero n] {a b δ C : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hδ : 0 < δ) (hn : 3 ≤ n)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (rank : (Fin n → Fin n) → ℕ) (hinj : Function.Injective rank)
    (hpriority : ∀ v : Fin n → Fin n → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) →
      ∀ y : Fin n → Fin n, span δ y v = span δ (allocOf f δ v) v →
        rank (allocOf f δ v) ≤ rank y)
    (i : Fin n) (t r : Fin n → ℝ) (ht : ∀ j, a ≤ t j ∧ t j ≤ b)
    (hr : ∀ j, a ≤ r j ∧ r j ≤ b) (hop : DeclarationOptimal f δ a b i t r)
    (p0 : Fin n → Fin n) (hp0 : Function.Injective p0) (j₀ : Fin n) (hj₀ : p0 j₀ = i)
    (htj : roundUp δ (t j₀) ≤ C) (m : ℤ) (hm : C = δ * (m : ℝ)) :
    roundUp δ (r j₀) ≤ C + δ := by
  classical
  have hRmono : roundUp δ a ≤ C := (ru_mono hδ (ht j₀).1).trans htj
  have hC : 0 ≤ C := (ha.le.trans (ru_ge hδ)).trans hRmono
  by_contra hbad
  have hRhigh : C + δ < roundUp δ (r j₀) := lt_of_not_ge hbad
  have hG : C + δ = δ * ((m + 1 : ℤ) : ℝ) := by rw [hm]; simp [mul_add]
  have hQround : roundUp δ (C + δ) = C + δ := by rw [hG, ru_grid hδ]
  have hQa : a ≤ C + δ := by linarith [ru_ge (u := a) hδ]
  have hQb : C + δ ≤ b := by
    have hl : (m + 1 : ℤ) < ⌈r j₀ / δ⌉ := by
      rw [hG] at hRhigh
      exact_mod_cast (lt_of_mul_lt_mul_left hRhigh hδ.le)
    have hfine : C + δ + δ ≤ roundUp δ (r j₀) := by
      have hh : ((m + 1 + 1 : ℤ) : ℝ) ≤ (⌈r j₀ / δ⌉ : ℤ) := by
        exact_mod_cast Int.add_one_le_of_lt hl
      rw [hG]
      simpa [roundUp, mul_add] using mul_le_mul_of_nonneg_left hh hδ.le
    linarith [ru_lt (u := r j₀) hδ, (hr j₀).2]
  let probe (p : Fin n → Fin n) (q : ℝ) (l j : Fin n) :=
    if l = i then r j else if p j = l then a else q
  have hb (p : Fin n → Fin n) (q : ℝ) (hqa : a ≤ q) (hqb : q ≤ b) (l j : Fin n) :
      a ≤ probe p q l j ∧ probe p q l j ≤ b := by
    by_cases hl : l = i <;> by_cases hj : p j = l <;> simp [probe, hl, hj, hr, hab, hqa, hqb]
  have hprobe_i (p : Fin n → Fin n) (q : ℝ) : probe p q i = r := by funext j; simp [probe]
  have hpositive (u : ℝ) (hu : a ≤ u) : 0 < roundUp δ u :=
    (ha.trans_le hu).trans_le (ru_ge hδ)
  have fixedTrue (p : Fin n → Fin n) (q : ℝ)
      (hp : Function.Injective p) (hpi : p j₀ = i) :
      span δ p (Function.update (probe p q) i t) ≤ C := by
    apply injective_span p hp _ hC
    intro j
    by_cases h : p j = i
    · have hj : j = j₀ := hp (h.trans hpi.symm)
      subst j
      simpa [hpi] using htj
    · simpa [Function.update_of_ne h, probe, h] using hRmono
  have forced (p : Fin n → Fin n) (q : ℝ) (hq : C < roundUp δ q)
      (hqa : a ≤ q) (hqb : q ≤ b) (hp : Function.Injective p) (hpi : p j₀ = i) :
      ∀ j, (allocOf f δ (probe p q)) j = i ∨ (allocOf f δ (probe p q)) j = p j := by
    intro j
    let x := allocOf f δ (probe p q)
    change x j = i ∨ x j = p j
    by_cases hxi : x j = i
    · exact Or.inl hxi
    right
    by_contra hne
    let v' := Function.update (probe p q) i t
    have hlower (l j : Fin n) : a ≤ v' l j := by
      by_cases hl : l = i
      · simpa [v', hl] using (ht j).1
      · simpa [v', Function.update_of_ne hl] using (hb p q hqa hqb l j).1
    have hlarge := task_le x v' (fun l j => (hpositive _ (hlower l j)).le) j
    have hjval : v' (x j) j = q := by
      simp [v', probe, hxi, Ne.symm hne]
    rw [hjval] at hlarge
    have hopt : span δ x v' ≤ C := (hop (probe p q) (hb p q hqa hqb) (hprobe_i p q) p).trans
      (fixedTrue p q hp hpi)
    exact (hq.trans_le (hlarge.trans hopt)).false
  by_cases hsmall : ∃ u, roundUp δ (r u) ≤ C + δ
  · obtain ⟨u, hu⟩ := hsmall
    let q := C + δ
    let v := probe p0 q
    let z := (Equiv.swap i (p0 u)) ∘ p0
    have hz : Function.Injective z := (Equiv.swap i (p0 u)).injective.comp hp0
    have hzu : z u = i := by simp [z]
    have hbound : span δ z v ≤ q := by
      apply injective_span z hz v (C := q) (by linarith)
      intro j
      by_cases h : z j = i
      · have he : j = u := hz (h.trans hzu.symm)
        subst j
        simpa [hzu, v, probe, q] using hu
      · by_cases hh : p0 j = z j
        · simpa [v, probe, h, hh, q] using (hRmono.trans (by linarith) : roundUp δ a ≤ C + δ)
        · simp [v, probe, h, hh, q, hQround]
    let x := allocOf f δ v
    have hx : span δ x v ≤ q := ((hf n v (hb p0 q hQa hQb)).2 z).trans hbound
    have hxj : x j₀ = i := by
      rcases forced p0 q (by simpa [q, hQround] using lt_add_of_pos_right C hδ)
        hQa hQb hp0 hj₀ j₀ with h | h
      · exact h
      · exact h.trans hj₀
    have hdanger := task_le x v (fun l j => (hpositive _ (hb p0 q hQa hQb l j).1).le) j₀
    change x j₀ = i at hxj
    have hh : v (x j₀) j₀ = r j₀ := by simp [v, probe, hxj]
    rw [hh] at hdanger
    exact (hRhigh.trans_le (hdanger.trans hx)).false
  · push Not at hsmall
    let A := roundUp δ a
    obtain ⟨jmin, _, hmmin⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun j : Fin n => roundUp δ (r j))
    let q := r jmin
    let D := roundUp δ q
    have hD (j : Fin n) : D ≤ roundUp δ (r j) := by
      dsimp only [D, q]
      rw [← hmmin]
      exact Finset.inf'_le _ (Finset.mem_univ j)
    have hDc : C < D := (lt_add_of_pos_right _ hδ).trans (hsmall jmin)
    have hDa : A ≤ D := (hRmono.trans hDc.le)
    have hDpos : 0 < D := hpositive _ (hr jmin).1
    have core (p : Fin n → Fin n) (hp : Function.Injective p) (hpi : p j₀ = i) :
        ∀ y : Fin n → Fin n, Function.Injective y → y j₀ = i → rank p ≤ rank y := by
      let v := probe p q
      have hv := hb p q (hr jmin).1 (hr jmin).2
      let z := (Equiv.swap i (p jmin)) ∘ p
      have hz := (Equiv.swap i (p jmin)).injective.comp hp
      have hzj : z jmin = i := by simp [z]
      have hbound : span δ z v ≤ D := by
        apply injective_span z hz v hDpos.le
        intro j
        by_cases h : z j = i
        · have hj : j = jmin := hz (h.trans hzj.symm)
          subst j
          simp [v, probe, hzj, D, q]
        · by_cases h' : p j = z j
          · simpa [v, probe, h, h', A] using hDa
          · simp [v, probe, h, h', D]
      let x := allocOf f δ v
      have hxcap : span δ x v ≤ D := ((hf n v hv).2 z).trans hbound
      have hposv (l j : Fin n) := hpositive _ (hv l j).1
      have hInject : Function.Injective x := by
        intro j j' he
        by_contra hne
        have hh := (pair_le x v (fun l j => (hposv l j).le) (x j) j j' hne rfl he.symm).trans hxcap
        by_cases hi : x j = i
        · have ht0 : D ≤ roundUp δ (v (x j) j) := by simpa [v, probe, hi] using hD j
          linarith [hposv (x j) j']
        · by_cases h0 : p j = x j
          · have h1 : p j' ≠ x j := fun hh => hne (hp (h0.trans hh.symm))
            have ht1 : roundUp δ (v (x j) j') = D := by simp [v, probe, hi, h1, D]
            rw [ht1] at hh
            linarith [hposv (x j) j]
          · have ht0 : roundUp δ (v (x j) j) = D := by simp [v, probe, hi, h0, D]
            rw [ht0] at hh
            linarith [hposv (x j) j']
      have hxval : span δ x v = D := by
        obtain ⟨j, hj⟩ := Finite.surjective_of_injective hInject i
        have ht0 : D ≤ roundUp δ (v (x j) j) := by simpa [v, probe, hj] using hD j
        exact le_antisymm hxcap (ht0.trans (task_le x v (fun l j => (hposv l j).le) j))
      have hbforce := forced p q hDc (hr jmin).1 (hr jmin).2 hp hpi
      have hxf : x = p := by
        have hjx : x j₀ = i := by
          rcases hbforce j₀ with hp' | hp'
          · exact hp'
          · exact hp'.trans hpi
        funext j
        rcases hbforce j with h | h
        · have hj : j = j₀ := hInject (h.trans hjx.symm)
          subst j
          exact h.trans hpi.symm
        · exact h
      have hdj : roundUp δ (r j₀) ≤ D := by
        have hh := (task_le x v (fun l j => (hposv l j).le) j₀).trans hxcap
        have hj : x j₀ = i := by rw [hxf, hpi]
        simpa [v, probe, hj] using hh
      intro y hy hyi
      have hyv : span δ y v ≤ D := by
        apply injective_span y hy v hDpos.le
        intro j
        by_cases hi : y j = i
        · have hj : j = j₀ := hy (hi.trans hyi.symm)
          subst j
          simpa [v, probe, hyi] using hdj
        · by_cases hh : p j = y j
          · simpa [v, probe, hi, hh, A] using hDa
          · simp [v, probe, hi, hh, D]
      have hval : span δ y v = span δ x v :=
        le_antisymm (hyv.trans_eq hxval.symm) ((hf n v hv).2 y)
      have hh := hpriority v hv y hval
      change rank x ≤ rank y at hh
      rwa [hxf] at hh
    obtain ⟨p1, hp1, hp1i, hpne⟩ := split_off_permutation hn i p0 hp0 j₀ hj₀
    exact hpne (hinj (le_antisymm (core p1 hp1 hp1i p0 hp0 hj₀) (core p0 hp0 hj₀ p1 hp1 hp1i)))

private theorem two_per_machine {n : ℕ} (hn : 3 ≤ n) (i : Fin n)
    (S : Finset (Fin n)) (hS : S.Nonempty) {A : ℝ} (hA : 0 ≤ A) :
    ∃ spare : Fin n, spare ≠ i ∧ ∃ bg : Fin n → Fin n,
      (∀ j, j ∉ S → bg j ≠ i ∧ bg j ≠ spare) ∧
      ∀ l : Fin n, (∑ _j ∈ Finset.univ.filter (fun j => j ∉ S ∧ bg j = l), A) ≤ 2 * A := by
  classical
  obtain _ | n := n
  · omega
  obtain _ | m := n
  · omega
  have hm : 0 < m := by omega
  let spare := i.succAbove (0 : Fin (m + 1))
  let group (l : Fin m) := i.succAbove l.succ
  have hg : Function.Injective group := fun _ _ h =>
    Fin.succ_injective _ (Fin.succAbove_right_injective h)
  have hgi (l : Fin m) : group l ≠ i := i.succAbove_ne _
  have hgs (l : Fin m) : group l ≠ spare := fun h =>
    Fin.succ_ne_zero _ (Fin.succAbove_right_injective h)
  have hc : Fintype.card {j : Fin (m + 2) // j ∉ S} ≤ Fintype.card (Fin m × Fin 2) := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, Fintype.card_fin]
    have hs := Finset.card_pos.mpr hS
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_iff_card_le.mpr hc
  let bg (j : Fin (m + 2)) := if h : j ∉ S then group (e ⟨j, h⟩).1 else i
  refine ⟨spare, i.succAbove_ne _, bg, ?_, ?_⟩
  · intro j hj
    simpa [bg, hj] using And.intro (hgi (e ⟨j, hj⟩).1) (hgs (e ⟨j, hj⟩).1)
  · intro l
    let F := Finset.univ.filter (fun j : Fin (m + 2) => j ∉ S ∧ bg j = l)
    have hf (j : F) : (j : Fin (m + 2)) ∉ S ∧ bg j = l :=
      (Finset.mem_filter.1 j.property).2
    let g (j : F) := (e ⟨j, (hf j).1⟩).2
    have hi : Function.Injective g := by
      intro j j' h
      apply Subtype.ext
      have he : e ⟨(j : Fin (m + 2)), (hf j).1⟩ =
          e ⟨(j' : Fin (m + 2)), (hf j').1⟩ := by
        refine Prod.ext (hg ?_) h
        simpa only [bg, dif_pos (hf j).1, dif_pos (hf j').1] using
          (hf j).2.trans (hf j').2.symm
      exact congrArg (fun x : {j : Fin (m + 2) // j ∉ S} => x.val) (e.injective he)
    have hcF : F.card ≤ 2 := by
      simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective g hi
    change (∑ _ ∈ F, A) ≤ 2 * A
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcF) hA

private theorem span_grid {n k : ℕ} [NeZero n] (δ : ℝ)
    (x : Fin k → Fin n) (d : Fin n → Fin k → ℝ) :
    ∃ z : ℤ, span δ x d = δ * (z : ℝ) := by
  rw [span_eq]
  obtain ⟨i, _, hm⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (jobLoad δ x d)
  refine ⟨∑ j ∈ Finset.univ.filter (fun j => x j = i), ⌈d i j / δ⌉, hm.trans ?_⟩
  simp [jobLoad, roundUp, Finset.mul_sum]


theorem solution {n : ℕ} [NeZero n] {a b δ ε : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hδ : 0 < δ) (hδε : 2 * δ ≤ ε * a) (hn : 3 ≤ n)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (rank : (Fin n → Fin n) → ℕ) (hinj : Function.Injective rank)
    (hpriority : ∀ v : Fin n → Fin n → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) →
      ∀ y : Fin n → Fin n,
        roundedMakespan δ y (corrStar y v) =
          roundedMakespan δ (allocOf f δ v) (corrStar (allocOf f δ v) v) →
        rank (allocOf f δ v) ≤ rank y)
    (t d : Fin n → Fin n → ℝ)
    (ht : ∀ l j, a ≤ t l j ∧ t l j ≤ b) (hd : ∀ l j, a ≤ d l j ∧ d l j ≤ b)
    (hop : ∀ i, DeclarationOptimal f δ a b i (t i) (d i))
    (y : Fin n → Fin n) :
    HasAllocationCertificates f δ a b t d ((1 + ε) * makespan y (corrStar y t)) := by
  classical
  let A := roundUp δ a
  let B := roundUp δ b
  let C := span δ y t
  let M := C + δ
  let T := makespan y (corrStar y t)
  have hA : 0 < A := ha.trans_le (ru_ge hδ)
  have hpos (l j : Fin n) : 0 ≤ roundUp δ (t l j) :=
    hA.le.trans (ru_mono hδ (ht l j).1)
  let j₀ : Fin n := Fin.ofNat n 0
  have hAC : A ≤ C := (ru_mono hδ (ht (y j₀) j₀).1).trans (task_le y t hpos j₀)
  have hTa : a ≤ T := by
    refine (ht (y j₀) j₀).1.trans ?_
    unfold T makespan
    change t (y j₀) j₀ ≤ _
    have hsingle : corrStar y t j₀ ≤ load y (corrStar y t) (y j₀) :=
      Finset.single_le_sum (f := corrStar y t) (fun j _ => ha.le.trans (ht (y j) j).1)
      (show j₀ ∈ Finset.univ.filter (fun j => y j = y j₀) by simp)
    exact hsingle.trans (Finset.le_sup' (load y (corrStar y t)) (Finset.mem_univ (y j₀)))
  have hMT : M ≤ (1 + ε) * T := by
    have hround := (rounding_error_bound ha hδ y (corrStar y t)
      (fun j => (ht (y j) j).1)).2
    change C ≤ (1 + δ / a) * T at hround
    have hsub : δ / a ≤ ε - δ / a := (div_le_iff₀ ha).2 (by
      rw [sub_mul, div_mul_cancel₀ _ ha.ne']
      linarith)
    have htunit : 1 ≤ T / a := (le_div_iff₀ ha).2 (by simpa using hTa)
    have hadd : δ ≤ (δ / a) * T := by
      rw [div_mul_eq_mul_div, mul_div_assoc]
      simpa using mul_le_mul_of_nonneg_left htunit hδ.le
    have hcoeff := mul_le_mul_of_nonneg_right hsub (ha.le.trans hTa)
    dsimp [M]
    linarith only [hround, hadd, hcoeff]
  have hMa : a ≤ M := (ru_ge hδ).trans (hAC.trans (le_add_of_nonneg_right hδ.le))
  have hM0 : 0 ≤ M := ha.le.trans hMa
  obtain ⟨m, hm⟩ := span_grid δ y t
  change C = δ * (m : ℝ) at hm
  have hMgrid : M = δ * ((m + 1 : ℤ) : ℝ) := by simp [M, hm, mul_add]
  have hMru : roundUp δ M = M := by rw [hMgrid, ru_grid hδ]
  intro i _
  refine ⟨d, hd, rfl, rfl, ?_⟩
  let v := Function.update d i (t i)
  have hv (l j : Fin n) : a ≤ v l j ∧ v l j ≤ b := by
    by_cases h : l = i
    · subst l; simpa [v] using ht i j
    · simpa [v, h] using hd l j
  suffices h : ∃ z : Fin n → Fin n, span δ z v ≤ M by
    obtain ⟨z, hz⟩ := h
    exact ⟨z, hz.trans hMT⟩
  by_cases hBM : B ≤ M
  · refine ⟨id, injective_span id Function.injective_id v hM0 (fun j => ?_)⟩
    exact (ru_mono hδ (hv j j).2).trans hBM
  have hMb : M ≤ b := by
    have hl : (m + 1 : ℤ) < ⌈b / δ⌉ := by
      have hh := lt_of_not_ge hBM
      rw [hMgrid] at hh
      exact_mod_cast (lt_of_mul_lt_mul_left hh hδ.le)
    have hbig : M + δ ≤ B := by
      rw [hMgrid]
      have hh : ((m + 1 + 1 : ℤ) : ℝ) ≤ ↑⌈b / δ⌉ := by
        exact_mod_cast Int.add_one_le_of_lt hl
      simpa [B, roundUp, mul_add] using mul_le_mul_of_nonneg_left hh hδ.le
    linarith [ru_lt (u := b) hδ]
  refine ⟨y, ?_⟩
  by_cases hCA : C < 2 * A
  · have hy : Function.Injective y := by
      intro j j' he
      by_contra hne
      have hsum := pair_le y t hpos (y j) j j' hne rfl he.symm
      have h1 := ru_mono (δ := δ) hδ (ht (y j) j).1
      have h2 := ru_mono (δ := δ) hδ (ht (y j) j').1
      exact (not_le_of_gt hCA) (by linarith [show _ ≤ C from hsum])
    apply injective_span y hy v hM0
    intro j
    have hj := task_le y t hpos j
    change _ ≤ C at hj
    by_cases hi : y j = i
    · exact (show roundUp δ (v (y j) j) ≤ C by simpa [v, hi] using hj).trans
        (le_add_of_nonneg_right hδ.le)
    · have hh := set_probe_bound ha hab hδ hn f hf rank hinj hpriority (y j)
        (t (y j)) (d (y j)) (ht (y j)) (hd (y j)) (hop (y j)) y hy j rfl hj m hm
      simpa [v, hi, M] using hh
  · have hCA' : 2 * A ≤ C := le_of_not_gt hCA
    rw [span_eq]
    apply Finset.sup'_le
    intro l _
    by_cases hli : l = i
    · subst l
      have hh := (load_le_span y t i).trans (le_add_of_nonneg_right (a := C) hδ.le)
      simpa [v, jobLoad, M] using hh
    · let F := Finset.univ.filter (fun j => y j = l)
      have bind (S : Finset (Fin n)) :
          S ⊆ F → (∑ j ∈ S, roundUp δ (d l j)) ≤ M := by
        induction S using Finset.strongInductionOn
        rename_i S ih
        intro hSF
        by_cases hempty : S = ∅
        · simp [hempty, hM0]
        obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        obtain ⟨spare, hs, bg, hbg, hbgload⟩ := two_per_machine hn l S ⟨j, hj⟩ hA.le
        have hbgload' (u : Fin n) :
            (∑ j ∈ Finset.univ.filter (fun j => j ∉ S ∧ bg j = u), roundUp δ a) < M :=
          ((hbgload u).trans hCA').trans_lt (lt_add_of_pos_right C hδ)
        have htS : (∑ j ∈ S, roundUp δ (t l j)) < M := by
          have hsub := Finset.sum_le_sum_of_subset_of_nonneg
            (f := fun j => roundUp δ (t l j)) hSF (fun j _ _ => hpos l j)
          exact (hsub.trans (load_le_span y t l)).trans_lt (lt_add_of_pos_right C hδ)
        exact bundle_report_bound_with_reserved_machine ha hδ hMa hMb hMru f hf l spare hs
          (t l) (d l) (ht l) (hd l) (hop l) S j hj bg hbg hbgload' htS
          (ih _ (Finset.erase_ssubset hj) ((Finset.erase_subset _ _).trans hSF))
      simpa [jobLoad, v, hli] using bind F (by rfl)
