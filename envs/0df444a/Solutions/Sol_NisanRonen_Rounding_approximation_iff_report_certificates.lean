-- Prove2me | solution 1 for NisanRonen.Rounding.approximation_iff_report_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:12:42.997199+00:00
-- url     : https://prove2.me/submissions/8f202d60-91e0-4045-b15a-a734355dd414

import Definitions.Def_NisanRonen_Rounding_CertificateCriterion
import Theorems.Thm_NisanRonen_Rounding_dominant_iff_rounded_optimal
import Theorems.Thm_NisanRonen_Rounding_rounding_error_bound

open NisanRonen.Rounding

set_option autoImplicit false

private theorem roundedMono {n k : ℕ} [NeZero n] {δ : ℝ} (hδ : 0 < δ)
    (x : Fin k → Fin n) {u v : Fin k → ℝ} (h : ∀ j, u j ≤ v j) :
    roundedMakespan δ x u ≤ roundedMakespan δ x v := by
  unfold roundedMakespan makespan
  apply Finset.sup'_le
  intro i hi
  refine le_trans ?_ (Finset.le_sup' _ hi)
  unfold load
  apply Finset.sum_le_sum
  intro j _
  unfold roundUp
  exact mul_le_mul_of_nonneg_left
    (by exact_mod_cast Int.ceil_mono (div_le_div_of_nonneg_right (h j) hδ.le)) hδ.le

private theorem roundUp_ge {δ u : ℝ} (hδ : 0 < δ) : u ≤ roundUp δ u := by
  have h : u / δ ≤ (↑⌈u / δ⌉ : ℝ) := Int.le_ceil _
  have hm := mul_le_mul_of_nonneg_left h hδ.le
  rw [mul_comm δ (u / δ), div_mul_cancel₀ _ hδ.ne'] at hm
  exact hm

private theorem roundUp_grid {δ : ℝ} (hδ : 0 < δ) (z : ℤ) :
    roundUp δ (δ * (z : ℝ)) = δ * (z : ℝ) := by
  simp [roundUp, mul_div_cancel_left₀ _ hδ.ne']

private theorem roundedLoad_grid {n k : ℕ} (δ : ℝ)
    (x : Fin k → Fin n) (τ : Fin k → ℝ) (i : Fin n) :
    load x (fun j => roundUp δ (τ j)) i =
      δ * (↑(∑ j ∈ Finset.univ.filter (fun j => x j = i), ⌈τ j / δ⌉) : ℝ) := by
  simp [load, roundUp, Finset.mul_sum]

private theorem roundedMakespan_grid {n k : ℕ} [NeZero n] (δ : ℝ)
    (x : Fin k → Fin n) (τ : Fin k → ℝ) :
    ∃ z : ℤ, roundedMakespan δ x τ = δ * (z : ℝ) := by
  unfold roundedMakespan makespan
  obtain ⟨i, hi, hm⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (load x fun j => roundUp δ (τ j))
  exact ⟨_, hm.trans (roundedLoad_grid δ x τ i)⟩

private theorem certificates_sufficient {n k : ℕ} [NeZero n] {a b δ : ℝ} (ha : 0 < a)
    (hab : a < b) (hδ : 0 < δ) (f : List (Fin n → ℕ) → List (Fin n))
    (hf : IsExactRoundedSolver f δ a b) (t : Fin n → Fin k → ℝ)
    (ht : ∀ i j, a ≤ t i j ∧ t i j ≤ b) (s : Fin n → Strategy n k)
    (hs : ∀ i, IsDominant f δ a b i (t i) (s i)) (C : ℝ) (hC : 0 ≤ C)
    (hcert : HasAllocationCertificates f δ a b t (fun l => (s l).decl) C) :
    makespan (allocOf f δ (fun l => (s l).decl)) (actualTimes f δ s) ≤ C := by
  classical
  unfold makespan
  apply Finset.sup'_le
  intro i _
  by_cases hi : ∃ j, allocOf f δ (fun l => (s l).decl) j = i
  · obtain ⟨d, hd, hdi, hx, y, hy⟩ := hcert i hi
    let q : Fin n → Strategy n k := fun l => ⟨d l, fun _ => d l⟩
    have hup : (fun l => (Function.update q i (s i) l).decl) = d := by
      funext l
      by_cases he : l = i
      · subst l
        simpa only [Function.update_self] using hdi.symm
      · simp [Function.update_of_ne he, q]
    have hdom := ((dominant_iff_rounded_optimal ha hab hδ f hf t ht i (s i) (hs i).1).mp
      (hs i)) q (fun l _ j => hd l j) y
    rw [hup] at hdom
    let x := allocOf f δ d
    let τ := corr i x d ((s i).exec x)
    have hτ : ∀ j, a ≤ τ j := by
      intro j
      by_cases hj : x j = i
      · simpa [τ, corr, hj] using (ht i j).1.trans ((hs i).1.2 x j hj)
      · simpa [τ, corr, hj] using (hd (x j) j).1
    have hload : load x (actualTimes f δ s) i = load x τ i := by
      unfold load
      apply Finset.sum_congr rfl
      intro j hj
      have he : x j = i := (Finset.mem_filter.mp hj).2
      simp [τ, x, corr, actualTimes, ← hx, he]
    rw [← hx, hload]
    exact (Finset.le_sup' _ (Finset.mem_univ i)).trans
      ((rounding_error_bound ha hδ x τ hτ).1.trans (hdom.trans hy))
  · unfold load
    push Not at hi
    simpa [hi] using hC

private theorem minimal_is_dominant {n k : ℕ} [NeZero n] {a b δ : ℝ} (ha : 0 < a)
    (hab : a < b) (hδ : 0 < δ) (f : List (Fin n → ℕ) → List (Fin n))
    (hf : IsExactRoundedSolver f δ a b) (t : Fin n → Fin k → ℝ)
    (ht : ∀ i j, a ≤ t i j ∧ t i j ≤ b) (i : Fin n) (s : Strategy n k)
    (hs : IsDominant f δ a b i (t i) s) :
    IsDominant f δ a b i (t i) ⟨s.decl, fun _ => t i⟩ := by
  classical
  let s' : Strategy n k := ⟨s.decl, fun _ => t i⟩
  have hv : IsValid a b (t i) i s' := ⟨hs.1.1, fun _ _ _ => le_rfl⟩
  apply (dominant_iff_rounded_optimal ha hab hδ f hf t ht i s' hv).2
  intro w hw
  dsimp only
  intro y
  have he : (fun l => (Function.update w i s' l).decl) =
      (fun l => (Function.update w i s l).decl) := by
    funext l
    by_cases hl : l = i <;> simp [s', hl]
  rw [he]
  let d := fun l => (Function.update w i s l).decl
  let x := allocOf f δ d
  have hdom := (dominant_iff_rounded_optimal ha hab hδ f hf t ht i s hs.1).1 hs w hw y
  refine le_trans (roundedMono hδ x ?_) hdom
  intro j
  change corr i x d (t i) j ≤ corr i x d (s.exec x) j
  by_cases hj : x j = i
  · simpa [corr, hj] using hs.1.2 x j hj
  · simp [corr, hj]

private theorem certificate_necessary {n k : ℕ} [NeZero n] {a b δ : ℝ} (ha : 0 < a)
    (hab : a < b) (hδ : 0 < δ) (f : List (Fin n → ℕ) → List (Fin n))
    (hf : IsExactRoundedSolver f δ a b) (t d : Fin n → Fin k → ℝ)
    (ht : ∀ i j, a ≤ t i j ∧ t i j ≤ b)
    (hs : ∀ i, IsDominant f δ a b i (t i) ⟨d i, fun _ => t i⟩) (C : ℝ)
    (hbound : ∀ s : Fin n → Strategy n k, (∀ i, IsDominant f δ a b i (t i) (s i)) →
      (∀ i, (s i).decl = d i) →
      makespan (allocOf f δ d) (actualTimes f δ s) ≤ C) :
    HasAllocationCertificates f δ a b t d C := by
  classical
  let x := allocOf f δ d
  let s₀ : Fin n → Strategy n k := fun i => ⟨d i, fun _ => t i⟩
  intro i hi
  obtain ⟨j₀, hj₀⟩ := hi
  by_contra hfail
  let z₀ : ℤ := ⌊C / δ⌋ + 1
  have hz₀ : C < δ * (z₀ : ℝ) := by
    rw [mul_comm, ← div_lt_iff₀ hδ]
    simp [z₀, Int.lt_floor_add_one]
  have hgrid {V : ℝ} (hV : C < V) (hVgrid : ∃ z : ℤ, V = δ * (z : ℝ)) :
      δ * (z₀ : ℝ) ≤ V := by
    obtain ⟨z, rfl⟩ := hVgrid
    have hz : z₀ ≤ z := by
      apply Int.add_one_le_of_lt
      exact Int.floor_lt.mpr ((div_lt_iff₀ hδ).mpr (by simpa [mul_comm] using hV))
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hz) hδ.le
  let jobs := Finset.univ.filter (fun j => x j = i)
  let u (j : Fin k) : ℤ := ⌈t i j / δ⌉
  let L : ℤ := ∑ j ∈ jobs, u j
  let z := max z₀ L
  let delayed (j : Fin k) : ℝ :=
    δ * (↑(u j + if j = j₀ then z - L else 0) : ℝ)
  let si : Strategy n k := ⟨d i, fun w j => if w = x then delayed j else t i j⟩
  have hpos (j : Fin k) : t i j ≤ delayed j := by
    refine (roundUp_ge hδ).trans ?_
    unfold delayed roundUp
    apply mul_le_mul_of_nonneg_left _ hδ.le
    exact_mod_cast (show u j ≤ u j + (if j = j₀ then z - L else 0) by
      have h : L ≤ z := le_max_right .. 
      split <;> omega)
  have hdelayed (j : Fin k) : roundUp δ (delayed j) = delayed j := roundUp_grid hδ _
  have hjmem : j₀ ∈ jobs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj₀⟩
  have hdelayLoad : load x delayed i = δ * (z : ℝ) := by
    change (∑ j ∈ jobs, δ * (↑(u j + if j = j₀ then z - L else 0) : ℝ)) = _
    rw [← Finset.mul_sum, ← Int.cast_sum, Finset.sum_add_distrib, Finset.sum_ite_eq' jobs j₀]
    rw [if_pos hjmem]
    change δ * (↑(L + (z - L)) : ℝ) = δ * (z : ℝ)
    congr 2
    omega
  have hv : IsValid a b (t i) i si := by
    refine ⟨(hs i).1.1, fun w j _ => ?_⟩
    by_cases he : w = x
    · simpa [si, he] using hpos j
    · simp [si, he]
  have hdom : IsDominant f δ a b i (t i) si := by
    apply (dominant_iff_rounded_optimal ha hab hδ f hf t ht i si hv).2
    intro w hw
    dsimp only
    intro y
    let v := fun l => (Function.update w i si l).decl
    have hvi : v i = d i := by simp [v, si]
    have hve : (fun l => (Function.update w i (s₀ i) l).decl) = v := by
      funext l
      by_cases hl : l = i <;> simp [v, s₀, si, Function.update_apply, hl]
    have hvb (l : Fin n) (j : Fin k) : a ≤ v l j ∧ v l j ≤ b := by
      by_cases hl : l = i
      · subst l
        rw [hvi]
        exact (hs i).1.1 j
      · simpa [v, Function.update_of_ne hl] using hw l hl j
    let x' := allocOf f δ v
    let W := roundedMakespan δ y (corrStar y (Function.update v i (t i)))
    have h₀ := (dominant_iff_rounded_optimal ha hab hδ f hf t ht i (s₀ i) (hs i).1).1
      (hs i) w hw y
    rw [hve] at h₀
    change roundedMakespan δ x' (corr i x' v (t i)) ≤ W at h₀
    change roundedMakespan δ x' (corr i x' v (si.exec x')) ≤ W
    by_cases he : x' = x
    · have hbig : C < W := lt_of_not_ge
        (fun hle => hfail ⟨v, hvb, hvi, he, y, hle⟩)
      have hgrid' := hgrid hbig (roundedMakespan_grid δ y _)
      rw [he] at h₀ ⊢
      have hL : δ * (L : ℝ) ≤ W := by
        have hload : load x (fun j => roundUp δ (corr i x v (t i) j)) i = δ * (L : ℝ) := by
          rw [roundedLoad_grid]
          congr 2
          apply Finset.sum_congr rfl
          intro j hj
          have hj' : x j = i := (Finset.mem_filter.mp hj).2
          simp [corr, hj', u]
        rw [← hload]
        exact (Finset.le_sup' _ (Finset.mem_univ i)).trans h₀
      have hzle : δ * (z : ℝ) ≤ W := by
        rcases le_total z₀ L with h | h
        · simpa [z, max_eq_right h] using hL
        · simpa [z, max_eq_left h] using hgrid'
      unfold roundedMakespan makespan
      apply Finset.sup'_le
      intro l hl
      by_cases hil : l = i
      · subst l
        rw [← hdelayLoad] at hzle
        refine le_trans ?_ hzle
        unfold load
        apply le_of_eq
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : x j = i := (Finset.mem_filter.mp hj).2
        simp [corr, hj', si, hdelayed]
      · have heq : load x (fun j => roundUp δ (corr i x v (si.exec x) j)) l =
            load x (fun j => roundUp δ (corr i x v (t i) j)) l := by
          unfold load
          apply Finset.sum_congr rfl
          intro j hj
          have hj' : x j = l := (Finset.mem_filter.mp hj).2
          simp [corr, hj'.trans_ne hil]
        rw [heq]
        exact (Finset.le_sup' _ hl).trans h₀
    · simpa [si, he] using h₀
  let s := Function.update s₀ i si
  have hs' (l : Fin n) : IsDominant f δ a b l (t l) (s l) := by
    by_cases hl : l = i
    · subst l
      simpa [s] using hdom
    · simpa [s, Function.update_of_ne hl, s₀] using hs l
  have hd (l : Fin n) : (s l).decl = d l := by
    by_cases hl : l = i <;> simp [s, s₀, si, hl]
  have hActual : load x (actualTimes f δ s) i = load x delayed i := by
    unfold load
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : x j = i := (Finset.mem_filter.mp hj).2
    have hmatrix : (fun l => (s l).decl) = d := funext hd
    simp [actualTimes, hmatrix, ← show x = allocOf f δ d from rfl, hj', s, si]
  have hReal := hbound s hs' hd
  have hM : load x (actualTimes f δ s) i ≤ C :=
    (Finset.le_sup' _ (Finset.mem_univ i)).trans hReal
  rw [hActual, hdelayLoad] at hM
  exact hz₀.not_ge ((mul_le_mul_of_nonneg_left (by exact_mod_cast le_max_left z₀ L) hδ.le).trans hM)


private theorem correct_minimal {n k : ℕ} (i : Fin n) (x : Fin k → Fin n)
    (v : Fin n → Fin k → ℝ) (ti : Fin k → ℝ) :
    corr i x v ti = corrStar x (Function.update v i ti) := by
  funext j
  by_cases h : x j = i <;> simp [corr, corrStar, h]

private theorem declaration_test_iff {n k : ℕ} [NeZero n] {a b δ : ℝ} (ha : 0 < a)
    (hab : a < b) (hδ : 0 < δ) (f : List (Fin n → ℕ) → List (Fin n))
    (hf : IsExactRoundedSolver f δ a b) (t : Fin n → Fin k → ℝ)
    (ht : ∀ i j, a ≤ t i j ∧ t i j ≤ b) (i : Fin n) (r : Fin k → ℝ)
    (hr : ∀ j, a ≤ r j ∧ r j ≤ b) :
    IsDominant f δ a b i (t i) (⟨r, fun _ => t i⟩ : Strategy n k) ↔
      DeclarationOptimal f δ a b i (t i) r := by
  classical
  let σ : Strategy n k := ⟨r, fun _ => t i⟩
  have hv : IsValid a b (t i) i σ := ⟨hr, fun _ _ _ => le_rfl⟩
  have step := dominant_iff_rounded_optimal ha hab hδ f hf t ht i σ hv
  constructor
  · intro h d hd hdi
    dsimp only
    intro y
    let w : Fin n → Strategy n k := fun l => ⟨d l, fun _ => d l⟩
    have he : (fun l => (Function.update w i σ l).decl) = d := by
      funext l
      by_cases hl : l = i
      · subst l
        simpa [σ] using hdi.symm
      · simp [w, Function.update_of_ne hl]
    have hh := step.1 h w (fun l _ j => hd l j) y
    rw [he] at hh
    simpa only [σ, correct_minimal] using hh
  · intro h
    apply step.2
    intro w hw
    dsimp only
    intro y
    let d := fun l => (Function.update w i σ l).decl
    have hdi : d i = r := by simp [d, σ]
    have hd (l : Fin n) (j : Fin k) : a ≤ d l j ∧ d l j ≤ b := by
      by_cases hl : l = i
      · subst l
        rw [hdi]
        exact hr j
      · simpa [d, Function.update_of_ne hl] using hw l hl j
    simpa only [σ, correct_minimal] using h d hd hdi y

theorem solution {n : ℕ} [NeZero n] {a b δ ε : ℝ} (ha : 0 < a) (hab : a < b)
    (hδ : 0 < δ) (hε : 0 ≤ ε)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b) :
    (∀ (k : ℕ) (t : Fin n → Fin k → ℝ), (∀ i j, a ≤ t i j ∧ t i j ≤ b) →
      ∀ s : Fin n → Strategy n k, (∀ i, IsDominant f δ a b i (t i) (s i)) →
      ∀ y : Fin k → Fin n,
        makespan (allocOf f δ (fun i => (s i).decl)) (actualTimes f δ s) ≤
          (1 + ε) * makespan y (corrStar y t)) ↔ CertificateCriterion f δ a b ε := by
  constructor
  · intro h k t d ht hd hopt y
    apply certificate_necessary ha hab hδ f hf t d ht
      (fun i => (declaration_test_iff ha hab hδ f hf t ht i (d i) (hd i)).2 (hopt i))
    intro s hs he
    rw [← funext he]
    exact h k t ht s hs y
  · intro h k t ht s hs y
    let d := fun i => (s i).decl
    have hd (i : Fin n) (j : Fin k) : a ≤ d i j ∧ d i j ≤ b := (hs i).1.1 j
    have hopt (i : Fin n) : DeclarationOptimal f δ a b i (t i) (d i) :=
      (declaration_test_iff ha hab hδ f hf t ht i (d i) (hd i)).1
        (minimal_is_dominant ha hab hδ f hf t ht i (s i) (hs i))
    have hM : 0 ≤ makespan y (corrStar y t) := by
      have hl : 0 ≤ load y (corrStar y t) (0 : Fin n) := by
        unfold load
        apply Finset.sum_nonneg
        intro j _
        exact ha.le.trans (ht (y j) j).1
      exact hl.trans (Finset.le_sup' _ (Finset.mem_univ _))
    exact certificates_sufficient ha hab hδ f hf t ht s hs _
      (mul_nonneg (by positivity) hM) (h k t d ht hd hopt y)
