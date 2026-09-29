-- Prove2me | solution 1 for LinearOptimization.polyhedron_std_form_has_bfs
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-05T06:23:52.002887+00:00
-- url     : https://prove2.me/submissions/281c36e3-c5f7-4e6f-9e5e-c88e8963fa87

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Segment
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.List.TFAE
import Mathlib.Data.EReal.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.Set.Finite.Lattice
import Definitions.Def_Polyhedron
import Definitions.Def_ContainsLine
import Definitions.Def_Vertex
import Definitions.Def_BasicSolution
import Theorems.Thm_LinearOptimization_lp_active_constraint_equiv
import Theorems.Thm_LinearOptimization_lp_vertex_extreme_bfs_equiv
import Theorems.Thm_LinearOptimization_lp_basic_solutions_finite
import Theorems.Thm_LinearOptimization_polyhedron_extreme_point_existence

open Matrix LinearOptimization


namespace LOCore2

/-- The span of the constraint vectors active at `x`. -/
def actSpan {ι : Type} {n : ℕ} (C : ι → LinearConstraint n) (x : Fin n → ℝ) :
    Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ ((fun i => (C i).a) '' {i | (C i).IsActiveAt x})

/-- Constraint families with no `≤` constraint. -/
def NoLe {ι : Type} {n : ℕ} (C : ι → LinearConstraint n) : Prop :=
  ∀ i, (C i).rel ≠ ConstraintRel.le

lemma ge_of_mem {ι : Type} {n : ℕ} {C : ι → LinearConstraint n} (hC : NoLe C)
    {x : Fin n → ℝ} (hx : x ∈ constraintSet C) (i : ι) : (C i).b ≤ (C i).a ⬝ᵥ x := by
  have h := hx i
  rcases hr : (C i).rel with _ | _ | _
  · simp only [LinearConstraint.IsSatisfiedAt, hr] at h; exact h
  · exact absurd hr (hC i)
  · simp only [LinearConstraint.IsSatisfiedAt, hr] at h; exact le_of_eq h.symm

lemma eq_active_of_mem {ι : Type} {n : ℕ} {C : ι → LinearConstraint n}
    {x : Fin n → ℝ} (hx : x ∈ constraintSet C) (i : ι)
    (hi : (C i).rel = ConstraintRel.eq) : (C i).IsActiveAt x := by
  have h := hx i
  simp only [LinearConstraint.IsSatisfiedAt, hi] at h
  exact h

lemma mem_of_ge {ι : Type} {n : ℕ} {C : ι → LinearConstraint n} (hC : NoLe C)
    {y : Fin n → ℝ} (h1 : ∀ i, (C i).b ≤ (C i).a ⬝ᵥ y)
    (h2 : ∀ i, (C i).rel = ConstraintRel.eq → (C i).a ⬝ᵥ y = (C i).b) :
    y ∈ constraintSet C := by
  intro i
  rcases hr : (C i).rel with _ | _ | _
  · simp only [LinearConstraint.IsSatisfiedAt, hr]; exact h1 i
  · exact absurd hr (hC i)
  · simp only [LinearConstraint.IsSatisfiedAt, hr]; exact h2 i hr

/-- Theorem 2.2: spanning active vectors at a feasible point give a basic feasible solution. -/
lemma isBFS_of_actSpan_top {ι : Type} [Fintype ι] {n : ℕ} {C : ι → LinearConstraint n}
    {x : Fin n → ℝ} (hx : x ∈ constraintSet C) (h : actSpan C x = ⊤) :
    IsBasicFeasibleSolution C x :=
  ⟨⟨fun i hi => eq_active_of_mem hx i hi,
    ((lp_active_constraint_equiv C x).out 1 0).mp h⟩, hx⟩

/-- Moving along a ray on which the cost strictly decreases makes the LP unbounded. -/
lemma unbounded_of_ray {ι : Type} {n : ℕ} {C : ι → LinearConstraint n} (hC : NoLe C)
    (c : Fin n → ℝ) {x e : Fin n → ℝ} (hx : x ∈ constraintSet C)
    (hray : ∀ i, 0 ≤ (C i).a ⬝ᵥ e)
    (hactzero : ∀ i, (C i).IsActiveAt x → (C i).a ⬝ᵥ e = 0)
    (hc : c ⬝ᵥ e < 0) :
    ∀ M : ℝ, ∃ w ∈ constraintSet C, c ⬝ᵥ w < M := by
  intro M
  obtain ⟨lam, hlam0, hlam⟩ : ∃ lam : ℝ, 0 ≤ lam ∧ c ⬝ᵥ x + lam * (c ⬝ᵥ e) < M := by
    refine ⟨max 0 ((c ⬝ᵥ x - M) / (-(c ⬝ᵥ e)) + 1), le_max_left _ _, ?_⟩
    have hpos : 0 < -(c ⬝ᵥ e) := by linarith
    have hge : (c ⬝ᵥ x - M) / (-(c ⬝ᵥ e)) + 1 ≤ max 0 ((c ⬝ᵥ x - M) / (-(c ⬝ᵥ e)) + 1) :=
      le_max_right _ _
    have hkey : (c ⬝ᵥ x - M) < ((c ⬝ᵥ x - M) / (-(c ⬝ᵥ e)) + 1) * (-(c ⬝ᵥ e)) := by
      rw [add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hpos)]
      linarith
    nlinarith [hge, hpos]
  refine ⟨x + lam • e, ?_, ?_⟩
  · refine mem_of_ge hC ?_ ?_
    · intro i
      have h1 : (C i).b ≤ (C i).a ⬝ᵥ x := ge_of_mem hC hx i
      have h2 : 0 ≤ lam * ((C i).a ⬝ᵥ e) := mul_nonneg hlam0 (hray i)
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
      linarith
    · intro i hi
      have hia : (C i).IsActiveAt x := eq_active_of_mem hx i hi
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hactzero i hia, mul_zero, add_zero]
      exact hia
  · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    exact hlam

/-- The blocking step. -/
lemma block {ι : Type} [Fintype ι] {n : ℕ} {C : ι → LinearConstraint n} (hC : NoLe C)
    {x e : Fin n → ℝ} (hx : x ∈ constraintSet C)
    (hact : ∀ i, (C i).IsActiveAt x → (C i).a ⬝ᵥ e = 0)
    (hS : (Finset.univ.filter (fun i => (C i).a ⬝ᵥ e < 0)).Nonempty) :
    ∃ lam : ℝ, 0 ≤ lam ∧ (x + lam • e) ∈ constraintSet C ∧
      actSpan C x < actSpan C (x + lam • e) := by
  classical
  set S : Finset ι := Finset.univ.filter (fun i => (C i).a ⬝ᵥ e < 0) with hSdef
  have hmemS : ∀ i, i ∈ S ↔ (C i).a ⬝ᵥ e < 0 := by intro i; simp [hSdef]
  set f : ι → ℝ := fun i => ((C i).a ⬝ᵥ x - (C i).b) / (-((C i).a ⬝ᵥ e)) with hf
  set lam : ℝ := S.inf' hS f with hlam
  have hlam0 : 0 ≤ lam := by
    refine Finset.le_inf' hS f ?_
    intro i hi
    have hneg : (C i).a ⬝ᵥ e < 0 := (hmemS i).mp hi
    have h1 : (C i).b ≤ (C i).a ⬝ᵥ x := ge_of_mem hC hx i
    exact div_nonneg (by linarith) (by linarith)
  obtain ⟨j, hjS, hjeq⟩ := Finset.exists_mem_eq_inf' hS f
  have hlamj : lam = f j := by rw [hlam]; exact hjeq
  have hjneg : (C j).a ⬝ᵥ e < 0 := (hmemS j).mp hjS
  -- previously active constraints stay active
  have hkeep : ∀ i, (C i).IsActiveAt x → (C i).a ⬝ᵥ (x + lam • e) = (C i).b := by
    intro i hi
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hact i hi, mul_zero, add_zero]
    exact hi
  have hgeall : ∀ i, (C i).b ≤ (C i).a ⬝ᵥ (x + lam • e) := by
    intro i
    have h1 : (C i).b ≤ (C i).a ⬝ᵥ x := ge_of_mem hC hx i
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    rcases lt_or_ge ((C i).a ⬝ᵥ e) 0 with hneg | hnonneg
    · have hi : i ∈ S := (hmemS i).mpr hneg
      have hle : lam ≤ f i := Finset.inf'_le f hi
      have hpos : 0 < -((C i).a ⬝ᵥ e) := by linarith
      have hne : -((C i).a ⬝ᵥ e) ≠ 0 := ne_of_gt hpos
      have hval : f i * (-((C i).a ⬝ᵥ e)) = (C i).a ⬝ᵥ x - (C i).b := div_mul_cancel₀ _ hne
      have hmul : lam * (-((C i).a ⬝ᵥ e)) ≤ (C i).a ⬝ᵥ x - (C i).b := by
        calc lam * (-((C i).a ⬝ᵥ e)) ≤ f i * (-((C i).a ⬝ᵥ e)) :=
              mul_le_mul_of_nonneg_right hle (le_of_lt hpos)
          _ = (C i).a ⬝ᵥ x - (C i).b := hval
      linarith
    · nlinarith [mul_nonneg hlam0 hnonneg]
  have hfeas : (x + lam • e) ∈ constraintSet C := by
    refine mem_of_ge hC hgeall ?_
    intro i hi
    exact hkeep i (eq_active_of_mem hx i hi)
  -- the blocking constraint becomes active
  have hjact : (C j).a ⬝ᵥ (x + lam • e) = (C j).b := by
    have hne : (C j).a ⬝ᵥ e ≠ 0 := ne_of_lt hjneg
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hlamj]
    show (C j).a ⬝ᵥ x
        + (((C j).a ⬝ᵥ x - (C j).b) / (-((C j).a ⬝ᵥ e))) * ((C j).a ⬝ᵥ e) = (C j).b
    field_simp
    ring
  have hjnot : (C j).a ∉ actSpan C x := by
    intro hmem
    have hsub : ((fun i => (C i).a) '' {i | (C i).IsActiveAt x}) ⊆
        {v : Fin n → ℝ | v ⬝ᵥ e = 0} := by
      rintro v ⟨i, hi, rfl⟩
      exact hact i hi
    have hspan : actSpan C x ≤
        (⟨⟨⟨{v : Fin n → ℝ | v ⬝ᵥ e = 0}, by
            intro u v hu hv
            simp only [Set.mem_setOf_eq, add_dotProduct] at *
            rw [hu, hv, add_zero]⟩, by simp⟩, by
            intro r v hv
            simp only [Set.mem_setOf_eq, smul_dotProduct] at *
            rw [hv, smul_zero]⟩ : Submodule ℝ (Fin n → ℝ)) :=
      Submodule.span_le.mpr hsub
    have : (C j).a ⬝ᵥ e = 0 := hspan hmem
    linarith
  refine ⟨lam, hlam0, hfeas, lt_of_le_of_ne ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨i, hi, rfl⟩
    exact Submodule.subset_span ⟨i, hkeep i hi, rfl⟩
  · intro hEq
    exact hjnot (hEq ▸ Submodule.subset_span ⟨j, hjact, rfl⟩)

/-- **Descent to a basic feasible solution**, for any `≤`-free constraint family whose
constraint vectors span `ℝⁿ`. -/
lemma descent {ι : Type} [Fintype ι] {n : ℕ} {C : ι → LinearConstraint n} (hC : NoLe C)
    (c : Fin n → ℝ) (hspan : ∀ y : Fin n → ℝ, (∀ i, (C i).a ⬝ᵥ y = 0) → y = 0) :
    ∀ (k : ℕ) (x : Fin n → ℝ), x ∈ constraintSet C →
      n - Module.finrank ℝ (actSpan C x) ≤ k →
      (∀ M : ℝ, ∃ w ∈ constraintSet C, c ⬝ᵥ w < M) ∨
      (∃ y, IsBasicFeasibleSolution C y ∧ c ⬝ᵥ y ≤ c ⬝ᵥ x) := by
  classical
  have hfrn : Module.finrank ℝ (Fin n → ℝ) = n := by
    rw [Module.finrank_pi ℝ, Fintype.card_fin]
  intro k
  induction k with
  | zero =>
      intro x hx hk
      right
      have hle : Module.finrank ℝ (actSpan C x) ≤ n := by
        have h := Submodule.finrank_le (actSpan C x)
        rw [hfrn] at h
        exact h
      have heq : Module.finrank ℝ (actSpan C x) = Module.finrank ℝ (Fin n → ℝ) := by
        rw [hfrn]; omega
      exact ⟨x, isBFS_of_actSpan_top hx (Submodule.eq_top_of_finrank_eq heq), le_refl _⟩
  | succ k ih =>
      intro x hx hk
      by_cases htop : actSpan C x = ⊤
      · exact Or.inr ⟨x, isBFS_of_actSpan_top hx htop, le_refl _⟩
      obtain ⟨y0, hy0, hy0ne⟩ : ∃ y : Fin n → ℝ,
          (∀ i, (C i).IsActiveAt x → (C i).a ⬝ᵥ y = (C i).b) ∧ y ≠ x := by
        by_contra hcon
        push_neg at hcon
        exact htop (((lp_active_constraint_equiv C x).out 1 2).mpr (fun y hy => hcon y hy))
      set d : Fin n → ℝ := y0 - x with hd
      have hdne : d ≠ 0 := sub_ne_zero.mpr hy0ne
      have hdact : ∀ i, (C i).IsActiveAt x → (C i).a ⬝ᵥ d = 0 := by
        intro i hi
        have h1 : (C i).a ⬝ᵥ x = (C i).b := hi
        rw [hd, dotProduct_sub, hy0 i hi, h1, sub_self]
      obtain ⟨i₀, hi₀⟩ : ∃ i, (C i).a ⬝ᵥ d ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hdne (hspan d hcon)
      have step : ∀ e : Fin n → ℝ, (∀ i, (C i).IsActiveAt x → (C i).a ⬝ᵥ e = 0) →
          (Finset.univ.filter (fun i => (C i).a ⬝ᵥ e < 0)).Nonempty → c ⬝ᵥ e ≤ 0 →
          (∀ M : ℝ, ∃ w ∈ constraintSet C, c ⬝ᵥ w < M) ∨
          (∃ y, IsBasicFeasibleSolution C y ∧ c ⬝ᵥ y ≤ c ⬝ᵥ x) := by
        intro e hacte hSe hce
        obtain ⟨lam, hlam0, hfeas, hlt⟩ := block hC hx hacte hSe
        have hrank : Module.finrank ℝ (actSpan C x) <
            Module.finrank ℝ (actSpan C (x + lam • e)) :=
          Submodule.finrank_lt_finrank_of_lt hlt
        have hk' : n - Module.finrank ℝ (actSpan C (x + lam • e)) ≤ k := by omega
        rcases ih (x + lam • e) hfeas hk' with h | ⟨y, hy, hcy⟩
        · exact Or.inl h
        · refine Or.inr ⟨y, hy, ?_⟩
          have hmono : c ⬝ᵥ (x + lam • e) ≤ c ⬝ᵥ x := by
            rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
            have : lam * (c ⬝ᵥ e) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam0 hce
            linarith
          linarith
      have ray : ∀ e : Fin n → ℝ, ¬ (Finset.univ.filter (fun i => (C i).a ⬝ᵥ e < 0)).Nonempty →
          ∀ i, 0 ≤ (C i).a ⬝ᵥ e := by
        intro e hSe i
        by_contra hcon
        push_neg at hcon
        exact hSe ⟨i, by simp [hcon]⟩
      have hdactneg : ∀ i, (C i).IsActiveAt x → (C i).a ⬝ᵥ (-d) = 0 := by
        intro i hi; rw [dotProduct_neg, hdact i hi, neg_zero]
      rcases lt_trichotomy (c ⬝ᵥ d) 0 with hc | hc | hc
      · by_cases hS : (Finset.univ.filter (fun i => (C i).a ⬝ᵥ d < 0)).Nonempty
        · exact step d hdact hS (le_of_lt hc)
        · exact Or.inl (unbounded_of_ray hC c hx (ray d hS) hdact hc)
      · rcases lt_or_gt_of_ne hi₀ with hlt | hgt
        · exact step d hdact ⟨i₀, by simp [hlt]⟩ (le_of_eq hc)
        · refine step (-d) hdactneg ⟨i₀, by simp [dotProduct_neg, hgt]⟩ ?_
          rw [dotProduct_neg, hc, neg_zero]
      · have hcneg : c ⬝ᵥ (-d) < 0 := by rw [dotProduct_neg]; linarith
        by_cases hS : (Finset.univ.filter (fun i => (C i).a ⬝ᵥ (-d) < 0)).Nonempty
        · exact step (-d) hdactneg hS (le_of_lt hcneg)
        · exact Or.inl (unbounded_of_ray hC c hx (ray (-d) hS) hdactneg hcneg)

/-- The descent applied with zero cost: a nonempty feasible set whose constraint
vectors span `ℝⁿ` contains a basic feasible solution. -/
lemma exists_bfs {ι : Type} [Fintype ι] {n : ℕ} {C : ι → LinearConstraint n} (hC : NoLe C)
    (hspan : ∀ y : Fin n → ℝ, (∀ i, (C i).a ⬝ᵥ y = 0) → y = 0)
    {x : Fin n → ℝ} (hx : x ∈ constraintSet C) :
    ∃ y, IsBasicFeasibleSolution C y := by
  rcases descent hC 0 hspan n x hx (Nat.sub_le _ _) with h | ⟨y, hy, -⟩
  · obtain ⟨w, -, hw⟩ := h 0
    rw [zero_dotProduct] at hw
    exact absurd hw (lt_irrefl _)
  · exact ⟨y, hy⟩

end LOCore2


open LOCore2

private lemma single_dot {n : ℕ} (j : Fin n) (y : Fin n → ℝ) :
    (Pi.single j (1:ℝ)) ⬝ᵥ y = y j := by
  simp [dotProduct, Pi.single_apply, Finset.sum_ite_eq']

private lemma constraintSet_generalForm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : constraintSet (generalFormSystem A b) = polyhedron A b := by
  ext x
  constructor
  · intro h i; exact h i
  · intro h i; exact h i

private lemma constraintSet_stdForm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : constraintSet (stdFormSystem A b) = stdPolyhedron A b := by
  ext x
  constructor
  · intro h
    refine ⟨funext fun i => h (Sum.inl i), fun j => ?_⟩
    have hj : (0:ℝ) ≤ (Pi.single j (1:ℝ)) ⬝ᵥ x := h (Sum.inr j)
    rw [single_dot] at hj
    exact hj
  · rintro ⟨heq, hpos⟩ i
    cases i with
    | inl i => exact congrFun heq i
    | inr j =>
        show (0:ℝ) ≤ (Pi.single j (1:ℝ)) ⬝ᵥ x
        rw [single_dot]
        exact hpos j

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    ((polyhedron A b).Nonempty → IsBoundedSet (polyhedron A b) →
      ∃ x, IsBasicFeasibleSolution (generalFormSystem A b) x) ∧
    ((stdPolyhedron A b).Nonempty →
      ∃ x, IsBasicFeasibleSolution (stdFormSystem A b) x) := by
  classical
  constructor
  · -- a nonempty bounded polyhedron contains no line, hence has an extreme point
    intro hne hbdd
    have hnoline : ¬ ContainsLine (polyhedron A b) := by
      rintro ⟨z, hz, d, hd0, hd⟩
      obtain ⟨K, hK⟩ := hbdd
      obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hd0 (funext hcon)
      have hzj : |z j| ≤ K := hK z hz j
      set lam : ℝ := (K + |z j| + 1) / (d j) with hlam
      have hlamd : lam * d j = K + |z j| + 1 := by
        rw [hlam]; exact div_mul_cancel₀ _ hj
      have hmem := hd lam
      have hb : |(z + lam • d) j| ≤ K := hK _ hmem j
      have hval : (z + lam • d) j = z j + lam * d j := rfl
      rw [hval, hlamd] at hb
      have hub := (abs_le.mp hb).2
      have hzj2 : -|z j| ≤ z j := neg_abs_le _
      linarith
    have h26 := polyhedron_extreme_point_existence A b hne
    obtain ⟨x, hx⟩ := (h26.out 1 0).mp hnoline
    have hxP : x ∈ polyhedron A b := hx.1
    have hxc : x ∈ constraintSet (generalFormSystem A b) := by
      rwa [constraintSet_generalForm]
    have hxe : x ∈ Set.extremePoints ℝ (constraintSet (generalFormSystem A b)) := by
      rwa [constraintSet_generalForm]
    have h23 := lp_vertex_extreme_bfs_equiv (generalFormSystem A b) x ⟨x, hxc⟩ hxc
    exact ⟨x, (h23.out 1 2).mp hxe⟩
  · -- a nonempty standard-form polyhedron contains no line: `x ≥ 0` blocks every direction
    intro hne
    obtain ⟨x₀, hx₀⟩ := hne
    have hC : NoLe (stdFormSystem A b) := by
      rintro (i | j) <;> simp [stdFormSystem]
    have hspan : ∀ y : Fin n → ℝ,
        (∀ i, (stdFormSystem A b i).a ⬝ᵥ y = 0) → y = 0 := by
      intro y hy
      funext j
      have h : (Pi.single j (1:ℝ)) ⬝ᵥ y = 0 := hy (Sum.inr j)
      rw [single_dot] at h
      simpa using h
    have hx₀c : x₀ ∈ constraintSet (stdFormSystem A b) := by
      rwa [constraintSet_stdForm]
    exact exists_bfs hC hspan hx₀c
