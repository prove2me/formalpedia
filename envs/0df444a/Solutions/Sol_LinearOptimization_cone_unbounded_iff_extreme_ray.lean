-- Prove2me | solution 1 for LinearOptimization.cone_unbounded_iff_extreme_ray
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T21:30:03.039793+00:00
-- url     : https://prove2.me/submissions/c840dfef-af8d-4699-b6c2-0383dcc3db7c

import Theorems.Thm_LinearOptimization_cone_pointed_iff_extreme_zero
import Theorems.Thm_LinearOptimization_polyhedron_extreme_point_existence
import Theorems.Thm_LinearOptimization_lp_vertex_extreme_bfs_equiv
import Mathlib.Analysis.Convex.Segment
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith

open Matrix

private lemma extreme_nonempty_of_no_line_fintype
    {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (a : ι → (Fin n → ℝ)) (b : ι → ℝ)
    (hne : ({y | ∀ i, b i ≤ a i ⬝ᵥ y} : Set (Fin n → ℝ)).Nonempty)
    (hnoline : ¬ LinearOptimization.ContainsLine
      ({y | ∀ i, b i ≤ a i ⬝ᵥ y} : Set (Fin n → ℝ))) :
    (Set.extremePoints ℝ
      ({y | ∀ i, b i ≤ a i ⬝ᵥ y} : Set (Fin n → ℝ))).Nonempty := by
  classical
  let e := Fintype.equivFin ι
  let A : Matrix (Fin (Fintype.card ι)) (Fin n) ℝ := fun k ↦ a (e.symm k)
  let rhs : Fin (Fintype.card ι) → ℝ := fun k ↦ b (e.symm k)
  have hset : LinearOptimization.polyhedron A rhs =
      ({y | ∀ i, b i ≤ a i ⬝ᵥ y} : Set (Fin n → ℝ)) := by
    ext y
    constructor
    · intro hy i
      have hi := hy (e i)
      simpa [A, rhs, Matrix.mulVec] using hi
    · intro hy k
      simpa [A, rhs, Matrix.mulVec] using hy (e.symm k)
  have hne' : (LinearOptimization.polyhedron A rhs).Nonempty := by
    simpa [hset] using hne
  have hnoline' : ¬ LinearOptimization.ContainsLine
      (LinearOptimization.polyhedron A rhs) := by
    simpa [hset] using hnoline
  have ht := LinearOptimization.polyhedron_extreme_point_existence A rhs hne'
  obtain ⟨y, hy⟩ := (ht.out 1 0).mp hnoline'
  refine ⟨y, ?_⟩
  simpa [hset] using hy

private lemma cone_value_bot_iff_exists_negative {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) :
    LinearOptimization.lpValue c (LinearOptimization.polyhedron A 0) = ⊥ ↔
      ∃ x ∈ LinearOptimization.polyhedron A 0, c ⬝ᵥ x < 0 := by
  classical
  constructor
  · intro hbot
    rw [LinearOptimization.lpValue, iInf_eq_bot] at hbot
    obtain ⟨x, hx⟩ := hbot ((-1 : ℝ) : EReal) (EReal.bot_lt_coe _)
    have hxmem : x ∈ LinearOptimization.polyhedron A 0 := by
      by_contra hnot
      simp [hnot] at hx
    refine ⟨x, hxmem, ?_⟩
    have hcost : c ⬝ᵥ x < -1 := by
      simpa [hxmem] using hx
    linarith
  · rintro ⟨d, hd, hcd⟩
    rw [LinearOptimization.lpValue, iInf_eq_bot]
    intro z hz
    induction z using EReal.rec with
    | bot => exact (lt_irrefl _ hz).elim
    | coe r =>
        let lam : ℝ := max 0 ((-r + 1) / (-(c ⬝ᵥ d)))
        have hden : 0 < -(c ⬝ᵥ d) := by linarith
        have hlam : 0 ≤ lam := le_max_left _ _
        have hge : (-r + 1) / (-(c ⬝ᵥ d)) ≤ lam := le_max_right _ _
        have hkey : -r + 1 ≤ lam * (-(c ⬝ᵥ d)) := by
          calc
            -r + 1 = ((-r + 1) / (-(c ⬝ᵥ d))) * (-(c ⬝ᵥ d)) := by
              rw [div_mul_cancel₀ _ (ne_of_gt hden)]
            _ ≤ lam * (-(c ⬝ᵥ d)) :=
              mul_le_mul_of_nonneg_right hge (le_of_lt hden)
        have hfeas : lam • d ∈ LinearOptimization.polyhedron A 0 := by
          intro i
          have hdi : 0 ≤ A i ⬝ᵥ d := hd i
          change 0 ≤ A i ⬝ᵥ (lam • d)
          rw [dotProduct_smul, smul_eq_mul]
          exact mul_nonneg hlam hdi
        refine ⟨lam • d, ?_⟩
        have hcost : c ⬝ᵥ (lam • d) < r := by
          rw [dotProduct_smul, smul_eq_mul]
          linarith
        simpa [hfeas] using EReal.coe_lt_coe_iff.mpr hcost
    | top =>
        have hzero : (0 : Fin n → ℝ) ∈ LinearOptimization.polyhedron A 0 := by
          intro i
          simp
        refine ⟨0, ?_⟩
        simpa [hzero] using EReal.coe_lt_top (0 : ℝ)

private lemma extreme_normalized_slice_is_ray {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (d : Fin n → ℝ)
    (hd : d ∈ LinearOptimization.polyhedron A 0) (hcost : c ⬝ᵥ d = -1)
    (hext : d ∈ Set.extremePoints ℝ
      ({y | y ∈ LinearOptimization.polyhedron A 0 ∧ c ⬝ᵥ y = -1} :
        Set (Fin n → ℝ))) :
    LinearOptimization.IsExtremeRay A d := by
  classical
  let C : Option (Fin m) → LinearOptimization.LinearConstraint n
    | none => ⟨c, -1, .eq⟩
    | some i => ⟨A i, 0, .ge⟩
  have hCset : LinearOptimization.constraintSet C =
      ({y | y ∈ LinearOptimization.polyhedron A 0 ∧ c ⬝ᵥ y = -1} :
        Set (Fin n → ℝ)) := by
    ext y
    constructor
    · intro hy
      constructor
      · intro i
        have hi := hy (some i)
        have hi' : 0 ≤ A i ⬝ᵥ y := by
          simpa [C, LinearOptimization.LinearConstraint.IsSatisfiedAt] using hi
        exact hi'
      · have hnone := hy none
        simpa [C, LinearOptimization.LinearConstraint.IsSatisfiedAt] using hnone
    · rintro ⟨hy, hcy⟩ o
      cases o with
      | none => simpa [C, LinearOptimization.LinearConstraint.IsSatisfiedAt] using hcy
      | some i =>
          have hi' : 0 ≤ A i ⬝ᵥ y := hy i
          simpa [C, LinearOptimization.LinearConstraint.IsSatisfiedAt] using hi'
  have hdC : d ∈ LinearOptimization.constraintSet C := by
    rw [hCset]
    exact ⟨hd, hcost⟩
  have hextC : d ∈ Set.extremePoints ℝ (LinearOptimization.constraintSet C) := by
    rw [hCset]
    exact hext
  have ht := LinearOptimization.lp_vertex_extreme_bfs_equiv C d ⟨d, hdC⟩ hdC
  have hbfs := (ht.out 1 2).mp hextC
  obtain ⟨heqactive, s, hcard, hactive, hli⟩ := hbfs.1
  have hnoneMem : none ∈ s := by
    by_contra hnone
    let K : Submodule ℝ (Fin n → ℝ) := {
      carrier := {v | v ⬝ᵥ d = 0}
      zero_mem' := by simp
      add_mem' := by
        intro u v hu hv
        change u ⬝ᵥ d = 0 at hu
        change v ⬝ᵥ d = 0 at hv
        change (u + v) ⬝ᵥ d = 0
        rw [add_dotProduct, hu, hv, add_zero]
      smul_mem' := by
        intro r v hv
        change v ⬝ᵥ d = 0 at hv
        change (r • v) ⬝ᵥ d = 0
        rw [smul_dotProduct, hv, smul_zero] }
    have hrange : Set.range (fun i : s ↦ (C i.1).a) ⊆ K := by
      rintro v ⟨i, rfl⟩
      have hi := hactive i.1 i.2
      cases hidx : i.1 with
      | none =>
          exfalso
          exact hnone (by simpa [hidx] using i.2)
      | some j =>
          simpa [K, C, hidx, LinearOptimization.LinearConstraint.IsActiveAt] using hi
    have hspan : Submodule.span ℝ (Set.range (fun i : s ↦ (C i.1).a)) = ⊤ := by
      apply hli.span_eq_top_of_card_eq_finrank'
      simpa [hcard, Module.finrank_pi ℝ]
    have htopK : (⊤ : Submodule ℝ (Fin n → ℝ)) ≤ K := by
      rw [← hspan]
      exact Submodule.span_le.mpr hrange
    have hdd : d ⬝ᵥ d = 0 := htopK (Submodule.mem_top)
    have hdzero : d = 0 := by
      ext j
      change d j = 0
      have hsquares : (∑ k : Fin n, d k * d k) = 0 := by
        simpa [dotProduct] using hdd
      have hle : d j * d j ≤ ∑ k : Fin n, d k * d k :=
        Finset.single_le_sum (fun k hk ↦ mul_self_nonneg (d k)) (Finset.mem_univ j)
      nlinarith [mul_self_nonneg (d j)]
    rw [hdzero, dotProduct_zero] at hcost
    norm_num at hcost
  let t : Finset (Fin m) := Finset.univ.filter (fun i ↦ some i ∈ s)
  let eFun : t → (s.erase none) := fun i ↦ ⟨some i.1, by
    simp only [Finset.mem_erase]
    have hi := i.2
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact ⟨Option.some_ne_none _, hi⟩⟩
  have heFun : Function.Bijective eFun := by
    constructor
    · intro i j hij
      apply Subtype.ext
      have := congrArg (fun o : Option (Fin m) ↦ o) (congrArg Subtype.val hij)
      simpa [eFun] using this
    · intro o
      cases hidx : o.1 with
      | none =>
          have hone : o.1 ≠ none := (Finset.mem_erase.mp o.2).1
          exact (hone hidx).elim
      | some i =>
          have his0 := (Finset.mem_erase.mp o.2).2
          have his : some i ∈ s := by simpa [hidx] using his0
          let ii : t := ⟨i, by simp [t, his]⟩
          refine ⟨ii, ?_⟩
          apply Subtype.ext
          simp [eFun, ii, hidx]
  let e : t ≃ (s.erase none) := Equiv.ofBijective eFun heFun
  have hcardt : t.card = n - 1 := by
    have hc := Fintype.card_congr e
    simp only [Fintype.card_coe] at hc
    rw [Finset.card_erase_of_mem hnoneMem, hcard] at hc
    exact hc
  have hliErase : LinearIndependent ℝ
      (fun i : (s.erase none) ↦ (C i.1).a) := by
    apply hli.comp (fun i : (s.erase none) ↦
      (⟨i.1, Finset.mem_of_mem_erase i.2⟩ : s))
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun z : s ↦ z.1) hij
  have hliT : LinearIndependent ℝ (fun i : t ↦ A i.1) := by
    have hcomp := hliErase.comp e e.injective
    simpa [e, eFun, C, Function.comp_def] using hcomp
  refine ⟨hd, ?_, t, hcardt, ?_, hliT⟩
  · intro hdzero
    rw [hdzero, dotProduct_zero] at hcost
    norm_num at hcost
  · intro i hi
    have his : some i ∈ s := by
      simpa only [t, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    have hact := hactive (some i) his
    simpa [C, LinearOptimization.LinearConstraint.IsActiveAt] using hact

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (hpointed : LinearOptimization.IsPointedCone
      (LinearOptimization.polyhedron A 0)) :
    LinearOptimization.lpValue c (LinearOptimization.polyhedron A 0) = ⊥ ↔
      ∃ d : Fin n → ℝ,
        LinearOptimization.IsExtremeRay A d ∧ c ⬝ᵥ d < 0 := by
  classical
  rw [cone_value_bot_iff_exists_negative]
  constructor
  · rintro ⟨x, hx, hcx⟩
    let alpha : ℝ := (-1) / (c ⬝ᵥ x)
    have halpha : 0 < alpha := div_pos_of_neg_of_neg (by norm_num) hcx
    let xnorm : Fin n → ℝ := alpha • x
    have hxnorm : xnorm ∈ LinearOptimization.polyhedron A 0 := by
      intro i
      have hxi : 0 ≤ A i ⬝ᵥ x := hx i
      change 0 ≤ A i ⬝ᵥ (alpha • x)
      rw [dotProduct_smul, smul_eq_mul]
      exact mul_nonneg (le_of_lt halpha) hxi
    have hcostnorm : c ⬝ᵥ xnorm = -1 := by
      rw [show xnorm = alpha • x by rfl, dotProduct_smul, smul_eq_mul]
      exact div_mul_cancel₀ (-1) (ne_of_lt hcx)
    let B : ((Fin m) ⊕ Bool) → (Fin n → ℝ)
      | Sum.inl i => A i
      | Sum.inr false => c
      | Sum.inr true => -c
    let rhs : ((Fin m) ⊕ Bool) → ℝ
      | Sum.inl _ => 0
      | Sum.inr false => -1
      | Sum.inr true => 1
    have hBset : ({y | ∀ q, rhs q ≤ B q ⬝ᵥ y} : Set (Fin n → ℝ)) =
        ({y | y ∈ LinearOptimization.polyhedron A 0 ∧ c ⬝ᵥ y = -1} :
          Set (Fin n → ℝ)) := by
      ext y
      constructor
      · intro hy
        constructor
        · intro i
          have hi' : 0 ≤ A i ⬝ᵥ y := by simpa [B, rhs] using hy (Sum.inl i)
          exact hi'
        · have hlo := hy (Sum.inr false)
          have hhi := hy (Sum.inr true)
          simp [B, rhs, dotProduct] at hlo hhi
          change c ⬝ᵥ y = -1
          rw [dotProduct]
          linarith
      · rintro ⟨hy, hcy⟩ q
        rcases q with i | s
        · have hi' : 0 ≤ A i ⬝ᵥ y := hy i
          simpa [B, rhs] using hi'
        · cases s with
          | false =>
              change -1 ≤ c ⬝ᵥ y
              linarith
          | true =>
              change 1 ≤ (-c) ⬝ᵥ y
              have hcy' : (∑ i : Fin n, c i * y i) = -1 := by
                simpa [dotProduct] using hcy
              simp only [dotProduct, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
              linarith
    have hneB : ({y | ∀ q, rhs q ≤ B q ⬝ᵥ y} :
        Set (Fin n → ℝ)).Nonempty := by
      rw [hBset]
      exact ⟨xnorm, hxnorm, hcostnorm⟩
    have hnolineCone : ¬ LinearOptimization.ContainsLine
        (LinearOptimization.polyhedron A 0) :=
      (LinearOptimization.cone_pointed_iff_extreme_zero A).1.mp hpointed
    have hnolineB : ¬ LinearOptimization.ContainsLine
        ({y | ∀ q, rhs q ≤ B q ⬝ᵥ y} : Set (Fin n → ℝ)) := by
      intro hline
      apply hnolineCone
      rcases hline with ⟨y, hy, d, hdne, hline⟩
      have hySlice : y ∈
          ({z | z ∈ LinearOptimization.polyhedron A 0 ∧ c ⬝ᵥ z = -1} :
            Set (Fin n → ℝ)) := by
        rw [← hBset]
        exact hy
      have hy' : y ∈ LinearOptimization.polyhedron A 0 := hySlice.1
      refine ⟨y, hy', d, hdne, ?_⟩
      intro lam
      have hlamSlice : y + lam • d ∈
          ({z | z ∈ LinearOptimization.polyhedron A 0 ∧ c ⬝ᵥ z = -1} :
            Set (Fin n → ℝ)) := by
        rw [← hBset]
        exact hline lam
      exact hlamSlice.1
    obtain ⟨d, hdext⟩ := extreme_nonempty_of_no_line_fintype B rhs hneB hnolineB
    have hdext' : d ∈ Set.extremePoints ℝ
        ({y | y ∈ LinearOptimization.polyhedron A 0 ∧ c ⬝ᵥ y = -1} :
          Set (Fin n → ℝ)) := by
      rw [← hBset]
      exact hdext
    have hdslice := hdext'.1
    refine ⟨d, extreme_normalized_slice_is_ray A c d hdslice.1 hdslice.2 hdext', ?_⟩
    have hcd : c ⬝ᵥ d = -1 := hdslice.2
    linarith
  · rintro ⟨d, hd, hcd⟩
    exact ⟨d, hd.1, hcd⟩
