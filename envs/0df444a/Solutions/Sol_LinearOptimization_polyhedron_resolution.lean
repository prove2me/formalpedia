-- Prove2me | solution 1 for LinearOptimization.polyhedron_resolution
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T21:47:28.438637+00:00
-- url     : https://prove2.me/submissions/8ff7c519-d72b-402d-9d9e-91c12011ec29

import Definitions.Def_LinearOptimization_FinitelyGeneratedSet
import Theorems.Thm_LinearOptimization_cone_pointed_iff_extreme_zero
import Theorems.Thm_LinearOptimization_cone_unbounded_iff_extreme_ray
import Theorems.Thm_LinearOptimization_farkas_inequality_form_fintype
import Theorems.Thm_LinearOptimization_finitely_generated_is_polyhedron
import Theorems.Thm_LinearOptimization_lp_extreme_point_optimality
import Theorems.Thm_LinearOptimization_polyhedron_closed
import Theorems.Thm_LinearOptimization_polyhedron_extreme_point_existence
import Theorems.Thm_LinearOptimization_separating_hyperplane_polyhedron
import Mathlib.Tactic.Linarith

open Matrix

private lemma polyhedron_convex {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Convex ℝ (LinearOptimization.polyhedron A b) := by
  intro u hu v hv a c ha hc hac i
  change b i ≤ A i ⬝ᵥ (a • u + c • v)
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
    smul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left (hu i) ha
  have h2 := mul_le_mul_of_nonneg_left (hv i) hc
  calc
    b i = a * b i + c * b i := by rw [← add_mul, hac, one_mul]
    _ ≤ a * (A i ⬝ᵥ u) + c * (A i ⬝ᵥ v) := add_le_add h1 h2

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
    have hcost : c ⬝ᵥ x < -1 := by simpa [hxmem] using hx
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
          change 0 ≤ A i ⬝ᵥ (lam • d)
          rw [dotProduct_smul, smul_eq_mul]
          exact mul_nonneg hlam (hd i)
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

private lemma polyhedron_value_bot_imp_cone_value_bot {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hne : (LinearOptimization.polyhedron A b).Nonempty)
    (hbot : LinearOptimization.lpValue c (LinearOptimization.polyhedron A b) = ⊥) :
    LinearOptimization.lpValue c (LinearOptimization.polyhedron A 0) = ⊥ := by
  classical
  rw [cone_value_bot_iff_exists_negative]
  by_contra hneg
  push_neg at hneg
  have hvalid : ∀ d : Fin n → ℝ, (-A).mulVec d ≤ 0 → (-c) ⬝ᵥ d ≤ 0 := by
    intro d hd
    have hdcone : d ∈ LinearOptimization.polyhedron A 0 := by
      intro i
      have hi := hd i
      simp only [Matrix.mulVec, dotProduct, Matrix.neg_apply, Pi.zero_apply,
        neg_mul, Finset.sum_neg_distrib] at hi
      change 0 ≤ A i ⬝ᵥ d
      exact neg_nonpos.mp hi
    have hnonneg : 0 ≤ c ⬝ᵥ d := hneg d hdcone
    simpa [dotProduct] using neg_nonpos.mpr hnonneg
  have hzero : ∃ d : Fin n → ℝ, (-A).mulVec d ≤ 0 := by
    refine ⟨0, ?_⟩
    intro i
    simp [Matrix.mulVec]
  obtain ⟨p, hp, hstat, hpobj⟩ :=
    (LinearOptimization.farkas_inequality_form_fintype (-A) 0 (-c) 0 hzero).mp hvalid
  have hstat' : Aᵀ.mulVec p = c := by
    funext j
    have hj := congrFun hstat j
    simpa [Matrix.mulVec, dotProduct] using hj
  have hlower_real : ∀ y ∈ LinearOptimization.polyhedron A b,
      p ⬝ᵥ b ≤ c ⬝ᵥ y := by
    intro y hy
    calc
      p ⬝ᵥ b ≤ p ⬝ᵥ A.mulVec y := by
        exact Finset.sum_le_sum fun i _ ↦
          mul_le_mul_of_nonneg_left (hy i) (hp i)
      _ = Aᵀ.mulVec p ⬝ᵥ y := by
        rw [Matrix.dotProduct_mulVec]
        congr 1
        funext j
        simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
      _ = c ⬝ᵥ y := by rw [hstat']
  have hlower : ((p ⬝ᵥ b : ℝ) : EReal) ≤
      LinearOptimization.lpValue c (LinearOptimization.polyhedron A b) := by
    rw [LinearOptimization.lpValue]
    apply le_iInf
    intro y
    apply le_iInf
    intro hy
    exact EReal.coe_le_coe_iff.mpr (hlower_real y hy)
  rw [hbot] at hlower
  exact (not_le_of_gt (EReal.bot_lt_coe (p ⬝ᵥ b))) hlower

private lemma generator_mem_finitelyGeneratedSet {n k r : ℕ}
    (x : Fin k → (Fin n → ℝ)) (w : Fin r → (Fin n → ℝ)) (i : Fin k) :
    x i ∈ LinearOptimization.finitelyGeneratedSet x w := by
  classical
  refine ⟨Pi.single i 1, 0, ?_, ?_, ?_, ?_⟩
  · intro q
    by_cases h : q = i <;> simp [Pi.single_apply, h]
  · intro j
    simp
  · simp [Pi.single_apply]
  · ext a
    simp [Pi.single_apply]

private lemma generator_add_ray_mem_finitelyGeneratedSet {n k r : ℕ}
    (x : Fin k → (Fin n → ℝ)) (w : Fin r → (Fin n → ℝ))
    (i : Fin k) (j : Fin r) (t : ℝ) (ht : 0 ≤ t) :
    x i + t • w j ∈ LinearOptimization.finitelyGeneratedSet x w := by
  classical
  refine ⟨Pi.single i 1, Pi.single j t, ?_, ?_, ?_, ?_⟩
  · intro q
    by_cases h : q = i <;> simp [Pi.single_apply, h]
  · intro q
    by_cases h : q = j <;> simp [Pi.single_apply, h, ht]
  · simp [Pi.single_apply]
  · ext a
    simp [Pi.single_apply]

private lemma finitelyGeneratedSet_subset_polyhedron {m n k r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin k → (Fin n → ℝ)) (w : Fin r → (Fin n → ℝ))
    (hx : ∀ i, x i ∈ LinearOptimization.polyhedron A b)
    (hw : ∀ j, w j ∈ LinearOptimization.polyhedron A 0) :
    LinearOptimization.finitelyGeneratedSet x w ⊆
      LinearOptimization.polyhedron A b := by
  classical
  rintro y ⟨lam, theta, hlam, htheta, hsum, rfl⟩ q
  have hconv : b q ≤ ∑ i : Fin k, lam i * (A q ⬝ᵥ x i) := by
    calc
      b q = ∑ i : Fin k, lam i * b q := by
        rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ i : Fin k, lam i * (A q ⬝ᵥ x i) := by
        exact Finset.sum_le_sum fun i _ ↦
          mul_le_mul_of_nonneg_left (hx i q) (hlam i)
  have hray : 0 ≤ ∑ j : Fin r, theta j * (A q ⬝ᵥ w j) := by
    exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (htheta j) (hw j q)
  change b q ≤ A q ⬝ᵥ
    ((∑ i : Fin k, lam i • x i) + ∑ j : Fin r, theta j • w j)
  rw [dotProduct_add]
  simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul]
  exact hconv.trans (le_add_of_nonneg_right hray)

theorem solution {m n k r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hne : (LinearOptimization.polyhedron A b).Nonempty)
    (x : Fin k → (Fin n → ℝ)) (hk : 0 < k)
    (hx : Set.extremePoints ℝ (LinearOptimization.polyhedron A b) = Set.range x)
    (w : Fin r → (Fin n → ℝ))
    (hw : LinearOptimization.IsCompleteExtremeRaySet A w) :
    LinearOptimization.finitelyGeneratedSet x w =
      LinearOptimization.polyhedron A b := by
  classical
  let i0 : Fin k := ⟨0, hk⟩
  have hxP : ∀ i, x i ∈ LinearOptimization.polyhedron A b := by
    intro i
    have hi : x i ∈ Set.extremePoints ℝ
        (LinearOptimization.polyhedron A b) := by
      rw [hx]
      exact Set.mem_range_self i
    exact hi.1
  have hextP : (Set.extremePoints ℝ
      (LinearOptimization.polyhedron A b)).Nonempty := by
    exact ⟨x i0, by rw [hx]; exact Set.mem_range_self i0⟩
  have hwcone : ∀ j, w j ∈ LinearOptimization.polyhedron A 0 := by
    intro j
    exact (hw.1 j).1
  have hQP : LinearOptimization.finitelyGeneratedSet x w ⊆
      LinearOptimization.polyhedron A b :=
    finitelyGeneratedSet_subset_polyhedron A b x w hxP hwcone
  obtain ⟨mQ, AQ, bQ, hQpoly⟩ :=
    LinearOptimization.finitely_generated_is_polyhedron x w
  have hQne : (LinearOptimization.finitelyGeneratedSet x w).Nonempty :=
    ⟨x i0, generator_mem_finitelyGeneratedSet x w i0⟩
  have hQclosed : IsClosed (LinearOptimization.finitelyGeneratedSet x w) := by
    rw [hQpoly]
    exact LinearOptimization.polyhedron_closed AQ bQ
  have hQconv : Convex ℝ (LinearOptimization.finitelyGeneratedSet x w) := by
    rw [hQpoly]
    exact polyhedron_convex AQ bQ
  apply Set.Subset.antisymm hQP
  intro z hz
  by_contra hzQ
  obtain ⟨p, hsep⟩ :=
    LinearOptimization.separating_hyperplane_polyhedron
      (LinearOptimization.finitelyGeneratedSet x w) hQne hQclosed hQconv z hzQ
  have hpw : ∀ j, 0 ≤ p ⬝ᵥ w j := by
    intro j
    by_contra hnot
    have hjneg : p ⬝ᵥ w j < 0 := lt_of_not_ge hnot
    let t : ℝ := max 0
      ((p ⬝ᵥ x i0 - p ⬝ᵥ z + 1) / (-(p ⬝ᵥ w j)))
    have hden : 0 < -(p ⬝ᵥ w j) := by linarith
    have ht : 0 ≤ t := le_max_left _ _
    have hge : (p ⬝ᵥ x i0 - p ⬝ᵥ z + 1) /
        (-(p ⬝ᵥ w j)) ≤ t := le_max_right _ _
    have hkey : p ⬝ᵥ x i0 - p ⬝ᵥ z + 1 ≤
        t * (-(p ⬝ᵥ w j)) := by
      calc
        p ⬝ᵥ x i0 - p ⬝ᵥ z + 1 =
            ((p ⬝ᵥ x i0 - p ⬝ᵥ z + 1) /
              (-(p ⬝ᵥ w j))) * (-(p ⬝ᵥ w j)) := by
                rw [div_mul_cancel₀ _ (ne_of_gt hden)]
        _ ≤ t * (-(p ⬝ᵥ w j)) :=
          mul_le_mul_of_nonneg_right hge (le_of_lt hden)
    have hmember := generator_add_ray_mem_finitelyGeneratedSet x w i0 j t ht
    have hs := hsep (x i0 + t • w j) hmember
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at hs
    linarith
  have hbasis : ∃ s : Finset (Fin m), s.card = n ∧
      LinearIndependent ℝ (fun i : s ↦ A i.1) :=
    (LinearOptimization.polyhedron_extreme_point_existence A b hne).out 0 2 |>.mp hextP
  have hnolineCone : ¬ LinearOptimization.ContainsLine
      (LinearOptimization.polyhedron A 0) :=
    (LinearOptimization.cone_pointed_iff_extreme_zero A).2.mpr hbasis
  have hpointed : LinearOptimization.IsPointedCone
      (LinearOptimization.polyhedron A 0) :=
    (LinearOptimization.cone_pointed_iff_extreme_zero A).1.mpr hnolineCone
  rcases LinearOptimization.lp_extreme_point_optimality A b p hextP with
    hbot | ⟨y, hyext, hyopt⟩
  · have hconebot := polyhedron_value_bot_imp_cone_value_bot A b p hne hbot
    obtain ⟨d, hdext, hdneg⟩ :=
      (LinearOptimization.cone_unbounded_iff_extreme_ray A p hpointed).mp hconebot
    obtain ⟨j, ⟨t, ht, hdt⟩, _⟩ := hw.2 d hdext
    have hjnonneg := hpw j
    rw [hdt, dotProduct_smul, smul_eq_mul] at hdneg
    nlinarith
  · have hyrange : y ∈ Set.range x := by
      rw [← hx]
      exact hyext
    obtain ⟨i, rfl⟩ := hyrange
    have hoptle := hyopt.2 z hz
    have hstrict := hsep (x i) (generator_mem_finitelyGeneratedSet x w i)
    linarith
