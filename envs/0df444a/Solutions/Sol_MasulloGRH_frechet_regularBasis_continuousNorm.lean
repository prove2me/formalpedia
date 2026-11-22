-- Prove2me | solution 1 for MasulloGRH.frechet_regularBasis_continuousNorm
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T17:59:01.83658+00:00
-- url     : https://prove2.me/submissions/498b592a-9f78-4f85-b503-0d8622a18883

import Definitions.Def_MasulloGRH_SchauderBases
import Theorems.Thm_MasulloGRH_schauderBasis_equicontinuous_frechet_or_strictLF

open Filter Topology MasulloGRH Set
set_option autoImplicit false

theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hF : IsFrechet E) (x : ℕ → E) (f : ℕ → StrongDual ℂ E) (hx : IsSchauderBasis x f)
    (hreg : IsRegularBasis x) :
    (∃ q : Seminorm ℂ E, Continuous q ∧ ∀ u : E, q u = 0 → u = 0) ∧
      ¬ ∃ S : Submodule ℂ E, IsClosed (S : Set E) ∧ S.ClosedComplemented ∧
        Nonempty (S ≃L[ℂ] (ℕ → ℂ)) := by
  classical
  have : T2Space E := hF.2.1.1
  have hEqui := schauderBasis_equicontinuous_frechet_or_strictLF E
    ⟨hF.1, hF.2.1.1⟩ x f hx (Or.inl hF)
  obtain ⟨ι, _, p, hp⟩ := hF.1
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have : ContinuousSMul ℂ E := hp.continuousSMul
  obtain ⟨U, hU, hAvoid⟩ := hreg
  obtain ⟨I, r, hr, hSub⟩ := (hp.mem_nhds_iff 0 U).mp hU
  let p₀ := I.sup p
  have hHalf : p₀.ball 0 (r / 2) ∈ 𝓝 (0 : E) :=
    hp.hasBasis_zero_ball.mem_iff.mpr ⟨(I, r / 2), half_pos hr, Subset.rfl⟩
  obtain ⟨V, hV, hControl⟩ := hEqui (p₀.ball 0 (r / 2)) hHalf
  obtain ⟨J, ε, hε, hSmall⟩ := (hp.mem_nhds_iff 0 V).mp hV
  let q := J.sup p
  have hqCont : Continuous q := Seminorm.continuous' <|
    mem_of_superset
      (hp.hasBasis_zero_ball.mem_iff.mpr ⟨(J, ε), hε, Subset.rfl⟩)
      (Seminorm.ball_subset_closedBall q 0 ε)
  have hTerm (u : E) (hu : u ∈ V) (n : ℕ) : p₀ (f n u • x n) < r := by
    cases n with
    | zero =>
      have h := (p₀.mem_ball_zero.mp (hControl 0 u hu)).trans (half_lt_self hr)
      simpa [basicProjection] using h
    | succ n =>
      have hSplit :
          basicProjection x f (n + 1) u =
            basicProjection x f n u + f (n + 1) u • x (n + 1) := by
        simp only [basicProjection, Finset.sum_range_succ
          (f := fun m => f m u • x m) (n + 1)]
      have hDiff : f (n + 1) u • x (n + 1) =
          basicProjection x f (n + 1) u - basicProjection x f n u := by
        rw [hSplit, add_sub_cancel_left]
      rw [hDiff]
      refine (map_sub_le_add p₀ _ _).trans_lt ?_
      have h₁ := p₀.mem_ball_zero.mp (hControl (n + 1) u hu)
      have h₂ := p₀.mem_ball_zero.mp (hControl n u hu)
      linarith
  have hqZero (u : E) (hu : q u = 0) : u = 0 := by
    have hCoeff (n : ℕ) : f n u = 0 := by
      by_contra hne
      let c : ℂ := (f n u)⁻¹
      have hcu : q (c • u) = 0 := by rw [map_smul_eq_mul, hu, mul_zero]
      have hcV : c • u ∈ V := hSmall (q.mem_ball_zero.mpr (hcu ▸ hε))
      have hxU : x n ∈ U := by
        apply hSub
        apply p₀.mem_ball_zero.mpr
        have h := hTerm (c • u) hcV n
        have hScalar : f n (c • u) = 1 := by
          rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hne]
        simpa only [hScalar, one_smul] using h
      exact hAvoid n hxU
    have hExp := hx.expansion u
    simp only [basicProjection, hCoeff, zero_smul, Finset.sum_const_zero] at hExp
    exact tendsto_nhds_unique hExp tendsto_const_nhds
  refine ⟨⟨q, hqCont, hqZero⟩, ?_⟩
  rintro ⟨S, _, _, ⟨e⟩⟩
  let A (v : ℕ → ℂ) : E := (e.symm v : S)
  have hA : Continuous A := continuous_subtype_val.comp e.symm.continuous
  have hA0 : A 0 = 0 := by simp [A]
  have hNeighborhood : {v : ℕ → ℂ | q (A v) < 1} ∈ 𝓝 (0 : ℕ → ℂ) :=
    (isOpen_lt (hqCont.comp hA) continuous_const).mem_nhds (by simp [hA0])
  rw [nhds_pi, Filter.mem_pi'] at hNeighborhood
  obtain ⟨K, B, hB, hSubset⟩ := hNeighborhood
  obtain ⟨i, hi⟩ := K.exists_notMem
  let v : ℕ → ℂ := Pi.single i 1
  have hv : v ≠ 0 := by
    intro h
    have hv' := congrFun h i
    simp [v] at hv'
  have hAv : A v ≠ 0 := by
    intro h
    apply hv
    exact e.symm.injective (Subtype.ext (by simpa [A] using h))
  have hPos : 0 < q (A v) :=
    lt_of_le_of_ne (apply_nonneg q _) (Ne.symm (fun h => hAv (hqZero _ h)))
  let c : ℂ := ((q (A v))⁻¹ : ℝ)
  have hInside : q (A (c • v)) < 1 := by
    apply hSubset
    intro j hj
    have hji : j ≠ i := by
      intro h
      exact hi (h ▸ hj)
    have h0 : (0 : ℂ) ∈ B j := mem_of_mem_nhds (hB j)
    simpa [v, Pi.smul_apply, Pi.single_eq_of_ne hji] using h0
  have hAs : A (c • v) = c • A v := by simp [A]
  rw [hAs, map_smul_eq_mul] at hInside
  have hc : ‖c‖ = (q (A v))⁻¹ := by
    simp [c, Complex.norm_real, Real.norm_eq_abs]
  rw [hc, inv_mul_cancel₀ hPos.ne'] at hInside
  exact (lt_irrefl _ hInside)
