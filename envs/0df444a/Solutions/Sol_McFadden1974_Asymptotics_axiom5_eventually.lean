-- Prove2me | solution 1 for McFadden1974.Asymptotics.axiom5_eventually
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T14:57:26.892717+00:00
-- url     : https://prove2.me/submissions/93683743-605a-411d-b8b1-6bc6e409e98c

import Mathlib
import Definitions.Def_McFadden1974_Asymptotics_LogitSample

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Matrix in
theorem McFadden1974.Asymptotics.axiom5_eventually_aux {K : ℕ}
    (D : McFadden1974.Asymptotics.SerialData K) (θ₀ : EuclideanSpace ℝ (Fin K))
    (Ωlim : Matrix (Fin K) (Fin K) ℝ)
    (hT : Tendsto (fun q : ℕ => (q : ℝ)⁻¹ •
      ∑ m ∈ Finset.range q, McFadden1974.Asymptotics.momentMatrix D θ₀ m) atTop (𝓝 Ωlim))
    (hpd : Ωlim.PosDef) (γ : EuclideanSpace ℝ (Fin K))
    (hγ : ∀ m (i : Fin (D.J m)),
      inner ℝ (D.z m i - McFadden1974.Asymptotics.zbar D m θ₀) γ = 0) : γ = 0 := by
  by_contra hne
  set x : Fin K → ℝ := WithLp.ofLp γ with hx
  have hx0 : x ≠ 0 := by
    intro h
    apply hne
    have : γ = WithLp.toLp 2 x := rfl
    rw [this, h]
    rfl
  have hm : ∀ m, McFadden1974.Asymptotics.momentMatrix D θ₀ m *ᵥ x = 0 := by
    intro m
    unfold McFadden1974.Asymptotics.momentMatrix
    rw [Matrix.sum_mulVec]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
    have h1 := hγ m i
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h1
    have h2 : WithLp.ofLp (D.z m i - McFadden1974.Asymptotics.zbar D m θ₀) ⬝ᵥ x = 0 := by
      rw [dotProduct_comm]; simpa using h1
    rw [h2]
    simp
  have hseq : ∀ q : ℕ, ((q : ℝ)⁻¹ •
      ∑ m ∈ Finset.range q, McFadden1974.Asymptotics.momentMatrix D θ₀ m) *ᵥ x = 0 := by
    intro q
    rw [Matrix.smul_mulVec, Matrix.sum_mulVec]
    simp [hm]
  have hclosed : IsClosed {A : Matrix (Fin K) (Fin K) ℝ | A *ᵥ x = 0} :=
    isClosed_eq (Continuous.matrix_mulVec continuous_id continuous_const) continuous_const
  have hlim : Ωlim *ᵥ x = 0 :=
    hclosed.mem_of_tendsto hT (Eventually.of_forall hseq)
  have := hpd.dotProduct_mulVec_pos hx0
  rw [hlim] at this
  simp at this

open MeasureTheory ProbabilityTheory Filter Topology Matrix McFadden1974.Asymptotics in
theorem solution {K : ℕ} (D : SerialData K) (Jstar : ℕ) (M : ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin K)) (Ωlim : Matrix (Fin K) (Fin K) ℝ)
    (h7 : Axiom7 D Jstar M θ₀ Ωlim) :
    ∃ q₀ : ℕ, ∀ q ≥ q₀,
      Submodule.span ℝ {v | ∃ m < q, ∃ i : Fin (D.J m), v = D.z m i - zbar D m θ₀} = ⊤ := by
  let W : ℕ → Submodule ℝ (EuclideanSpace ℝ (Fin K)) := fun q =>
    Submodule.span ℝ {v | ∃ m < q, ∃ i : Fin (D.J m),
      v = D.z m i - McFadden1974.Asymptotics.zbar D m θ₀}
  have hmono : Monotone W := by
    intro a b hab
    apply Submodule.span_mono
    rintro v ⟨m, hm, i, rfl⟩
    exact ⟨m, lt_of_lt_of_le hm hab, i, rfl⟩
  obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian (R := ℝ)
    (M := EuclideanSpace ℝ (Fin K))).mpr inferInstance ⟨W, hmono⟩
  have hmem : ∀ m (i : Fin (D.J m)),
      D.z m i - McFadden1974.Asymptotics.zbar D m θ₀ ∈ W n := by
    intro m i
    have h1 : D.z m i - McFadden1974.Asymptotics.zbar D m θ₀ ∈ W (max n (m + 1)) :=
      Submodule.subset_span ⟨m, by omega, i, rfl⟩
    have h2 := hn (max n (m + 1)) (le_max_left _ _)
    simp only [OrderHom.coe_mk] at h2
    rw [h2]
    exact h1
  have htop : W n = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff]
    rw [Submodule.eq_bot_iff]
    intro γ hγ
    refine McFadden1974.Asymptotics.axiom5_eventually_aux D θ₀ Ωlim h7.tendsto_avg h7.posDef γ ?_
    intro m i
    exact Submodule.inner_right_of_mem_orthogonal (hmem m i) hγ
  refine ⟨n, fun q hq => ?_⟩
  have := hmono hq
  rw [htop] at this
  exact top_le_iff.mp this
