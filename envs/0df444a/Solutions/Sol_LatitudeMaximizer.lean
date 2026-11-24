-- Prove2me | solution 1 for LatitudeMaximizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:26:55.207355+00:00
-- url     : https://prove2.me/submissions/bdae14c1-d00d-46cc-9ba2-0236cd165431

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_LatitudeMaximizer

set_option autoImplicit false
@[expose] public section
public section
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) {e : EuclideanSpace ℝ (Fin n)}
    (he : ‖e‖ = 1) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f) :
    ∃ v₀ : EuclideanSpace ℝ (Fin n), ‖v₀‖ = 1 ∧ inner ℝ e v₀ = (0 : ℝ) ∧
      ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → inner ℝ e v = (0 : ℝ) → f v ≤ f v₀ := by
  classical
  have he0 : e ≠ 0 := by
    intro h; rw [h] at he; simp at he
  set S : Set (EuclideanSpace ℝ (Fin n)) :=
    {v | ‖v‖ = 1 ∧ inner ℝ e v = (0 : ℝ)} with hS
  have hSeq : S = Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
      ∩ {v | inner ℝ e v = (0 : ℝ)} := by
    ext v; simp [hS, Set.mem_inter_iff, mem_sphere_iff_norm, sub_zero, and_comm]
  have hclosed : IsClosed {v : EuclideanSpace ℝ (Fin n) | inner ℝ e v = (0 : ℝ)} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hcompact : IsCompact S := by
    rw [hSeq]; exact (isCompact_sphere _ _).inter_right hclosed
  have hne : S.Nonempty := by
    have hKfr : Module.finrank ℝ (ℝ ∙ e) = 1 := finrank_span_singleton he0
    have hsum := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ)
      (E := EuclideanSpace ℝ (Fin n)) (ℝ ∙ e)
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
    have hpos : 0 < Module.finrank ℝ ((ℝ ∙ e)ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) := by
      omega
    have hnebot : ((ℝ ∙ e)ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) ≠ ⊥ := by
      intro h; rw [h] at hpos; simp at hpos
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hnebot
    have hew : inner ℝ e w = (0 : ℝ) := by
      have := hw e (Submodule.mem_span_singleton_self e)
      simpa [real_inner_comm] using this
    have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw0
    refine ⟨(‖w‖⁻¹ : ℝ) • w, ?_, ?_⟩
    · simp [norm_smul, inv_mul_cancel₀ hwn]
    · simp [inner_smul_right, hew]
  obtain ⟨v₀, hv₀S, hmax⟩ := hcompact.exists_isMaxOn hne hf.continuousOn
  exact ⟨v₀, hv₀S.1, hv₀S.2, fun v hv hev => hmax ⟨hv, hev⟩⟩
