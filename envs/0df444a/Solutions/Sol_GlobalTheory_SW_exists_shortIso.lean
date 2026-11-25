-- Prove2me | solution 1 for GlobalTheory.SW.exists_shortIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:11:35.705021+00:00
-- url     : https://prove2.me/submissions/4f78171a-a903-4947-8595-5ebe1811f023

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_hval_eq
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_short
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_gram_le
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_comb_le
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_emb_cc
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_ccT_mul
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_intM_mul
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_intM_ccT
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_li_of_mul
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_det_le
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_exists_int_rows
import Theorems.Thm_GlobalTheory_SW_Base_ccT_mul
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory.SW.MinkowskiProductBounds
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (N D : ℕ) (ε : ℝ), 0 < D → 0 < ε →
    ∃ C : ℝ, ShortIso Ψ N D ε C := by
  intro E _ _ _ Ψ h N D ε hD hε
  classical
  obtain ⟨n, C, hC⟩ := short h (2 * N) (∏ _τ : Ψ, (D : ℝ) ^ (2 * N)) ε hε
  let F : Set (Matrix (Fin n) (Fin n) E) :=
    {Γ | ∀ i j, Γ i j ∈ {x : E | IsIntegral ℤ x ∧ ∀ σ : E →+* ℂ, ‖σ x‖ ≤ D * C}}
  have hF : F.Finite :=
    Set.Finite.pi' fun _ => Set.Finite.pi' fun _ => Embeddings.finite_of_norm_le E ℂ _
  have hex : ∀ Γ : Matrix (Fin n) (Fin n) E, ∃ T : Matrix (Fin N) (Fin n) E,
      (∃ T : Matrix (Fin N) (Fin n) E, IntM T ∧ IsoRows' Γ T) → IntM T ∧ IsoRows' Γ T := by
    intro Γ
    by_cases hΓ : ∃ T : Matrix (Fin N) (Fin n) E, IntM T ∧ IsoRows' Γ T
    · exact ⟨hΓ.choose, fun _ => hΓ.choose_spec⟩
    · exact ⟨0, fun h => absurd h hΓ⟩
  choose T hT using hex
  obtain ⟨M, hM⟩ := ((hF.prod (Set.finite_univ (α := Ψ × Fin N × Fin n))).image
    fun p => ‖p.2.1.1 (T p.1 p.2.2.1 p.2.2.2)‖).bddAbove
  refine ⟨(n * (M * √C)) ^ 2, fun G H hG h0 hD1 hD2 ⟨W, hW⟩ hH hmin => ?_⟩
  obtain ⟨V, hV, ⟨S, hS⟩, hVC⟩ := hC H (fun τ => (hH τ).1) (det_le h hD h0 hD2 hH) hmin
  set Γ := V * ((D : E) • G) * ccT V with hΓ
  have hΓF : Γ ∈ F := by
    intro i j
    refine ⟨intM_mul (intM_mul hV hD1) (intM_ccT hV) i j, ?_⟩
    have key : ∀ τ : Ψ, ‖τ.1 (Γ i j)‖ ≤ D * C := by
      intro τ
      have h1 : (G.map τ.1)ᴴ = G.map τ.1 := by
        ext a b
        have := congrArg τ.1 (congrFun (congrFun hG a) b)
        simpa [ccT, emb_cc] using this
      have h2 : (G.map τ.1).det ≠ 0 := by
        rw [show (G.map τ.1).det = τ.1 G.det from (RingHom.map_det _ _).symm]
        simpa using h0
      have h3 := gram_le (hH τ).1 h1 h2 (hH τ).2 _ _ (hVC i τ) (hVC j τ)
      have h4 : τ.1 (Γ i j) = D * ((fun a => τ.1 (V i a)) ⬝ᵥ G.map τ.1 *ᵥ
          star fun a => τ.1 (V j a)) := by
        rw [hΓ, Matrix.mul_assoc]
        simp [Matrix.mul_apply, ccT, emb_cc, dotProduct, mulVec, Finset.mul_sum, mul_assoc,
          mul_left_comm]
      rw [h4, norm_mul, Complex.norm_natCast]
      gcongr
    intro σ
    by_cases hσ : σ ∈ Ψ
    · exact key ⟨σ, hσ⟩
    · simpa using key ⟨ComplexEmbedding.conjugate σ, by have := h σ; tauto⟩
  obtain ⟨hT1, hT2, hT3⟩ := hT Γ (exists_int_rows hD h0 hW hS)
  refine ⟨T Γ * V, intM_mul hT1 hV, ⟨?_, ?_⟩, fun i τ => ?_⟩
  · refine li_of_mul (R := ((D : E) • G) * ccT V) ?_
    rwa [Matrix.mul_assoc, ← Matrix.mul_assoc V]
  · have hD' : (D : E) ≠ 0 := by exact_mod_cast hD.ne'
    refine (smul_eq_zero_iff_right hD').1 ?_
    rw [← hT3, ccT_mul]
    simp only [hΓ, Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
  · have h1 : (fun a => τ.1 ((T Γ * V) i a)) = ∑ j, τ.1 (T Γ i j) • fun a => τ.1 (V j a) := by
      ext a
      simp [Matrix.mul_apply]
    rw [hval_eq, h1]
    exact comb_le (hH τ).1 _ _ (fun j => hVC j τ) fun j =>
      hM ⟨(Γ, τ, i, j), ⟨hΓF, trivial⟩, rfl⟩
end GlobalTheory.SW
