-- Prove2me | solution 1 for GlobalTheory.exists_drift_function_orthFrames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:34:25.097644+00:00
-- url     : https://prove2.me/submissions/ea3e1e82-7a3a-4f31-b316-28e082500374

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIsLUBHeightRpowLowerSemicontinuousOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_WeightedHeightSupDriftOrthonormalFramesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_HeightSupInvariantUnderHermitianLatticeAutStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumLowerOfLineHeightsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsPosLeLatticeHeightAtFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsSubspaceHeightGramDeterminantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MajorantEqSumNormSqOrthonormalFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDriftFunctionOrthonormalHermitianFrames
import Theorems.Thm_GlobalTheory_lowerSemicontinuousOn_sum_pos_mul
import Theorems.Thm_GlobalTheory_T_exists_pos_le_latticeHeight_at_frame
import Theorems.Thm_GlobalTheory_T_exists_subspaceHeight_gramDeterminant
import Theorems.Thm_GlobalTheory_T_firstMinimum_lower_of_lineHeights
import Theorems.Thm_GlobalTheory_T_heightSup_invariant_under_hermitianLattice_aut
import Theorems.Thm_GlobalTheory_T_majorant_eq_sum_norm_sq_orthonormalFrame
import Theorems.Thm_GlobalTheory_T_weighted_height_sup_drift_orthonormal_frames
import Theorems.Thm_GlobalTheory_exists_isLUB_height_rpow_lowerSemicontinuousOn
import Theorems.Thm_GlobalTheory_exists_submodule_finrank_eq_of_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : (∀ (r : ℕ) (X : Data E r), 0 < X.p0 → X.p0 < r → ∀ (τ0 : X.Ψ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → (∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1)) → ∃ (f : Frame X.Ψ r → ℝ) (c b : ℝ), 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ LowerSemicontinuousOn f {x | IsOrth X x} ∧ (∀ x, IsOrth X x → 0 ≤ f x) ∧ (∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → ∀ x, IsOrth X x → f (lact γ x) = f x) ∧ (∀ x, IsOrth X x → ∑ a ∈ S, f (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) ≤ S.card * (c * f x + b)) ∧ ∀ M : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ x, IsOrth X x → f x ≤ M → ε ≤ X.la1 x) := by
  intro r X hp0 hp0r τ0 S hS hirr hU
  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_subspaceHeight_gramDeterminant r X
  obtain ⟨δ, hδ, hdrift⟩ := GlobalTheory.T.weighted_height_sup_drift_orthonormal_frames r X d hd τ0 S hS hirr hU
  obtain ⟨α, hlub, hlsc⟩ := exists_isLUB_height_rpow_lowerSemicontinuousOn r X d hd δ hδ
  obtain ⟨e, c, b, he, hc0, hc1, hb, hdr⟩ := hdrift α hlub
  have hdet : ∀ x, IsOrth X x → ∀ τ : X.Ψ, (mat x τ).det ≠ 0 := fun x hx => (GlobalTheory.T.majorant_eq_sum_norm_sq_orthonormalFrame r X x hx).1
  have hr : 0 < r := lt_trans hp0 hp0r
  have hlow : ∀ x, IsOrth X x → ∀ i ≤ r, ∀ W : Submodule E (Fin r → E),
      Module.finrank E W = i → 0 < d x W ∧ d x W ^ (-δ) ≤ α i x := by
    intro x hx i hi W hW
    obtain ⟨m, hm, hmW⟩ := GlobalTheory.T.exists_pos_le_latticeHeight_at_frame r X d hd x (hdet x hx)
    exact ⟨lt_of_lt_of_le hm (hmW W), (hlub i hi x (hdet x hx)).1 ⟨W, hW, rfl⟩⟩
  have hαnn : ∀ x, IsOrth X x → ∀ i ≤ r, 0 ≤ α i x := by
    intro x hx i hi
    obtain ⟨W, hW⟩ := exists_submodule_finrank_eq_of_le (K := E) hi
    obtain ⟨hpos, hle⟩ := hlow x hx i hi W hW
    exact le_trans (Real.rpow_nonneg hpos.le _) hle
  have hterm_nn : ∀ x, IsOrth X x → ∀ i ∈ Finset.Ioo 0 r, 0 ≤ e i * α i x := fun x hx i hi =>
    mul_nonneg (he i).le (hαnn x hx i (Finset.mem_Ioo.1 hi).2.le)
  refine ⟨fun x => ∑ i ∈ Finset.Ioo 0 r, e i * α i x, c, b, hc0, hc1, hb, ?_, ?_, ?_, hdr, ?_⟩
  · exact lowerSemicontinuousOn_sum_pos_mul _ e he α fun i hi =>
      (hlsc i (Finset.mem_Ioo.1 hi).2.le).mono fun x hx => hdet x hx
  · intro x hx
    exact Finset.sum_nonneg (hterm_nn x hx)
  · intro γ hγ x hx
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [GlobalTheory.T.heightSup_invariant_under_hermitianLattice_aut r X d hd δ α hlub γ hγ x (hdet x hx) i (Finset.mem_Ioo.1 hi).2.le]
  · intro M
    have h1 : (1 : ℕ) ∈ Finset.Ioo 0 r := Finset.mem_Ioo.2 ⟨Nat.one_pos, lt_of_le_of_lt hp0 hp0r⟩
    set K : ℝ := max (M / e 1) 1 with hK
    have hKpos : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
    obtain ⟨ε, hε, hεla⟩ := GlobalTheory.T.firstMinimum_lower_of_lineHeights r X d hd hr (K ^ (-1 / δ)) (Real.rpow_pos_of_pos hKpos _)
    refine ⟨ε, hε, fun x hx hfM => hεla x hx fun W hW => ?_⟩
    obtain ⟨hpos, hle⟩ := hlow x hx 1 (Finset.mem_Ioo.1 h1).2.le W hW
    have hsingle : e 1 * α 1 x ≤ M :=
      le_trans (Finset.single_le_sum (hterm_nn x hx) h1) hfM
    have hdK : d x W ^ (-δ) ≤ K := by
      refine le_trans hle (le_trans ?_ (le_max_left _ _))
      rw [le_div_iff₀ (he 1)]
      linarith
    have hpow : K ^ (-1 / δ) ≤ (d x W ^ (-δ)) ^ (-1 / δ) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hpos _) hdK
        (div_nonpos_of_nonpos_of_nonneg (by norm_num) hδ.le)
    rwa [← Real.rpow_mul hpos.le, show -δ * (-1 / δ) = 1 by field_simp, Real.rpow_one] at hpow
end GlobalTheory
