-- Prove2me | solution 1 for GlobalTheory.torusAtExists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:01:56.116776+00:00
-- url     : https://prove2.me/submissions/1f14333c-de47-4a44-8628-4ad0b835a140

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_SumCMulImHermCEqSignMulTrace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsTorusCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_TorusAtExistsOfParts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_TorusAtExists
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
import Theorems.Thm_GlobalTheory_CMLattice_exists_basis_lattice
import Theorems.Thm_GlobalTheory_ThetaExist_exists_theta_ne_zero
import Theorems.Thm_GlobalTheory_c_eq_two_mul_abs_im
import Theorems.Thm_GlobalTheory_exists_torus_coordinates
import Theorems.Thm_GlobalTheory_hermC_emb_eq_map_herm
import Theorems.Thm_GlobalTheory_re_map_xi_eq_zero
import Theorems.Thm_GlobalTheory_torusAtExists_of_parts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_bOf_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_ortho_bOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceFormIndependence_trace_re
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_e_linInd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply


section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
namespace GlobalTheory
open NumberField in
private lemma span_col_mul_castLE_eq_span_col {r i : ℕ} (hi : i ≤ r)
    (M B : Matrix (Fin r) (Fin r) ℂ) (hB : ∀ a c : Fin r, c < a → B a c = 0)
    (hli : LinearIndependent ℂ (fun a => _root_.ReciprocityTheory.ChartRestriction.G.FD.col (M * B) a)) :
    Submodule.span ℂ (Set.range fun a : Fin i => _root_.ReciprocityTheory.ChartRestriction.G.FD.col (M * B) (Fin.castLE hi a)) =
      Submodule.span ℂ (Set.range fun a : Fin i => _root_.ReciprocityTheory.ChartRestriction.G.FD.col M (Fin.castLE hi a)) := by
  have hle : Submodule.span ℂ (Set.range fun a : Fin i => _root_.ReciprocityTheory.ChartRestriction.G.FD.col (M * B) (Fin.castLE hi a)) ≤
      Submodule.span ℂ (Set.range fun a : Fin i => _root_.ReciprocityTheory.ChartRestriction.G.FD.col M (Fin.castLE hi a)) := by
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    have hcol : _root_.ReciprocityTheory.ChartRestriction.G.FD.col (M * B) (Fin.castLE hi c) =
        ∑ a, B a (Fin.castLE hi c) • _root_.ReciprocityTheory.ChartRestriction.G.FD.col M a := by
      funext k
      simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, Finset.sum_apply, mul_comm]
    show _root_.ReciprocityTheory.ChartRestriction.G.FD.col (M * B) (Fin.castLE hi c) ∈ _
    rw [hcol]
    refine Submodule.sum_mem _ fun a _ => ?_
    by_cases ha : (a : ℕ) < i
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩)
    · rw [hB a _ (by rw [Fin.lt_def]; simp only [Fin.coe_castLE]; omega), zero_smul]
      exact zero_mem _
  apply Submodule.eq_of_le_of_finrank_le hle
  have h1 := finrank_span_eq_card (R := ℂ) (hli.comp _ (Fin.castLE_injective hi))
  have h2 : Module.finrank ℂ
      (Submodule.span ℂ (Set.range fun a : Fin i => _root_.ReciprocityTheory.ChartRestriction.G.FD.col M (Fin.castLE hi a))) ≤ i :=
    (finrank_range_le_card (R := ℂ) (fun a : Fin i => _root_.ReciprocityTheory.ChartRestriction.G.FD.col M (Fin.castLE hi a))).trans_eq
      (Fintype.card_fin i)
  simp only [Function.comp_def, Fintype.card_fin] at h1
  omega
open NumberField in
private lemma exists_frame_span_castLE_eq_span_col (E : Type) [Field E] [NumberField E]
    [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) :
    ∀ x ∈ X.dom, ∃ e : X.Ψ → Fin r → Fin r → ℂ,
      (∀ (τ : X.Ψ) (a b : Fin r),
        _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (↑τ) X.Gm (e τ a) (e τ b) = if a = b then ↑(_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 ↑a) else 0) ∧
      ∀ (τ : X.Ψ) (i : ℕ) (hi : i ≤ r),
        Submodule.span ℂ (Set.range fun a => e τ (Fin.castLE hi a)) =
          Submodule.span ℂ (Set.range fun a => _root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (Fin.castLE hi a)) := by
  intro x hx
  have hb := _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem X hx
  have ho := _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsOrtho at ho
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor at hb
  have horth : ∀ (τ : X.Ψ) (a c : Fin r),
      _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) τ) a)
          (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) τ) c) =
        if a = c then ↑(_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 ↑a) else 0 := by
    intro τ a c
    simpa [_root_.ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.diagonal_apply] using congrFun (congrFun (ho τ) a) c
  refine ⟨fun τ a => _root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) τ) a, horth, fun τ i hi => ?_⟩
  have hli := _root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.e_linInd X τ _ (horth τ)
  exact span_col_mul_castLE_eq_span_col hi (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)
    (fun a c h => (hb τ).2 a c h) hli
open NumberField in
private lemma im_hermC_emb_eq_sign_mul_trace (E : Type) [Field E] [NumberField E]
    [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) :
    ∃ sg : ℝ, (sg = 1 ∨ sg = -1) ∧ ∀ (u v : Fin r → E),
      ∑ τ, X.c τ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) u) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) v)).im =
        sg * ↑((Algebra.trace ℚ E) (X.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v)) := by
  rcases X.κ0_xi with h | h
  · refine ⟨1, Or.inl rfl, fun u v => ?_⟩
    rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence.trace_re X, one_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hy : (τ.1 X.ξ0).im < 0 := by
      have := X.κ0_sign τ
      rw [h, map_mul, map_ofNat] at this
      simp at this
      linarith
    have hre := _root_.GlobalTheory.re_map_xi_eq_zero X τ.1
    rw [_root_.GlobalTheory.c_eq_two_mul_abs_im, abs_of_neg hy,
      _root_.GlobalTheory.hermC_emb_eq_map_herm, map_mul, Complex.mul_re, hre]
    ring
  · refine ⟨-1, Or.inr rfl, fun u v => ?_⟩
    rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence.trace_re X, neg_one_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hy : 0 < (τ.1 X.ξ0).im := by
      have := X.κ0_sign τ
      rw [h, map_neg, map_mul, map_ofNat] at this
      simp at this
      linarith
    have hre := _root_.GlobalTheory.re_map_xi_eq_zero X τ.1
    rw [_root_.GlobalTheory.c_eq_two_mul_abs_im, abs_of_pos hy,
      _root_.GlobalTheory.hermC_emb_eq_map_herm, map_mul, Complex.mul_re, hre]
    ring
end GlobalTheory
end

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open NumberField
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : _root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtExistsStatement :=
  _root_.GlobalTheory.torusAtExists_of_parts exists_frame_span_castLE_eq_span_col
    _root_.GlobalTheory.CMLattice.exists_basis_lattice im_hermC_emb_eq_sign_mul_trace
    _root_.GlobalTheory.exists_torus_coordinates _root_.GlobalTheory.ThetaExist.exists_theta_ne_zero
end _root_.GlobalTheory
end GlobalTheory
