-- Prove2me | solution 1 for GlobalTheory.CuspExist.exists_congr_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:29:42.004405+00:00
-- url     : https://prove2.me/submissions/8b546603-2786-4e0e-b59e-1f6a4d6e337e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LandherrStOfHasseNormSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LinearIndependentSingleAdd
import Theorems.Thm_Formalism_L2_Pj_FJ_gram_eq
import Theorems.Thm_Formalism_L2_Pj_gram_eq
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Inertia_embedding_cc
import Theorems.Thm_GlobalTheory_Inertia_gram_eq
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_det
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_symm
import Theorems.Thm_GlobalTheory_Published_Landherr_of_signature
import Theorems.Thm_GlobalTheory_Published_Landherr_re_det_div_pos
import Theorems.Thm_GlobalTheory_Published_cc_det_of_herm
import Theorems.Thm_GlobalTheory_Published_embedding_cc
import Theorems.Thm_GlobalTheory_Published_gram_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.Inertia.negIndex_neg
attribute [local simp] GlobalTheory.Inertia.posIndex_neg



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open scoped Matrix ComplexConjugate
open GlobalTheory GlobalTheory.CuspExist
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.CuspExist
theorem _root_.solution (H : GlobalTheory.Published.Landherr) (X : Data E r) (k : Fin r) :
    ∃ (d : E) (P : Matrix (Fin r) (Fin r) E), P.det ≠ 0 ∧
      Matrix.diagonal (fun a : Fin r => (if (a : ℕ) < X.p0 then (1 : E) else -1) *
        (if a = k then d else 1)) = Pᵀ * X.Gm * P.map cc := by
  classical
  set s : Fin r → E := fun a => if (a : ℕ) < X.p0 then (1 : E) else -1 with hs
  have hs0 : ∀ a, s a ≠ 0 := fun a => by
    simp only [hs]; split_ifs <;> simp
  have hscc : ∀ a, cc (s a) = s a := fun a => by
    simp only [hs]; split_ifs <;> simp [cc]
  have hsτ : ∀ (τ : E →+* ℂ) a, τ (s a) = ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := fun τ a => by
    simp only [hs, sgn]; split_ifs <;> simp
  have hS0 : (Matrix.diagonal s).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => hs0 a
  have hSh : ∀ a b, cc (Matrix.diagonal s a b) = Matrix.diagonal s b a := by
    intro a b
    by_cases h : a = b
    · subst h; simpa using hscc a
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]; simp [cc]
  set d : E := X.Gm.det / (Matrix.diagonal s).det with hd
  have hd0 : d ≠ 0 := div_ne_zero X.Gm_det hS0
  have hdcc : cc d = d := by
    have h1 := GlobalTheory.Published.cc_det_of_herm X.Gm_herm
    have h2 := GlobalTheory.Published.cc_det_of_herm hSh
    unfold cc at h1 h2 ⊢
    rw [hd, map_div₀, h1, h2]
  have hdet : (Matrix.diagonal fun a : Fin r => s a * (if a = k then d else 1)).det = X.Gm.det := by
    rw [Matrix.det_diagonal, Finset.prod_mul_distrib, Finset.prod_ite_eq', if_pos (Finset.mem_univ _),
      ← Matrix.det_diagonal, hd]
    field_simp
  refine ⟨d, GlobalTheory.Published.Landherr.of_signature H X.Gm_herm ?_ X.Gm_det (hdet ▸ X.Gm_det)
    (X.Ψ : Set (E →+* ℂ)) (fun τ => ?_) (fun τ hτ => ⟨X.p0, X.signature ⟨τ, hτ⟩, ?_⟩) ⟨1, ?_⟩⟩
  · intro a b
    by_cases h : a = b
    · subst h
      have h1 := hscc a
      unfold cc at h1 hdcc ⊢
      rw [Matrix.diagonal_apply_eq, map_mul, h1]
      congr 1
      split_ifs
      · exact hdcc
      · exact map_one _
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]; simp [cc]
  · by_cases h : ComplexEmbedding.conjugate τ ∈ X.Ψ
    · exact Or.inr h
    · exact Or.inl ((X.cmType τ).mpr h)
  · obtain ⟨Q, hQ, hg⟩ := X.signature ⟨τ, hτ⟩
    have hpos : 0 < (τ d).re := by
      refine GlobalTheory.Published.Landherr.re_det_div_pos X.Gm_det τ ⟨Q, hQ, ?_⟩
      rw [← GlobalTheory.Published.gram_eq, hg, Matrix.diagonal_map (map_zero τ)]
      simp only [hsτ]
    have hre : ((τ d).re : ℂ) = τ d := by
      rw [← Complex.conj_eq_iff_re, ← GlobalTheory.Published.embedding_cc, hdcc]
    set t : ℝ := (Real.sqrt (τ d).re)⁻¹ with ht
    have ht0 : t ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hpos).ne'
    have htt : (t : ℂ) * τ d * t = 1 := by
      rw [← hre, mul_right_comm, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ht, ← mul_inv,
        Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one]
    refine ⟨Matrix.diagonal fun a => if a = k then (t : ℂ) else 1, ?_, ?_⟩
    · rw [Matrix.det_diagonal, Finset.prod_ite_eq', if_pos (Finset.mem_univ _)]
      exact_mod_cast ht0
    · rw [GlobalTheory.Published.gram_eq, Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero τ),
        Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext a
      rw [map_mul, hsτ]
      split_ifs
      · rw [Complex.conj_ofReal]
        linear_combination ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * htt
      · simp
  · rw [hdet, div_self X.Gm_det]; simp [cc]
end GlobalTheory.CuspExist
