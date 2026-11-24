-- Prove2me | solution 1 for GlobalTheory.HermLocal.congr_diagonal_of_five
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:37:40.732166+00:00
-- url     : https://prove2.me/submissions/beac7fe2-388a-4727-bf71-87c31f19b097

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometricCm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasseNormTheoremQuadraticExtension
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Theorems.Thm_GlobalTheory_HermLocal_exists_represent_of_five
import Theorems.Thm_GlobalTheory_HermDiag_exists_congr_diagonal_col_eq
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_det
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_symm
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_trans
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_congr_diagonal_of_tail
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.Inertia.negIndex_neg
attribute [local simp] GlobalTheory.Inertia.posIndex_neg
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate WithZero
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LocalQuad GlobalTheory.LocalQuad.HermClass
open GlobalTheory GlobalTheory.HermLocal
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {c : L →+* L}
namespace GlobalTheory.HermLocal
theorem _root_.solution (h2 : (2 : K) ≠ 0)
    (H : ∀ a : Fin 5 → K, ∃ x : Fin 5 → K, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0) (hc : ∀ t, c (c t) = t)
    (hF : ∀ t : L, c t = t ↔ ∃ s : K, algebraMap K L s = t) {θ : L} (hθ0 : θ ≠ 0) (hθ : c θ = -θ)
    (r : ℕ) : ∀ g g' : Fin r → L,
    (∀ i, c (g i) = g i) → (∀ i, c (g' i) = g' i) → (∀ i, g i ≠ 0) → (∀ i, g' i ≠ 0) →
    (∃ x : L, ∏ i, g i = x * c x * ∏ i, g' i) →
    Congr c (Matrix.diagonal g) (Matrix.diagonal g') := by
  have h2L : (2 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap K L) 2]
    exact (map_ne_zero _).2 h2
  induction r with
  | zero =>
    intro g g' _ _ _ _ _
    exact ⟨1, by simp, Subsingleton.elim _ _⟩
  | succ r ih =>
    intro g g' hg hg' h0 h0' ⟨x, hx⟩
    obtain ⟨z, hz⟩ : ∃ z : Fin (r + 1) → L, z ⬝ᵥ Matrix.diagonal g *ᵥ (c ∘ z) = g' 0 := by
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one] at hx
        have hx0 : x ≠ 0 := by
          rintro rfl
          exact h0 0 (by simpa using hx)
        have hx1 : c x ≠ 0 := (map_ne_zero c).2 hx0
        refine ⟨fun _ => x⁻¹, ?_⟩
        simp only [dotProduct, Matrix.mulVec_diagonal, Function.comp_apply, map_inv₀,
          Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, hx]
        field_simp
      · exact exists_represent_of_five h2 H hF hθ0 hθ (by omega) hg h0 (hg' 0) (h0' 0)
    have hG : ∀ a b, c (Matrix.diagonal g a b) = Matrix.diagonal g b a := by
      intro a b
      by_cases hab : a = b
      · subst hab
        simpa using hg a
      · simp [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab)]
    obtain ⟨P, k, hP, hPk, hk, hk0, -, hk1⟩ :=
      GlobalTheory.HermDiag.exists_congr_diagonal_col_eq h2L hc hG (x := z) (hz ▸ h0' 0) 0
    have hp : ∏ i, g i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => h0 i
    have hk0 := hk0 (by rwa [Matrix.det_diagonal])
    have hcg : Congr c (Matrix.diagonal g) (Matrix.diagonal k) := ⟨P, hP, hPk.symm⟩
    have hk2 : k 0 = g' 0 := hk1.trans hz
    refine hcg.trans (congr_diagonal_of_tail hk2 (ih _ _ (fun i => hk _) (fun i => hg' _)
      (fun i => hk0 _) (fun i => h0' _) ?_))
    obtain ⟨y, -, hy⟩ := hcg.det
    rw [Matrix.det_diagonal, Matrix.det_diagonal, hx, Fin.prod_univ_succ, Fin.prod_univ_succ,
      hk2] at hy
    refine ⟨y * x, mul_left_cancel₀ (h0' 0) ?_⟩
    rw [hy, map_mul]
    ring
end GlobalTheory.HermLocal
