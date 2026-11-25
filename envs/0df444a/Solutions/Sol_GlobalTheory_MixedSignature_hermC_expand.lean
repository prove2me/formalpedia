-- Prove2me | solution 1 for GlobalTheory.MixedSignature.hermC_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:39:26.137149+00:00
-- url     : https://prove2.me/submissions/fecc85cd-89d4-4f24-9472-9c6db0163f10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_WeightedSupDriftOnOrthonormalFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsBoundOrthonormalFrame
import Theorems.Thm_GlobalTheory_FlagMahler_Qy_smul_le
import Theorems.Thm_GlobalTheory_FlagMahler_col_map_eq
import Theorems.Thm_GlobalTheory_FlagMahler_comb_bound
import Theorems.Thm_GlobalTheory_FlagMahler_comp_le_Qy
import Theorems.Thm_GlobalTheory_FlagMahler_finite_int_sq
import Theorems.Thm_GlobalTheory_FlagMahler_inv_lact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_mulVec_eq_sum_col
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_hermC_emb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianLatticeMaps_phi_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianLatticeMaps_phi_phi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_Am_posDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_Ly_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_Ly_surjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_ipB_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_quad_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_emb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_right
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MixedSignature
open ReciprocityTheory.ChartRestriction.G.FD NumberField Module Complex
open Matrix hiding col gram
open scoped ComplexConjugate
open QuadraticLatticeForms (ip ipB ipB_apply Ly Am Qy Ly_injective Ly_surjective quad_int Am_posDef)
open HermitianLatticeMaps (phi phi_f phi_zsum phi_mem phi_phi smul_coe coe_expand mulQ mulQ_apply)
open GlobalTheory.FlagMahler (col_map_eq inv_lact comp_le_Qy comb_bound Qy_smul_le finite_int_sq)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ}
namespace GlobalTheory.MixedSignature
theorem _root_.solution (τ : E →+* ℂ) (P : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ G ((P.map τ) *ᵥ u) ((P.map τ) *ᵥ w) =
      ∑ k, ∑ l, u k * conj (w l) * τ (herm G (P *ᵥ Pi.single k 1) (P *ᵥ Pi.single l 1)) := by
  rw [Data.mulVec_eq_sum_col (P.map τ) u, Data.mulVec_eq_sum_col (P.map τ) w, hermC_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hermC_smul_left, hermC_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hermC_smul_right, col_map_eq, col_map_eq, hermC_emb]
  ring
end GlobalTheory.MixedSignature
