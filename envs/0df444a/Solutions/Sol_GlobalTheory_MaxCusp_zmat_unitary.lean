-- Prove2me | solution 1 for GlobalTheory.MaxCusp.zmat_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:58:19.04864+00:00
-- url     : https://prove2.me/submissions/bf3f54e5-2da8-4deb-b45b-8f01b06c96c0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientSupportHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsHermOfMemLZ
import Theorems.Thm_GlobalTheory_MaxCusp_zmat_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_hermC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_hermC_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_hermC_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_hermC_emb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_emb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MaxCusp
open NumberField Complex MeasureTheory Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r d : ℕ}
variable (X : Data E r)
namespace GlobalTheory.MaxCusp
theorem _root_.solution (u : Fin d → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin d → Fin d → ℂ) (hb : IsHerm b) (τ : X.Ψ) (v w : Fin r → ℂ) :
    hermC τ.1 X.Gm (zmat X u b τ *ᵥ v) (zmat X u b τ *ᵥ w) = hermC τ.1 X.Gm v w := by
  have hiso : ∀ i k, hermC τ.1 X.Gm (Data.emb τ.1 (u i)) (Data.emb τ.1 (u k)) = 0 := fun i k => by
    rw [hermC_emb, hu, map_zero]
  have hbc : ∀ i k, conj (b τ i k) = b τ k i := fun i k => (hb τ i k).symm
  have hcI : conj (I * (X.c τ : ℂ)) = -(I * X.c τ) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  rw [zmat_mulVec, zmat_mulVec]
  generalize (I * (X.c τ : ℂ)) = q at hcI
  simp only [hermC_add_left, hermC_add_right, hermC_sum_left, hermC_sum_right, hermC_smul_left,
    hermC_smul_right, hiso, map_mul, map_neg, map_sum, hcI, hbc, hermC_conj τ.1 X.Gm_herm,
    mul_zero, Finset.sum_const_zero, add_zero, neg_neg]
  rw [add_assoc, add_eq_left]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  ring
end GlobalTheory.MaxCusp
