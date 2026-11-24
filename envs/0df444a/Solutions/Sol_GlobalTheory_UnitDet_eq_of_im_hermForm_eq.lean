-- Prove2me | solution 1 for GlobalTheory.UnitDet.eq_of_im_hermForm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:44:28.076785+00:00
-- url     : https://prove2.me/submissions/b9edb607-3e62-435c-abd2-e01acce1ad88

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmTypeLetterFrameColumnDictionaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFramePeriodsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TriangularFrameMovesPeriodBlockTriangularStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitFrameEqOrthonormalMulTriangularStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemIffConjugateNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOfImHermFormEq
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.UnitDet
namespace GlobalTheory.UnitDet
theorem _root_.solution {g : ℕ} (S : Set (Fin g → ℂ)) (hS : Submodule.span ℝ S = ⊤)
    (A B : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ z ∈ S, ∀ w ∈ S, (hermForm A z w).im = (hermForm B z w).im) : A = B := by
  have h1 : ∀ z, ∀ w ∈ S, (hermForm A z w).im = (hermForm B z w).im := by
    intro z w hw
    have hz : z ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx => exact h x hx w hw
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, add_dotProduct, Complex.add_im] at hx hy ⊢
      rw [hx, hy]
    | smul a x _ hx =>
      simp only [hermForm, smul_dotProduct, Complex.smul_im] at hx ⊢
      rw [hx]
  have h2 : ∀ z w, (hermForm A z w).im = (hermForm B z w).im := by
    intro z w
    have hw : w ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx => exact h1 z x hx
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im] at hx hy ⊢
      rw [hx, hy]
    | smul a x _ hx =>
      simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im] at hx ⊢
      rw [hx]
  ext i j
  have e1 := h2 (Pi.single i 1) (Pi.single j 1)
  have e2 := h2 (Pi.single i Complex.I) (Pi.single j 1)
  simp [hermForm] at e1 e2
  exact Complex.ext e2 e1
end GlobalTheory.UnitDet
