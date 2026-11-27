-- Prove2me | solution 1 for GlobalTheory.UnitDet.det_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:36:27.676269+00:00
-- url     : https://prove2.me/submissions/53f36785-acf3-4aef-ac8a-f00dfddf3248

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
import Theorems.Thm_GlobalTheory_UnitDet_eq_of_im_hermForm_eq
import Theorems.Thm_GlobalTheory_UnitDet_hermForm_mulVec
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
import Theorems.Thm_GlobalTheory_T_cmType_letter_frame_column_dictionary
import Theorems.Thm_GlobalTheory_T_exists_framePeriods_alt
import Theorems.Thm_GlobalTheory_T_triangularFrame_moves_period_blockTriangular
import Theorems.Thm_GlobalTheory_T_unitFrame_eq_orthonormal_mul_triangular
import Theorems.Thm_GlobalTheory_UnitFrame_im_hermForm_eq
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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k Pf, IsPerFr e F M k Pf → ∀ x ∈ (M.X k).dom, (∀ τ i, ‖dmin (M.X k).Gm x τ i‖ = 1) → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ a b, (hermForm Hm (Pf x a) (Pf x b)).im = (F.Di k).EF a b) → Hm.det = ((∏ j, (2 * ‖relab c σ (e j).1 (M.X k).ξ0‖) : ℝ) : ℂ) := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hG hB hN k Pf hPf x hx hu Hm hHm
  obtain ⟨hl1, hl2, -⟩ := GlobalTheory.T.unitFrame_eq_orthonormal_mul_triangular E r (M.X k).p0 (M.X k).Ψ (M.X k).Gm (M.X k).Gm_herm
  obtain ⟨x₀, b, hb, hgr, hb1, rfl⟩ := hl1 x hx hu
  have hx₀ : x₀ ∈ (M.X k).dom := (hl2 x₀ hgr).1
  obtain ⟨h₀, -, hh, -, -, hdet, -⟩ :=
    GlobalTheory.T.triangularFrame_moves_period_blockTriangular E H Dw l Xo c σ g e F r M hG hB hN k Pf hPf x₀ hx₀ b hb
  replace hdet := hdet hb1
  obtain ⟨Pf', -, huniq, hper, -⟩ := GlobalTheory.T.exists_framePeriods_alt E H Dw l Xo c σ g e F r M hG hB hN k
  obtain rfl := huniq Pf hPf
  have hspan := (hper x₀ hx₀).2.2.2.1
  obtain ⟨⟨idx, hty, -, hfr⟩, hp, -, hξ, hpos, hφ⟩ := GlobalTheory.T.cmType_letter_frame_column_dictionary E H Dw l Xo c σ g e F r M hG hB hN k
  let φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E) := (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap
  have hD := GlobalTheory.UnitFrame.im_hermForm_eq E H (F.Di k) r (-(M.X k).ξ0) (M.X k).Gm φ (M.X k).Ψ
    (hB.type k).2 g idx (fun j => relab c σ (e j).1) hty hξ hpos (hφ φ fun _ => rfl).2 x₀ (Pf x₀)
    (fun v j => by rw [hPf, hfr]; rfl) (fun τ => by rw [← hp]; exact hgr τ)
  have key : h₀ᵀ * (Hm * h₀.map (starRingEnd ℂ)) =
      Matrix.diagonal fun j => ((2 * ‖(idx j).1.1 (-(M.X k).ξ0)‖ : ℝ) : ℂ) := by
    refine eq_of_im_hermForm_eq _ hspan _ _ ?_
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    rw [hD, ← hermForm_mulVec, ← hh, ← hh, hHm]
  have h1 := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h1
  have h2 : h₀.det * starRingEnd ℂ h₀.det = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hdet]; simp
  have h3 : Hm.det = h₀.det * (Hm.det * starRingEnd ℂ h₀.det) := by
    linear_combination (-Hm.det) * h2
  rw [h3, h1, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hty j, map_neg, norm_neg]
  split_ifs
  · rw [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
  · rfl
end GlobalTheory.UnitDet
