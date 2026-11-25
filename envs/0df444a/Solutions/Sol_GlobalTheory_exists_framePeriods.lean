-- Prove2me | solution 1 for GlobalTheory.exists_framePeriods
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:29:40.625799+00:00
-- url     : https://prove2.me/submissions/b1bdaf9b-3e79-4d5c-a18d-7e3eff5cbcaa

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PeriodsEqFramePeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFramePeriods
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
import Theorems.Thm_GlobalTheory_T_cmType_letter_frame_column_dictionary
import Theorems.Thm_GlobalTheory_per_move
import Theorems.Thm_GlobalTheory_periods_eq_frame_periods
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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k, ∃ Pf, IsPerFr e F M k Pf ∧ (∀ Pf', IsPerFr e F M k Pf' → Pf' = Pf) ∧ (∀ x ∈ (M.X k).dom, IsPeriod (F.Di k) (fun j => relab c σ (e j).1) (Pf x)) ∧ (∀ a, DifferentiableOn ℂ (fun x => Pf x a) (M.X k).dom) ∧ ∀ P, IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → ∃ x ∈ (M.X k).dom, Pf x = P := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hg hb hn k
  obtain ⟨⟨idx, hty, -, hper⟩, hp0, hr, hξ, hpos, hφ⟩ := GlobalTheory.T.cmType_letter_frame_column_dictionary E H Dw l Xo c σ g e F r M hg hb hn k
  let φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E) := (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap
  have hφa : ∀ a, φ a = (M.φ k a : Fin r → E) := fun a => rfl
  obtain ⟨-, hφ'⟩ := hφ φ hφa
  have hemb : ∀ (τ : E →+* ℂ) (v w : Fin r → E), Data.emb τ (v + w) = Data.emb τ v + Data.emb τ w := by
    intro τ v w
    funext a
    simp [Data.emb]
  let Pf : Frame (M.X k).Ψ r → ((F.Di k).La →+ (Fin g → ℂ)) := fun x =>
    AddMonoidHom.mk' (fun a j => perFr (M.X k) x (φ a) (relab c σ (e j).1) (e j).2) (by
      intro a b
      funext j
      simp only [Pi.add_apply, hper, map_add, hemb]
      split_ifs
      · simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      · rw [Matrix.mulVec_add, Pi.add_apply])
  have hPf : IsPerFr e F M k Pf := fun x a j => rfl
  have hPf' : ∀ x v j, Pf x v j = if ((idx j).2 : ℕ) < (F.Di k).q then
      hermC (idx j).1.1 (M.X k).Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 (φ v))
      else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 (φ v)) (idx j).2 :=
    fun x v j => (hPf x v j).trans (hper x _ j)
  have hdom : (M.X k).dom = GG (M.X k).Ψ (M.X k).Gm (F.Di k).q := by rw [← hp0]
  obtain ⟨h1, h2⟩ := GlobalTheory.periods_eq_frame_periods E H Dw l Xo _ g _ F k r _ (M.X k).Gm φ (M.X k).Ψ idx Pf
    (hb.type k).2 hty hξ hpos hφ' hr hPf'
  have h3 := (GlobalTheory.per_move E H (F.Di k) r _ (M.X k).Gm φ (M.X k).Ψ (hb.type k).2 g idx _ hty hξ hpos hφ').1
    Pf hPf'
  rw [hdom]
  refine ⟨Pf, hPf, fun Pf' h' => ?_, fun x hx => (h1 x hx).1, h3, h2⟩
  funext x
  exact AddMonoidHom.ext fun a => funext fun j => (h' x a j).trans (hPf x a j).symm
end GlobalTheory
