-- Prove2me | solution 1 for GlobalTheory.AbCoh.exists_fin_span_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:01:19.558887+00:00
-- url     : https://prove2.me/submissions/91cc7752-7698-4590-8077-f2ebc1e09965

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafCohomologyBasisBijective
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory GlobalTheory.AbCoh
namespace GlobalTheory.AbCoh
theorem _root_.solution {X : Scheme.{0}} (T : X.affineOpens) (B : Set Γ(X, T.1))
    (hB : ∀ x ∈ T.1, ∃ f ∈ B, x ∈ X.basicOpen f) :
    ∃ (n : ℕ) (b : Fin n → Γ(X, T.1)), Ideal.span (Set.range b) = ⊤ ∧ ∀ i, b i ∈ B := by
  have hsp : Ideal.span B = ⊤ := by
    rw [← T.2.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨f, hf, hxf⟩ := hB x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hf⟩, hxf⟩
  obtain ⟨F, hFB, hF⟩ := (Ideal.span_eq_top_iff_finite B).1 hsp
  refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, fun i ↦ hFB (F.equivFin.symm i).2⟩
  rw [eq_top_iff, ← hF]
  exact Ideal.span_mono fun x hx ↦ ⟨F.equivFin ⟨x, hx⟩, by simp⟩
end GlobalTheory.AbCoh
