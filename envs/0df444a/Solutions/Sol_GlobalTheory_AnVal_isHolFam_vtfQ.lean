-- Prove2me | solution 1 for GlobalTheory.AnVal.isHolFam_vtfQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:41:15.274732+00:00
-- url     : https://prove2.me/submissions/f991679c-fd43-49e1-aeb0-bfe9ec4c68f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SectionReadingExistsUniqueIsTheta
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__comp_88757af08841
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isHolFam_vtfLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_pt_uniq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnVal
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
namespace GlobalTheory.AnVal
theorem _root_.solution {x0 : Sp ℂ ⟶ S} {g : ℕ} (e : (Fin g → ℂ) → (Over.mk x0 ⟶ A))
    (hol : IsHolFam (fun z => (e z).left)) : IsHolFam (fun z => (vtfQ A (e z)).left) := by
  have he : ∀ z, (e z).left ≫ A.hom = x0 := fun z => Over.w (e z)
  have h := isHolFam_vtfLift A.hom x0 (fun z => (e z).left) he hol
  let σ : pullback A.hom x0 ⟶ (Over.mk x0 ⊗ A).left := (pullbackSymmetry A.hom x0).hom
  have key : ∀ z, (vtfQ A (e z)).left = vtfLift A.hom x0 (fun z => (e z).left) he z ≫ σ := by
    intro z
    symm
    apply vtf_pt_uniq
    · have : σ ≫ (snd (Over.mk x0) A).left = pullback.fst A.hom x0 :=
        pullbackSymmetry_hom_comp_snd A.hom x0
      rw [Category.assoc, this]
      exact pullback.lift_fst _ _ _
    · have : σ ≫ (fst (Over.mk x0) A).left = pullback.snd A.hom x0 :=
        pullbackSymmetry_hom_comp_fst A.hom x0
      rw [Category.assoc, this]
      exact pullback.lift_snd _ _ _
  intro V φ
  have h1 := h (σ ⁻¹ᵁ V) ((σ.app V).hom φ)
  have h2 : (fun z => valAt' (vtfQ A (e z)).left V φ) = fun z =>
      valAt' (vtfLift A.hom x0 (fun z => (e z).left) he z) (σ ⁻¹ᵁ V) ((σ.app V).hom φ) := by
    funext z
    rw [key]
    exact (valAt'_comp _ σ V φ).symm
  have h3 : {z | ⊤ ≤ (vtfQ A (e z)).left ⁻¹ᵁ V} =
      {z | ⊤ ≤ vtfLift A.hom x0 (fun z => (e z).left) he z ⁻¹ᵁ (σ ⁻¹ᵁ V)} := by
    ext z
    rw [Set.mem_ofPred_eq, key]
    rfl
  exact ⟨h3 ▸ h1.1, h3 ▸ h2 ▸ h1.2⟩
end GlobalTheory.AnVal
