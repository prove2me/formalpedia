-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isBasisOn_pullbackUnitApp_of_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:23:56.804888+00:00
-- url     : https://prove2.me/submissions/33aa6cc7-5df8-4c19-a673-f21a1ab86638

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_ImmersionPullback
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_pullbackUnitApp_naturality
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isBasisOn_pullbackUnitApp_one
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_bijective
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_comp
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_comp_hom
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_res
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsBasisOn_map_iso
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isBasisOn_one
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isIso_of_isBasisOn
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_resM_refl
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_resM_resM


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
open GroundTheory.Arith.Etale (pullbackUnitApp pullbackUnitApp_res pullbackUnitApp_comp
  pullbackUnitApp_comp_hom pullbackUnitApp_bijective)
universe u
noncomputable section
variable {Y Z : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (f : Y ⟶ Z) {N : Z.Modules} {O : Z.Opens} (hO : ⊤ ≤ O)
    {t : Γ(N, O)} (ht : IsBasisOn ((preMod Z).obj N) O t) :
    IsBasisOn ((preMod Y).obj ((Scheme.Modules.pullback f).obj N)) (f ⁻¹ᵁ O)
      (pullbackUnitApp f N O t) := by
  obtain rfl : O = ⊤ := top_le_iff.mp hO
  let sec : N.val.sections := ⟨fun j => resM ((preMod Z).obj N) (le_top : j.unop ≤ ⊤) t,
    fun {j j'} g => by
      exact resM_resM _ _ _ _⟩
  let f₀ : 𝟙_ Z.Modules ⟶ N :=
    (SheafOfModules.unitHomEquiv N).symm sec
  have hf₀ : ∀ U : Z.Opens, Scheme.Modules.Hom.app f₀ U (unitOne Z U) = resM ((preMod Z).obj N) (le_top : U ≤ ⊤) t := by
    intro U
    have := SheafOfModules.unitHomEquiv_apply_coe N f₀ (op U)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  have hf₀t : Scheme.Modules.Hom.app f₀ ⊤ (unitOne Z ⊤) = t := by
    rw [hf₀]
    exact resM_refl _ t
  have : IsIso f₀ := isIso_of_isBasisOn f₀ (fun _ => ⟨⊤, trivial, unitOne Z ⊤,
    isBasisOn_one ⊤, by
      change IsBasisOn _ ⊤ (Scheme.Modules.Hom.app f₀ ⊤ (unitOne Z ⊤))
      rw [hf₀t]
      exact ht⟩)
  have h2 := (isBasisOn_pullbackUnitApp_one f).map_iso (asIso ((Scheme.Modules.pullback f).map f₀))
  have hx : ((preMod Y).map (asIso ((Scheme.Modules.pullback f).map f₀)).hom).app (op ⊤)
      (pullbackUnitApp f (SheafOfModules.unit Z.ringCatSheaf) ⊤ (unitOne Z ⊤)) =
      pullbackUnitApp f N ⊤ t := by
    change Scheme.Modules.Hom.app ((Scheme.Modules.pullback f).map f₀) (f ⁻¹ᵁ ⊤)
      (pullbackUnitApp f (𝟙_ Z.Modules) ⊤ (unitOne Z ⊤)) = _
    rw [pullbackUnitApp_naturality, hf₀t]
  rw [hx] at h2
  exact h2
end GroundTheory.Arith.SchemeCoh
