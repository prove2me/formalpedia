-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isBasisOn_pullbackUnitApp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:05:21.679246+00:00
-- url     : https://prove2.me/submissions/bbb06ed2-f39a-4d6d-b025-b8d135567c27

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_ImmersionPullback
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_pullbackUnitApp_smul_resM
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_bijective
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_comp
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_comp_hom
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_res


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
theorem _root_.solution (j : Y ⟶ Z) [IsOpenImmersion j] (N : Z.Modules) {O : Z.Opens}
    (hO : O ≤ j.opensRange) (t : Γ(N, O)) :
    IsBasisOn ((preMod Y).obj ((Scheme.Modules.pullback j).obj N)) (j ⁻¹ᵁ O)
        (pullbackUnitApp j N O t) ↔ IsBasisOn ((preMod Z).obj N) O t := by
  have key : ∀ (V : Z.Opens) (h : V ≤ O),
      Function.Bijective (fun r : ringOn Y (j ⁻¹ᵁ V) =>
        r • resM ((preMod Y).obj ((Scheme.Modules.pullback j).obj N))
          ((Opens.map j.base).monotone h) (pullbackUnitApp j N O t)) ↔
      Function.Bijective (fun r : ringOn Z V => r • resM ((preMod Z).obj N) h t) := by
    intro V h
    have hV : V ≤ j.opensRange := h.trans hO
    have b1 : Function.Bijective (appR j V) := by
      have := Scheme.Hom.isIso_app j V hV
      exact ConcreteCategory.bijective_of_isIso _
    have b2 := pullbackUnitApp_bijective j N hV
    have comm : (fun r : ringOn Y (j ⁻¹ᵁ V) =>
        r • resM ((preMod Y).obj ((Scheme.Modules.pullback j).obj N))
          ((Opens.map j.base).monotone h) (pullbackUnitApp j N O t)) ∘ appR j V =
        pullbackUnitApp j N V ∘ (fun r : ringOn Z V => r • resM ((preMod Z).obj N) h t) := by
      funext r
      exact (pullbackUnitApp_smul_resM j N h r t).symm
    constructor
    · intro hl
      have := hl.comp b1
      rw [comm] at this
      exact (Function.Bijective.of_comp_iff' b2 _).1 this
    · intro hr
      have := b2.comp hr
      rw [← comm] at this
      exact (Function.Bijective.of_comp_iff _ b1).1 this
  constructor
  · intro hb V h
    exact (key V h).1 (hb (j ⁻¹ᵁ V) ((Opens.map j.base).monotone h))
  · intro hb V' h'
    obtain ⟨V, hVO, rfl⟩ : ∃ V, V ≤ O ∧ V' = j ⁻¹ᵁ V :=
      ⟨j ''ᵁ V', (j.image_mono h').trans (j.image_preimage_le O), (j.preimage_image_eq V').symm⟩
    exact (key V hVO).2 (hb V hVO)
end GroundTheory.Arith.SchemeCoh
