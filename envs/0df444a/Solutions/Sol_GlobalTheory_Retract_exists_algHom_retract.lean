-- Prove2me | solution 1 for GlobalTheory.Retract.exists_algHom_retract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:16:48.444609+00:00
-- url     : https://prove2.me/submissions/12bd7bfb-02d3-4175-96c5-fcbe7ea22703

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_section_comp
import Theorems.Thm_GlobalTheory_Retract_appLE_comp_appLE
import Theorems.Thm_GlobalTheory_Retract_base_appLE_comp_retraction
import Theorems.Thm_GlobalTheory_Retract_base_appLE_comp_section

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory GlobalTheory.Retract
variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {i : X ⟶ Y} {r : Y ⟶ X}
namespace GlobalTheory.Retract
theorem _root_.solution (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g)
    {U : X.Opens} {V : Y.Opens} {W : S.Opens}
    (hUV : U ≤ i ⁻¹ᵁ V) (hVU : V ≤ r ⁻¹ᵁ U) (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ g ⁻¹ᵁ W) :
    letI := (f.appLE W U hUW).hom.toAlgebra
    letI := (g.appLE W V hVW).hom.toAlgebra
    ∃ (s : Γ(X, U) →ₐ[Γ(S, W)] Γ(Y, V)) (p : Γ(Y, V) →ₐ[Γ(S, W)] Γ(X, U)),
      s.toRingHom = (r.appLE U V hVU).hom ∧ p.toRingHom = (i.appLE V U hUV).hom ∧
        p.comp s = AlgHom.id _ _ := by
  letI := (f.appLE W U hUW).hom.toAlgebra
  letI := (g.appLE W V hVW).hom.toAlgebra
  refine ⟨⟨(r.appLE U V hVU).hom, fun a ↦ ?_⟩, ⟨(i.appLE V U hUV).hom, fun a ↦ ?_⟩, rfl, rfl, ?_⟩
  · exact congr($(base_appLE_comp_retraction hr hVU hUW hVW).hom a)
  · exact congr($(base_appLE_comp_section (section_comp hir hr) hUV hUW hVW).hom a)
  · ext a
    exact congr($(appLE_comp_appLE hir hUV hVU).hom a)
end GlobalTheory.Retract
