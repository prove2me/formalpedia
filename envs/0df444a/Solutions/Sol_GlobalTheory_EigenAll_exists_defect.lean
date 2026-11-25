-- Prove2me | solution 1 for GlobalTheory.EigenAll.exists_defect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:51:27.879802+00:00
-- url     : https://prove2.me/submissions/31b9dc36-f3ba-4b8b-9066-53fe2414b7b9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SectionEqZeroOfForallGeometricPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EigenEquationOfForallGeometricPoint
import Theorems.Thm_GlobalTheory_EigenAll_gs_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.EigenAll
namespace GlobalTheory.EigenAll
theorem _root_.solution {Y G H : Scheme.{0}} (m s : Y ⟶ G) (p : Y ⟶ H) (V : G.Opens) (t : Γ(G, V))
    (u : Γ(H, ⊤)) : ∃ f : Γ(Y, m ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V), ∀ (Z : Scheme.{0}) (g : Z ⟶ Y) (z : Z),
      g z ∈ m ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V → gs g z (m ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V) f =
        gs (g ≫ m) z V t - gs (g ≫ p) z ⊤ u * gs (g ≫ s) z V t := by
  have hp : m ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V ≤ p ⁻¹ᵁ (⊤ : H.Opens) := fun _ _ => trivial
  refine ⟨(Y.presheaf.map (homOfLE inf_le_left).op).hom ((m.app V).hom t) -
    (Y.presheaf.map (homOfLE hp).op).hom ((p.app ⊤).hom u) *
      (Y.presheaf.map (homOfLE inf_le_right).op).hom ((s.app V).hom t), ?_⟩
  intro Z g z hz
  rw [gs_sub g z _ hz, gs_mul g z _ hz, gs_res g z _ hz, gs_res g z _ hz, gs_res g z _ hz,
    gs_pull g m z V hz.1, gs_pull g p z ⊤ trivial, gs_pull g s z V hz.2]
end GlobalTheory.EigenAll
