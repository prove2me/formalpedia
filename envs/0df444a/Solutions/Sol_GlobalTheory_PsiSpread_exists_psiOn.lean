-- Prove2me | solution 1 for GlobalTheory.PsiSpread.exists_psiOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:52:07.453975+00:00
-- url     : https://prove2.me/submissions/dcbdc4c8-7c66-4bc2-aaeb-9df753cd91c0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFiniteCubeInduction
import Theorems.Thm_GlobalTheory_PsiSpread_exists_finite_cube_induction
import Theorems.Thm_GlobalTheory_PsiSpread_exists_extends
import Theorems.Thm_GlobalTheory_PsiSpread_Extends_cube
import Theorems.Thm_GlobalTheory_PsiSpread_nonempty_psiOn
import Theorems.Thm_GlobalTheory_TauPull_jK_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.PsiSpread
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
namespace GlobalTheory.PsiSpread
theorem _root_.solution (hB : D.TauBimult) : ∃ W : (Spec (CommRingCat.of R)).Opens,
    genericPoint (Spec (CommRingCat.of R)) ∈ W ∧ Nonempty (PsiOn D W) := by
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  obtain ⟨S, hS, ind⟩ := exists_finite_cube_induction D.X
  choose V hV ext using fun χ => exists_extends D χ z
  let W : (Spec (CommRingCat.of R)).Opens := ⟨⋂ χ ∈ S, V χ, hS.isOpen_biInter fun χ _ => (V χ).isOpen⟩
  have hz : jK R z ∈ W := Set.mem_iInter₂.2 fun χ _ => hV χ
  let κ : TK R ⟶ TW W := Over.homMk (IsOpenImmersion.lift W.ι (jK R) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact TauPull.jK_mem y W ⟨_, hz⟩)) (IsOpenImmersion.lift_fac _ _ _)
  refine ⟨W, ?_, nonempty_psiOn D κ (ind _ (fun χ hχ => ext χ W (fun x hx => Set.mem_iInter₂.1 hx χ hχ) κ)
    (Extends.cube D hB κ))⟩
  exact ((genericPoint_spec (Spec (CommRingCat.of R))).mem_open_set_iff W.isOpen).2 ⟨_, trivial, hz⟩
end GlobalTheory.PsiSpread
