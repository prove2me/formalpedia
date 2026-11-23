-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.secScal_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:15:21.603804+00:00
-- url     : https://prove2.me/submissions/f783cc9a-ce67-48d7-9dd6-4d0c9ba1dd58

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExpF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sval_smul__9bcebbd1d3c5
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sec_ext__7d36e2669680
import Theorems.Thm_GlobalTheory_FieldBaseChange_sval_pullOver
import Theorems.Thm_GlobalTheory_FieldBaseChange_secScal_iff_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R R' : Type} [CommRing R] [CommRing R'] {X Y Y' Z : Scheme.{0}}
variable (π : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y)
variable {π} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
variable {π' : Y' ⟶ Spec (CommRingCat.of R')} {f : R →+* R'} {p : Y' ⟶ Y}
  (hp : p ≫ π = π' ≫ Spec.map (CommRingCat.ofHom f)) {φ' : K → (Y' ⟶ X)} (hφ : ∀ k, φ' k = p ≫ φ k)
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution (hL : L.IsLB) (s₁ : SecOver π' (LB.LinComb L φ' ε)) (s : SecOver π (LB.LinComb L φ ε))
    {S : Type} [CommRing S] (π₀ : Y' ⟶ Spec (CommRingCat.of S)) (g : S →+* R')
    (h₀ : π₀ = π' ≫ Spec.map (CommRingCat.ofHom g)) (c : S) :
    GeneratorPullback.SecScal L φ' ε s₁ φ ε s p (scal π₀ c) ↔ pullOver L ε hp hφ s = g c • s₁ := by
  refine (secScal_iff_val hL s₁ s p _).trans ?_
  have e : ∀ y J, Good L y J → (sval s (𝟙 Y' ≫ p) y J = gs (𝟙 Y') y ⊤ (scal π₀ c) * sval s₁ (𝟙 Y') y J ↔
      sval (pullOver L ε hp hφ s) (𝟙 Y') y J = sval (g c • s₁ : SecOver π' _) (𝟙 Y') y J) := fun y J hJ => by
    rw [sval_pullOver hp hφ s _ hJ, sval_smul' hJ, gs_scal, h₀, ← Category.assoc, constVal_specMap]
  exact ⟨fun H => sec_ext' hL fun y J hJ => (e y J hJ).1 (H y J hJ),
    fun H y J hJ => (e y J hJ).2 (by rw [H])⟩
end GlobalTheory.FieldBaseChange
