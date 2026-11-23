-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.secLin_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:15:35.49965+00:00
-- url     : https://prove2.me/submissions/2cdac159-1a0e-43b0-af51-27b7eecaaef3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExpF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sval_smul__9bcebbd1d3c5
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sval_sum__11871ebd81a9
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sec_ext__7d36e2669680
import Theorems.Thm_GlobalTheory_FieldBaseChange_secLin_iff_val

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
theorem _root_.solution (hL : L.IsLB) {φ₁ : K' → (Y' ⟶ X)} {ε₁ : K' → ℤ} (s₁ : SecOver π' (LB.LinComb L φ₁ ε₁))
    {n : ℕ} (s : Fin n → LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (c : Fin n → R')
    (t : Fin n → SecOver π' (LB.LinComb L φ₁ ε₁))
    (ht : ∀ i y J, Good L y J → sval (t i) (𝟙 Y') y J = sval (s i) (𝟙 Y' ≫ h) y J) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ ε s h (fun i => scal π' (c i)) ↔ s₁ = ∑ i, c i • t i := by
  refine (secLin_iff_val hL s₁ s h _).trans ?_
  have e : ∀ y J, Good L y J → ∑ i, gs (𝟙 Y') y ⊤ (scal π' (c i)) * sval (s i) (𝟙 Y' ≫ h) y J =
      sval (∑ i, c i • t i : SecOver π' _) (𝟙 Y') y J := fun y J hJ => by
    rw [sval_sum' hJ]
    exact Finset.sum_congr rfl fun i _ => by rw [sval_smul' hJ, gs_scal, ht i y J hJ]
  exact ⟨fun H => sec_ext' hL fun y J hJ => (H y J hJ).trans (e y J hJ),
    fun H y J hJ => by rw [e y J hJ, H]⟩
end GlobalTheory.FieldBaseChange
