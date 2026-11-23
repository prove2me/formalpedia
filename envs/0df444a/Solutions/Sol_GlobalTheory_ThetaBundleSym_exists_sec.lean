-- Prove2me | solution 1 for GlobalTheory.ThetaBundleSym.exists_sec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:14:57.095737+00:00
-- url     : https://prove2.me/submissions/0e04d89d-5ea8-4501-8586-a28d7b12af6a

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfComplexPoints
import Theorems.Thm_GlobalTheory_ThetaBundleSym_le_of_complex_points
import Theorems.Thm_GlobalTheory_top_le_preimage_inf
import Theorems.Thm_P2M_GlobalTheory_valAt__map_238ef0722272
import Theorems.Thm_P2M_GlobalTheory_valAt__mul_dca2439ccec2
import Theorems.Thm_P2M_GlobalTheory_valAt__res_db2aea6d876c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaBundleSym
variable {X : Over (Sp ℂ)} [LocallyOfFiniteType X.hom] {Z : Type} {ex : Z → (𝟙_ (Over (Sp ℂ)) ⟶ X)}
namespace GlobalTheory.ThetaBundleSym
theorem _root_.solution (hex : Function.Surjective ex)
    (hext : ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U →
      valAt' x.left U f = valAt' x.left U f') → f = f')
    (M : LB X.left) (v : M.ι → Z → ℂ)
    (hv : ∀ i, ∃ (W : X.left.Opens) (φ : Γ(X.left, W)), ∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ M.U i →
      ⊤ ≤ (ex z).left ⁻¹ᵁ W ∧ valAt' (ex z).left W φ = v i z)
    (hc : ∀ i j z, ⊤ ≤ (ex z).left ⁻¹ᵁ M.U i → ⊤ ≤ (ex z).left ⁻¹ᵁ M.U j →
      v i z = valAt' (ex z).left (M.U i ⊓ M.U j) (M.g i j).val * v j z) :
    ∃ s : M.Sec, ∀ i z, ⊤ ≤ (ex z).left ⁻¹ᵁ M.U i → valAt' (ex z).left (M.U i) (s.f i) = v i z := by
  choose W φ hφ using hv
  have hle : ∀ i, M.U i ≤ W i := fun i => le_of_complex_points hex fun z hz => (hφ i z hz).1
  have hval : ∀ i z, ⊤ ≤ (ex z).left ⁻¹ᵁ M.U i →
      valAt' (ex z).left (M.U i) (resG X.left (hle i) (φ i)) = v i z := fun i z hz =>
    (valAt'_res _ (hle i) (φ i) hz).trans (hφ i z hz).2
  refine ⟨⟨fun i => resG X.left (hle i) (φ i), fun i j => hext _ _ _ fun x hx => ?_⟩, hval⟩
  obtain ⟨z, rfl⟩ := hex x
  obtain ⟨hi, hj⟩ := (top_le_preimage_inf _ _ _).1 hx
  rw [valAt'_mul, valAt'_map _ _ _ hx, valAt'_map _ _ _ hx, hval i z hi, hval j z hj, hc i j z hi hj]
end GlobalTheory.ThetaBundleSym
