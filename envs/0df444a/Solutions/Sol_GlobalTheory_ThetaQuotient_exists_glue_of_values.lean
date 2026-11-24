-- Prove2me | solution 1 for GlobalTheory.ThetaQuotient.exists_glue_of_values
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:32:57.98133+00:00
-- url     : https://prove2.me/submissions/51c4af95-1cdf-4602-be6f-5fcb34462488

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EvalDivOfIsHomogeneous
import Theorems.Thm_GlobalTheory_top_le_preimage_iff_mem
import Theorems.Thm_GlobalTheory_top_le_preimage_inf
import Theorems.Thm_P2M_GlobalTheory_valAt__map_238ef0722272


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
open GlobalTheory
open GlobalTheory.ThetaQuotient
namespace GlobalTheory.ThetaQuotient
theorem _root_.solution {X : Over (Sp ℂ)}
    (hext : ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)),
      (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f')
    {κ : Type} (V : κ → X.left.Opens) (s : ∀ i, Γ(X.left, V i)) (a : (𝟙_ (Over (Sp ℂ)) ⟶ X) → ℂ)
    (hs : ∀ i x, ⊤ ≤ x.left ⁻¹ᵁ V i → valAt' x.left (V i) (s i) = a x) :
    ∃ φ : Γ(X.left, ⨆ i, V i), ∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ x.left ⁻¹ᵁ (⨆ i, V i) →
      valAt' x.left (⨆ i, V i) φ = a x := by
  obtain ⟨φ, hφ, -⟩ := X.left.sheaf.existsUnique_gluing V s (by
    intro i j
    refine hext _ _ _ fun x hx => ?_
    obtain ⟨hi, hj⟩ := (top_le_preimage_inf x.left _ _).1 hx
    refine (valAt'_map x.left _ (s i) hx).trans (Eq.trans ?_ (valAt'_map x.left _ (s j) hx).symm)
    rw [hs i x hi, hs j x hj])
  refine ⟨φ, fun x hx => ?_⟩
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 ((top_le_preimage_iff_mem x.left _).1 hx)
  have hi' := (top_le_preimage_iff_mem x.left _).2 hi
  rw [← hs i x hi', ← hφ i]
  exact (valAt'_map x.left _ φ hi').symm
end GlobalTheory.ThetaQuotient
