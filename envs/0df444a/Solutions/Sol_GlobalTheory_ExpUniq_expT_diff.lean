-- Prove2me | solution 1 for GlobalTheory.ExpUniq.expT_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:47:42.054232+00:00
-- url     : https://prove2.me/submissions/f520f830-8538-4828-a166-46cf5ffc14b0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfWeightSum
import Theorems.Thm_GlobalTheory_ExpUniq_sval_diffSec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.ExpUniq
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {U : PreU I D A G} {T : Over (Spec (CommRingCat.of R))} {k : ℕ} {σ σ' : U.SecGT T k} {f f' : ∀ α, SecBT D T k α}
namespace GlobalTheory.ExpUniq
theorem _root_.solution (h : U.ExpT T k σ f) (h' : U.ExpT T k σ' f') :
    U.ExpT T k (diffSec σ σ') (fun α => diffSec (f α) (f' α)) := fun e => by
  classical
  obtain ⟨s, hs⟩ := h e
  obtain ⟨s', hs'⟩ := h' e
  refine ⟨s ∪ s', fun Z x rG rB h₁ h₂ h₃ z JG J hJG hJ => ?_⟩
  obtain ⟨a, b⟩ := hs Z x rG rB h₁ h₂ h₃ z JG J hJG hJ
  obtain ⟨a', b'⟩ := hs' Z x rG rB h₁ h₂ h₃ z JG J hJG hJ
  refine ⟨fun α hα => ?_, ?_⟩
  · rw [Finset.mem_union, not_or] at hα
    rw [sval_diffSec _ _ _ hJ, a α hα.1, a' α hα.2, sub_zero]
  · rw [sval_diffSec _ _ _ hJG, mul_sub, b, b',
      Finset.sum_subset (Finset.subset_union_left (s₂ := s')) (fun α _ hα => by rw [a α hα, zero_mul]),
      Finset.sum_subset (s₁ := s') (Finset.subset_union_right (s₁ := s)) (fun α _ hα => by rw [a' α hα, zero_mul]),
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun α _ => by rw [sval_diffSec _ _ _ hJ, sub_mul]
end GlobalTheory.ExpUniq
