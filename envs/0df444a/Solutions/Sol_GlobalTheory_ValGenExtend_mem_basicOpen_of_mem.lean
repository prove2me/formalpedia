-- Prove2me | solution 1 for GlobalTheory.ValGenExtend.mem_basicOpen_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:30:35.114571+00:00
-- url     : https://prove2.me/submissions/9946186b-b463-47f7-99cb-a02c773e5fff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulSecNonzeroOnSpecialFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GeneratorExtendsFromGenericFibreValuationRing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.ValGenExtend
namespace GlobalTheory.ValGenExtend
theorem _root_.solution {X : Scheme.{0}} {L : LB X} (s : LB.Sec L) {x : X}
    (hx : x ∈ Out.nonzeroLocus s) {i : L.ι} (hi : x ∈ L.U i) : x ∈ X.basicOpen (s.f i) := by
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have h := congrArg X.basicOpen (s.compat i k)
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (L.g i k).isUnit] at h
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at h
  have hm : x ∈ L.U i ⊓ L.U k := ⟨hi, X.basicOpen_le _ hk⟩
  exact (h.ge (⟨hm, hm, hk⟩ : x ∈ _ ⊓ (_ ⊓ X.basicOpen (s.f k)))).2
end GlobalTheory.ValGenExtend
