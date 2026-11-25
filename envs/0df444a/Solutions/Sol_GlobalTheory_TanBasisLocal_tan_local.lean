-- Prove2me | solution 1 for GlobalTheory.TanBasisLocal.tan_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:18:41.112056+00:00
-- url     : https://prove2.me/submissions/d351172b-996b-46e2-8cf9-5b263a8076d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsTangentVectorBasisAtPointBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TanBasisLocal
import Theorems.Thm_GlobalTheory_TanBasisLocal_dual_ext
import Theorems.Thm_GlobalTheory_TanBasisLocal_base_ext
import Theorems.Thm_GlobalTheory_TanBasisLocal_fst_dual
import Theorems.Thm_GlobalTheory_TanBasisLocal_one_pull
import Theorems.Thm_Formalism_L2_Pj_dualMap_alg
import Theorems.Thm_Formalism_L2_Pj_spMap_comp_ring
import Theorems.Thm_GlobalTheory_SqZero_dual_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open GlobalTheory GlobalTheory.TanBasisLocal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
namespace GlobalTheory.TanBasisLocal
theorem _root_.solution {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {n : ℕ} {h : Fin n → S}
    (hs : Ideal.span (Set.range h) = ⊤) {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (hv : ∀ i, IsTanAt (spMap (algebraMap S (Localization.Away (h i))) ≫ x)
      (spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ v)) : IsTanAt x v := by
  refine ⟨dual_ext hs fun i => ?_, base_ext hs fun i => ?_⟩
  · rw [← Category.assoc, (hv i).1, ← Category.assoc, ← Category.assoc, spMap_comp_ring, spMap_comp_ring,
      dualMap_alg]
  · rw [one_pull, ← (hv i).2, ← Category.assoc, ← Category.assoc, spMap_comp_ring, spMap_comp_ring, fst_dual]
end GlobalTheory.TanBasisLocal
