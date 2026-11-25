-- Prove2me | solution 1 for GlobalTheory.AbLaw.acyclic_comap_secCube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:46:27.585087+00:00
-- url     : https://prove2.me/submissions/9536c0e7-2b55-4d17-8e9e-c12c20539bb0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AcyclicSliceSecCubeOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineOpenBiInfOfLe
import Theorems.Thm_GlobalTheory_AbLaw_isAffineOpen_biInf_of_le
import Theorems.Thm_GlobalTheory_AbLaw_acyclic_slice_secCube_of_isAffineOpen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
variable {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R)) {M : LB Y}
  {ν κ : Type}
namespace GlobalTheory.AbLaw
theorem _root_.solution [LinearOrder ν] [LinearOrder κ] [Fintype κ] (hM : M.IsLB)
    (E : ν → Y.Opens) (hE : ∀ i V, IsAffineOpen V → IsAffineOpen (E i ⊓ V)) (e : κ ↪o ν)
    (hc : ⨆ k, E (e k) = ⊤) (s₀ : Finset ν) {V : Y.Opens} (hV : IsAffineOpen V)
    (h : ⨅ i ∈ s₀, E i ≤ V) (g : Finset κ → Finset ν) (hg : Monotone g)
    (hgs : ∀ t, g t = s₀ ∪ t.map e.toEmbedding) :
    (cubeComplex (Cube.comap g hg (secCube f M E))).Acyclic := by
  rw [Cube.comap_congr hg (Cube.monotone_union_map e s₀) hgs]
  exact acyclic_slice_secCube_of_isAffineOpen R Y f M ν κ E e s₀ hM (hc ▸ le_top) fun t =>
    isAffineOpen_biInf_of_le E hE _ hV
      ((iInf_le_iInf_of_subset E Finset.subset_union_left).trans h)
end GlobalTheory.AbLaw
