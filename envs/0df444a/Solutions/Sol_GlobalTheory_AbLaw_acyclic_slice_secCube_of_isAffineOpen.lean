-- Prove2me | solution 1 for GlobalTheory.AbLaw.acyclic_slice_secCube_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:11:48.151899+00:00
-- url     : https://prove2.me/submissions/9c5c070e-ff57-439f-9fe4-7a0cce8a9e55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SecOnBasicOpenLocalization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AcyclicSliceSecCubeOfIsAffineOpen
import Theorems.Thm_GlobalTheory_AbLaw_secCubeLE_exactAt
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_cubeComplex_exactAt_succ_iff
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
variable {Y : Scheme.{0}} (M : LB Y)
variable {M}
namespace GlobalTheory.AbLaw
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (μ κ : Type) [LinearOrder μ] [LinearOrder κ] [Fintype κ] (D : μ → Y.Opens) (e : κ ↪o μ) (s₀ : Finset μ), M.IsLB → (⨅ i ∈ s₀, D i) ≤ ⨆ k, D (e k) → (∀ t : Finset κ, IsAffineOpen (⨅ i ∈ s₀ ∪ t.map e.toEmbedding, D i)) → (cubeComplex (Cube.slice e s₀ (secCube f M D))).Acyclic := by
  intro R _ Y f M μ κ _ _ _ D e s₀ hM hc ha p
  let V : Finset κ → Y.Opens := fun t => ⨅ i ∈ s₀ ∪ t.map e.toEmbedding, D i
  have hV : Antitone V := fun _ _ h => iInf_le_iInf_of_subset D (Cube.monotone_union_map e s₀ h)
  have H := secCubeLE_exactAt hM V hV ha (fun k => D (e k))
    ((iInf_le_iInf_of_subset D Finset.subset_union_left).trans hc) (fun k s => by
      simp only [V, Finset.map_insert, Finset.union_insert, Finset.iInf_insert]
      exact le_inf inf_le_right inf_le_left)
  have hd (q : ℕ) (x : Cube.Term (Cube.slice e s₀ (secCube f M D)) q) :
      Cube.d (Cube.slice e s₀ (secCube f M D)) q x = Cube.d (secCubeLE M V hV) q x :=
    funext fun t => (Cube.d_apply _ q x t).trans (Cube.d_apply (secCubeLE M V hV) q x t).symm
  cases p with
  | zero =>
    rw [cubeComplex_exactAt_zero_iff']
    exact fun x y h => (cubeComplex_exactAt_zero_iff' _).1 (H 0) ((hd 0 x).symm.trans (h.trans (hd 0 y)))
  | succ p =>
    rw [cubeComplex_exactAt_succ_iff]
    intro x
    refine ⟨fun hx => ?_, by rintro ⟨y, rfl⟩; exact Cube.d_d _ p y⟩
    obtain ⟨y, hy⟩ := ((cubeComplex_exactAt_succ_iff _ p).1 (H (p + 1)) x).1 ((hd _ x).symm.trans hx)
    exact ⟨y, (hd p y).trans hy⟩
end GlobalTheory.AbLaw
