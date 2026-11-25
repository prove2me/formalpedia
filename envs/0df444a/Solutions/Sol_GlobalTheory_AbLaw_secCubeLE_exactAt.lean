-- Prove2me | solution 1 for GlobalTheory.AbLaw.secCubeLE_exactAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:59:08.434152+00:00
-- url     : https://prove2.me/submissions/5bbf5e53-680d-454d-93ad-b136f4e33325

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SecOnBasicOpenLocalization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AcyclicSliceSecCubeOfIsAffineOpen
import Theorems.Thm_GlobalTheory_AbLaw_restrict_torsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (hM : M.IsLB) {κ : Type} [LinearOrder κ] [Finite κ]
    (V : Finset κ → Y.Opens) (hV : Antitone V) (ha : ∀ s, IsAffineOpen (V s)) (U : κ → Y.Opens)
    (hU : V ∅ ≤ ⨆ k, U k) (hVU : ∀ k s, V s ⊓ U k ≤ V (insert k s)) (p : ℕ) :
    (cubeComplex (secCubeLE M V hV)).ExactAt p := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]
  refine subsingleton_of_forall_eq 0 fun x => ?_
  let S : Set Γ(Y, V ∅) := {a | ∃ k, Y.basicOpen a ≤ U k}
  have hS : Ideal.span S = ⊤ := by
    rw [← (ha ∅).self_le_iSup_basicOpen_iff]
    intro y hy
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hU hy)
    obtain ⟨a, h₁, h₂⟩ := (ha ∅).exists_basicOpen_le (V := U k) ⟨y, hk⟩ hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, k, h₁⟩, h₂⟩
  refine (Submodule.mem_bot _).1 (Submodule.mem_of_span_eq_top_of_smul_pow_mem ⊥ _ hS x ?_)
  rintro ⟨a, k, hk⟩
  have key (s : Finset κ) := restrict_torsion hM (ha s) (ha (insert k s))
    (hV (Finset.empty_subset s)) (hV (Finset.subset_insert k s)) a
    ((inf_le_inf_left _ hk).trans (hVU k s))
  obtain ⟨_, ⟨n, rfl⟩, h⟩ := cubeComplex_exists_smul_homology_eq_zero (secCubeLE M V hV)
    (.powers a) k
    (fun s _ y hy => by
      obtain ⟨n, hn⟩ := (key s).1 y hy
      exact ⟨_, ⟨n, rfl⟩, hn⟩)
    (fun s _ z => by
      obtain ⟨n, y, hn⟩ := (key s).2 z
      exact ⟨_, ⟨n, rfl⟩, y, hn⟩) p x
  exact ⟨n, h⟩
end GlobalTheory.AbLaw
