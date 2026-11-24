-- Prove2me | solution 1 for GlobalTheory.MonicRootExtension.isLocalHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:58:26.083605+00:00
-- url     : https://prove2.me/submissions/7d050b4a-fb0d-4ba4-817a-26ba3b1fa7bd

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularLocalExtensionWithSimpleRoot
import Theorems.Thm_GlobalTheory_MonicRootExtension_maximalIdeal_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory GlobalTheory.MonicRootExtension
variable {A : Type} [CommRing A] [IsLocalRing A] (M : A[X]) (hM : M.Monic)
  (hirr : Irreducible (M.map (residue A)))
include hM hirr
namespace GlobalTheory.MonicRootExtension
theorem _root_.solution [IsLocalRing (AdjoinRoot M)] : IsLocalHom (algebraMap A (AdjoinRoot M)) := by
  constructor
  intro x hx
  by_contra h
  have h2 : algebraMap A (AdjoinRoot M) x ∈ maximalIdeal (AdjoinRoot M) := by
    rw [← maximalIdeal_eq M hM hirr]; exact Ideal.mem_map_of_mem _ h
  exact h2 hx
end GlobalTheory.MonicRootExtension
