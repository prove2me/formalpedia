-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.splitsCompletely_kummerExtension_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:45:23.070799+00:00
-- url     : https://prove2.me/submissions/6c5c823e-aa25-4b78-95f5-d966b3f9d533

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Degree
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_SplittingInfinite
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_SplittingKummer
import Theorems.Thm_GroundTheory_Global_finrank_eq_one_iff_of_kummerExtension
import Theorems.Thm_GroundTheory_Global_InfinitePlace_nonempty_placesOver
import Theorems.Thm_GroundTheory_Global_InfinitePlace_splitsCompletely_iff_forall_finrank
import Theorems.Thm_GroundTheory_Global_nonempty_placesOver
import Theorems.Thm_GroundTheory_Global_splitsCompletely_iff_forall_finrank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField Module IntermediateField GroundTheory.ProfCoh
open scoped TensorProduct
variable {K : Type*} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosed Ω] {Δ : Subgroup Kˣ}
  [Finite (Δ ⧸ (unitsPow K n).subgroupOf Δ)]
open scoped NumberField.LiesOver
namespace GroundTheory.Global
namespace InfinitePlace
theorem _root_.solution (v : NumberField.InfinitePlace K) :
    InfinitePlace.SplitsCompletely (kummerExtension K n Ω Δ) v ↔
      ∀ a ∈ Δ, ∃ x : v.Completion, x ^ n = algebraMap K v.Completion (a : K) := by
  have key (w : v.placesOver (kummerExtension K n Ω Δ)) :=
    finrank_eq_one_iff_of_kummerExtension
      ((Pi.evalAlgHom v.Completion _ w).comp
        (InfinitePlace.tensorPiHom (L := kummerExtension K n Ω Δ) v))
      ((Function.surjective_eval w).comp
        (InfinitePlace.tensorPiHom_surjective (L := kummerExtension K n Ω Δ) v))
  rw [InfinitePlace.splitsCompletely_iff_forall_finrank]
  refine ⟨fun h ↦ ?_, fun h w ↦ (key w).2 h⟩
  obtain ⟨w⟩ := InfinitePlace.nonempty_placesOver (kummerExtension K n Ω Δ) v
  exact (key w).1 (h w)
end InfinitePlace
end GroundTheory.Global
