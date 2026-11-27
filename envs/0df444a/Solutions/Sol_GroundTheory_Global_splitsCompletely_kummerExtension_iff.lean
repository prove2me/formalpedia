-- Prove2me | solution 1 for GroundTheory.Global.splitsCompletely_kummerExtension_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:46:46.992826+00:00
-- url     : https://prove2.me/submissions/82663bfa-67d0-4c02-bc1a-598d49e485c3

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
open SemiLocal
namespace GroundTheory.Global
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) :
    SplitsCompletely (kummerExtension K n Ω Δ) v ↔
      ∀ a ∈ Δ, ∃ x : v.adicCompletion K, x ^ n = algebraMap K (v.adicCompletion K) (a : K) := by
  have key (w : PlacesOver (kummerExtension K n Ω Δ) v) :=
    finrank_eq_one_iff_of_kummerExtension
      ((Pi.evalAlgHom (v.adicCompletion K) _ w).comp
        (tensorEquiv (kummerExtension K n Ω Δ) v).toAlgHom)
      ((Function.surjective_eval w).comp (tensorEquiv (kummerExtension K n Ω Δ) v).surjective)
  rw [splitsCompletely_iff_forall_finrank]
  refine ⟨fun h ↦ ?_, fun h w ↦ (key w).2 h⟩
  obtain ⟨w⟩ := nonempty_placesOver (kummerExtension K n Ω Δ) v
  exact (key w).1 (h w)
end GroundTheory.Global
