-- Prove2me | solution 1 for GroundTheory.Global.finrank_eq_one_of_tensor_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:56:18.515165+00:00
-- url     : https://prove2.me/submissions/2ed610e8-cb15-4982-a4e5-ae158ec941b6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Degree
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_SplittingInfinite
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_SplittingKummer

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
variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
  {Ω : Type*} [Field Ω] [Algebra K Ω] {Δ : Subgroup Kˣ}
  {F E : Type*} [Field F] [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
  [IsScalarTower K F E]
omit [Algebra K E] [IsScalarTower K F E]
namespace GroundTheory.Global
theorem _root_.solution {A : Type*} [CommRing A] [Algebra K A]
    (g : F ⊗[K] A →ₐ[F] E) (hg : Function.Surjective g)
    (hA : ∀ m : A, g (1 ⊗ₜ m) ∈ (algebraMap F E).fieldRange) : finrank F E = 1 := by
  rw [← Subalgebra.bot_eq_top_iff_finrank_eq_one]
  refine eq_top_iff.2 fun e he ↦ ?_
  clear he
  obtain ⟨t, rfl⟩ := hg e
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul c m =>
    have : c ⊗ₜ[K] m = c • ((1 : F) ⊗ₜ[K] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Subalgebra.smul_mem _ (Algebra.mem_bot.2 (hA m)) c
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
end GroundTheory.Global
