-- Prove2me | solution 1 for GlobalTheory.SemilinearExt.exists_basis_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:17:06.034078+00:00
-- url     : https://prove2.me/submissions/a4959043-e773-49d1-ab58-896e0fc8b1a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SemilinearExtensionBases
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsBasisTensor
import Theorems.Thm_GlobalTheory_SemilinearExt_algebraMap_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open Module
open GlobalTheory GlobalTheory.SemilinearExt
open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases
variable {O K K'' : Type} [CommRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
  {Fm : Type} [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm]
namespace GlobalTheory.SemilinearExt
theorem _root_.solution {ι : Type} (b : Basis ι K Fm) :
    ∃ c : Basis ι K'' (K'' ⊗[O] Fm), ∀ i, c i = (1 : K'') ⊗ₜ[O] b i := by
  have : TensorProduct.CompatibleSMul O K K'' Fm := ⟨fun c x m => by
    rw [Algebra.smul_def, mul_comm, ← smul_eq_mul x, ← TensorProduct.smul_tmul', algebraMap_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]⟩
  refine ⟨(Algebra.TensorProduct.basis K'' b).map (TensorProduct.equivOfCompatibleSMul O K K'' K'' Fm),
    fun i => ?_⟩
  rw [Basis.map_apply, Algebra.TensorProduct.basis_apply]
  rfl
end GlobalTheory.SemilinearExt
