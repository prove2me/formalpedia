-- Prove2me | solution 1 for GlobalTheory.InfAdeleCM.exists_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:12:13.328511+00:00
-- url     : https://prove2.me/submissions/6c347fff-839e-4338-a18e-9d39f261a476

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
open GlobalTheory GlobalTheory.InfAdeleCM
variable {F : Type} [Field F] [NumberField F]
variable {E : Type} [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.InfAdeleCM
theorem _root_.solution {δ : E} (hs : ∀ x : E, ∃ p q : F, x = algebraMap F E p + algebraMap F E q * δ)
    (z : InfiniteAdeleRing F ⊗[F] E) : ∃ a b : InfiniteAdeleRing F, z = a ⊗ₜ 1 + b ⊗ₜ δ := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a x =>
    obtain ⟨p, q, rfl⟩ := hs x
    refine ⟨p • a, q • a, ?_⟩
    rw [TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul, Algebra.smul_def,
      Algebra.smul_def, mul_one]
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by rw [TensorProduct.add_tmul, TensorProduct.add_tmul]; abel⟩
end GlobalTheory.InfAdeleCM
