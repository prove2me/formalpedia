-- Prove2me | solution 1 for GlobalTheory.TensorUnitSpanTop.span_one_tmul_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:27:42.876312+00:00
-- url     : https://prove2.me/submissions/9e44c610-e938-4d30-860e-7599395def66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanOneTmulEqTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorUnitSpanTop
open TensorProduct
namespace GlobalTheory.TensorUnitSpanTop
theorem _root_.solution {R M : Type} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    {ι : Type} (f : ι → M) (hf : Submodule.span R (Set.range f) = ⊤) :
    Submodule.span (IsLocalRing.ResidueField R)
      (Set.range fun (i : ι) ↦ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f i) = ⊤ := by
  set N := Submodule.span (IsLocalRing.ResidueField R)
      (Set.range fun (i : ι) ↦ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f i) with hN
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul a m =>
    have hm : m ∈ Submodule.span R (Set.range f) := hf ▸ Submodule.mem_top
    have h1 : (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] m ∈ N.restrictScalars R := by
      induction hm using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact Submodule.subset_span ⟨i, rfl⟩
      | zero => simp
      | add y z _ _ hy hz => rw [tmul_add]; exact add_mem hy hz
      | smul r y _ hy => rw [tmul_smul]; exact Submodule.smul_mem _ r hy
    have h2 : a ⊗ₜ[R] m = a • ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] m) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    rw [h2]
    exact N.smul_mem a h1
  | add x y hx hy => exact add_mem hx hy
end GlobalTheory.TensorUnitSpanTop
