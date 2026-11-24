-- Prove2me | solution 1 for GlobalTheory.CNorm.mem_smul_top_iff_repr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:06:54.847543+00:00
-- url     : https://prove2.me/submissions/b435c002-5d18-484f-9bc2-15fc76163967

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteSpanAlgebraMapOfFreeFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
theorem _root_.solution {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (J : Ideal R) (x : M) :
    x ∈ (J • ⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ J := by
  constructor
  · intro hx i
    refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun y z hy hz => ?_)
    · simpa using J.mul_mem_right _ hr
    · simpa using J.add_mem hy hz
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top
end GlobalTheory.CNorm
