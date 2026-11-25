-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.mem_fixedGrading
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:44:11.928272+00:00
-- url     : https://prove2.me/submissions/91d55751-c29b-4f4d-b3e1-9127378e06d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueHomogeneousIdealFixedSubalgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L G A : Type*} [Field K] [Field L] [Algebra K L] [Group G] [MulSemiringAction G L]
  [Ring A] [Algebra K A] [Algebra L A] [IsScalarTower K L A]
  [MulSemiringAction G A] [SMulDistribClass G L A] [SMulCommClass G K A]
variable {ι : Type*} (𝒜 : ι → Submodule L A)
omit [MulSemiringAction G L] [SMulDistribClass G L A]
namespace GlobalTheory.GaloisDescent
theorem _root_.solution {i : ι} {a : FixedPoints.subalgebra K A G} :
    a ∈ fixedGrading K G 𝒜 i ↔ (a : A) ∈ 𝒜 i := Iff.rfl
end GlobalTheory.GaloisDescent
