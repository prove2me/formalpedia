-- Prove2me | solution 1 for GlobalTheory.SW.unip_mem_symplecticGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:31:24.053538+00:00
-- url     : https://prove2.me/submissions/f120663a-911b-441b-a353-100846d63afe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticEqParabolicJParabolicJParabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open private exists_symmetric_X_isUnit_det_add_mul_of_symplectic from Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory GlobalTheory.SW
namespace GlobalTheory.SW
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℚ}
    (hX : X.IsSymm) : (fromBlocks 1 X 0 1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) ∈ symplecticGroup ι ℚ := by
  simp [SymplecticGroup.fromBlocks_mem_iff, hX.eq]
end GlobalTheory.SW
