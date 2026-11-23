-- Prove2me | solution 1 for GlobalTheory.CoeffExt.funCoord_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:10.004064+00:00
-- url     : https://prove2.me/submissions/0dc571a4-7d71-4120-adab-abf8d14267ee

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemFiniteCocyclesIffBcrisTensorCoboundary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoeffExt
open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module
variable {O LL : Type} [CommRing O] [Field LL] [Algebra O LL]
  {V V' : Type} [AddCommGroup V] [AddCommGroup V'] [Module LL V] [Module LL V'] [Module O V]
  [Module O V'] [IsScalarTower O LL V] [IsScalarTower O LL V'] {ι : Type}
namespace GlobalTheory.CoeffExt
theorem _root_.solution (G : Type) (E : V' ≃ₗ[LL] (ι → V)) (c : G → V') (i : ι) (g : G) :
    funCoord O G E c i g = E (c g) i := rfl
end GlobalTheory.CoeffExt
