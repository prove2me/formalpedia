-- Prove2me | solution 1 for GlobalTheory.Published.IsHilbertClassField.unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:19.816516+00:00
-- url     : https://prove2.me/submissions/919c6b33-6a58-4324-86f9-f19b12454533

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
omit [NumberField K]
namespace GlobalTheory.Published
namespace IsHilbertClassField
theorem _root_.solution {H H' : IntermediateField K ℂ} (h : IsHilbertClassField H)
    (h' : IsHilbertClassField H') : H = H' :=
  le_antisymm (h'.2 H h.1) (h.2 H' h'.1)
end IsHilbertClassField
end GlobalTheory.Published
