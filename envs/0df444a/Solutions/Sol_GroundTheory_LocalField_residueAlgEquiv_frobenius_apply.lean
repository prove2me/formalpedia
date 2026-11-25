-- Prove2me | solution 1 for GroundTheory.LocalField.residueAlgEquiv_frobenius_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:50:34.985288+00:00
-- url     : https://prove2.me/submissions/158db747-2281-40a9-8787-1b3298dd13a1

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois

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
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable (K L)
namespace GroundTheory.LocalField
theorem _root_.solution (h : ramificationIndex K L = 1) (y : 𝓀[L]) :
    residueAlgEquiv K L (frobenius K L h) y = y ^ Nat.card 𝓀[K] := by
  let := Fintype.ofFinite 𝓀[K]
  have : residueAlgEquiv K L (frobenius K L h) =
      FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] 𝓀[L] :=
    (galoisEquivResidue K L h).apply_symm_apply _
  rw [this, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, Fintype.card_eq_nat_card]
end GroundTheory.LocalField
