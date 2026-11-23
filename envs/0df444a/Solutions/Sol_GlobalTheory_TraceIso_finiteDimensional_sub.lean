-- Prove2me | solution 1 for GlobalTheory.TraceIso.finiteDimensional_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:27.568501+00:00
-- url     : https://prove2.me/submissions/8bc3aeb6-7abb-43ea-b6c6-1e07111503fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyLinearEquivOfCharpolyEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TraceIso
open Module
variable {k A : Type} [Field k] [Ring A] [Algebra k A]
variable {V W : Type} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
namespace GlobalTheory.TraceIso
theorem _root_.solution [FiniteDimensional k V] (P : Submodule A V) : FiniteDimensional k P := inferInstanceAs (FiniteDimensional k (P.restrictScalars k))
end GlobalTheory.TraceIso
