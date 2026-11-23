-- Prove2me | solution 1 for GlobalTheory.LocMod.Inhab.isBichar_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:38.700326+00:00
-- url     : https://prove2.me/submissions/b1fbc85b-115a-439f-8840-c2c124a77a60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.PlaceModel Filter
open scoped Topology
open GlobalTheory GlobalTheory.LocMod GlobalTheory.LocMod.Inhab
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
namespace GlobalTheory.LocMod.Inhab
theorem _root_.solution (ψ : AddChar k Circle) : IsBichar (pairing (Y := Y) (Y' := Y') ψ) where
  left a b y := by simp [pairing, mul_add, Finset.sum_add_distrib, AddChar.map_add_eq_mul]
  right a b y := by simp [pairing, add_mul, Finset.sum_add_distrib, AddChar.map_add_eq_mul]
  zero_left y := by simp [pairing]
  zero_right y := by simp [pairing]
end GlobalTheory.LocMod.Inhab
