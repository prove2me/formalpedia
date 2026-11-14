-- Prove2me | solution 1 for NarrowDNF.main_narrow_dnf
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T09:07:11.726497+00:00
-- url     : https://prove2.me/submissions/13806cf6-c4be-41c4-804d-402bb30bee36

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_MainStatements
import Theorems.Thm_NarrowDNF_HatamiInput_hatami_arity_load
import Theorems.Thm_NarrowDNF_narrowDNF_of_hatami

namespace NarrowDNF
end NarrowDNF

section


/-!
# Unconditional headline results of Liu–Meng, STOC revision of 2026-11-06

Every external input used by these wrappers is proved in this project. The
wrappers take no Hatami, Bourgain, junta, or approximation assumption.
The proposition definitions expose the paper's complete quantifier order.
-/
namespace NarrowDNF

/-- Lemma 2.1: simultaneous approximation, increasing activation family,
arity, and multiplicity-counted load with the paper's exact parameters. -/
private theorem hatami_arity_load : HatamiArityLoad := HatamiInput.hatami_arity_load





end NarrowDNF


end

open NarrowDNF
/-- Theorem 1.2: dimension- and low-bias-uniform narrow monotone DNF
approximation, with a proved explicit absolute constant. -/
theorem solution : NarrowDNFApproximation := narrowDNF_of_hatami hatami_arity_load
