-- Prove2me | solution 1 for NarrowDNF.HatamiResidual.fires_congr_atom
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:14:47.695788+00:00
-- url     : https://prove2.me/submissions/5904252e-d72c-4937-a775-c8bddba2a668

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.HatamiResidual
end NarrowDNF.HatamiResidual

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure

section


/-! Local activation families and their adaptive atoms. The global-input encoding
of a local activation carries an explicit locality proof, so it does not grant
an activation access to coordinates outside its indexing set. -/
namespace NarrowDNF





namespace Activation
variable {ι : Type*} [DecidableEq ι]











omit [DecidableEq ι] in
private theorem mem_active_of_fires {J : Activation ι} {S : Finset ι} {x : Cube ι}
    (h : J.fires S x) {i : ι} (hi : i ∈ S) : i ∈ J.active x := ⟨S, hi, h⟩









end Activation
end NarrowDNF


end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.HatamiResidual
open ProductMeasure
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι] in
/-- Any local activation has constant firing status on its own adaptive atoms. -/
theorem solution (J : Activation ι) (T : Finset ι) {x y : Cube ι}
    (hxy : J.SameAtom x y) : J.fires T x ↔ J.fires T y := by
  constructor
  · intro hx
    apply (J.locality T x y ?_).mp hx
    intro i hi
    exact hxy.2 i (Activation.mem_active_of_fires hx hi)
  · intro hy
    apply (J.locality T y x ?_).mp hy
    intro i hi
    have hiy := Activation.mem_active_of_fires hy hi
    have hix : i ∈ J.active x := hxy.1 ▸ hiy
    exact (hxy.2 i hix).symm
