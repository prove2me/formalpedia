-- Prove2me | solution 1 for OAI.Laughlin.Fock.limitFourColumn_physical_L_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T17:48:12.031028+00:00
-- url     : https://prove2.me/submissions/c7ce6b72-4cef-4f62-a12c-80ee0a2f2a3a

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L012
import Definitions.Def_OAIQ050L014
import Theorems.Thm_OAI_Laughlin_Fock_limitFourColumn_adjoint_s50
import Theorems.Thm_OAI_Laughlin_Fock_weightedFourEnd_readout_s50
import Theorems.Thm_OAI_Laughlin_Spin_limitSliceCoefficient_antisymmetric_s50
import Theorems.Thm_OAI_Laughlin_Spin_source_fourBody_Slater_coefficient_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_Inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationInner_smul_right (Q : ℕ) (c : ℂ) (x y : Space Q) :
    occupationInner Q x (c • y) = c * occupationInner Q x y := by
  simp [occupationInner,Finset.mul_sum,mul_left_comm]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_Bidegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupation_empty (Q : ℕ) : occupationBasis Q ∅ = (1 : Space Q) := by
  let A : Set.powersetCard (Fin (Q+1)) 0 := ⟨∅,rfl⟩
  change (Pi.basisFun ℂ (Fin (Q+1))).ExteriorAlgebra A.val = _
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simp [ExteriorAlgebra.ιMulti_family,ExteriorAlgebra.ιMulti_zero_apply]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_SliceCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem sum_pairLimit_slice (D r a b c d : ℕ) (hab : a < b) (hT : a+b+c+d=D+1) :
    (∑ p ∈ Finset.range (D+1), Real.sqrt 2 * pairLimitCoefficient p a b *
      limitSliceCoefficient r D p c d) = limitSlaterTerm D r a b c d := by
  rw [Finset.sum_eq_single (a+b-1)]
  · rw [limitSliceCoefficient,ite_eq_left (by omega)]
    rfl
  · intro p hp hne
    have h : a+b ≠ p+1 := by omega
    simp [pairLimitCoefficient,h]
  · intro h
    have hm : a+b-1 ∈ Finset.range (D+1) := Finset.mem_range.mpr (by omega)
    exact (h hm).elim

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_PhysicalSlaterReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem limitFourCopyEnd_Slater_readout (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r)
    (a b c d : Fin (Q+1)) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hT : a.val+b.val+c.val+d.val=D+1) :
    limitFourCopyEnd Q r D (create a (create b (create c (create d (1 : Space Q))))) =
      (limitSlaterCoefficient D r a.val b.val c.val d.val : ℂ) • (1 : Space Q) := by
  simp only [limitFourCopyEnd,LinearMap.sum_apply]
  simp_rw [weightedFourEnd_readout_s50 Q _ _
    (fun j k => limitSliceCoefficient_antisymmetric_s50 r D _ j.val k.val hr hor)]
  rw [← Finset.sum_smul,← Complex.ofReal_sum]
  apply congrArg (fun v : ℝ => (v : ℂ) • (1 : Space Q))
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
  rw [sum_pairLimit_slice D r a.val b.val c.val d.val hab hT,
    sum_pairLimit_slice D r a.val c.val b.val d.val (by exact_mod_cast lt_trans hab hbc) (by omega),
    sum_pairLimit_slice D r a.val d.val b.val c.val (by exact_mod_cast lt_trans hab (lt_trans hbc hcd)) (by omega),
    sum_pairLimit_slice D r b.val c.val a.val d.val hbc (by omega),
    sum_pairLimit_slice D r b.val d.val a.val c.val (by exact_mod_cast lt_trans hbc hcd) (by omega),
    sum_pairLimit_slice D r c.val d.val a.val b.val hcd (by omega)]
  rfl

theorem source_fourBody_physical_L (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r)
    (a b c d : Fin (Q+1)) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hT : a.val+b.val+c.val+d.val=D+1) :
    limitFourCopyEnd Q r D (create a (create b (create c (create d (1 : Space Q))))) =
      ((Real.sqrt (sourceCopyWeight D r /
        ((a.val.factorial : ℝ)*b.val.factorial*c.val.factorial*d.val.factorial)) *
        (Certificate.L D r (a.val,b.val,c.val,d.val) : ℝ) : ℝ) : ℂ) • (1 : Space Q) := by
  rw [limitFourCopyEnd_Slater_readout Q r D hr hor a b c d hab hbc hcd hT,
    source_fourBody_Slater_coefficient_s50 D r a.val b.val c.val d.val hr hor hab hbc hcd hT]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_PhysicalColumn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem occupationInner_vacuum (Q : ℕ) : occupationInner Q (1 : Space Q) 1 = 1 := by
  rw [← occupation_empty Q]
  simp [occupationInner,Module.Basis.repr_self,Finsupp.single_apply]

theorem limitFourColumn_physical_L_s50_oai (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r)
    (a b c d : Fin (Q+1)) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hT : a.val+b.val+c.val+d.val=D+1) :
    occupationInner Q (limitFourColumn Q r D)
      (create a (create b (create c (create d (1 : Space Q))))) =
      ((Real.sqrt (sourceCopyWeight D r /
        ((a.val.factorial : ℝ)*b.val.factorial*c.val.factorial*d.val.factorial)) *
        (Certificate.L D r (a.val,b.val,c.val,d.val) : ℝ) : ℝ) : ℂ) := by
  rw [limitFourColumn_adjoint_s50,source_fourBody_physical_L Q r D hr hor a b c d hab hbc hcd hT,
    occupationInner_smul_right,occupationInner_vacuum,mul_one]

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.limitFourColumn_physical_L_s50_oai := @OAI.Laughlin.Fock.limitFourColumn_physical_L_s50_oai
