-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.serializedRows_kernel_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:49:22.872821+00:00
-- url     : https://prove2.me/submissions/fadedb11-0e7f-41a5-b9c1-2eaa9eb05371

import Mathlib
import Definitions.Def_OAIQ081S060
import Definitions.Def_OAIQ081S063
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_SparseCode_supplied_kernel_bound_of_coverage

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramSlotSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators

variable {r D t m : ℕ}

theorem coefficient_filterMap (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (ps : List (Fin D)) (c : Fin m) :
    coefficient (ps.filterMap (slot m shifts Q side v a)) c =
      (ps.map fun p => if (index shifts side v p).val=c.val then Q a p else 0).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    by_cases hm : (index shifts side v p).val < m
    · have he : (⟨(index shifts side v p).val,hm⟩ : Fin m)=c ↔
          (index shifts side v p).val=c.val := Fin.ext_iff
      simpa [coefficient,slot,hm,he] using congrArg
        (fun z => (if (index shifts side v p).val=c.val then Q a p else 0)+z) ih
    · have hn : (index shifts side v p).val≠c.val := by intro h; have := c.isLt; omega
      simpa [coefficient,slot,hm,hn] using ih

theorem coefficient_slots (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (c : Fin m) :
    coefficient (slots m shifts Q side v a) c =
      ∑ p : Fin D, if (index shifts side v p).val=c.val then Q a p else 0 := by
  rw [slots,coefficient_filterMap]
  simpa using (List.sum_toFinset
    (fun p : Fin D => if (index shifts side v p).val=c.val then Q a p else 0)
    (List.nodup_finRange D)).symm

theorem edge_eq_iff (shifts : Fin D → Cayley.Cube r) (side : Bool)
    (v : Cayley.Cube r) (p : Fin D) (e : Cayley.Cube r × Fin D) :
    edge shifts side v p=e ↔ p=e.2 ∧ (if side then e.1+shifts e.2 else e.1)=v := by
  rcases e with ⟨w,q⟩
  cases side
  · simp [edge,Prod.mk.injEq,and_comm,eq_comm]
  · constructor
    · intro h
      have hp : p=q := congrArg Prod.snd h
      subst p
      have hv : v+shifts q=w := congrArg Prod.fst h
      refine ⟨rfl,?_⟩
      rw [←hv]
      simp [add_assoc]
    · rintro ⟨rfl,hv⟩
      apply Prod.ext
      · change v+shifts p=w
        rw [←hv]
        simp [add_assoc]
      · rfl

theorem edge_sum_matrix (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (e : Cayley.Cube r × Fin D) :
    (∑ p : Fin D, if edge shifts side v p=e then Q a p else 0) =
      (Cayley.graph shifts).matrix Q (matrixRow side v a) e := by
  simp_rw [edge_eq_iff]
  rcases e with ⟨w,q⟩
  cases side
  · by_cases h : w=v <;> simp [matrixRow,SparseCode.PortGraph.matrix,h]
  · by_cases h : w+shifts q=v <;> simp [matrixRow,SparseCode.PortGraph.matrix,Cayley.graph,h]

theorem slots_matrix (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (hm : m ≤ 2^r*D) (c : Fin m) :
    coefficient (slots m shifts Q side v a) c =
      (Cayley.graph shifts).matrix Q (matrixRow side v a)
        (SparseCode.edgeEquiv r D (Fin.castLE hm c)) := by
  rw [coefficient_slots]
  have hh (p : Fin D) : (index shifts side v p).val=c.val ↔
      edge shifts side v p=SparseCode.edgeEquiv r D (Fin.castLE hm c) := by
    constructor
    · intro h
      have he : index shifts side v p=Fin.castLE hm c := Fin.ext h
      have hv := congrArg (SparseCode.edgeEquiv r D) he
      simpa [index] using hv
    · intro h
      have hv := congrArg (SparseCode.edgeEquiv r D).symm h
      exact congrArg Fin.val (by simpa [index] using hv)
  simp_rw [hh]
  exact edge_sum_matrix shifts Q side v a _

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The precise order emitted by the native vertex/check loops. Each row is
present even when shortening removes every one of its local ports. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators

variable {r D t m : ℕ}

theorem mem_serializedRows_iff (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (ss : List (Fin m × SparseCode.F3)) :
    ss∈serializedRows m shifts Q ↔
      ∃ side v a, slots m shifts Q side v a=ss := by
  simp only [serializedRows,List.mem_reverse,chronologicalRows,List.mem_flatMap,
    List.mem_finRange,true_and,List.mem_append,List.mem_ofFn]
  constructor
  · rintro ⟨i,⟨a,h⟩|⟨a,h⟩⟩
    · exact ⟨false,WalshExistence.cubeEquiv r i,a,h⟩
    · exact ⟨true,WalshExistence.cubeEquiv r i,a,h⟩
  · rintro ⟨side,v,a,h⟩
    refine ⟨(WalshExistence.cubeEquiv r).symm v,?_⟩
    cases side
    · exact Or.inl ⟨a,by simpa using h⟩
    · exact Or.inr ⟨a,by simpa using h⟩

theorem serializedRows_covers (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (hm : m ≤ 2^r*D)
    (row : (Cayley.Cube r × Fin t) ⊕ (Cayley.Cube r × Fin t)) :
    (fun c => (Cayley.graph shifts).matrix Q row
      (SparseCode.edgeEquiv r D (Fin.castLE hm c))) ∈
      (serializedRows m shifts Q).map coefficient := by
  have one (side : Bool) (v : Cayley.Cube r) (a : Fin t) :
      (fun c => (Cayley.graph shifts).matrix Q (matrixRow side v a)
        (SparseCode.edgeEquiv r D (Fin.castLE hm c))) ∈
        (serializedRows m shifts Q).map coefficient := by
    apply List.mem_map.mpr
    refine ⟨slots m shifts Q side v a,
      (mem_serializedRows_iff shifts Q _).mpr ⟨side,v,a,rfl⟩,?_⟩
    funext c
    exact slots_matrix shifts Q side v a hm c
  cases row with
  | inl va => exact one false va.1 va.2
  | inr va => exact one true va.1 va.2

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramSupplied
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators
open SparseCode

theorem serializedRows_supplied_covers {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (s : SuppliedShifts m B) (Q : SuppliedLocal m B) (i : Fin (totalRows m B)) :
    suppliedMatrix m B hm hB s Q i ∈ (serializedRows m s Q).map coefficient := by
  exact serializedRows_covers s Q (graph_edge_lower hm hB) (rowEquiv m B i)

theorem serializedRows_kernel_bound_oai {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (s : SuppliedShifts m B) (Q : SuppliedLocal m B)
    (hs : WalshExistence.Good (gapDenom m B) s)
    (hQ : HasDistance Q (degree m B / (100*B*logSize m)+1))
    (w : Fin m → F3)
    (hw : ∀ row ∈ serializedRows m s Q, (∑ c, coefficient row c*w c)=0)
    (hw0 : w≠0) : m ≤ distanceDenom m B*weight w := by
  apply supplied_kernel_bound_of_coverage hm hB s Q hs hQ
    ((serializedRows m s Q).map coefficient) (serializedRows_supplied_covers hm hB s Q) w _ hw0
  intro row hrow
  obtain ⟨slots,hslots,rfl⟩ := List.mem_map.mp hrow
  exact hw slots hslots

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.serializedRows_kernel_bound_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.serializedRows_kernel_bound_oai
