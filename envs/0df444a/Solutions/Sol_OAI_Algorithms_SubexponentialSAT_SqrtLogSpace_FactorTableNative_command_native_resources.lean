-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.command_native_resources
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:26:40.355646+00:00
-- url     : https://prove2.me/submissions/b7c1e848-30a6-4875-ae32-0a259f7fb325

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S189
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorTableNative_Ready_staged_common
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorTableNative_native_literal
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorTableNative_source_of_masters
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorTableSpace_command_resources
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorTableSpace_staged_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocation and the finite total-variable table traversal. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

attribute [local simp] Fin.coe_ofNat_eq_mod


theorem tableResult_eq (payload : ℕ → List Bool) (n : ℕ) (acc : List Bool) :
    tableResult payload n acc=(List.range n).flatMap (tableRecord payload) ++ acc := by
  induction n generalizing acc with
  | zero => simp [tableResult]
  | succ n ih => simp [tableResult,ih,List.range_succ,List.flatMap_append,List.append_assoc]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyTable
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native descending/prepending loop produces the exact raw incidence
slice consumed by the original-variable literal lookup. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT

theorem tableResult_incidence (payload : ℕ → List Bool) (n : ℕ) :
    tableResult payload n []=Squarefree.Program.lookupRecords
      (HashCircuitProgram.incidenceEntries (fun (_ : Unit) (v : Fin n) => payload v.val) ()) := by
  rw [tableResult_eq]
  simp only [List.append_nil,HashCircuitProgram.incidenceEntries,
    Squarefree.Program.lookupRecords,Subexp.SelectorProgram.rawRecords,List.flatMap_map]
  rw [← List.map_coe_finRange n,List.flatMap_map]
  rfl

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The selected-factor incidence service with a concrete source generator.
All ring/layout inputs are copied from persistent masters, and the complete
private worker is reclaimed after exporting the actual lookup table. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Incidence
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem mem_workerPorts (i : Fin 768) : i ∈ workerPorts ↔ 340 ≤ i.val ∧ i.val < 680 := by
  simp only [workerPorts,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change 340+j.val=i.val at hv
    omega
  · intro hi
    refine ⟨⟨i.val-340,by omega⟩,?_⟩
    apply Fin.ext
    change 340+(i.val-340)=i.val
    omega

end SubexponentialSAT.SqrtLog.LeafProgram.Incidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual selected-factor table runs over ambient variable IDs. Each low
payload is specialized immediately before its framed table entry is retained.
The source scratch embedding excludes persistent layout masters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

private theorem decodeBasePort_low (i : Fin 896) (hi : i.val < 768) :
    decodeBasePort i = i.val := by
  have h885 : i ≠ 885 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h886 : i ≠ 886 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h887 : i ≠ 887 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h888 : i ≠ 888 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h889 : i ≠ 889 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h890 : i ≠ 890 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h891 : i ≠ 891 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h892 : i ≠ 892 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  simp only [decodeBasePort, ite_eq_right h885, ite_eq_right h886, ite_eq_right h887,
    ite_eq_right h888, ite_eq_right h889, ite_eq_right h890, ite_eq_right h891,
    ite_eq_right h892]

private theorem decodeBasePort_basePort (i : Fin 768) : decodeBasePort (basePort i) = i.val := by
  unfold basePort
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · exact decodeBasePort_low _ i.isLt

theorem basePort_injective : Function.Injective basePort := by
  intro i j hij
  apply Fin.ext
  have hv := congrArg decodeBasePort hij
  simpa only [decodeBasePort_basePort] using hv

theorem basePort_protected (i : Fin 768) :
    basePort i ≠ 640 ∧ basePort i ≠ 641 ∧ basePort i ≠ 642 ∧ basePort i ≠ 647 ∧
      basePort i ≠ 650 ∧ basePort i ≠ 651 ∧ basePort i ≠ 670 ∧ basePort i ≠ 671 := by
  simp only [basePort]
  split_ifs <;> simp_all [Fin.ext_iff, Fin.coe_ofNat_eq_mod]

theorem basePort_high (i : Fin 768) :
    (basePort i).val < 768 ∨ (885 ≤ (basePort i).val ∧ (basePort i).val ≤ 892) := by
  simp only [basePort]
  split_ifs <;> simp_all only [Fin.val_castAdd, Fin.coe_ofNat_eq_mod] <;> omega

theorem basePort_outside (i : Fin 896)
    (hi : i ∈ protectedPorts ∨ (768 ≤ i.val ∧ (i.val < 885 ∨ 892 < i.val))) :
    ¬ ∃ j, basePort j = i := by
  rintro ⟨j, hj⟩
  rcases hi with hi | hi
  · simp only [protectedPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
    have hp := basePort_protected j
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.1 hj
    · exact hp.2.1 hj
    · exact hp.2.2.1 hj
    · exact hp.2.2.2.1 hj
    · exact hp.2.2.2.2.1 hj
    · exact hp.2.2.2.2.2.1 hj
    · exact hp.2.2.2.2.2.2.1 hj
    · exact hp.2.2.2.2.2.2.2 hj
  · have hm := basePort_high j
    rw [hj] at hm
    omega

theorem projectBase_update (s : OuterStore) (i : Fin 768) (word : List Bool) :
    projectBase (Function.update s (basePort i) word) = Function.update (projectBase s) i word := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [projectBase]
  · have hne : basePort j ≠ basePort i := fun h => hj (basePort_injective h)
    simp [projectBase, Function.comp_def, hj, hne]


theorem tableResult_original (payload : ℕ → List Bool) (n : ℕ) (acc : List Bool) :
    tableResult payload n acc = PerturbationAssembly.tableResult payload n acc := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih => simpa only [tableResult, PerturbationAssembly.tableResult, tableRecord,
      PerturbationAssembly.tableRecord] using ih (tableRecord payload n ++ acc)

/-- Every ambient coordinate has exactly one framed lookup entry, including
unused coordinates and high coordinates. -/
theorem tableResult_incidence (payload : ℕ → List Bool) (n : ℕ) :
    tableResult payload n [] = Squarefree.Program.lookupRecords
      (HashCircuitProgram.incidenceEntries (fun (_ : Unit) (v : Fin n) => payload v.val) ()) := by
  rw [tableResult_original]
  exact PerturbationAssembly.tableResult_incidence payload n

theorem initialized_empty (a : OuterData) (i : Fin 768)
    (hlo : 340 ≤ i.val) (hhi : i.val < 680) (hne : i ≠ 556) :
    (initialized a).stacks (basePort i) = [] := by
  rw [initialized, SubexpSetupStorage.clearMany_stacks, ite_eq_left]
  apply List.mem_append_left
  apply List.mem_map.mpr
  exact ⟨i, List.mem_filter.mpr ⟨(LeafProgram.Incidence.mem_workerPorts i).mpr ⟨hlo,hhi⟩,
    by simpa using hne⟩, rfl⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyFactorInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One invariant of the physically staged masters yields every per-literal
low-worker precondition. No beta, shifted polynomial, or output table occurs
as an input hypothesis. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls DensePolynomialProgram SubexpConvolutionControl
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem ArithmeticInput.frame_low {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {s u : Store} (h : ArithmeticInput t a M cache s)
    (hf : ∀ i:Fin 256,i.val < 205 → u i=s i) : ArithmeticInput t a M cache u := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hf 194 (by decide)] using h.modulus
  · simpa only [hf 5 (by decide),hf 194 (by decide)] using h.lowModulus
  · simpa only [hf 202 (by decide)] using h.width
  · simpa only [hf 10 (by decide),hf 202 (by decide)] using h.lowWidth
  · simpa only [hf 203 (by decide)] using h.zero
  · simpa only [hf 201 (by decide)] using h.table
  · simpa only [hf 204 (by decide)] using h.degree
  · simpa only [hf 104 (by decide)] using h.fullZero
  · intro i hi hn
    exact (hf i hi).trans (h.clean i hi hn)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblySourceCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual literal-loop call changes only its key, index and accumulated
table. All physical source masters and blank working cells are preserved. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem sourceCallData_frame (s : OuterStore) (j : ℕ) (acc : List Bool)
    (regs : Fin 16 → Bool) (i : Fin 768) (hk : i≠555) (ha : i≠569) (hj : i≠573) :
    (sourceCallData s j acc regs).stacks i=s i := by
  simp only [sourceCallData,literalReady,Function.update_of_ne hk,
    Function.update_of_ne ha,Function.update_of_ne hj]

theorem sourceCallData_index (s : OuterStore) (j : ℕ) (acc : List Bool) (regs : Fin 16 → Bool) :
    (sourceCallData s j acc regs).stacks 573=List.replicate j true := by
  simp [sourceCallData,literalReady]

theorem sourceCallData_clean (s : OuterStore) (j : ℕ) (acc : List Bool)
    (regs : Fin 16 → Bool)
    (h : ∀ i : Fin 340,i∉LeafProgram.SourceReady.physicalLive →
      s (LeafProgram.SourceReady.localPort i)=[]) :
    ∀ i : Fin 340,i∉LeafProgram.SourceReady.physicalLive →
      (sourceCallData s j acc regs).stacks (LeafProgram.SourceReady.localPort i)=[] := by
  intro i hi
  have hn : LeafProgram.SourceReady.localPort i≠555 ∧
      LeafProgram.SourceReady.localPort i≠569 ∧ LeafProgram.SourceReady.localPort i≠573 := by
    constructor
    · intro he
      apply hi
      have hv := congrArg Fin.val he
      have hi215 : i = 215 := by
        apply Fin.ext
        simp [LeafProgram.SourceReady.localPort] at hv
        omega
      simp [LeafProgram.SourceReady.physicalLive, hi215]
    constructor
    · intro he
      apply hi
      have hv := congrArg Fin.val he
      have hi229 : i = 229 := by
        apply Fin.ext
        simp [LeafProgram.SourceReady.localPort] at hv
        omega
      simp [LeafProgram.SourceReady.physicalLive, hi229]
    · intro he
      apply hi
      have hv := congrArg Fin.val he
      have hi233 : i = 233 := by
        apply Fin.ext
        simp [LeafProgram.SourceReady.localPort] at hv
        omega
      simp [LeafProgram.SourceReady.physicalLive, hi233]
  exact (sourceCallData_frame s j acc regs _ hn.1 hn.2.1 hn.2.2).trans (h i hi)

theorem sourceCallData_arithmetic {t d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (a : OuterData) (j : ℕ) (acc : List Bool) (regs : Fin 16 → Bool)
    (h : ArithmeticInput t model M cache (LeafProgram.SourceReady.rawLow a)) :
    ArithmeticInput t model M cache
      (LeafProgram.SourceReady.rawLow (sourceCallData a.stacks j acc regs)) := by
  apply h.frame_low
  intro i hi
  have hn : LeafProgram.SourceReady.localPort (LayoutSourceRowsProgram.executorPorts i)≠555 ∧
      LeafProgram.SourceReady.localPort (LayoutSourceRowsProgram.executorPorts i)≠569 ∧
      LeafProgram.SourceReady.localPort (LayoutSourceRowsProgram.executorPorts i)≠573 := by
    constructor
    · intro he
      have hv := congrArg Fin.val he
      simp [LeafProgram.SourceReady.localPort, LayoutSourceRowsProgram.executorPorts] at hv
      omega
    constructor <;> intro he <;>
      have hv := congrArg Fin.val he <;>
      simp [LeafProgram.SourceReady.localPort, LayoutSourceRowsProgram.executorPorts] at hv <;>
      omega
  exact sourceCallData_frame a.stacks j acc regs _ hn.1 hn.2.1 hn.2.2

theorem sourceInput_at_call {r Q d : ℕ} (p : LayoutProgram.SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ))
    (P : Subexp.ConstructivePacking.PackingData (Fin ps.length) (MulticolorTypes.UniversalType r Q 1))
    (a : OuterData) (v n f S j : ℕ) (acc : List Bool) (regs : Fin 16 → Bool)
    (h : LeafProgram.SourceReady.Input p ps P a v n f S)
    (hsize : ∀ i,((sourceCallData a.stacks j acc regs).stacks i).length ≤ S) :
    LeafProgram.SourceReady.Input p ps P (sourceCallData a.stacks j acc regs) j n f S := by
  constructor
  · exact sourceCallData_arithmetic p.model p.modulus p.cache a j acc regs h.arithmetic
  · exact sourceCallData_clean a.stacks j acc regs h.clean
  · simpa [sourceCallData,literalReady] using h.tmp
  · intro i hi
    have hn : i≠555 ∧ i≠569 ∧ i≠573 := by
      simp only [LeafProgram.SourceStaging.backupPorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> decide
    exact (sourceCallData_frame a.stacks j acc regs i hn.1 hn.2.1 hn.2.2).trans (h.backups i hi)
  · simpa [sourceCallData,literalReady,LeafProgram.SourceReady.localPort] using h.dimension
  · simpa [sourceCallData,literalReady,LeafProgram.SourceReady.localPort] using h.ambient
  · simpa [sourceCallData,literalReady,LeafProgram.SourceReady.localPort] using h.factor
  · simpa [LeafProgram.SourceReady.localPort,LayoutSourcePlanLookup.unary] using
      sourceCallData_index a.stacks j acc regs
  · simpa [sourceCallData,literalReady] using h.colors
  · simpa [sourceCallData,literalReady] using h.nodes
  · simpa [sourceCallData,literalReady] using h.typeWidth
  · simpa [sourceCallData,literalReady] using h.positive
  · simpa [sourceCallData,literalReady] using h.negative
  · simpa [sourceCallData,literalReady] using h.scalarWidth
  · simpa [sourceCallData,literalReady] using h.power
  · exact h.powerNegative
  · simpa [sourceCallData,literalReady] using h.radius
  · simpa [sourceCallData,literalReady] using h.offset
  · simpa [sourceCallData,literalReady] using h.metadata
  · simpa [sourceCallData,literalReady] using h.plans
  · simpa [sourceCallData,literalReady] using h.inverses
  · simpa [sourceCallData,literalReady] using h.negatives
  · simpa [sourceCallData,literalReady] using h.differences
  · simpa [sourceCallData,literalReady] using h.ringWidth
  · simpa [sourceCallData,literalReady] using h.rowWidth
  · simpa [sourceCallData,literalReady] using h.zero
  · simpa [sourceCallData,literalReady] using h.one
  · simpa [sourceCallData,literalReady] using h.minusOne
  · simpa [sourceCallData,literalReady] using h.inverseDenominator
  · exact hsize
  · exact h.arraySize
  · exact h.countSize
  · exact h.metadataSize
  · exact h.incidenceBound

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramIncidenceFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact byte placement and reclamation for the executed incidence worker.
The source cutoff is computed by the staging command, independently of J. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Incidence
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage


private theorem destination_nodup : (pairs.map Prod.snd).Nodup := by
  simp [pairs]

private theorem separated : ∀ p ∈ pairs, ∀ q ∈ pairs, p.1 ≠ q.2 := by
  intro p hp q hq
  have hs : p.1.val < 340 ∨ 700 ≤ p.1.val := by
    simp only [pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> decide
  have hd : 340 ≤ q.2.val ∧ q.2.val < 700 := by
    simp only [pairs,List.mem_cons,List.mem_nil_iff,or_false] at hq
    rcases hq with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst q <;> decide
  intro he
  have hv := congrArg Fin.val he
  omega

private theorem destination_ne_cutoff : ∀ p ∈ pairs, p.2 ≠ 550 := by
  intro p hp
  simp only [pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> decide

/-- All eighteen cache/master copies are exact when their destinations start
empty. This includes runtime theta, the merged assignment, and high context. -/
theorem staged_copy (a : Data) (hz : ∀ p ∈ pairs,a.stacks p.2 = [])
    (p : Fin 768 × Fin 768) (hp : p ∈ pairs) :
    (staged a).stacks p.2 = a.stacks p.1 := by
  change Function.update (copyManyState pairs a).stacks 550 _ p.2 = _
  rw [Function.update_of_ne (destination_ne_cutoff p hp)]
  exact copyMany_value pairs a destination_nodup hz separated p hp

theorem staged_frame (a : Data) (i : Fin 768) (hcut : i ≠ 550)
    (hi : ∀ p ∈ pairs,i ≠ p.2) : (staged a).stacks i = a.stacks i := by
  change Function.update (copyManyState pairs a).stacks 550 _ i = _
  rw [Function.update_of_ne hcut]
  exact copyMany_frame pairs a i hi

end SubexponentialSAT.SqrtLog.LeafProgram.Incidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyStaging
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The common perturbation input invariant follows from the actual paid leaf
staging copies and a clean worker. The full source count is built as R+1. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls DensePolynomialProgram SubexpConvolutionControl
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {t d : ℕ} {a : RingModel.Data d}
  {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
  {J R : ℕ} {theta : Coeff (baseWidth 3 t) d} {s : OuterData} {n : ℕ}

theorem CallerInput.destinations_empty (h : CallerInput t a M cache J R theta s n) :
    ∀ p∈LeafProgram.Incidence.pairs,s.stacks p.2=[] := by
  intro p hp
  have hb : 340 ≤ p.2.val ∧ p.2.val < 680 ∧ p.2≠556 := by
    simp only [LeafProgram.Incidence.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp <;> subst p <;> decide
  exact h.workerEmpty p.2 hb.1 hb.2.1 hb.2.2

theorem CallerInput.staged_high (h : CallerInput t a M cache J R theta s n) :
    ((LeafProgram.Incidence.staged s).stacks 575).length=n := by
  rw [LeafProgram.Incidence.staged_copy s h.destinations_empty (703,575) (by decide)]
  exact h.highLength

theorem CallerInput.staged_empty (h : CallerInput t a M cache J R theta s n)
    (i : Fin 768) (hi : i∈([460,545,555,557,561,569,573,585] : List (Fin 768))) :
    (LeafProgram.Incidence.staged s).stacks i=[] := by
  have hb : 340 ≤ i.val ∧ i.val < 680 ∧ i≠556 := by
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with hi|hi|hi|hi|hi|hi|hi|hi <;> subst i <;> decide
  have hc : i≠550 := by
    intro he; subst i; norm_num [Fin.ext_iff] at hi
  have hp : ∀ p∈LeafProgram.Incidence.pairs,i≠p.2 := by
    intro p hmem
    simp only [LeafProgram.Incidence.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hmem
    rcases hmem with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh <;> subst p
    all_goals intro he; subst i; norm_num [Fin.ext_iff] at hi
  rw [LeafProgram.Incidence.staged_frame s i hc hp]
  exact h.workerEmpty i hb.1 hb.2.1 hb.2.2

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Space for one actual ambient-coordinate table construction. Its unary
traversal has only n iterations, so its polynomial local time bounds every
source prefix. No outer signature or finite-difference iteration count occurs
in this estimate. The concrete literal and staging traces are instantiated by
the factor-table producer, rather than supplied to a final counting endpoint. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace

open SqrtLog

open BitProgram StructuredCalls FactorTableProgram

/-- Every actual external source master survives entry clearing, including
masters702/703 and710..728; no initial scratch-blank premise is used. -/
theorem initialized_base_external (a : OuterData) (i : Fin 768)
    (hi : (i.val < 340 ∧ i ≠ 62) ∨ 684 < i.val) :
    (initialized a).stacks (basePort i) = a.stacks (basePort i) := by
  have hn (j : Fin 768) (hj : 340 ≤ j.val ∧ j.val ≤ 684) : i ≠ j := by
    intro hij
    subst j
    rcases hi with hi | hi <;> omega
  have hbase : basePort i = i.castAdd 128 := by
    simp only [basePort, ite_eq_right (hn 640 (by decide)), ite_eq_right (hn 641 (by decide)),
      ite_eq_right (hn 642 (by decide)), ite_eq_right (hn 647 (by decide)),
      ite_eq_right (hn 650 (by decide)), ite_eq_right (hn 651 (by decide)),
      ite_eq_right (hn 670 (by decide)), ite_eq_right (hn 671 (by decide))]
  rw [initialized, SubexpSetupStorage.clearMany_stacks, ite_eq_right]
  simp only [entryPorts, List.mem_append]
  rintro (h | h)
  · obtain ⟨j, hj, he⟩ := List.mem_map.mp h
    have hji : j = i := basePort_injective he
    subst j
    have hw := (LeafProgram.Incidence.mem_workerPorts i).mp (List.mem_filter.mp hj).1
    rcases hi with hi | hi <;> omega
  · rw [hbase] at h
    have hnum : (i.val < 340 ∧ i.val ≠ 62) ∨ 684 < i.val := by
      rcases hi with ⟨hlt, hne⟩ | hgt
      · exact Or.inl ⟨hlt, fun hv => hne (Fin.ext hv)⟩
      · exact Or.inr hgt
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Fin.ext_iff,
      Fin.val_castAdd, Fin.coe_ofNat_eq_mod] at h
    norm_num at h
    omega

theorem initialized_frame (a : OuterData) (i : Fin 896) (hi : i ∉ writtenPorts) :
    (initialized a).stacks i = a.stacks i := by
  rw [initialized, SubexpSetupStorage.clearMany_stacks, ite_eq_right]
  intro he
  apply hi
  rcases List.mem_append.mp he with he | he
  · obtain ⟨j, hj, hji⟩ := List.mem_map.mp he
    exact List.mem_append_left _ (List.mem_map.mpr ⟨j, (List.mem_filter.mp hj).1, hji⟩)
  · exact List.mem_append_right _ he

private theorem original_staged_worker_frame (a : LeafProgram.Incidence.Data) (i : Fin 768)
    (hi : i ∉ LeafProgram.Incidence.workerPorts) :
    (LeafProgram.Incidence.staged a).stacks i = a.stacks i := by
  have h550 : i ≠ 550 := by
    intro he
    subst i
    exact hi ((LeafProgram.Incidence.mem_workerPorts 550).mpr (by decide))
  change Function.update (SubexpSetupStorage.copyManyState LeafProgram.Incidence.pairs a).stacks
    550 _ i = a.stacks i
  rw [Function.update_of_ne h550]
  apply SubexpSetupStorage.copyMany_frame
  intro p hp he
  apply hi
  rw [he]
  apply (LeafProgram.Incidence.mem_workerPorts p.2).mpr
  simp only [LeafProgram.Incidence.pairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> decide

/-- All caller masters outside the finite write set survive actual staging. -/
theorem staged_frame (a : OuterData) (i : Fin 896) (hi : i ∉ writtenPorts) :
    (staged a).stacks i = a.stacks i := by
  by_cases himage : ∃ j, basePort j = i
  · obtain ⟨j, rfl⟩ := himage
    have hj : j ∉ LeafProgram.Incidence.workerPorts := by
      intro hj
      exact hi (List.mem_append_left _ (List.mem_map.mpr ⟨j, hj, rfl⟩))
    rw [staged, embedState_stack _ _ _ _ basePort_injective,
      original_staged_worker_frame _ j hj]
    simpa only [projectState, Function.comp_apply] using initialized_frame a (basePort j) hi
  · change (embedState id basePort (initialized a) _).stacks i = a.stacks i
    rw [embedState_stack_frame _ _ _ _ i himage]
    exact initialized_frame a i hi

/-- The protected caller regions include every low node port except the
export62, all eight layout masters, and high ports outside the private bank. -/
theorem caller_port_not_written (i : Fin 896)
    (hi : (i.val < 340 ∧ i ≠ 62) ∨ i ∈ protectedPorts ∨
      (768 ≤ i.val ∧ i ≠ 881 ∧ i ≠ 882 ∧ (i.val < 885 ∨ 892 < i.val))) :
    i ∉ writtenPorts := by
  intro hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨j, hj, hji⟩ := List.mem_map.mp hm
    rcases hi with hi | hi | hi
    · have hw := (LeafProgram.Incidence.mem_workerPorts j).mp hj
      have hb : 340 ≤ (basePort j).val := by
        simp only [basePort]
        split_ifs <;> simp_all only [Fin.coe_ofNat_eq_mod, Fin.val_castAdd] <;> omega
      have hv := congrArg Fin.val hji
      omega
    · exact basePort_outside i (Or.inl hi) ⟨j, hji⟩
    · exact basePort_outside i (Or.inr ⟨hi.1, hi.2.2.2⟩) ⟨j, hji⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [protectedPorts, Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical source preparation for the specialized factor table. The old
master-word argument is generalized to the actually selected unary factor,
then transported through the fixed protected-port embedding. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram
open PerturbationAssembly LayoutProgram SubexpSetupStorage DensePolynomialProgram
open OAI.Algorithms.SubexponentialSAT.Subexp OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod


/-- Entry clearing reconstructs the ordinary caller cleanliness rather than
assuming the private worker survived a previous head reload. -/
theorem ScalarMasters.initialized {t d J R n : ℕ} {model : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d}
    (a : FactorTableProgram.OuterData)
    (h : ScalarMasters t model M cache J R theta
      (projectState id FactorTableProgram.basePort a) n) :
    CallerInput t model M cache J R theta
      (projectState id FactorTableProgram.basePort (FactorTableProgram.initialized a)) n := by
  have frame (i : Fin 768) (hi : (i.val < 340 ∧ i ≠ 62) ∨ 684 < i.val) :
      (projectState id FactorTableProgram.basePort (FactorTableProgram.initialized a)).stacks i =
        (projectState id FactorTableProgram.basePort a).stacks i :=
    FactorTableSpace.initialized_base_external a i hi
  refine ⟨h.widthPositive,h.zeroCanonical,h.zeroBits,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [frame 194 (by decide)]; exact h.modulus
  · rw [frame 202 (by decide)]; exact h.width
  · rw [frame 203 (by decide)]; exact h.zero
  · rw [frame 201 (by decide)]; exact h.table
  · rw [frame 204 (by decide)]; exact h.degree
  · rw [frame 145 (by decide)]; exact h.choicesLength
  · rw [frame 280 (by decide)]; exact h.zeroWord
  · rw [frame 207 (by decide)]; exact h.oneWord
  · rw [frame 78 (by decide)]; exact h.thetaWord
  · rw [frame 128 (by decide)]; exact h.ambientCount
  · rw [frame 243 (by decide)]; exact h.targetCount
  · rw [frame 138 (by decide)]; exact h.radius
  · rw [frame 703 (by decide)]; exact h.highLength
  · intro i hlo hhi hn
    exact FactorTableProgram.initialized_empty a i hlo hhi hn

variable {r Q d n J S f : ℕ} {p : SourceBank.Parameters r Q d}
    {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {a : SourceReady.Data} {theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d}

theorem sourceCallData_wordBound (s : FactorTableProgram.OuterStore) (B n L j : ℕ)
    (acc : List Bool) (regs : Fin 16 → Bool)
    (hbase : ∀ i, (s i).length ≤ B) (hj : j < n)
    (hacc : acc.length ≤ n * FactorTableProgram.literalRecordBound n L) :
    ∀ i, ((sourceCallData s j acc regs).stacks i).length ≤
      B + n + n * FactorTableProgram.literalRecordBound n L + 1 := by
  intro i
  by_cases h555 : i = 555
  · subst i
    simp only [sourceCallData, Function.update_self, Encoding.length_encodeNat]
    omega
  by_cases h569 : i = 569
  · subst i
    simpa [sourceCallData, FactorTableProgram.literalReady] using
      hacc.trans (by omega : n * FactorTableProgram.literalRecordBound n L ≤
        B + n + n * FactorTableProgram.literalRecordBound n L + 1)
  by_cases h573 : i = 573
  · subst i
    simp [sourceCallData, FactorTableProgram.literalReady]
    omega
  simp only [sourceCallData, FactorTableProgram.literalReady, Function.update_of_ne h555,
    Function.update_of_ne h569, Function.update_of_ne h573]
  exact (hbase i).trans (by omega)

theorem project_sourceCallData (s : FactorTableProgram.OuterStore) (j : ℕ) (acc : List Bool)
    (regs : Fin 16 → Bool) :
    projectState id FactorTableProgram.basePort (sourceCallData s j acc regs) =
      PerturbationAssembly.sourceCallData (FactorTableProgram.projectBase s) j acc regs := by
  apply SubexpScanPrimitives.state_ext
  · rfl
  · change FactorTableProgram.projectBase (Function.update
      (Function.update (Function.update s (FactorTableProgram.basePort 573) (List.replicate j true))
        (FactorTableProgram.basePort 569) acc) (FactorTableProgram.basePort 555) (Encoding.encodeNat j)) = _
    rw [FactorTableProgram.projectBase_update, FactorTableProgram.projectBase_update, FactorTableProgram.projectBase_update]
    rfl

theorem project_staged (a : FactorTableProgram.OuterData) :
    projectState id FactorTableProgram.basePort (FactorTableProgram.staged a) =
      Incidence.staged (projectState id FactorTableProgram.basePort (FactorTableProgram.initialized a)) := by
  exact projectState_embed id FactorTableProgram.basePort _ _ Function.injective_id FactorTableProgram.basePort_injective

/-- A physical source invariant before the loop supplies every relocated
source call, including its actual candidate index and polynomial table word. -/
theorem sourceInput_at_call {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (a : FactorTableProgram.OuterData) (v n f S j : ℕ) (acc : List Bool) (regs : Fin 16 → Bool)
    (h : SourceReady.Input p ps P (projectState id FactorTableProgram.basePort a) v n f S)
    (hsize : ∀ i, ((sourceCallData a.stacks j acc regs).stacks i).length ≤ S) :
    SourceReady.Input p ps P
      (projectState id FactorTableProgram.basePort (sourceCallData a.stacks j acc regs)) j n f S := by
  rw [project_sourceCallData]
  exact PerturbationAssembly.sourceInput_at_call p ps P
    (projectState id FactorTableProgram.basePort a) v n f S j acc regs h (fun i => by
      have hh := hsize (FactorTableProgram.basePort i)
      change ((projectState id FactorTableProgram.basePort (sourceCallData a.stacks j acc regs)).stacks i).length ≤ S at hh
      rw [project_sourceCallData] at hh
      exact hh)


/-- The physical source invariant is reused at every ambient ID, while its
size covers the actual cursor, encoded key and retained specialized table. -/
theorem native_literal_body {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f S B : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 p.t) d) (a : FactorTableProgram.OuterData)
    (h : StagedInput p.t p.model p.modulus p.cache J (p.R+1) theta
      (FactorTableProgram.projectBase a.stacks) n)
    (hsource : SourceReady.Input p ps P
      (projectState id FactorTableProgram.basePort a) 0 n f S)
    (hbase : ∀ i, (a.stacks i).length ≤ B)
    (hsize : B+n+n*FactorTableProgram.literalRecordBound n
      (specializedPayloadBound n u J (baseWidth 3 p.t) d)+1 ≤ S)
    (hn : n ≤ S) (hf : f ≤ S)
    (hplans : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
    (h545 : a.stacks 545 = []) (h555 : a.stacks 555 = []) (h557 : a.stacks 557 = [])
    (hm : (a.stacks 575).length = n) (hmask : (a.stacks 857).length = n)
    (htmp : a.stacks 881 = []) :
    FactorTableProgram.RelLiteralBody a.stacks FactorTableProgram.literalIteration
      (PayloadMeaning p ps P u J n f theta a.stacks)
      (specializedLiteralWork p u J n S (a.stacks 574).length) n
      (specializedPayloadBound n u J (baseWidth 3 p.t) d) := by
  constructor
  intro j hj acc hacc regs
  apply native_literal p ps P u J n f S j hu hJ theta a.stacks acc h
  · intro rs
    apply sourceInput_at_call p ps P a 0 n f S j acc rs hsource
    intro i
    exact (sourceCallData_wordBound a.stacks B n _ j acc rs hbase hj hacc i).trans hsize
  · exact hj
  · exact hn
  · exact hf
  · exact hplans
  · exact h545
  · exact h555
  · exact h557
  · exact hm
  · exact hmask
  · exact htmp

theorem Ready.staged_empty {r Q d u J n f B S : ℕ}
    {p : SourceBank.Parameters r Q d} {ps : List (ℕ × ℕ)}
    {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {theta : Coeff (baseWidth 3 p.t) d} {a : FactorTableProgram.OuterData}
    (h : Ready p ps P u J n f B S theta a) (i : Fin 768)
    (hi : i ∈ ([460,545,555,557,561,569,573,585] : List (Fin 768))) :
    (FactorTableProgram.staged a).stacks (FactorTableProgram.basePort i) = [] := by
  have hh := (h.scalar.initialized a).staged_empty i hi
  have he := congrArg (fun b : SourceReady.Data => b.stacks i) (project_staged a)
  exact he.trans hh

theorem Ready.staged_high {r Q d u J n f B S : ℕ}
    {p : SourceBank.Parameters r Q d} {ps : List (ℕ × ℕ)}
    {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {theta : Coeff (baseWidth 3 p.t) d} {a : FactorTableProgram.OuterData}
    (h : Ready p ps P u J n f B S theta a) :
    ((FactorTableProgram.staged a).stacks 575).length = n := by
  have hh := (h.scalar.initialized a).staged_high
  have he := congrArg (fun b : SourceReady.Data => (b.stacks 575).length) (project_staged a)
  exact he.trans hh

theorem staged_mask (a : FactorTableProgram.OuterData) :
    (FactorTableProgram.staged a).stacks 857 = a.stacks 857 :=
  FactorTableSpace.staged_frame a 857
    (FactorTableSpace.caller_port_not_written 857 (Or.inr (Or.inr (by decide))))

theorem staged_mask_scratch (a : FactorTableProgram.OuterData) :
    (FactorTableProgram.staged a).stacks 881 = [] := by
  change (embedState id FactorTableProgram.basePort (FactorTableProgram.initialized a) _).stacks 881 = []
  rw [embedState_stack_frame _ _ _ _ 881
    (FactorTableProgram.basePort_outside 881 (Or.inr (by decide)))]
  rw [FactorTableProgram.initialized,clearMany_stacks,ite_eq_left]
  exact List.mem_append_right _ (by simp)

theorem Ready.body {r Q d u J n f B S : ℕ}
    {p : SourceBank.Parameters r Q d} {ps : List (ℕ × ℕ)}
    {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {theta : Coeff (baseWidth 3 p.t) d} {a : FactorTableProgram.OuterData}
    (h : Ready p ps P u J n f B S theta a) :
    FactorTableProgram.RelLiteralBody (FactorTableProgram.staged a).stacks FactorTableProgram.literalIteration
      (PayloadMeaning p ps P u J n f theta (FactorTableProgram.staged a).stacks)
      (specializedLiteralWork p u J n S ((FactorTableProgram.staged a).stacks 574).length) n
      (specializedPayloadBound n u J (baseWidth 3 p.t) d) := by
  apply native_literal_body p ps P u J n f S (1029*B+99) h.positiveU h.positiveJ theta
    (FactorTableProgram.staged a) h.staged_common
  · exact source_of_masters p ps P a theta h.scalar h.masters h.selected h.incoming
      (by have := h.size; omega) h.arraySize h.countSize h.metadataSize h.incidenceSize
  · exact FactorTableSpace.staged_stack_bound a B h.incoming
  · exact h.size
  · exact h.ambientSize
  · exact h.factorSize
  · exact h.plansSize
  · exact h.staged_empty 545 (by simp)
  · exact h.staged_empty 555 (by simp)
  · exact h.staged_empty 557 (by simp)
  · exact h.staged_high
  · rw [staged_mask]; exact h.mask
  · exact staged_mask_scratch a

/-- The table entry contract discharges every literal execution. The output
is the exact attained native family, with scalar Goodempty dictionaries,
full original-variable lookup format, time, and all-prefix source space on
one and the same fixed finite program run. -/
theorem command_native_resources_oai {r Q d u J n f B S : ℕ}
    {p : SourceBank.Parameters r Q d} {ps : List (ℕ × ℕ)}
    {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {theta : Coeff (baseWidth 3 p.t) d} {a : FactorTableProgram.OuterData}
    (h : Ready p ps P u J n f B S theta a) :
    let K := specializedLiteralWork p u J n S ((FactorTableProgram.staged a).stacks 574).length
    let L := specializedPayloadBound n u J (baseWidth 3 p.t) d
    ∃ (incidence : Fin n → List (MomentsProgram.Product.Entry n (baseWidth 3 p.t) d))
      (steps : ℕ) (e : FactorTableProgram.OuterData),
      (∀ v, TruncatedRingProgram.Good ∅ u J (incidence v)) ∧
      (∀ v, (MomentsProgram.Product.bytes (incidence v)).length ≤ L) ∧
      (∀ v, PayloadMeaning p ps P u J n f theta (FactorTableProgram.staged a).stacks
        v.val (MomentsProgram.Product.bytes (incidence v))) ∧
      steps ≤ FactorTableSpace.commandBudget B n K L ∧
      Trace FactorTableProgram.program steps (a.withPC (some FactorTableProgram.program.entry)) (e.withPC none) ∧
      e.stacks 62 = Squarefree.Program.lookupRecords
        (HashCircuitProgram.incidenceEntries (fun (_ : Unit) v => MomentsProgram.Product.bytes (incidence v)) ()) ∧
      (∀ i, i ∉ FactorTableSpace.writtenPorts → e.stacks i = a.stacks i) ∧
      (∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → e.stacks i = []) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace FactorTableProgram.program prefixSteps (a.withPC (some FactorTableProgram.program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 896*B+FactorTableSpace.commandBudget B n K L := by
  classical
  dsimp only
  obtain ⟨payload,steps,e,hpayload,hsteps,htrace,houtput,hframe,hclean,hprefix⟩ :=
    FactorTableSpace.command_resources a B n _ _ h.incoming h.staged_common.ambientCount
      (h.staged_empty 460 (by simp)) (h.staged_empty 573 (by simp))
      (h.staged_empty 569 (by simp)) (h.staged_empty 561 (by simp))
      (h.staged_empty 585 (by simp)) _ h.body
  have hw (v : Fin n) := (hpayload v.val v.isLt).2.good
  choose incidence hgood hbytes using hw
  refine ⟨incidence,steps,e,hgood,?_,?_,hsteps,htrace,?_,hframe,hclean,hprefix⟩
  · intro v
    rw [← hbytes v]
    exact (hpayload v.val v.isLt).1
  · intro v
    rw [← hbytes v]
    exact (hpayload v.val v.isLt).2
  · rw [houtput,FactorTableProgram.tableResult_incidence]
    have hf : (fun (_ : Unit) (v : Fin n) => payload v.val) =
        (fun (_ : Unit) (v : Fin n) => MomentsProgram.Product.bytes (incidence v)) := by
      funext x v
      exact hbytes v
    rw [hf]


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.command_native_resources_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.command_native_resources_oai
