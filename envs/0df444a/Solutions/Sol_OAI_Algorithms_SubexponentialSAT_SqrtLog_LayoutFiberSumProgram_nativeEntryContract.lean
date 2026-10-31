-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.nativeEntryContract
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:18:35.625292+00:00
-- url     : https://prove2.me/submissions/c342a94d-9434-4e1c-af51-58c6a0d6ab7d

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S174
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutFiberSumProgram_command_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutFiberSumProgram_entryAt

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem mem_fiberIndices_bounds (query index : ℕ) (ps : List (ℕ × ℕ))
    {i : ℕ} (hi : i ∈ fiberIndices query index ps) :
    index ≤ i ∧ i < index+ps.length := by
  induction ps generalizing index with
  | nil => simp [fiberIndices] at hi
  | cons p ps ih =>
      by_cases h : p.1=query
      · simp only [fiberIndices,h,ite_true, if_true,List.mem_cons] at hi
        rcases hi with rfl | hi
        · simp
        · have hh := ih (index+1) hi
          simp only [List.length_cons]
          omega
      · simp only [fiberIndices,h,ite_false] at hi
        have hh := ih (index+1) hi
        simp only [List.length_cons]
        omega

theorem mem_fiberIndices_lt (query : ℕ) (ps : List (ℕ × ℕ))
    {i : ℕ} (hi : i ∈ fiberIndices query 0 ps) : i < ps.length := by
  have hh := mem_fiberIndices_bounds query 0 ps hi
  omega

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramInterface
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Adapter from the native owner-fiber loop to the matrix builder's fixed-bank
entry contract.  The incidence callback is still an actual command/Eval premise;
there is no table of precomputed entry values. -/
namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

theorem matrix_data (base : Fin 288 → List Bool) (j : ℕ)
    (hb : Ready (matrixBase base j)) (regs : Fin 16 → Bool)
    (col : List Bool) (result : WordPair) :
    data (matrixBase base j) regs [] col ([],[]) result =
      LayoutMatrixProgram.entryState base regs (unary j) col result.1 result.2 := by
  have h212 := hb.2 212 (by decide) (by decide)
  have h213 := hb.2 213 (by decide) (by decide)
  have h214 := hb.2 214 (by decide) (by decide)
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    by_cases h : i=212
    · subst i; simpa [matrixBase,LayoutMatrixProgram.entryState,data,bank] using h212.symm
    by_cases h' : i=213
    · subst i; simpa [matrixBase,LayoutMatrixProgram.entryState,data,bank] using h213.symm
    by_cases h'' : i=214
    · subst i; simpa [matrixBase,LayoutMatrixProgram.entryState,data,bank] using h214.symm
    by_cases hr : i=252
    · subst i; simp [matrixBase,LayoutMatrixProgram.entryState,bank]
    by_cases hc : i=253
    · subst i; simp [bank]
    by_cases hp : i=254
    · subst i; simp [bank]
    by_cases hn : i=255
    · subst i; simp [bank]
    simp [matrixBase,LayoutMatrixProgram.entryState,bank,h,h',h'',hr,hc,hp,hn]

/-- Native original-column contract. The time and length inequalities are the
only uniform resource envelopes added to the pointwise owner-fiber theorem.
The caller may retain both the exact signed sum and the literal mass bound in
its desired relation. -/
theorem entryContract (entry : Code) (base : Fin 288 → List Bool)
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → WordPair → Prop)
    (ps : List (ℕ × ℕ)) (value : ℕ → ℕ → ℤ)
    (Ti Bi Mi Tout Bout : ℕ)
    (hready : ∀ j v, Valid j v → Ready (matrixBase base j))
    (hsource : base (LayoutMatrixProgram.bankPort 201)=LayoutOwnerFiberProgram.stream ps)
    (hentry : ∀ j v, Valid j v → ∀ i∈LayoutOwnerFiberProgram.fiberIndices v 0 ps,
      EntryAt entry (parked (matrixBase base j) v) (value j) Ti Bi Mi i)
    (htime : ∀ j v, Valid j v → budget Ti Bi ps.length v ps ≤ Tout)
    (hlength : ∀ j v, Valid j v →
      (LayoutOwnerFiberProgram.fiberIndices v 0 ps).length*(Bi+2) ≤ Bout)
    (hrel : ∀ j v, Valid j v → ∀ result : WordPair,
      pairValue result=((LayoutOwnerFiberProgram.fiberIndices v 0 ps).map (value j)).sum →
      pairTotal result.1 result.2 ≤ (LayoutOwnerFiberProgram.fiberIndices v 0 ps).length*Mi →
      Rel j v result) :
    LayoutMatrixProgram.EntryContract (command entry) base Valid Rel Tout Bout := by
  intro regs j v hv
  have hb := hready j v hv
  have hs : (matrixBase base j).stacks 201=LayoutOwnerFiberProgram.stream ps := by
    simpa [matrixBase,LayoutMatrixProgram.entryState] using hsource
  obtain ⟨n,hn,rf,result,he,heq,hlen,hmass⟩ := command_eval entry (matrixBase base j) hb
    v ps hs (value j) Ti Bi Mi ps.length (hentry j v hv)
    (by
      intro i hi
      exact Nat.le_of_lt (LayoutOwnerFiberProgram.mem_fiberIndices_lt v ps hi)) regs
  rw [matrix_data base j hb regs, matrix_data base j hb rf] at he
  refine ⟨n,le_trans (Nat.le_of_lt hn) (htime j v hv),rf,result,he,hrel j v hv result heq hmass,?_⟩
  exact le_trans hlen (hlength j v hv)

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramContract
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The closed owner-fiber command realizes the literal matrix relation used
by the produced-head/rank join. Only actual cache data and numerical envelopes
remain as hypotheses; no per-entry machine contract is assumed. -/
namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking RowSelectionProgram

theorem matrix_cached {r Q : ℕ} (base : Fin 288 → List Bool)
    (c : LayoutProgram.Numerator.Saved) (t : Fin Q)
    (hc : LayoutProgram.EntryBank.CacheWords (r:=r) (matrixBase base 0) c t)
    (j v : ℕ) :
    LayoutProgram.EntryBank.CacheWords (r:=r) (parked (matrixBase base j) v) c t := by
  constructor
  · simpa [parked,matrixBase,LayoutMatrixProgram.entryState] using hc.hp
  · simpa [parked,matrixBase,LayoutMatrixProgram.entryState] using hc.hn
  · simpa [parked,matrixBase,LayoutMatrixProgram.entryState] using hc.hw
  · simpa [parked,matrixBase,LayoutMatrixProgram.entryState] using hc.hpos
  · exact hc.hneg
  · simpa [parked,matrixBase,LayoutMatrixProgram.entryState] using hc.hr
  · simpa [parked,matrixBase,LayoutMatrixProgram.entryState] using hc.ha
  · simpa [parked,matrixBase,LayoutMatrixProgram.entryState] using hc.colors
  · simpa [parked,matrixBase,LayoutMatrixProgram.entryState] using hc.nodes
  · simpa [parked,matrixBase,LayoutMatrixProgram.entryState] using hc.node
  · simpa [parked,matrixBase,LayoutMatrixProgram.entryState] using hc.typeWidth

theorem matrix_low_frame (base : Fin 288 → List Bool) (j v : ℕ)
    (i : Fin 256) (hi : i.val < 212) :
    (parked (matrixBase base j) v).stacks i=base (LayoutMatrixProgram.bankPort i) := by
  have h216 : i≠216 := by intro h; have hh : i.val=216 := congrArg Fin.val h; omega
  have h252 : i≠252 := by intro h; have hh : i.val=252 := congrArg Fin.val h; omega
  have h253 : i≠253 := by intro h; have hh : i.val=253 := congrArg Fin.val h; omega
  have h254 : i≠254 := by intro h; have hh : i.val=254 := congrArg Fin.val h; omega
  have h255 : i≠255 := by intro h; have hh : i.val=255 := congrArg Fin.val h; omega
  simp [parked,matrixBase,LayoutMatrixProgram.entryState,h216,h252,h253,h254,h255]

theorem nativeEntryContract_oai {r Q D : ℕ}
    (P : PackingData (Fin D) (UniversalType r Q 1))
    (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (aWord : List Bool) (R : ℕ) (t : Fin Q)
    (base : Fin 288 → List Bool) (ps : List (ℕ × ℕ))
    (Valid : ℕ → ℕ → Prop) (S U H Tout Bout : ℕ)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H aWord.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hpos : BinaryArithmetic.toNat power.1=2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : aWord.length ≤ Q) (hQ : 1 ≤ Q)
    (hc : LayoutProgram.EntryBank.CacheWords (r:=r) (matrixBase base 0)
      (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R aWord) t)
    (hready : ∀ j v, Valid j v → Ready (matrixBase base j))
    (hmeta : base (LayoutMatrixProgram.bankPort 200)=
      SelectorProgram.rawRecords (LayoutProgram.EntryBank.metadataRecords P))
    (hsource : base (LayoutMatrixProgram.bankPort 201)=LayoutOwnerFiberProgram.stream ps)
    (hsize : ∀ i : Fin 256, i.val < 212 → (base (LayoutMatrixProgram.bankPort i)).length ≤ S)
    (hps : ps.length=D) (hDS : D ≤ S)
    (hvalid : ∀ j v, Valid j v → j < D)
    (hmetadata : ∀ v, LayoutProgram.EntryBank.MetadataBound
      (PackingMetadata.value P CollisionProgram.encodeType v) S)
    (hlookup : ∀ row col : Fin D, LayoutProgram.EntryBank.lookupBudget P row col ≤ U)
    (htime : ∀ j v, Valid j v →
      budget (nativeTime r Q R width power aWord S U) (nativeLength R width power)
        ps.length v ps ≤ Tout)
    (hlength : ∀ j v, Valid j v →
      (LayoutOwnerFiberProgram.fiberIndices v 0 ps).length*(nativeLength R width power+2) ≤ Bout)
    (hmass : ∀ j v, Valid j v →
      (LayoutOwnerFiberProgram.fiberIndices v 0 ps).length*LayoutProgram.constraintMassBound Q R ≤ H) :
    LayoutMatrixProgram.EntryContract (command LayoutProgram.EntryBank.command) base Valid
      (BucketProgram.ProducedRank.FiberRel ps
        (BucketProgram.ProducedRank.entryNat P aWord.length R t) H) Tout Bout := by
  apply entryContract LayoutProgram.EntryBank.command base Valid _ ps
    (BucketProgram.ProducedRank.entryNat P aWord.length R t)
    (nativeTime r Q R width power aWord S U) (nativeLength R width power)
    (LayoutProgram.constraintMassBound Q R) Tout Bout hready hsource
    ?_ htime hlength ?_
  · intro j v hv i hi
    have hj : j < D := hvalid j v hv
    have hiD : i < D := by simpa only [hps] using LayoutOwnerFiberProgram.mem_fiberIndices_lt v ps hi
    let row : Fin D := ⟨j,hj⟩
    let col : Fin D := ⟨i,hiD⟩
    let b := parked (matrixBase base j) v
    have hb := hready j v hv
    have hwork : ∀ x : Fin 256, x.val < 200 → b.stacks x=[] := by
      intro x hx
      have hn : x≠216 := by intro h; have he : x.val=216 := congrArg Fin.val h; omega
      simpa [b,parked,Function.update_of_ne hn] using hb.1 x hx
    have he := entryAt P Hwords width power aWord R t row col b S U
      hlen hwords hvalues hp hpt hpos hwidth hAQ hQ
      (matrix_cached base _ t hc j v) hwork
      (by simpa [b,parked,matrixBase,LayoutMatrixProgram.entryState] using hmeta)
      (by simp [b,parked,matrixBase,LayoutMatrixProgram.entryState,row,unary])
      (by
        intro x hx
        rw [matrix_low_frame base j v x hx]
        exact hsize x hx)
      (by dsimp [row]; omega) (by dsimp [col]; omega) hmetadata (hlookup row col)
    have heq : incidenceValue P aWord.length R t row=
        BucketProgram.ProducedRank.entryNat P aWord.length R t j := by
      funext z
      simp [incidenceValue,BucketProgram.ProducedRank.entryNat,row,hj]
    rw [heq] at he
    exact he
  · intro j v hv result hvalue htotal
    exact ⟨hvalue,htotal.trans (hmass j v hv)⟩

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.nativeEntryContract_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.nativeEntryContract_oai
