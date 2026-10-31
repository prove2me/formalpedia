-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.command_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:18:36.621205+00:00
-- url     : https://prove2.me/submissions/e3eb2ca8-e14c-474d-86bf-75a351d61f68

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S174
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_EntryBank_covered_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_EntryBank_covered_uncovered_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_EntryBank_uncovered_cleanup_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_EntryBankFrame_lookup_lifted

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact lookup semantics for the storage-ordered packing metadata table.
The physical extraction proof identifies its emitted records with this table. -/

namespace SubexponentialSAT.Subexp.PackingMetadata

open ConstructivePacking
open GlobalBasisMetadata (Metadata)

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

theorem lookup_eq (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) (hvertex : Function.Injective encodeVertex) (v : V) :
    (records P encodeVertex encodeType).lookup (encodeVertex v) =
      some (value P encodeType v).encode :=
  lookup_graph_encoded _ _ _ hvertex v
    (by simpa using PackingReorder.mem_storageVertices P v)

end SubexponentialSAT.Subexp.PackingMetadata

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete incidence-entry program. Its read-only cache bank is200..211,
its input indices252/253, and the returned signed pair254/255. Ports212..251
belong to the caller and are outside every local subroutine map. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem lookupRegs_inj : Function.Injective lookupRegs := Fin.castAdd_injective _ _
theorem lookupPorts_inj : Function.Injective lookupPorts := by decide

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem metadataStacks_frame (a : Data) (mr mc : GlobalBasisMetadata.Metadata)
    (j : Fin 256) (hj : j.val < 64 ∨ 70 ≤ j.val) : metadataStacks a mr mc j=a.stacks j := by
  have h64 : j≠64 := by intro h; have hv := congrArg Fin.val h; simp at hv; omega
  have h65 : j≠65 := by intro h; have hv := congrArg Fin.val h; simp at hv; omega
  have h66 : j≠66 := by intro h; have hv := congrArg Fin.val h; simp at hv; omega
  have h67 : j≠67 := by intro h; have hv := congrArg Fin.val h; simp at hv; omega
  have h68 : j≠68 := by intro h; have hv := congrArg Fin.val h; simp at hv; omega
  have h69 : j≠69 := by intro h; have hv := congrArg Fin.val h; simp at hv; omega
  simp [metadataStacks,h64,h65,h66,h67,h68,h69]

theorem lookup_eval (a : Data) (records : List (List Bool × List Bool))
    (row col : List Bool) (mr mc : GlobalBasisMetadata.Metadata)
    (hr : records.lookup row=some mr.encode) (hc : records.lookup col=some mc.encode)
    (hm : a.stacks 200=SelectorProgram.rawRecords records)
    (hrow : a.stacks 252=row) (hcol : a.stacks 253=col)
    (hready : ∀ j : Fin 256, 64 ≤ j.val → j.val ≤ 76 → a.stacks j=[]) :
    ∃ n ≤ 400*(GlobalBasisMetadata.volume records row)^2+
        400*(GlobalBasisMetadata.volume records col)^2+1,
      ∃ e : Data, Eval lookup n a e ∧ e.stacks=metadataStacks a mr mc ∧
        e.regs 4=mr.coveredFlag ∧ e.regs 5=mc.coveredFlag := by
  have ha : projectState lookupRegs lookupPorts a=
      LookupPair.state (a.regs ∘ lookupRegs) (SelectorProgram.rawRecords records)
        row col [] [] [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [lookupPorts,hm,hrow,hcol,hready]
  obtain ⟨n,hn,e,he,hp,hf,_⟩ := EntryBankFrame.lookup_lifted lookupRegs lookupPorts
    lookupRegs_inj lookupPorts_inj a records row col mr mc hr hc ha
  refine ⟨n,hn,e,he,?_,?_,?_⟩
  · funext j
    by_cases hj : ∃ i, lookupPorts i=j
    · obtain ⟨i,rfl⟩ := hj
      have h := congrArg (fun d : LookupPair.Data => d.stacks i) hp
      fin_cases i <;>
        simpa [projectState,lookupPorts,LookupPair.state,metadataStacks,hm,hrow,hcol,hready] using h
    · rw [hf j hj]
      have h64 : j≠64 := by intro h; apply hj; exact ⟨3,h.symm⟩
      have h65 : j≠65 := by intro h; apply hj; exact ⟨4,h.symm⟩
      have h66 : j≠66 := by intro h; apply hj; exact ⟨5,h.symm⟩
      have h67 : j≠67 := by intro h; apply hj; exact ⟨6,h.symm⟩
      have h68 : j≠68 := by intro h; apply hj; exact ⟨7,h.symm⟩
      have h69 : j≠69 := by intro h; apply hj; exact ⟨8,h.symm⟩
      simp [metadataStacks,h64,h65,h66,h67,h68,h69]
  · exact congrArg (fun d : LookupPair.Data => d.regs 4) hp
  · exact congrArg (fun d : LookupPair.Data => d.regs 5) hp

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankFrameUncovered
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem metadataFieldsLength_eq (a : Data) : metadataFieldsLength a=
    (a.stacks 64).length+(a.stacks 65).length+(a.stacks 66).length+
    (a.stacks 67).length+(a.stacks 68).length+(a.stacks 69).length := by
  simp [metadataFieldsLength,metadataIndices]
  omega

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankCache
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q : ℕ}

theorem CacheWords.frame {a b : Data} {c : Numerator.Saved} {t : Fin Q}
    (h : CacheWords (r:=r) a c t)
    (hf : ∀ j : Fin 256, 200 ≤ j.val → b.stacks j=a.stacks j) : CacheWords (r:=r) b c t := by
  constructor
  · exact (hf _ (by decide)).trans h.hp
  · exact (hf _ (by decide)).trans h.hn
  · exact (hf _ (by decide)).trans h.hw
  · exact (hf _ (by decide)).trans h.hpos
  · exact h.hneg
  · exact (hf _ (by decide)).trans h.hr
  · exact (hf _ (by decide)).trans h.ha
  · exact (hf _ (by decide)).trans h.colors
  · exact (hf _ (by decide)).trans h.nodes
  · exact (hf _ (by decide)).trans h.node
  · exact (hf _ (by decide)).trans h.typeWidth

theorem metadata_ready {a b : Data} (mr mc : GlobalBasisMetadata.Metadata)
    (ha : BaseReady a) (hb : b.stacks=metadataStacks a mr mc) : MetadataReady b := by
  intro j hj hk
  rw [hb,metadataStacks_frame a mr mc j hk]
  exact ha.1 j hj

theorem metadata_high {a b : Data} (mr mc : GlobalBasisMetadata.Metadata)
    (hb : b.stacks=metadataStacks a mr mc) :
    ∀ j : Fin 256,200 ≤ j.val → b.stacks j=a.stacks j := by
  intro j hj
  rw [hb,metadataStacks_frame a mr mc j (Or.inr (by omega))]

theorem metadata_length {a b : Data} (mr mc : GlobalBasisMetadata.Metadata) (S : ℕ)
    (hb : b.stacks=metadataStacks a mr mc)
    (ha : ∀ j : Fin 256,j.val < 212 → (a.stacks j).length ≤ S)
    (hr : MetadataBound mr S) (hc : MetadataBound mc S) :
    ∀ j : Fin 256,j.val < 212 → (b.stacks j).length ≤ S := by
  intro j hj
  rw [hb]
  simp only [metadataStacks,Function.update_apply]
  split_ifs <;> first
    | exact hr.1
    | exact hr.2.1
    | exact hr.2.2
    | exact hc.1
    | exact hc.2.1
    | exact hc.2.2
    | exact ha j hj

theorem metadata_fields_le {a : Data} {S : ℕ}
    (h : ∀ j : Fin 256,j.val < 212 → (a.stacks j).length ≤ S) :
    metadataFieldsLength a ≤ 6*S := by
  have h1 := h 64 (by decide)
  have h2 := h 65 (by decide)
  have h3 := h 66 (by decide)
  have h4 := h 67 (by decide)
  have h5 := h 68 (by decide)
  have h6 := h 69 (by decide)
  rw [metadataFieldsLength_eq]
  omega

theorem finish_frame {a b : Data} (regs : Fin 16 → Bool) (result : RowSelectionProgram.WordPair)
    (hf : ∀ j : Fin 256,200 ≤ j.val → b.stacks j=a.stacks j) :
    finish b regs result=finish a regs result := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext j
  by_cases hj : j.val < 200
  · simp [hj]
  · simp only [ite_eq_right hj]
    rw [hf j (by omega)]

/-- Reattach the row-covered flag after either concrete branch has run. -/
theorem selected_attach {a z : Data} {n : ℕ} {coveredFlag : Bool}
    (hf : a.regs 4=coveredFlag)
    (he : Eval (.seq (if coveredFlag then covered else uncovered) cleanup) n a z) :
    Eval (.seq (.ite 4 covered uncovered) cleanup) (n+1) a z := by
  cases coveredFlag
  · simp only [Bool.false_eq_true,ite_false] at he
    cases he with
    | seq h hclean =>
      simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
        (Eval.ite_false (yes:=covered) hf h).seq hclean
  · simp only [ite_true, if_true] at he
    cases he with
    | seq h hclean =>
      simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
        (Eval.ite_true (no:=uncovered) hf h).seq hclean

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native entry of the all-incidence integer matrix. The actual packing
metadata is read twice; no precomputed integer matrix is supplied. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking RowSelectionProgram

variable {r Q D : ℕ}

private theorem unary_inj {x y : Fin D} :
    List.replicate x.val true=List.replicate y.val true ↔ x=y := by
  constructor
  · intro h; apply Fin.ext; simpa using congrArg List.length h
  · rintro rfl; rfl

private theorem constraintMassBound_one (Q R : ℕ) : 1 ≤ constraintMassBound Q R := by
  have hh : 0 < 2^(R-1) := by positivity
  unfold constraintMassBound
  omega

/-- The callback consumed by the owner-fiber loop. `K` and `L` are numerical
upper bounds on the closed universal program, not program-service premises. -/
theorem command_eval_oai (P : PackingData (Fin D) (UniversalType r Q 1))
    (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (aWord : List Bool) (R : ℕ) (t : Fin Q) (row col : Fin D)
    (a : Data) (S K L : ℕ)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H aWord.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hpos : BinaryArithmetic.toNat power.1=2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : aWord.length ≤ Q) (hQ : 1 ≤ Q)
    (hc : CacheWords (r:=r) a (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R aWord) t)
    (hready : BaseReady a)
    (hmeta : a.stacks 200=SelectorProgram.rawRecords (metadataRecords P))
    (hrow : a.stacks 252=List.replicate row.val true)
    (hcol : a.stacks 253=List.replicate col.val true)
    (hsize : ∀ j : Fin 256,j.val < 212 → (a.stacks j).length ≤ S)
    (hrs : row.val ≤ S) (hcs : col.val ≤ S)
    (hmetadata : ∀ v, MetadataBound (PackingMetadata.value P CollisionProgram.encodeType v) S)
    (hK : ∀ u y : UniversalType r Q 1, IntegerEntry.budget aWord.length R width.length (pairLength power) power.1.length t u y ≤ K)
    (hL : ∀ u y : UniversalType r Q 1, IntegerEntry.lengthBound R width.length (pairLength power) u y+power.1.length+1 ≤ L)
    (hL1 : 1 ≤ L) :
    ∃ n ≤ lookupBudget P row col+K+550*S+450*L+1200, ∃ rf result,
      Eval command n a (finish a rf result) ∧
      pairValue result=localEntry P aWord.length R t row col ∧
      LayoutProgramScalar.wordTotal result ≤ constraintMassBound Q R ∧ pairLength result ≤ L := by
  let mr := PackingMetadata.value P CollisionProgram.encodeType row
  let mc := PackingMetadata.value P CollisionProgram.encodeType col
  have hkey : Function.Injective (fun v : Fin D => List.replicate v.val true) := by
    intro x y h; exact unary_inj.mp h
  obtain ⟨nl,hnl,b,hl,hbs,h4,h5⟩ := lookup_eval a (metadataRecords P)
    (List.replicate row.val true) (List.replicate col.val true) mr mc
    (PackingMetadata.lookup_eq P _ _ hkey row)
    (PackingMetadata.lookup_eq P _ _ hkey col) hmeta hrow hcol
    (fun j hj hk => hready.1 j (by omega))
  change nl ≤ lookupBudget P row col at hnl
  have hbready : MetadataReady b := metadata_ready mr mc hready hbs
  have hbhigh := metadata_high mr mc hbs
  have hb254 : b.stacks 254=[] := (hbhigh _ (by decide)).trans hready.2.1
  have hb255 : b.stacks 255=[] := (hbhigh _ (by decide)).trans hready.2.2
  have hbsize := metadata_length mr mc S hbs hsize (hmetadata row) (hmetadata col)
  have hbfields := metadata_fields_le hbsize
  have hbcache := hc.frame hbhigh
  have hbrow : b.stacks 252=List.replicate row.val true := (hbhigh _ (by decide)).trans hrow
  have hbcol : b.stacks 253=List.replicate col.val true := (hbhigh _ (by decide)).trans hcol
  cases hv : P.lookup row with
  | none =>
    have hb4 : b.regs 4=false := by
      simpa [mr,PackingMetadata.value,hv,GlobalBasisMetadata.Metadata.coveredFlag] using h4
    obtain ⟨nu,hnu,z,hu,hzs⟩ := uncovered_cleanup_eval b hbready hb254
    let result : WordPair := (if row=col then [true] else [],[])
    have hkeys : b.stacks 252=b.stacks 253 ↔ row=col := by rw [hbrow,hbcol]; exact unary_inj
    have hz : z=finish b z.regs result := by
      apply congrArg₂ StructuredProgram.State.mk rfl
      funext j
      rw [hzs j]
      simp only [result]
      by_cases h255 : j=255
      · subst j; simp [hb255]
      · simp [h255,hkeys]
    rw [hz,finish_frame z.regs result hbhigh] at hu
    have hs := selected_attach (coveredFlag:=false) hb4 hu
    have ht := hl.seq hs
    refine ⟨nl+(nu+1),?_,z.regs,result,ht,?_,?_,?_⟩
    · simp only [hbrow,hbcol,List.length_replicate] at hnu
      omega
    · by_cases heq : row=col
      · subst col
        simp [result,pairValue,RowSelectionProgram.signedValue,localEntry,hv]
      · simp [result,pairValue,RowSelectionProgram.signedValue,localEntry,hv,heq,eq_comm]
    · have hone := constraintMassBound_one Q R
      by_cases heq : row=col <;> simp [result,heq,LayoutProgramScalar.wordTotal,pairTotal] ; omega
    · by_cases heq : row=col <;> simp [result,heq,pairLength] ; omega
  | some z =>
    rcases z with ⟨j,u⟩
    have hb4 : b.regs 4=true := by
      simpa [mr,PackingMetadata.value,hv,GlobalBasisMetadata.Metadata.coveredFlag] using h4
    cases hw : P.lookup col with
    | none =>
      have hb5 : b.regs 5=false := by
        simpa [mc,PackingMetadata.value,hw,GlobalBasisMetadata.Metadata.coveredFlag] using h5
      obtain ⟨nu,hnu,rf,hu⟩ := covered_uncovered_eval b hbready hb254 hb255 hb5
      rw [finish_frame rf ([],[]) hbhigh] at hu
      have hs := selected_attach (coveredFlag:=true) hb4 hu
      refine ⟨nl+(nu+1),by omega,rf,([],[]),hl.seq hs,?_,?_,?_⟩
      · simp [pairValue,RowSelectionProgram.signedValue,localEntry,hv,hw]
      · simp [LayoutProgramScalar.wordTotal,pairTotal]
      · simp [pairLength]
    | some z =>
      rcases z with ⟨k,y⟩
      have hb5 : b.regs 5=true := by
        simpa [mc,PackingMetadata.value,hw,GlobalBasisMetadata.Metadata.coveredFlag] using h5
      have hbu : b.stacks 65=CollisionProgram.encodeType u := by
        simp [hbs,metadataStacks,mr,PackingMetadata.value,hv,GlobalBasisMetadata.Metadata.typeCode]
      have hby : b.stacks 68=CollisionProgram.encodeType y := by
        simp [hbs,metadataStacks,mc,PackingMetadata.value,hw,GlobalBasisMetadata.Metadata.typeCode]
      have hbblock : b.stacks 64=b.stacks 67 ↔ j=k := by
        simp only [hbs,metadataStacks,Function.update_apply]
        simp [mr,mc,PackingMetadata.value,hv,hw,GlobalBasisMetadata.Metadata.block,
          PackingMetadata.unary,Fin.val_inj]
      obtain ⟨nu,hnu,rf,result,hu,hvresult,hmresult,hlresult⟩ := covered_eval Hwords width power aWord R t u y
        b S K L hlen hwords hvalues hp hpt hpos hwidth hAQ hQ hbcache hbready hb254 hb255
        hbu hby hb5 hbsize (hK u y) (hL u y)
      rw [finish_frame rf result hbhigh] at hu
      have hs := selected_attach (coveredFlag:=true) hb4 hu
      refine ⟨nl+(nu+1),by omega,rf,result,hl.seq hs,?_,hmresult,hlresult⟩
      rw [hvresult]
      by_cases heq : j=k <;>
        by_cases ha : MatrixExtendedEntryProgram.anchorValid (0:Fin 1) t u y <;>
        simp [localEntry,hv,hw,IntegerEntry.value,heq,ha,hbblock]

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.command_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.command_eval_oai
