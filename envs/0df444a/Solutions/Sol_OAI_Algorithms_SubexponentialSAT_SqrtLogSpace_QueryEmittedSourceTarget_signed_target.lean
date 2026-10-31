-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget.signed_target
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:34:48.608927+00:00
-- url     : https://prove2.me/submissions/67c51164-1999-4c23-9103-b87f0ba44888

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S044
import Definitions.Def_OAIQ081S190
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_NodeConcrete_fixedSourceRow_baseline_eq
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSourceLocality_colored_source_admissible
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryJetSemantics_colored_residual_target_dense_shift
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryTupleReadoutSemantics_grouped_dense_query_emitted

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSignatureLocality
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact full-integer head labels and fixed-high cancellation, extracted
unchanged from HeadSourceLocality. All raw rows and original coordinate IDs
are retained; source-product locality remains in the importing module. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog

/-- Equal fixed-high bits cancel; the remaining exact signature is the full
integer signature on the actual free coordinates of this head. -/
theorem signature_eq_of_free {n r D : ℕ} (H : Finset (Fin n))
    (head : Fin n → Fin r) (g : Fin r) (C : Fin D → Fin n → ℤ)
    (x y : Fin n → Bool) (hhigh : ∀ v ∈ H,x v=y v)
    (hfree : LayoutSignatureBound.boolSignature
        (fun j (v : Moments.Head (fun v : {v : Fin n // v ∉ H} => head v.val) g) => C j v.val.val)
        (fun v => x v.val.val) =
      LayoutSignatureBound.boolSignature
        (fun j (v : Moments.Head (fun v : {v : Fin n // v ∉ H} => head v.val) g) => C j v.val.val)
        (fun v => y v.val.val)) :
    LayoutSignatureBound.boolSignature (fun j (v : Moments.Head head g) => C j v.val)
      (fun v => x v.val) =
    LayoutSignatureBound.boolSignature (fun j (v : Moments.Head head g) => C j v.val)
      (fun v => y v.val) := by
  classical
  funext j
  let e := freeHeadInclusion H head g
  have he :
      (∑ v : Moments.Head head g, C j v.val *
        ((if x v.val then 1 else 0 : ℤ)-(if y v.val then 1 else 0))) =
      ∑ v : Moments.Head (fun v : {v : Fin n // v ∉ H} => head v.val) g,
        C j v.val.val * ((if x v.val.val then 1 else 0 : ℤ)-
          (if y v.val.val then 1 else 0)) := by
    calc
      _ = ∑ v ∈ Finset.univ.map e, C j v.val *
          ((if x v.val then 1 else 0 : ℤ)-(if y v.val then 1 else 0)) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro v _ hn
        have hH : v.val ∈ H := by
          by_contra hv
          exact hn (Finset.mem_map.mpr ⟨⟨⟨v.val,hv⟩,v.property⟩,Finset.mem_univ _,rfl⟩)
        simp [hhigh v.val hH]
      _ = _ := by rw [Finset.sum_map]; rfl
  simp only [mul_sub,Finset.sum_sub_distrib] at he
  have hf := congrFun hfree j
  simp only [LayoutSignatureBound.boolSignature,LayoutExactBuckets.signature] at hf ⊢
  apply sub_eq_zero.mp
  rw [he,hf,sub_self]


open OAI.Algorithms.SubexponentialSAT.MulticolorTypes OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSourceLocality
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete source locality for the streamed head evaluation.
The source correspondence is `NodeConcrete.fixedSourceRow_baseline_eq` in
LeafProgramNodeConcretePlan, the actual residualJet in
LeafProgramNodeConcreteResidual, and residualProduct in
LeafProgramNodeConcreteResidualProduct. Fixed-high bits cancel in the full
integer signatures; every correction specialization uses one common U. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog



open OAI SubexpLiftRing SubexpQuarticRing
open MulticolorTypes Subexp.ConstructivePacking
open LeafProgram LeafProgram.NodeConcrete
open LayoutProgram PerturbationAssembly Polynomial

noncomputable section

variable {r Q d n : ℕ}

/-- The actually stored baseline is equal under the owned-head bits and all
foreign full keys. Fixed-high coordinates cancel in the integer signatures. -/
theorem baseline_locality (p : SourceBank.Parameters r Q d) (ps : List (ℕ × ℕ))
    (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (howner : ∀ i,(ps.get i).1=(owner i).val)
    (head : Fin Q → Fin n → Fin r) (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (H : Finset (Fin n)) (node : Fin Q) (g : Fin r)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)
    (htheta : p.ops.decode theta=p.model.node p.t Q p.ht p.hfield node)
    (a b : Fin 768 → List Bool)
    (hhigh : ∀ v ∈ H,(a 145).getD v.val false=(b 145).getD v.val false)
    (hown : ∀ v : ResidualEmbedding.Free H,head node v.val=g →
      (a 145).getD v.val.val false=(b 145).getD v.val.val false)
    (hother : ∀ h,h≠g → freeLabel p ps P owner head H node h
        (fun v => (a 145).getD v.val.val.val false) =
      freeLabel p ps P owner head H node h (fun v => (b 145).getD v.val.val.val false))
    (f j : ℕ) (hj : (j,n+f)∈ps)
    (hslot : (P.label (planIndex ps n f j hj)).slot 0 node=g) :
    baseline (n:=n) p ps P theta a f j=baseline (n:=n) p ps P theta b f j := by
  have he := fixedSourceRow_baseline_eq p ps P owner howner head hhead f j hj node
    (fun v => boolInt ((a 145).getD v.val false))
    (fun v => boolInt ((b 145).getD v.val false))
    (by
      intro v hv
      apply congrArg boolInt
      by_cases hh : v∈H
      · exact hhigh v hh
      · exact hown ⟨v,hh⟩ (hv.trans hslot))
    (by
      intro h hh
      have hf := signature_eq_of_free H (head node) h
        (fun k v => LayoutProducedMatrix.literalNat P owner p.aWord.length p.R node k.val v.val)
        (fun v => (a 145).getD v.val false) (fun v => (b 145).getD v.val false)
        hhigh (hother h (by simpa only [hslot] using hh))
      exact hf)
  simpa only [baseline,boolInt_cast,←htheta,HashInput.boolValue] using he

/-- This is equality of the actual source jets before correction evaluation.
The missing-incidence branch is zero and the high branch is the common fixed bit. -/
theorem residualJet_locality (p : SourceBank.Parameters r Q d) (ps : List (ℕ × ℕ))
    (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (howner : ∀ i,(ps.get i).1=(owner i).val)
    (head : Fin Q → Fin n → Fin r) (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (H : Finset (Fin n)) (high : H → Bool) (node : Fin Q) (g : Fin r)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)
    (htheta : p.ops.decode theta=p.model.node p.t Q p.ht p.hfield node)
    (a b : Fin 768 → List Bool)
    (hhigh : ∀ v ∈ H,(a 145).getD v.val false=(b 145).getD v.val false)
    (hown : ∀ v : ResidualEmbedding.Free H,head node v.val=g →
      (a 145).getD v.val.val false=(b 145).getD v.val.val false)
    (hother : ∀ h,h≠g → freeLabel p ps P owner head H node h
        (fun v => (a 145).getD v.val.val.val false) =
      freeLabel p ps P owner head H node h (fun v => (b 145).getD v.val.val.val false))
    (f : ℕ) (hslot : ∀ j (hj : (j,n+f)∈ps),
      (P.label (planIndex ps n f j hj)).slot 0 node=g) :
    residualJet p ps P H high theta a f=residualJet p ps P H high theta b f := by
  funext j
  unfold residualJet
  by_cases hh : j∈H
  · simp only [dite_eq_left hh]
  · simp only [dite_eq_right hh]
    apply congrArg (Moments.incidenceJet _ (p.ops.decode theta))
    by_cases hj : (j.val,n+f)∈ps
    · exact baseline_locality p ps P owner howner head hhead H node g theta htheta
        a b hhigh hown hother f j.val hj (hslot j.val hj)
    · simp [baseline,fixedSourceRow,LayoutSourceRowsProgram.sourceRowFamily,hj]


/-- Whole selected group products agree as squarefree jets, before applying
the one shared correction U. All actual incidence rows use original IDs. -/
theorem sourceProduct_locality (q : Factor.Spec r Q n d)
    (owner : Fin q.ps.length → Fin n) (howner : ∀ i,(q.ps.get i).1=(owner i).val)
    (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t,(q.packing.label i).head t=head t (owner i))
    (H : Finset (Fin n)) (high : H → Bool) (node : Fin Q) (g : Fin r)
    (htheta : q.p.ops.decode q.theta=q.p.model.node q.p.t Q q.p.ht q.p.hfield node)
    (a b : Fin 768 → List Bool)
    (hhigh : ∀ v ∈ H,(a 145).getD v.val false=(b 145).getD v.val false)
    (hown : ∀ v : ResidualEmbedding.Free H,head node v.val=g →
      (a 145).getD v.val.val false=(b 145).getD v.val.val false)
    (hother : ∀ h,h≠g → freeLabel q.p q.ps q.packing owner head H node h
        (fun v => (a 145).getD v.val.val.val false) =
      freeLabel q.p q.ps q.packing owner head H node h
        (fun v => (b 145).getD v.val.val.val false))
    (ids : List ℕ) (hslot : ∀ f ∈ ids, ∀ j (hj : (j,n+f)∈q.ps),
      (q.packing.label (planIndex q.ps n f j hj)).slot 0 node=g) :
    sourceProduct q H high a ids=sourceProduct q H high b ids := by
  unfold sourceProduct
  apply congrArg (Squarefree.canonical q.u q.J)
  apply congrArg List.prod
  apply List.map_congr_left
  intro f hf
  have he := residualJet_locality q.p q.ps q.packing owner howner head hhead H high node g
    q.theta htheta a b hhigh hown hother f (hslot f hf)
  unfold AssignmentConcrete.residualValue
  rw [he]

/-- Immediate specialization uses the identical U for both original
assignments; equality therefore survives the actual dense projection. -/
theorem sourceProduct_specialize_locality (q : Factor.Spec r Q n d)
    (owner : Fin q.ps.length → Fin n) (howner : ∀ i,(q.ps.get i).1=(owner i).val)
    (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t,(q.packing.label i).head t=head t (owner i))
    (H : Finset (Fin n)) (high : H → Bool) (node : Fin Q) (g : Fin r)
    (htheta : q.p.ops.decode q.theta=q.p.model.node q.p.t Q q.p.ht q.p.hfield node)
    (a b : Fin 768 → List Bool)
    (hhigh : ∀ v ∈ H,(a 145).getD v.val false=(b 145).getD v.val false)
    (hown : ∀ v : ResidualEmbedding.Free H,head node v.val=g →
      (a 145).getD v.val.val false=(b 145).getD v.val.val false)
    (hother : ∀ h,h≠g → freeLabel q.p q.ps q.packing owner head H node h
        (fun v => (a 145).getD v.val.val.val false) =
      freeLabel q.p q.ps q.packing owner head H node h
        (fun v => (b 145).getD v.val.val.val false))
    (ids : List ℕ) (hslot : ∀ f ∈ ids, ∀ j (hj : (j,n+f)∈q.ps),
      (q.packing.label (planIndex q.ps n f j hj)).slot 0 node=g)
    (U : ResidualEmbedding.Free H → Bool) :
    QueryEvaluation.specializeDense q.u q.J U (sourceProduct q H high a ids) =
      QueryEvaluation.specializeDense q.u q.J U (sourceProduct q H high b ids) :=
  congrArg (QueryEvaluation.specializeDense q.u q.J U)
    (sourceProduct_locality q owner howner head hhead H high node g htheta
      a b hhigh hown hother ids hslot)

/-- Concrete hlocal for the actual colored selected-factor lists. Own-head
agreement and foreign full integer keys suffice; no evaluator, layout service,
or correction-dependent representative is assumed. -/
theorem colored_source_hlocal (q : Factor.Spec r Q n d)
    (owner : Fin q.ps.length → Fin n) (howner : ∀ i,(q.ps.get i).1=(owner i).val)
    (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t,(q.packing.label i).head t=head t (owner i))
    (H : Finset (Fin n)) (high : H → Bool) (node : Fin Q)
    (htheta : q.p.ops.decode q.theta=q.p.model.node q.p.t Q q.p.ht q.p.hfield node)
    (ids : List ℕ) (color : ℕ → Fin r)
    (hslot : ∀ f ∈ ids, ∀ j (hj : (j,n+f)∈q.ps),
      (q.packing.label (planIndex q.ps n f j hj)).slot 0 node=color f)
    (U : ResidualEmbedding.Free H → Bool) (g : Fin r)
    (x y : ResidualEmbedding.Free H → Bool)
    (hown : Moments.split (fun v : ResidualEmbedding.Free H => head node v.val) x g =
      Moments.split (fun v : ResidualEmbedding.Free H => head node v.val) y g)
    (hother : ∀ h,h≠g → freeLabel q.p q.ps q.packing owner head H node h
        (Moments.split (fun v : ResidualEmbedding.Free H => head node v.val) x h) =
      freeLabel q.p q.ps q.packing owner head H node h
        (Moments.split (fun v : ResidualEmbedding.Free H => head node v.val) y h)) :
    QueryEvaluation.specializeDense q.u q.J U
        (sourceProduct q H high (stateFor H high x) (ids.filter (fun f => color f=g))) =
      QueryEvaluation.specializeDense q.u q.J U
        (sourceProduct q H high (stateFor H high y) (ids.filter (fun f => color f=g))) := by
  apply sourceProduct_specialize_locality q owner howner head hhead H high node g htheta
  · intro v hv
    simp only [stateFor_get, HighIncidence.glue, dite_eq_left hv]
  · intro v hv
    simpa only [stateFor_get, HighIncidence.glue, dite_eq_right v.property, Moments.split]
      using congrFun hown ⟨v,hv⟩
  · intro h hh
    have hx : (fun v : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) h =>
        (stateFor H high x 145).getD v.val.val.val false) =
        Moments.split (fun v : ResidualEmbedding.Free H => head node v.val) x h := by
      funext v
      simp only [stateFor_get, HighIncidence.glue, dite_eq_right v.val.property,
        Moments.split]
    have hy : (fun v : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) h =>
        (stateFor H high y 145).getD v.val.val.val false) =
        Moments.split (fun v : ResidualEmbedding.Free H => head node v.val) y h := by
      funext v
      simp only [stateFor_get, HighIncidence.glue, dite_eq_right v.val.property,
        Moments.split]
    rw [hx,hy]
    exact hother h hh
  · intro f hf j hj
    have hh : f∈ids ∧ color f=g := by simpa only [List.mem_filter,decide_eq_true_eq] using hf
    exact (hslot f hh.1 j hj).trans hh.2

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QuerySourceTarget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual colored source products determine the interpolation target.
This joins the emitted first-occurrence sum to the existing source diagonal
identity. Native traversal, serialization and resources remain caller proofs. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySourceTarget

open scoped BigOperators
open Classical Polynomial OAI OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafProgram NodeConcrete Moments
open SignatureTupleDFS SignatureTupleTraversal HeadSourceLocality

variable {r Q n d : ℕ} {count : ℕ → ℕ} {K : ℕ → Type*}

/-- The signed finite-difference sum of the exact emitted tuple values is
the retained shifted source target. Admissibility and full-key locality are
derived from the actual source, rather than assumed as evaluator services. -/
theorem signed_source_target (q : Factor.Spec r Q n d) (hu : q.u = q.p.t)
    (H : Finset (Fin n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin n)
    (howner : ∀ i, (q.ps.get i).1 = (owner i).val)
    (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t, (q.packing.label i).head t = head t (owner i))
    (node : Fin Q)
    (htheta : q.p.ops.decode q.theta = q.p.model.node q.p.t Q q.p.ht q.p.hfield node)
    (ids : List ℕ) (hn : ids.Nodup)
    (hh : ∀ id < (AssignmentConcrete.weightedHashes q).length, id ∈ ids)
    (hm : q.marked = true → (AssignmentConcrete.weightedHashes q).length ∈ ids)
    (color : ℕ → Fin r)
    (hslot : ∀ f ∈ ids, ∀ j (hj : (j, n + f) ∈ q.ps),
      (q.packing.label (planIndex q.ps n f j hj)).slot 0 node = color f)
    (hzero : ∀ id j (v : Fin n), v ∈ H →
      PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v = 0)
    (hhash : ∀ id ∈ ids, ∀ hi : id < (AssignmentConcrete.weightedHashes q).length,
      ∀ w ∈ (AssignmentConcrete.weightedHashes q)[id], ∀ l ∈ w.literals,
        l.variable ∉ H → (l.variable.val, n + id) ∈ q.ps)
    (hmark : q.marked = true → (AssignmentConcrete.weightedHashes q).length ∈ ids →
      ∀ l ∈ q.markedClause, l.variable ∉ H →
        (l.variable.val, n + (AssignmentConcrete.weightedHashes q).length) ∈ q.ps)
    (key : (i : ℕ) → Fin (count i) → K i)
    (enumerate : ∀ g : Fin r, Fin (count g.val) ≃
      (Head (fun v : ResidualEmbedding.Free H => head node v.val) g → Bool))
    (hkernel : ∀ g i j, key g.val i = key g.val j ↔
      freeLabel q.p q.ps q.packing owner head H node g (enumerate g i) =
        freeLabel q.p q.ps q.packing owner head H node g (enumerate g j)) :
    (∑ E ∈ Finset.univ.filter (fun E : Finset (ResidualEmbedding.Free H) => E.card < q.J),
      ∑ U ∈ E.powerset, ((-1 : ℤ) ^ (E.card - U.card)) •
        ∑ reps : Prefix (Representatives key) r,
          Dense.readout (∏ g,
            ∑ x : Head (fun v : ResidualEmbedding.Free H => head node v.val) g → Bool,
              if freeLabel q.p q.ps q.packing owner head H node g x =
                  freeLabel q.p q.ps q.packing owner head H node g (enumerate g (reps g).val) ∧
                  (∀ v : Head (fun v : ResidualEmbedding.Free H => head node v.val) g,
                    v.val ∈ E → x v = true) then
                QueryEvaluation.specializeDense q.p.t q.J (fun v => decide (v ∈ U))
                  (sourceProduct q H high
                    (stateFor H high (assemble (fun v : ResidualEmbedding.Free H => head node v.val)
                      (Function.update (fun h => enumerate h (reps h).val) g x)))
                    (ids.filter (fun f => color f = g)))
              else 0)) =
      Truncated.ofPolynomial q.J ((specTarget q H high).comp
        (X + C (q.p.ops.decode q.theta))) := by
  let A := fun (g : Fin r) (x : ResidualEmbedding.Free H → Bool) =>
    sourceProduct q H high (stateFor H high x) (ids.filter (fun f => color f = g))
  let label := freeLabel q.p q.ps q.packing owner head H node
  have hlocal (U : Finset (ResidualEmbedding.Free H)) (g : Fin r)
      (x z : ResidualEmbedding.Free H → Bool)
      (hown : split (fun v : ResidualEmbedding.Free H => head node v.val) x g =
        split (fun v : ResidualEmbedding.Free H => head node v.val) z g)
      (hother : ∀ h, h ≠ g →
        label h (split (fun v : ResidualEmbedding.Free H => head node v.val) x h) =
          label h (split (fun v : ResidualEmbedding.Free H => head node v.val) z h)) :
      QueryEvaluation.specializeDense q.p.t q.J (fun v => decide (v ∈ U)) (A g x) =
        QueryEvaluation.specializeDense q.p.t q.J (fun v => decide (v ∈ U)) (A g z) := by
    have h := colored_source_hlocal q owner howner head hhead H high node
      htheta ids color hslot (fun v => decide (v ∈ U)) g x z hown hother
    exact Eq.mp (congrArg (fun u =>
      QueryEvaluation.specializeDense u q.J (fun v => decide (v ∈ U)) (A g x) =
        QueryEvaluation.specializeDense u q.J (fun v => decide (v ∈ U)) (A g z)) hu) h
  have hgroup := QueryTupleReadoutSemantics.grouped_dense_query_emitted q.p.t q.J
    (fun v : ResidualEmbedding.Free H => head node v.val) key enumerate label hkernel A
    (fun x => colored_source_admissible q H high (stateFor H high x) ids color) hlocal
  have htarget : Dense.readout (∑ x, QueryEvaluation.specializeDense q.p.t q.J x (∏ g, A g x)) =
      Truncated.ofPolynomial q.J ((specTarget q H high).comp
        (X + C (q.p.ops.decode q.theta))) := by
    simp only [map_prod]
    exact QueryJetSemantics.colored_residual_target_dense_shift q hu H high
      (stateFor H high) (stateFor_get H high) ids hn hh hm color hzero hhash hmark
  exact hgroup.symm.trans htarget

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySourceTarget
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureKeySource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Actual full signature keys and the source head labels

The selected-coordinate list retains its physical order. The equivalence below
is the existing explicit selected-ID equivalence; it neither sorts assignments
nor replaces the full raw matrix by a basis.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeySource

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
open BucketTupleProgram.Concrete
open LayoutProgram


variable {r Q d n : ℕ}

/-- Reindexing the actual selected columns gives exactly the full integer
label used by source locality, with every original row retained. -/
theorem ordered_signature (p : SourceBank.Parameters r Q d) (ps : List (ℕ × ℕ))
    (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
    (H : Finset (Fin n)) (node : Fin Q) (g : Fin r)
    (js : List ℕ) (hb : ∀ v ∈ js, v < n) (hn : js.Nodup)
    (hs : ∀ v : Fin n, v.val ∈ js ↔ ∃ _ : v ∉ H, head node v = g)
    (a : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) g → Bool) :
    LayoutSignatureBound.boolSignature
      (fun (j : Fin ps.length) (i : Fin js.length) =>
        LayoutProducedMatrix.literalNat P owner p.aWord.length p.R node j.val (js.get i))
      (freeAssignmentEquiv H (fun v => head node v.val) g js hb hn hs a) =
      HeadSourceLocality.freeLabel p ps P owner head H node g a := by
  funext j
  exact (freeOrder H (fun v => head node v.val) g js hb hn hs).sum_comp
    (fun v => LayoutProducedMatrix.literalNat P owner p.aWord.length p.R node
      j.val v.val.val.val * (if a v then 1 else 0 : ℤ))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeySource
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleSourceAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The frontend's actual mask, the produced head rows and the authentic
source factory use the same ambient variables and the same full integer keys.
No selected-coordinate or factory-alignment witness is supplied by the caller. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSourceAlignment

open scoped BigOperators
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open MulticolorTypes Subexp.ConstructivePacking
open LeafHeadSetupProgram LeafParametersProgram LayoutProgram
open BucketTupleProgram.Concrete

/-- Equality of all raw rows is unchanged by the actual length cast. -/
theorem row_cast_eq_iff {D E : ℕ} (h : D = E) (f g : Fin E → ℤ) :
    (fun j : Fin D => f (Fin.cast h j)) = (fun j => g (Fin.cast h j)) ↔ f = g := by
  cases h
  rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSourceAlignment
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryEmittedSourceTarget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The exact completed native tuple aggregate, with the same bounded numeric
representatives and the same physical factor IDs, has the source-target value. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget
open scoped BigOperators
open Classical Polynomial OAI OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafProgram NodeConcrete Moments
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleSource
open SignatureTupleRun HeadSourceLocality BucketTupleProgram.Concrete

variable (s : ProducedSource) {d : ℕ}
    (q : Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)

/-- Every original integer row agrees with the actual source label after only
the proved row-count cast. -/
theorem ordered_key (g : Fin s.input.r) (i : Fin (2^s.headSize g.val)) :
    (fun j : Fin s.input.D =>
      freeLabel q.p q.ps q.packing owner head H s.input.node g
        (enumerate s q H owner head facts g i) (Fin.cast facts.dimension.symm j)) =
      s.key g.val i := by
  have he := SignatureKeySource.ordered_signature q.p q.ps q.packing owner head H
    s.input.node g
    (selectedIds s g) (selectedIds_bound s g) (selectedIds_nodup s g)
    (facts.selected g) (enumerate s q H owner head facts g i)
  have henum : selectedEquiv s q H owner head facts g
      (enumerate s q H owner head facts g i) =
      AttainedSignatures.assignmentEquiv (s.headSize g.val) i := by
    change selectedEquiv s q H owner head facts g
      ((selectedEquiv s q H owner head facts g).symm
        (AttainedSignatures.assignmentEquiv (s.headSize g.val) i)) = _
    exact Equiv.apply_symm_apply _ _
  funext j
  calc
    _ = _ := (congrFun he (Fin.cast facts.dimension.symm j)).symm
    _ = _ := by
      change LayoutSignatureBound.boolSignature _
        (selectedEquiv s q H owner head facts g
          (enumerate s q H owner head facts g i)) _ = _
      rw [henum]
      unfold LayoutSignatureBound.boolSignature LayoutExactBuckets.signature
        ProducedSource.key SignatureTupleLoader.integerMatrix AttainedSignatures.integerKey
      apply Finset.sum_congr rfl
      intro v _
      dsimp only [Fin.val_cast]
      rw [facts.literal]
      rfl

theorem key_kernel (g : Fin s.input.r) (i j : Fin (2^s.headSize g.val)) :
    s.key g.val i = s.key g.val j ↔
      freeLabel q.p q.ps q.packing owner head H s.input.node g
        (enumerate s q H owner head facts g i) =
      freeLabel q.p q.ps q.packing owner head H s.input.node g
        (enumerate s q H owner head facts g j) := by
  rw [← ordered_key s q H owner head facts g i,
    ← ordered_key s q H owner head facts g j]
  exact SignatureTupleSourceAlignment.row_cast_eq_iff facts.dimension.symm _ _

private theorem mem_free_image (E : Finset (ResidualEmbedding.Free H))
    (v : ResidualEmbedding.Free H) :
    v.val ∈ E.image Subtype.val ↔ v ∈ E :=
  Subtype.val_injective.mem_finset_image

/-- The completed aggregate is precisely the pure emitted-tuple expression.
The ambient E/U images are the same physical masks, and all factor IDs remain. -/
theorem tuple_total_eq (E U : Finset (ResidualEmbedding.Free H))
    (ids : List ℕ) (color : ℕ → Fin s.input.r)
    (hids : ∀ g : Fin s.input.r, QueryVisitorHead.factorIds s.input g = ids.filter (fun f => color f = g)) :
    tupleTotal s.key s.input.r
      (emittedValue s q H (E.image Subtype.val) (U.image Subtype.val) high owner head facts) =
    tupleTotal s.key s.input.r (fun reps =>
      Dense.readout (∏ g,
        ∑ x : Head (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g → Bool,
          if freeLabel q.p q.ps q.packing owner head H s.input.node g x =
              freeLabel q.p q.ps q.packing owner head H s.input.node g
                (enumerate s q H owner head facts g (reps g).val) ∧
              (∀ v : Head (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g,
                v.val ∈ E → x v = true) then
            QueryEvaluation.specializeDense q.p.t q.J (fun v => decide (v ∈ U))
              (sourceProduct q H high
                (stateFor H high (assemble
                  (fun v : ResidualEmbedding.Free H => head s.input.node v.val)
                  (Function.update (fun h => enumerate s q H owner head facts h (reps h).val) g x)))
                (ids.filter (fun f => color f = g)))
          else 0)) := by
  apply congrArg (tupleTotal s.key s.input.r)
  funext reps
  unfold emittedValue
  apply congrArg Dense.readout
  apply Finset.prod_congr rfl
  intro g _
  unfold QueryVisitorHead.headValue QueryVisitorHead.fiberValue
  rw [hids g, emittedRepresentatives_eq]
  have hU : (fun v : ResidualEmbedding.Free H => decide (v.val ∈ U.image Subtype.val)) =
      fun v => decide (v ∈ U) := by
    funext v
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using mem_free_image s H U v
  rw [hU]
  apply Finset.sum_congr rfl
  intro x _
  have hE : (∀ v : Head (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g,
      v.val.val ∈ E.image Subtype.val → x v = true) ↔
      (∀ v : Head (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g,
        v.val ∈ E → x v = true) :=
    forall_congr' (fun v => imp_congr (mem_free_image s H E v.val) Iff.rfl)
  exact if_congr (and_congr Iff.rfl hE) rfl rfl

/-- The actual native aggregate, signed by ring multiplication as in the
pair commit, gives every retained coefficient of the shifted source target. -/
theorem signed_target_oai (hu : q.u = q.p.t)
    (howner : ∀ i, (q.ps.get i).1 = (owner i).val)
    (hhead : ∀ i t, (q.packing.label i).head t = head t (owner i))
    (htheta : q.p.ops.decode q.theta = q.p.model.node q.p.t s.input.Q q.p.ht q.p.hfield s.input.node)
    (ids : List ℕ) (hn : ids.Nodup)
    (hh : ∀ id < (AssignmentConcrete.weightedHashes q).length, id ∈ ids)
    (hm : q.marked = true → (AssignmentConcrete.weightedHashes q).length ∈ ids)
    (color : ℕ → Fin s.input.r)
    (hids : ∀ g : Fin s.input.r, QueryVisitorHead.factorIds s.input g = ids.filter (fun f => color f = g))
    (hslot : ∀ f ∈ ids, ∀ j (hj : (j, s.input.n + f) ∈ q.ps),
      (q.packing.label (planIndex q.ps s.input.n f j hj)).slot 0 s.input.node = color f)
    (hhash : ∀ id ∈ ids, ∀ hi : id < (AssignmentConcrete.weightedHashes q).length,
      ∀ w ∈ (AssignmentConcrete.weightedHashes q)[id], ∀ l ∈ w.literals,
        l.variable ∉ H → (l.variable.val, s.input.n + id) ∈ q.ps)
    (hmark : q.marked = true → (AssignmentConcrete.weightedHashes q).length ∈ ids →
      ∀ l ∈ q.markedClause, l.variable ∉ H →
        (l.variable.val, s.input.n + (AssignmentConcrete.weightedHashes q).length) ∈ q.ps)
 :
    (∑ E ∈ Finset.univ.filter (fun E : Finset (ResidualEmbedding.Free H) => E.card < q.J),
      ∑ U ∈ E.powerset, (-1) ^ (E.card - U.card) *
        tupleTotal s.key s.input.r
          (emittedValue s q H (E.image Subtype.val) (U.image Subtype.val) high owner head facts)) =
      Truncated.ofPolynomial q.J ((specTarget q H high).comp
        (X + C (q.p.ops.decode q.theta))) := by
  rw [← QuerySourceTarget.signed_source_target q hu H high owner howner head hhead
    s.input.node htheta ids hn hh hm color hslot facts.source_zero hhash hmark
    s.key (enumerate s q H owner head facts) (key_kernel s q H owner head facts)]
  apply Finset.sum_congr rfl
  intro E _
  apply Finset.sum_congr rfl
  intro U _
  rw [tuple_total_eq s q H high owner head facts E U ids color hids]
  simp only [tupleTotal, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget.signed_target_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget.signed_target_oai
