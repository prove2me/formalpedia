-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.fixedSourceRow_baseline_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:29:50.737612+00:00
-- url     : https://prove2.me/submissions/8fe2864c-6451-4aab-8061-234f330ca75b

import Mathlib
import Definitions.Def_OAIQ081S174
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_NodeConcrete_literal_signature_eq

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutExactBuckets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Exact integer signatures survive every coefficient-ring reduction

The assignments in this module are integer vectors. In the counting
application they are Boolean vectors or differences of Boolean vectors.
Equality of signatures is an equality in `ℤ`, before any reduction.
No claim about the kernel of a matrix reduced modulo a prime is used.
-/

namespace SubexponentialSAT.SqrtLog.LayoutExactBuckets

open scoped BigOperators
open LayoutPullback

variable {V J R : Type*} [Fintype V] [CommRing R]

theorem signature_sub (A : J → V → ℤ) (x y : V → ℤ) (j : J) :
    signature A (x - y) j = signature A x j - signature A y j := by
  simp [signature, mul_sub, Finset.sum_sub_distrib]

theorem value_sub (a : V → R) (x y : V → ℤ) :
    value a (x - y) = value a x - value a y := by
  simp [value, mul_sub, Finset.sum_sub_distrib]

theorem value_eq_of_signature_eq (a : V → R) (A : J → V → ℤ)
    (ha : KillsIntegerKernel a A) (x y : V → ℤ)
    (hxy : signature A x = signature A y) : value a x = value a y := by
  apply sub_eq_zero.mp
  rw [← value_sub]
  apply ha
  intro j
  rw [signature_sub, congrFun hxy j, sub_self]

end SubexponentialSAT.SqrtLog.LayoutExactBuckets

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutInterface
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Exact integer-bucket interface for the new incidence layout

This interface does not assert existence or a running time. Concrete
construction is assembled from the new packing, integer numerator, and
incidence-pullback modules. Unlike the old residue-only interface, its
locality conclusion is an exact equality in the coefficient ring.
-/

namespace SubexponentialSAT.SqrtLog.Layout

open scoped BigOperators
open LayoutExactBuckets

variable {V I F G O : Type*}
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G]
variable [CommRing O]

namespace Data

variable {owner : I → V} {factor : I → F} {Q R : ℕ}
variable (L : Data (O := O) (G := G) owner factor Q R)

theorem nodeValue_eq_sum (t : Fin Q) (i : I) (x : V → ℤ) :
    L.nodeValue t i x = ∑ g, L.localValue t i g (L.restrict t g x) := by
  exact (Fintype.sum_fiberwise (L.head t)
    (fun v => (L.row i v).eval (L.node t) * (x v : O))).symm

omit [Fintype G] in
/-- A foreign local contribution is constant on its actual integer bucket,
with equality in the entire coefficient ring, not only its residue field. -/
theorem localValue_eq (t : Fin Q) (i : I) (g : G)
    (hg : g ≠ L.color (factor i) t) (x y : L.Head t g → ℤ)
    (hxy : L.bucketLabel t g x = L.bucketLabel t g y) :
    L.localValue t i g x = L.localValue t i g y :=
  value_eq_of_signature_eq _ _ (L.locality t i g hg) x y hxy

/-- Keeping the owned head fixed and all other bucket labels fixed keeps
the actual incidence-row evaluation fixed. -/
theorem nodeValue_eq_of_buckets (t : Fin Q) (i : I) (x y : V → ℤ)
    (hown : L.restrict t (L.color (factor i) t) x =
      L.restrict t (L.color (factor i) t) y)
    (hother : ∀ g, g ≠ L.color (factor i) t →
      L.bucketLabel t g (L.restrict t g x) =
        L.bucketLabel t g (L.restrict t g y)) :
    L.nodeValue t i x = L.nodeValue t i y := by
  rw [L.nodeValue_eq_sum, L.nodeValue_eq_sum]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : g = L.color (factor i) t
  · subst g
    rw [hown]
  · exact L.localValue_eq t i g hg _ _ (hother g hg)

end Data

end SubexponentialSAT.SqrtLog.Layout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramBlockCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Literal block-lookup and incidence-fiber circuits for the ring source rows.
The branches are exactly those implemented by the packing metadata lookup;
this file identifies their polynomial meanings without any field assumption. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.SubexpSymbolicCost
open SubexponentialSAT.SubexpRowInterpolation SubexponentialSAT.SubexpTaylorExecution
open LayoutPullback

variable {I U C O : Type*} [Fintype I] [DecidableEq I]
  [Fintype U] [DecidableEq U] [CommRing O]

omit [Fintype I] in
theorem packedValue_eq (P : PackingData I U) (rows : U → U → Polynomial O) (v w : I) :
    packedValue P rows v w = LayoutBlocks.assembledRow P.completeBlocks rows v w := by
  cases hv : P.lookup v with
  | none =>
      rw [LayoutBlocks.assembledRow_outside _ _ _ ((P.lookup_none_iff v).mp hv)]
      simp only [packedValue, hv]
      split_ifs <;> simp
  | some z =>
      rcases z with ⟨j,u⟩
      have hv' := (P.lookup_some_iff v (j,u)).mp hv
      rw [← hv', LayoutBlocks.assembledRow_apply]
      cases hw : P.lookup w with
      | none =>
          have hout : w ∉ Set.range (P.completeBlocks.blockEmbedding j) := by
            rintro ⟨a,ha⟩
            exact (P.lookup_none_iff w).mp hw ⟨(j,a),ha⟩
          rw [row_eq_zero _ _ _ hout]
          simp [packedValue, PackingData.completeBlocks_apply, PackingData.lookup_at, hw]
      | some z =>
          rcases z with ⟨k,y⟩
          have hw' := (P.lookup_some_iff w (k,y)).mp hw
          rw [← hw']
          by_cases hj : j = k
          · subst k
            change packedValue P rows (P.completeBlocks.embed (j,u))
              (P.completeBlocks.embed (j,y)) = _
            rw [show P.completeBlocks.embed (j,y) = P.completeBlocks.blockEmbedding j y from rfl,
              row_apply_injective _ (P.completeBlocks.blockEmbedding j).injective]
            simp [packedValue, PackingData.completeBlocks_apply, PackingData.lookup_at,
              SubexponentialSAT.BlockPacking.CompleteBlocks.blockEmbedding]
          · have hout : P.completeBlocks.embed (k,y) ∉
                Set.range (P.completeBlocks.blockEmbedding j) := by
              rintro ⟨a,ha⟩
              have he := P.completeBlocks.embed.injective ha
              exact hj (congrArg Prod.fst he)
            rw [row_eq_zero _ _ _ hout]
            simp [packedValue, PackingData.completeBlocks_apply, PackingData.lookup_at, hj]

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The exact polynomial computed by the native owner-fiber traversal. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT
open scoped BigOperators

variable {A : Type*}

theorem fiber_sum_zipIdx [AddMonoid A] (ps : List (ℕ × ℕ)) (owner index : ℕ) (value : ℕ → A) :
    ((LayoutOwnerFiberProgram.fiberIndices owner index ps).map value).sum=
      ((ps.zipIdx index).map (fun x => if x.1.1=owner then value x.2 else 0)).sum := by
  induction ps generalizing index with
  | nil => rfl
  | cons p ps ih =>
      by_cases h : p.1=owner <;>
        simp [LayoutOwnerFiberProgram.fiberIndices,h,ih]

theorem ownerSum_zipIdx [AddMonoid A] (ps : List (ℕ × ℕ)) (owner : ℕ) (value : ℕ → A) :
    ownerSum ps owner value=
      ((ps.zipIdx).map (fun x => if x.1.1=owner then value x.2 else 0)).sum :=
  fiber_sum_zipIdx ps owner 0 value

theorem ownerSum_pullback [AddCommMonoid A] {n : ℕ} (ps : Fin n → ℕ × ℕ)
    (owner : ℕ) (value : ℕ → A) :
    ownerSum (List.ofFn ps) owner value=
      LayoutPullback.row (fun i : Fin n => (ps i).1) (fun i => value i.val) owner := by
  have hzip : (List.ofFn ps).zipIdx=List.ofFn (fun i : Fin n => (ps i,i.val)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [ownerSum_zipIdx,hzip]
  simp [LayoutPullback.row,List.map_ofFn,List.sum_ofFn]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramFamily
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Total original-coordinate source family computed by the native controller.
The missing-incidence branch is zero; required factor-scope incidences use
the exact packed row selected by the actual plan lookup. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

theorem sourceRowFamily_present {A : Type*} [AddMonoid A] (ps : List (ℕ × ℕ))
    (ambient factor literal : ℕ) (source : ℕ → ℕ → A) (owner : ℕ)
    (h : (literal,ambient+factor) ∈ ps) :
    sourceRowFamily ps ambient factor literal source owner=
      ownerSum ps owner (source (ps.idxOf (literal,ambient+factor))) := by
  simp [sourceRowFamily,h]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteLocality
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Equality of the integer signatures emitted by the actual matrix implies
exact equality of the source-row baseline in the full coefficient ring. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram LayoutExactBuckets LayoutPullback

variable {r Q d D n : ℕ}

theorem pulled_baseline_eq (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (t : Fin Q) (i : Fin D) (x y : Fin n → ℤ)
    (hown : ∀ v,head t v=(P.label i).slot 0 t → x v=y v)
    (hother : ∀ g,g≠(P.label i).slot 0 t →
      signature (fun (j : Fin D) (v : {v : Fin n //head t v=g}) =>
        LayoutProducedMatrix.literalNat P owner p.aWord.length p.R t j.val v.val.val)
        (fun v=>x v.val) =
      signature (fun (j : Fin D) (v : {v : Fin n //head t v=g}) =>
        LayoutProducedMatrix.literalNat P owner p.aWord.length p.R t j.val v.val.val)
        (fun v=>y v.val)) :
    (∑ v,(row owner (packedValue P p.rows i) v).eval (p.model.node p.t Q p.ht p.hfield t)*(x v : p.model.O p.t)) =
    ∑ v,(row owner (packedValue P p.rows i) v).eval (p.model.node p.t Q p.ht p.hfield t)*(y v : p.model.O p.t) := by
  have he : packedValue P p.rows i = LayoutBlocks.assembledRow P.completeBlocks p.rows i := by
    funext v
    exact packedValue_eq P p.rows i v
  rw [he]
  apply (pulled p P owner head hhead).nodeValue_eq_of_buckets t i x y
  · funext v
    exact hown v.val v.property
  · intro g hg
    exact literal_signature_eq p P owner head hhead t g _ _ (hother g hg)

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcretePlan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The original-address source lookup is exactly the owner pullback used by
integer-bucket locality, including repeated owner incidences. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram LayoutSourceRowsProgram PerturbationAssembly LayoutPullback

variable {r Q d n : ℕ}

theorem fixedSourceRow_eq_pullback (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (howner : ∀ i,(ps.get i).1=(owner i).val)
    (f j : ℕ) (hj : (j,n+f)∈ps) (v : Fin n) :
    fixedSourceRow p ps P n f j v =
      row owner (packedValue P p.rows (planIndex ps n f j hj)) v := by
  let i := planIndex ps n f j hj
  unfold fixedSourceRow
  rw [sourceRowFamily_present _ _ _ _ _ _ hj]
  have hs := ownerSum_pullback (fun a : Fin ps.length => ps.get a) v.val
    (totalPackedSource p P i.val)
  rw [List.ofFn_get] at hs
  have hi : i.val=ps.idxOf (j,n+f) := by
    simp only [i,planIndex,List.idxOf,beq_eq_decide]
  rw [← hi,hs]
  unfold row
  apply Finset.sum_congr rfl
  intro a _
  simp only [howner,totalPackedSource,packedSourceValue,dite_eq_left i.isLt,dite_eq_left a.isLt,
    Fin.ext_iff]
  rfl

theorem fixedSourceRow_baseline_eq_oai (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (howner : ∀ i,(ps.get i).1=(owner i).val)
    (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (f j : ℕ) (hj : (j,n+f)∈ps) (t : Fin Q) (x y : Fin n → ℤ)
    (hown : ∀ v,head t v=(P.label (planIndex ps n f j hj)).slot 0 t → x v=y v)
    (hother : ∀ g,g≠(P.label (planIndex ps n f j hj)).slot 0 t →
      LayoutExactBuckets.signature (fun (k : Fin ps.length) (v : {v : Fin n //head t v=g}) =>
        LayoutProducedMatrix.literalNat P owner p.aWord.length p.R t k.val v.val.val)
        (fun v=>x v.val) =
      LayoutExactBuckets.signature (fun (k : Fin ps.length) (v : {v : Fin n //head t v=g}) =>
        LayoutProducedMatrix.literalNat P owner p.aWord.length p.R t k.val v.val.val)
        (fun v=>y v.val)) :
    (∑ v,(fixedSourceRow p ps P n f j v).eval (p.model.node p.t Q p.ht p.hfield t)*
      (x v : p.model.O p.t)) =
    ∑ v,(fixedSourceRow p ps P n f j v).eval (p.model.node p.t Q p.ht p.hfield t)*
      (y v : p.model.O p.t) := by
  simp_rw [fixedSourceRow_eq_pullback p ps P owner howner f j hj]
  exact pulled_baseline_eq p P owner head hhead t (planIndex ps n f j hj) x y hown hother

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.fixedSourceRow_baseline_eq_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.fixedSourceRow_baseline_eq_oai
