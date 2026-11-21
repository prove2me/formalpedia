-- Prove2me | solution 1 for OAI.HadwigerCounterexample.StatusAnalysis.invoke
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T23:06:27.246217+00:00
-- url     : https://prove2.me/submissions/bde71441-681e-4f1f-bd43-50ffa83d71d8

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Projection
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_OAIQ430Hc000

section
-- module Solutions.OAIQ430_HC.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BinaryMatrices
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary Matrices -/

noncomputable section
namespace HadwigerCounterexample

open scoped BigOperators
open Matrix

theorem bit_cases (x : F) : x = 0 ∨ x = 1 :=
  (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) x
theorem bit_sq (x : F) : x*x = x := by rcases bit_cases x with e|e <;> rw [e] <;> simp

section Linear

variable {I J K L R S : Type} [Fintype I] [Fintype J]

theorem mpair_outer (M : Mat I J) (x : Vec I) (y : Vec J) :
    mpair M (vecMulVec x y) = evmat M x y := by
  dsimp [mpair,evmat,mulVec,dotProduct,vecMulVec]
  simp only [Finset.mul_sum,mul_left_comm]

theorem liftM_outer (P : Mat K I) (Q : Mat L J) (x : Vec I) (y : Vec J) :
    liftM P Q (vecMulVec x y) = vecMulVec (P *ᵥ x) (Q *ᵥ y) := by
  rw [liftM_def,mul_vecMulVec,vecMulVec_mul,vecMul_transpose]

variable [Fintype K] [Fintype L]

theorem mpair_liftM (P : Mat K I) (Q : Mat L J) (M : Mat K L) (A : Mat I J) :
    mpair M (liftM P Q A) = mpair (liftM Pᵀ Qᵀ M) A := by

  simp only [liftM_def, mpair, transpose_transpose, LinearMap.coe_mk,AddHom.coe_mk,
    Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, transpose_apply]

  conv_lhs =>
    arg 2
    intro k
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs =>
    arg 2
    intro k
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

end Linear
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MatrixRanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! # Matrix Ranks -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Function

section Generic
variable {V W U : Type}
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  [AddCommGroup U] [Module F U]

theorem rk_inj {f : V →ₗ[F] W} [FiniteDimensional F V] : Injective f ↔ rk f = dim V := by
  constructor
  · exact LinearMap.finrank_range_of_inj
  intro h
  rw [← ker_eq_bot, ← Submodule.finrank_eq_zero (R:=F)]
  have hj := f.finrank_range_add_finrank_ker
  dsimp only [rk,dim] at h
  omega

end Generic

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ComponentIndices
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Component Indices -/

noncomputable section
namespace HadwigerCounterexample

variable {g : ℕ}

theorem card_allowed (d : Tag g) : Fintype.card {l : Tag g // allowed d l} = (g-1)/2 := by
  have : NeZero g := ⟨by have := d.isLt; omega⟩
  let T := {l : Tag g // allowed d l}
  let f (i : Fin ((g-1)/2)) : Tag g := ⟨i.val+1,by have := i.isLt; omega⟩
  have hf (i) : allowed d (f i + d) := by
    have := i.isLt
    simp only [allowed,add_sub_cancel_right,f]
    omega
  let h : Fin ((g-1)/2) → T := fun i => ⟨f i + d,hf i⟩
  have hh : Function.Bijective h := by
    constructor
    · intro i j hij
      have he : f i = f j := add_right_cancel (congrArg Subtype.val hij)
      have he' := congrArg Fin.val he
      exact Fin.ext (Nat.add_right_cancel he')
    · intro l
      have hl := l.property
      unfold allowed at hl
      let i : Fin ((g-1)/2) := ⟨(l.val-d).val-1,by omega⟩
      have hi : f i = l.val-d := Fin.ext (by dsimp only [i,f]; omega)
      refine ⟨i,Subtype.ext ?_⟩
      change f i + d = _
      rw [hi,sub_add_cancel]
  simpa using (Fintype.card_congr (Equiv.ofBijective h hh)).symm

theorem card_allowed' (l : Tag g) :
    Fintype.card {d : Tag g // allowed d l} = (g-1)/2 := by
  have : NeZero g := ⟨by have := l.isLt; omega⟩
  let h : {d : Tag g // allowed d l} ≃ {x : Tag g // allowed 0 x} := {
    toFun := fun d => ⟨l-d.val, by simpa only [allowed,sub_zero] using d.property⟩
    invFun := fun x => ⟨l-x.val, by simpa only [allowed,sub_sub_cancel,sub_zero] using
      x.property⟩
    left_inv := fun d => Subtype.ext (sub_sub_cancel _ _)
    right_inv := fun x => Subtype.ext (sub_sub_cancel _ _) }
  exact (Fintype.card_congr h).trans (card_allowed _)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BooleanLabels
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Boolean Labels -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Finset
variable {b : ℕ}

theorem mono_insert (s : Label b) (S : Finset (Fin b)) (i) :
    monoBit s (insert i S) = s i * monoBit s S := by
  by_cases h : i∈S
  · rw [insert_eq_of_mem h]
    unfold monoBit
    rw [← Finset.mul_prod_erase _ _ h,← mul_assoc,bit_sq]
  · simp [monoBit,h]

/-- Independence up to degree j for at most j+1 labels, in coefficient form. -/
theorem selector_indep (L : Finset (Label b)) (c : Label b → F) (j : ℕ)
    (h : L.card ≤ j+1) (hf : ∀ S : Finset (Fin b), S.card ≤ j →
      ∑ s ∈ L,c s*monoBit s S=0) : ∀ i∈L,c i=0 := by
  classical
  intro s hs
  induction L using Finset.strongInductionOn generalizing c j with | _ L ih
  by_cases hL : ∃ i∈L,i≠s
  · obtain ⟨t,ht,hst⟩ := hL
    obtain ⟨i,hi⟩ : ∃ i : Fin b,t i≠s i := Function.ne_iff.mp hst
    let d (u : Label b) := (u i-t i) * c u
    have hg : j>0 := by have he := Finset.one_lt_card.mpr ⟨t,ht,s,hs,hst⟩; omega
    have he : (L.erase t).card ≤ (j-1)+1 := by
      have he := card_erase_add_one ht; omega
    have hw (U : Finset (Fin b)) (hu : U.card ≤ j-1) :
        ∑ s ∈ L.erase t,d s*monoBit s U=0 := by
      have heq (s : Label b) :
          d s * monoBit s U = c s * monoBit s (insert i U) - t i*(c s*monoBit s U) := by
        unfold d; rw [mono_insert]; ring
      rw [show ∑ s ∈ L.erase t,d s*monoBit s U = ∑ s ∈ L,d s*monoBit s U by
        conv_rhs => rw [← Finset.add_sum_erase _ _ ht]
        simp [d]]
      simp_rw [heq, Finset.sum_sub_distrib,← Finset.mul_sum]
      have hj : (insert i U).card ≤ j := by
        by_cases hh : i∈U
        · rw [insert_eq_of_mem hh]; omega
        · rw [card_insert_of_notMem hh]; omega
      rw [hf _ hj, hf _ (by omega),mul_zero,sub_zero]
    have hu := ih (L.erase t) (erase_ssubset ht) d (j-1) he hw
      (Finset.mem_erase.mpr ⟨hst.symm,hs⟩)
    exact (mul_eq_zero.mp hu).resolve_left (sub_ne_zero.mpr hi.symm)
  · have he : L={s} := by
      ext x; constructor
      · intro hx; exact mem_singleton.mpr (Classical.byContradiction fun h => hL ⟨x,hx,h⟩)
      intro hx; rwa [mem_singleton.mp hx]
    have hh := hf ∅ (by simp)
    simpa [he,monoBit] using hh

variable {p : Shape} {n : ℕ}

/-- Short label-tagged rays give a direct family of copies of the affine-vector space. -/
theorem ray_indep (L : Finset (Label p.b)) (Z : Label p.b → Vec (AIdx p.g n))
    (hj : L.card ≤ p.j+1) (he : ∑ i∈L, putLab p n i (Z i) = 0) :
    ∀ i∈L, Z i=0 := by
  have hg (u : AIdx p.g n) (i : Label p.b) (hi : i ∈ L) :
      Z i u=0 := by
    refine selector_indep L (fun i => Z i u) p.j hj ?_ i hi
    intro S hS
    have hh := congr_fun he ((⟨S,hS⟩ : SelIdx p.b p.j),u)
    simpa [putLab,Finset.sum_apply,monoBit,selV,mul_comm] using hh
  exact fun i hi => funext (fun u => hg u i hi)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CoordinateEmbeddings
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate Embeddings -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Function
open scoped BigOperators
variable {U V I J K T : Type} [Fintype U] [Fintype V] [Fintype I] [Fintype J]
    [Fintype K] [Fintype T]

omit [Fintype I] in
theorem embedMatT [DecidableEq U] (f : I → U) (x : Vec U) :
    (embedMat f)ᵀ *ᵥ x = fun i => x (f i) := by
  classical funext i
            simp [embedMat,Matrix.mulVec,dotProduct]

omit [Fintype V] [Fintype I] in
theorem mul_embedMat [DecidableEq U] (f : I → U) (M : Mat V U) :
    M*embedMat f = M.submatrix _root_.id f := by
  ext i j
  simp [Matrix.mul_apply,embedMat]

omit [Fintype V] [Fintype I] in
theorem embedMat_mul [DecidableEq U] (f : I → U) (M : Mat U V) :
    (embedMat f)ᵀ*M = M.submatrix f _root_.id := by
  ext i j
  simp [Matrix.mul_apply,embedMat]

omit [Fintype I] in
theorem embedMat_self [DecidableEq I] [DecidableEq U] {f : I → U} (h : Injective f) :
    (embedMat f)ᵀ * embedMat f = 1 := by
  ext i j
  rw [embedMat_mul]
  simp only [embedMat,Matrix.submatrix_apply,Matrix.of_apply,id_eq,
    Matrix.one_apply,h.eq_iff]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Laws -/

noncomputable section
open scoped BigOperators

namespace HadwigerCounterexample

variable {α β : Type*}

theorem ind_one {p : Prop} (h : p) : ind p = 1 := by classical simp [ind, h]
theorem ind_zero {p : Prop} (h : ¬p) : ind p = 0 := by classical simp [ind, h]
@[simp] theorem ind_true : ind True = 1 := ind_one trivial
@[simp] theorem ind_false : ind False = 0 := ind_zero (not_false)

theorem ind_nonneg (p : Prop) : 0 ≤ ind p := by
  by_cases h : p
  · exact le_of_lt (by rw [ind_one h]; norm_num)
  · rw [ind_zero h]

theorem ind_le_one (p : Prop) : ind p ≤ 1 := by
  by_cases h : p
  · rw [ind_one h]
  · rw [ind_zero h]
    norm_num

theorem ind_mono {p q : Prop} (hp : p → q) : ind p ≤ ind q := by
  by_cases h : p
  · rw [ind_one h, ind_one (hp h)]
  · rw [ind_zero h]
    exact ind_nonneg _

theorem ind_and (p q : Prop) : ind (p ∧ q) = ind p * ind q := by
  by_cases h : p <;> by_cases h2 : q <;> simp [ind, h, h2]

section Basic
variable [Fintype α] {w v f g : Wgt α} {p q : α → Prop}

theorem tot_nonneg (hw : ∀ x, 0 ≤ w x) : 0 ≤ tot w := Finset.sum_nonneg fun x _ => hw x

theorem avg_mono (hw : ∀ x, 0 ≤ w x) (h : ∀ x, f x ≤ g x) : avg w f ≤ avg w g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (hw x)

theorem avg_nonneg (hw : ∀ x, 0 ≤ w x) (hf : ∀ x, 0 ≤ f x) : 0 ≤ avg w f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (hf x)

theorem avg_const (w : Wgt α) (a : ℝ) : avg w (fun _ => a) = tot w * a := by
  rw [avg, tot, Finset.sum_mul]

theorem avg_mul (w f : Wgt α) (b : ℝ) : avg w (fun x => f x * b) = avg w f * b := by
  simp only [avg, Finset.sum_mul, mul_assoc]

theorem avg_mul' (w f : Wgt α) (b : ℝ) : avg w (fun x => b * f x) = b * avg w f := by
  simpa only [mul_comm b] using avg_mul w f b

theorem pr_nonneg (hw : ∀ x, 0 ≤ w x) : 0 ≤ pr w p :=
  avg_nonneg hw fun _ => ind_nonneg _

theorem pr_le_tot (hw : ∀ x, 0 ≤ w x) : pr w p ≤ tot w := by
  unfold pr
  refine (avg_mono hw fun x => ind_le_one (p x)).trans_eq ?_
  rw [avg_const, mul_one]

@[simp] theorem pr_true (w : Wgt α) : pr w (fun _ => True) = tot w := by simp [pr, avg, tot]
@[simp] theorem pr_false (w : Wgt α) : pr w (fun _ => False) = 0 := by simp [pr]

theorem exists_of_pr_pos (hw : ∀ x, 0 ≤ w x) (hp : 0 < pr w p) :
    ∃ x, p x ∧ 0 < w x := by
  by_contra! hn
  have h : pr w p = 0 := by
    unfold pr avg
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : p x
    · rw [le_antisymm (hn x hx) (hw x), zero_mul]
    · simp only [ind_zero hx, mul_zero]
  exact hp.ne' h

end Basic

section Restrict
variable [Fintype α] {w : Wgt α} {p : α → Prop}

omit [Fintype α] in
theorem subW_nonneg (hw : ∀ x, 0 ≤ w x) (p : α → Prop) : ∀ x, 0 ≤ subW w p x :=
  fun x => mul_nonneg (hw x) (ind_nonneg _)

omit [Fintype α] in
theorem subW_carried (w : Wgt α) (p : α → Prop) : carried (subW w p) p :=
  fun x h => by rw [subW, ind_zero h, mul_zero]

theorem normW_nonneg (hw : ∀ x, 0 ≤ w x) : ∀ x, 0 ≤ normW w x :=
  fun x => div_nonneg (hw x) (tot_nonneg hw)

theorem tot_norm (w : Wgt α) : tot (normW w) = tot w / tot w := by
  simp only [tot, normW, div_eq_mul_inv, Finset.sum_mul]

theorem normW_law (hw : ∀ x, 0 ≤ w x) (hpos : 0 < tot w) : IsLaw (normW w) :=
  ⟨normW_nonneg hw, by rw [tot_norm, div_self hpos.ne']⟩

end Restrict

section Prod
variable [Fintype α] [Fintype β] {w : Wgt α} {v : Wgt β}

theorem pairW_avg (w : Wgt α) (v : Wgt β) (f : α × β → ℝ) :
    avg (pairW w v) f = avg w (fun x => avg v (fun y => f (x,y))) := by
  simp only [avg, Finset.mul_sum, Fintype.sum_prod_type, pairW, mul_assoc]

theorem pairW_separate (w f : Wgt α) (v g : Wgt β) :
    avg (pairW w v) (fun p => f p.1 * g p.2) = avg w f * avg v g := by
  simp only [pairW_avg, avg_mul', avg_mul]

theorem pairW_pr (w : Wgt α) (v : Wgt β) (p : α → Prop) (q : β → Prop) :
    pr (pairW w v) (fun x => p x.1 ∧ q x.2) = pr w p * pr v q := by
  simp_rw [pr, ind_and]
  exact pairW_separate w (fun x => ind (p x)) v (fun y => ind (q y))

theorem pairW_tot (w : Wgt α) (v : Wgt β) : tot (pairW w v) = tot w * tot v := by
  simpa using pairW_pr w v (fun _ => True) (fun _ => True)

theorem pairW_law (hw : IsLaw w) (hv : IsLaw v) : IsLaw (pairW w v) :=
  ⟨fun x => mul_nonneg (hw.nz _) (hv.nz _), by rw [pairW_tot, hw.total, hv.total, mul_one]⟩

end Prod

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteAffineLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Affine Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap
open scoped BigOperators

theorem dim_mat (I J : Type) [Fintype I] [Fintype J] :
    dim (Mat I J) = Fintype.card I * Fintype.card J := by
  simp only [dim,Mat,finrank_matrix,finrank_self,mul_one]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_TensorIntersections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tensor Intersections -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule
open scoped BigOperators

variable {p : Shape} {n N : ℕ}

section Rank
variable {U I J L : Type} [Fintype I] [Fintype J] [Fintype U] [Fintype L]

omit [Fintype U] in
theorem colSp_lift_le (P : Mat U I) (Q : Mat L J) (A : Mat I J) :
    colSp (liftM P Q A) ≤ colSp P := by
  rw [liftM_def,Matrix.mul_assoc,colSp, Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

end Rank

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MatrixQuotients
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matrix Quotients -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module
open scoped BigOperators
variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

theorem box_dim (S : Space (Vec I)) (T : Space (Vec J)) :
    dim (box S T) = dim S*dim T := by
  have h := rk_inj.mp (liftM_inj (pack_inj S) (pack_inj T))
  change dim (box S T)=dim (Mat _ _) at h
  rw [dim_mat, Fintype.card_fin,Fintype.card_fin] at h
  exact h

omit [Fintype K] [Fintype L] in
theorem liftM_transpose (A : Mat I J) (P : Mat K I) (Q : Mat L J) :
    (liftM P Q A)ᵀ = liftM Q P Aᵀ := by
  simp only [liftM_def,transpose_mul,transpose_transpose,Matrix.mul_assoc]

theorem box_mem (M : Mat I J) (S : Space (Vec I)) (T : Space (Vec J)) :
    M∈box S T ↔ colSp M ≤ S ∧ colSp Mᵀ ≤ T := by
  classical
  constructor
  · rintro ⟨A,rfl⟩
    rw [liftM_transpose]
    exact ⟨(colSp_lift_le ..).trans_eq (colSp_pack _),
      (colSp_lift_le ..).trans_eq (colSp_pack _)⟩
  · rintro ⟨h,g⟩
    obtain ⟨X,hX⟩ := mat_left_inv (pack_inj S)
    obtain ⟨Y,hY⟩ := mat_left_inv (pack_inj T)
    have h1 {I J : Type} [Fintype I] [Fintype J] {A : Mat I J} {S : Space (Vec I)}
        (h : colSp A ≤ S) {X : Mat (Fin (dim S)) I} (hx : X*pack S=1) : pack S*(X*A)=A := by
      apply coe_mv_inj
      refine LinearMap.ext fun x => ?_
      have he : A*ᵥx ∈ colSp (pack S) := (colSp_pack S).symm ▸
        h (show A*ᵥx∈colSp A from ⟨x,rfl⟩)
      obtain ⟨y,hy⟩ := he
      change pack S *ᵥ y=A *ᵥ x at hy
      change _ *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hy, Matrix.mulVec_mulVec y X, hx,
        Matrix.one_mulVec]
      exact hy
    refine ⟨liftM X Y M,?_⟩
    have h2 := congrArg Matrix.transpose (h1 g hY)
    rw [transpose_mul,transpose_mul,transpose_transpose] at h2
    change pack S * (X*M*Yᵀ)*(pack T)ᵀ=M
    rw [← Matrix.mul_assoc (pack S) (X*M),h1 h hX,h2]

theorem box_le {M M' : Space (Vec I)} {N N' : Space (Vec J)} (hm : M ≤ M') (hn : N ≤ N') :
    box M N ≤ box M' N' := fun _ h =>
  have he := (box_mem ..).mp h
  (box_mem ..).mpr ⟨he.1.trans hm,he.2.trans hn⟩

theorem outer_in_box (x : Vec I) (y : Vec J) {S : Space (Vec I)} {T : Space (Vec J)}
    (hx : x∈S) (hy : y∈T) : vecMulVec x y ∈ box S T := by
  obtain ⟨a,rfl⟩ := (pack_mem_iff ..).mp hx
  obtain ⟨b,rfl⟩ := (pack_mem_iff ..).mp hy
  exact ⟨vecMulVec a b,liftM_outer ..⟩

theorem lift_mem_box {M : Mat I J} {S : Space (Vec I)} {T : Space (Vec J)}
    (P : Mat K I) (Q : Mat L J) (h : M ∈ box S T) :
    liftM P Q M ∈ box (S.map P.mulVecLin) (T.map Q.mulVecLin) := by
  obtain ⟨A,rfl⟩ := h
  rw [liftM_comp,box_mem,liftM_transpose]
  constructor <;> apply le_trans (colSp_lift_le ..) <;>
    rw [colSp,mulVecLin_mul,LinearMap.range_comp]
  · rw [show LinearMap.range (pack S).mulVecLin=S from colSp_pack _]
  rw [show LinearMap.range (pack T).mulVecLin=T from colSp_pack _]

theorem evmat_transpose (M : Mat I J) (x : Vec I) (y : Vec J) :
    evmat Mᵀ y x=evmat M x y := dotProduct_transpose_mulVec _ _ _
theorem evmat_pull (P : Mat K I) (Q : Mat L J) (A : Mat K L) (x : Vec I) (y : Vec J) :
    evmat (pullM P Q A) x y=evmat A (P *ᵥ x) (Q *ᵥ y) := by
  rw [←mpair_outer,←mpair_outer,← liftM_outer,mpair_liftM]; rfl

theorem evmat_ext {M N : Mat I J} (h : ∀ x y, evmat M x y=evmat N x y) : M=N := by
  classical
  ext i j
  simpa [evmat] using h (Pi.single i 1) (Pi.single j 1)

theorem box_eval_iff (S : Space (Vec I)) (T : Space (Vec J)) (M N : Mat I J) :
    (∀ x∈S,∀ y∈T,evmat M x y=evmat N x y) ↔ (∀ x∈box S T,mpair M x=mpair N x) := by
  constructor
  · intro h x hx
    have hE : pullM (pack S) (pack T) M=pullM (pack S) (pack T) N := by
      refine evmat_ext (fun x y => ?_)
      rw [evmat_pull,evmat_pull]
      exact h _ ((pack_mem_iff ..).mpr ⟨x,rfl⟩) _ ((pack_mem_iff ..).mpr ⟨y,rfl⟩)
    obtain ⟨A,rfl⟩ := hx
    rw [mpair_liftM,mpair_liftM]
    exact congrArg (fun x => mpair x A) hE
  intro h x hx y hy
  rw [← mpair_outer,← mpair_outer]
  exact h _ (outer_in_box _ _ hx hy)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SparseLabelBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sparse Label Bounds -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Finset Submodule
variable {p : Shape} {n : ℕ}

theorem labcomb_eval (L : Finset (Label p.b)) (z : LabVals p n) :
    labcomb p n L z= ∑ i∈L, putLab p n i (z i) := by simp [labcomb,LinearMap.sum_apply]

theorem within_eq {L B : Finset (Label p.b)} (h : B ⊆ L) (z : LabVals p n) :
    labcomb p n B z = labcomb p n L (withinL p B z) := by
  classical
  rw [labcomb_eval,labcomb_eval]
  refine (sum_congr (g:=fun i => putLab p n i (withinL p B z i)) rfl fun i hi => ?_).trans
    (sum_subset h fun i _ hi => ?_)
  · simp [withinL,hi]
  simp [withinL,hi]

theorem labV_mono {L B : Finset (Label p.b)} (h : B ⊆ L) : labV p n B ≤ labV p n L := by
  rintro x ⟨y,rfl⟩
  exact ⟨_,(within_eq h y).symm⟩

theorem labV_unique {L B : Finset (Label p.b)} {z : LabVals p n}
    (h : labcomb p n B z∈labV p n L) (hj : (B∪L).card≤p.j+1) :
    ∀ i∈B,i∉L → z i=0 := by
  intro i hi hL
  obtain ⟨x,hx⟩ := h
  rw [within_eq (B:=L) (L:=B∪L) subset_union_right,
    within_eq (B:=B) (L:=B∪L) subset_union_left] at hx
  have he :
      labcomb p n (B∪L) ((withinL p B z)-(withinL p L x))=0 := by rw [map_sub,hx,sub_self]
  rw [labcomb_eval] at he
  have hg := ray_indep _ _ hj he i (mem_union_left L hi)
  simpa [withinL,hL,hi] using hg

theorem protect_labels (p : Shape) {n} (S : Space (Ray p n)) (q : ℕ)
    (hq : (dim S+1)*q≤p.j+1) :
    ∃ L : Finset (Label p.b), L.card≤dim S * q ∧ protectedBy p S q L := by
  classical
  let T : Set ℕ := {t | ∃ (A : Space (Ray p n)) (L : Finset (Label p.b)), A ≤ S ∧
    A ≤ labV p n L ∧ L.card ≤ t*q ∧ t = dim A}
  have he : BddAbove T := ⟨dim S, by
    rintro x ⟨A,L, hA,hL,_,rfl⟩
    exact Submodule.finrank_mono hA⟩
  have hn : T.Nonempty := ⟨0, ⊥,∅, bot_le, bot_le, by simp, (finrank_bot ..).symm⟩
  obtain ⟨A,L,hA,hL,hsize,hd⟩ := (show sSup T∈T from Nat.sSup_mem hn he)
  have hi := finrank_mono hA
  rw [hd] at hsize
  have hsc : L.card ≤ dim S*q := hsize.trans (Nat.mul_le_mul_right _ hi)
  refine ⟨L,hsc,fun B z hz hB => ?_⟩
  have hh : (B∪L).card≤p.j+1 := by
    refine (card_union_le _ _).trans ((add_le_add hB hsc).trans ?_)
    simpa [Nat.add_mul, Nat.add_comm] using hq
  let x := labcomb p n B z
  apply labV_unique _ hh
  by_cases hx : x∈A
  · exact hL hx
  let V : Space (Ray p n) := Submodule.span F ({x}:Set _)
  have hv : dim A < dim (A⊔V : Submodule _ _) := by
    apply Nat.lt_of_le_of_ne (Submodule.finrank_mono (show A≤A⊔V from le_sup_left)) (fun h => hx ?_)
    have hh : A=A⊔V := Submodule.eq_of_le_of_finrank_eq le_sup_left h
    exact (show V≤A from le_trans le_sup_right hh.symm.le) (show x ∈ V from
      Submodule.subset_span (Set.mem_singleton _))
  have hk : dim (A⊔V : Submodule _ _)∈ T := by
    refine ⟨A⊔V,B∪L,sup_le hA ((Submodule.span_singleton_le_iff_mem x S).mpr hz),
      sup_le (hL.trans (labV_mono subset_union_right)) ?_, ?_,rfl⟩
    · refine le_trans ((Submodule.span_singleton_le_iff_mem x _).mpr (show x∈labV p n B from
        ⟨z,rfl⟩)) (labV_mono subset_union_left)
    exact (card_union_le _ _).trans ((Nat.add_le_add hB hsize).trans (by
      simpa [Nat.add_mul,add_comm q] using Nat.mul_le_mul_right q hv))
  have hg := le_csSup he hk
  exact (not_le_of_gt hv (by rwa [← hd])).elim

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_NominalSpaces
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nominal Spaces -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module
open scoped BigOperators

variable {p : Shape} {n N : ℕ}

theorem IP_self (b) : (IP p n b)ᵀ*IP p n b=1 := by
  apply embedMat_self
  intro i j; cases b <;> simp [putFull]
theorem IP_IH (a b : Bool) : (IP p n a)ᵀ * IH p n b=0 := by
  unfold IP IH; rw [embedMat_mul]
  ext i j; cases a <;> cases b <;> simp [embedMat,putFull]

theorem IP_cross {a b : Bool} (h : a ≠ b) : (IP p n a)ᵀ * IP p n b=0 := by
  unfold IP; rw [embedMat_mul]
  ext i j; cases a <;> cases b <;> first | contradiction | simp [embedMat,putFull]

theorem ip_decomp (x : Dir p n) :
    (∑ b : Bool, ((IP p n b) *ᵥ ((IP p n b)ᵀ*ᵥx)+ (IH p n b)*ᵥ ((IH p n b)ᵀ*ᵥx)))=x := by
  rw [Fintype.sum_bool]
  unfold IP IH
  simp_rw [embedMatT]
  ext i
  rcases i with (i|i)|(i|i) <;>
    simp [embedMat,putFull,Matrix.mulVec,dotProduct,Pi.add_apply]

theorem images_ip (x : UnitType p n N) (z : Place p) (b : Bool) :
    images x z * IP p n b = primary (takeSign (onSide x b z.1) z.2) := by
  unfold IP; rw [mul_embedMat]
  cases b <;> ext <;> rfl
theorem images_ih (x : UnitType p n N) (z : Place p) (b : Bool) :
    images x z * IH p n b = channel (takeSign (onSide x b z.1) z.2) := by
  unfold IH; rw [mul_embedMat]
  cases b <;> ext <;> rfl

theorem half_le_table (s : Plan p n) (z) (i) : halfTable s z i ≤ tabSpace s z := by
  cases i
  · exact le_sup_right
  exact le_sup_left

theorem channel_le_table (s : Plan p n) (z i) : colSp (IH p n i)≤tabSpace s z :=
  le_trans le_sup_right (half_le_table s z i)

theorem tab_mem (s : Plan p n) (z : Place p) (x : Dir p n) :
    x∈tabSpace s z ↔ ∀ i,(IP p n i)ᵀ *ᵥ x ∈ sPin s z i := by
  constructor
  · intro h i
    let Q := (sPin s z i).comap (IP p n i)ᵀ.mulVecLin
    suffices he : tabSpace s z ≤ Q from he h
    have hg (j : Bool) : halfTable s z j≤Q := by
      refine sup_le ?_ ?_
      · rintro y ⟨x,hx,rfl⟩
        change (IP p n i)ᵀ *ᵥ (IP p n j *ᵥ x) ∈ sPin s z i
        by_cases e : i = j
        · subst j; rwa [mulVec_mulVec,IP_self,Matrix.one_mulVec]
        rw [mulVec_mulVec,IP_cross e,Matrix.zero_mulVec]; exact Submodule.zero_mem _
      rintro y ⟨x,rfl⟩
      change (IP p n i)ᵀ *ᵥ (IH p n j *ᵥ x) ∈ sPin s z i
      rw [mulVec_mulVec,IP_IH,Matrix.zero_mulVec]; exact Submodule.zero_mem _
    exact sup_le (hg _) (hg _)
  intro h
  rw [←ip_decomp x]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  apply (half_le_table s z i)
  exact Submodule.add_mem_sup (show IP p n i *ᵥ _ ∈ (sPin s z i).map (IP p n i).mulVecLin from
    ⟨_,h i,rfl⟩) (show IH p n i *ᵥ _ ∈ colSp (IH p n i) from ⟨_,rfl⟩)

theorem pin_le_table (s : Plan p n) (z : Place p) : s z ≤ tabSpace s z := fun x h =>
  (tab_mem ..).mpr fun _ => ⟨x,h,rfl⟩

theorem effective_mem {s : Plan p n} {i} {x : Profile p n} : x∈effective s i ↔
    x∈Xspace p n ∧ ∀ e, x e∈box (sPin s (e,true) i) (sPin s (e,false) i) :=
  and_congr Iff.rfl (by simp)

theorem sPin_dim (s : Plan p n) (z : Place p) (i) : dim (sPin s z i)≤dim (s z) :=
  Submodule.finrank_map_le _ _

theorem sPin_sum (s : Plan p n) (b i : Bool) :
    ∑ e : Comp p.g, dim (sPin s (e,b) i) ≤ planRank s := by
  unfold planRank
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum (fun e _ => (sPin_dim _ _ _).trans ?_)
  exact Finset.single_le_sum (fun j _ => Nat.zero_le ((fun b => dim (s (e,b))) j))
    (Finset.mem_univ b)

theorem dim_le_plan (s : Plan p n) (e : Place p) :
    dim (s e) ≤ planRank s := Finset.single_le_sum (fun j _ => Nat.zero_le (dim (s j)))
      (Finset.mem_univ _)

theorem effective_rank {s : Plan p n} {x : Profile p n} {i} (hx : x ∈ effective s i) :
    totalRank x ≤ planRank s := by
  apply le_trans (Finset.sum_le_sum ?_) (sPin_sum s true i)
  intro j _
  exact (Submodule.finrank_mono ((box_mem ..).mp ((effective_mem.mp hx).2 j)).1)

private theorem pi_dim_le {V J : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [Fintype J] (s : J→ Submodule F V) :
    dim (Submodule.pi Set.univ s) ≤ ∑ i, dim (s i) := by
  let T := Submodule.pi Set.univ s
  have h (i : J) (x : T) : x.val i∈ s i := x.property i (Set.mem_univ i)
  let f : T →ₗ[F] (∀ i,s i) := {
    toFun := fun x i => ⟨_,h i x⟩
    map_add' := by intro x y; rfl
    map_smul' := by intro x y; rfl }
  have hf : Function.Injective f := fun x y e => Subtype.ext (funext (fun i =>
    show x.val i=y.val i from congrArg (fun t:s i => t.val) (congr_fun e i)))
  exact (LinearMap.finrank_le_finrank_of_injective hf).trans_eq
    (Module.finrank_pi_fintype _)

theorem effective_dim (s : Plan p n) (i : Bool) :
    dim (effective s i) ≤ (planRank s)^2 := by
  unfold effective
  let p' (e : Comp p.g) := (sPin s (e,true) i)
  let q (e : Comp p.g) := (sPin s (e,false) i)
  refine ((Submodule.finrank_mono (show _ ⊓ _ ≤ Submodule.pi Set.univ (fun e => box (p' e)
    (q e)) from inf_le_right)).trans (pi_dim_le _)).trans ?_
  simp_rw [box_dim]
  calc ∑ i, dim (p' i) * dim (q i) ≤ ∑ i, dim (p' i)* planRank s := Finset.sum_le_sum (fun j _ =>
         Nat.mul_le_mul_left _ ((sPin_dim s _ i).trans (dim_le_plan s _)))
       _ ≤ _ := by rw [← Finset.sum_mul,pow_two]; exact Nat.mul_le_mul_right _ (sPin_sum s true i)

theorem pin_protection (s : Plan p n) (i : Bool) (K q : ℕ)
    (hk : planRank s ≤ K) (hj : (K+1)*q≤p.j+1) :
    ∃ L : Finset (Label p.b),
      L.card ≤ 2*Fintype.card (Comp p.g)*K*q ∧
      ∀ z : Place p, protectedBy p (sPin s z i) q L := by
  classical
  have he z : dim (sPin s z i)≤K := ((sPin_dim s z i).trans (dim_le_plan s z)).trans hk
  choose L hL hP using fun z => protect_labels p (sPin s z i) q
    (le_trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right (he z) 1)) hj)
  refine ⟨Finset.univ.biUnion L, ?_,fun z B v h hq x hx hl =>
    hP z B v h hq x hx (fun ht => hl (Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,ht⟩))⟩
  calc (Finset.univ.biUnion L).card
    _ ≤ _ := Finset.card_biUnion_le
    _ ≤ ∑ z : Place p, K*q := Finset.sum_le_sum
          (fun j _ => (hL j).trans (Nat.mul_le_mul_right _ (he j)))
    _ = _ := by simp [Place] <;> ring

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CrossForms
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cross Forms -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

private theorem ev_gram {I J W : Type} [Fintype I] [Fintype J] [Fintype W]
    (P : Mat W I) (Q : Mat W J) (v : Vec I) (w : Vec J) :
    evmat (Pᵀ*Q) v w = dotProduct (P *ᵥ v) (Q *ᵥ w) := by
  rw [evmat,← Matrix.mulVec_mulVec,dotProduct_transpose_mulVec,dotProduct_comm]

theorem flag_actual {a b : Pin p n N} (x y : UnitType p n N) (h : b.agree y) :
    tableFlag a b (actual p x y) x := by
  intro z v hv w hw
  rw [actual,ev_gram,h _ _ hw]

theorem contract_actual (x y : UnitType p n N) (i j : Bool) :
    contract p (actual p x y) i j = (ufun (onSide y j)) ∘ₗ (Uembed (onSide x i)) := by
  let A := onSide x i
  let B := onSide y j
  have he (z : Place p) : actual p x y z * IH p n j = (images x z)ᵀ *
      channel (takeSign (B z.1) !z.2) := by rw [actual,Matrix.mul_assoc,images_ih]; rfl
  apply LinearMap.ext
  intro w
  change ∑ e : Comp p.g, _ = ∑ e : Comp p.g, _
  refine Finset.sum_congr rfl fun e _ => ?_

  let P := images x (e,true)
  let Q := images x (e,false)
  let Y := channel (B e).2
  let X := channel (B e).1
  have hm : (channelOut p (actual p x y) j (e,true))ᵀ * channelOut p (actual p x y) j (e,false) =
      liftM Pᵀ Qᵀ (Y*Xᵀ) := by
    unfold channelOut
    rw [he,he]
    simp only [transpose_mul,transpose_transpose,liftM_def]
    change (Pᵀ * Y)*(Xᵀ*Q)=_
    simp only [Matrix.mul_assoc]
  change mpair _ _ = mpair (Y*Xᵀ) (liftM (primary (A e).1) (primary (A e).2) (w e))
  rw [hm, ← mpair_liftM P Q,liftM_comp]
  have hP : P * IP p n i = primary (A e).1 := images_ip x (e,true) _
  have hQ : Q * IP p n i = primary (A e).2 := images_ip x (e,false) _
  rw [hP,hQ]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GradientRankBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.momFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gradient Rank Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n : ℕ}

namespace Volley
variable {I : Type} [Fintype I] [DecidableEq I] (v : Volley p n I)

theorem here_card {w : I → Bool} (h : v.bounded w) (i : Bool) : (v.here i).card≤14 := by
  have he : v.here i ⊆ v.shoots w i true ∪ v.shoots w i false :=
    fun j hj => by
      have hi : v.obj j=i := (Finset.mem_filter.mp hj).2
      cases h : w j <;> simp [shoots,hi,h]
  exact le_trans ((Finset.card_le_card he).trans (Finset.card_union_le _ _))
    (Nat.add_le_add (h _ _).2 (h _ _).2)

end Volley
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BaselineForms
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Baseline Forms -/

noncomputable section
namespace HadwigerCounterexample

open scoped BigOperators
open Matrix
variable {p : Shape} {n N : ℕ}

theorem fits_recip {B T : Cross p n} {a b : Plan p n} (h : fitsTable a b B T) :
    fitsTable b a (reciprocal p B) (reciprocal p T) := by
  intro z x hx y hy
  have hx' : x∈tabSpace b (flipZ p (flipZ p z)) := by rwa [flipZ_flip]
  change evmat _ _ _=evmat _ _ _
  unfold reciprocal
  rw [evmat_transpose,evmat_transpose,h _ y hy x hx']

theorem channel_eval (p : Shape) {n} (M : Cross p n) (j : Bool) (z : Place p)
    (x : Dir p n) (y : Vec (Chan p)) :
    dotProduct y (channelOut p M j z *ᵥ x)=evmat (M z) x (IH p n j *ᵥ y) := by
  unfold channelOut evmat
  rw [dotProduct_transpose_mulVec, Matrix.mulVec_mulVec]

theorem channel_same {M T : Cross p n} (i z u)
    (h : ∀ v : Vec (Chan p), evmat (M z) u (IH p n i *ᵥ v)=evmat (T z) u (IH p n i *ᵥ v)) :
    channelOut p M i z *ᵥ u = channelOut p T i z *ᵥ u := by
  classical
  funext j
  have he v : dotProduct v (channelOut p M i z *ᵥ u)=dotProduct v (channelOut p T i z*ᵥ u) := by
    rw [channel_eval, channel_eval, h]
  simpa using he (Pi.single j 1)

theorem fits_channel {M T : Cross p n} {a b : Plan p n} (h : fitsTable a b M T)
    (z : Place p) (x : Dir p n) (hx : x∈tabSpace a z) (j : Bool) :
    channelOut p M j z *ᵥ x = channelOut p T j z *ᵥ x := by
  apply channel_same j
  intro v
  exact h z x hx _ (channel_le_table b _ j ⟨_,rfl⟩)

private theorem cout_ev (A B : Mat (Chan p) (JointIdx p n)) (x y) :
    evmat (Aᵀ*B) x y=dotProduct (A *ᵥ x) (B *ᵥ y) := by
  rw [evmat,← mulVec_mulVec,dotProduct_transpose_mulVec,dotProduct_comm]

theorem fits_contract {M T : Cross p n} {a b : Plan p n} (h : fitsTable a b M T)
    (i j : Bool) (x : Profile p n) (hx : x ∈ effective a i) :
    contract p M i j x=contract p T i j x := by
  change ∑ e : Comp p.g, _ = _
  refine Finset.sum_congr rfl fun e _ => ?_
  apply (box_eval_iff (tabSpace a (e,true)) (tabSpace a (e,false)) _ _).mp ?_ _
  · have hp := lift_mem_box (IP p n i) (IP p n i) ((effective_mem.mp hx).2 e)
    exact box_le (le_trans le_sup_left (half_le_table a _ i))
      (le_trans le_sup_left (half_le_table a _ i)) hp
  intro x hx y hy; rw [cout_ev, cout_ev,fits_channel h _ _ hx,fits_channel h _ _ hy]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ResponseAnnihilators
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Response Annihilators -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset LinearMap Submodule Module
open scoped BigOperators
variable {p : Shape} {n : ℕ}
variable {I : Type} [Fintype I]

theorem dotL_surj (x : Vec I →ₗ[F] F) : ∃ y : Vec I,x=dotL y := by
  classical
  let y (i:I) := x (Pi.single i 1)
  refine ⟨y,LinearMap.ext fun v => ?_⟩
  have he : x v=x (∑ i, Pi.single i (v i)) := by rw [Finset.univ_sum_single]
  rw [he,map_sum]
  change (∑ i,x (Pi.single i (v i)))=∑ i,y i*v i
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show Pi.single i (v i)=v i • (Pi.single i 1 : Vec I) from (by
    funext j
    by_cases h : j = i
    · simp [h]
    simp [Pi.single_eq_of_ne h]),
    map_smul]
  exact mul_comm _ _

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AtomFlavors
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Atom Flavors -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Finset Function
open scoped BigOperators
variable {g r n b : ℕ} {p : Shape}

namespace Flavor

theorem keep_o {f : Flavor g} {x : Tag g} {i j}
    (h : keeps f x (Block.O i j)) : allowed i x := by
  rcases f with (_|_|_) <;> simp [keeps] at h
  · exact h
  exact h.1

end Flavor

theorem lit_allows (f : Flavor g) (x : Tag g) (y : Knobs g n) :
    allows x (lit f x y) :=
  fun _ _ h _ => ite_eq_right (fun g => h (Flavor.keep_o g))

theorem mem_useAtom (p : Shape) {n : ℕ} (x : Tag p.g) (s : Label p.b)
    (f : Flavor p.g) (y : Knobs p.g n) : useAtom p x s f y∈Xspace p n :=
  atom_mem s (lit_allows f x y)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BinaryPrescriptions
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary Prescriptions -/

noncomputable section
namespace HadwigerCounterexample

open scoped BigOperators
open Matrix Finset
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I]

/-- Solve symmetric row sums at one endpoint. Couple via opposite
same-target pmiss/role sum equality. Only the resulting necessary
(common d+f sum) is used as input here. -/
private theorem binary_plan (a b : I→Bool) (i : Bool) (d f : Vec I)
    (h : (∑ j∈aiming a b i true,(d j+f j))=∑ j∈aiming a b i false,(d j+f j))
    (h' : ∀ j,(aiming a b i j).Nonempty) :
    ∃ M : Mat I I, Mᵀ=M ∧ (∀ x,M x x=d x) ∧ ∀ j : Bool,∀ x∈Finset.univ.filter (fun l => a l=i),
      (∑ l∈aiming a b i j,M l x) = d x+(if j=b x then 0 else f x) := by
  classical
  let S := aiming a b i
  let X : Mat I Bool := Matrix.of (fun i j => if i∈S j then 1 else 0)
  let V : Mat I Bool := Matrix.of (fun x j => d x + (if j=b x then 0 else f x))
  let D := Matrix.diagonal d
  let Y := V+D*X
  obtain ⟨L,hL⟩ := mat_left_inv (P:=X) (by
    intro x y he
    funext j
    obtain ⟨v,hv⟩ := h' j
    have ha := (Finset.mem_filter.mp hv).2
    have heq (x) : (X *ᵥ x) v=x j := by
      unfold X Matrix.mulVec dotProduct
      rw [Finset.sum_eq_single j]
      · simp [hv,S]
      · intro k _ hk; simp [S,aiming,ha,hk.symm]
      simp
    rw [← heq x,← heq y,he])
  let B := Xᵀ*Y
  have hg (j k : Bool) : B j k=if j=k then 0 else (∑ l∈S j,(d l+f l)) := by
    have hi {l : I} (hh : l∈S j) : a l=i ∧ b l=j := (Finset.mem_filter.mp hh).2
    have hy {l : I} (hL : l∈S j) :
        Y l k= (if j=k then 0 else d l+f l) := by
      unfold Y V X; rw [Matrix.add_apply,Matrix.of_apply,Matrix.diagonal_mul,Matrix.of_apply]
      by_cases h : j=k
      · subst k
        simp only [(hi hL).2,hL,ite_true, if_true,add_zero,mul_one,char_two]
      have hv : l∉S k := fun hw => h ((hi hL).2.symm.trans (Finset.mem_filter.mp hw).2.2)
      simp [h,Ne.symm h,(hi hL).2,hv]
    have ht (l : I) : X l j*Y l k= if l∈S j then Y l k else 0 := by
      by_cases hv : l∈S j <;> simp [X,hv]
    unfold B; rw [Matrix.mul_apply]
    simp_rw [Matrix.transpose_apply,ht,← Finset.sum_filter]
    rw [show Finset.univ.filter (fun x => x∈S j)=S j from (by simp)]
    by_cases g : j=k
    · rw [ite_eq_left g]
      exact Finset.sum_eq_zero fun l hl => (hy hl).trans (ite_eq_left g)
    rw [ite_eq_right g]
    exact Finset.sum_congr rfl fun l hl => (hy hl).trans (ite_eq_right g)
  have ha (j : Bool) : B j j=0 := by rw [hg,ite_eq_left rfl]
  have hB : Bᵀ=B := by
    ext j k
    rw [Matrix.transpose_apply,hg,hg]
    cases j <;> cases k
    all_goals simp
    · exact h
    exact h.symm
  let W := Lᵀ*B*L
  have hW : Wᵀ=W := by unfold W; simp only [transpose_mul,transpose_transpose,hB,Matrix.mul_assoc]
  have hw (x : I) : W x x=0 := by
    unfold W
    have hf : B false true=B true false := congr_fun (congr_fun hB true) false
    simp only [Matrix.mul_apply,Fintype.sum_bool,Matrix.transpose_apply,ha,mul_zero,zero_add,
      add_zero,hf]
    rw [mul_right_comm (L false x), show L true x * B true false * L false x=
        L false x * L true x * B true false from (by ring),char_two]
  let Z := Y*L+(Y*L)ᵀ + W
  have he : (D+Z)*X=V := by
    have he : (Y*L)ᵀ*X=W*X := by
      unfold W
      have hh : Yᵀ * X=B := by
        have ht : Bᵀ=Yᵀ*X := by unfold B; rw [Matrix.transpose_mul,transpose_transpose]
        rw [← ht,hB]
      rw [Matrix.transpose_mul,Matrix.mul_assoc Lᵀ Yᵀ X,hh,Matrix.mul_assoc _ L X,hL,
        Matrix.mul_one]
    unfold Z
    rw [Matrix.add_mul,Matrix.add_mul,Matrix.add_mul,Matrix.mul_assoc Y L X,hL,
      Matrix.mul_one,he,add_assoc Y,char_two,add_zero]
    unfold Y
    rw [add_left_comm,char_two,add_zero]
  refine ⟨D+Z,?_,?_,fun j x hx => ?_⟩
  · unfold Z D
    simp only [transpose_add,Matrix.diagonal_transpose,transpose_transpose,hW]
    ac_rfl
  · intro x
    unfold D Z
    simp only [Matrix.add_apply,Matrix.diagonal_apply_eq,Matrix.transpose_apply,hw,
      char_two,add_zero]
  let Q := D+Z
  have hq : Qᵀ=Q := by
    unfold Q Z D
    simp only [transpose_add,Matrix.diagonal_transpose,transpose_transpose,hW]
    ac_rfl
  have h1 : (Q * X) x j= _ := congr_fun (congr_fun he x) j
  rw [Matrix.mul_apply] at h1
  have hy : ∑ l∈S j, Q l x =∑ l, Q x l * X l j := by
    conv_rhs => unfold X
    simp only [Matrix.of_apply,mul_ite,mul_one,mul_zero, ←Finset.sum_filter]
    rw [show Finset.univ.filter (fun x => x∈ S j)=S j from (by simp)]
    exact Finset.sum_congr rfl fun l _ => congr_fun (congr_fun hq x) l
  exact hy.trans h1

omit [Fintype I] in
private theorem scripted (p : Shape) (t : Tagging p I) (g : I→I→F)
    (h : 2≤p.g) (hJ : 1 ≤ p.J) :
    ∃ s : Script p I,∀ x y,prescribedB p t s x y=g x y := by
  classical
  have hh (x : I) : ∃ i : Comp p.g,inc i (t x) := by
    have he := card_star (t x)
    have hi : Nonempty (TagStar (t x)) := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨⟨i,h⟩⟩ := hi
    exact ⟨i,h⟩
  choose q hq using hh
  let i0 : Fin p.J := ⟨0,hJ⟩
  let s : Script p I := fun x y i =>
    if i.1=(i0,q x,q y) then if i.2 then g x y else 1 else 0
  refine ⟨s,fun x y => ?_⟩
  unfold prescribedB
  rw [Finset.sum_eq_single i0]
  · rw [Finset.sum_eq_single (q x)]
    · rw [Finset.sum_eq_single (q y)]
      · simp [s,hq]
      · intro i _ hi; simp [s,hi]
      simp
    · intro i _ hi; simp [s,hi]
    simp
  · intro i _ hi; simp [s,hi]
  simp

set_option maxHeartbeats 600000 in
theorem choose_script (p : Shape) (t : Tagging p I) (a b : I→Bool)
    (d : Vec I)
    (f : Vec I)
    (d' : Vec I)
    (h : ∀ i : Bool,(∑ x∈aiming a b i true,(d' x+f x)) =
      ∑ x∈aiming a b i false,(d' x+f x))
    (ha : ∀ i j : Bool, ∑ x∈aiming a b i j,(d x+d' x)=1)
    (hc : ∀ i j : Bool,(aiming a b i j).Nonempty)
    (u : Mat I I) (hu : uᵀ=u)
    (hg : 2≤p.g) (hi : 1≤p.J) :
    ∃ s : Script p I, fulfills p t d f u s a b := by
  classical
  have hh (i j : Bool) :
      (∑ x∈aiming a b i j,(d x+f x))=1+ ∑ x∈aiming a b i j,(d' x+f x) := by
    rw [←ha,← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [add_assoc,←add_assoc (d' x),char_two,zero_add]
  choose M hM hD hA using fun i : Bool => binary_plan a b i d f (by rw [hh,hh,h]) (hc i)
  let F' := Fintype.equivFin I
  let g (x y : I) := if F' x < F' y then M (a x) x y+u x y else 0
  obtain ⟨s,hs⟩ := scripted p t g hg hi
  have hf (x y : I) (h : a x=a y) : prescribedT p t d u s x y=M (a x) x y := by
    unfold prescribedT
    split
    · rename_i he
      subst y
      exact (hD _ _).symm
    rename_i he
    rw [hs x y, hs y x]
    rcases lt_or_gt_of_ne (show F' x ≠ F' y from fun h => he (F'.injective h)) with e|e
    · simp only [g, ite_eq_left e,ite_eq_right (not_lt.mpr e.le),add_zero]
      rw [add_left_comm,char_two,add_zero]
    simp only [g,ite_eq_left e,ite_eq_right (not_lt.mpr e.le),zero_add]
    rw [←h,show u y x=u x y from congr_fun (congr_fun hu x) y,
      show M (a x) y x=M (a x) x y from congr_fun (congr_fun (hM (a x)) x) y]
    rw [add_left_comm,char_two,add_zero]
  refine ⟨s,fun x j => ?_⟩
  let S := aiming a b (a x) j
  have he : ∑ i∈S,prescribedT p t d u s i x=∑ i∈S,M (a x) i x :=
    Finset.sum_congr rfl fun i hi => by
      have hm : a i=a x := (Finset.mem_filter.mp hi).2.1
      rw [hf i x hm,hm]
  rw [he,hA (a x) j x (by simp), ← add_assoc, char_two,zero_add]
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CellPruning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cell Pruning -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Finset
variable {A B I J : Type} [Fintype A] [Fintype B] [Fintype I] [Fintype J]

/-- implication needed only almost surely for finite measures. -/
theorem pr_on_mono {w : Wgt A} (hw : ∀ x,0≤w x) {P Q : A→Prop}
    (h : ∀ x,w x≠0→ P x→ Q x) : pr w P ≤ pr w Q :=
  Finset.sum_le_sum (fun x _ => by
    by_cases he : w x=0
    · simp [he]
    exact mul_le_mul_of_nonneg_left (ind_mono (h x he)) (hw x))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_WalshBounds
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Walsh Bounds -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators

@[simp] theorem wsign_abs (x) : |wsign x|=1 := by rcases bit_cases x with h|h <;> simp [h]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_IndependentPhaseBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent Phase Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {J K : Type} [Fintype J] [Fintype K]

theorem phase_actual (p : Shape) {n N} (x : Orient p n N) :
    uPhase p (hcube p x)=ufun x := by
  apply LinearMap.ext
  intro v
  simp only [uPhase,LinearMap.sum_apply]; rfl

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PhaseAlternativeSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Phase Alternative Support -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N r : ℕ}
variable {A : Type} [Fintype A]

theorem onW_ne {w : Wgt A} {P : A→Prop} {x : A} (h : onW w P x≠0) : P x ∧ w x≠0 := by
  have hh : subW w P x≠0 := fun hx => h (by unfold onW normW; rw [hx,zero_div])
  exact ⟨Classical.byContradiction (fun hx => hh (subW_carried _ _ _ hx)),
    left_ne_zero_of_mul hh⟩

theorem on_law {w : Wgt A} (hw : ∀ x,0 ≤ w x) {P : A→Prop} (hp : 0<pr w P) :
    IsLaw (onW w P) := normW_law (subW_nonneg hw _) hp
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_TesterSummaryMass
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tester Summary Mass -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Finset Function
open scoped BigOperators
variable {p : Shape} {r n : ℕ} {A I : Type} [Fintype A] [Fintype I]
variable [DecidableEq I]

theorem generic_summary (p : Shape) (hg : 3≤p.g) (l : Tag p.g) (q y : F) :
    ∃ v : Digest p.g, v.feasible l Flavor.full ∧ v.sumBit=q ∧ v.diagO=y := by
  classical
  have hi := card_allowed' l
  obtain ⟨i,hi⟩ := show ∃ i,allowed i l from by
    have ht : 0 < Fintype.card {i : Tag p.g // allowed i l} := by omega
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp ht
    exact ⟨x.val,x.property⟩
  let v : Digest p.g := Sum.elim (Pi.single (i,l) y) (fun _ => q-y)
  have hf : v.diagO=y := by
    unfold Digest.diagO; rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single l]
      · simp [v]
      · intro k _ hk; simp [v,hk]
      simp
    · intro k _ hk; simp [v,hk]
    simp
  refine ⟨v,?_,?_,hf⟩
  · rintro (⟨j,t⟩|_) hj
    · have h : (j,t) ≠ (i,l) := by
        rintro hk
        obtain rfl : j=i := congrArg Prod.fst hk
        exact hj hi
      exact Pi.single_eq_of_ne h _
    exact (hj trivial).elim
  unfold Digest.sumBit
  rw [hf]; change y+(q-y)=q
  rw [add_sub_cancel]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_StatusCharts
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Status Charts -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function Module LinearMap Submodule
open scoped BigOperators

namespace StatusAnalysis
variable {p : Shape} {n N : ℕ} {d e : Rates}
theorem sendPair (b : Bool) (x : Grid) :
    (sendId b x,sendId (!b) x)=transit b x := by cases b <;> rfl
theorem transit_inv (b : Bool) (x : Grid) : transit b (transit b x)=x := by cases b <;> rfl

theorem roll_project {u : ℕ} (f : Ax p n u) (g : Pdual p n) (z : Cell u) :
    g (f z)=dotProduct (roll f g) z := by
  let h:=g ∘ₗ f
  obtain ⟨x,hx⟩:=dotL_surj h
  have hi (i:Fin u) :
      roll f g i=x i := by
    change h (Pi.single i 1)=_
    rw [hx]; change dotProduct x (Pi.single i 1)=x i
    simp
  rw [show roll f g=x from funext hi]
  exact LinearMap.congr_fun hx z

variable {q : Format}

set_option maxHeartbeats 600000 in
theorem shooting_range (b : Bool) (v : Volley p n (Messenger q)) (x : Grid)
    (h : v.obj = parcel b) :
    v.shoots (parcel (!b)) (sendId b x) (sendId (!b) x) =
      univ.image (fun i:Fin (q x)=> Sigma.mk x i) := by
  classical
  ext i; unfold Volley.shoots
  rw [h]; rcases i with ⟨j,i⟩
  constructor
  · intro hh
    have he := (mem_filter.mp hh).2
    have ht : transit b j=transit b x := by
      rw [←sendPair,←sendPair]; exact Prod.ext he.1 he.2
    have hh : j=x := by rw [←transit_inv b j,ht,transit_inv]
    subst j; exact mem_image.mpr ⟨i,mem_univ _,rfl⟩
  intro h
  obtain ⟨k,_,hh⟩:= mem_image.mp h
  rw [← hh]; exact mem_filter.mpr ⟨mem_univ _,rfl,rfl⟩

variable {H : Type} [AddCommMonoid H]
theorem sum_shots (b : Bool) (v : Volley p n (Messenger q)) (x : Grid)
    (h : v.obj=parcel b) (u : Messenger q→ H) :
    (∑ j∈v.shoots (parcel (!b)) (sendId b x) (sendId (!b) x),u j) =
      ∑ i:Fin (q x),u ⟨x,i⟩ := by
  classical
  rw [shooting_range b _ _ h,Finset.sum_image]
  exact (fun x hx y hy e=> Sigma.mk.inj_iff.mp e |>.2 |> eq_of_heq)

theorem shots_ok {q : Format} (b : Bool) (v : Volley p n (Messenger q))
    (h : v.obj=parcel b) (hh : ∀ i,1≤q i∧q i≤7) :
    v.bounded (parcel (!b)) := by
  intro x y
  let i:= transit b (x,y)
  have he : sendId b i=x := congrArg Prod.fst ((sendPair b i).trans (transit_inv b _))
  have hg : sendId (!b) i=y := congrArg Prod.snd ((sendPair b i).trans (transit_inv b _))
  have ht : (v.shoots (parcel (!b)) x y).card = q i := by
    rw [←he,←hg,shooting_range b v i h, card_image_of_injective,card_univ,Fintype.card_fin]
    exact fun i j he=> Sigma.mk.inj_iff.mp he |>.2 |> eq_of_heq
  change 1≤_∧_≤7; rw [ht]
  exact hh i
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ExplicitStatusEquations
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit Status Equations -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Finset Function
open scoped BigOperators
namespace StatusAnalysis
variable {d e : Rates} {p : Shape} {n N : ℕ} {q : Format}

set_option maxHeartbeats 600000 in
theorem speak_val (u : ∀ i,Suite d e i) :
    speak d e u = ((fun i=>want _ _ (u i)),
      (fun j:Bool=> ∑ i:Bool,couple _ (u (i,j)).2.1),
      (fun i:Bool=> ∑ j:Bool,couple _ (u (i,j)).2.2)) := by
  unfold speak; rw [LinearMap.sum_apply]
  apply Prod.ext
  · rw [Prod.fst_sum]
    exact Finset.univ_sum_single (fun i=>want _ _ (u i))
  apply Prod.ext
  · rw [Prod.snd_sum,Prod.fst_sum]
    funext i
    rw [Finset.sum_apply]
    change (∑ j:Grid,(Pi.single j.2 (couple _ (u j).2.1) : Quota) i)=_
    rw [Fintype.sum_prod_type]; cases i <;> simp [Nodes,Pi.single_apply]
  rw [Prod.snd_sum,Prod.snd_sum]
  funext i
  rw [Finset.sum_apply]
  change (∑ j:Grid,(Pi.single j.1 (couple _ (u j).2.2) : Quota) i)=_
  rw [Fintype.sum_prod_type]; cases i <;> simp [Nodes,Pi.single_apply]

theorem sendSum_by (u : Messenger q → F) (a : Amounts p q d true) (b : Amounts p q e false)
    (i : Grid) :
    sendSum u a b i=(fullq u i, (funds a i : Whole (d i.1)), (funds b i : Whole (e i.2))) := by
  unfold sendSum
  apply Prod.ext
  · rw [Prod.fst_sum]; rfl
  apply Prod.ext
  · rw [Prod.snd_sum,Prod.fst_sum]; rfl
  rw [Prod.snd_sum,Prod.snd_sum]; rfl

set_option maxHeartbeats 800000 in
theorem spoken (v : Charts p n d) (w : Charts p n e) (M : Cross p n) (z : Messenger q→ F)
    (a : Amounts p q d true) (b : Amounts p q e false) :
    speak _ _ (sendSum z a b)=(hailing p v w M,0) ↔
      (∀ i,fullq z i=1)∧rhyme a b∧ still true a v M∧ still false b w (reciprocal p M) := by
  classical
  let f i:=funds a i; let g i:= funds b i
  let h1 i := couple (d (sendId true i)) (f i)
  let h2 i := couple (e (sendId false i)) (g i)
  rw [speak_val]
  simp_rw [sendSum_by]
  have h (x y:F) : x+y=0↔ x=y := by rw [← ZModModule.sub_eq_add,sub_eq_zero]
  constructor
  · intro ht
    have hh := congrArg Prod.fst ht
    have hx := congrArg Prod.fst (congrArg Prod.snd ht)
    have hy := congrArg Prod.snd (congrArg Prod.snd ht)
    refine ⟨fun i=>congrArg Prod.fst (congr_fun hh i),fun i=>congrArg (fun x=>x.2.1)
      (congr_fun hh i),⟨fun i=>congrArg (fun x=>x.2.2.1) (congr_fun hh i),fun i=>?_⟩,
      fun i=>congrArg (fun x=>x.2.2.2) (congr_fun hh i),fun i=>?_⟩
    · have ht:=congr_fun hx i
      change ∑ j:Bool,h1 (j,i)=0 at ht; rw [Fintype.sum_bool,h] at ht; exact ht
    have ht:=congr_fun hy i; change ∑ j:Bool,h2 (i,j)=0 at ht; rw [Fintype.sum_bool,h] at ht
    exact ht
  rintro ⟨ht,hv,⟨hF,hA⟩,hG,hB⟩
  apply Prod.ext
  · funext i; exact Prod.ext (ht i) (Prod.ext (hv i) (Prod.ext (hF i) (hG i)))
  apply Prod.ext
  · funext i; change ∑ j:Bool,h1 (j,i)=0
    rw [Fintype.sum_bool,h]; exact hA i
  funext i; change ∑ j:Bool,h2 (i,j)=0
  rw [Fintype.sum_bool,h]; exact hB i
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_NumericalGradientTests
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical Gradient Tests -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function Submodule
open scoped BigOperators
namespace StatusAnalysis
variable {p : Shape} {n N : ℕ} {q : Format} {d e : Rates}

theorem aim_sum {H : Type} [AddCommMonoid H] (b : Bool) (x : Grid) (u : Messenger q→H) :
    ∑ j∈aiming (parcel b) (parcel (!b)) (sendId b x) (sendId (!b) x),u j=∑ i:Fin (q x),u ⟨x,i⟩ := by
  let p : Shape := ⟨0,0,0,0,0,0⟩
  let v : Volley p 0 (Messenger q) := ⟨parcel b,fun _ =>0,fun _=>0⟩
  exact sum_shots b v x rfl _
theorem tmill_sym {b} (t : Tagging p (Messenger q)) (w : Amounts p q d b) :
    (TMill p t w)ᵀ=TMill p t w := by
  classical
  ext i j
  unfold TMill; simp only [transpose_apply,Matrix.of_apply]; congr 1
  · ring
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem funds_roles {b} (a : Amounts p q d b) (i : Grid) :
    (funds a i).1.1=∑ x : Fin (q i), mailRole a ⟨i,x⟩ := by
  let entries : Fin (q i) → Whole (d (sendId b i)) := fun k => (a ⟨i,k⟩).2
  change (∑ k, entries k).1.1 = _
  rw [Prod.fst_sum,Prod.fst_sum]
  rfl
theorem funds_duos {b} (a : Amounts p q d b) (i : Grid) :
    couple _ (funds a i)=
      ∑ x: Fin (q i), (mailRole a ⟨i,x⟩+mailBias a ⟨i,x⟩) := by
  let entries : Fin (q i) → Whole (d (sendId b i)) := fun k => (a ⟨i,k⟩).2
  change couple _ (∑ k, entries k) = _
  rw [map_sum]
  rfl

set_option maxHeartbeats 800000 in
theorem proclaim_script (b : Bool) (a : Amounts p q d b) (w : Amounts p q e (!b)) (t : Tagging p
    (Messenger q))
    (v : Charts p n e) (M : Cross p n)
    (h : rhyme a w) (hb : ∀ i,1≤ q i)
    (hr : still (!b) w v M)
    (hg : 2≤p.g) (hj : 1≤p.J) : ∃ s, proclaims p a w t s := by
  have ha {H : Type} [AddCommMonoid H] (a e : Nodes) (f : Messenger q→ H) :
      ∑ x∈aiming (parcel b) (parcel (!b)) a e, f x=∑ i:Fin (q (transit b (a,e))),f
        ⟨transit b (a,e),i⟩ := by
    have hA := aim_sum b (transit b (a,e)) f
    have he := (sendPair b (transit b (a,e))).trans (transit_inv b _)
    rw [show sendId b _ = a from congrArg Prod.fst he,
      show sendId (!b) _=e from congrArg Prod.snd he] at hA
    exact hA
  apply choose_script p t _ _ _ _ (mailRole w) _ _ _ _ (tmill_sym ..) hg hj
  · intro i
    rw [ha,ha,←funds_duos w,←funds_duos w]
    have hx:=hr.2 i; cases b <;> exact hx
  · intro i j; rw [ha,sum_add_distrib,←funds_roles a, ←funds_roles w]
    exact h _
  intro i j
  let k:=transit b (i,j)
  let x : Messenger q:=⟨k,0,(hb k)⟩
  have he := (sendPair b k).trans (transit_inv b (i,j))
  exact ⟨x,Finset.mem_filter.mpr ⟨mem_univ _,congrArg Prod.fst he,congrArg Prod.snd he⟩⟩

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteTableEnumeration
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Table Enumeration -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset LinearMap Submodule Module Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
namespace StatusAnalysis

theorem fits_flag (M T : Cross p n) (a b : Pin p n N) (x : UnitType p n N)
    (hf : fitsTable a.sp b.sp M T) (h : tableFlag a b T x) : tableFlag a b M x :=
  fun i j hj k hk=> (hf i j hj k (pin_le_table b.sp _ hk)).trans (h i j hj k hk)
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PhaseClassCompatibility
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Phase Class Compatibility -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset LinearMap
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

open PredictionClass

theorem lone (p : Shape) {n N} (x : UnitType p n N) (i : Bool) (v : Ambient p N) :
    tone p x (unary i) v= ufun (onSide x i) v := by
  classical
  unfold tone joinPhase unary; rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same,one_smul]
    rw [show onSide (listens p x) i=hcube p (onSide x i) from by cases i<;>rfl, phase_actual]
  · intro j _ h; simp [h]
  simp

theorem exactInner (m : Mixer p n) (z : BMark p n N) (x : UnitType p n N)
    (h : exactInk p m z x) :
    ∀ i, ∀ v∈Xspace p n,innerP p x i v = grad m (z x i) v := by
  intro i v hv
  have he := h i v hv
  change innerP p x i v+(Tsym m (z x i) v +1*role p n v)=0 at he
  rw [one_mul,add_comm (Tsym m (z x i) v),← grad_val] at he
  exact add_right_cancel (he.trans (char_two _).symm)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_LeafMixtures
attribute [-instance] _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Leaf Mixtures -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset LinearMap Filter
open scoped BigOperators
variable {p : Shape} {n N M : ℕ}

namespace LeafMixture

theorem poller_eq (s : LeafMixture p n N) (h : apart s.T) {x i} (hi : i∈s.T) (hx : x∈i) :
    s.poller x=s.pin i := by
  classical
  have hc : inTiles s.T x := ⟨_,hi,hx⟩
  unfold poller; rw [dite_eq_left hc,h _ _ hc.choose_spec.1 _ hi hc.choose_spec.2 hx]

end LeafMixture
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CompatibleOptionRealization
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatible Option Realization -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function Module LinearMap
open scoped BigOperators
variable {p:Shape} {n N M K s0:ℕ}
namespace StatusAnalysis

variable {q:Format} {d e: Rates} {b:Bool}
theorem buildBooths (K:ℕ) (s:Plan p n) (h:planRank s≤K)
    (hj:(K+1)*qorth K≤p.j+1) :
    ∃ H,booths p K s H := by
  classical
  choose H hH hG using fun i : Bool=> pin_protection s i K (qorth K) h hj
  exact ⟨H,hH,hG⟩

theorem shelter (K :ℕ) (S:Pin p n N) (t : Quill p q d b) (z : Tagging p (Messenger q)) (H:Stalls p)
    (h:booths p K S.sp H) (hp : Injective t.sel)
    (ht:∀ i:Messenger q,t.sel i∉H (parcel b i))
    (hg : ∀ i,1≤q i ∧ q i≤7) : t.penSpace z S K := by
  intro x i
  let v:=(t.pen z).draw x
  refine ⟨H i,h.2 i,fun j hj=>?_,?_,hp.injOn⟩
  · have he : parcel b j=i := Finset.mem_filter.mp hj|>.2
    rw [←he]; exact ht j
  exact (Volley.here_card v (shots_ok b v rfl hg) i).trans (by unfold qorth; omega)

theorem sizedCharts (K:ℕ) (w:LeafMixture p n N) (t:Station p n N K w) (ht:t.bank)
    (i:w.T) (h:planRank (w.pin i.val).sp≤K) :
    ∃ d:Stakes K,charted (t.cAxes i (toRates d)) (w.pin i.val).sp := by
  let s:=(w.pin i.val).sp
  let d (i:Nodes):= dim (effective s i)
  have hd i : d i < K^2+1 := Nat.lt_of_le_of_lt
    ((effective_dim s i).trans (by gcongr)) (Nat.lt_succ_self _)
  exact ⟨fun i=>⟨d i,hd i⟩,ht.1 i⟩

variable {i j:Bool} {L:ℕ}
set_option maxHeartbeats 1200000 in
theorem optionVia (q:Format) (d e : Rates) (s t:Pin p n N) (T:Cross p n) (K:ℕ)
    (ha: tableInj s.sp t.sp T) (hb : tableInj t.sp s.sp (reciprocal p T))
    (p':Tagging p (Messenger q)) (x:Charts p n d) (y:Charts p n e)
    (hx:charted x s.sp) (hy:charted y t.sp)
    (f:Fabric p q d true) (g:Fabric p q e false)
    (hs h:Stalls p) (hm:booths p K s.sp hs) (hu : booths p K t.sp h)
    (hf:∀ i,f.sel i∉ hs (parcel true i)) (hg:∀ i,g.sel i∉ h (parcel false i))
    (z:Messenger q→F) (hF:f.up p' z)(hG:g.up p' z)
    (hj : 1≤p.J) (h2: 2≤p.g) (h₀:∀ i,1≤q i∧q i≤7)
    (he:speak _ _ (sendSum z f.amp g.amp)=(hailing p x y T,0)) :
    ∃ (a b:Script p (Messenger q)),Typus.chances ⟨p',z,f.hang a,g.hang b⟩ x y s t T K := by
  obtain ⟨hQ,hR,hL,hS⟩:= (spoken x y T z f.amp g.amp).mp he
  obtain ⟨a,ha'⟩:= proclaim_script true f.amp g.amp p' y (reciprocal p T) hR (fun i=>(h₀ i).1)
    hS h2 hj
  have hh : rhyme g.amp f.amp := fun i=> (add_comm ..).trans (hR i)
  obtain ⟨b,hb'⟩:= proclaim_script false g.amp f.amp p' x T hh (fun i=>(h₀ i).1)
    hL h2 hj
  exact ⟨a,b, ⟨h₀,hF,hG,hQ,hR,ha',hb'⟩,⟨hx,shelter K s (f.hang a) p' hs hm hF.1 hf h₀,hL,ha⟩,
    ⟨hy,shelter K t (g.hang b) p' h hu hG.1 hg h₀,hS,hb⟩⟩

theorem berth_flags (a b:Pin p n N) (T:Cross p n) {x:UnitType p n N × UnitType p n N}
    (h:berthTicket a b T x) (ha:a.agree x.1) (hb:b.agree x.2) :
    tableFlag a b T x.1 ∧ tableFlag b a (reciprocal p T) x.2 := by
  have hg:=fits_recip h.2.2; rw [reciprocal_actual] at hg
  exact ⟨fits_flag T _ a b x.1 h.2.2 (flag_actual _ _ hb),
         fits_flag _ _ b a x.2 hg (flag_actual _ _ ha)⟩

theorem actualTone (m:BMark p n N) (a b : UnitType p n N) (j:Bool) :
    cardTone m a (actual p a b) j = tone p b (unary j) (delta m a) := by
  rw [lone]
  unfold cardTone delta
  rw [map_add,Fintype.sum_bool]
  simp_rw [contract_actual]; rfl
theorem fitsTone {w v: Plan p n} {T U:Cross p n}
    (m:BMark p n N) (x:UnitType p n N)
    (h:fitsTable w v T U) (hx:∀ i,m x i∈effective w i) (j) :
    cardTone m x T j=cardTone m x U j :=
    Finset.sum_congr rfl (fun i _=>fits_contract h i j _ (hx i))
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RareTestEvents
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rare Test Events -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix LinearMap Module Function
open scoped BigOperators Topology
variable {p:Shape} {n N K M : ℕ}
namespace StatusAnalysis

theorem singles_card : Fintype.card (Messenger singles)=4 := by
  decide
theorem singles_short : ∀ i,1 ≤ singles i ∧ singles i≤7 :=by simp [singles]
theorem funds_one {b : Bool} {d : Rates} (f: Fabric p singles d b) (i:Grid) :
    funds f.amp i=(f.amp ⟨i,(0:Fin 1)⟩).2 := by
  unfold funds
  let : Unique (Fin (singles i)) := (show Unique (Fin 1) from inferInstance)
  exact Fintype.sum_unique _

theorem fourPens (s:Plan p n) (K:ℕ) (H : Stalls p) (h:booths p K s H)
    (ht : 2*frameBills p.g K+4 ≤Fintype.card (Label p.b)) :
    ∃ z:Messenger singles→Label p.b, Injective z ∧ ∀ i j, z i∉ H j := by
  classical
  let F:=H true ∪ H false; let T:=Fᶜ
  have hp : F.card≤ 2* frameBills p.g K :=
    (Finset.card_union_le _ _).trans ((add_le_add (h.1 _) (h.1 _)).trans_eq (two_mul _).symm)
  have he : Fintype.card (Messenger singles) ≤ Fintype.card (↑T:Type) := by
    rw [Fintype.card_coe,singles_card]; unfold T; rw [Finset.card_compl]; omega
  obtain ⟨i,hi⟩: ∃ i : Messenger singles → ↑T,Injective i := by

    obtain ⟨g⟩:=Function.Embedding.nonempty_of_card_le he
    exact ⟨g,g.injective⟩
  refine ⟨fun x=>(i x).val,Subtype.val_injective.comp hi,fun x b=>?_⟩
  have hh:(i x).val∉F:=Finset.mem_compl.mp (i x).property
  intro hx; cases b
  · exact hh (Finset.mem_union_right _ hx)
  exact hh (Finset.mem_union_left _ hx)

variable {d:Rates}

set_option maxHeartbeats 800000 in
theorem stillBeacon (m:BMark p n N) (o:UnitType p n N) (s:Charts p n d)
    (w:∀ i:Nodes,Cell (d i)) (b:Bool) (T:Cross p n) (z:Digest p.g)
    (h:coordSpec m o s w) (hT:∀ i,cardTone m o T i= glint p (m o)) :
    still b (beacon p s w b T z) s T := by
  classical
  let f:Amounts p singles d b:= beacon p s w b T z
  have hf (i): funds f i=(f ⟨i,(0:Fin 1)⟩).2 := by
    unfold funds; let : Unique (Fin (singles i)) := (show Unique (Fin 1) from inferInstance); exact Fintype.sum_unique _
  change (∀ i, _ ) ∧ _
  constructor
  · intro i
    change (funds f i).1.2=_
    rw [hf]
    rfl
  intro i
  have hh t q : couple _ (funds f (transit b (t,q))) =
      contract p T t q (m o t)+role p n (m o t) := by
    rw [hf]
    let k : Messenger singles:=⟨transit b (t,q),(0:Fin 1)⟩
    let a:= targetMark p s T (parcel b k) (parcel (!b) k)
    change z.diagO+(z.diagO+dotProduct a (w _))=_
    rw [← add_assoc,char_two,zero_add]; unfold a targetMark
    rw [← roll_project]
    have he (i t): (contract p T i t+role p n) (s i (w i))=contract p T i t (m o i)+role p n (m o i) :=
      by rw [h]; rfl
    rw [he]; cases b <;> rfl
  change couple _ (funds f _) = couple _ (funds f _)
  simp_rw [hh]
  have ht:= hT i
  unfold glint cardTone at ht; rw [Fintype.sum_bool,Fintype.sum_bool] at ht
  apply sub_eq_zero.mp
  rw [ZModModule.sub_eq_add]
  rw [add_add_add_comm,ht,char_two]

set_option maxHeartbeats 700000 in
theorem steadyBeacon {plan : Plan p n} (m:BMark p n N) (o:UnitType p n N) (s:Charts p n d)
    (w:∀ i:Nodes,Cell (d i)) (b:Bool) (T:Cross p n)
    (q:Quill p singles d b) (t:Tagging p (Messenger singles))
    (g: Mixer p n) (z:Digest p.g) (K:ℕ)
    (hd:∀ i,d i≤K^2)
    (ha:q.amp=beacon p s w b T z)
    (hk:planRank plan≤K)
    (hs:charted s plan)
    (h:coordSpec m o s w)
    (hF : PreparationParameters.frameSide p g o)
    (hg : exactInk p g m o) :
    q.steady t (fun _=>1) g K s o := by
  classical
  refine ⟨hF,fun i=> ⟨hd _,(hs _).2,fun y=>?_⟩,fun i=>by rw [ha];rfl, fun i v hv => ?_⟩
  · refine (effective_rank (i:=parcel b i) ?_).trans hk
    rw [← (hs _).1]; exact mem_range_self _ _
  · let l:= q.allure t (fun _=>1) i; let j:=parcel b i
    let V:= l.profile j o g (s j) v
    have ht : V.1 = (q.amp i).1 ∧ V.2.1=(q.amp i).2.1 → V=q.amp i := by
      rintro ⟨h1,h2⟩
      apply Prod.ext h1 (Prod.ext h2 _)
      rw [ha] at h2 ⊢
      let a:= useAtom p l.l l.s l.f v
      let k:=targetMark p s T j (parcel (!b) i)
      have heq : V.2.2 = z.diagO + dotProduct k (w j) := by
        have he := exactInner g m o hg j a
        have hx : a∈Xspace p n:= mem_useAtom ..
        have hg' : role p n a=z.diagO := congrArg Prod.fst h2
        have hk : roll (s j) (Tsym g a)=k := congrArg Prod.snd h2
        change innerP p o j a=_
        rw [he hx, grad_val,hg',T_swap, ←h,roll_project,hk]
      exact heq
    exact (hv ht).elim

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CompatibleTableEvents
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatible Table Events -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix LinearMap Function
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
open PreparationParameters PredictionClass

variable {p:Shape} {n M K s0 N :ℕ} {w:LeafMixture p n N} {q:PreparationParameters}

variable (v: Station p n N q.pins w) (i j:w.T)
    (U:Wgt (UnitType p n N)) (m:Mixer p n) (z:BMark p n N)

private theorem chartKnown {r : F} (q:PreparationParameters) (x:w.T) (d: Stakes q.pins)
    (hw:Settled w m q U z r)
    {v : Charts p n (toRates d)} (hc:charted v (w.pin x.val).sp)
    (o : UnitType p n N) (hx:o∈x.val) :
    (∀ i,totalRank (z o i)≤ q.pins) ∧ ∃ y,∀ i∈x.val,coordSpec z i v y := by
  obtain ⟨h1,h2,h3⟩:=hw.readyC
  let A:=(w.pin x.val).sp
  have hi j : z o j∈effective A j := by
    have hh : w.rooting o=A:=congrArg Pin.sp (LeafMixture.poller_eq w h2.part x.property hx)
    rw [←hh]; exact (h3 x.val x.property o hx).2.2.1 j
  obtain ⟨T,hK,hB,hG⟩:=hw.hard
  obtain ⟨b,hb,hf⟩:=hG x.val x.property
  choose y hy using fun j=> show z o j∈LinearMap.range (v j) from (hc j).1.symm ▸ hi j
  refine ⟨fun i=>(effective_rank (hi i)).trans (h2.leaf x.val x.property).bound,y,
    fun i hh j=>?_⟩
  exact (hy j).trans (congr_fun (hb.2.2 _ hx _ hh).1 j)

set_option maxHeartbeats 1800000 in
theorem invoke_oai (k:Fin (2^deckMax p q.pins))
    (r:F) (a:ℝ) (hα:0<a) (h:AnalyticParameters p M q s0)
    (hw:Settled w m q U z r) (ht:v.bank)
    (hk:2*a ≤ pr (pairW (partW U i.val) (partW U j.val))
       (fun x=> shimmer z r x∧ berthTicket (w.pin i.val) (w.pin j.val) (v.mails i j k) x)) :
    ∃ x:Scrip p q.pins, v.charter x.2.2 m x.2.1 U a (i,j) := by
  classical
  let K:=q.pins
  let T:=v.mails i j k
  have hq:=h.enter.first
  let a0:= w.pin i.val; let b0:= w.pin j.val
  let μ i:=partW U (Subtype.val (show w.T from i))
  let S:=pairW (μ i) (μ j)
  obtain ⟨hm,hv,hC⟩:=hw.readyC
  have hu x:=show IsLaw (μ x) from on_law hm.nz (hv.leaf x.val x.property).pos
  have hμ: IsLaw S:= pairW_law (hu _) (hu _)
  have hK x : planRank (w.pin (Subtype.val (show w.T from x))).sp ≤ K :=
    (hv.leaf _ (Subtype.prop x)).bound
  obtain ⟨f,hF⟩:=sizedCharts q.pins w v ht i (hK i)
  obtain ⟨g,hG⟩:=sizedCharts q.pins w v ht j (hK j)
  let A:= toRates f; let B:=toRates g; let X:=v.cAxes i A; let Y:=v.cAxes j B
  let P x:= shimmer z r x∧ berthTicket a0 b0 T x
  obtain ⟨o,⟨hop,hOK⟩,ho⟩:= exists_of_pr_pos hμ.nz (lt_of_lt_of_le
    (show 0<2*a by positivity) hk)
  let x:=o.1; let y:=o.2
  have hcol i x (hx:μ i x≠0) : x∈ i.val := (onW_ne hx).1
  have hx : x∈ i.val:= hcol i x (left_ne_zero_of_mul ho.ne')
  have hy : y∈ j.val:= hcol j y (right_ne_zero_of_mul ho.ne')
  obtain ⟨hχ,l,hl⟩:= chartKnown (v:=X) U m z q i f hw hF x hx
  obtain ⟨hξ,t,ht'⟩:= chartKnown (v:=Y) U m z q j g hw hG y hy
  have he (i : w.T) x (hx:x∈ i.val) : ∀ j,z x j∈effective (w.pin i.val).sp j := by
    have hi : w.rooting x=(w.pin i.val).sp:=congrArg Pin.sp (LeafMixture.poller_eq w hv.part i.property hx)
    rw [← hi]; exact (hC _ i.property _ hx).2.2.1
  let kappa : Tag p.g:= ⟨0,by linarith only [hq.hG]⟩
  let tt : Tagging p (Messenger singles):=fun _=>kappa
  let ref := show Messenger singles→F from fun _=>1
  obtain ⟨E,h1,h2,h3⟩:= generic_summary p hq.hG kappa 1 0
  obtain ⟨H,h4,h5,h6⟩:= generic_summary p hq.hG kappa 1 1
  obtain ⟨L,hLa⟩:= buildBooths K a0.sp (hK i) h.penRoom
  obtain ⟨O,hLb⟩:= buildBooths K b0.sp (hK j) h.penRoom
  have hh : 2*frameBills p.g K+4 ≤ Fintype.card (Label p.b) := by
    have hl : frameBills p.g K + 1000 ≤ q.B:=h.forbid
    have he:= h.spare; omega
  obtain ⟨J,hJ,hJ'⟩:= fourPens _ K L hLa hh
  obtain ⟨I,hI,hI'⟩:= fourPens _ K O hLb hh
  let F0:Fabric p singles A true:=⟨J,fun _ => Flavor.full,beacon p X l true T E⟩
  let T':= reciprocal p T
  let G0:Fabric p singles B false:=⟨I,fun _=> Flavor.full,beacon p Y t false T' H⟩
  have hs : speak A B (sendSum ref F0.amp G0.amp)=(hailing p X Y T,0) := by
    apply (spoken X Y T ref F0.amp G0.amp).mpr
    have hFq a : fullq ref a=1 := by
      unfold fullq
      change (∑ _:Fin 1,(1:F))=1; rw [Fintype.sum_unique]
    have hR : rhyme F0.amp G0.amp := by
      intro i; have hf : (funds F0.amp i).1.1=E.diagO := congrArg (fun x=> x.1.1) (funds_one F0 i)
      have hg : (funds G0.amp i).1.1=H.diagO := congrArg (fun x=> x.1.1) (funds_one G0 i)
      change (funds (b:=true) F0.amp i).1.1+(funds (b:=false) G0.amp i).1.1=_; rw [hf,hg,h3,h6,zero_add]
    refine ⟨hFq,hR, stillBeacon z x X l true T E (hl _ hx) (fun k=>?_),stillBeacon z y Y t false
      T' H (ht' _ hy) (fun k=>?_)⟩
    · rw [fitsTone z x hOK.2.2 (he _ _ hx), actualTone,(hC _ i.property _ hx).2.2.2]
      exact congr_fun (congrArg Prod.fst hop) k
    have hg:=fits_recip hOK.2.2; rw [reciprocal_actual] at hg
    rw [fitsTone z y hg (he _ _ hy), actualTone,(hC _ j.property _ hy).2.2.2]
    exact congr_fun (congrArg Prod.snd hop) k
  obtain ⟨P0,Q0,hf⟩:= optionVia singles A B a0 b0 T K hOK.1 hOK.2.1 tt X Y hF hG F0 G0 L O hLa hLb
    (fun i=>hJ' i _) (fun i=> hI' i _) ref ⟨hJ,fun i=>h2,fun i=>h1⟩
    ⟨hI,fun i=>h5,fun i=>h4⟩ h.jump (by linarith only [hq.hG]) singles_short hs
  let τ:Typus p singles A B:= ⟨tt,ref,F0.hang P0,G0.hang Q0⟩
  let Front:=v.frontPage τ m i j k; let Back:=v.backPage τ m i j k
  have hi a (ha:a∈ i.val): a0.agree a := (hv.leaf _ i.property).fixpin _ ha
  have hi' a (ha:a∈ j.val): b0.agree a := (hv.leaf _ j.property).fixpin _ ha
  have hm : 2*a≤ (pr (μ i) Front)*(pr (μ j) Back) := by
    rw [←pairW_pr]
    apply hk.trans
    refine pr_on_mono hμ.nz (fun x hx he=>?_)
    have h1 := hcol i x.1 (left_ne_zero_of_mul hx)
    have h2 := hcol j x.2 (right_ne_zero_of_mul hx)
    obtain ⟨ha,hb⟩:= berth_flags a0 b0 T he.2 (hi _ h1) (hi' _ h2)
    exact ⟨⟨hf,hi _ h1,(hC _ i.property x.1 h1).1, ha⟩,
      ⟨hf,hi' _ h2,(hC _ j.property _ h2).1,hb⟩⟩
  refine ⟨⟨(volume1,f,g),k,show OnFile p _ from τ⟩,hf.1,⟨?_,fun o ho hx=>?_⟩,
    ⟨?_,fun o ho hx=>?_⟩⟩
  · exact hm.trans ((mul_le_mul_of_nonneg_left ((pr_le_tot (hu _).nz).trans (hu j).total.le)
      (pr_nonneg (hu _).nz)).trans_eq (mul_one _))
  · have hv := hcol i o hx
    exact steadyBeacon z o X l true T τ.qA tt m E K
      (fun x=> Nat.lt_succ_iff.mp (f x).isLt) rfl (hK i) hF (hl _ hv) ho.2.2.1
      (hC _ i.property _ hv).2.1
  · exact hm.trans ((mul_le_mul_of_nonneg_right ((pr_le_tot (hu _).nz).trans (hu i).total.le)
      (pr_nonneg (hu _).nz)).trans_eq (one_mul _))
  have hv:=hcol j o hx
  exact steadyBeacon z o Y t false T' τ.qB tt m H K
    (fun x=> Nat.lt_succ_iff.mp (g x).isLt) rfl (hK j) hG (ht' _ hv) ho.2.2.1
    (hC _ j.property _ hv).2.1

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

theorem solution : type_of% @OAI.HadwigerCounterexample.StatusAnalysis.invoke_oai := @OAI.HadwigerCounterexample.StatusAnalysis.invoke_oai
