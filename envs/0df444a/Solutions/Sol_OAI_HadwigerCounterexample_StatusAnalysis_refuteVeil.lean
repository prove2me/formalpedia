-- Prove2me | solution 1 for OAI.HadwigerCounterexample.StatusAnalysis.refuteVeil
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T23:07:23.833526+00:00
-- url     : https://prove2.me/submissions/8e6fbfbf-13be-419b-96be-efa7ce2f3bd2

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
import Theorems.Thm_OAI_HadwigerCounterexample_StatusAnalysis_dim_end
import Theorems.Thm_OAI_HadwigerCounterexample_StatusAnalysis_lightmap

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
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
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

theorem rk_surj {f : V →ₗ[F] W} [FiniteDimensional F W] : Surjective f ↔ rk f = dim W := by
  rw [← range_eq_top]
  constructor
  · intro h; unfold rk dim; rw [h]; exact finrank_top _ _
  exact Submodule.eq_top_of_finrank_eq

theorem rk_inj {f : V →ₗ[F] W} [FiniteDimensional F V] : Injective f ↔ rk f = dim V := by
  constructor
  · exact LinearMap.finrank_range_of_inj
  intro h
  rw [← ker_eq_bot, ← Submodule.finrank_eq_zero (R:=F)]
  have hj := f.finrank_range_add_finrank_ker
  dsimp only [rk,dim] at h
  omega

end Generic

variable {I J K : Type}
variable [Fintype I] [Fintype J]

theorem dim_vec (K : Type) [Fintype K] : dim (Vec K) = Fintype.card K :=
  Module.finrank_pi F

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

theorem not_allowed (d : Tag g) : ¬allowed d d := by
  have : NeZero g := ⟨by have := d.isLt; omega⟩
  simp [allowed]

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MomentCoordinates
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Moment Coordinates -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Finset

variable (p : Shape)
variable {n : ℕ}

variable {p}

theorem getPair_edge (l d : Tag p.g) (h : l ≠ d) (x : Profile p n) :
    getPair p n l d x = x (edge l d h) := by rw [getPair,dite_eq_left h]; rfl

theorem getPair_cut (w : Tag p.g → Moment p n) (l d : Tag p.g) :
    getPair p n l d (cut p n w) = w l + w d := by
  by_cases h : l = d
  · subst l; rw [getPair,dite_eq_right, LinearMap.zero_apply,char_two]; simp
  · rw [getPair_edge _ _ h]
    change w _ + w _ = _
    rcases lt_or_gt_of_ne h with e|e
    · rw [edge_eq e]
    · rw [edge_symm,edge_eq e,add_comm]

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_QuadraticTesters
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quadratic Testers -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators

theorem pair_outers {I J : Type} [Fintype I] [Fintype J] (x x' : Vec I) (y y' : Vec J) :
    mpair (vecMulVec x y) (vecMulVec x' y') =
      dotProduct x x' * dotProduct y y' := by
  simp only [mpair, dotProduct,vecMulVec_apply,LinearMap.coe_mk,AddHom.coe_mk,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mpair_sum {I J : Type} [Fintype I] [Fintype J] (m : Mat I J)
    {α : Type*} (s : Finset α) (f : α → Mat I J) :
    mpair (∑ i ∈ s, f i) m = ∑ i ∈ s, mpair (f i) m := by
  rw [mpair_comm,map_sum]
  exact Finset.sum_congr rfl fun i _ => mpair_comm _ _

variable (p : Shape)

theorem pick_point {n} (s) (z : Base p.g n) (u : SelIdx p.b p.j)
    (d : Block p.g) (i : ℕ) :
    dotProduct (pick p n u d i) (point p s z) = selV _ s u * readBit z d i := by
  by_cases hi : i < n
  · rw [pick,dite_eq_left hi,single_one_dotProduct,readBit,dite_eq_left hi]; rfl
  · rw [pick,dite_eq_right hi,zero_dotProduct, readBit,dite_eq_right hi,mul_zero]

theorem etab_point {n} (d : Block p.g) (s s') (z z' : Base p.g n) :
    etab p n d (vecMulVec (point p s z) (point p s' z')) = test p n d z z' := by
  unfold etab testM test
  simp only [mpair_sum,pair_outers,pick_point]
  simp [selV,emptySel]

theorem etab_disabled {n} {l d : Tag p.g} (h : ¬allowed d l) (t : Tag p.g)
    {m : Moment p n} (hm : m ∈ Wtag p n l) :
    etab p n (Block.O d t) m = 0 := by
  unfold Wtag at hm
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨s,z,hz,rfl⟩ := hm
    rw [mom,etab_point]
    have h' (i : ℕ) : readBit z (Block.O d t) i = 0 := by
      simp [readBit,hz d t h]
    simp only [test,h',mul_zero,Finset.sum_const_zero]
  | zero => rw [map_zero]
  | add _ _ _ _ h g => rw [map_add,h,g,add_zero]
  | smul _ _ _ h => rw [map_smul,h,smul_zero]

theorem roleT_cut {n} (t : Tag p.g) (w : Tag p.g → Moment p n)
    (hw : ∀ i, w i ∈ Wtag p n i) :
    roleT p n t (cut p n w) =
      ∑ (l : Tag p.g), ∑ (d : Tag p.g), etab p n (Block.O d t) (w l) := by
  simp only [roleT,LinearMap.sum_apply,LinearMap.comp_apply,getPair_cut,map_add]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases h : allowed d l
  · rw [ite_eq_left h,etab_disabled p (not_allowed d) t (hw d),add_zero]
  · rw [ite_eq_right h,etab_disabled p h t (hw l)]

theorem role_cut {n} (w : Tag p.g → Moment p n) (hw : ∀ i,w i ∈ Wtag p n i) :
    role p n (cut p n w) = ∑ i, etaO p n (w i) := by
  simp only [role,LinearMap.sum_apply,roleT_cut _ _ _ hw]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  simp only [etaO,LinearMap.sum_apply]

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

theorem ind_not (p : Prop) : ind (¬p) = 1 - ind p := by
  by_cases h : p <;> simp [ind, h]

theorem ind_and (p q : Prop) : ind (p ∧ q) = ind p * ind q := by
  by_cases h : p <;> by_cases h2 : q <;> simp [ind, h, h2]

theorem ind_or_le (p q : Prop) : ind (p ∨ q) ≤ ind p + ind q := by
  by_cases h : p
  · simp only [h, true_or, ind_true]
    have := ind_nonneg q
    linarith
  · simp [h]

section Basic
variable [Fintype α] {w v f g : Wgt α} {p q : α → Prop}

theorem tot_nonneg (hw : ∀ x, 0 ≤ w x) : 0 ≤ tot w := Finset.sum_nonneg fun x _ => hw x

theorem avg_comm (w f : Wgt α) : avg w f = avg f w := by simp only [avg, mul_comm]

theorem avg_mono (hw : ∀ x, 0 ≤ w x) (h : ∀ x, f x ≤ g x) : avg w f ≤ avg w g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (hw x)

theorem avg_mono_left (hf : ∀ x, 0 ≤ f x) (h : ∀ x, w x ≤ v x) : avg w f ≤ avg v f := by
  rw [avg_comm w, avg_comm v]
  exact avg_mono hf h

theorem avg_nonneg (hw : ∀ x, 0 ≤ w x) (hf : ∀ x, 0 ≤ f x) : 0 ≤ avg w f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (hf x)

theorem avg_const (w : Wgt α) (a : ℝ) : avg w (fun _ => a) = tot w * a := by
  rw [avg, tot, Finset.sum_mul]

theorem IsLaw.avg_const (hw : IsLaw w) (a : ℝ) : avg w (fun _ => a) = a := by
  rw [HadwigerCounterexample.avg_const, hw.total, one_mul]

theorem IsLaw.avg_le (hw : IsLaw w) {b : ℝ} (h : ∀ x, f x ≤ b) : avg w f ≤ b :=
  (avg_mono hw.nz h).trans (hw.avg_const _).le

theorem IsLaw.le_avg (hw : IsLaw w) {b : ℝ} (h : ∀ x, b ≤ f x) : b ≤ avg w f :=
  (hw.avg_const _).ge.trans (avg_mono hw.nz h)

theorem abs_avg_le (hw : ∀ x, 0 ≤ w x) : |avg w f| ≤ avg w (fun x => |f x|) := by
  rw [avg, avg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
  simp_rw [abs_mul, abs_of_nonneg (hw _)]

theorem avg_add (w f g : Wgt α) : avg w (fun x => f x + g x) = avg w f + avg w g := by
  simp only [avg, mul_add, Finset.sum_add_distrib]

theorem avg_sub (w f g : Wgt α) : avg w (fun x => f x - g x) = avg w f - avg w g := by
  simp only [avg, mul_sub, Finset.sum_sub_distrib]

theorem avg_mul (w f : Wgt α) (b : ℝ) : avg w (fun x => f x * b) = avg w f * b := by
  simp only [avg, Finset.sum_mul, mul_assoc]

theorem avg_mul' (w f : Wgt α) (b : ℝ) : avg w (fun x => b * f x) = b * avg w f := by
  simpa only [mul_comm b] using avg_mul w f b

theorem avg_div (w f : Wgt α) (b : ℝ) : avg w (fun x => f x / b) = avg w f / b := by
  simp_rw [div_eq_mul_inv]
  exact avg_mul _ _ _

theorem avg_congr (h : ∀ x, w x ≠ 0 → f x = g x) : avg w f = avg w g := by
  unfold avg
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : w x = 0
  · rw [hx, zero_mul, zero_mul]
  · rw [h x hx]

theorem avg_sum {ι : Type*} (w : Wgt α) (s : Finset ι) (f : ι → Wgt α) :
    avg w (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, avg w (f i) := by
  simp only [avg, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem avg_avg [Fintype β] (w : Wgt α) (v : Wgt β) (f : α → β → ℝ) :
    avg w (fun x => avg v (f x)) = avg v (fun y => avg w (fun x => f x y)) := by
  simp only [avg, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_left_comm]

theorem pr_nonneg (hw : ∀ x, 0 ≤ w x) : 0 ≤ pr w p :=
  avg_nonneg hw fun _ => ind_nonneg _

theorem pr_le_tot (hw : ∀ x, 0 ≤ w x) : pr w p ≤ tot w := by
  unfold pr
  refine (avg_mono hw fun x => ind_le_one (p x)).trans_eq ?_
  rw [avg_const, mul_one]

theorem pr_mono (hw : ∀ x, 0 ≤ w x) (h : ∀ x, p x → q x) : pr w p ≤ pr w q :=
  avg_mono hw fun x => ind_mono (h x)

theorem pr_mono_left (h : ∀ x, w x ≤ v x) (p : α → Prop) : pr w p ≤ pr v p :=
  avg_mono_left (fun x => ind_nonneg (p x)) h

theorem pr_not (w : Wgt α) (p : α → Prop) : pr w (fun x => ¬p x) = tot w - pr w p := by
  simp_rw [pr, ind_not, avg_sub, avg_const, mul_one]

@[simp] theorem pr_true (w : Wgt α) : pr w (fun _ => True) = tot w := by simp [pr, avg, tot]
@[simp] theorem pr_false (w : Wgt α) : pr w (fun _ => False) = 0 := by simp [pr]

theorem pr_or_le (hw : ∀ x, 0 ≤ w x) :
    pr w (fun x => p x ∨ q x) ≤ pr w p + pr w q :=
  (avg_mono hw fun x => ind_or_le (p x) (q x)).trans_eq (avg_add _ _ _)

theorem pr_union_le (hw : ∀ x, 0 ≤ w x) {ι : Type*} (s : Finset ι) (p : ι → α → Prop) :
    pr w (fun x => ∃ i ∈ s, p i x) ≤ ∑ i ∈ s, pr w (p i) := by
  let F : ι → Wgt α := fun i x => ind (p i x)
  change _ ≤ ∑ i ∈ s, avg w (F i)
  rw [← avg_sum]
  refine avg_mono hw fun x => ?_
  change ind (∃ i ∈ s, p i x) ≤ _
  by_cases h : ∃ i ∈ s, p i x
  · rw [ind_one h]
    obtain ⟨i, hi, hp⟩ := h
    have : F i x ≤ ∑ i ∈ s, F i x :=
      Finset.single_le_sum (fun (j : ι) _ => ind_nonneg (p j x)) hi
    simpa only [F, ind_one hp] using this
  · rw [ind_zero h]
    exact Finset.sum_nonneg fun i _ => ind_nonneg (p i x)

theorem pr_exists_le (hw : ∀ x, 0 ≤ w x) {ι : Type*} [Fintype ι] (p : ι → α → Prop) :
    pr w (fun x => ∃ i, p i x) ≤ ∑ i, pr w (p i) := by
  simpa using pr_union_le hw Finset.univ p

theorem weight_le_pr (hw : ∀ x, 0 ≤ w x) {x} (hx : p x) : w x ≤ pr w p := by
  have h := pr_mono (p:=fun y => x = y) (q:=p) hw (fun y e => e ▸ hx)
  simpa only [pr_point] using h

end Basic

section Restrict
variable [Fintype α] {w : Wgt α} {p : α → Prop}

omit [Fintype α] in
theorem subW_nonneg (hw : ∀ x, 0 ≤ w x) (p : α → Prop) : ∀ x, 0 ≤ subW w p x :=
  fun x => mul_nonneg (hw x) (ind_nonneg _)

omit [Fintype α] in
theorem subW_le (hw : ∀ x, 0 ≤ w x) (p : α → Prop) (x : α) : subW w p x ≤ w x :=
  (mul_le_mul_of_nonneg_left (ind_le_one _) (hw x)).trans_eq (mul_one _)

omit [Fintype α] in
theorem subW_carried (w : Wgt α) (p : α → Prop) : carried (subW w p) p :=
  fun x h => by rw [subW, ind_zero h, mul_zero]

theorem pr_sub (w : Wgt α) (p q : α → Prop) :
    pr (subW w p) q = pr w (fun x => p x ∧ q x) := by
  simp only [pr, avg, ind_and, subW, mul_assoc]

theorem normW_nonneg (hw : ∀ x, 0 ≤ w x) : ∀ x, 0 ≤ normW w x :=
  fun x => div_nonneg (hw x) (tot_nonneg hw)

theorem avg_norm (w f : Wgt α) : avg (normW w) f = avg w f / tot w := by
  rw [avg_comm, avg_comm w f]
  exact avg_div _ _ _

theorem tot_norm (w : Wgt α) : tot (normW w) = tot w / tot w := by
  simp only [tot, normW, div_eq_mul_inv, Finset.sum_mul]

theorem normW_law (hw : ∀ x, 0 ≤ w x) (hpos : 0 < tot w) : IsLaw (normW w) :=
  ⟨normW_nonneg hw, by rw [tot_norm, div_self hpos.ne']⟩

theorem normW_subLaw (hw : ∀ x, 0 ≤ w x) : SubLaw (normW w) := by
  refine ⟨normW_nonneg hw, ?_⟩
  rw [tot_norm]
  by_cases h : tot w = 0 <;> simp [h]

theorem normW_carried (hp : carried w p) : carried (normW w) p :=
  fun x h => by rw [normW, hp x h, zero_div]

theorem unif_apply (x : α) : unif x = (Fintype.card α : ℝ)⁻¹ := by
  simp [unif, normW, tot]

theorem unif_law [Nonempty α] : IsLaw (unif : Wgt α) := by
  refine normW_law (fun _ => zero_le_one) ?_
  simp [tot, Fintype.card_pos]

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

theorem mixW_avg (w : Wgt α) (F : α → Wgt β) (g : Wgt β) :
    avg (mixW w F) g = avg w (fun x => avg (F x) g) := by
  simp only [avg, mixW, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem mixW_tot (w : Wgt α) (F : α → Wgt β) :
    tot (mixW w F) = avg w (fun x => tot (F x)) := by
  simpa only [avg_const, mul_one] using mixW_avg w F (fun _ => 1)

theorem mixW_law (hw : IsLaw w) {F : α → Wgt β} (hF : ∀ x, IsLaw (F x)) :
    IsLaw (mixW w F) := by
  refine ⟨fun x => avg_nonneg hw.nz (fun y => (hF y).nz _), ?_⟩
  rw [mixW_tot]
  simp_rw [(hF _).total]
  exact hw.avg_const _

theorem mapW_avg (w : Wgt α) (f : α → β) (g : Wgt β) :
    avg (mapW w f) g = avg w (fun x => g (f x)) := by
  classical
  change avg (mixW w (fun x y => ind (f x = y))) g = _
  rw [mixW_avg]
  simp [avg, ind]

theorem mapW_law (hw : IsLaw w) (f : α → β) : IsLaw (mapW w f) := by
  refine ⟨fun _ => pr_nonneg hw.nz, ?_⟩
  simpa only [avg_const, mul_one, hw.total] using mapW_avg w f (fun _ => 1)

theorem mapW_pr (w : Wgt α) (f : α → β) (q : β → Prop) :
    pr (mapW w f) q = pr w (fun x => q (f x)) := mapW_avg _ _ _

end Prod

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ProductLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product Laws -/

noncomputable section
open scoped BigOperators
namespace HadwigerCounterexample

theorem ind_all {ι : Type*} [Fintype ι] (p : ι → Prop) :
    ind (∀ i, p i) = ∏ i, ind (p i) := by
  classical
  simp [ind, Fintype.prod_ite_zero]

variable {ι κ α : Type*}
variable {β : ι → Type*}

section
variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (β i)]

theorem prodW_tot (w : ∀ i, Wgt (β i)) : tot (prodW w) = ∏ i, tot (w i) :=
  (Fintype.prod_sum w).symm

theorem prodW_avg (w f : ∀ i, Wgt (β i)) :
    avg (prodW w) (prodW f) = ∏ i, avg (w i) (f i) := by
  simp only [avg, prodW]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

theorem prodW_pr (w : ∀ i, Wgt (β i)) (p : ∀ i, β i → Prop) :
    pr (prodW w) (fun x => ∀ i, p i (x i)) = ∏ i, pr (w i) (p i) := by
  simp_rw [pr, ind_all]
  exact prodW_avg w (fun i x => ind (p i x))

omit [DecidableEq ι] [∀ i, Fintype (β i)] in
theorem prodW_nonneg {w : ∀ i, Wgt (β i)} (h : ∀ i x, 0 ≤ w i x) (x) : 0 ≤ prodW w x :=
  Finset.prod_nonneg (fun i _ => h i _)

theorem prodW_law {w : ∀ i, Wgt (β i)} (hw : ∀ i, IsLaw (w i)) : IsLaw (prodW w) := by
  refine ⟨prodW_nonneg (fun i => (hw i).nz), ?_⟩
  rw [prodW_tot]
  simp_rw [(hw _).total]
  simp

end

section
variable [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq κ]
/-- Observe distinct coordinates of a (constant-type) product law. -/
theorem prodW_pr_inj {e : ι → κ} (he : Function.Injective e)
    {w : κ → Wgt α} (hw : ∀ k, IsLaw (w k)) (p : ι → α → Prop) :
    pr (prodW (β:=fun _ => α) w) (fun x => ∀ i, p i (x (e i))) =
      ∏ i, pr (w (e i)) (p i) := by
  classical
  let P (k : κ) (x : α) := ∀ i, e i = k → p i x
  have h (x : κ → α) : (∀ i, p i (x (e i))) ↔ ∀ k, P k (x k) :=
    ⟨fun h k i hi => hi ▸ h i, fun h i => h (e i) i rfl⟩
  simp_rw [h]
  rw [prodW_pr _ P]
  let f (k : κ) (i : ι) := if e i = k then pr (w k) (p i) else 1
  have hf (k : κ) : pr (w k) (P k) = ∏ i, f k i := by
    by_cases hk : ∃ i, e i = k
    · obtain ⟨i, rfl⟩ := hk
      have hP : P (e i) = p i := funext fun x => propext
        ⟨fun h => h i rfl, fun h j hj => (he hj).symm ▸ h⟩
      rw [hP]
      symm
      rw [Finset.prod_eq_single i]
      · simp [f]
      · intro j _ hj
        simp [f, show e j ≠ e i from he.ne hj]
      · simp
    · push Not at hk
      have hP : P k = (fun _ => True) := funext fun _ => propext
        ⟨fun _ => trivial, fun _ j hj => (hk j hj).elim⟩
      simp [hP, (hw k).total, f, hk]
  simp_rw [hf]
  rw [Finset.prod_comm]
  simp [f]

end
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! # Finite Conditioning -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators

variable {A B : Type*} [Fintype A]

theorem unifOn_sub (p : A → Prop) : SubLaw (unifOn p) :=
  normW_subLaw fun x => ind_nonneg (p x)

theorem pr_on (w : Wgt A) (p q : A → Prop) :
    pr (onW w p) q = pr w (fun x => p x ∧ q x) / pr w p := by
  unfold onW
  change avg _ _ = _
  rw [avg_norm,subW_tot]
  exact congrArg (fun b => b / pr w p) (pr_sub w p q)

theorem pr_of_on {w : Wgt A} (hw : ∀ x, 0 ≤ w x) (p q : A → Prop) :
    pr w (fun x => p x ∧ q x) = pr w p * pr (onW w p) q := by
  rw [pr_on]
  by_cases h : pr w p = 0
  · rw [h,zero_mul]
    apply le_antisymm _ (pr_nonneg hw)
    rw [← h]
    exact pr_mono hw fun _ => And.left
  · field_simp

theorem onW_val (w : Wgt A) (p : A → Prop) (x) :
    onW w p x = w x * ind (p x) / pr w p := rfl

theorem on_mon {w : Wgt A} (hw : ∀ x, 0 ≤ w x) {p : A → Prop} {a : ℝ}
    (ha : 0 < a) (h : a ≤ pr w p) (x) : onW w p x ≤ a⁻¹ * w x :=
  calc onW w p x = (subW w p x) / pr w p := rfl
       _ ≤ w x / a := div_le_div₀ (hw x) (subW_le hw p x) ha h
       _ = _ := by rw [div_eq_mul_inv,mul_comm]

theorem avg_bij (e : A ≃ A) (w f : Wgt A) :
    avg (fun x => w (e x)) (fun x => f (e x)) = avg w f := by
  unfold avg
  exact Equiv.sum_comp e (fun x => w x * f x)

variable [Fintype B]

omit [Fintype B] in
theorem mapW_carried {w : Wgt A} {p : A → Prop} {q : B → Prop} {f : A → B}
    (hw : carried w p) (h : ∀ x, p x → q (f x)) : carried (mapW w f) q := by
  intro y hy
  change ∑ x, w x * ind (f x=y) = 0
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases e : f x=y
  · rw [hw x (fun hp => hy (e ▸ h x hp)),zero_mul]
  · rw [ind_zero e,mul_zero]

/-- A pointwise fiber disintegration. -/
theorem disintegrate {w : Wgt A} (hw : ∀ x, 0 ≤ w x) (f : A → B) :
    w = mixW (mapW w f) (fun y => onW w (fun x => f x = y)) := by
  funext x
  unfold mixW avg
  rw [Finset.sum_eq_single (f x)]
  · simp only [mapW,onW_val,ind_true,mul_one]
    by_cases h : pr w (fun z => f z = f x) = 0
    · rw [h,zero_mul]
      apply le_antisymm _ (hw x)
      rw [← h]; exact weight_le_pr hw rfl
    · field_simp
  · intro i _ hi; simp [onW_val, ind, Ne.symm hi]
  · simp

omit [Fintype B] in
/-- Mapping changes a density bound functorially. -/
theorem mapW_cap {w v : Wgt A} {c : ℝ} (h : ∀ x, w x ≤ c * v x) (f : A → B) (y) :
    mapW w f y ≤ c * mapW v f y := by
  unfold mapW
  refine (pr_mono_left (v:=fun x => c * v x) h _).trans_eq ?_
  simp only [pr,avg,Finset.mul_sum,mul_assoc]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConditionalProductLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional Product Laws -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators

variable {A B I : Type} [Fintype A] [Fintype B]

theorem semi_avg (w : Wgt A) (k : A → Wgt B) (f : A × B → ℝ) :
    avg (semi w k) f = avg w (fun x => avg (k x) (fun y => f (x,y))) := by
  simp only [avg,semi,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ExponentialRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential Rates -/

noncomputable section
namespace HadwigerCounterexample

open Filter Real
open scoped Topology

theorem bp_pos (x : ℝ) : 0 < bp x := by unfold bp; positivity
theorem bp_nat (x : ℕ) : bp x = (2:ℝ)^x := by simp [bp]
theorem bp_add (x y : ℝ) : bp (x+y) = bp x * bp y :=
  Real.rpow_add (by norm_num) _ _
theorem bp_sub (x y : ℝ) : bp (x-y) = bp x / bp y :=
  Real.rpow_sub (by norm_num) _ _
theorem bp_neg (x : ℝ) : bp (-x) = (bp x)⁻¹ := by simpa using bp_sub 0 x

theorem bp_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => bp (a*x)) atTop atTop :=
  (tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num)).comp
    ((tendsto_const_mul_atTop_of_pos ha).mpr tendsto_id)

variable {ι : Type*} {l : Filter ι} {n f g : ι → ℝ}

theorem expO_const (hn : Tendsto n l atTop) (b : ℝ) :
    ExpO l n (fun _ => b) := fun _ hc =>
  ((bp_tendsto hc).comp hn).eventually (eventually_ge_atTop _)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteAffineLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

section General
variable (V W : Type)
variable [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

theorem card_space [Fintype V] : (Fintype.card V : ℝ) = bp (dim V) := by
  rw [Module.card_eq_pow_finrank (K:=F)]
  rw [show Fintype.card F = 2 from ZMod.card 2, bp_nat]
  push_cast; rfl

end General

theorem dim_mat (I J : Type) [Fintype I] [Fintype J] :
    dim (Mat I J) = Fintype.card I * Fintype.card J := by
  simp only [dim,Mat,finrank_matrix,finrank_self,mul_one]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RawFrameLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Raw Frame Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators

variable {p : Shape} {n N : ℕ}

theorem raw_nonneg (m : Mixer p n) (X : Orient p n N) : 0 ≤ raw m N X :=
  prodW_nonneg (fun _ _ => (unifOn_sub _).nz _) _

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MatrixQuotients
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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

theorem table_dim (s : Plan p n) (e : Place p) :
    dim (tabSpace s e) ≤ 2*(planRank s + p.h) := by
  have hh i : dim (halfTable s e i)≤ planRank s+p.h := by
    have hg : dim (colSp (IH p n i)) ≤ p.h := (IH p n i).rank_le_card_width.trans_eq
      (Fintype.card_fin _)
    apply le_trans (Submodule.finrank_add_le_finrank_add_finrank ..)
    exact Nat.add_le_add ((Submodule.finrank_map_le _ _).trans
      ((sPin_dim ..).trans (dim_le_plan s e))) hg
  exact ((Submodule.finrank_add_le_finrank_add_finrank ..).trans
    (Nat.add_le_add (hh true) (hh false))).trans_eq (two_mul _).symm

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
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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

theorem fits_inj {M T : Cross p n} {a b : Plan p n} (h : fitsTable a b M T)
    (ht : tableInj a b T) : tableInj a b M := by
  intro z i j v hv hh
  apply ht z i j v hv
  rwa [fits_channel h z _ (pin_le_table a z hv) j] at hh

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
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SumRankBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sum Rank Bounds -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Finset
variable {A I : Type} [Fintype A] [Fintype I] [DecidableEq I]

theorem draws_law {w : Wgt A} (h : IsLaw w) :
    IsLaw (draws I w) := prodW_law (fun _ => h)

theorem fresh_avg (w : Wgt A) (hw : IsLaw w) (J : Finset I) (f : Wgt (I→A)) :
    avg (draws I w) f =
    avg (draws I w) (fun x => avg (draws I w) (fun y => f (refresh J x y))) := by
  classical
  let P := draws I w
  have hP : IsLaw P := draws_law hw
  let E := fun x : (I→A)×(I→A) => (refresh J x.1 x.2, refresh J x.2 x.1)
  have hE x : E (E x)=x := by
    apply Prod.ext
    · funext i; change refresh _ _ _ _=_; by_cases h : i∈J <;> simp [refresh,E,h]
    · funext i; change refresh _ _ _ _=_; by_cases h : i∈J <;> simp [refresh,E,h]
  let e : (I→A)×(I→A) ≃ _ := ⟨E,E,hE,hE⟩
  have he x : pairW P P (E x)=pairW P P x := by
    unfold pairW P draws prodW
    rw [←Finset.prod_mul_distrib,←Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    dsimp only [E,refresh]
    split <;> ring
  have ht := avg_bij e (pairW P P) (fun x => f x.1)
  change avg (fun x => pairW P P (E x)) (fun x => f (E x).1)=_ at ht
  simp_rw [he] at ht
  rw [pairW_avg,pairW_avg] at ht
  simp_rw [hP.avg_const] at ht
  exact ht.symm

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BinaryPrescriptions
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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

theorem sum_pr_tag (w : Wgt A) (P : A → Prop) (f : A→I) :
    ∑ i:I,pr w (fun x => P x ∧ f x=i) = pr w P := by
  classical
  unfold pr
  rw [← avg_sum]
  refine avg_congr fun x _ => ?_
  simp only [ind_and, ← Finset.mul_sum]
  rw [Finset.sum_eq_single (f x)]
  · rw [ind_one rfl,mul_one]
  · intro j _ hj; exact ind_zero hj.symm
  simp

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ChannelFrameLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Channel Frame Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset Function
open scoped BigOperators

variable {A B : Type} [Fintype A] [Fintype B]

theorem map_pair_law {C D : Type} [Fintype C] [Fintype D]
    (w : Wgt A) (v : Wgt B) (f : A→C) (g : B→D) :
    mapW (pairW w v) (Prod.map f g)=pairW (mapW w f) (mapW v g) := by
  funext x
  unfold mapW pairW
  simp only [Prod.ext_iff]
  exact pairW_pr w v (fun y => f y=x.1) (fun y => g y=x.2)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AtomFlavors
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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

theorem asBlock_inj {g : ℕ} : Injective (@asBlock g) := by
  rintro (⟨i,j⟩|⟨⟩) (⟨k,l⟩|⟨⟩) e <;> simp_all [asBlock,Block.O,Block.S]

theorem scan_is (p : Shape) {n} (l) (s : Label p.b) (f : Flavor p.g) (x : Knobs p.g n)
    (i : ProbeIdx p.g) :
    scan p l f x i=etab p n (asBlock i) (mom p s (lit f l x)) := by
  classical
  rw [mom,etab_point]
  let d := asBlock i
  unfold scan
  split
  · rename_i he
    have hg j : readBit (lit f l x) d j=zget (x d) j := by
      by_cases h : j<n <;> simp [readBit,zget,h,lit,d,he]
    unfold tested test
    simp_rw [show ∀ j, readBit (lit f l x) (asBlock i) j=zget (x (asBlock i)) j from hg]
  rename_i he
  unfold test
  have hZ j :
      readBit (lit f l x) (asBlock i) j=0 := by
    by_cases h : j<n <;> simp [readBit,lit,h,he]
  simp_rw [hZ,zero_mul,Finset.sum_const_zero]

theorem role_scan (p : Shape) {n} (l s f) (x : Knobs p.g n) :
    role p n (useAtom p l s f x)=(scan p l f x).diagO := by
  unfold Digest.diagO useAtom atom
  let M := mom p s (lit f l x)
  have h (i : Tag p.g) :
      (Pi.single l M : Tag p.g → Moment p n) i∈Wtag p n i := by
    by_cases h : i=l
    · subst i; rw [Pi.single_eq_same]
      exact Submodule.subset_span ⟨_,_,lit_allows f l x,rfl⟩
    simp [h]
  rw [role_cut _ _ h,Finset.sum_eq_single l]
  · rw [Pi.single_eq_same,etaO,LinearMap.sum_apply]
    simp_rw [LinearMap.sum_apply,scan_is p l s]
    rfl
  · intro i _ hi; simp [hi]
  simp

theorem spins_law (p : Shape) (n : ℕ) : IsLaw (spins p n) := draws_law unif_law

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

theorem draws_unif :
    unif (α:=I → A)=draws I (unif : Wgt A) := by
  classical funext i
            simp [draws,prodW,unif_apply]

set_option maxHeartbeats 600000 in
theorem tested_fraction (r n : ℕ) (hr : 1 ≤ r) (hn : 2*r≤n) (q : F) :
    1/4 ≤ pr unif (fun x : Vec (Fin n) => tested r x=q) := by
  classical
  let w := draws (Fin n) (unif (α:=F))
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨1,by omega⟩
  let Z : Finset (Fin n) := {a,b}
  have hh : pr unif (fun x : Vec (Fin n) => tested r x=q) =
      avg w (fun x => pr w (fun y => tested r (refresh Z x y)=q)) := by
    unfold pr; rw [draws_unif]
    exact fresh_avg _ unif_law _ _
  rw [hh]
  refine (draws_law unif_law).le_avg (fun v => ?_)
  let i0 : Fin r := ⟨0,hr⟩
  let S : Finset (Fin r) := Finset.univ.erase i0
  let h (y : Vec (Fin n)) (i : Fin r) := zget y (2*i.val)*zget y (2*i.val+1)
  let t := ∑ i∈S,h v i
  have hg (y) (ha : y a=1) (hb : y b=q-t) :
      tested r (refresh Z v y) = q := by
    have hu (i : Fin r) (hh : i∈ S) : h (refresh Z v y) i=h v i := by
      have hi := (mem_erase.mp hh).1
      have hi' : i.val ≠ 0 := fun h => hi (Fin.ext h)
      have heq (j : ℕ) (h : 1<j) : zget (refresh Z v y) j=zget v j := by
        by_cases hj : j<n
        · let x : Fin n := ⟨j,hj⟩
          have hr : x∉Z := by simp [x,Z,a,b]; omega
          simp only [zget,dite_eq_left hj,refresh,show (⟨j,hj⟩ : Fin n) ∉ Z from hr,ite_false, if_false]
        simp [zget,hj]
      unfold h
      rw [heq (2*i.val) (by omega),heq _ (by omega)]
    change ∑ i,h _ i=q
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
    change h _ i0 + ∑ i∈S, _=_
    rw [show (∑ i∈S,h (refresh Z v y) i)=t from sum_congr rfl hu]
    have h0 := a.isLt
    have h1 := b.isLt
    change 0<n at h0; change 1<n at h1
    have hx : h (refresh Z v y) i0=y a*y b := by
      simp only [h,i0,zget,Nat.mul_zero,Nat.zero_add,dite_eq_left h0,dite_eq_left h1,refresh]
      simp [a,b,Z]
    rw [hx,ha,hb,one_mul,sub_add_cancel]
  let f (i : Bool) := if i then a else b
  let P (i : Bool) (y : F) := y=if i then 1 else q-t
  have he : Injective f := by intro i j; cases i <;> cases j <;> simp [f,a,b]
  have hi : pr w (fun x => ∀ i,P i (x (f i)))=1/4 := by
    change pr (prodW _) _ = _
    rw [prodW_pr_inj he (fun _ => unif_law) P]
    simp only [Fintype.prod_bool,P,pr_point',unif_apply,F]
    norm_num [ZMod.card]
  rw [←hi]
  exact pr_mono (draws_law unif_law).nz (fun y h => hg _ (h true) (h false))

theorem scan_fraction (l : Tag p.g) (f : Flavor p.g) (x : Digest p.g)
    (hr : 1 ≤ p.r) (hn : 2*p.r ≤ n) (hx : x.feasible l f) :
    scanPrice p ≤ pr (spins p n) (fun y => scan p l f y=x) := by
  classical
  let P (i : ProbeIdx p.g) (v : Vec (Fin n)) :=
    (if f.keeps l (asBlock i) then tested p.r v else 0)=x i
  have h (i) : 1/4 ≤ pr unif (P i) := by
    by_cases h : f.keeps l (asBlock i)
    · simpa only [P,h,ite_true, if_true] using tested_fraction _ _ hr hn (x i)
    simp [P,h,hx _ h,unif_law.total] <;> norm_num
  have hi y : scan p l f y=x ↔ ∀ i,P i (y (asBlock i)) := funext_iff
  change _ ≤ pr (draws _ _) _
  simp_rw [hi]
  rw [draws,prodW_pr_inj asBlock_inj (fun _ => unif_law) P]
  refine le_trans ?_ (Finset.prod_le_prod (fun i _ => ?_) fun i _ => h i)
  · simp [scanPrice]
  norm_num

theorem dial_fraction (p : Shape) (n : ℕ) (l) (f : Flavor p.g) (x : F)
    (hr : 1 ≤ p.r) (hn : 2*p.r ≤ n) (hx : canDial p l f x) :
    scanPrice p ≤ pr (spins p n) (fun y => dialed p l f y=x) := by
  obtain ⟨v,hv,h⟩ := hx
  exact (scan_fraction l f v hr hn hv).trans
    (pr_mono (spins_law p n).nz fun i hi => (congrArg Digest.sumBit hi).trans h)

theorem scanPrice_pos (p : Shape) : 0 < scanPrice p := by unfold scanPrice; positivity

theorem dial_law (p : Shape) (n : ℕ) (l) (f : Flavor p.g) (x : F)
    (hr : 1 ≤ p.r) (hn : 2*p.r≤n) (hx : canDial p l f x) :
    IsLaw (scopedBit p n l f x) := on_law (spins_law p n).nz
      ((scanPrice_pos p).trans_le (dial_fraction p n _ _ _ hr hn hx))

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PairIndexedTests
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pair Indexed Tests -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module Function
open scoped BigOperators
variable {I J A : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A]
variable {s : Stage I J} {B : J→ Type}
variable [∀ i,Fintype (B i)] [∀ i,DecidableEq (B i)]

omit [DecidableEq J] in
theorem wavelength_pos (B : J →Type) [∀ i,Fintype (B i)] [∀ i,DecidableEq (B i)] :
    0<wavelength B := prod_pos (fun i _ => by simp only [unif_apply] <;> positivity)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BinaryMixingBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary Mixing Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Filter Matrix Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]
namespace Template
variable (v : Template p I)

omit [DecidableEq I] in
theorem kappa_pos : 0<v.kappa := wavelength_pos _

end Template

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_UnaryQueryFrequencies
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unary Query Frequencies -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Finset Filter Real Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

theorem scanLaw (p : Shape) {n : ℕ} (l : Tag p.g) (z : Digest p.g)
    (f : Flavor p.g) (hr : 1 ≤ p.r) (hn : 2*p.r≤n) (h : z.feasible l f) :
    IsLaw (scopedScan p n l f z) := on_law (spins_law p n).nz
      ((scanPrice_pos p).trans_le (scan_fraction l f z hr hn h))
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ScalarStatusAlgebra
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar Status Algebra -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Finset Function Module
open scoped BigOperators

namespace StatusAnalysis
variable {d e : ℕ}

theorem testV_surj (d e : ℕ) : Surjective (testV d e) := by
  rintro ⟨a,b,x,y⟩
  exact ⟨(a,(b,x),(0,y)),Prod.ext rfl (Prod.ext (add_zero _) rfl)⟩
theorem coversFull {V : Space (Signal d e)} (h : coverBase V) : Surjective (want d e ∘ₗ V.subtype) :=
  (testV_surj _ _).comp h

variable {A B : Rates}

theorem speak_solo (A B : Rates) (i : Grid) (x : Suite A B i) :
    speak A B (Pi.single i x)=separate A B i x := by
  classical
  unfold speak; rw [LinearMap.sum_apply,sum_eq_single i]
  · rw [LinearMap.comp_apply]; change separate _ _ _ ((Pi.single i x : ∀ i, Suite A B i) i)=_
    rw [Pi.single_eq_same]
  · intro j _ hj; rw [LinearMap.comp_apply]
    change separate _ _ _ ((Pi.single i x : ∀ i, Suite A B i) j)=_
    rw [Pi.single_eq_of_ne hj,map_zero]
  simp

private theorem vanishes {M : Type} [AddCommGroup M] [Module F M] (V : Space M) {z}
    (h : z∉ V) :
    ∃ f:M→ₗ[F] F,f z ≠0 ∧ ∀ i∈V,f i=0 := by
  have he : V.mkQ z ≠0 := fun hg=>h ((Submodule.Quotient.mk_eq_zero V).mp hg)
  obtain ⟨f,hf⟩ := Module.Projective.exists_dual_ne_zero F he
  exact ⟨f ∘ₗ V.mkQ,hf,fun i hi =>by rw [LinearMap.comp_apply,show V.mkQ i=0 from
    (Submodule.Quotient.mk_eq_zero V).mpr hi,map_zero]⟩

set_option maxHeartbeats 800000 in
theorem counter_score (V : StatusSp A B) (T : Cabinet A B)
    (h : ¬scorecard V T) :
    ∃ g : Critic A B,Counter g V ∧ ∑ i,g.alf i (T i)≠0 := by
  classical
  let S := (Submodule.pi Set.univ V).map (speak A B)
  have ht : (T,(0 : Quota × Quota))∉ S := by
    rintro ⟨z,hz,he⟩
    exact h ⟨z,fun i => hz i (Set.mem_univ _),he⟩
  obtain ⟨f,hf,hx⟩ := vanishes S ht
  let g : Critic A B := {
    alf := fun i => f ∘ₗ LinearMap.inl F (Cabinet A B) _ ∘ₗ LinearMap.single F _ i
    altL := fun i=> f (0,Pi.single i 1,0)
    altR := fun i=> f (0,0,Pi.single i 1) }
  refine ⟨g,fun i v hv => ?_,?_⟩
  · have hi :
        f (separate A B i v)=0 := by
      apply hx
      refine ⟨Pi.single i v,?_,speak_solo A B i v⟩
      intro j _
      by_cases ht : j=i
      · subst j; rwa [Pi.single_eq_same]
      rw [Pi.single_eq_of_ne ht]; exact zero_mem _
    let a:= couple _ v.2.1
    let b:= couple _ v.2.2
    let Q:= want _ _ v
    have hh (a:F) (i:Bool) :
       (a • Pi.single i 1 : Quota)=Pi.single i a := by
      ext j; by_cases he:j=i <;> simp [he]
    have hz :
        separate A B i v =
        ( (Pi.single i Q : Cabinet A B),0) + (a • (0,Pi.single i.2 1,(0:Quota))+
          b • (0,(0:Quota),Pi.single i.1 1)) := by
      change ((Pi.single i Q:Cabinet A B),(Pi.single i.2 a:Quota),(Pi.single i.1 b:Quota))=_
      apply Prod.ext; simp
      apply Prod.ext <;> simp [hh]
    rw [hz,map_add,map_add,map_smul,map_smul] at hi
    change g.alf i Q+(a*g.altL i.2+b*g.altR i.1)=0 at hi
    change _=g.altL _ * a+g.altR _ * b
    rw [mul_comm _ a,mul_comm _ b]
    exact add_right_cancel (hi.trans (char_two _).symm)
  · have hh (i) : g.alf i (T i)=f ((Pi.single i (T i) : Cabinet A B),0) := rfl
    have ht : ∑ i:Grid, ((Pi.single i (T i) : Cabinet A B),(0 : Quota × Quota))=
        (T,0) := by
      apply Prod.ext
      · rw [Prod.fst_sum]; exact Finset.univ_sum_single _
      · simp only [Prod.snd_sum,Finset.sum_const_zero]
    simp_rw [hh, ← map_sum,ht]
    exact hf

theorem critic_nz (V : StatusSp A B) (T : Cabinet A B) (hV : ∀ i,coverBase (V i)) (g : Critic A B)
    (h : Counter g V) (hh : ∑ i,g.alf i (T i)≠0) : g.altL≠0 ∨ g.altR≠0 := by
  classical
  by_contra! hz
  apply hh; apply Finset.sum_eq_zero
  intro i _
  obtain ⟨⟨v,hv⟩,ht⟩ := coversFull (hV i) (T i)
  simpa only [show want (A i.1) (B i.2) v=T i from ht,hz.1,hz.2,Pi.zero_apply,zero_mul,add_zero]
    using h i v hv

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CoordinateDuality
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate Duality -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Submodule Function
open scoped BigOperators
namespace StatusAnalysis
variable {A B : Rates} {d e : ℕ}

private theorem coordinates (f : Question d e →ₗ[F] F) :
    ∃ a b : F,∃ (u : Cell d) (v : Cell e),∀ (x:Question d e),
    f x=a*x.1+b*x.2.1 + (dotProduct u x.2.2.1+dotProduct v x.2.2.2) := by
  let g := f ∘ₗ LinearMap.inr F F _ ∘ₗ LinearMap.inr F F _
  obtain ⟨u,hu⟩:=dotL_surj (g ∘ₗ LinearMap.inl F _ _)
  obtain ⟨v,hv⟩:=dotL_surj (g ∘ₗ LinearMap.inr F _ _)
  let a : Question d e := (1,0); let b : Question d e := (0,1,0)
  refine ⟨f a,f b,u,v,?_⟩
  rintro ⟨x,y,z,w⟩
  have he : ((x,y,z,w):Question d e)=x • a +y • b+((0,0,z,0)+(0,0,0,w)) := by
    unfold a b; ext <;> simp
  have h1 : f (0,0,z,0)=dotProduct u z := LinearMap.congr_fun hu z
  have h2 : f (0,0,0,w)=dotProduct v w := LinearMap.congr_fun hv w
  change f (x,y,z,w)=f a*x + f b*y + _
  conv_lhs => rw [he]
  rw [map_add,map_add,map_add,map_smul,map_smul,h1,h2]; simp [mul_comm]

theorem jargon_score (V : StatusSp A B) (T : Cabinet A B)
    (h : ¬scorecard V T) (hh : ∀ i,coverBase (V i)) :
    ∃ p : DualCoefficients A B, (p.left≠0 ∨ p.right≠0) ∧ p.law V ∧ ∑ i,p.bet i (T i)≠0 := by
  obtain ⟨p,hp,hf⟩:= counter_score V T h
  choose a b u v he using fun i=>coordinates (p.alf i)
  let g : DualCoefficients A B:=⟨p.altL,p.altR,a,b,u,v⟩
  have hz i x : g.bet i x=p.alf i x := (he i x).symm
  refine ⟨g,critic_nz V T hh p hp hf,fun i x hx=>?_,?_⟩
  · rw [hz]; exact hp i x hx
  simp_rw [hz]; exact hf

theorem signal_dim :
    dim (Signal d e) = dim (View d e)+2 := by
  simp only [Signal,View,Whole,dim,finrank_prod,finrank_self]
  omega
theorem ker_two (V : Space (Signal d e)) :
    dim (excessK V) ≤ 2 := by
  have he : Surjective (view d e) := by
    rintro ⟨i,j,k⟩; exact ⟨(i,(j,0),(k,0)),rfl⟩
  have ht := LinearMap.finrank_range_add_finrank_ker (view d e)
  change rk (view _ _) + dim _=dim (Signal d e) at ht
  rw [rk_surj.mp he,signal_dim] at ht
  exact (Submodule.finrank_mono (show excessK V≤_ from inf_le_right)).trans
    (by omega : dim (LinearMap.ker (view d e)) ≤ 2)

theorem overage_two (V : Space (Signal d e)) : overage V≤2 := by
  have hi : dim V ≤ dim (Signal d e) := finrank_le _
  rw [signal_dim] at hi; unfold overage; omega
theorem overage_mono {V W : Space (Signal d e)} (h : V≤W) :
    overage V≤overage W := Nat.sub_le_sub_right (finrank_mono h) _
theorem overage_lt {V W : Space (Signal d e)} (h : V<W) (he : coverBase V) :
    overage V<overage W := by
  have hh := finrank_lt_finrank_of_lt h; change dim V<dim W at hh
  have hx : dim (View d e) ≤ dim V := LinearMap.finrank_le_finrank_of_surjective he
  unfold overage; omega
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_LabeledGenerators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Labeled Generators -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function LinearMap Submodule Module
open scoped BigOperators
namespace StatusAnalysis
variable {L I X Y : Type} [DecidableEq L] [DecidableEq I] [AddCommGroup X]
    [Module F X] [AddCommGroup Y] [Module F Y]

variable (C : Club I X L)
namespace Club

omit [DecidableEq L] [DecidableEq I] in
theorem band_write (s : Straps L) {i : I} (hi : C.zone s i) :
    C.writes i∈ C.band s := subset_span ⟨i,hi,rfl⟩
omit [DecidableEq L] [DecidableEq I] in
theorem band_contents (s : Straps L) {p : Finset I} (hp : C.bundle p s) :
    C.contents p∈ C.band s := Submodule.sum_mem _ fun i hi=> band_write C s (hp.1 i hi)
omit [DecidableEq L] [DecidableEq I] in
theorem length3_zero (s : Straps L) (π : X→ₗ[F] Y) :
    C.length3 s π 0 := by refine ⟨∅,⟨?_,?_⟩,?_,?_,?_⟩ <;> simp [contents]

omit [DecidableEq L] [DecidableEq I] [AddCommGroup X] [Module F X] in
theorem zone_smaller {s t : Straps L} (h : s≤t) (i:I) (hi : zone C t i) : zone C s i :=
  ⟨hi.1,fun b hx=> hi.2 b (h b hx)⟩
omit [DecidableEq L] [DecidableEq I] in
theorem ration_le (s : Straps L) (π : X→ₗ[F] Y) : ration C s π ≤ C.band s⊓LinearMap.ker π := by
  refine Submodule.span_le.mpr ?_
  rintro i ⟨x,ha,hb,rfl,hg⟩
  exact ⟨band_contents C s ha,hg⟩

omit [DecidableEq I] in
theorem yield_after (s : Straps L) (π : X→ₗ[F] Y) (h : yield3 C s π)
    (p : Finset I) (hp : p.card≤ 2) (y : Y) :
    ∃ i,zone C s i ∧ π (C.writes i)=y ∧
      ∀ j∈p,∀ b,C.addr i b≠C.addr j b := by
  obtain ⟨i,hi,ht⟩ := h (addrs C p) (fun i=>card_image_le.trans hp) y
  refine ⟨i,C.zone_smaller le_sup_left i hi,ht,fun j hj b h=>?_⟩
  exact hi.2 b (mem_union_right _ (Finset.mem_image.mpr ⟨j,hj,h.symm⟩))

omit [DecidableEq L] [DecidableEq I] [AddCommGroup X] [Module F X] in
theorem different_ne {i j : I} (h : C.different i j) : i≠j := fun hx=> h true (hx ▸ rfl)
omit [DecidableEq L] [DecidableEq I] [AddCommGroup X] [Module F X] in
theorem bundle_one (s : Straps L) {i} (h : zone C s i) : bundle C {i} s := by
  constructor
  · intro j hj; rwa [mem_singleton.mp hj]
  simp

omit [DecidableEq L] [AddCommGroup X] [Module F X] in
theorem bundle_insert (s : Straps L) {i} (h : zone C s i) (p : Finset I) (hp : bundle C p s)
    (he : ∀ j∈p,C.different i j) : bundle C (insert i p) s := by
  refine ⟨fun j hj=>?_,fun b y hy z hz hh=>?_⟩
  · rcases mem_insert.mp hj with h'|h'
    · exact h' ▸ h
    exact hp.1 j h'
  rcases mem_insert.mp hy with h'|h'
  · subst y; rcases mem_insert.mp hz with hz|hz
    · exact hz.symm
    exact (he _ hz b hh).elim
  rcases mem_insert.mp hz with hz|hz
  · subst z; exact (he _ h' b hh.symm).elim
  exact hp.2 b h' hz hh

set_option maxHeartbeats 900000 in
theorem ration_eq (s : Straps L) (π : X→ₗ[F] Y) (h : yield3 C s π) :
    ration C s π=C.band s⊓LinearMap.ker π := by
  classical
  let R:=ration C s π; let q:=R.mkQ

  have hr (i j:I) (hi:C.zone s i) (hj:C.zone s j) (ht : π (C.writes i)=π (C.writes j))
      (hh : C.different i j) : q (C.writes i)=q (C.writes j) := by
    have hg:=C.different_ne hh
    let W := C.writes
    apply add_right_cancel (b:=q (W j))
    rw [char_two,←map_add]
    apply (Submodule.Quotient.mk_eq_zero R).mpr
    refine subset_span ⟨{i,j},C.bundle_insert s hi _ (C.bundle_one s hj)
      (fun z hz=> (mem_singleton.mp hz).symm ▸ hh),by simp [hg],
      by simp [contents,W,hg],?_⟩
    rw [map_add,ht,char_two]
  let f:=C.writes
  have hg (i j:I) (hi:C.zone s i) (hj:C.zone s j) (ht : π (f i)=π (f j)) :
      q (f i)=q (f j) := by
    obtain ⟨t,ht',hy,hb⟩:=C.yield_after s π h {i,j} (by
      by_cases hi : i=j <;> simp [hi]) (π (f j))
    exact (hr t i ht' hi (hy.trans ht.symm) (hb i (by simp))).symm.trans
      (hr t j ht' hj hy (hb j (by simp)))
  choose g he hG hP using fun y=>C.yield_after s π h ∅ (by simp) y
  let F (x : Y) := q (f (g x))
  have hq i (hi:C.zone s i) : F (π (f i))=q (f i) := hg _ i (he _) hi (hG _)
  have h0 : F 0=0 := by
    have hh:=he 0
    refine (Submodule.Quotient.mk_eq_zero R).mpr (subset_span ?_)
    exact ⟨{g 0},C.bundle_one s hh, by simp, by simp [f,contents], hG 0⟩
  have hh (x y) : F (x+y)=F x+F y := by
    let i:=g x
    obtain ⟨j,hj,hJ,hA⟩:=C.yield_after s π h {i} (by simp) y
    have hai:=hA i (by simp)
    have hg' : j≠i:=C.different_ne hai
    let t : Finset I := {j,i}
    have ht : t.card=2 := by simp [t,hg']
    obtain ⟨k,hk,hK,hB⟩:=C.yield_after s π h t (by omega) (x+y)
    have hkt : k∉t := fun hx=> C.different_ne (hB k hx) rfl
    have hQ :
        q (f k)+(q (f j)+q (f i))=0 := by
      have hR : C.length3 s π (f k+(f j+f i)) := by
        refine ⟨insert k t,C.bundle_insert s hk _ (C.bundle_insert s hj _ (C.bundle_one s
          (he x)) (fun i hi => hA i hi)) hB,?_,?_,?_⟩
        · rw [card_insert_of_notMem hkt,ht]
        · rw [contents, Finset.sum_insert hkt]
          simp [t,f,hg']
        rw [map_add,map_add,hK,hJ,hG]
        rw [add_comm y,char_two]
      rw [← map_add,←map_add]
      exact (Submodule.Quotient.mk_eq_zero R).mpr (subset_span hR)
    change q _+ _=0 at hQ
    have hq' (z a) (hz:zone C s a) (h : π (C.writes a)=z) : q (f a)=F z := by rw [←h]; exact (hq a hz).symm
    rw [hq' _ k hk hK,hq' _ j hj hJ,hq' x i (he x) (hG x),add_comm (F y)] at hQ
    exact add_right_cancel (hQ.trans (char_two _).symm)
  apply le_antisymm (ration_le ..)
  rintro x ⟨hy,hx⟩
  apply (Submodule.Quotient.mk_eq_zero R).mp
  have hz {x} (h : x∈C.band s) : q x=F (π x) := by
    unfold band at h; induction h using Submodule.span_induction with
    | zero => rw [map_zero,map_zero,h0]
    | mem x hx =>
      obtain ⟨i,hi,rfl⟩ := hx; exact (hq i hi).symm
    | add a b _ _ ha hb => rw [map_add,map_add,hh,ha,hb]
    | smul a b _ hb =>
      rcases bit_cases a with ha|ha
      · rw [ha,zero_smul,map_zero,map_zero,h0]
      rw [ha,one_smul,hb]
  change q x=0; change π x=0 at hx
  rw [hz hy,hx,h0]
end Club
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FreshGeneratorCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fresh Generator Correction -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function LinearMap Submodule Module
open scoped BigOperators
namespace StatusAnalysis
variable {L I X Y : Type} [DecidableEq L] [DecidableEq I]
variable [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
namespace Club
variable (C : Club I X L)

omit [DecidableEq L] [DecidableEq I] [AddCommGroup X] [Module F X] in
theorem bundle_back {p : Finset I} {s t : Straps L} (ht : s≤t) (h : bundle C p t) :
    bundle C p s := ⟨fun i hi=> zone_smaller C ht i (h.1 i hi),h.2⟩
omit [AddCommGroup X] [Module F X] in
theorem bundle_combine {p q : Finset I} {s : Straps L} (h : bundle C p s)
    (hQ : bundle C q (s⊔addrs C p)) :
    bundle C (p∪q) s∧ Disjoint p q := by
  classical
  have he {i j} (hi:i∈q) (hj:j∈p) : different C i j := fun b ht => (hQ.1 i hi).2 b
    (mem_union_right _ (mem_image.mpr ⟨j,hj,Eq.symm ht⟩))
  refine ⟨⟨fun i h'=>?_, fun b i hi j hj ht=>?_⟩,
    Finset.disjoint_left.mpr (fun i hi ht=> (he ht hi) true rfl)⟩
  · rcases mem_union.mp h' with hp|hp
    · exact h.1 i hp
    exact (bundle_back C le_sup_left hQ).1 i hp
  rcases mem_union.mp hi with hi|hi <;> rcases mem_union.mp hj with hj|hj
  · exact h.2 b hi hj ht
  · exact (he hj hi b ht.symm).elim
  · exact (he hi hj b ht).elim
  exact hQ.2 b hi hj ht

private theorem binary_word {x z : X} (h : z∈ Submodule.span F {x}) :
    z=0 ∨ z=x := by
  obtain ⟨a,ha⟩ := (Submodule.mem_span_singleton.mp h)
  rcases bit_cases a with h|h <;> simpa [h,eq_comm,ha] using (by
    simp [h] at ha; tauto : z=0∨z=x)

omit [DecidableEq I] in
theorem travel_more {s : Straps L} {a b : ℕ} {π : X→ₗ[F] Y} {V}
    (h : C.travels s a π V) {n : ℕ} (t : Straps L) (ht : sizeB t b) (hh : n+b ≤ a) :
    C.travels (s⊔t) n π V := by
  intro u hu
  rw [sup_assoc]
  apply h
  exact fun i=> (Finset.card_union_le ..).trans
    ((Nat.add_le_add (ht i) (hu i)).trans (add_comm b n ▸ hh))
omit [DecidableEq I] in
theorem travel_now {s : Straps L} {a : ℕ} {π : X→ₗ[F] Y} {V} (h : C.travels s a π V) :
    band C s=V ∧ yield3 C s π := by simpa using h ⊥ (by intro i; change (∅:Finset L).card≤_; simp)

theorem length3_rich {s : Straps L} {a : ℕ} {π : X→ₗ[F] Y} {V} (h : C.travels s a π V) :
    Submodule.span F (C.length3 s π) = V⊓LinearMap.ker π :=
  (ration_eq C s π (travel_now C h).2).trans (congrArg (·⊓LinearMap.ker π) (travel_now C h).1)

variable [Module.Finite F X]
set_option maxHeartbeats 1000000 in
theorem jump_two {s : Straps L} {π : X →ₗ[F] Y} {V : Space X}
    (h : C.travels s 3 π V)
    (he : dim (V ⊓ LinearMap.ker π : Space X) ≤ 2) (x : X) (hx : x∈ V⊓LinearMap.ker π) :
    ∃ p:Finset I,C.bundle p s∧p.card≤6∧C.contents p=x := by
  classical
  by_cases h0 : x=0
  · obtain ⟨p,h1,h2,h3,_⟩:=length3_zero C s π
    exact ⟨p,h1,h2.trans (by decide),h3.trans h0.symm⟩
  let R := V⊓LinearMap.ker π
  have hh {t : Straps L} {i : ℕ} (h : C.travels t i π V)
      (Q : Space X) (e : x∉Q) :
      ∃ y,y∈R∧C.length3 t π y∧y∉Q := by
    rw [←length3_rich C h] at hx
    by_contra! hg
    apply e
    exact (Submodule.span_le.mpr (fun i (hi : C.length3 _ _ _) =>
      hg i ((length3_rich C h).le (Submodule.subset_span hi)) hi)) hx
  obtain ⟨y,hy,⟨p,hp,hP,hQ,hd⟩,ht⟩:=hh h ⊥ (by simpa using h0)
  have hy' : y≠0 := by simpa using ht
  let S:=Submodule.span F {y}
  by_cases hh1 : x∈ S
  · exact ⟨p,hp,hP.trans (by decide),hQ.trans (((binary_word hh1).resolve_left h0).symm)⟩
  let T:=s⊔C.addrs p
  have hT : C.travels T 0 π V := travel_more C h (C.addrs p)
    (fun i=>card_image_le.trans hP) (Nat.le_refl 3)
  obtain ⟨z,hz,⟨q,hq,hq',hZ,_⟩,hv⟩:=hh hT S hh1
  let B:=Submodule.span F {z}
  have hm : S⊔B=R := by
    have hk : S⊔B≤ R := sup_le ((Submodule.span_singleton_le_iff_mem ..).mpr hy)
      ((Submodule.span_singleton_le_iff_mem ..).mpr hz)
    have hh:= Submodule.finrank_sup_span_singleton hv
    have ht : dim S=1 := finrank_span_singleton hy'
    exact Submodule.eq_of_le_of_finrank_le hk (by
      change dim R≤dim (S⊔B : Space X)
      change dim (S⊔B : Space X) = dim S+1 at hh
      rw [hh,ht]; exact he)
  obtain ⟨u,hu,t,ht,hx⟩:= Submodule.mem_sup.mp (show x∈ S⊔B from hm.symm ▸ hx)
  rcases binary_word hu with hA|hA <;> rcases binary_word ht with hB|hB
  · rw [hA,hB,zero_add] at hx; exact (h0 hx.symm).elim
  · rw [hA,hB,zero_add] at hx
    exact ⟨q,bundle_back C le_sup_left hq,hq'.trans (by decide),hZ.trans hx⟩
  · rw [hA,hB,add_zero] at hx; exact ⟨p,hp,hP.trans (by decide),hQ.trans hx⟩
  obtain ⟨hg,hD⟩:=bundle_combine C hp hq
  refine ⟨p∪q,hg,(card_union_le ..).trans (by omega),?_⟩
  rw [contents,Finset.sum_union hD]; change C.contents _+_=_
  exact (congrArg₂ (·+·) (hQ.trans hA.symm) (hZ.trans hB.symm)).trans hx
end Club
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ReservedLabels
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reserved Labels -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Function Finset
open scoped BigOperators
namespace StatusAnalysis
variable {I L : Type} [DecidableEq L] [DecidableEq I] {d e : ℕ}
open Club
set_option maxHeartbeats 600000 in
theorem fresh_single (C : Club I (Signal d e) L) {s : Straps L} {V}
    (h : C.travels s 4 (view d e) V) (x : Signal d e) (hx : x∈V) :
    ∃ p:Finset I,C.bundle p s∧ C.contents p=x∧1≤p.card∧p.card≤7 := by
  classical
  obtain ⟨hh,hC⟩:= C.travel_now h
  let Q:= view d e
  obtain ⟨i,hi,hI,_⟩:= C.yield_after s Q hC ∅ (by simp) (Q x)
  let p : Finset I:= {i}
  have hp := C.bundle_one s hi
  have hr : C.travels (s⊔ C.addrs p) 3 Q V := C.travel_more h (C.addrs p)
    (fun i=>card_image_le.trans (by unfold p; simp : p.card≤1)) (by norm_num)
  obtain ⟨q,hq,hQ,hT⟩ := jump_two C hr (ker_two _) (x-C.writes i) (by
    constructor
    · exact Submodule.sub_mem _ hx (hh ▸ C.band_write s hi)
    change Q (x-C.writes i)=0
    rw [map_sub,hI,sub_self])
  obtain ⟨ha,hb⟩:= C.bundle_combine hp hq
  refine ⟨p∪q,ha,?_,?_,(card_union_le ..).trans ?_⟩
  · change ∑ j∈p∪q,_=_
    rw [sum_union hb, ←show C.contents q=(∑ j∈q,_) from rfl, hT]
    simp only [sum_singleton,add_sub_cancel]
  · exact card_pos.mpr ⟨i, mem_union_left _ (by simp [p])⟩
  simp only [p,card_singleton]
  omega

variable {I : Grid → Type} [∀ i,DecidableEq (I i)] {A B : Rates}
namespace Guild
variable (C : Congress I A B L)

omit [DecidableEq L] [∀ i,DecidableEq (I i)] in
theorem excess_bound (s : Straps L) : excess C s ≤8 := by
  unfold excess
  exact (Finset.sum_le_sum (g:=fun _=>2) (fun i _=>overage_two
    (chapter C s i))).trans_eq (by norm_num [Grid,Nodes])

omit [DecidableEq L] [∀ i,DecidableEq (I i)] in
theorem chapter_mono {s t : Straps L} (h : s≤t) (i) :
    chapter C t i ≤ chapter C s i := span_mono (fun _ ⟨a,ht,hx⟩=>
  ⟨a,(C i).zone_smaller h a ht,hx⟩)

omit [DecidableEq L] [∀ i,DecidableEq (I i)] in
theorem rich_covers (h : rich C) (s : Straps L) (hs : sizeB s 902) (i) :
    coverBase (chapter C s i) := by
  intro y
  obtain ⟨j,hj,hy⟩:=h i s hs y
  exact ⟨⟨_, (C i).band_write s hj⟩,hy⟩

set_option maxHeartbeats 800000 in
omit [∀ i,DecidableEq (I i)] in
theorem stable (h : rich C) :
    ∃ s:Straps L,sizeB s 800 ∧
      ∀ i:Grid,(C i).travels s 100 (view _ _) (chapter C s i) := by
  classical
  have hh (k : ℕ) (hk : k≤ 8) (t : Straps L)
      (ht : sizeB t ((8-k)*100)) (hb : excess C t≤ k) :
      ∃ s:Straps L,sizeB s 800 ∧
      ∀ i:Grid,(C i).travels s 100 (view _ _) (chapter C s i) := by
    induction k generalizing t with
    | zero =>
      refine ⟨t,ht,fun i u hu=>?_⟩
      let v:=t⊔u
      have he : sizeB v 900:= fun i=> (card_union_le ..).trans (Nat.add_le_add (ht i) (hu i))
      constructor
      · change chapter C v i=chapter C t i
        have hm (i:Grid) : overage (chapter C t i)=0 := by
          have hy : overage (chapter C t i) ≤ 0 := le_trans (Finset.single_le_sum (s:=Finset.univ)
            (fun i _=>Nat.zero_le (overage (chapter C t i))) (Finset.mem_univ i)) hb
          exact Nat.eq_zero_of_le_zero hy
        exact eq_of_le_of_not_lt (chapter_mono C le_sup_left i) (fun hx=> Nat.not_lt_zero _
          ((overage_lt hx (rich_covers C h v (fun i=> (he i).trans (by decide)) i)).trans_eq (hm i)))
      intro w hw y
      exact h i (v⊔w) (fun i=> (card_union_le ..).trans (Nat.add_le_add (he i) (hw i))) y
    | succ k ih =>
      have hT : sizeB t 800 := fun i=> (ht i).trans (by omega)
      by_cases hE : ∃ (s:Straps L), sizeB s 100∧∃ i:Grid, chapter C (t⊔s) i < chapter C t i
      · obtain ⟨u,hu,i,hU⟩:=hE
        let s:=t⊔u
        have he : sizeB s ((8-k)*100):= fun i=> (card_union_le ..).trans
          ((Nat.add_le_add (ht i) (hu i)).trans (by omega))
        refine ih (by omega) s he ?_
        have hS : excess C s < excess C t := by
          unfold excess
          have h1 := overage_lt hU (rich_covers C h s (fun i=> (he i).trans (by omega)) i)
          exact Finset.sum_lt_sum (fun i _=> overage_mono (chapter_mono C le_sup_left i))
            ⟨i,mem_univ _,h1⟩
        omega
      refine ⟨t,hT,fun i u hu=>?_⟩
      constructor
      · exact eq_of_le_of_not_lt (chapter_mono C (s:=t) (t:=t⊔u) le_sup_left i) (fun hx =>
          hE ⟨u,hu,i,hx⟩)
      intro w hw y
      have he : sizeB (t⊔u) 900:= fun i=> (card_union_le ..).trans (Nat.add_le_add (hT i) (hu i))
      exact h i ((t⊔u)⊔w) (fun i=> (card_union_le ..).trans (Nat.add_le_add (he i) (hw i))) y
  exact hh 8 (Nat.le_refl _) ⊥ (by intro i; change (∅:Finset L).card ≤_; simp) (excess_bound C _)
end Guild
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FourEdgeFamilies
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Four Edge Families -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Finset Function
open scoped BigOperators
namespace StatusAnalysis
variable {A B : Rates} {I : Grid→Type} {L : Type} [DecidableEq L] [∀ i,DecidableEq (I i)]
namespace Guild
open Club
variable (C : Congress I A B L)

set_option maxHeartbeats 800000 in
theorem full_parade (s : Straps L) {v : ∀ i,Suite A B i}
    (ht : ∀ i:Grid,(C i).travels s 100 (view _ _) (chapter C s i))
    (hv : ∀ i, v i∈chapter C s i) :
    ∃ g, Parade C s v g Finset.univ := by
  classical
  have he (p:Finset Grid) :
      ∃ g, Parade C s v g p := by
    induction p using Finset.induction_on with
    | empty =>
      exact ⟨fun _=>∅,⟨fun i hi=> (notMem_empty i hi).elim,
        fun i _ hi=> (notMem_empty i hi).elim⟩⟩
    | insert i p hi ih =>
      obtain ⟨g,hg⟩:=ih
      let Q (b : Bool) := p.biUnion (fun i=> (C i).addrs (g i) b)
      have hh (b) : (Q b).card≤28 := by
        have he (i:Grid) (h:i∈p) : ((C i).addrs (g i) b).card≤7 :=
          Finset.card_image_le.trans (hg.batch i h).2.2.2
        refine (Finset.card_biUnion_le).trans ((Finset.sum_le_sum he).trans ?_)
        have hh : p.card≤4 := p.card_le_univ.trans_eq (by simp [Grid,Nodes])
        simp only [Finset.sum_const,nsmul_eq_mul, Nat.cast_id]; omega
      let V:= chapter C s i
      have hr : (C i).travels (s⊔Q) 4 (view _ _) V := (C i).travel_more (ht i) Q hh (by norm_num)
      obtain ⟨t,ht,hT,hA,hB⟩:=fresh_single (C i) hr (v i) (hv i)
      let f:=update g i t
      have hC (j) (h:j∈p) (x : I j) (hx:x∈f j) (y : I i) (hy:y∈t) (b) :
          (C j).addr x b≠ (C i).addr y b := by
        intro hz
        apply ((ht.1 y hy).2 b)
        refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,h,?_⟩)
        unfold f at hx
        rw [Function.update_of_ne (show j ≠ i from fun e=>hi (e ▸ h))] at hx
        exact Finset.mem_image.mpr ⟨x,hx,hz⟩
      refine ⟨f,⟨fun j hj=>?_,fun j k hj hk he x hx y hy b=>?_⟩⟩
      · rcases Finset.mem_insert.mp hj with hj|hj
        · subst j; unfold f; rw [update_self]
          exact ⟨Club.bundle_back _ le_sup_left ht,hT,hA,hB⟩
        unfold f; rw [update_of_ne (show j ≠ i from fun h=>hi (h ▸ hj))]
        exact hg.batch j hj
      rcases Finset.mem_insert.mp hj with hj|hj
      · subst j; exact Ne.symm (hC k ((Finset.mem_insert.mp hk).resolve_left (Ne.symm he)) y hy x
          (by simpa only [f,update_self] using hx) b)
      rcases Finset.mem_insert.mp hk with hk|hk
      · subst k; exact hC j hj x hx y (by simpa only [f,update_self] using hy) b
      unfold f at hx hy
      rw [update_of_ne (show j ≠ i from fun h=>hi (h ▸ hj))] at hx
      rw [update_of_ne (show k ≠ i from fun h=>hi (h ▸ hk))] at hy
      exact hg.mixed j k hj hk he x hx y hy b
  exact he _
end Guild
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_UnaryPositivityBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unary Positivity Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function Filter
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
namespace Template
variable (v : Solo p)

variable {K s : ℕ}

theorem basebeta_pos (p : Shape) (K : ℕ) : 0<basebeta p K :=
  mul_pos (bp_pos _) (scanPrice_pos _)

set_option maxHeartbeats 800000 in
theorem patrol_beta (v : Solo p)
    (S : AtomKey (p:=p) (v.t ()) N→ Prop) (m : Mixer p n) (K : ℕ)
    (z : Digest p.g) (hz : z.feasible (v.t ()) (v.f ())) (hr : 1 ≤ p.r) (hn : 2*p.r≤n)
    (o : Orient p n N) :
    let l := v.t (); let t := v.f (); let q := z.sumBit
    let u := lawOmega p N l q
    patrol v m (scopedScan p n l t z) S K q o →
    ∀ d : ℕ,d≤ K^2 → ∀ f : Vec (Fin d)→ₗ[F] Profile p n,
      Injective f → (∀ x,totalRank (f x)≤K) → ∀ x,
      basebeta p K*pr u S ≤
        pr (scopedBit p n l t q) (fun i=> (scan p l t i=z∧ (offBeat v S o) i) ∧ stains v m f i=x) := by
  classical
  intro l t q u h d hd f hf hx x
  let Q := offBeat v S o; let F (j : Knobs p.g n) := scan p l t j=z
  let w := spins p n; let R (j : Knobs p.g n) := dialed p l t j=q
  let v' := onW w F
  have hw := spins_law p n
  have hv' := scanLaw (n:=n) p l z t hr hn hz
  let Z i := stains v m f i=x
  let A := pr u S; let a := pr v' Q
  have hA : 0 ≤ A := pr_nonneg (unifOn_sub _).nz
  obtain ⟨⟨ha,hh⟩,he⟩ := h
  specialize hh d hd f hf hx x
  have ht : ∀ i,(F i ∧ Q i)∧Z i → R i := fun i h=> congrArg Digest.sumBit h.1.1
  let B := fun i=> (F i ∧ Q i) ∧ Z i
  have hi : pr w B=pr w F*(a * pr (onW v' Q) Z) := by
    rw [show B=(fun i => F i ∧ Q i∧Z i) from funext fun i=>propext and_assoc]
    rw [pr_of_on hw.nz F]; congr 1
    exact pr_of_on hv'.nz Q Z
  have hY : 0 < pr w R :=
    (scanPrice_pos _).trans_le (dial_fraction p n l t q hr hn ⟨z,hz,rfl⟩)
  have hL : (7/8:ℝ)*bp (- (d:ℝ)) ≥ 7/8*bp (- ((K^2:ℕ):ℝ)) :=
    mul_le_mul_of_nonneg_left (bp_le (by exact_mod_cast neg_le_neg (by exact_mod_cast hd :
      (d:ℝ)≤((K^2:ℕ):ℝ)))) (by norm_num)
  change _≤pr (onW w R) B
  have hR : pr w B≤ pr (onW w R) B := by
    rw [pr_on,show (fun x=> R x∧ B x)= B from funext fun i=>propext ⟨And.right,fun h=>⟨ht i h,h⟩⟩]
    exact (by
      rw [le_div_iff₀ hY]
      have hh := (pr_le_tot (p:=R) hw.nz).trans hw.total.le
      exact (mul_le_mul_of_nonneg_left hh (pr_nonneg hw.nz)).trans_eq (mul_one _))
  apply le_trans ?_ hR
  rw [hi]; unfold basebeta; rw [bp_sub,bp_one]
  let K' := bp (-((K^2:ℕ):ℝ))
  have hg : scanPrice p*( (3/4*A)*(7/8*K')) ≤ pr w F*(a * pr (onW v' Q) Z) :=
    mul_le_mul (scan_fraction l t z hr hn hz)
      (mul_le_mul he (le_trans hL hh) (mul_nonneg (by norm_num) (bp_pos _).le) ha.le)
      (mul_nonneg (mul_nonneg (by norm_num) hA) (mul_nonneg (by norm_num) (bp_pos _).le))
      (pr_nonneg hw.nz)
  refine le_trans ?_ hg
  change K' / 2 * _ * _ ≤ _
  nlinarith only [mul_nonneg (mul_nonneg (scanPrice_pos p).le
    (show 0≤K' from (bp_pos _).le)) hA]

end Template
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

theorem chart_create (p : Shape) (n : ℕ) (w : Plan p n) :
    let d:= fun i:Nodes=> dim (effective w i)
    ∃ v : Charts p n d,charted v w := by
  classical
  intro d
  have hh (i) :
      ∃ f : Ax p n (d i),LinearMap.range f=effective w i ∧ Injective f := by
    let S:= effective w i
    let E : Cell (d i)≃ₗ[F] S := LinearEquiv.ofFinrankEq _ _
      (by change dim (Cell (d i))=d i; rw [dim_vec,Fintype.card_fin])
    refine ⟨S.subtype ∘ₗ E.toLinearMap,?_,Subtype.val_injective.comp E.injective⟩
    rw [LinearMap.range_comp,LinearMap.range_eq_top.mpr E.surjective,← LinearMap.range_eq_map,
      Submodule.range_subtype S]
  choose f h using hh
  exact ⟨f,h⟩

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

theorem nomen_fits (p : Shape) (n : ℕ) (a b : Plan p n) (x y : Cross p n)
    (h : nomen p a b x=nomen p a b y) :
    fitsTable a b x y := by
  intro i j hj k hk
  obtain ⟨u,rfl⟩: ∃ v, pack (tabSpace a i)*ᵥv=j := by
    exact (pack_mem_iff ..).mp hj
  obtain ⟨v,rfl⟩: ∃ v, pack (tabSpace b (flipZ p i))*ᵥv=k := (pack_mem_iff ..).mp hk
  simp_rw [← evmat_pull]; exact congrArg (fun t=>evmat t u v) (congr_fun h i)

theorem deck_cap (p : Shape) (n : ℕ) (K : ℕ)
    (a b : Plan p n) (h : planRank a ≤ K) (hg :planRank b ≤ K) :
    Fintype.card (CouponDeck p a b) ≤ 2^ deckMax p K := by
  classical
  have ht :
      dim (CouponDeck p a b)=∑ i:Place p,dim (tabSpace a i)*dim (tabSpace b (flipZ p i)) := by
    unfold CouponDeck dim; rw [Module.finrank_pi_fintype]
    refine Finset.sum_congr rfl fun i _=>?_
    rw [show Module.finrank F _ = _ from dim_mat (Fin (dim (tabSpace a i)))
      (Fin (dim (tabSpace b (flipZ p i)))),Fintype.card_fin,Fintype.card_fin]
  have he (i) : dim (tabSpace a i)*dim (tabSpace b (flipZ p i)) ≤ (2*(K+p.h))^2 := by
    rw [pow_two]; exact Nat.mul_le_mul ((table_dim ..).trans (by omega)) ((table_dim ..).trans
      (by omega))
  have hi : dim (CouponDeck p a b) ≤ deckMax p K := ht ▸
    (Finset.sum_le_sum (fun i _=>he i)).trans_eq (by rw [Finset.sum_const]; exact
      (by simp [deckMax]))
  have hh := card_space (CouponDeck p a b)
  have hx : (↑(Fintype.card (CouponDeck p a b)) : ℝ)≤2^deckMax p K := hh.le.trans
    ((bp_le (by exact_mod_cast hi : (dim (CouponDeck p a b):ℝ) ≤ deckMax p K)).trans_eq (bp_nat _))
  exact_mod_cast hx

theorem deck_cast (p : Shape) (n : ℕ) (K : ℕ)
    (a b : Plan p n) (h : planRank a ≤ K) (hg :planRank b ≤ K) :
    ∃ M : Fin (2^deckMax p K)→Cross p n,∀ v,∃ i,fitsTable a b (M i) v := by
  classical
  let A := CouponDeck p a b
  let f := nomen p a b
  choose w he using fun x : A =>
    show ∃ y:Cross p n,∀ z,f z=x → f y=x from (by
      by_cases h : ∃ z,f z=x
      · obtain ⟨z,hz⟩:=h; exact ⟨z,fun _ _=>hz⟩
      exact ⟨0,fun i hi=>(h ⟨i,hi⟩).elim⟩)
  let t := Fintype.card A
  let e := Fintype.equivFin A
  let g (x : Fin (2^deckMax p K)) := if h : x.val<t then w (e.symm ⟨x.val,h⟩) else 0
  have hk : t≤2^deckMax p K := deck_cap p n K a b h hg
  refine ⟨g,fun v=>?_⟩
  let i:=e (f v); let z:Fin (2^deckMax p K):= Fin.castLE hk i
  refine ⟨z,nomen_fits p n _ _ _ _ ?_⟩
  change f (g z)=f v
  unfold g; rw [dite_eq_left (show z.val<t from i.isLt)]
  exact (by change f (w (e.symm (e (f v))))=f v; rw [Equiv.symm_apply_apply]; exact he _ _ rfl)

theorem fits_flag (M T : Cross p n) (a b : Pin p n N) (x : UnitType p n N)
    (hf : fitsTable a.sp b.sp M T) (h : tableFlag a b T x) : tableFlag a b M x :=
  fun i j hj k hk=> (hf i j hj k (pin_le_table b.sp _ hk)).trans (h i j hj k hk)
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConditionalFlags
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional Flags -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A B C X Y : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype X] [Fintype Y]
variable {w : Wgt X}

theorem stained_law (f : X→Y) (hw : IsLaw w) (i : Y) : IsLaw (stained w f i) := by
  unfold stained; split
  next h => exact on_law hw.nz (lt_of_le_of_ne ((mapW_law hw f).nz _) (Ne.symm h))
  next => exact hw

theorem stain_rebuild (f : X→Y) (P : Y→Prop) (hw : IsLaw w) :
    subW w (P∘f) = mixW (subW (mapW w f) P) (stained w f) := by
  classical
  have hh := disintegrate hw.nz f
  funext i
  have hi (y) :
      mapW w f y * stained w f y i=
        mapW w f y * onW w (fun x => f x=y) i := by
    by_cases h : mapW w f y=0 <;> simp [stained,h]
  have he := congr_fun hh i
  unfold subW mixW Function.comp
  unfold mixW at he
  rw [he,avg,Finset.sum_mul]
  unfold avg at *
  apply sum_congr rfl
  intro j _
  rw [mul_right_comm _ (ind _), hi]
  by_cases hx : f i=j
  · rw [hx]
  simp only [onW_val,ind_zero hx,mul_zero,zero_div,zero_mul]

theorem stain_inputs (f : X→Y) (hw : IsLaw w) :
    w=mixW (mapW w f) (stained w f) := by
  have ht := stain_rebuild f (fun _ => True) hw
  unfold subW at ht
  simpa only [Function.comp_apply,ind_true,mul_one] using ht

variable {μ : Wgt A}

theorem semi_total (μ : Wgt A) (v : A → Wgt Y) :
    tot (semi μ v)=avg μ (fun i=>tot (v i)) := by
  simpa only [avg_const,mul_one] using semi_avg μ v (fun i=>1)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_WeightedPartitions
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted Partitions -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Finset
variable {A : Type} [Fintype A]

variable {w : Wgt A} {T : Tiles A}

omit [Fintype A] in
theorem ind_tiles (ht : apart T) (x : A) :
    ind (inTiles T x)= ∑ i∈T,ind (x∈i) := by
  classical
  by_cases hh : inTiles T x
  · rw [ind_one hh]
    obtain ⟨i,hi,hx⟩ := hh
    rw [Finset.sum_eq_single i]
    · rw [ind_one hx]
    · intro j hj h; exact ind_zero (fun hc => h (ht x j hj i hi hc hx))
    simp [hi]
  rw [ind_zero hh]
  exact (Finset.sum_eq_zero (fun i hi => ind_zero (fun h => hh ⟨i,hi,h⟩))).symm

theorem tiles_inter (w : Wgt A) (T : Tiles A) (P : A→Prop) (hT : apart T) :
    pr w (fun x => inTiles T x∧P x)= ∑ i∈T,pr w (fun x => x∈i ∧ P x) := by
  unfold pr
  simp_rw [ind_and, ind_tiles hT,Finset.sum_mul,avg_sum]

theorem mass_apart (h : apart T) : allMass w T=∑ i∈T,partMass w i := by
  simpa only [and_true,allMass,partMass] using tiles_inter w T (fun x => True) h

theorem rebuild {T : Tiles A} (hw : ∀ x, 0 ≤ w x)
    (hT : apart T) (he : ∀ i ∈ T, 0 < partMass w i)
    (h : 0 < allMass w T) :
    IsLaw (portionW w T) ∧ allW w T = mixW (portionW w T) (fun i => partW w i.val) := by
  classical
  constructor
  · refine ⟨fun i => div_nonneg (pr_nonneg hw) h.le,?_⟩
    unfold tot portionW
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul,Finset.sum_coe_sort,← mass_apart hT,mul_inv_cancel₀ h.ne']
  funext x
  rw [allW,onW_val,ind_tiles hT]
  unfold mixW avg
  have hg (i:T) :
      portionW w T i* partW w i.val x = w x*ind (x∈i.val)/allMass w T := by
    have hx : pr w (fun x => x∈i.val) ≠ 0 := (he _ i.property).ne'
    unfold portionW partW partMass
    rw [onW_val]; field_simp
  change w x * _ / allMass w T=_
  simp_rw [hg]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul,← Finset.mul_sum, Finset.sum_coe_sort T (fun y => ind (x∈y))]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_UltrafilterRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ultrafilter Rates -/

noncomputable section
namespace HadwigerCounterexample
open Filter Real Finset
open scoped Topology

variable {A B : Type} {l : Filter A} {U : Ultrafilter A} {x y z v a : A → ℝ}

namespace warm

theorem positive (h : warm l z x) : ∀ᶠ i in l,0<x i :=
  (h 1 zero_lt_one).mono (fun _ hi => (bp_pos _).trans_le hi)

theorem inv_cap (h : warm l z x) : ExpO l z (fun i=> (x i)⁻¹) := by
  intro c hc
  filter_upwards [h c hc] with i hi
  rw [abs_of_nonneg (inv_nonneg.mpr ((bp_pos _).le.trans hi))]
  exact le_trans (inv_anti₀ (bp_pos _) hi) (le_of_eq (by rw [neg_mul,bp_neg,inv_inv]))

end warm

theorem taking {X : A→ Type*} [∀ n,Nonempty (X n)]
    {P : ∀ n,X n→Prop} (h : ∀ᶠ n in l,∃ w:X n,P n w) :
    ∃ w:∀ n,X n,∀ᶠ n in l,P n (w n) := by
  classical
  let f n:= if h:∃ w,P n w then h.choose else Classical.choice (inferInstance:Nonempty (X n))
  refine ⟨f,h.mono (fun n hn=>?_)⟩
  unfold f; rw [dite_eq_left hn]; exact hn.choose_spec

theorem trend_sizes (l : Filter ℕ) (h : l ≤ atTop) {M : ℕ} (hM : 1≤ M) :
    Tendsto (fun n=> M*n) l atTop ∧ Tendsto (fun n=> ((M*n:ℕ):ℝ)) l atTop := by
  have hh : Tendsto (fun n : ℕ=> M*n) atTop atTop := tendsto_atTop.mpr (fun a =>
    (eventually_ge_atTop a).mono (fun k hk=> le_trans hk (by nlinarith)))
  exact ⟨hh.mono_left h, tendsto_natCast_atTop_atTop.comp (hh.mono_left h)⟩

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
namespace PredictionClass

theorem dusk_lit (α : Party) (h : dusk.lit α) : ∀ i,α i = 1 := fun i=>by
  have hh : 1+α i=0 := h.1 i not_false
  exact add_left_cancel (hh.trans (char_two 1).symm)
end PredictionClass

open PredictionClass

theorem lone (p : Shape) {n N} (x : UnitType p n N) (i : Bool) (v : Ambient p N) :
    tone p x (unary i) v= ufun (onSide x i) v := by
  classical
  unfold tone joinPhase unary; rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same,one_smul]
    rw [show onSide (listens p x) i=hcube p (onSide x i) from by cases i<;>rfl, phase_actual]
  · intro j _ h; simp [h]
  simp

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_LeafMixtures
attribute [-instance] _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

variable {s : LeafMixture p n N} {w μ : Wgt (X p n N)}
variable {D E ζ η : ℝ} {K L : ℕ}

theorem sapLaw (h : 0 < s.amount w) (hw : IsLaw w) : IsLaw (s.sap w) := on_law hw.nz h

theorem upper_sap (hw : IsLaw w) (hp : 0 < s.amount w) (x) :
    s.sap w x ≤ (s.amount w)⁻¹*w x :=
  on_mon hw.nz hp le_rfl x
theorem upperSide {N n} {Lr K' : ℝ} {w v : Wgt (X p n N)} {m : Mixer p n} (hp : bySide p w m Lr)
    {Lr' : ℝ} (h : ∀ x,v x≤K'*w x) (hk : 0≤K') (hh : K'*Lr ≤ Lr') :
    bySide p v m Lr' := by
  intro i x
  refine (mapW_cap h _ x).trans ?_
  calc _ ≤ K'*(Lr*raw m N x) := mul_le_mul_of_nonneg_left (hp i _) hk
       _ ≤ _ := by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right hh (raw_nonneg m _)

end LeafMixture
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PairedOptions
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Paired Options -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Finset Submodule Function
open scoped BigOperators
namespace StatusAnalysis
variable {p : Shape} {n N K : ℕ}

variable {q : Format} {d e : Rates}

namespace Station
variable {s : LeafMixture p n N} (v : Station p n N K s)

theorem create (h : ∀ i:s.T, planRank (s.pin i.val).sp ≤K) :
    ∃ v : Station p n N K s,v.bank := by
  classical
  let d (i:s.T) j:=dim (effective (s.pin (Subtype.val i)).sp j)
  choose F hF using fun i:s.T=> chart_create p n (s.pin i.val).sp
  choose G hG using fun i j:s.T=> deck_cast p n K (s.pin i.val).sp (s.pin j.val).sp (h i) (h j)
  let axes (i:s.T) (r:Rates): Charts p n r := if ht:r=d i then ht ▸ (F i) else fun _=>0
  refine ⟨⟨axes,G⟩,fun i=>?_,hG⟩
  change charted (axes i (d i)) _
  unfold axes; rw [dite_eq_left rfl]; exact hF i

end Station
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AnalyticParameters
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Analytic Parameters -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix
open scoped BigOperators Topology
open StatusAnalysis StatusAnalysis.Station

namespace PreparationParameters
variable {b : PreparationParameters} {p : Shape} {N M r : ℕ} {l : Filter ℕ} {m : cycleM p}
  {s : rhythms p M} {w : tale p M}

set_option maxHeartbeats 1200000 in
theorem veil.upright (h : veil p M b r l m s w) :
    ∀ᶠ n in l,Align b r p M n (m n) ((s n).sap (w n)) := by
  let z n:= ((M*n:ℕ):ℝ)
  have ht := h.easel.enter.first
  have hM : 1 ≤ (M:ℝ) := by exact_mod_cast ht.hM
  let e : ℝ := 1/(128*M)
  have he : 0< e:=by unfold e; positivity
  have hz := (trend_sizes l h.timeL ht.hM).2
  let D n:=((s n).amount (w n))⁻¹
  filter_upwards [h.moment,h.durableS.mass.inv_cap e he,
    h.durableS.mass.positive,expO_const hz b.L e he, ht.wrap.filter_mono h.timeL,
    (eventually_ge_atTop (2*p.r)).filter_mono h.timeL] with n hn he' ht' hL hG hH
  have hw := hn.1.law
  have h1 (i) := LeafMixture.upper_sap hw ht' i
  have h2 : 0≤D n := (inv_pos_of_pos ht').le
  have hB : D n * b.L ≤ bp (1/32*(n:ℝ)) := by
    have hi : e*z n=(1/128)*(n:ℝ) := by unfold e z; push_cast; field_simp
    calc _ ≤ bp (e*z n)*bp (e*z n) :=
           mul_le_mul ((le_abs_self _).trans he') ((le_abs_self _).trans hL) ht.early.hL
             (bp_pos _).le
         _ ≤ _ := by rw [←bp_add,hi]; apply bp_le; linarith [(Nat.cast_nonneg n :0≤(n:ℝ))]
  have hv := LeafMixture.upperSide hn.1.border h1 h2 hB
  refine ⟨hn.2.2.1,hn.2.1,hH,hG.1, LeafMixture.sapLaw ht' hw, hv true,hv false,fun i=>?_⟩
  have hh := hn.1.total i
  apply ((h1 i).trans (mul_le_mul_of_nonneg_left hh h2)).trans
  rw [←mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (raw_nonneg ..) (raw_nonneg ..))
  have hx : e ≤1 := by unfold e; exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  refine (mul_le_mul_of_nonneg_right ((le_abs_self _).trans he') (bp_pos _).le).trans ?_
  rw [←bp_add]
  unfold spJoint; refine bp_le ?_; rw [←add_mul]
  exact mul_le_mul_of_nonneg_right (by linarith only [hx]) (by positivity)
end PreparationParameters
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SurrogateStatusLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Surrogate Status Laws -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology

variable {A B C H : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype H]
variable {p : Shape} {n N K M r : ℕ}

namespace StatusAnalysis

namespace Appearance
variable (x : Appearance p)
theorem witLaw {x : Appearance p} (h : x.apt) (hq : 1≤p.r) (hn : 2*p.r≤n) :
    IsLaw (x.wit n) := dial_law _ _ _ _ _ hq hn h

variable (Y : Silhouette p N r)

variable {d : ℕ}

theorem reflectedLaw (h : IsLaw (x.wit n)) (i : Nodes)
    (o : UnitType p n N) (m : Mixer p n) (v : Ax p n d)
    (a : Fin r) : IsLaw (x.reflected Y i o m v a) :=
  mapW_law (stained_law _ h _) _

end Appearance

omit [Fintype B] in
private theorem stained_except (w : Wgt A) (f : A→B) (x : B)
    (hx : mapW w f x ≠0) :
    carried (stained w f x) (fun i=> f i=x) := by
  unfold stained; rw [ite_eq_left hx]
  exact normW_carried (subW_carried w _)

theorem inside_color (w : Wgt A) (hw : IsLaw w) (f : A→B) (r : A→C)
    (u : B→C→ℝ) :
    avg w (fun i=> u (f i) (r i)) = avg (mapW w f) (fun i=>avg (mapW (stained w f i) r) (u i)) := by
  classical
  let d i:= u (f i) (r i)
  calc avg w d = avg (mixW (mapW w f) (stained w f)) d := congrArg (fun w=>avg w d)
         (stain_inputs f hw)
       _ = _ := by
        rw [mixW_avg]
        refine avg_congr fun i hi=> ?_
        rw [mapW_avg]
        refine avg_congr fun j hj=> ?_
        have he : f j=i := not_not.mp (fun h=>hj (stained_except w f i hi j h))
        unfold d; rw [he]

theorem varError (w v : Wgt A) (f : A→ℝ) (h : ∀ i, |f i|≤1) :
    |avg w f-avg v f| ≤ varOne w v := by
  unfold avg varOne
  rw [←sum_sub_distrib]
  refine (abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun i _=> ?_)
  rw [← sub_mul,abs_mul]; exact (mul_le_mul_of_nonneg_left (h _) (abs_nonneg _)).trans_eq (mul_one _)

namespace Appearance
variable (x : Appearance p) (Y : Silhouette p N r)
variable {d : ℕ}

theorem close_expect (i : Nodes) (o : UnitType p n N) (m : Mixer p n) (v : Ax p n d)
    (hw : IsLaw (x.wit n)) (u : Fin r → Magazine p d→ ℝ) (hu : ∀ i j, |u i j| ≤ 1)
    {ε : ℝ} (h : x.close Y (onSide o i) ε) :
    |avg (x.reference Y) (fun a=> avg (x.reflected Y i o m v a) (u a))-
     avg (x.wit n) (fun a=>u (x.showTag Y (onSide o i) a) (x.profile i o m v a))|≤ ε := by
  rw [inside_color _ hw]
  refine le_trans (varError (x.reference Y) (x.empirical Y (onSide o i)) _ (fun j=>?_)) h
  let w := x.reflected Y i o m v j
  have he : IsLaw w:= x.reflectedLaw Y hw i o m v j
  exact (abs_avg_le he.nz).trans ((avg_mono he.nz (hu j)).trans_eq (he.avg_const _))

theorem show_pr (i : Nodes) (o : UnitType p n N) (m : Mixer p n) (v : Ax p n d)
    (hw : IsLaw (x.wit n)) (j : Fin r) (U : Magazine p d→Prop) :
    pr (x.wit n) (fun y => x.showTag Y (onSide o i) y=j∧ U (x.profile i o m v y))=
      x.empirical Y (onSide o i) j * pr (x.reflected Y i o m v j) U := by
  classical
  rw [pr_of_on hw.nz]
  unfold reflected empirical
  rw [mapW_pr]
  let f:=x.showTag Y (onSide o i)
  let w:= x.wit n
  by_cases h : mapW w f j ≠0
  · unfold stained; rw [ite_eq_left h]; rfl
  have hh : pr w (fun y=> f y=j)=0 := not_not.mp h
  change pr w _*_=pr w _ * _
  rw [hh,zero_mul,zero_mul]

theorem reflection_exact (i : Nodes) (o : UnitType p n N) (m : Mixer p n) (v : Ax p n d)
    (j : Fin r) (P : Magazine p d→Prop)
    (hw : carried (x.wit n) (P ∘ x.profile i o m v)) :
    carried (x.reflected Y i o m v j) P := by
  unfold reflected
  let f := P∘x.profile i o m v
  refine mapW_carried (p:=f) ?_ (fun _ hh=>hh)
  unfold stained; split
  next h =>
    refine normW_carried ?_; intro a ha
    unfold subW; rw [hw a ha,zero_mul]
  next => exact hw
end Appearance
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConditionalSignaturePositivity
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional Signature Positivity -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
variable {p:Shape} {n N K r d : ℕ}
namespace StatusAnalysis
open Template

namespace Appearance
variable (x : Appearance p) (Y : Silhouette p N r)

theorem smudges (o : UnitType p n N) (m:Mixer p n) (v : Ax p n d) (i:Nodes) (j : Knobs p.g n) :
    (x.profile i o m v j).2.1=((scan p x.l x.f j).diagO,stains x.trot m v j) := by
  apply Prod.ext
  · exact role_scan p _ _ _ _
  funext i; exact T_swap m _ _

set_option maxHeartbeats 800000 in
theorem demonstrates (o : UnitType p n N) {m : Mixer p n}
    (v : Ax p n d) (K:ℕ) (i:Nodes) (j:Fin r) (δ : ℝ) (hd:0<δ)
    (z : Digest p.g) (u:Cell d)
    (he : z.feasible x.l x.f) (hf : z.sumBit=x.q) (ht : 1≤p.r) (hn : 2*p.r≤n)
    (hh : δ≤ x.reference Y j)
    (hs : smoothSilk p δ δ Y m K (onSide o i)) (hK : d≤K^2)
    (hV : Injective v) (hv : ∀ x,totalRank (v x) ≤ K) :
    basebeta p K/2 ≤ pr (x.reflected Y i o m v j) (nearly p z (z.diagO,u)) := by
  classical
  have ha : x.apt := ⟨z,he,hf⟩
  let μ:= x.reference Y j
  let f := onSide o i
  obtain ⟨hM,hB⟩:= hs x
  specialize hM ha
  specialize hB z j he hf hh
  let U (y:AtomKey (p:=p) (x.trot.t ()) N) := Y x.l x.q y=j
  have hm : basebeta p K*μ ≤
      pr (x.wit n) (fun y=> (scan p x.l x.f y=z∧Y x.l x.q (x.face f y)=j) ∧
        stains x.trot m v y=u) := by
    let h := patrol_beta x.trot U m K z he ht hn f
    dsimp only at h
    rw [hf] at h
    exact h hB d hK v hV hv u
  let w := nearly p z (z.diagO,u)
  have hq (y : Knobs p.g n) :
      (scan p x.l x.f y=z ∧ Y x.l x.q (x.face f y)=j) ∧ stains x.trot m v y=u →
        x.showTag Y (onSide o i) y=j∧ w (x.profile i o m v y) := by
    rintro ⟨⟨h,h1⟩,h2⟩
    refine ⟨h1,h,?_⟩; rw [smudges,h,h2]
  have hW := witLaw ha ht hn
  have heq := (hm.trans (pr_mono hW.nz hq)).trans_eq (x.show_pr Y i o m v hW j w)
  let ν:= x.empirical Y f j
  have h2 : ν ≤ 2*μ := by
    have hz : |μ-ν|≤δ := le_trans
      (Finset.single_le_sum (fun k _ => abs_nonneg (x.reference Y k-x.empirical Y f k))
        (Finset.mem_univ j)) hM
    change δ≤ μ at hh
    linarith [(abs_le.mp hz).1]
  let Q := pr (x.reflected Y i o m v j) w
  have h3 : basebeta p K*μ≤ ν*Q := heq
  have ht := mul_le_mul_of_nonneg_right h2
    (show 0≤ Q from pr_nonneg (x.reflectedLaw Y hW i o m v j).nz)
  apply le_of_mul_le_mul_right _ (hd.trans_le hh)
  change _*μ ≤ Q*μ
  linarith only [h3,ht]

theorem rawink (x : Appearance p) (m : Mixer p n) (i : Nodes) (o : UnitType p n N)
    (v : Ax p n d) :
    carried (x.wit n) (x.fitsink ∘ x.profile i o m v) := by
  let w:=x.wit n
  have hC : carried w (fun y=>dialed p x.l x.f y=x.q) :=
    normW_carried (subW_carried (spins p n) _)
  intro y hi
  refine hC y (fun h=>?_); apply hi
  refine ⟨?_,h, (role_scan p _ _ _ _).symm⟩
  intro j hj
  unfold profile; change scan p x.l x.f y j=0
  unfold scan
  simp [hj]
theorem refInk (i : Nodes) (o : UnitType p n N) (m:Mixer p n) (v : Ax p n d)
    (j:Fin r) : carried (x.reflected Y i o m v j) x.fitsink :=
  reflection_exact x Y i o m v j _ (rawink x m i o v)

end Appearance

end StatusAnalysis
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

theorem issueTicket (x y:UnitType p n N) (w : LeafMixture p n N) (t:Station p n N K w)
    (i j:w.T) (ha:apart w.T)
    (hx:x∈i.val) (hy:y∈j.val) (ht:t.bank)
    (he : secureAt p w.rooting (x,y)) :
    ∃ k, berthTicket (w.pin i.val) (w.pin j.val) (t.mails i j k) (x,y) := by
  obtain ⟨k,hk⟩:=ht.2 i j (actual p x y)
  obtain ⟨h1,h2⟩:=he
  let a:= w.pin i.val; let b:= w.pin j.val
  have hh : w.rooting x=a.sp:= congrArg Pin.sp (LeafMixture.poller_eq w ha i.property hx)
  have hg : w.rooting y=b.sp:= congrArg Pin.sp (LeafMixture.poller_eq w ha j.property hy)
  change tableInj (w.rooting x) (w.rooting y) (actual p x y) at h1
  change tableInj (w.rooting y) (w.rooting x) (actual p y x) at h2
  rw [hh,hg] at h1 h2
  rw [← reciprocal_actual] at h2
  exact ⟨k, fits_inj hk h1,fits_inj (fits_recip hk) h2,hk⟩

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteDualSystems
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Dual Systems -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Finset Function LinearMap Module
open scoped BigOperators Topology
open Template
variable {p : Shape} {N n r K : ℕ}
namespace StatusAnalysis

variable {d e : Rates}
namespace DualAnalysis

theorem playbook_pos (p : Shape) (K : ℕ) : 0 < playbook p K := by unfold playbook num; positivity
theorem booklet_cap (p:Shape) (K d e:ℕ) (hd:d≤K^2) (he:e≤K^2) :
    num (Magazine p d × Magazine p e) ≤ playbook p K := by
  have ht (d e) (h:d≤e) :
      Fintype.card (Magazine p d) ≤ Fintype.card (Magazine p e) := by
    simp only [Magazine,Whole,Par,Fintype.card_prod,Cell,Vec,Fintype.card_fun,Fintype.card_fin]
    have hF:0<Fintype.card F := Fintype.card_pos
    gcongr
  unfold num playbook num
  exact_mod_cast (show Fintype.card (Magazine p d × Magazine p e) ≤ _ from by
    simpa only [Fintype.card_prod] using Nat.mul_le_mul (ht _ _ hd) (ht _ _ he))

theorem plume_reports (p:Shape) (K :ℕ) (m:Mixer p n) (Y:Silhouette p N r)
    (s:Plan p n) (t:Charts p n d) (o:UnitType p n N)
    (hs:charted t s) (hh:∀ i,d i≤K^2) (h:planRank s≤K)
    (hg:3≤p.g) (hp:1≤p.r) (hn:2*p.r≤n) (δ:ℝ) (hδ:0<δ)
    (hY:gauze p δ δ Y m K o):
    reports p r (wisp p Y) (wake p Y m o t) (basebeta p K/2) δ := by
  constructor
  · intro i x hx k; exact x.reflectedLaw Y (Appearance.witLaw hx hp hn) _ _ _ _ _
  · intro i x hx k; exact x.refInk Y _ _ _ _ _
  intro i x hx he k hk v
  obtain ⟨g,ha,hb,hc⟩:=generic_summary p hg x.l x.q v.1
  rw [←hx] at ha
  have hf:= x.demonstrates Y o (m:=m) (t i) K i k δ hδ g v.2 ha hb hp hn hk (hY _)
    (hh _) (hs i).2 (fun x=>le_trans (effective_rank (i:=i) (s:=s) (by rw [←(hs i).1]; exact mem_range_self _ _)) h)
  exact hf.trans (pr_mono (x.reflectedLaw Y (Appearance.witLaw he hp hn) i o m (t i) k).nz
    (fun j hj=>hj.2.trans (Prod.ext hc rfl)))

variable (u:Terrain p r) (s:Gazette p r d) (t:Gazette p r e)
  (η:ℝ)

variable {β δ:ℝ}
theorem circlet_state (hu:origami p r u δ) (hs:reports p r u s β δ)
    (ht:reports p r u t β δ)
    (x: Zodiac p) (hx:x.common) (i:Grid):
    IsLaw (circlet u s t x i) ∧ carried (circlet u s t x i)
      (fun y=>(x.aspect true).fitsink y.1 ∧ (x.aspect false).fitsink y.2) := by
  have hh := hu.1 x.l x.q
  refine ⟨mixW_law hh (fun _=>pairW_law (hs.law _ _ (hx _) _) (ht.law _ _ (hx _) _)),?_⟩
  intro y hy
  have hi j : couplePage s t x i j y=0 := by
    by_cases h :(x.aspect true).fitsink y.1
    · unfold couplePage pairW
      rw [ht.supp _ _ (hx _) j _ (fun hh=>hy ⟨h,hh⟩),mul_zero]
    unfold couplePage pairW; rw [hs.supp _ _ (hx _) j y.1 h,zero_mul]
  unfold circlet mixW
  simp_rw [hi,avg_const,mul_zero]

set_option maxHeartbeats 1000000 in
theorem sturdy_contact (hu:origami p r u δ) (hs:reports p r u s β δ)
    (ht:reports p r u t β δ) (hβ:0<β)
    (x: Zodiac p) (hx:x.common) (h:∀ i, x.f i=Flavor.full)
    (i: Grid) (L: Par (d i.1)) (R: Par (e i.2))
    {η:ℝ} (he:0<η) (hη:num (Touch p d e i)*η < 1/2*β^2):
    ∃ j : Touch p d e i, eligible u s t η x i j ∧ j.1.2.1=L∧ j.2.2.1=R := by
  classical
  obtain ⟨hF,hG⟩:= circlet_state u s t hu hs ht x hx i
  let μ:=u x.l x.q
  let Q j:=δ≤μ j
  let Z (j:Touch p d e i):=j.1.2.1=L∧ j.2.2.1=R
  let W:=circlet u s t x i
  have hh:1/2*β^2 ≤ pr W Z := by
    let g:= couplePage s t x i
    have hh : pr W Z=avg μ (fun j=>pr (g j) Z):= mixW_avg ..
    have heq j (hj : Q j) :
       β^2≤ pr (g j) Z := by
      rw [pow_two]
      let P0 (x:Magazine p (d i.1)):= x.2.1=L
      let Q0 (x:Magazine p (e i.2)):= x.2.1=R
      have he := pairW_pr (s i.1 (x.aspect true) j) (t i.2 (x.aspect false) j) P0 Q0
      have hh:=hs.generous i.1 (x.aspect true) (h _) (hx _) j hj L
      exact (mul_le_mul hh (ht.generous i.2 (x.aspect false) (h _) (hx _) j hj R) hβ.le
        (hβ.le.trans hh)).trans_eq he.symm
    refine (mul_le_mul_of_nonneg_right (hu.2 x.l x.q) (sq_nonneg _)).trans ?_
    rw [hh]; unfold pr; rw [←avg_mul]; refine avg_mono (hu.1 _ _).nz (fun j=> ?_)
    change ind (Q j) * β^2 ≤ pr (g j) Z
    by_cases hj:Q j
    · rw [ind_one hj,one_mul]; exact heq _ hj
    rw [ind_zero hj,zero_mul]
    exact pr_nonneg (pairW_law (hs.law _ _ (hx _) j) (ht.law _ _ (hx _) j)).nz
  by_contra! hv
  have hg j : W j * ind (Z j) ≤ η := by
    by_cases h:Z j
    · rw [ind_one h,mul_one]
      by_contra! he'
      have hc : W j≠0:=(he.trans he').ne'
      have h1 : (x.aspect true).fitsink j.1∧(x.aspect false).fitsink j.2 :=
        not_not.mp fun h=> hc (hG _ h)
      exact hv _ ⟨hx,h1.1,h1.2,he'.le⟩ h.1 h.2
    rw [ind_zero h,mul_zero]; exact he.le
  apply hη.not_ge; exact hh.trans ((Finset.sum_le_sum fun i _=>hg i).trans_eq (by simp [num]))

end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RelationMismatchBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relation Mismatch Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Finset Function Submodule LinearMap
open scoped BigOperators Topology
open Template
variable {p:Shape} {N n r K : ℕ}
namespace StatusAnalysis
namespace DualAnalysis
open Club Guild
variable {d e : Rates}
    {u:Terrain p r} {s:Gazette p r d} {t:Gazette p r e}
    {β η δ:ℝ}

theorem any_label (A : Finset (Label p.b)) (h : A.card<Fintype.card (Label p.b)) :
    ∃ x,x∉A := by
  by_contra! hh
  have hf := card_le_card (show univ ⊆ A from fun _ _=>hh _)
  rw [card_univ] at hf; exact h.not_ge hf

theorem generic_apt (p:Shape) (hg:3≤p.g) (x:Appearance p) (hx:x.f=Flavor.full) :
    x.apt := by obtain ⟨s,h1,h2,h3⟩:=generic_summary p hg x.l x.q 0; exact ⟨s,hx ▸ h1,h2⟩

set_option maxHeartbeats 900000 in
theorem plenitude (h:origami p r u δ) (hs:reports p r u s β δ) (ht:reports p r u t β δ)
    (hg:3 ≤ p.g) (A B:Stalls p) (hk:seeking p A) (hl:seeking p B)
    (hβ:0<β) (hz:0<η) (hη : playbook p K*η<1/2*β^2)
    (hd:∀ i,d i≤K^2) (he:∀ i,e i≤K^2):
    Guild.rich (stellar u s t η A B) := by
  classical
  intro i S hu y
  have hh a (b:Finset (Label p.b)) (h : b.card+902<Fintype.card (Label p.b)):
      ∃ z,z∉b∧z∉S a := by
    obtain ⟨z,hz⟩:=any_label (b∪S a) ((card_union_le ..).trans_lt ((Nat.add_le_add_left
      (hu a) _).trans_lt h))
    exact ⟨z,fun ht=>hz (mem_union_left _ ht),fun ht=>hz (mem_union_right _ ht)⟩
  obtain ⟨v,h1,h2⟩:= hh true (A i.1) (hk _)
  obtain ⟨w,h3,h4⟩:= hh false (B i.2) (hl _)
  let x : Zodiac p:= ⟨⟨0,by omega⟩,y.1,fun i=>if i then v else w,fun _=>Flavor.full⟩
  have hh : x.common:= fun i=> generic_apt p hg _ rfl
  obtain ⟨W,hA,hB,hC⟩:= sturdy_contact u s t h hs ht hβ x hh (fun _=>rfl) i y.2.1 y.2.2 hz
    ((mul_le_mul_of_nonneg_right (booklet_cap p K _ _ (hd _) (he _)) hz.le).trans_lt hη)
  refine ⟨(x,W),⟨⟨h1,h3,hA⟩,fun i=>?_⟩,?_⟩
  · cases i; exact h4; exact h2
  exact Prod.ext rfl (Prod.ext hB hC)

set_option maxHeartbeats 900000 in
theorem dual_eq (q:DualCoefficients d e) (V : StatusSp d e) (hq:q.law V)
    (i:Grid) (x:Suite d e i) (hx:x∈V i) :
    (leftChime q i).read x.1 x.2.1=(rightChime q i).read x.1 x.2.2 := by
  classical
  specialize hq i x hx
  rcases x with ⟨a,⟨⟨b,u⟩,s⟩,⟨c,v⟩,t⟩
  let f:= q.hed i; let W:= dotProduct (q.north i) u
  let Z:= dotProduct (q.south i) v
  let g:=q.left i.2; let h:=q.right i.1; let G:=q.gam i*a
  change G+f*(b+c)+(W+Z)=g*(b+s)+h*(c+t) at hq
  change g*s+W+(g+f)*b+0*_ = h*t+Z+(h+f)*c+G
  apply sub_eq_zero.mp
  rw [ZModModule.sub_eq_add]
  calc _
      _=(G+f*(b+c)+(W+Z))+(g*(b+s)+h*(c+t)):=by ring
      _=0:= by rw [hq,char_two]

set_option maxHeartbeats 900000 in
theorem charge_counter (h:origami p r u δ) (hs:reports p r u s β δ) (ht:reports p r u t β δ)
    (A B:Stalls p) (S : Straps (Label p.b)) (q:DualCoefficients d e)
    (he:q.law (chapter (stellar u s t η A B) S)) (hη:0≤η)
    (x: Zodiac p) (i:Grid) (hx:x.common) (hk:x.s true∉outstraps A S true i.1)
    (hl:x.s false∉outstraps B S false i.2) :
    charge u x s t i (leftChime q i) (rightChime q i)≤ num (Touch p d e i)*η := by
  classical
  let W:=circlet u s t x i
  obtain ⟨hm,hn⟩:=circlet_state u s t h hs ht x hx i
  let P:=fun y : Touch p d e i=> (leftChime q i).soot (x.aspect true) y.1≠
    (rightChime q i).soot (x.aspect false) y.2
  have hh (y): W y*ind (P y)≤η := by
    by_cases hp : P y
    · rw [ind_one hp,mul_one]
      by_contra! hy
      let C:=stellar u s t η A B
      let v : Scriptum p d e i := (x,y)
      have heq : (x.aspect true).fitsink y.1∧ (x.aspect false).fitsink y.2 := not_not.mp
        (fun h=> (hη.trans_lt hy).ne' (hn y h))
      have ht : (C i).zone S v :=
        ⟨⟨fun h=>hk (mem_union_left _ h),fun h=>hl (mem_union_left _ h),hx,heq.1,heq.2,hy.le⟩,
          fun i=>by cases i; exact fun h=>hl (mem_union_right _ h); exact fun h=>hk (mem_union_right _ h)⟩
      exact hp (dual_eq q (chapter C S) he i ((C i).writes v) ((C i).band_write S ht))
    rw [ind_zero hp,mul_zero]; exact hη
  change pr W P≤ _
  exact (Finset.sum_le_sum fun i _=> hh i).trans_eq (by simp [num])

end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteOptionLabels
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Option Labels -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Finset Function Submodule LinearMap
open scoped BigOperators Topology
open Template
variable {p:Shape} {N n r K : ℕ}
namespace StatusAnalysis
namespace DualAnalysis
open Club Guild
variable {d e: Rates}
    {u:Terrain p r} {s:Gazette p r d} {t:Gazette p r e}
    {β η δ:ℝ}

set_option maxHeartbeats 800000 in
theorem invite (p: Shape) (u:Terrain p r) (s:Gazette p r d) (t:Gazette p r e)
    (A B:Stalls p) (η:ℝ)
    (v: ∀ i,Suite d e i) (H:Straps (Label p.b)) (f:Bags (Scriptum p d e))
    (hf : Parade (stellar u s t η A B) H v f Finset.univ) :
    let C:=stellar u s t η A B
    ∃ (q : Volumes) (g:Engagement p (toFormat q) d e),
      (∀ i,1 ≤ toFormat q i ∧ toFormat q i ≤7) ∧
      (∀ i:Messenger (toFormat q),(C i.1).valid (g i)) ∧
      (∀ b:Bool,Injective (fun i:Messenger (toFormat q)=>(g i).1.s b)) ∧
      ∀ i,∑ j:Fin (toFormat q i),(C i).writes (g ⟨i,j⟩)=v i := by
  classical
  intro C
  have he i:= hf.batch i (mem_univ _)
  let q (i:Grid):Fin 8:= ⟨(f i).card,Nat.lt_succ_of_le (he i).2.2.2⟩
  let Q:=toFormat q
  let E (i:Grid): Fin (Q i)≃(↑(f i) : Type) := (Fintype.equivFinOfCardEq (Fintype.card_coe _)).symm
  let g:Engagement p Q d e:=fun i=>(E _ i.2).val
  have hG (i) : g i∈ f i.1:=(E i.1 i.2).property
  refine ⟨q,g,fun i=>(he i).2.2,fun i=>((he _).1.1 _ (hG i)).1,fun b i j h=>?_,
    fun i=>?_⟩
  · rcases i with ⟨i,x⟩;rcases j with ⟨j,y⟩
    by_cases hi:i=j
    · subst j
      have ht : g ⟨i,x⟩=g ⟨i,y⟩:=
        (he i).1.2 b (hG ⟨i,x⟩) (hG ⟨i,y⟩) h
      rw [show x=y from (E i).injective (Subtype.ext ht)]
    exact (hf.mixed i j (mem_univ _) (mem_univ _) hi _ (hG ⟨i,x⟩) _ (hG ⟨j,y⟩) b h).elim
  calc _ = ∑ x:↑(f i), (C i).writes x.val := Equiv.sum_comp (E i) (fun x=>(C i).writes x.val)
       _ = _ := (Finset.sum_coe_sort (f i) _).trans (he i).2.1

variable (p:Shape)
namespace Engagement

set_option maxHeartbeats 900000 in
theorem solicit {q:Format} (g:Engagement p q d e) (a b:Script p (Messenger q))
    (Y : Silhouette p N r) (X:Charts p n d) (Z:Charts p n e) (m:Mixer p n)
    (o o':UnitType p n N) (i:Messenger q) :
    (g.binding p a b).chimera o o' X Z m Y i=
    let H:= g i
    circlet (wisp p Y) (wake p Y m o X) (wake p Y m o' Z) H.1 i.1 H.2 := by
  classical
  let H:=g i
  let μ:= lawOmega p N H.1.l H.1.q
  let u:= Y H.1.l H.1.q
  let F:=couplePage (wake p Y m o X) (wake p Y m o' Z) H.1 i.1
  change _=avg (mapW μ u) (fun i =>F i H.2)
  rw [mapW_avg]
  rfl
end Engagement

set_option maxHeartbeats 1200000 in
theorem processions (K:ℕ) {u:Terrain p r} {s:Gazette p r d} {t:Gazette p r e} (A:Stalls p) (B:Stalls p) (a b:Pin p n N)
    (X:Charts p n d) (W:Charts p n e) (T:Cross p n)
    (hA:charted X a.sp) (hB:charted W b.sp) (ha:tableInj a.sp b.sp T) (hb:tableInj b.sp a.sp
      (reciprocal p T))
    (x y:Stalls p) (hX:booths p K a.sp x) (hY:booths p K b.sp y) (hx: x ≤ A) (hy: y ≤ B)
    (hg:2≤p.g) (hp:1≤p.J)
    (H:Straps (Label p.b))
    (ht : ∀ i:Grid,(stellar u s t η A B i).travels H 100 (view _ _)
       (chapter (stellar u s t η A B) H i))
    (hv:scorecard (chapter (stellar u s t η A B) H) (hailing p X W T)) :
    ∃ (q:Volumes) (g:Engagement p (toFormat q) d e) (s0 t0:Script p (Messenger (toFormat q))),
       (g.binding p s0 t0).chances X W a b T K ∧ ∀ i:Messenger (toFormat q),
       η ≤ circlet u s t (g i).1 i.1 (g i).2 := by
  classical
  obtain ⟨v,hv,hp0⟩:=hv
  let C:=stellar u s t η A B
  obtain ⟨g,hg'⟩:= full_parade C H ht hv
  obtain ⟨q,g,hI,hG,hS,hQ⟩:=invite p u s t A B η v H g hg'
  let z:=g.tags p; let w:=g.bits p; let F0:=g.genre0 p; let F1:=g.genre1 p
  have hM : F0.up z w ∧ F1.up z w := by
    constructor
    · exact ⟨hS true,fun i=> (hG i).2.2.2.1.2.1,fun i=> (hG i).2.2.2.1.1⟩
    exact ⟨hS false,fun i=> (hG i).2.2.2.2.1.2.1,fun i=>(hG i).2.2.2.2.1.1⟩
  obtain ⟨P,Q,hP⟩:= optionVia (toFormat q) d e a b T K ha hb z X W hA hB F0 F1 x y hX hY
    (fun i h=> (hG i).1 (hx _ h)) (fun i h=> (hG i).2.1 (hy _ h)) w hM.1 hM.2 hp hg hI
    (by
      have he : sendSum w F0.amp F1.amp = v := funext (fun i=>hQ i)
      rw [he]; exact hp0)
  exact ⟨q,g,P,Q,hP,fun i=>(hG i).2.2.2.2.2⟩

end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BinaryStatusComparison
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary Status Comparison -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Filter Function Submodule Module LinearMap
open scoped BigOperators
variable {A B J H : Type} [Fintype A] [Fintype B] [Fintype J]

theorem disagreement_bound (w : Wgt A) (hw : ∀ x,0 ≤ w x) (f g h:A→ H) :
    pr w (fun i=> f i≠ h i) ≤ pr w (fun i=>f i≠ g i) + pr w (fun i=>g i≠h i) :=
  let p (i:A) := f i≠g i∨g i≠h i
  ((pr_mono hw fun i h=>show p i from Classical.byContradiction (fun hi => h (Eq.trans
    (not_not.mp (mt Or.inl hi)) (not_not.mp (mt Or.inr hi))))).trans (pr_or_le hw))

theorem majority_bound (w : Wgt A) (hw:IsLaw w) (f : A→F) :
    1/2 ≤ pr w (fun i=> f i= majority w f) := by
  classical
  unfold majority
  split
  next h => exact h
  next h =>
    have hi i : f i=1 ↔ ¬f i=0 :=
      ⟨fun hh=>by rw [hh]; exact one_ne_zero,fun hh=>(bit_cases _).resolve_left hh⟩
    simp_rw [hi,pr_not,hw.total]
    exact le_of_lt (by linarith only [h])

theorem majority_charge (p:Wgt A) (q:Wgt B) (hp:IsLaw p) (hq:IsLaw q)
    (f:A→F) (g:B→F) :
    pr p (fun i=> f i≠majority q g)≤2 * pr (pairW p q) (fun i=> f i.1≠g i.2) := by
  classical
  let Q i:= g i=majority q g; let P i:= f i≠majority q g
  let v:= pairW p q
  have hm (z:A×B) (h:P z.1∧Q z.2): f z.1≠g z.2 := h.2 ▸ h.1
  have hh : pr p P*pr q Q ≤ pr v (fun i=>f i.1≠g i.2) :=
    (pairW_pr ..).symm.le.trans (pr_mono (pairW_law hp hq).nz hm)
  have hx:=majority_bound q hq g
  have hh' := mul_le_mul_of_nonneg_left hx (pr_nonneg (p:=P) hp.nz)
  change _* (1/2) ≤ _*pr q Q at hh'
  change pr p P≤2*pr v _
  linarith only [hh,hh']

theorem reflect_cost (p:Wgt A) (q:Wgt B) (hp:IsLaw p) (hq:IsLaw q)
    (f:A→H) (g:B→H) (k:H) :
    pr q (fun i=>g i≠k)≤ pr (pairW p q) (fun i=>f i.1≠g i.2)+pr p (fun i=>f i≠k) := by
  let w:=pairW p q
  let t i:= g i≠k; let s i:= f i≠k
  have hi : pr q t=pr w (fun i=> t i.2) := by simpa [hp.total] using
    (pairW_pr p q (fun _=>True) t).symm
  have hj : pr p s=pr w (fun i=>s i.1) := by simpa [hq.total] using
    (pairW_pr p q s (fun _=>True)).symm
  let P (i:A×B):= f i.1 ≠ g i.2
  rw [hi,hj]
  have hh (i:A×B) (h:t i.2): P i∨ s i.1 := by
    by_cases he:P i
    · exact Or.inl he
    exact Or.inr (fun hc=> h ((not_not.mp he).symm.trans hc))
  exact (pr_mono (pairW_law hp hq).nz hh).trans (pr_or_le (pairW_law hp hq).nz)

namespace StatusAnalysis
namespace DualAnalysis
variable {p:Shape} {d e: Rates} {r K:ℕ}
variable (u:Terrain p r) (s:Gazette p r d) (t:Gazette p r e)

theorem amendsB (x y: Appearance p)(h:x.l=y.l)(ht:x.q=y.q):
    (amends p x y).aspect false=y := by cases x; cases y; simp_all [amends,Zodiac.aspect]

theorem splitCounsel (i:Grid) (A B:Finset (Label p.b))
    (a : RhymeSet (d i.1)) (b : RhymeSet (e i.2)) (ε :ℝ)
    (h:counsel u s t i A B a b ε) (x y:Appearance p)
    (hx:x.s∉A) (hy:y.s∉B) (he:x.apt) (hf:y.apt) (hg:x.l=y.l) (hk:x.q=y.q) :
    avg (u x.l x.q) (fun j=>pr (pairW (s i.1 x j) (t i.2 y j)) (fun k=>a.soot x k.1 ≠
      b.soot y k.2))≤ε := by
  classical
  let Z:=amends p x y
  have hQ : Z.aspect false=y := amendsB _ _ hg hk
  have hP : Z.aspect true=x := rfl
  have hm : Z.common := by intro i;cases i; rw [hQ];exact hf; rw [hP];exact he
  have hi:= h Z hm hx hy
  unfold charge circlet pr couplePage at hi
  rw [mixW_avg,hQ,hP] at hi
  exact hi

set_option maxHeartbeats 800000 in
theorem paeans {β δ:ℝ} (hu:origami p r u δ)(hs:reports p r u s β δ)(ht:reports p r u t β δ)
    (i:Grid) (A B:Finset (Label p.b)) (hx:A.card<Fintype.card (Label p.b))
    (hy:B.card<Fintype.card (Label p.b)) (hg:3≤p.g)
    (a : RhymeSet (d i.1)) (b : RhymeSet (e i.2)) (ε:ℝ) (he:0≤ε)
    (h:counsel u s t i A B a b ε) :
    ∃ f:Pulsar p r, praise u s i.1 A a f (3*ε) ∧ praise u t i.2 B b f (3*ε) := by
  classical
  obtain ⟨x,hx⟩:=any_label A hx
  obtain ⟨y,hy⟩:=any_label B hy
  let Z:= amazes p y
  let f l q j:= majority (t i.2 (Z l q) j) (b.soot (Z l q))
  have hl:praise u s i.1 A a f (2*ε) := by
    intro z hz hhq
    let w:= Z z.l z.q
    have ht' := generic_apt p hg w rfl
    have hh := splitCounsel u s t i A B a b ε h z w hz hy hhq ht' rfl rfl
    refine le_trans (avg_mono (hu.1 z.l z.q).nz (fun j=> majority_charge (s i.1 z j) (t i.2 w j)
      (hs.law _ _ hhq _) (ht.law _ _ ht' _) (a.soot z) (b.soot w))) ?_
    rw [avg_mul']
    exact mul_le_mul_of_nonneg_left hh (by norm_num)
  refine ⟨f,fun w hw hx=>(hl _ hw hx).trans (by linarith only [he]), fun w hw hv=>?_⟩
  let z:=amazes p x w.l w.q
  have hf : z.apt:=generic_apt _ hg _ rfl
  have hx0:= splitCounsel u s t i A B a b ε h z w hx hw hf hv rfl rfl
  have hl0:=hl z hx hf
  let W:=u w.l w.q
  have heq j:= reflect_cost (s i.1 z j) (t i.2 w j) (hs.law _ _ hf j) (ht.law _ _ hv j)
    (a.soot z) (b.soot w) (f w.l w.q j)
  apply (avg_mono (hu.1 w.l w.q).nz heq).trans
  rw [avg_add]; exact (add_le_add hx0 hl0).trans_eq (by ring)
end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_UniqueStatusCoefficients
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unique Status Coefficients -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Function Matrix Submodule Module LinearMap
open scoped BigOperators
namespace StatusAnalysis
namespace DualAnalysis
variable {p:Shape} {r:ℕ} {d:Rates}
    {u:Terrain p r} {s:Gazette p r d} {β δ:ℝ}

private theorem loose_coeff {n:ℕ} (a b:RhymeSet n) (h:a.coal≠b.coal∨a.headBit≠b.headBit)
    (Q S T:F) :
    ∃ x:Par n,dotProduct a.coal x.2+a.headBit*x.1+a.gamma*Q+S ≠
      dotProduct b.coal x.2+b.headBit*x.1+b.gamma*Q+T := by
  classical
  by_contra! he
  have h0 := he (0,0)
  simp only [dotProduct_zero,mul_zero,add_zero,zero_add] at h0
  obtain ⟨ha,hb⟩ : a.coal=b.coal∧a.headBit=b.headBit :=by
    constructor
    · funext i
      have hh:=he (0,Pi.single i 1)
      simp only [dotProduct_single,mul_one,mul_zero,add_zero,add_assoc,h0] at hh
      exact add_right_cancel hh
    have hh:=he (1,0); simp only [dotProduct_zero,mul_one,zero_add,add_assoc,h0] at hh
    exact add_right_cancel hh
  simp [ha,hb] at h

theorem shot_switch (u:Terrain p r) (s:Gazette p r d) (i) (z:Appearance p)
    (a:RhymeSet (d i)) (f g:Pulsar p r)
    (hw:IsLaw (u z.l z.q)) (hs:∀ j, IsLaw (s i z j)) :
    shot u s i z a g ≤ shot u s i z a f+pr (u z.l z.q) (fun j=>f z.l z.q j≠ g z.l z.q j) := by
  unfold shot pr; rw [←avg_add]
  refine avg_mono hw.nz (fun j=>?_); let T:=s i z j
  have hh := disagreement_bound (s i z j) (hs j).nz (a.soot z)
    (fun _=>f z.l z.q j) (fun _=>g z.l z.q j)
  unfold pr at hh; rw [(hs j).avg_const] at hh; exact hh
set_option maxHeartbeats 1000000 in
theorem unison (hp:3≤p.g) (hu:origami p r u δ) (hs:reports p r u s β δ)
    (i : Nodes) {ε e:ℝ}
    (a b:RhymeSet (d i))
    (f g:Pulsar p r) (A B : Finset (Label p.b)) (h:(A∪B).card < Fintype.card (Label p.b))
    (hA:praise u s i A a f ε) (hB:praise u s i B b g e)
    (hC:a.bit=b.bit) (ht:ε+e<1/2*β) (hβ:0≤β) :
    a.coal=b.coal ∧ a.headBit=b.headBit ∧ ∀ l q, pr (u l q)
      (fun k=>f l q k+a.gamma*q≠g l q k+b.gamma*q) ≤ ε+e := by
  classical
  obtain ⟨x,hx⟩:= any_label _ h
  let X:= amazes p x
  let P l q k (w:Magazine p (d i)) :=
    a.read q w.2≠ f l q k ∨ b.read q w.2 ≠g l q k
  have hX l q : (X l q).apt:=generic_apt p hp _ rfl
  have hi l q :
      avg (u l q) (fun k=>pr (s i (X l q) k) (P l q k)) ≤ ε+e := by
    have h1:=hA (X l q) (fun h=>hx (mem_union_left _ h)) (hX l q)
    have h2:=hB (X l q) (fun h=>hx (mem_union_right _ h)) (hX l q)
    let t k:=s i (X l q) k
    let q1 (k:Fin r) (w:Magazine p (d i)):= a.read q w.2≠ f l q k
    let q2 (k:Fin r) (w:Magazine p (d i)):= b.read q w.2≠g l q k
    apply (avg_mono (hu.1 l q).nz (fun j=> pr_or_le (p:=q1 j) (q:=q2 j)
      (hs.law _ _ (hX ..) j).nz)).trans
    rw [avg_add]
    exact add_le_add h1 h2
  have ht' (l q k) (w:Magazine p (d i)) (h:¬P l q k w) :
      let x:=(w.2.1)
      dotProduct a.coal x.2+a.headBit*x.1+a.gamma*q + f l q k =
        dotProduct b.coal x.2+b.headBit*x.1+b.gamma*q+g l q k := by
    have ha : a.read q w.2=f l q k := not_not.mp (mt Or.inl h)
    have hb : b.read q w.2=g l q k := not_not.mp (mt Or.inr h)
    let x:=w.2.1
    let V (s:RhymeSet (d i)) := dotProduct s.coal x.2+s.headBit*x.1+s.gamma*q
    have hh (s:RhymeSet (d i)) : V s + s.read q w.2=s.bit*(w.2.2+x.1) := by
      have hh : s.read q w.2=s.bit*(w.2.2+x.1)+V s := by unfold RhymeSet.read V x; ring
      rw [hh,add_left_comm,char_two,add_zero]
    change V a+_= V b+_
    rw [←ha, ←hb,hh,hh,hC]
  have he : a.coal=b.coal∧a.headBit=b.headBit := by
    let l:Tag p.g:= ⟨0,by omega⟩; let Q:=show F from 0
    let R:=X l Q; let S(k:Fin r):= δ≤u l Q k
    by_contra! hf
    have hb (k) (hk:S k): β ≤ pr (s i R k) (P l Q k) := by
      obtain ⟨z,hz⟩:= loose_coeff a b (by tauto) Q (f l Q k)
        (g l Q k)
      · exact le_trans (hs.generous i _ rfl (hX _ _) k hk z)
          (pr_mono (hs.law _ R (hX _ _) k).nz (fun x hx=> not_not.mp
          (fun ht=>hz (hx ▸ ht' l Q k x ht))))

    have hh : 1/2*β ≤ avg (u l Q) (fun k=>pr (s i R k) (P l Q k)) := by
      refine (mul_le_mul_of_nonneg_right (hu.2 l Q) hβ).trans ?_
      unfold pr; rw [←avg_mul]; refine avg_mono (hu.1 l Q).nz fun i=> ?_
      change ind (S i) * _ ≤ _
      by_cases h:S i
      · rw [ind_one h,one_mul]; exact hb i h
      rw [ind_zero h,zero_mul]; exact pr_nonneg (hs.law _ _ (hX _ _) i).nz
    exact ht.not_ge (hh.trans (hi l Q))
  refine ⟨he.1,he.2,fun l q=> le_trans ?_ (hi l q)⟩
  refine avg_mono (hu.1 l q).nz fun k=> ?_
  let W:=s i (X l q) k
  have hw:=hs.law i _ (hX l q) k
  let C:=f l q k+a.gamma*q≠g l q k+b.gamma*q
  change ind C ≤ pr W _
  by_cases h:C
  · have hh w : P l q k w := by
      by_contra hy
      have hm:=ht' l q k w hy; dsimp only at hm
      rw [he.1,he.2,add_assoc _ (a.gamma*q),add_assoc _ (b.gamma*q)] at hm
      exact h (by rw [add_comm _ (a.gamma*q),add_comm _ (b.gamma*q)]; exact add_left_cancel hm)
    rw [ind_one h]; simp_rw [funext fun w=>eq_true (hh w),pr_true,show tot W=1 from hw.total]; exact le_rfl
  rw [ind_zero h]
  exact pr_nonneg hw.nz
end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FinitePredictions
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Predictions -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Filter Finset LinearMap Module Function
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
namespace DualAnalysis
variable {p:Shape} {r n N K:ℕ} {d:Rates}

theorem lyrically (i:Bool) (o:UnitType p n N)
    (m:Mixer p n) (s:Charts p n d) (w:Cell (d i)) (α:F) (x: Appearance p) (z:Knobs p.g n) :
    (yokeSet w α).soot x (x.profile i o m (s i) z)=
       compass i o s m w α (useAtom p x.l x.s x.f z) := by
  classical
  let A:=useAtom p x.l x.s x.f z
  change 1*(innerP p o i) A+dotProduct w (roll (s i) (Tsym m A)) +
    (1+(1+α))*role p n A+0*x.q=(innerP p o i) A+(Tsym m (s i w) A+α*role p n A)
  rw [one_mul,←add_assoc (1:F),char_two,zero_add,zero_mul,add_zero,dotProduct_comm,← roll_project,
      T_swap,add_assoc]

theorem notary (s:Charts p n d) (Y:Silhouette p N r) (i:Bool) (o:UnitType p n N)
    (m:Mixer p n) (w:Cell (d i)) (α:F) (x:Appearance p) (f:Pulsar p r)
    {δ:ℝ} (h:x.close Y (onSide o i) δ) (hx:IsLaw (x.wit n)) :
    let g:= mismatch p (fromPulse Y f) (compass i o s m w α) x.l x.s x.f (onSide o i)
    |shot (wisp p Y) (wake p Y m o s) i x (yokeSet w α) f - pr (x.wit n) g|≤δ := by
  classical
  intro g
  let P k (y:Magazine p (d i)):= ((yokeSet w α).soot x y≠ f x.l x.q k)
  let W k y:=ind (P k y)
  have hh (k y):|W k y|≤1 := by unfold W; rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _
  have he := x.close_expect Y i o m (s i) hx W hh h
  let f' := x.profile i o m (s i)
  let V z:= W (x.showTag Y (onSide o i) z) (f' z)
  have hf : avg (x.wit n) V=pr (x.wit n) g := by
    refine avg_congr fun z hz =>?_
    have hx : dialed p x.l x.f z=x.q := (onW_ne hz).1
    have hq : g z ↔ P (x.showTag Y (onSide o i) z) (f' z) := by
      unfold g mismatch fromPulse P f'
      rw [hx, lyrically]
      rfl
    exact congrArg ind (propext hq.symm)
  change |_ - avg (x.wit n) V|≤_ at he; rw [hf] at he; exact he

set_option maxHeartbeats 800000 in
theorem praise_predict (s:Charts p n d) (Y:Silhouette p N r) (i:Bool)
    (o:UnitType p n N) (m:Mixer p n) (w:Cell (d i)) (α:F) (f:Pulsar p r) {ε δ:ℝ}
    (A:Finset (Label p.b))
    (he:0≤ε) (hδ:0≤δ)
    (hp : 1≤ p.r) (hn:2*p.r≤n)
    (hh:∀ x:Appearance p,x.apt→x.close Y (onSide o i) δ)
    (hw:praise (wisp p Y) (wake p Y m o s) i A (yokeSet w α) f ε) :
    postulates p (onSide o i) (fromPulse Y f) (compass i o s m w α) A ((ε+δ)*2) := by
  classical
  intro b hb t g
  let μ:=spins p n; let v:=onSide o i; let X (y:F) : Appearance p:=
    ⟨t,b,g,y⟩
  let Z:=mismatch p (fromPulse Y f) (compass i o s m w α) t b g v
  let Q y (x:Knobs p.g n):=dialed p t g x=y
  have hμ := spins_law p n
  have hz (y:F) : pr μ (fun x=>Z x∧Q y x)≤ ε+δ := by
    let x:=X y
    by_cases hg : x.apt
    · have hk:= hw x hb hg; have hx:= Appearance.witLaw hg hp hn
      have hi:= notary s Y i o m w α x f (hh x hg) hx
      change |_ - pr (x.wit n) Z|≤δ at hi
      have he : pr (x.wit n) Z ≤ ε+δ := by linarith only [hk, (abs_le.mp hi).1]
      rw [show (fun x=> Z x ∧ Q y x)=(fun x=>Q y x ∧ Z x) from funext fun x=>propext and_comm,
        pr_of_on hμ.nz]
      exact ((mul_le_mul_of_nonneg_right ((pr_le_tot hμ.nz).trans hμ.total.le)
        (pr_nonneg hx.nz)).trans_eq (one_mul _)).trans he
    have hm z : ¬ Q y z := by
      intro h
      refine hg ⟨scan p t g z,fun j hj=>?_,h⟩
      unfold scan; rw [ite_eq_right hj]
    simp_rw [show ∀ z,(Z z∧Q y z)=False from (fun z=>eq_false (fun h=>hm z h.2)),
      pr_false]; exact add_nonneg he hδ
  refine (sum_pr_tag μ Z (dialed p t g)).symm.le.trans
    ((Finset.sum_le_sum fun i _=>hz i).trans_eq ?_)
  simp only [sum_const,card_univ,nsmul_eq_mul,F,ZMod.card] <;> ring

set_option maxHeartbeats 800000 in
theorem predict_praise (s:Charts p n d) (Y:Silhouette p N r) (i:Bool)
    (o:UnitType p n N) (m:Mixer p n) (w:Cell (d i)) (α:F) (f:Pulsar p r) {ε δ:ℝ}
    (A:Finset (Label p.b))
    (he:0≤ε)
    (hp:1≤p.r) (hn:2*p.r≤n)
    (hh:∀ x:Appearance p,x.apt → x.close Y (onSide o i) δ)
    (hw:postulates p (onSide o i) (fromPulse Y f) (compass i o s m w α) A (scanPrice p *ε)) :
    praise (wisp p Y) (wake p Y m o s) i A (yokeSet w α) f (ε+δ) := by
  intro x hx h
  let Z:= mismatch p (fromPulse Y f) (compass i o s m w α) x.l x.s x.f (onSide o i)
  have hwit := Appearance.witLaw h hp hn
  have hz:= notary s Y i o m w α x f (hh x h) hwit
  have hv : pr (x.wit n) Z ≤ε := by
    unfold Appearance.wit scopedBit
    let w:=spins p n
    let Q (i:Knobs p.g n):=dialed p x.l x.f i=x.q
    have hf := show scanPrice p ≤ pr w Q from dial_fraction p n _ _ _ hp hn h
    rw [pr_on,div_le_iff₀ ((scanPrice_pos _).trans_le hf)]
    exact (((pr_mono (spins_law p n).nz fun _=> And.right).trans (hw _ hx _ _)).trans
      (((mul_comm (scanPrice p) ε).le).trans (mul_le_mul_of_nonneg_left hf he)))
  change |_-pr _ Z| ≤_ at hz
  linarith only [(abs_le.mp hz).2,hv]

end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PredictedDualCoefficients
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Predicted Dual Coefficients -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Module LinearMap
open scoped BigOperators Topology
variable {p:Shape} {r n:ℕ}
namespace StatusAnalysis
namespace DualAnalysis

variable {d e:Rates} {u:Terrain p r} {s:Gazette p r d} {t:Gazette p r e}

open PredictionClass

private theorem scaleShot (i:Nodes) (z:RhymeSet (d i)) (A:Finset (Label p.b)) (f:Pulsar p r)
    {ε:ℝ}(hc:0≤ε)(h:praise u s i A z f ε) (k:F) :
    praise u s i A (scaled k z) (f.mult k) ε := by
  classical
  rcases bit_cases k with ht|ht
  · subst k; intro x hx ha
    unfold shot Pulsar.mult RhymeSet.soot RhymeSet.read scaled
    simp only [zero_mul,zero_smul,zero_dotProduct,add_zero, ne_eq,not_true_eq_false,pr_false,avg_const,
      mul_zero]; exact hc
  subst k; rw [show f.mult 1=f from (by unfold Pulsar.mult; simp only [one_mul]), show scaled 1 z=z from (by unfold scaled; simp)] ; exact h

private theorem center_tri (w:Wgt (Fin r)) (k:F)
    (f g h:Fin r→ F) (b:F) (hw:IsLaw w)
    (x y:ℝ)
    (hx:pr w (fun i=>h i≠f i)≤x) (hy:pr w (fun i=>h i+b*k≠g i)≤y):
    pr w (fun i=> f i+g i≠ b*k)≤ x+y := by
  classical
  let P i:= h i≠f i; let Q i:=h i+b*k≠g i
  have hi i (h': f i+g i≠b*k):P i∨Q i:= by
    by_contra! hh
    apply h'
    rw [← not_not.mp hh.1,← not_not.mp hh.2,←add_assoc,char_two,zero_add]
  exact ((pr_mono hw.nz hi).trans (pr_or_le hw.nz)).trans (add_le_add hx hy)

set_option maxHeartbeats 900000 in
theorem duet_edge {δ β a ε:ℝ}
    (v:PredictionData p d e r) (z:DualCoefficients d e) (i:Grid)
    (hp:3≤p.g) (hu:origami p r u δ) (hs:reports p r u s β δ) (ht:reports p r u t β δ)
    (A B:Stalls p)
    (hv:v.colored u s t A B a) (hA:(A i.1).card<Fintype.card (Label p.b))
    (hB:(B i.2).card<Fintype.card (Label p.b))
    (hh:counsel u s t i (A i.1) (B i.2) (leftChime z i) (rightChime z i) ε)
    (hε:0 ≤ ε) (hz:0 ≤ a) (hb:0≤β) (hi :3*ε+a<1/2*β) :
    z.north i=z.left i.2 • v.X i.1 ∧ z.south i=z.right i.1 • v.Y i.2 ∧
      z.hed i=z.left i.2*firstBit v.α i.1 ∧ z.hed i=z.right i.1*firstBit v.α i.2 ∧
        ∀ l q,ChorusCost v z i u l q≤2*(3*ε+a) := by
  classical
  obtain ⟨P,h1,h2⟩:= paeans u s t hu hs ht i (A i.1) (B i.2) hA hB hp _ _ ε hε hh
  let X:= z.left i.2; let Y:=z.right i.1
  have h3:=scaleShot i.1 _ _ _ hz (hv.1 i.1) X
  have h4:=scaleShot i.2 _ _ _ hz (hv.2 i.2) Y
  have heq:=unison hp hu hs i.1 _ _ _ _ _ _ (by rw [union_idempotent]; exact hA)
    h1 h3 (show X=X*1 by rw [mul_one]) hi hb
  obtain ⟨hC,hD,hE⟩:=heq
  obtain ⟨hF,hG,hH⟩:=unison hp hu ht i.2 _ _ _ _ _ _ (by rw [union_idempotent]; exact hB)
    h2 h4 (show Y=Y*1 by rw [mul_one]) hi hb
  refine ⟨hC,hF,hD,hG,fun l q=>?_⟩
  unfold ChorusCost
  rw [two_mul]
  apply center_tri (w:=u l q) (k:=q) (h:=P l q) _ _ (b:=z.gam i) (hu.1 l q)
    (3*ε+a) (3*ε+a)
  · have ht:=hE l q
    simpa only [leftChime,scaled,yokeSet,mul_zero,zero_mul,add_zero,Pulsar.mult] using ht
  have ht:=hH l q
  simpa only [rightChime,scaled,yokeSet,mul_zero,zero_mul,add_zero,Pulsar.mult] using ht
end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PredictedDualEvaluation
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Predicted Dual Evaluation -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset Function LinearMap Module
open scoped BigOperators
namespace StatusAnalysis
namespace DualAnalysis
open PredictionClass
variable {p:Shape} {n N r :ℕ} {A B:Rates}

private theorem echo_pattern (c:PredictionClass) (z:DualCoefficients A B)
    (h:∀ i j,echoes c i j (z.left j) (z.right i))
    (hn:c≠dusk) (he:z.left ≠0∨ z.right≠0):
    z.left=z.right ∧
      ((∃ i, c=dawn i∧ z.left=unary i) ∨ (c=twinned∧ z.left=allSide)) := by
  classical
  have hh (i) : c.active i→ z.left i=z.right i := by
    intro ht; have hk:=(h i i).1
    rcases bit_cases (z.left i) with hi|hi <;> rcases bit_cases (z.right i) with hx|hx <;> simp_all
  cases c
  · exact (hn rfl).elim
  · rename_i i
    have ht : (dawn i).active i:= rfl
    have hact := hh i ht
    have hx j (hij:i≠j): z.left j=0 ∧ z.right j=0 := by
      have hf : ¬(dawn i).active j:=hij
      have h1:=(h i j).1; have h2:=(h j i).1
      constructor
      · exact (bit_cases _).resolve_right fun h'=> hf (h1.mp ⟨h',ht⟩).2
      exact (bit_cases _).resolve_right fun h'=> hf (h2.mpr ⟨h',ht⟩).2
    have hm : z.left=z.right := funext fun j=>by
      by_cases hij : i=j
      · exact hij ▸ hact
      exact (hx j hij).1.trans (hx j hij).2.symm
    have hz:=show z.left≠0 from he.elim id (fun h=>hm.symm ▸ h)
    refine ⟨hm,Or.inl ⟨i,rfl, funext fun j=>?_⟩⟩
    by_cases hij:i=j
    · subst j
      have hv : z.left i=1:= (bit_cases _).resolve_left (fun h=> hz (funext fun j=> by
        by_cases hi : i = j
        · exact hi ▸ h
        exact (hx j hi).1))
      simp [unary,hv]
    rw [(hx j hij).1]; simp [unary,Ne.symm hij]
  · have heq : z.left=z.right:= funext (fun i=> hh i trivial)
    have hz:=show z.left≠0 from he.elim id (fun h=>heq.symm ▸ h)
    refine ⟨heq,Or.inr ⟨rfl,funext fun j=>?_⟩⟩
    change z.left j=1; refine (bit_cases _).resolve_left (fun ht=>?_); apply hz
    apply funext; intro i
    have hx:= (h i j).1
    change z.left i=0; apply (hh i trivial).trans
    exact (bit_cases _).resolve_right (fun h=> zero_ne_one (ht.symm.trans (hx.mpr ⟨h,trivial⟩).1))
  have heq : z.left=z.right:=funext fun i=>hh i trivial
  exfalso
  have hz : z.left ≠0 := he.elim id (heq.symm ▸ id)
  apply hz
  apply funext; intro i; change z.left i=0
  refine (bit_cases _).resolve_right fun hx=>?_
  have ht:= (h (!i) i).2 ⟨hx,trivial⟩
  cases i <;> simp at ht

private theorem gamma_unique {u:Wgt (Fin r)} (w:Fin r→F) (a b:F)
    (hu:IsLaw u) {ε:ℝ} (h:2*ε<1)
    (ha:pr u (fun x=>w x≠a)≤ ε) (hb:pr u (fun x=>w x≠b)≤ ε):
    a=b := by
  classical
  by_contra hf
  have hi (i) (h:True): w i≠a∨w i≠b:=by
    by_cases hh:w i=a
    · exact Or.inr (hh ▸ hf)
    exact Or.inl hh
  have hp:=((pr_mono hu.nz hi).trans (pr_or_le hu.nz)).trans (add_le_add ha hb)
  rw [pr_true,hu.total,←two_mul] at hp
  linarith only [hp,h]

set_option maxHeartbeats 1400000 in
theorem harmony (v:PredictionData p A B r) (u:Terrain p r) (c:PredictionClass) (τ :ℝ)
    (m:BMark p n N) (x y:UnitType p n N)
    (T:Cross p n) (s:Charts p n A) (t:Charts p n B)
    (hx:coordSpec m x s v.X) (hy:coordSpec m y t v.Y)
    (hg:3≤p.g)
    (h:chorusClass p v u c τ)
    (hq:∀ l q,IsLaw (u l q))
    (he:glint p (m x)=glint p (m y))
    (hf:c.compatible v.α (glint p (m x)) (cardTone m x T,cardTone m y (reciprocal p T)))
    (z:DualCoefficients A B) (hτ:0≤τ) (ht:2*τ<1) (hz:z.left≠0∨z.right≠0)
    (ha:∀ i,z.north i=z.left i.2 • v.X i.1 ∧ z.south i=z.right i.1 •v.Y i.2)
    (hb:∀ i,z.hed i=z.left i.2*firstBit v.α i.1∧z.hed i=z.right i.1*firstBit v.α i.2)
    (hl:∀ i l q,ChorusCost v z i u l q≤τ):
    ∑ i,z.bet i (hailing p s t T i)=0 := by
  classical
  let G:= z.left; let H:=z.right
  let L i j:= contract p T i j (m x i)+role p n (m x i)
  let R i j:= contract p (reciprocal p T) j i (m y j)+role p n (m y j)
  let P:=cardTone m x T; let Q:=cardTone m y (reciprocal p T)
  let D:=glint p (m x)
  have h1 (i j): z.bet (i,j) (hailing p s t T (i,j)) =
      z.gam (i,j) + z.hed (i,j) + (G j * L i j + H i * R i j) := by
    unfold DualCoefficients.bet
    rw [(ha _).1,(ha _).2]; dsimp only [hailing]
    rw [smul_dotProduct,smul_dotProduct,mul_one,mul_one,dotProduct_comm (v.X _),dotProduct_comm (v.Y _)]
    unfold targetMark; rw [←roll_project, ←roll_project,hx _,hy _]; rfl
  let E:=∑ i:Grid,z.gam i
  let F' :=∑ i:Grid,z.hed i
  let g i:=G i*(P i+D); let h' i:=H i*(Q i+D)
  have hZ :∑ i,z.bet i (hailing p s t T i)=E+F'+((∑ i,g i)+(∑ j,h' j)):= by
    have h2 j : ∑ i:Nodes,G j*L i j=g j:= by
      unfold g P L; rw [←Finset.mul_sum,Finset.sum_add_distrib]; rfl
    have h3 i:∑ j:Nodes,H i*R i j=h' i:= by
      unfold h' Q R D; rw [←Finset.mul_sum,Finset.sum_add_distrib,he]; rfl
    unfold E F'; rw [Fintype.sum_prod_type, Fintype.sum_prod_type,Fintype.sum_prod_type]
    simp_rw [h1,Finset.sum_add_distrib,h3]
    congr 2
    rw [Finset.sum_comm]; simp_rw [h2]
  let l : Tag p.g:=⟨0,by omega⟩; let w:= u l 1
  have hh i: pr w (fun k=>G i.2 *v.g i.1 l 1 k+H i.1*v.g i.2 l 1 k ≠ z.gam i)≤τ :=by
    simpa only [w,ChorusCost,G,H,mul_one] using hl i l 1
  rw [hZ]
  by_cases hC : c=dusk
  · subst c
    have hg i : z.gam i=0:= by
      apply gamma_unique (w:=fun k=>_) _ _ (hq l 1) ht (hh i)
      simp only [h.2.1 rfl,mul_zero,add_zero, ne_eq,not_true_eq_false,pr_false]
      exact hτ
    have hf' i : z.hed i=0:= by
      rw [(hb i).1,h.1.1 i.1 not_false,mul_zero]
    have hx : P=fun _=> D:= congrArg Prod.fst hf
    have hy : Q=fun _=> D:= congrArg Prod.snd hf
    simp only [E,F',hg,hf',g,h',hx,hy,char_two,mul_zero,sum_const_zero]
  have hi := h.2.2 z hC hb hl
  obtain ⟨hr,hG⟩:=echo_pattern c z hi hC hz
  have hm : G=H :=hr
  have hf0 i: z.gam (i,i)=0:= by
    apply gamma_unique (w:=fun k=>_) _ _ (hq l 1) ht (hh (i,i))
    simp only [hm,char_two,ne_eq,not_true_eq_false,pr_false]
    exact hτ
  have hg1 i j : z.gam (i,j)=z.gam (j,i):= by
    apply gamma_unique (w:=fun k=>_) _ _ (hq l 1) ht (hh (i,j))
    simpa only [hm,add_comm] using hh (j,i)
  have hE : E=0 := by unfold E; rw [Fintype.sum_prod_type]
                                ; simp only [Fintype.sum_bool,hf0,hg1 false true,add_zero,zero_add,char_two]
  rw [hE,zero_add]
  obtain ⟨i,hc,hx⟩|⟨hc,hx⟩:=hG
  · subst c
    have hy : H=unary i:=hm ▸ hx
    change P i+Q i=firstBit v.α i at hf
    unfold F'
    rw [Fintype.sum_prod_type]; simp_rw [(hb _).1]
    have hi : firstBit v.α (!i)=0:= h.1.1 _ (by cases i <;> simp [active])
    cases i
    · change firstBit v.α true=0 at hi
      simp [hx,g,h',G,hy,unary,hi]
      rw [add_add_add_comm,char_two,add_zero,hf,char_two]
    · change firstBit v.α false=0 at hi
      simp [hx,g,h',G,hy,unary,hi]
      rw [add_add_add_comm,char_two,add_zero,hf,char_two]
  · subst c
    have hy : H=allSide:=hm ▸ hx
    change dotProduct allSide P + dotProduct allSide Q=0 at hf
    simp only [dotProduct,Fintype.sum_bool,allSide,one_mul] at hf
    unfold F'
    rw [Fintype.sum_prod_type]; simp_rw [(hb _).1]
    simp only [hx,g,h',G,hy,Fintype.sum_bool,allSide,one_mul,char_two,zero_add]
    rw [add_add_add_comm (P true) D,add_add_add_comm (Q true) D,char_two]
    simpa using hf
end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PredictionExtraction
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prediction Extraction -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Function Submodule LinearMap Module Finset
open scoped BigOperators
namespace StatusAnalysis
namespace DualAnalysis
variable {p:Shape} {r n:ℕ} {A B: Rates}
    {u:Terrain p r} {s:Gazette p r A} {t:Gazette p r B}
open PredictionClass Club Guild

theorem counter_bill {δ ε β η:ℝ} (q: DualCoefficients A B)
    {K:ℕ} (h:countStory p K η δ ε β u)
    (hs:reports p r u s β δ) (ht:reports p r u t β δ)
    (P Q:Stalls p) (S:Straps (Label p.b)) (i:Grid)
    (he:q.law (chapter (stellar u s t η P Q) S))
    (ha:A i.1≤K^2) (hb:B i.2≤K^2):
    counsel u s t i (outstraps P S true i.1) (outstraps Q S false i.2)
      (leftChime q i) (rightChime q i) ε := by
  intro x hx hp hq
  apply (charge_counter h.h hs ht P Q S q he h.ht x i hx hp hq).trans
  exact (mul_le_mul_of_nonneg_right (booklet_cap p K _ _ ha hb) h.ht).trans h.bill

theorem tells {δ ε β η:ℝ} (q: DualCoefficients A B) {K:ℕ}
    (h:countStory p K η δ ε β u)
    (hs:reports p r u s β δ) (ht:reports p r u t β δ)
    (P Q:Stalls p) (S:Straps (Label p.b))
    (he:q.law (chapter (stellar u s t η P Q) S))
    (ha:∀ i,A i≤K^2) (hb:∀ i,B i≤K^2)
    (h1 : ∀ i, (outstraps P S true i).card<Fintype.card (Label p.b))
    (h2 : ∀ i, (outstraps Q S false i).card<Fintype.card (Label p.b))
    (hg:3≤p.g) :
    Stirrings p r u s t q (outstraps P S true) (outstraps Q S false) ε := by
  constructor
  intro i
  refine paeans u s t h.h hs ht i _ _ (h1 _) (h2 _) hg _ _ ε h.he
    (counter_bill q h hs ht _ _ _ i he (ha _) (hb _))

set_option maxHeartbeats 800000 in
theorem build_anthology {δ ε β:ℝ} (P : Terrain p r) (s : Gazette p r A)
    (hp:origami p r P δ) (hs:reports p r P s β δ)
    (he:ε+ε<1/2*β) (hβ:0≤β) (hg:3≤p.g)
    (L:ℕ) (hL:2*L<Fintype.card (Label p.b)):
    ∃ d:Dict p r,anthology p r P s d L ε := by
  classical
  choose f hf using show ∀ (i:Nodes) (b k:F),∃ f:Pulsar p r,∀ (v: Pulsar p r) (A_:Finset (Label p.b))
    (a:RhymeSet (A i)), A_.card ≤ L → a.bit=b → a.gamma=k → praise P s i A_ a v ε →
       ∀ l q,pr (P l q) (fun x=> v l q x≠ f l q x) ≤2*ε from by
    intro i b k; let Q (v : Pulsar p r) :=
       ∃ (A' : Finset (Label p.b)) (a:RhymeSet (A i)),
         A'.card≤ L ∧ a.bit=b ∧ a.gamma=k ∧ praise P s i A' a v ε
    by_cases h:∃ v,Q v
    · obtain ⟨x,S,a0,hx,hy,hk,h⟩:= h
      refine ⟨x,fun v T a hc ha ht hz l q=>?_⟩
      obtain ⟨_,_,hg⟩:=unison hg hp hs i a a0 v x T S
        ((card_union_le ..).trans_lt (by rw [two_mul] at hL; linarith only [hL,hc,hx]))
        hz h (ha.trans hy.symm) he hβ
      specialize hg l q
      rw [ht,hk] at hg
      simpa only [ne_eq,add_left_inj,two_mul] using hg
    exact ⟨0,fun v t a h1 h2 h3 h4=>(h ⟨v,t,a,h1,h2,h3,h4⟩).elim⟩
  exact ⟨f,fun B i hi w a h=> hf i _ _ w (B i) a hi rfl rfl h⟩

theorem memo_card : Fintype.card Memo=128 := by simp [Memo,Nodes,Snip,F];

private theorem praise_tidy (d : Dict p r) (u:Terrain p r) (s:Gazette p r A)
    (t:Gazette p r B)
    {ε β δ:ℝ} (hs:reports p r u s β δ) (h:origami p r u δ) (L:ℕ)
    (S T:Stalls p) (i j:Nodes) (a:RhymeSet (A i)) (b:RhymeSet (B j))
    (f:Pulsar p r) (ha:a.bit=1) (hq:anthology p r u t d L ε)
    (hh:(T j).card ≤ L)
    (hA:praise u s i (S i) a f ε) (hB:praise u t j (T j) b f ε):
    praise u s i (S i) (yokeSet a.coal (1+a.headBit)) ((d j b.bit b.gamma).shift a.gamma) (3*ε) := by
  intro x hx hg
  let g:= d j b.bit b.gamma
  have hz : shot u s i x a g ≤ 3*ε :=
    ((shot_switch u s i x a f g (h.1 _ _) (hs.law _ _ hg)).trans (add_le_add (hA x hx hg)
      (hq T j hh f b hB _ _))).trans_eq (by ring)
  let y := yokeSet a.coal (1+a.headBit)
  have he (j k) :
      y.soot x k≠ g.shift a.gamma x.l x.q j ↔ a.soot x k≠g x.l x.q j := by
    have hh : a.soot x k=y.soot x k+a.gamma*x.q := by
      unfold y RhymeSet.soot RhymeSet.read yokeSet; rw [ha]
      simp only [zero_mul,add_zero,←add_assoc,char_two,zero_add]
    rw [hh]
    unfold Pulsar.shift
    have hx : g x.l x.q j=(g x.l x.q j+a.gamma*x.q)+a.gamma*x.q :=
      Eq.symm (by rw [add_assoc,char_two,add_zero])
    apply not_congr
    constructor
    · intro h; rw [h,←hx]
    intro h; exact add_right_cancel (h.trans hx)
  change shot u s i x y (g.shift a.gamma) ≤_
  unfold shot; simp_rw [he]; exact hz

set_option maxHeartbeats 900000 in
theorem quotes (d e:Dict p r)
    {ε β δ:ℝ} (hs:reports p r u s β δ) (ht:reports p r u t β δ) (h:origami p r u δ)
    (z:DualCoefficients A B) (hh:z.left ≠0 ∨ z.right≠0)
    (P Q:Stalls p) (hc:Stirrings p r u s t z P Q ε)
    (L:ℕ) (hA:anthology p r u s d L (3*ε)) (hB:anthology p r u t e L (3*ε))
    (hp:∀ i,(P i).card≤L)(hq:∀ i,(Q i).card≤L):
    announced u s e L (3*(3*ε)) ∨ announced u t d L (3*(3*ε)) := by
  classical
  choose f ha hb using hc.recollect
  have he (s: Quota) (h:s≠0): ∃ i:Nodes,s i=1 := by
    by_contra! hf; exact h (funext (fun i=> (bit_cases _).resolve_right (hf i)))
  rcases hh with h1|h1
  · obtain ⟨i,hi⟩:= he z.left h1
    let S j:= leftChime z (j,i); let T j:= rightChime z (j,i)
    let m : Memo:=(i,fun j=>((T j).bit,(T j).gamma,(S j).gamma))
    refine Or.inl ⟨m,fun j=>(S j).coal, fun j=>1+(S j).headBit,P, fun j=>⟨hp j,?_⟩⟩
    exact praise_tidy e u s t hs h L P Q j i (S j) (T j) (f (j,i)) hi hB (hq i)
      (ha (j,i)) (hb (j,i))
  obtain ⟨i,hi⟩:= he z.right h1
  let S j:= rightChime z (i,j); let T j:=leftChime z (i,j)
  let m : Memo:=(i,fun j=> ((T j).bit,(T j).gamma,(S j).gamma))
  refine Or.inr ⟨m,fun j=>(S j).coal,fun j=>1+(S j).headBit,Q,fun j=>⟨hq j,?_⟩⟩
  exact praise_tidy d u t s ht h L Q P j i (S j) (T j) (f (i,j)) hi hA (hp i) (hb (i,j)) (ha (i,j))

end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PositiveTestMass
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive Test Mass -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Function Filter Finset LinearMap Module
open scoped BigOperators Topology
open Template
variable {p:Shape} {n N K M s0 r :ℕ}
namespace StatusAnalysis
open PreparationParameters Station PredictionClass Club Guild DualAnalysis
variable {q:PreparationParameters} {w:LeafMixture p n N}

theorem engagedBudget (p:Shape) (K:ℕ) {η:ℝ} (h:0<η) :
    ∃ a,supportBudget p K η a := by
  classical
  let F (i:Scrip p K) := i.2.2.momus*η^Fintype.card (Messenger (toFormat i.1.1))
  have hf i:0<F i := mul_pos (mul_pos (kappa_pos _) (kappa_pos _)) (pow_pos h _)
  cases isEmpty_or_nonempty (Scrip p K)
  next h => exact ⟨1,zero_lt_one,fun i=>(h.false i).elim⟩
  next h =>
    let g:=univ.image F
    have he:g.Nonempty:=image_nonempty.mpr univ_nonempty
    refine ⟨g.min' he, ?_,fun i=> min'_le _ _ (mem_image_of_mem _ (mem_univ _))⟩
    obtain ⟨i,hi,h⟩:=mem_image.mp (min'_mem _ he)
    exact h ▸ hf i

set_option maxHeartbeats 1400000 in
theorem inform (w:LeafMixture p n N) (v:Station p n N K w)
    (m:Mixer p n) (Y:Silhouette p N r) (i j:Aspect p n N w)
    (hc:PreparationParameters.frameSide p m i.2) (he:PreparationParameters.frameSide p m j.2)
    (ha:(w.pin i.1.val).agree i.2) (hb:(w.pin j.1.val).agree j.2)
    (d e:Stakes K)
    (h1:charted (v.cAxes i.1 (toRates d)) (w.pin i.1.val).sp)
    (h2:charted (v.cAxes j.1 (toRates e)) (w.pin j.1.val).sp)
    {η a:ℝ} (h : supportBudget p K η a)
    (x y:Stalls p) (hx:booths p K (w.pin i.1.val).sp x)
    (hy:booths p K (w.pin j.1.val).sp y)
    (P Q:Stalls p) (hF:x≤P)(hG:y≤Q)
    (hg:3≤p.g)(hp:1≤p.J)(hη:0<η)
    (k:Fin (2^deckMax p K))
    (hk:berthTicket (w.pin i.1.val) (w.pin j.1.val) (v.mails i.1 j.1 k) (i.2,j.2))
    (S:Straps (Label p.b)) :
    let X:= v.cAxes i.1 (toRates d); let W:=v.cAxes j.1 (toRates e)
    let C:=stellar (wisp p Y) (wake p Y m i.2 X) (wake p Y m j.2 W) η P Q
    (∀ i:Grid,(C i).travels S 100 (view _ _) (chapter C S i)) →
    scorecard (chapter C S) (hailing p X W (v.mails i.1 j.1 k)) →
    eligiblePair v m i j Y a := by
  classical
  intro X W C hA hB
  obtain ⟨q,g,F,G,hT,hU⟩:=processions p K P Q _ _ X W (v.mails i.1 j.1 k) h1 h2 hk.1 hk.2.1 x y hx hy
    hF hG (by omega) hp S hA hB
  let z:=g.binding p F G
  let I:Scrip p K:=⟨(q,d,e),k,z⟩
  refine ⟨I,hT.1,?_⟩
  obtain ⟨hL,hR⟩:= berth_flags _ _ _ hk ha hb
  have hC :
      v.frontPage z m i.1 j.1 k i.2∧v.backPage z m i.1 j.1 k j.2 :=
    ⟨⟨hT,ha,hc,hL⟩,⟨hT,hb,he,hR⟩⟩
  change _≤ ind _ * z.constellation i.2 j.2 X W m Y
  rw [ind_one hC,one_mul]
  refine (h.2 I).trans (mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (kappa_pos _).le (kappa_pos _).le))
  let J:=Messenger (toFormat q)
  have hi (x:J):η ≤ z.chimera i.2 j.2 X W m Y x := (hU x).trans_eq
    (Engagement.solicit ..).symm
  exact le_trans (le_of_eq (show η^Fintype.card J=∏ _:J,η by simp)) (Finset.prod_le_prod
    (fun i _=> hη.le) fun i _=> hi i)

variable {U : Wgt (UnitType p n N)} {m : Mixer p n}

theorem troupe_bill (h:Lead U w m q) :
    IsLaw (troupe w U) ∧ mapW (troupe w U) Prod.snd=w.sap U := by
  classical
  obtain ⟨h1,h2⟩:=rebuild h.law.nz h.strength.part
    (fun i hi=>(h.strength.leaf _ hi).pos) h.amount
  have hk i:IsLaw (partW U (Subtype.val (show w.T from i))):=on_law h.law.nz (h.strength.leaf _
    i.property).pos
  constructor
  · constructor
    · intro x; exact mul_nonneg (h1.nz _) ((hk _).nz _)
    unfold troupe; rw [semi_total]; simp_rw [(hk _).total]; exact h1.avg_const _
  change _=allW U w.T; rw [h2]; funext i
  unfold mapW mixW pr troupe; rw [semi_avg]
  simp_rw [show ∀ w':↥w.T,avg (partW U w'.val) (fun x=> ind (x=i))=partW U w'.val i from
    (fun w=> pr_point' ..)]

theorem troupe_home (h:Lead U w m q) (x: Aspect p n N w) (hx:troupe w U x≠0):
    x.2∈x.1.val∧w.rooting x.2=(w.pin x.1.val).sp∧frameSide p m x.2∧ (w.pin x.1.val).agree x.2 := by
  have he : x.2∈x.1.val := (onW_ne (right_ne_zero_of_mul hx)).1
  exact ⟨he, congrArg Pin.sp (LeafMixture.poller_eq w h.strength.part x.1.property he),h.coverC _
    x.1.property x.2 he,(h.strength.leaf _ x.1.property).fixpin x.2 he⟩
theorem cirque_unit (w:LeafMixture p n N) (h: Lead U w m q) :
    mapW (cirque w U) (fun i=>(i.1.2,i.2.2)) = pairW (w.sap U) (w.sap U) := by
  classical
  have hk:=map_pair_law (troupe w U) (troupe w U) Prod.snd Prod.snd
  rw [(troupe_bill h).2] at hk; exact hk
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteComparisonBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Comparison Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Function Finset Module LinearMap Filter
open scoped BigOperators Topology
open Template
variable {p:Shape} {n N K M r s0:ℕ}
namespace StatusAnalysis
open PreparationParameters Station PredictionClass DualAnalysis Club Guild

theorem trimBeta_pos (p:Shape) (K:ℕ): 0<trimBeta p K:=half_pos (basebeta_pos _ _)

theorem cheapFest (p : Shape) (K:ℕ) (a:ℝ) (h:0<a) :
    ∃ ε η:ℝ,0<ε∧ε≤a∧Jubilee p K ε η := by
  let β:=trimBeta p K; have hβ:0<β:=trimBeta_pos p K
  let ε:= min a (min (β/14) (β^2/4)); let y:= playbook p K
  have hy:0<y:=playbook_pos _ _
  have he:0<ε:=lt_min h (lt_min (by positivity) (by positivity))
  have hF:=show ε≤β^2/4 from le_trans (min_le_right ..) (min_le_right ..)
  have hz:y*(ε/y)=ε:=by field_simp
  refine ⟨ε,ε/y,he,min_le_left ..,⟨div_pos he hy,hz.le,hz.trans_lt (hF.trans_lt ?_),?_⟩⟩
  · change β^2/4<1/2*β^2; nlinarith only [hβ]
  have hh:ε≤β/14:=le_trans (min_le_right ..) (min_le_left ..)
  change _<1/2*β; linarith only [hβ,hh]

variable {b:PreparationParameters}
theorem boothseek (q:PreparationParameters) (s:Plan p n) (p0 X:Stalls p)
    (h:booths p q.pins s p0) (hq:AnalyticParameters p M q s0) (hh:∀ i,(X i).card≤q.B):
    seeking p (p0⊔X) := by
  intro i
  have hf : ((p0⊔X:Stalls p) i).card≤(p0 i).card+(X i).card:= card_union_le ..
  have hi:= h.1 i; have he:= hh i; have hx:= hq.forbid; have hh:= hq.spare
  omega

theorem outcard (p:Shape) (s:Stalls p) (S : Straps (Label p.b))
    (h:seeking p s) (hs:sizeB S 800) (i j:Bool) :
    (outstraps s S i j).card < Fintype.card (Label p.b):= by
  apply lt_of_le_of_lt (card_union_le ..)
  have hv:=h j; have hg:= hs i; omega

variable {w:LeafMixture p n N} {m:Mixer p n}
theorem sickBound (U:Wgt (UnitType p n N)) (v:Station p n N b.pins w) (Y:Silhouette p N r)
    (h: Lead U w m b) (a ε δ τ:ℝ)
    (hp:Beams b m Y w U v a ε δ τ) :
    let P (i : Aspect p n N w):=¬gauze p δ δ Y m b.pins i.2
    pr (troupe w U) P ≤ τ ∧ pr (cirque w U) (fun x=> P x.1∨P x.2) ≤ τ+τ := by
  classical
  intro P
  let μ:=troupe w U; have hi:= (troupe_bill h)
  have hh :pr μ P ≤ τ := ((mapW_pr μ Prod.snd (fun i=>¬gauze p δ δ Y m b.pins i)).symm).trans_le
    (hi.2.symm ▸ hp.rare)
  refine ⟨hh,?_⟩
  apply (pr_or_le (pairW_law hi.1 hi.1).nz).trans
  refine add_le_add ?_ ?_
  · refine le_trans ?_ hh
    have h:= pairW_pr μ μ P (fun _=>True)
    have hl : IsLaw μ:=hi.1
    exact le_of_eq (by simpa [hl.total] using h)
  refine le_trans ?_ hh
  have h:=pairW_pr μ μ (fun _=> True) P
  have hl:IsLaw μ:=hi.1
  exact le_of_eq (by simpa [hl.total] using h)

theorem ready_loupe (w:LeafMixture p n N) (u:Station p n N b.pins w) (hu:u.bank)
    (h:AnalyticParameters p M b s0) (he:∀ i:w.T,planRank (w.pin i.val).sp ≤ b.pins) :
    ∃ t,Shipped w b.pins u t := by
  classical
  choose d hd using fun i:w.T=>sizedCharts _ _ _ hu i (he i)
  choose S hS using fun i:w.T=> buildBooths _ _ (he i) h.penRoom
  exact ⟨⟨d,S⟩,hd,hS⟩
variable (w:LeafMixture p n N) (L:Loupe p n N b.pins w) (t:Station p n N b.pins w)

set_option maxHeartbeats 800000 in
theorem routeLive (h:Shipped w b.pins t L) (m:Mixer p n)
    (H: AnalyticParameters p M b s0) (hn:2*p.r≤n)
    (x:Aspect p n N w) (Y: Silhouette p N r)
    (δ:ℝ)(he:0<δ) (hk:planRank (w.pin x.1.val).sp ≤b.pins)
    (hp:gauze p δ δ Y m b.pins x.2) :
    reports p r (wisp p Y) (wake p Y m x.2 (routeC w L t x)) (trimBeta p b.pins) δ := by
  apply plume_reports p b.pins m Y (w.pin x.1.val).sp _ _ (h.charts x.1)
    _ hk H.enter.first.hG H.enter.first.hR hn δ he hp
  intro i; exact Nat.lt_succ_iff.mp (L.r x.1 i).isLt
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ForbiddenPredictions
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Forbidden Predictions -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Module LinearMap Finset Function
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
open PreparationParameters Station PredictionClass Club Guild DualAnalysis
variable {p : Shape} {n N M r s0 K : ℕ} {w:LeafMixture p n N} {b:PreparationParameters}

set_option maxHeartbeats 1200000 in
theorem witnessed_cost (w:LeafMixture p n N) (v:Station p n N b.pins w) (L:Loupe p n N b.pins w)
    (h:Shipped w b.pins v L)
    (m:Mixer p n) (Y:Silhouette p N r)
    (δ ε a:ℝ) (U:Wgt (UnitType p n N)) (d:Dict p r)
    (hp:Lead U w m b) (hq:AnalyticParameters p M b s0) (hn:2*p.r≤n)
    (hδ:0≤δ) (he:0≤ε) (ht:(ε+δ)*2≤a)
    (hy:¬b.predicts p N m w U a) :
    pr (troupe w U) (witnessed w v L m Y δ ε b.B d) ≤ 0.001 := by
  classical
  let t:=troupe w U
  let F (i:Memo) := fun j=>fromPulse Y (Memo.words d i j)
  let P (i : Memo) (x : UnitType p n N):=∃ l B α,b.seems p m w x (F i) l B α a
  have hT:=troupe_bill hp
  have hi :
      pr t (fun i=>∃ j,P j i.2) ≤0.001 := by
    refine ((pr_exists_le hT.1.nz _).trans
      ((Finset.sum_le_sum (g:=fun _=>0.000001) fun i _ => ?_).trans ?_))
    · have hh : pr t (fun x=>P i x.2)=pr (w.sap U) (P i) := by
        rw [←hT.2,mapW_pr]
      rw [hh]; exact le_of_not_ge (fun he=> hy ⟨F i,he⟩)
    rw [Finset.sum_const,card_univ,memo_card]
    norm_num
  refine (pr_on_mono hT.1.nz ?_).trans hi
  rintro x hx ⟨hβ,i,q,r,S,hγ⟩
  let Q:=routeC w L v x
  have hm k:= praise_predict Q Y k x.2 m (q k) (r k) (Memo.words d i k)
    (S k) he hδ hq.enter.first.hR hn
    (fun z hz=> (hβ k z).1 hz) ((hγ k).2)
  have hh:=troupe_home hp x hx
  refine ⟨i,(fun i=>Q i (q i)), S,r,fun j=>⟨(hγ j).1,?_⟩,
     fun j i hi x v => (hm j i hi x v).trans ht⟩
  rw [hh.2.1,←(h.charts x.1 j).1]; exact mem_range_self _ _

set_option maxHeartbeats 2000000 in
theorem no_out (w:LeafMixture p n N) (b:PreparationParameters)
    (m:Mixer p n) (Y:Silhouette p N r) (U:Wgt (UnitType p n N))
    (v:Station p n N b.pins w) (ε η a δ τ:ℝ)
    (h:Lead U w m b) (ht:v.bank) (he:AnalyticParameters p M b s0) (hn:2*p.r≤n)
    (hp:Jubilee p b.pins ε η) (hε:0<ε)
    (hB:supportBudget p b.pins η a)
    (hv:Beams b m Y w U v a ε δ (1/16))
    (hτ:(9*ε+ε)*2≤τ) (hh:¬b.predicts p N m w U τ)
    (hu:0.99 < pr (pairW (w.sap U) (w.sap U)) (secureAt p w.rooting)) :
    False := by
  classical
  let W:=Aspect p n N w; let K:=b.pins; let L:=troupe w U; let V:=cirque w U
  let u:=wisp p Y
  let β:=trimBeta p K
  let S (x:W):=gauze p δ δ Y m K x.2
  have hK i: planRank (w.pin (Subtype.val (show w.T from i))).sp ≤ K :=
    (h.strength.leaf _ i.property).bound
  obtain ⟨g,hg⟩:= ready_loupe w v ht he hK
  let f (x:W):=routeC w g v x
  let Q (x:W):=wake p Y m x.2 (f x)
  have ht' := he.enter.first
  have hd (x:W) (hx:S x) : reports p r u (Q x) β δ :=
    routeLive w g v hg m he hn x Y δ hv.haze.1 (hK x.1) hx
  have hL:2*b.B<Fintype.card (Label p.b) := by have hi:=he.spare; omega
  have hβ:=trimBeta_pos p K
  choose d hD using show ∀ x:W,∃ d:Dict p r,S x→anthology p r u (Q x) d b.B (3*ε) from by
    intro x
    by_cases hx:S x
    · obtain ⟨d,ht'⟩:= build_anthology u (Q x) hv.soft (hd x hx)
       (show 3*ε+3*ε<1/2*β by linarith only [show _ < 1/2*β from hp.low])
       hβ.le ht'.hG b.B hL
      exact ⟨d,fun _=>ht'⟩
    exact ⟨0,fun h=>(hx h).elim⟩
  let X (x:W×W):= secureAt p w.rooting (x.1.2,x.2.2)
  let Y1 (x:W×W):= witnessed w v g m Y δ (9*ε) b.B (d x.2) x.1
  let Y2 (x:W×W):= witnessed w v g m Y δ (9*ε) b.B (d x.1) x.2
  let Z (x:W×W):=¬ S x.1∨¬ S x.2
  let P (x:W×W):=eligiblePair v m x.1 x.2 Y a
  have hF:∀ i,V i ≠0 → X i→ ((Z i∨P i)∨ (Y1 i∨Y2 i)) := by
    intro i hi hk
    by_cases hQ:Z i∨P i
    · exact Or.inl hQ
    have ha1:S i.1:=not_not.mp (mt (fun x=>Or.inl (Or.inl x)) hQ)
    have ha2:S i.2:=not_not.mp (mt (fun x=>Or.inl (Or.inr x)) hQ)
    let A:=g.H i.1.1; let B:=g.H i.2.1
    let C:= stellar u (Q i.1) (Q i.2) η A B
    have hk0 (i t) := Nat.lt_succ_iff.mp (g.r i t).isLt
    have hz i:seeking p (g.H i):=by
      have h:= boothseek b _ (g.H i) ⊥ (hg.baseline i) he (fun _=>Nat.zero_le b.B)
      rwa [sup_bot_eq] at h
    have hC : rich C := plenitude hv.soft (hd _ ha1) (hd _ ha2) ht'.hG A B (hz _) (hz _)
      hβ hp.pos hp.sturdyR (hk0 _) (hk0 _)
    obtain ⟨E,hE,hI⟩:=stable C hC
    have hm0:= troupe_home h i.1 (left_ne_zero_of_mul hi)
    have hm1:= troupe_home h i.2 (right_ne_zero_of_mul hi)
    obtain ⟨k,hk⟩:= issueTicket _ _ w v i.1.1 i.2.1 h.strength.part hm0.1 hm1.1 ht hk
    let T:= v.mails i.1.1 i.2.1 k
    let R:= hailing p (f i.1) (f i.2) T
    by_cases hV:scorecard (chapter C E) R
    · exact (hQ (Or.inr (inform w v m Y i.1 i.2 hm0.2.2.1 hm1.2.2.1
        hm0.2.2.2 hm1.2.2.2 (g.r _) (g.r _) (hg.charts _) (hg.charts _) hB A B (hg.baseline _)
        (hg.baseline _) A B le_rfl le_rfl ht'.hG he.jump hp.pos k hk E hI hV))).elim
    obtain ⟨z,hz1,hz2,hz3⟩ := jargon_score _ _ hV (rich_covers C hC E (fun x=>(hE x).trans (by norm_num)))
    have hStory: countStory p K η δ ε β u:=⟨hv.soft,hβ.le,hε.le,hp.pos.le,hp.book,hp.low⟩
    let G0:=outstraps A E true; let G1:=outstraps B E false
    have hE0 (j):= outcard p A E (hz _) hE true j
    have hE1 (j):= outcard p B E (hz _) hE false j
    have hT:= tells z hStory (hd _ ha1) (hd _ ha2) A B E hz2 (hk0 _) (hk0 _) hE0 hE1 ht'.hG
    have hu i (j k:Bool): (outstraps (g.H i) E j k).card≤ b.B:= by
      refine (card_union_le ..).trans ?_
      have hi:=(hg.baseline i).1 k; have hh:= hE j; have hx:= he.forbid; omega
    right
    have hh:=quotes (d i.1) (d i.2) (hd _ ha1) (hd _ ha2) hv.soft z hz1 G0 G1 hT b.B
      (hD _ ha1) (hD _ ha2) (hu _ _) (hu _ _)
    rw [show 3*(3*ε)=9*ε from by ring] at hh
    exact hh.elim (fun h=>Or.inl ⟨ha1,h⟩) (fun h=>Or.inr ⟨ha2,h⟩)
  have hL:IsLaw L:= (troupe_bill h).1
  have hz0 (i:W): pr L (witnessed w v g m Y δ (9*ε) b.B (d i)) ≤ 0.001 :=
    witnessed_cost w v g hg m Y δ (9*ε) τ U (d i) h he hn hv.haze.1.le (by linarith)
      (by linarith only [hτ,hv.haze.2]) hh
  have hZ1: pr V Y1 ≤ 0.001 := by
    unfold pr V cirque; rw [pairW_avg,avg_avg]; exact hL.avg_le hz0
  have hZ2: pr V Y2 ≤0.001 := by unfold pr V cirque; rw [pairW_avg]; exact hL.avg_le hz0
  have hO:IsLaw V:=pairW_law hL hL
  have hX :0.99 < pr V X := by rw [←cirque_unit _ h,mapW_pr] at hu; exact hu
  have hP:= show pr V P≤1/16 from hv.zone
  have hZ:= show pr V Z ≤ 1/16+1/16 from (sickBound U v Y h _ _ _ _ hv).2
  have hx: pr V X≤(1/16+1/16+1/16)+(0.001+0.001):=
    ((pr_on_mono hO.nz hF).trans (pr_or_le hO.nz)).trans
      (add_le_add ((pr_or_le hO.nz).trans (add_le_add hZ hP)) ((pr_or_le hO.nz).trans
        (add_le_add hZ1 hZ2)))
  linarith only [hX,hx]
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PredictionClassBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prediction Class Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Function Module LinearMap Matrix
open scoped BigOperators Topology
open Template
variable {p:Shape} {n N r M K s0:ℕ}
namespace StatusAnalysis
open PreparationParameters Station PredictionClass DualAnalysis Club Guild
variable {w:LeafMixture p n N} {b:PreparationParameters} {B:Sketch p M}
variable {d e: Rates}

set_option maxHeartbeats 1200000 in
theorem laysScore (p:Shape) (K:ℕ)
    (Y: Silhouette p N r) (m: Mixer p n) (U:Terrain p r)
    (x y:UnitType p n N) (z:BMark p n N)
    (d e:Rates)
    (X:Charts p n d) (V:Charts p n e)
    (c:PredictionClass) (g:PredictionData p d e r)
    (A B:Stalls p)
    (S:Straps (Label p.b)) (η ε β δ τ:ℝ)
    (hx:coordSpec z x X g.X)(hy:coordSpec z y V g.Y)
    (h:chorusClass p g U c τ)(hτ:0≤τ)(hl:2*τ<1)
    (ht:countStory p K η δ ε β U)
    (ha:reports p r U (wake p Y m x X) β δ)
    (hb:reports p r U (wake p Y m y V) β δ)
    (hs:g.colored U (wake p Y m x X) (wake p Y m y V) A B (2*ε))
    (hk:∀ i,d i≤K^2)(hq:∀ i,e i≤K^2)
    (hg:3≤p.g)(hμ:10*ε≤τ)
    (hA:seeking p A)(hB:seeking p B)
    (he:sizeB S 800)
    (T:Cross p n)
    (hF:glint p (z x)=glint p (z y))
    (hQ:c.compatible g.α (glint p (z x))
       (cardTone z x T,cardTone z y (reciprocal p T))) :
    let C:=stellar U (wake p Y m x X) (wake p Y m y V) η A B
    Guild.rich C→scorecard (chapter C S) (hailing p X V T) := by
  classical
  intro C hC
  by_contra hc
  obtain ⟨j,h1,h2,h3⟩:= jargon_score _ _ hc (rich_covers C hC S (fun i=>(he i).trans (by norm_num)))
  let L:= wake p Y m x X; let R:=wake p Y m y V
  let A':=outstraps A S true; let B':=outstraps B S false
  have hS:g.colored U L R A' B' (2*ε):= by
    exact ⟨fun i z hz=> hs.1 i z (mt (Finset.mem_union_left _) hz),
      fun i z hz=> hs.2 i z (mt (Finset.mem_union_left _) hz)⟩
  have hh i:= duet_edge g j i hg ht.h ha hb A' B' hS (outcard p A S hA he _ _)
    (outcard p B S hB he _ _) (counter_bill j ht ha hb _ _ S i h2 (hk _) (hq _)) ht.he
    (show 0 ≤ 2*ε from by linarith only [ht.he]) ht.hb (show 3*ε+2*ε<1/2*β from
      by linarith only [ht.high,ht.he])
  apply h3
  refine harmony g U c τ z x y T X V hx hy hg h ht.h.1 hF hQ j hτ hl h1
    (fun i=>⟨(hh i).1,(hh i).2.1⟩) (fun i=>⟨(hh i).2.2.1,(hh i).2.2.2.1⟩)
    (fun i l q=>((hh i).2.2.2.2 l q).trans (by linarith only [hμ]))

theorem paintChorus (c:PredictionClass) (Y:Silhouette p N r) (f:Bool→ Pulsar p r)
    (u:Bool→Augur p N) (α:Party) (τ:ℝ)
    (h:hue c Y f u α τ) (A:styles d) (B:styles e) :
    chorusClass p (⟨α,f,A,B⟩:PredictionData p d e r) (wisp p Y) c τ := by
  classical
  refine ⟨h.consistent,?_,?_⟩
  · intro hg i j l k; change f i j l k=0; rw [h.atDawn hg]; rfl
  intro j hc ha hb x y
  obtain ⟨he,hf⟩:= ha (x,y)
  apply h.recording.2 x y (j.left y) (j.right x) (j.gam (x,y)) (he.symm.trans hf)
  intro l q
  specialize hb (x,y) l q
  unfold tabRef assembly; rw [← h.pulse_eq hc x,← h.pulse_eq hc y]
  unfold ChorusCost wisp at hb; rw [mapW_pr] at hb; exact hb

set_option maxHeartbeats 900000 in
theorem crew_praise (p:Shape) {q: PreparationParameters} (c:PredictionClass) (Y:Silhouette p N r)
    (f:Bool→ Pulsar p r) (u:Bool→Augur p N) (α:Party) (τ:ℝ) (h:hue c Y f u α τ)
    (m:Mixer p n)(A:Charts p n d)(g:styles d)(w:BMark p n N)
    (x:UnitType p n N) (H S : Stalls p) (hS:H ≤ S)(hp:coordSpec w x A g)
    {δ ε:ℝ} (he:0≤ε)(hd:δ≤ε) (ht:AnalyticParameters p M q s0)(hn:2*p.r≤n)
    (hf:claimed p x u m (w x) α H (scanPrice p*ε))
    (hg:c=dusk → exactInk p m w x) (hG:gauze p δ δ Y m q.pins x):
    ∀ i,praise (wisp p Y) (wake p Y m x A) i (S i) (yokeSet (g i) (α i)) (f i) (2*ε) := by
  classical
  intro i a ha hz
  let L:=S i
  have hk : postulates p (onSide x i) (fromPulse Y (f i)) (compass i x A m (g i) (α i))
      (H i) (scanPrice p*ε) := by
    unfold compass; rw [hp i]
    by_cases hC:c=dusk
    · have heq:= dusk_lit α (hC ▸ h.consistent)
      rw [heq,h.atDawn hC i]
      intro s hs z v
      have hj (y:Knobs p.g n): ¬mismatch p (fromPulse Y 0) (yoke p m x i (w x i) 1) z s v
        (onSide x i) y := by
        exact fun hk=>hk (show _= (0:F) from hg hC i _ (mem_useAtom ..))
      simp_rw [eq_false (hj _),pr_false]; exact mul_nonneg (scanPrice_pos _).le he
    rw [h.pulse_eq hC]; exact hf i
  have hi:= ht.enter.first
  exact (predict_praise A Y i x m (g i) (α i) (f i) (H i) he hi.hR hn
    (fun a h=> (hG i a).1 h) hk a (fun hx=>ha (hS i hx)) hz).trans
      (show ε+δ ≤ 2*ε from by linarith only [hd])

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CompatiblePairTests
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatible Pair Tests -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Function Module LinearMap Matrix
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
open PreparationParameters Station PredictionClass Club Guild DualAnalysis
variable {p:Shape} {n N M r s0:ℕ}
    {w:rhythms p M} {b:PreparationParameters}

set_option maxHeartbeats 1800000 in
theorem foretold (w:rhythms p M) (m:cycleM p) (x:Sketch p M)
    (v:Station p n (M*n) b.pins (w n)) (hv:v.bank)
    (U:Wgt (UnitType p n (M*n))) (h:Lead U (w n) (m n) b)
    (hE:AnalyticParameters p M b s0)
    (hm:(w n).within (engrave x b m w n))
    (hn:2*p.r≤n) (Y:Silhouette p (M*n) r) (f:Bool→Pulsar p r)
    {τ ε δ η a d0:ℝ} (hh: hue x.c Y f (fun i=>x.g i n) x.α τ)
    (hε:0<ε) (hp:Jubilee p b.pins ε η)
    (hB:supportBudget p b.pins η a)
    (hz:x.ε n ≤ scanPrice p*ε) (ht:10*ε≤τ) (hT:2*τ<1)
    (hF:Beams b (m n) Y (w n) U v a ε δ d0) (i : ViewPair p n (M*n) (w n))
    (hx:cirque (w n) U i ≠0)
    (hg1:gauze p δ δ Y (m n) b.pins i.1.2) (hg2:gauze p δ δ Y (m n) b.pins i.2.2)
    (hC:matchProg x n (i.1.2,i.2.2))
    (hS:secureAt p (w n).rooting (i.1.2,i.2.2)) :
    eligiblePair v (m n) i.1 i.2 Y a := by
  classical
  let s:=w n; let μ:= U; let K:=b.pins
  let X:=i.1.2; let Z:=i.2.2
  let j:=i.1.1; let k:=i.2.1
  let L:=troupe s μ
  have hs : L i.1≠0:=left_ne_zero_of_mul hx
  have hl : L i.2 ≠0:=right_ne_zero_of_mul hx
  have hX := troupe_home h i.1 hs
  have hZ:= troupe_home h i.2 hl
  have hL i:= (h.strength.leaf _ (Subtype.prop (show s.T from i))).bound
  obtain ⟨g,hg⟩:= ready_loupe s v hv hE hL
  let d:= g.r j; let e:=g.r k
  let t:=v.cAxes j (toRates d); let u:=v.cAxes k (toRates e)
  let A:=g.H j; let B:=g.H k
  let m':=x.m n
  let F:=x.L n X; let H:=x.L n Z
  let P:= A⊔F; let Q:=B⊔ H
  obtain ⟨⟨h1,h2⟩,h3,h4⟩:=hm _ j.property X hX.1
  obtain ⟨⟨h1',h2'⟩,h3',h4'⟩:=hm _ k.property Z hZ.1
  let M0:=s.pin j.val; let M1:=s.pin k.val
  have he (i):m' X i∈ effective M0.sp i:= (hX.2.1 ▸ (h1 i).2)
  have he' i:m' Z i∈effective M1.sp i:= (hZ.2.1 ▸ (h1' i).2)
  choose T hP using fun i=> show m' X i∈LinearMap.range (t i) from
    (hg.charts j i).1.symm ▸ he i
  choose S hQ using fun i=> show m' Z i∈ LinearMap.range (u i) from
    (hg.charts k i).1.symm ▸ he' i
  let Γ:PredictionData p (toRates d) (toRates e) r := ⟨x.α,f,T,S⟩
  have ht0:= hE.enter.first
  let M' := m n
  let D:=wisp p Y; let X0:=wake p Y M' X t; let X1:=wake p Y M' Z u
  let β:=trimBeta p K
  let C:=stellar D X0 X1 η P Q
  have hk0 i t:=Nat.lt_succ_iff.mp (g.r i t).isLt
  have hA: reports p r D X0 β δ:=routeLive s g v hg M' hE hn i.1 Y δ hF.haze.1 (hL _) hg1
  have hB1: reports p r D X1 β δ:=routeLive s g v hg M' hE hn i.2 Y δ hF.haze.1 (hL _) hg2
  have hR := boothseek b _ (g.H j) F (hg.baseline j) hE (fun i=>(h1 i).1)
  have hR' := boothseek b _ (g.H k) H (hg.baseline k) hE (fun i=>(h1' i).1)
  have hG: rich C:= plenitude hF.soft hA hB1 ht0.hG P Q hR hR' (trimBeta_pos ..) hp.pos
    hp.sturdyR (hk0 _) (hk0 _)
  obtain ⟨E,hE0,hr⟩:=stable C hG
  obtain ⟨y,hy⟩:= issueTicket X Z s v j k h.strength.part hX.1 hZ.1 hv hS
  let U0:=v.mails j k y
  have hQ': x.c.compatible x.α (glint p (m' X)) (cardTone m' X U0,cardTone m' Z
      (reciprocal p U0)) := by
    change glint p _=_ at h3
    have he1 l: cardTone m' X U0 l=(quench p (delta m') (X,Z)).1 l:=
      (fitsTone m' X hy.2.2 he l).trans (actualTone m' X Z l)
    have he2 l:cardTone m' Z (reciprocal p U0) l=(quench p (delta m') (X,Z)).2 l:= by
      have hg := fits_recip hy.2.2; rw [reciprocal_actual] at hg
      exact (fitsTone m' Z hg he' l).trans (actualTone m' Z X l)
    rw [funext he1,funext he2,h3]; exact hC
  have hc: countStory p K η δ ε β D:=⟨hF.soft,(trimBeta_pos ..).le,hε.le,hp.pos.le,
    hp.book,hp.low⟩
  have hv : Γ.colored D X0 X1 P Q (2*ε):= by
    constructor
    · exact crew_praise p x.c Y f (fun i=>x.g i n) x.α τ hh (m n) t T m' X F P le_sup_right
        hP hε.le hF.haze.2 hE hn (fun i j hj k f=>(h2 i j hj k f).trans hz) h4 hg1
    exact crew_praise p x.c Y f (fun i=>x.g i n) x.α τ hh (m n) u S m' Z H Q le_sup_right
      hQ hε.le hF.haze.2 hE hn (fun i j hj k f=>(h2' i j hj k f).trans hz) h4' hg2
  have hZ0 := laysScore p K Y (m n) D X Z m' (toRates d) (toRates e) t u x.c Γ P Q
    E η ε β δ τ hP hQ (paintChorus _ _ f _ x.α τ hh T S) (by linarith only [hε,ht]) hT hc
    hA hB1 hv (hk0 _) (hk0 _) ht0.hG ht hR hR' hE0 U0 (h3.trans h3'.symm) hQ' hG
  exact inform (w n) v _ Y i.1 i.2 hX.2.2.1 hZ.2.2.1 hX.2.2.2 hZ.2.2.2 d e (hg.charts _)
    (hg.charts _) hB A B (hg.baseline _) (hg.baseline _) P Q le_sup_left le_sup_left ht0.hG
    hE.jump hp.pos y hy E hr hZ0

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FinalContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Final Contradiction -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Finset Module LinearMap Function
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
open PreparationParameters Station PredictionClass Club Guild DualAnalysis
variable {p:Shape} {n N M r s0:ℕ} {w:rhythms p M}
    {m:cycleM p} {u:tale p M} {b:PreparationParameters} {l:Filter ℕ}

private theorem focused (x:Sketch p M):
    ∃ (L:ℕ) (Y:∀ n,Silhouette p (M*n) L),∀ (n r:ℕ) (X:Silhouette p (M*n) r),
      refines X (Y n) → ∀ τ:ℝ, recital x.c p (fun i=>x.g i n) x.α τ →
        ∃ f:Bool→ Pulsar p r,hue x.c X f (fun i=>x.g i n) x.α τ := by
  classical
  let L:=Fintype.card (Bool→ F); let E:=Fintype.equivFin (Bool→F)
  let Y (n:ℕ):Silhouette p (M*n) L := fun i q y=> E (fun j=> x.g j n i q y)
  refine ⟨L,Y,fun n r X h τ ht=>?_⟩
  choose f hf using h
  by_cases he : x.c=dusk
  · exact ⟨0,ht.1,fun hh=>(hh he).elim,fun _ _=>rfl,ht⟩
  let g j i q k:= (E.symm (f i q k)) j
  have hv j: fromPulse X (g j)=x.g j n:= by
    unfold fromPulse g; funext i q y; rw [← hf]
    exact congr_fun (Equiv.symm_apply_apply E _) j
  exact ⟨g, ht.1,fun _=>hv,fun h=>(he h).elim,ht⟩

private theorem haveLeads (h:veil p M b s0 l m w u) :
    ∀ᶠ n in l,Lead (u n) (w n) (m n) b:= by
  filter_upwards [h.durableS.shape,h.moment,h.durableS.mass.positive] with n hn ht hh
  exact ⟨hn.1,hh,ht.1.law,hn.2⟩

set_option maxHeartbeats 1400000 in
theorem goldEnd (v:Stations p M b.pins w) (h:veil p M b s0 l m w u) (ht:∀ᶠ n in l,(v n).bank)
    (hs:l.NeBot) (x:Sketch p M)
    (hb:b.bright l p M m w x) (hf:glowOutcome l p M u w x) : False := by
  classical
  obtain ⟨A,hA,hF⟩:=hf
  obtain ⟨τ,hτ,hT⟩:=hb.forecasts.classes
  let B:=min τ (1/4); have hB:0<B:=lt_min hτ (by norm_num)
  let K:= b.pins
  obtain ⟨ε,η,he,hM,hC⟩:= cheapFest p K (B/10) (by positivity)
  obtain ⟨a,hp⟩:= engagedBudget p K hC.pos
  obtain ⟨L,Y,hY⟩:=focused x
  obtain ⟨r,d,hr⟩:=lightmap v h a ε (A/4) hp.1 he (by positivity) L Y
  have heE:=h.easel
  have hX:∀ᶠ n in l,False := by
    filter_upwards [haveLeads h,h.upright,ht,hb.engraved,hT,hF,hr,hb.forecasts.small
      _ (show 0 < scanPrice p*ε from mul_pos (scanPrice_pos _) he)]
      with n hn ht' h heq hf hξ hT hx_
    obtain ⟨X,hX,hP⟩:=hT
    have hh: recital x.c p (fun i=>x.g i n) x.α B := ⟨hf.1,fun i j s t r hi hg=>hf.2 i j s t r
      hi (fun i j=>(hg i j).trans (min_le_left ..))⟩
    obtain ⟨f,hf⟩:= hY _ _ X hX B hh
    let W:=KAspect (w n); let V:=cirque (w n) (u n)
    let H (i:W):=¬gauze p d d X (m n) K i.2
    let P (i:W×W):= eligiblePair (v n) (m n) i.1 i.2 X a
    let S := fun i:UnitType p n (M*n)×_=>matchProg x n i∧secureAt p (w n).rooting i
    let T:= fun i:W×W=> S (i.1.2,i.2.2)
    have hD i (hi: V i≠0)(hq:T i): ((H i.1∨H i.2) ∨ P i):=by
      by_cases hc:H i.1∨ H i.2
      · exact Or.inl hc
      refine Or.inr (foretold w m x _ h _ hn heE heq ht'.age X f hf he hC hp hx_
        (show 10*ε≤B from by linarith only [hM])
        (show 2*B<1 by have h: B≤1/4:=min_le_right ..; linarith only [h])
        hP i hi (not_not.mp (mt Or.inl hc)) (not_not.mp (mt Or.inr hc)) hq.1 hq.2)
    have hQ0 := (troupe_bill hn).1; have hV:IsLaw V:=pairW_law hQ0 hQ0
    have hV' : pr V T ≥ A := by
      unfold gilded at hξ; rw [←cirque_unit _ hn,mapW_pr] at hξ; exact hξ
    have h1 := (sickBound (u n) (v n) X hn _ _ _ _ hP).2
    have h2 : pr V T ≤ (A/4+A/4)+A/4:= ((pr_on_mono hV.nz hD).trans
      (pr_or_le hV.nz)).trans (add_le_add h1 hP.zone)
    linarith only [h1,h2,hV',hA]
  exact hX.exists.elim (fun _ h=>h)

set_option maxHeartbeats 1200000 in
theorem quietEnd (v:Stations p M b.pins w) (h:veil p M b s0 l m w u)
    (ht:∀ᶠ n in l,(v n).bank) (hs:l.NeBot)
    (hq:b.silenceOutcome l p M m u w) : False := by
  classical
  obtain ⟨τ,hτ,hQ⟩:=hq
  let K:=b.pins
  obtain ⟨ε,η,he,hM,hC⟩:= cheapFest p K (τ/20) (by positivity)
  obtain ⟨a,hp⟩:= engagedBudget p K hC.pos
  obtain ⟨r,d,hr⟩:=lightmap v h a ε (1/16) hp.1 he (by norm_num) 1
    (fun _ _ _ _=>0)
  have hF:∀ᶠ n in l, False := by
    filter_upwards [hr,hQ,ht,h.upright,haveLeads h] with n hn hq ht hi hx
    obtain ⟨X,_,hE⟩:=hn
    exact no_out (w n) b (m n) X (u n) _ _ _ _ _ τ hx ht h.easel hi.age hC he hp hE
      (by linarith only [hM]) hq.1 hq.2
  exact hF.exists.elim (fun _ hi=>hi)

theorem refuteVeil_oai (h:veil p M b s0 l m w u) (hs:l.NeBot)
    (hT: b.silenceOutcome l p M m u w ∨ b.predOutcome l p M m u w) :
    False := by
  classical
  have he :
      ∀ᶠ n in l, ∃ s:Station p n (M*n) b.pins (w n),s.bank := by
    filter_upwards [h.durableS.shape] with n hn
    exact Station.create (fun x=>(hn.1.leaf _ x.property).bound)
  obtain ⟨s,hq⟩:= taking he
  rcases hT with hP|⟨b,hf,hR|hR⟩
  · exact quietEnd s h hq hs hP
  · exact goldEnd s h hq hs b hf hR
  exact dim_end h s hq hs b hf hR
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

theorem solution : type_of% @OAI.HadwigerCounterexample.StatusAnalysis.refuteVeil_oai := @OAI.HadwigerCounterexample.StatusAnalysis.refuteVeil_oai
