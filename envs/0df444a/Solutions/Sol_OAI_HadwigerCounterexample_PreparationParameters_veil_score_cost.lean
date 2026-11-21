-- Prove2me | solution 1 for OAI.HadwigerCounterexample.PreparationParameters.veil.score_cost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T23:06:01.81621+00:00
-- url     : https://prove2.me/submissions/6f17690f-8170-4ca8-948d-32cf92312654

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
theorem odd_smul_bit {n : ℕ} (hn : Odd n) (x : F) : n • x = x := by
  obtain ⟨m,rfl⟩ := hn
  rw [add_smul, one_smul, mul_smul, two_smul,char_two,zero_add]

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ComponentIndices
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch
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

theorem Wtag_le (l : Tag p.g) : Wtag p n l ≤ Wspace p n :=
  Submodule.span_mono (by rintro m ⟨s,z,h,rfl⟩; exact ⟨s,z,rfl⟩)

theorem Wspace_sym {m : Moment p n} (h : m ∈ Wspace p n) : mᵀ = m := by
  unfold Wspace at h
  induction h using Submodule.span_induction with
  | mem m hm => obtain ⟨s,z,rfl⟩ := hm; rw [mom,transpose_vecMulVec]
  | zero => simp
  | add x y _ _ hx hy => rw [transpose_add,hx,hy]
  | smul b x _ hx => rw [transpose_smul,hx]

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

theorem atom_def (l : Tag p.g) (s : Label p.b) (z : Base p.g n) (e) :
    atom p l s z e = if inc e l then mom p s z else 0 := by
  change (Pi.single l (mom p s z) : Tag p.g → Moment p n) e.val.1 +
    (Pi.single l (mom p s z) : Tag p.g → Moment p n) e.val.2 = _
  by_cases h : e.val.1 = l
  · have h' : e.val.2 ≠ l := h ▸ e.property.ne.symm
    rw [Pi.single_eq_of_ne h',ite_eq_left (show inc e l from Or.inl h)]
    rw [h, Pi.single_eq_same,add_zero]
  by_cases h' : e.val.2 = l
  · rw [Pi.single_eq_of_ne h,ite_eq_left (show inc e l from Or.inr h'),h',Pi.single_eq_same,zero_add]
  rw [Pi.single_eq_of_ne h,Pi.single_eq_of_ne h',add_zero,ite_eq_right (by simp [inc,h,h'])]

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

theorem sharedT_cut {n} (hg : Odd p.g) (t : Tag p.g) (w : Tag p.g → Moment p n) :
    sharedT p n t (cut p n w) =
      (∑ i, etab p n Block.S (w i)) + etab p n Block.S (w t) := by
  simp only [sharedT,LinearMap.sum_apply,LinearMap.comp_apply,getPair_cut,map_add,
    Finset.sum_add_distrib,Finset.sum_const, Finset.card_univ]
  simp [Tag,odd_smul_bit hg]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AffineFrames
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Affine Frames -/

noncomputable section
namespace HadwigerCounterexample

open Matrix
open scoped BigOperators

variable {p : Shape} {n N : ℕ}

theorem T_diag (m : Mixer p n) (x : Profile p n) : Tsym m x x = role p n x := by
  have h (a b : F) : a*b+b*a=0 := by rw [mul_comm b a,char_two]
  simp only [Tsym_val,T0_val,char_two,h,Finset.sum_const_zero,add_zero,bit_sq]

theorem ufun_self {m : Mixer p n} {o : Orient p n N} (h : frameLaw m o) (x : Profile p n) :
    ufun o (Uembed o x) = 0 := by
  simp only [ufun,Uembed,LinearMap.coe_mk,AddHom.coe_mk]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mpair_liftM,liftM_def,← Matrix.mul_assoc,(h i).2.2.2.2,Matrix.zero_mul,
    Matrix.zero_mul,mpair_comm,map_zero]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_LinearExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear Extension -/

noncomputable section
namespace HadwigerCounterexample

open Matrix Module Submodule LinearMap Function

variable {V W U V' : Type}
variable [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
variable [AddCommGroup U] [Module F U] [AddCommGroup V'] [Module F V']

theorem mem_range_comp {f : V →ₗ[F] W} {g : V →ₗ[F] U} (h : ker f ≤ ker g) :
    ∃ L : W →ₗ[F] U, L ∘ₗ f = g := by
  obtain ⟨i,hi⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨L,hL⟩ := (g ∘ₗ i).exists_extend
  refine ⟨L,LinearMap.ext fun x => ?_⟩
  have hm := LinearMap.congr_fun hL (f.rangeRestrict x)
  change L (f x) = g _ at hm
  change L (f x) = _
  rw [hm]
  have heq : f (i (f.rangeRestrict x)) = f x :=
    congrArg Subtype.val (LinearMap.congr_fun hi (f.rangeRestrict x))
  have ha : i (f.rangeRestrict x) - x ∈ ker f := by rw [mem_ker,map_sub,heq,sub_self]
  simpa only [mem_ker,map_sub,sub_eq_zero] using h ha

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

theorem rk_add_le [FiniteDimensional F W] (f g : V →ₗ[F] W) :
    rk (f+g) ≤ rk f+rk g :=
  (Submodule.finrank_mono (show LinearMap.range (f+g) ≤ range f ⊔ range g by
    rintro x ⟨y,rfl⟩
    exact Submodule.add_mem_sup (show f y ∈ range f from ⟨y,rfl⟩)
      (show g y ∈ range g from ⟨y,rfl⟩))).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

end Generic

variable {I J K : Type}
variable [Fintype I] [Fintype J]

omit [Fintype I] in
theorem rank_cast (P : Mat I J) : P.rank = rk P.mulVecLin := rfl
theorem dim_vec (K : Type) [Fintype K] : dim (Vec K) = Fintype.card K :=
  Module.finrank_pi F

omit [Fintype I] in
theorem mrk_inj {P : Mat I J} : Function.Injective P.mulVec ↔ P.rank = Fintype.card J := by
  rw [rank_cast,← dim_vec,rk_inj.symm]; rfl
theorem mrk_surj {P : Mat I J} : Function.Surjective P.mulVec ↔ P.rank = Fintype.card I := by
  rw [rank_cast,← dim_vec,rk_surj.symm]; rfl

theorem transpose_surj_iff {P : Mat I J} : Surjective Pᵀ.mulVec ↔ Injective P.mulVec := by
  rw [mrk_surj,mrk_inj,rank_transpose]

theorem mrk_add_le (A B : Mat I J) : (A+B).rank ≤ A.rank + B.rank := by
  rw [rank_cast,rank_cast,rank_cast,mulVecLin_add]; exact rk_add_le _ _

omit [Fintype I] in
theorem colSp_dim (P : Mat I J) : dim (colSp P) = P.rank := rfl

omit [Fintype I] in
theorem colSp_mem {P : Mat I J} (j : J) : P.col j ∈ colSp P := by
  rw [colSp,range_mulVecLin]
  exact Submodule.subset_span ⟨j,rfl⟩

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MatrixFactorization
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matrix Factorization -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module
open scoped BigOperators
variable {I J Q : Type} [Fintype I] [Fintype J] [Fintype Q]

/-- Projecting the columns onto their literal column space keeps the matrix. -/
theorem invariant_cols (M : Mat I J) (Z : Mat I Q) (R : Mat Q I) (e : colSp Z = colSp M)
    [DecidableEq Q] (hr : R*Z=(1:Mat Q Q)) :
    Z * (R*M) = M := by
  apply coe_mv_inj
  apply LinearMap.ext
  intro v
  change _ *ᵥ v = M *ᵥ v
  simp only [← Matrix.mulVec_mulVec]
  have h : M*ᵥv ∈ colSp Z := e.symm ▸ (show M*ᵥv ∈ colSp M from ⟨v,rfl⟩)
  obtain ⟨x,hx⟩ := h
  change Z*ᵥx=M*ᵥv at hx
  rw [← hx, Matrix.mulVec_mulVec x R Z,hr, Matrix.one_mulVec]

theorem rank_product (M : Mat I J) :
    ∃ (A : Mat I (Fin M.rank)) (B : Mat (Fin M.rank) J),
      Function.Injective A.mulVec ∧ Function.Surjective B.mulVec ∧ A*B=M := by
  let t := M.rank
  let A := pack (colSp M)
  have ha := pack_inj (colSp M)
  obtain ⟨L,hL⟩ := mat_left_inv ha
  have hh := invariant_cols M A L (colSp_pack _) hL
  refine ⟨A,L*M,ha, mrk_surj.mpr ?_, hh⟩
  refine le_antisymm (Matrix.rank_le_card_height _) ?_
  have hx := Matrix.rank_mul_le_right A (L*M)
  rw [hh] at hx
  rw [Fintype.card_fin]; exact hx

/-- Symmetric nonsingular factor on the rank space. -/
theorem rank_symmetric (M : Mat I I) (hm : Mᵀ=M) :
    ∃ (P : Mat I (Fin M.rank)) (G : Mat (Fin M.rank) (Fin M.rank)),
      Function.Injective P.mulVec ∧ Gᵀ=G ∧ Function.Injective G.mulVec ∧ P*G*Pᵀ=M := by
  let A := pack (colSp M)
  have ha := pack_inj (colSp M)
  obtain ⟨L,hL⟩ := mat_left_inv ha
  let H := L*M*Lᵀ
  have hs := invariant_cols M A L (colSp_pack _) hL
  have hx : A*H*Aᵀ=M := by
    rw [show A*H=A*(L*M)*Lᵀ from (Matrix.mul_assoc ..).symm, hs]
    simpa only [transpose_mul,hm] using congrArg Matrix.transpose hs
  refine ⟨A,H,ha,?_,mrk_inj.mpr ?_,hx⟩
  · change (L*M*Lᵀ)ᵀ = L*M*Lᵀ
    rw [transpose_mul,transpose_mul,transpose_transpose,hm, Matrix.mul_assoc]
  · refine le_antisymm (Matrix.rank_le_card_width _) ?_
    rw [Fintype.card_fin]
    have h := (Matrix.rank_mul_le_left (A*H) Aᵀ).trans (Matrix.rank_mul_le_right _ _)
    rwa [hx] at h

omit [Fintype Q] in
theorem matrix_cancel_left {A : Mat I J} (hA : Function.Injective A.mulVec)
    (C D : Mat J Q) (h : A*C=A*D) : C=D := by
  classical
  obtain ⟨R,hR⟩ := mat_left_inv hA
  have hh := congrArg ((R * ·) : Mat I Q → _) h
  simpa only [← Matrix.mul_assoc,hR,Matrix.one_mul] using hh

theorem eigenbasis_idem {A : Type} [AddCommGroup A] [Module F A] [Fintype A]
    [FiniteDimensional F A] (E : J → A →ₗ[F] A) (h : ∀ i j x, E i (E j x)=E j (E i x))
    (hg : ∀ i x, E i (E i x)=E i x) :
    ∃ B : Basis (Fin (dim A)) F A, ∀ i t, ∃ c : F, E t (B i)=c • B i := by
  classical
  let s (I : Finset J) := {x : A | ∀ i ∈ I, ∃ c : F, E i x=c • x}
  have he (I : Finset J) : Submodule.span F (s I) = ⊤ := by
    induction I using Finset.induction with
    | empty => simp [s]
    | insert t I _ ih =>
      rw [← ih]
      refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.mpr ?_)
      · exact fun x hx i hi => hx i (Finset.mem_insert_of_mem hi)
      intro x hx
      have hi (i) (hi : i ∈ I) :
          ∃ c : F, E i x = c • x ∧ E i (E t x) = c • E t x := by
        obtain ⟨c,hc⟩ := hx i hi
        exact ⟨c,hc,by rw [h,hc,map_smul]⟩
      have ht : E t x ∈ s (insert t I) := by
        intro j hj; rcases Finset.mem_insert.mp hj with rfl|hj
        · exact ⟨1, by rw [hg,one_smul]⟩
        obtain ⟨c,_,he⟩ := hi j hj
        exact ⟨c,he⟩
      have hu : x-E t x ∈ s (insert t I) := by
        intro j hj; rcases Finset.mem_insert.mp hj with rfl|hj
        · exact ⟨0,by rw [map_sub,hg,sub_self,zero_smul]⟩
        obtain ⟨c,hc,hc'⟩ := hi j hj
        exact ⟨c,by rw [map_sub,hc,hc',smul_sub]⟩
      have hw := Submodule.add_mem (Submodule.span F (s (insert t I))) (Submodule.subset_span hu)
        (Submodule.subset_span ht)
      rwa [sub_add_cancel] at hw
  let B := Basis.ofSpan (he Finset.univ).ge
  let e := Fintype.equivFinOfCardEq (finrank_eq_card_basis B).symm
  refine ⟨B.reindex e,fun i t => ?_⟩
  have hb : Set.range B ⊆ s Finset.univ := Basis.extendLe_subset ..
  rw [Basis.reindex_apply]
  exact hb (show B (e.symm i) ∈ Set.range B from ⟨_,rfl⟩) t (Finset.mem_univ _)

theorem diagonalize [DecidableEq I] (M : J → Mat I I)
    (hm : ∀ i j, M i * M j=M j*M i) (hg : ∀ i,M i*M i=M i) :
    ∃ (C D : Mat I I) (f : J → I → F), D*C=1 ∧ C*D=1 ∧ ∀ i, M i*C=C*diagonal (f i) := by
  classical
  let E i := (M i).mulVecLin
  have hh i j x : E i (E j x)=E j (E i x) := by
    simp only [E, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
    rw [hm]
  have hb i x : E i (E i x)=E i x := by
    simp only [E, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,hg]
  obtain ⟨B,hB⟩ := eigenbasis_idem E hh hb
  let A : Basis I F (Vec I) :=
    B.reindex (Fintype.equivOfCardEq (by rw [Fintype.card_fin,dim_vec]))
  have h (i j) : ∃ c : F, E i (A j) = c • A j := by
    unfold A; rw [Basis.reindex_apply]; exact hB _ _
  choose f hf using h
  let C : Mat I I := Matrix.of (fun i j => A j i)
  have hi : Function.Injective C.mulVec := Matrix.mulVec_injective_iff.mpr A.linearIndependent
  obtain ⟨D,hD⟩ := mat_left_inv hi
  have he : C*D=1 := mul_eq_one_comm.mp hD
  refine ⟨C,D,f,hD,he,fun i => ?_⟩
  ext j k
  rw [Matrix.mul_diagonal]
  have hk := congr_fun (hf i k) j
  change ∑ l, M i j l * A k l = f i k*A k j at hk
  change ∑ l, M i j l * A k l = A k j * _
  rw [hk,mul_comm]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BooleanLabels
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
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

theorem mono_union (s : Label b) (S T : Finset (Fin b)) :
    monoBit s (S∪T)= monoBit s S*monoBit s T := by
  induction S using Finset.induction with
  | empty => simp [monoBit]
  | insert i S h ih =>
    rw [insert_union,mono_insert,mono_insert,ih,mul_assoc]

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

theorem point_eval (p : Shape) (s : Label p.b) (z : Base p.g n)
    (r : SelIdx p.b p.j) (i : AIdx p.g n) : point p s z (r,i) = monoBit s r.val * baseV z i :=
  rfl

theorem Wspace_hank {M : Moment p n} (h : M∈Wspace p n) : hankel M := by
  intro i k a b c d hab
  unfold Wspace at h
  induction h using Submodule.span_induction with
  | mem M hm =>
    obtain ⟨s,z,rfl⟩ := hm
    have h (a b : SelIdx p.b p.j) :
        mom p s z (a,i) (b,k) = monoBit s (a.val ∪ b.val) * (baseV z i*baseV z k) := by
      simp only [mom,vecMulVec_apply,point_eval,mono_union] <;> ring
    rw [h,h,hab]
  | zero => rfl
  | add x y _ _ hx hy => simp only [Matrix.add_apply,hx,hy]
  | smul v x _ hx => simp only [Matrix.smul_apply,hx]

theorem Wspace_diag {M : Moment p n} (h : M∈Wspace p n) : diagBase M := by
  intro i a b
  unfold Wspace at h
  induction h using Submodule.span_induction with
  | mem M hm =>
    obtain ⟨s,z,rfl⟩ := hm
    simp only [mom,vecMulVec_apply,point_eval,baseV]
    rw [mul_mul_mul_comm,bit_sq]
    have hn : Option.elim' (1:F) z none = 1 := rfl
    rw [hn]
    ring
  | zero => rfl
  | add x y _ _ hx hy => simp only [Matrix.add_apply,hx,hy]
  | smul v x _ hx => simp only [Matrix.smul_apply,hx]

theorem labMat_act (s) (z : Vec (AIdx p.g n)) :
    labMat p n s *ᵥ z = putLab p n s z := by
  funext i
  simp [Matrix.mulVec,dotProduct,labMat,putLab,monoBit,selV]

theorem mput_apply (s) (Z : BaseMat p n) (i j) : mput p s Z i j =
    monoBit s i.1.val*monoBit s j.1.val*Z i.2 j.2 := by
  classical
  simp [mput,liftM_def,Matrix.mul_apply,transpose_apply,labMat, mul_comm,mul_left_comm,mul_assoc]

theorem mput_hank (s) (Z : BaseMat p n) : hankel (mput p s Z) := by
  intro i j a b c d h
  rw [mput_apply,mput_apply]
  simp_rw [← mono_union,h]

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

omit [Fintype I] in
theorem rank_ge_mul (A : Mat I J) (B : Mat J K) :
    A.rank+B.rank ≤ (A*B).rank+Fintype.card J := by
  let f := A.mulVecLin
  let g := f ∘ₗ (colSp B).subtype
  have he : LinearMap.range g = colSp (A*B) := by
    change LinearMap.range g = LinearMap.range ((A*B).mulVecLin)
    rw [mulVecLin_mul]
    unfold g
    rw [LinearMap.range_comp,LinearMap.range_comp]
    simp [f,colSp]
  have hi : dim (LinearMap.ker g) ≤ dim (LinearMap.ker f) := by
    let q := ((colSp B).subtype ∘ₗ (LinearMap.ker g).subtype)
    have hq (x : LinearMap.ker g) : q x ∈ LinearMap.ker f := x.property
    let k := q.codRestrict (LinearMap.ker f) hq
    have hk : Injective k := by
      intro x y h
      have heq := congrArg (fun b : LinearMap.ker f => b.val) h
      exact Subtype.ext (Subtype.ext heq)
    exact LinearMap.finrank_le_finrank_of_injective hk
  have h1 := g.finrank_range_add_finrank_ker
  rw [he] at h1
  have h2 := f.finrank_range_add_finrank_ker
  change (A*B).rank + dim (LinearMap.ker g)=B.rank at h1
  change A.rank + dim (LinearMap.ker f)=dim (Vec J) at h2
  rw [dim_vec] at h2; omega

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CoordinateBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate Blocks -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n : ℕ}

theorem pullM_def {I J V U : Type} [Fintype V] [Fintype U] (P : Mat V I)
    (Q : Mat U J) (M : Mat V U) : pullM P Q M=Pᵀ*M*Q := rfl

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

theorem IsLaw.sub [Fintype α] {w : Wgt α} (hw : IsLaw w) : SubLaw w where
  nz := hw.nz
  total := hw.total.le

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

theorem SubLaw.avg_le (hw : SubLaw w) {b : ℝ} (hb : 0 ≤ b) (h : ∀ x, f x ≤ b) :
    avg w f ≤ b := by
  refine (avg_mono hw.nz h).trans ?_
  rw [avg_const]
  exact (mul_le_mul_of_nonneg_right hw.total hb).trans_eq (one_mul b)

theorem IsLaw.le_avg (hw : IsLaw w) {b : ℝ} (h : ∀ x, b ≤ f x) : b ≤ avg w f :=
  (hw.avg_const _).ge.trans (avg_mono hw.nz h)

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

theorem mapW_avg (w : Wgt α) (f : α → β) (g : Wgt β) :
    avg (mapW w f) g = avg w (fun x => g (f x)) := by
  classical
  change avg (mixW w (fun x y => ind (f x = y))) g = _
  rw [mixW_avg]
  simp [avg, ind]

theorem mapW_law (hw : IsLaw w) (f : α → β) : IsLaw (mapW w f) := by
  refine ⟨fun _ => pr_nonneg hw.nz, ?_⟩
  simpa only [avg_const, mul_one, hw.total] using mapW_avg w f (fun _ => 1)

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

theorem nbr_eq_card (p : A → Prop) [Fintype {x // p x}] :
    nbr p = (Fintype.card {x // p x}:ℝ) := by
  classical
  rw [Fintype.card_subtype]
  simp [nbr,tot,ind]

theorem unifOn_val (p : A → Prop) (x) :
    unifOn p x = ind (p x) / nbr p := rfl

theorem unifOn_sub (p : A → Prop) : SubLaw (unifOn p) :=
  normW_subLaw fun x => ind_nonneg (p x)

theorem unifOn_carried (p : A → Prop) : carried (unifOn p) p :=
  fun x h => by rw [unifOn_val,ind_zero h,zero_div]

theorem pr_on (w : Wgt A) (p q : A → Prop) :
    pr (onW w p) q = pr w (fun x => p x ∧ q x) / pr w p := by
  unfold onW
  change avg _ _ = _
  rw [avg_norm,subW_tot]
  exact congrArg (fun b => b / pr w p) (pr_sub w p q)

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

theorem subLaw_pair {w : Wgt A} {v : Wgt B} (hw : SubLaw w) (hv : SubLaw v) :
    SubLaw (pairW w v) := by
  refine ⟨fun x => mul_nonneg (hw.nz _) (hv.nz _),?_⟩
  rw [pairW_tot]
  exact (mul_le_mul hw.total hv.total (tot_nonneg hv.nz) (by norm_num)).trans_eq (one_mul _)

theorem pr_cap {w v : Wgt A} {c : ℝ} (h : ∀ x, w x ≤ c*v x) (p : A → Prop) :
    pr w p ≤ c*pr v p := calc
  _ ≤ pr (fun x => c*v x) p := pr_mono_left (w:=w) (v:=fun x => c*v x) h _
  _ = _ := by simp only [pr,avg,Finset.mul_sum,mul_assoc]

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

namespace ExpSmall

theorem mul (hf : ExpSmall l n f) (hg : ExpO l n g) :
    ExpSmall l n (fun i => f i*g i) := by
  obtain ⟨c,hc,h⟩ := hf
  refine ⟨c/2,by linarith,?_⟩
  filter_upwards [h,hg (c/2) (by linarith)] with i hi hj
  rw [abs_mul, show -(c/2)*n i = -c*n i + c/2*n i by ring, bp_add]
  exact mul_le_mul hi hj (abs_nonneg _) (bp_pos _).le

theorem add (hn : Tendsto n l atTop) (hf : ExpSmall l n f) (hg : ExpSmall l n g) :
    ExpSmall l n (fun i => f i+g i) := by
  obtain ⟨c,hc,h⟩ := hf; obtain ⟨d,hd,h'⟩ := hg
  let a := min c d
  have ha : 0 < a := lt_min hc hd
  refine ⟨a/2,by linarith, ?_⟩
  filter_upwards [h,h',hn.eventually (eventually_ge_atTop 0),
    ((bp_tendsto (show 0 < a/2 by linarith)).comp hn).eventually
      (eventually_ge_atTop 2)] with i hi hj hx hb
  change 2 ≤ bp (a/2*n i) at hb
  have h₁ : -c*n i ≤ -a*n i := by gcongr; exact min_le_left _ _
  have h₂ : -d*n i ≤ -a*n i := by gcongr; exact min_le_right _ _
  refine le_trans (abs_add_le _ _) ?_
  rw [show -(a/2)*n i = a/2*n i + -a*n i by ring,bp_add]
  calc |f i| + |g i| ≤ bp (-a*n i)+bp (-a*n i) :=
         add_le_add (hi.trans (bp_le h₁)) (hj.trans (bp_le h₂))
       _ = 2*bp (-a*n i) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_right hb (bp_pos _).le

end ExpSmall

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

variable {V W}

theorem add_polar (t : V) : ∀ x : V, x+t+t=x := by
  intro x; rw [add_assoc,char_two,add_zero]

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
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

theorem Pin.agree_pack {a : Pin p n N} {x : UnitType p n N} :
    a.agree x ↔ ∀ i : Place p, images x i * pack (a.sp i) = a.target i * pack (a.sp i) := by
  have heq {I J L : Type} [Fintype I] [Fintype J] [Fintype L] (P Q : Mat I J) (M : Mat J L) :
      (∀ v ∈ colSp M, P *ᵥ v = Q *ᵥ v) ↔ P*M=Q*M := by
    constructor
    · intro h
      apply coe_mv_inj
      exact LinearMap.ext fun v => by
        change (P*M) *ᵥ v=(Q*M) *ᵥ v
        rw [← mulVec_mulVec,← mulVec_mulVec]
        exact h _ ⟨v,rfl⟩
    · rintro h x ⟨v,rfl⟩
      change P *ᵥ (M *ᵥ v) = Q *ᵥ (M *ᵥ v)
      rw [mulVec_mulVec,mulVec_mulVec,h]
  unfold Pin.agree
  apply forall_congr'; intro i
  have hh := heq (images x i) (a.target i) (pack (a.sp i))
  rw [colSp_pack] at hh
  exact hh

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SparseCutProfiles
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.momFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sparse Cut Profiles -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators

variable {p : Shape} {n : ℕ}

theorem mem_nonzeroTags (i) (w : Tag p.g → Moment p n) :
    i ∈ nonzeroTags w ↔ w i ≠ 0 := by classical simp [nonzeroTags]

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

omit [Fintype U] in
theorem rank_lift_le (P : Mat U I) (Q : Mat L J) (A : Mat I J) :
    (liftM P Q A).rank ≤ A.rank :=
  (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

end Rank

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FlatLevelShifts
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Flat Level Shifts -/

noncomputable section
namespace HadwigerCounterexample
open Matrix

variable {I J Q : Type} [Fintype I] [Fintype J] [Fintype Q]

/-- Shift a P row to an X t row. If the Gram comparisons obey Boolean
monomial identities, there are coordinate factors of H for which both the
left and the right row arrays diagonalize all these shifts. -/
theorem shift_factors [DecidableEq J] (P : Mat I J) (H : Mat J J)
    (hP : Function.Injective P.mulVec) (hH : Function.Injective H.mulVec)
    (X : Q → Mat I J)
    (h1 : ∀ a, X a * H * Pᵀ = P * H * (X a)ᵀ)
    (h2 : ∀ a b, X a * H * (X b)ᵀ = X b * H * (X a)ᵀ)
    (h3 : ∀ a, X a * H * (X a)ᵀ = X a * H * Pᵀ) :
    ∃ (K C : Mat J J) (f : Q → J → F), H = K * Cᵀ ∧
      ∀ a, X a * C = P * C * diagonal (f a) ∧ X a * K = P * K * diagonal (f a) := by
  classical
  obtain ⟨R,hR⟩ := mat_left_inv hP
  obtain ⟨L,hL⟩ := mat_left_inv hH
  have hh : H*L=1 := mul_eq_one_comm.mp hL
  have hr : Pᵀ*Rᵀ=1 := by rw [← Matrix.transpose_mul,hR,Matrix.transpose_one]
  have hp_cancel {A B : Mat J J} (h : P*A*Pᵀ=P*B*Pᵀ) : A=B := by
    have hx := matrix_cancel_left hP (A*Pᵀ) (B*Pᵀ)
      (by simpa only [Matrix.mul_assoc] using h)
    have hx := congrArg (fun A => A*Rᵀ) hx
    simpa only [Matrix.mul_assoc,hr,Matrix.mul_one] using hx
  have hr_cancel {W : Type} [Fintype W] (A B : Mat W J)
      (h : A*H=B*H) : A=B := by
    have he := congrArg (fun t : Mat W J => t*L) h
    simpa only [Matrix.mul_assoc,hh,Matrix.mul_one] using he
  let M := fun a => R*X a
  have he (a : Q) : X a = P*M a := by
    apply hr_cancel
    calc X a * H = X a * H * (Pᵀ*Rᵀ) := by rw [hr,Matrix.mul_one]
         _ = P * (H * ((X a)ᵀ * Rᵀ)) := by
           rw [← Matrix.mul_assoc, h1]
           simp only [Matrix.mul_assoc]
         _ = P * (R * (P * H * (X a)ᵀ) * Rᵀ) := by
           simp only [← Matrix.mul_assoc,hR,Matrix.mul_one]
         _ = P * M a * H := by
           rw [← h1]
           simp only [M,Matrix.mul_assoc,hr,Matrix.mul_one]
  have es a : M a*H=H*(M a)ᵀ := by
    apply hp_cancel
    have hh := h1 a
    rw [he] at hh
    simpa only [transpose_mul,Matrix.mul_assoc] using hh
  have ei (a b) :
      P*(M a*(M b*H))*Pᵀ=X a*H*(X b)ᵀ := by
    simp only [he,es b,transpose_mul,Matrix.mul_assoc]
  have hc (a b) : M a * M b=M b*M a := by
    apply hr_cancel
    apply hp_cancel
    rw [Matrix.mul_assoc (M a), ei, h2, Matrix.mul_assoc (M b),ei]
  have hi a : M a * M a=M a := by
    apply hr_cancel
    apply hp_cancel
    rw [Matrix.mul_assoc (M a), ei, h3, he]
    simp only [Matrix.mul_assoc]
  obtain ⟨C,D,hD,hc1,hc2,hc3⟩ := diagonalize M hc hi
  let K := H * Dᵀ
  refine ⟨K,C,hD,?_,fun a => ?_⟩
  · unfold K
    rw [Matrix.mul_assoc,←transpose_mul,hc2,transpose_one,Matrix.mul_one]
  have hv : D*M a=diagonal (hD a)*D := by
    calc D*M a = D*(M a*C)*D := by simp only [Matrix.mul_assoc,hc2,Matrix.mul_one]
         _ = diagonal (hD a)*D := by rw [hc3,←Matrix.mul_assoc,hc1,Matrix.one_mul]
  have hk : M a*K=K*diagonal (hD a) := by
    unfold K
    rw [←Matrix.mul_assoc,es a, Matrix.mul_assoc, ← transpose_mul,hv,transpose_mul,
      diagonal_transpose,Matrix.mul_assoc]
  rw [he]
  constructor
  · simp only [Matrix.mul_assoc,hc3]
  · simp only [Matrix.mul_assoc,hk]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FlatRankLevels
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Flat Rank Levels -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n k : ℕ}

theorem rank_atLayer_le (M : Moment p n) {k : ℕ} (h : k≤p.j) :
    (atLayer M h).rank ≤ M.rank := M.rank_submatrix_le _ _

private theorem atLayer_mono (M : Moment p n) {k l} (h : k≤l) (hh : l≤p.j) :
    (atLayer M (h.trans hh)).rank ≤ (atLayer M hh).rank := by
  let f := (rise p (n:=n) h)
  have he := (atLayer M hh).rank_submatrix_le f f
  exact he

theorem flat_atLayer (M : Moment p n) {R : ℕ} (hR : M.rank ≤ R)
    (hj : 6*R+4 ≤ p.j) :
    ∃ (k : ℕ) (h : k+1≤p.j), 4*R+2≤k ∧
      (atLayer M ((Nat.le_succ k).trans h)).rank = (atLayer M h).rank := by
  classical
  by_contra hn
  let a := 4*R+2
  have hi (i : ℕ) (h : a+i ≤ p.j) :
      i ≤ (atLayer M h).rank := by
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have he : a+i ≤ p.j := (Nat.le_succ _).trans h
      have hh : (atLayer M he).rank < (atLayer M h).rank := by
        refine lt_of_le_of_ne (atLayer_mono M (Nat.le_succ _) h) (fun hx => hn ?_)
        exact ⟨a+i,h,by unfold a; omega,hx⟩
      exact (Nat.succ_le_succ (ih he)).trans hh
  have he : a+(R+1)≤p.j := by unfold a; omega
  have hx := ((hi (R+1) he).trans (rank_atLayer_le M he)).trans hR
  omega

theorem flat_entries {M : Moment p n} (hs : Mᵀ=M) (hh : hankel M)
    (hk : k+1≤p.j) (hr :
      (atLayer M ((Nat.le_succ _).trans hk)).rank = (atLayer M hk).rank) :
    let t := (atLayer M hk).rank
    ∃ (s : Fin t → Label p.b) (u v : Fin t → Vec (AIdx p.g n)),
      ∀ i j : Layer p n k,
        atLayer M ((Nat.le_succ _).trans hk) i j = ∑ x : Fin t,
          monoBit (s x) i.1.val * monoBit (s x) j.1.val * (u x i.2 * v x j.2) := by
  classical
  intro t
  let h := (Nat.le_succ k).trans hk
  let A := atLayer M hk
  let r := rise p (n:=n) (Nat.le_succ k)
  obtain ⟨Q,H,hQ,_,hH,hA⟩ := rank_symmetric A (show Aᵀ=A by
    ext i j
    exact congr_fun (congr_fun hs _) _)
  let P := Q.submatrix r id
  let X := fun i => Q.submatrix (bump p (k:=k) i) id
  have eqn (a b : Layer p n k → Layer p n (k+1)) :
      Q.submatrix a id * H * (Q.submatrix b id)ᵀ = A.submatrix a b := by

    have he :
        Q.submatrix a id * H * (Q.submatrix b id)ᵀ =
          (Q*H*Qᵀ).submatrix a b := by ext; rfl
    exact he.trans (congrArg (fun m => m.submatrix a b) hA)
  have hL : P*H*Pᵀ=atLayer M h := eqn _ _
  have hP : Function.Injective P.mulVec := by
    rw [mrk_inj,Fintype.card_fin]
    apply le_antisymm (by simpa using P.rank_le_card_width) ?_
    have hh := (Matrix.rank_mul_le_left (P*H) Pᵀ).trans (Matrix.rank_mul_le_left P H)
    rw [hL] at hh
    rwa [hr] at hh
  have hentry (x y a b : Layer p n (k+1))
      (h1 : x.2 = a.2) (h2 : y.2=b.2)
      (h3 : x.1.val∪y.1.val=a.1.val∪b.1.val) : A x y=A a b := by
    change M (⟨_,_⟩,x.2) (⟨_,_⟩,y.2) = M (⟨_,_⟩,a.2) (⟨_,_⟩,b.2)
    rw [h1,h2]; exact hh _ _ _ _ _ _ h3
  obtain ⟨K,C,f,hf,hd⟩ := shift_factors P H hP hH X
    (fun a => by
      unfold X P; rw [eqn,eqn]; ext i j
      apply hentry <;> simp [bump,r,rise])
    (fun a b => by
      unfold X; rw [eqn,eqn]; ext i j
      apply hentry <;> try rfl
      simp only [bump]
      ext; simp; tauto)
    (fun a => by
      unfold X P; rw [eqn,eqn]; ext i j
      apply hentry <;> try rfl
      simp only [bump,r,rise]
      ext; simp)
  let s (x : Fin t) : Label p.b := fun a => f a x
  have hi (F : Mat (Fin t) (Fin t)) (hF : ∀ a, X a * F=P*F*diagonal (f a))
      (x : Fin t) (i : Layer p n k) :
      (P*F) i x = monoBit (s x) i.1.val * (P*F) (emptySel,i.2) x := by
    rcases i with ⟨⟨l,hl⟩,i⟩
    induction l using Finset.induction with
    | empty =>
      simp only [monoBit,Finset.prod_empty,one_mul]
      rfl
    | insert a l ha ih =>
      have hg := Finset.card_insert_of_notMem ha
      have he : l.card≤k := by omega
      let u : Layer p n k := (⟨l,he⟩,i)
      have hh := congr_fun (congr_fun (hF a) u) x
      rw [Matrix.mul_diagonal] at hh
      change (P*F) (⟨insert a l,hl⟩,i) x = _
      change (P*F) (⟨insert a l,hl⟩,i) x = (P*F) u x * _ at hh
      rw [hh]
      change (P*F) (⟨l,he⟩,i) x * s x a = monoBit (s x) (insert a l) * _
      rw [ih he,mono_insert]
      ring
  let u := P*K
  let v := P*C
  refine ⟨s,fun x i => u (emptySel,i) x, fun x i => v (emptySel,i) x,fun i j => ?_⟩
  have he : u*vᵀ=atLayer M h := by rw [← hL,hf]; simp only [u,v,Matrix.transpose_mul,
    Matrix.mul_assoc]
  rw [← he]
  simp only [Matrix.mul_apply,Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hu := hi K (fun a => (hd a).2) x i
  have hv := hi C (fun a => (hd a).1) x j
  dsimp only [u,v] at *
  rw [hu,hv]
  ring

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MomentLabelSupport
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Moment Label Support -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset
open scoped BigOperators
variable {p : Shape} {n k : ℕ}

/-- Zero extension by the Boolean union rule for low rank matrices. -/
theorem zero_extension {M : Moment p n} (hh : hankel M) (hr : M.rank≤k)
    (hk : k≤p.j) (hg : atLayer M hk=0) : M=0 := by
  classical
  by_contra he
  let D (r : ℕ) := ∃ i j : Row p n,M i j≠0 ∧ (i.1.val∪j.1.val).card=r
  have hD : ∃ r,D r := by
    by_contra! h
    refine he (Matrix.ext fun i j => ?_)
    exact Classical.byContradiction fun g => h _ ⟨i,j,g,rfl⟩
  obtain ⟨x,y,hxy,hw⟩ := Nat.find_spec hD
  let U := x.1.val∪y.1.val
  let d := U.card
  have hd : k<d := by
    by_contra hd
    have hx : x.1.val.card≤k := (Finset.card_le_card subset_union_left).trans (Nat.le_of_not_gt hd)
    have hy : y.1.val.card≤k := (Finset.card_le_card subset_union_right).trans (Nat.le_of_not_gt hd)
    exact hxy (congr_fun (congr_fun hg (⟨x.1.val,hx⟩,x.2)) (⟨y.1.val,hy⟩,y.2))
  have hd' : d≤2*p.j := by
    have hi := x.1.property; have hj := y.1.property
    exact (card_union_le _ _).trans (by omega)
  let t := d/2
  let T := U.powersetCard t
  have hi (i : T) := mem_powersetCard.mp i.property
  have hs (i : T) : (U\i.val).card ≤ p.j := by
    rw [Finset.card_sdiff_of_subset (hi i).1,(hi i).2]
    change d - (d/2) ≤ _
    omega
  let f : T → Row p n := fun i => (⟨i.val, (hi i).2 ▸ (show t≤p.j by
    unfold t; omega)⟩, x.2)
  let g : T → Row p n := fun i => (⟨U\i.val, hs i⟩,y.2)
  have hf : M.submatrix f g=1 := by
    ext i j
    by_cases e : i = j
    · subst j
      rw [Matrix.one_apply_eq]
      change M _ _=_
      have hU : M (f i) (g i)=M x y :=
        hh x.2 y.2 _ _ x.1 y.1 (Finset.union_sdiff_of_subset (hi i).1)
      rw [hU]; exact (bit_cases _).resolve_left hxy
    rw [Matrix.one_apply_ne e]
    change M (f i) (g j)=0
    by_contra H
    have hl := Nat.find_min' hD (show D _ from ⟨f i,g j,H,rfl⟩)
    rw [← hw] at hl
    change d ≤ (i.val ∪ (U \ j.val)).card at hl
    have heq : i.val∪(U \ j.val) = U :=
      Finset.eq_of_subset_of_card_le (union_subset (hi i).1 sdiff_subset) hl
    have hsub : j.val⊆i.val := by
      intro a ha
      have hj := (hi j).1 ha
      rw [← heq] at hj
      exact (mem_union.mp hj).resolve_right (fun h => (mem_sdiff.mp h).2 ha)
    exact e (Subtype.ext (Finset.eq_of_subset_of_card_le hsub
      (by rw [(hi i).2,(hi j).2])).symm)
  have hK := M.rank_submatrix_le f g
  rw [hf, Matrix.rank_one,Fintype.card_coe] at hK
  dsimp only [T] at hK; rw [card_powersetCard] at hK
  have hv := Nat.choose_le_middle 1 d
  rw [Nat.choose_one_right] at hv
  exact Nat.not_lt_of_le ((hv.trans hK).trans hr) hd

theorem mrk_sum_le {I J A : Type} [Fintype I] [Fintype J] (s : Finset A) (f : A → Mat I J) :
    (∑ i∈s,f i).rank ≤ ∑ i∈s,(f i).rank := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s h ih =>
    rw [Finset.sum_insert h,Finset.sum_insert h]
    exact le_trans (mrk_add_le _ _) (by gcongr)

theorem mput_rank_le (s : Label p.b) (A : BaseMat p n) :
    (mput p s A).rank ≤ A.rank :=
  (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

set_option maxHeartbeats 800000 in
theorem label_support {M : Moment p n} (hm : M∈Wspace p n)
    (R : ℕ) (hj : 6*R+4≤p.j) (hr : M.rank ≤ R) :
    ∃ (L : Finset (Label p.b)) (Z : Label p.b → BaseMat p n),
      L.card ≤ R ∧ (∑ s∈L,(Z s).rank) ≤ R ∧ M=labelSum p L Z ∧
      ∀ s∈L,(Z s)ᵀ=Z s ∧ ∀ i,Z s i i=Z s none i := by
  classical
  obtain ⟨k,hk,hk',hh⟩ := flat_atLayer M hr hj
  let t := (atLayer M hk).rank
  let h := (Nat.le_succ k).trans hk
  obtain ⟨s,u,v,hv⟩ := flat_entries (Wspace_sym hm) (Wspace_hank hm) hk hh
  let L := Finset.univ.image s
  let S (z : Label p.b) : Finset (Fin t) := Finset.univ.filter (fun i => s i=z)
  let Z := fun z : Label p.b => ∑ i ∈ S z,vecMulVec (u i) (v i)
  have hS (i : Fin t) : s i∈L := mem_image_of_mem _ (mem_univ _)
  have ht : t≤R := (rank_atLayer_le _ _).trans hr
  have hL : L.card≤R := card_image_le.trans (by simpa [t] using ht)
  have hZ : (∑ i∈L,(Z i).rank) ≤ R := by
    have he (i : Label p.b) : (Z i).rank ≤ (S i).card := by
      refine (mrk_sum_le (S i) _).trans ((sum_le_sum (g:=fun _ => (1:ℕ))
        (fun j _ => Matrix.rank_vecMulVec_le (u j) (v j))).trans_eq ?_)
      simp
    refine le_trans (sum_le_sum (fun i _ => he i)) ?_
    have hx : (∑ i∈L,(S i).card) = (Finset.univ : Finset (Fin t)).card :=
      (Finset.card_eq_sum_card_fiberwise (fun i _ => hS i)).symm
    rw [hx,Finset.card_univ,Fintype.card_fin]; exact ht
  refine ⟨L,Z,hL,hZ,?_⟩
  let T := labelSum p L Z
  have hrT : T.rank ≤ R := (mrk_sum_le L _).trans
    ((sum_le_sum (fun i _ => mput_rank_le i (Z i))).trans hZ)
  have he : atLayer M h=atLayer T h := by
    ext i j
    rw [hv]
    let F (x : Fin t) := monoBit (s x) i.1.val * monoBit (s x) j.1.val * (u x i.2 * v x j.2)
    change ∑ x : Fin t, F x = (∑ z∈L,mput p z (Z z)) (rise p h i) (rise p h j)
    rw [Matrix.sum_apply, ← Finset.sum_fiberwise_of_maps_to (fun i _ => hS i) F]
    refine sum_congr rfl fun x _ => ?_
    simp only [mput_apply,Z,Matrix.sum_apply,vecMulVec_apply, mul_sum,rise]
    refine sum_congr rfl fun y hy => ?_
    unfold F
    rw [(mem_filter.mp hy).2]
  have heq : M=T := by
    have hzero : M+T=0 := by
      apply zero_extension (k:=k) _ _ h
      · unfold atLayer
        ext i j
        have h1 := congr_fun (congr_fun he i) j
        change M _ _ + T _ _ = _
        change M _ _=T _ _ at h1
        rw [h1,char_two]; rfl
      · intro i j a b c d hg
        have h1 := Wspace_hank hm i j a b c d hg
        have h2 : T (a,i) (b,j)=T (c,i) (d,j) := by
          simp only [T,labelSum,Matrix.sum_apply]
          exact sum_congr rfl fun x _ => mput_hank x _ i j a b c d hg
        simp only [Matrix.add_apply,h1,h2]
      · refine (mrk_add_le _ _).trans ?_; omega
    exact add_right_cancel (hzero.trans (char_two T).symm)
  refine ⟨heq,?_⟩
  have heA i j (b : SelIdx p.b p.j) :
      M (b,i) (emptySel,j) = ∑ s∈L,Z s i j*monoBit s b.val ∧
      M (emptySel,i) (b,j) = ∑ s∈L,Z s i j*monoBit s b.val := by
    rw [heq]
    simp only [T,labelSum,Matrix.sum_apply,mput_apply]
    simp only [monoBit,emptySel,Finset.prod_empty,mul_one,mul_comm]
    simp
  have hint (i j k l : AIdx p.g n)
      (h : ∀ b : SelIdx p.b p.j,
        ∑ s∈L,Z s i j*monoBit s b.val=∑ s∈L,Z s k l*monoBit s b.val) :
      ∀ s∈L,Z s i j = Z s k l := by
    intro s hs
    have he := selector_indep L (fun s => Z s i j-Z s k l) p.j (by omega) (by
      intro U hU
      simp only [sub_mul,Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (h ⟨U,hU⟩)) s hs
    exact sub_eq_zero.mp he
  intro s hs
  constructor
  · ext i j
    apply hint j i i j _ s hs
    intro b
    rw [← (heA j i b).1,← (heA i j b).2]
    exact congr_fun (congr_fun (Wspace_sym hm) _) _
  intro i
  apply hint i i none i _ s hs
  intro b
  rw [← (heA i i b).1,← (heA none i b).1]
  exact Wspace_diag hm _ _ _

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_WalshBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

theorem wsign_add (x y : F) : wsign (x+y) = wsign x * wsign y := by
  rcases bit_cases x with h|h <;> rcases bit_cases y with g|g <;>
    simp [h,g,char_two]

@[simp] theorem wsign_abs (x) : |wsign x|=1 := by rcases bit_cases x with h|h <;> simp [h]

variable {A B V W : Type} [Fintype A] [Fintype B]

theorem avg_prod (w f g : Wgt A) :
    avg w f * avg w g = avg (pairW w w) (fun x => f x.1*g x.2) := (pairW_separate ..).symm

variable [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W] [Fintype V] [Fintype W]

/-- Walsh orthogonality via a translation of the uniform measure. -/
theorem wsign_lin (b : V →ₗ[F] F) : avg unif (fun x => wsign (b x)) = ind (b=0) := by
  classical
  by_cases h : b = 0
  · simp only [h,LinearMap.zero_apply,wsign_zero]
    simpa using unif_law.avg_const _
  obtain ⟨x,hx⟩ : ∃ x, b x=1 := by
    by_contra! hg
    exact h (LinearMap.ext fun x => (bit_cases _).resolve_right (hg x))
  let E : V ≃ V := ⟨(·+x),(·+x),add_polar x,add_polar x⟩
  have he := avg_bij E unif (fun x => wsign (b x))
  change avg unif (fun z => wsign (b (z+x))) = _ at he
  simp_rw [map_add,wsign_add,hx,wsign_one] at he
  rw [avg_mul] at he
  rw [ind_zero h]
  linarith only [he]

omit [Fintype V] in
theorem avg_ws (b : V →ₗ[F] W →ₗ[F] F) (x z : V) :
    avg unif (fun w => wsign (b x w)*wsign (b z w)) = ind (b x=b z) := by
  simp_rw [← wsign_add]
  change avg unif (fun w => wsign ((b x+b z) w)) = _
  rw [wsign_lin]
  apply congrArg ind
  exact propext (by rw [← ZModModule.sub_eq_add,sub_eq_zero])

/-- Unnormalized inner mean square identity. -/
theorem avg_wsq (b : V →ₗ[F] W →ₗ[F] F) (v f : Wgt V) :
    avg unif (fun w => (avg v (fun x => f x*wsign (b x w)))^2) =
      avg (pairW v v) (fun x => f x.1 * f x.2 * ind (b x.1=b x.2)) := by
  simp_rw [pow_two,avg_prod]
  rw [avg_avg]
  refine avg_congr fun ⟨x,z⟩ _ => ?_
  simp_rw [mul_mul_mul_comm (f x) _ (f z)]
  rw [avg_mul',avg_ws]

/-- Min-entropy form, squared. -/
theorem walsh_mass (b : V →ₗ[F] W →ₗ[F] F) (hb : Function.Injective b) (u : Wgt V) (v : Wgt W)
    (f : Wgt V) (g : Wgt W)
    (hf : ∀ x, |f x|≤1) (hg : ∀ x, |g x|≤1) (hu : SubLaw u) (hv : SubLaw v)
    {p q : ℝ} (hp : ∀ x, u x ≤ p) (hq : ∀ x, v x ≤ q) :
    (avg v (fun w => g w * avg u (fun x => f x*wsign (b x w))))^2 ≤
      (Fintype.card W : ℝ)*p*q := by
  classical
  let F w := avg u (fun x => f x*wsign (b x w))
  have hi {A : Type} [Fintype A] {p : ℝ} (h : 0 ≤ p) (v f : Wgt A) (hw : SubLaw v)
      (hh : ∀ x, v x ≤ p) (hg : ∀ x, |f x|≤1) : ∑ x, (v x*f x)^2 ≤ p := by
    have hr x : (v x*f x)^2 ≤ v x*p := calc
      _ = v x^2*f x^2 := mul_pow _ _ _
      _ ≤ v x^2*1 := by
        have he := abs_le.mp (hg x)
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        nlinarith [he.1,he.2]
      _ ≤ _ := by rw [mul_one,pow_two]; exact mul_le_mul_of_nonneg_left (hh x) (hw.nz x)
    exact (Finset.sum_le_sum (fun x _ => hr x)).trans (hw.avg_le h (f:=fun _ => p) (fun _ => le_rfl))
  have hh1 := hi ((hv.nz 0).trans (hq 0)) v g hv hq hg
  have hh2 := hi ((hu.nz 0).trans (hp 0)) u f hu hp hf
  have heq : avg (pairW u u) (fun x : V×V => f x.1*f x.2*ind (b x.1=b x.2)) =
      ∑ x, (u x*f x)^2 := by
    rw [pairW_avg]; unfold avg
    refine Finset.sum_congr rfl fun x _ => ?_
    have h z : (b x=b z) ↔ x=z := hb.eq_iff
    simp [h,ind]
    ring
  have hW : 0 < (Fintype.card W : ℝ) := by exact_mod_cast Fintype.card_pos
  have hh3 : ∑ w, F w^2 ≤ (Fintype.card W : ℝ)*p := by
    rw [mul_comm]
    apply (div_le_iff₀ hW).mp
    calc _ = avg unif (fun w => F w^2) := by simp only [avg,unif_apply,← Finset.mul_sum];
                                              rw [div_eq_mul_inv,mul_comm]
         _ ≤ _ := (avg_wsq b u f).le.trans (heq.le.trans hh2)
  calc
    _ = (∑ w, (v w*g w)*F w)^2 := by simp only [mul_assoc]; rfl
    _ ≤ (∑ w, (v w*g w)^2) * ∑ w, (F w)^2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ _ := by rw [mul_comm _ q]; exact mul_le_mul hh1 hh3
                  (Finset.sum_nonneg fun _ _ => sq_nonneg _) ((hv.nz 0).trans (hq 0))

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

theorem annih_dim (S : Space (Vec I)) :
    dim S + dim (annih S) = Fintype.card I := by
  have h := (pack S)ᵀ.mulVecLin.finrank_range_add_finrank_ker
  change ((pack S)ᵀ).rank + dim (annih S)=dim (Vec I) at h
  rwa [Matrix.rank_transpose,mrk_inj.mp (pack_inj _),dim_vec,Fintype.card_fin] at h

theorem dot_ext_zero {x : Vec I} (h : ∀ y, dotProduct y x=0) : x=0 := by
  classical funext i
            simpa using h (Pi.single i 1)

theorem annih_mem (x : Vec I) (S : Space (Vec I)) :
    x ∈ annih S ↔ ∀ y ∈ S,dotProduct x y = 0 := by
  change (pack S)ᵀ *ᵥ x=0 ↔ _
  constructor
  · intro h y hy
    obtain ⟨z,rfl⟩ := (pack_mem_iff ..).mp hy
    rw [← dotProduct_transpose_mulVec,h,dotProduct_zero]
  intro h
  refine dot_ext_zero fun y => ?_
  rw [dotProduct_transpose_mulVec]; exact h _ ((pack_mem_iff ..).mpr ⟨y,rfl⟩)

theorem annih_annih (S : Space (Vec I)) : annih (annih S)=S := by
  symm
  have hh : S ≤ annih (annih S) := by
    intro x hx; rw [annih_mem]
    intro y hy; rw [dotProduct_comm]
    exact (annih_mem ..).mp hy _ hx
  refine Submodule.eq_of_le_of_finrank_eq hh ?_
  have he := annih_dim S
  have hg := annih_dim (annih S)
  change dim S=_

  exact Nat.add_right_cancel ((he.trans hg.symm).trans (Nat.add_comm ..))

/-- A tensor killed by the product of the two factor quotients has bounded rank. -/
theorem rank_vanish {S : Space (Vec I)} {T : Space (Vec J)} {M : Mat I J}
    (h : vanish S T M) : M.rank≤dim S+dim T := by
  let P := pack (annih S)
  let Q := pack (annih T)
  have hh : Pᵀ*M*Q=0 := by
    refine evmat_ext fun x y => ?_
    have he := h _ ((pack_mem_iff ..).mpr ⟨x,rfl⟩) _ ((pack_mem_iff ..).mpr ⟨y,rfl⟩)
    rw [← evmat_pull] at he
    exact he.trans (by simp [evmat])
  have h1 := rank_ge_mul Pᵀ M
  have h2 := rank_ge_mul (Pᵀ*M) Q
  have hi := (mrk_inj.mp (pack_inj (annih S))).trans (Fintype.card_fin _)
  have hj := (mrk_inj.mp (pack_inj (annih T))).trans (Fintype.card_fin _)
  rw [Matrix.rank_transpose] at h1
  change P.rank = _ at hi; change Q.rank = _ at hj
  rw [hi] at h1; rw [hj,hh,Matrix.rank_zero] at h2
  have hx := annih_dim S
  have hy := annih_dim T
  have hv (x y z u v a b r : ℕ) (h : u+x ≤ r+a) (g : r+v≤0+b) (hx : y+u=a) (hy : z+v=b) :
      x≤y+z := by omega
  exact hv _ _ _ _ _ _ _ _ h1 h2 hx hy

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SparseLabelBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
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
theorem IH_self (b) : (IH p n b)ᵀ*IH p n b=1 := by
  apply embedMat_self
  intro i j; cases b <;> simp [putFull]
theorem IP_IH (a b : Bool) : (IP p n a)ᵀ * IH p n b=0 := by
  unfold IP IH; rw [embedMat_mul]
  ext i j; cases a <;> cases b <;> simp [embedMat,putFull]

theorem IP_cross {a b : Bool} (h : a ≠ b) : (IP p n a)ᵀ * IP p n b=0 := by
  unfold IP; rw [embedMat_mul]
  ext i j; cases a <;> cases b <;> first | contradiction | simp [embedMat,putFull]
theorem IH_cross {a b : Bool} (h : a ≠ b) : (IH p n a)ᵀ * IH p n b=0 := by
  unfold IH; rw [embedMat_mul]
  ext i j; cases a <;> cases b <;> first | contradiction | simp [embedMat,putFull]
theorem IH_IP (a b : Bool) : (IH p n a)ᵀ * IP p n b=0 := by
  simpa only [transpose_mul,Matrix.transpose_zero,transpose_transpose] using
    congrArg Matrix.transpose (IP_IH (p:=p) (n:=n) b a)

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
theorem hPin_dim (s : Plan p n) (z : Place p) (i) : dim (hPin s z i)≤dim (s z) :=
  Submodule.finrank_map_le _ _

theorem dim_le_plan (s : Plan p n) (e : Place p) :
    dim (s e) ≤ planRank s := Finset.single_le_sum (fun j _ => Nat.zero_le (dim (s j)))
      (Finset.mem_univ _)

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ImagePartitions
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Image Partitions -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

theorem plan_mono {a b : Plan p n} (h : a ≤ b) : planRank a ≤ planRank b :=
  Finset.sum_le_sum fun i _ => Submodule.finrank_mono (h i)

theorem plan_add_rank (a b : Plan p n) :
    planRank a + planNew a b = planRank (a⊔b) :=
  Nat.add_sub_of_le (plan_mono le_sup_left)

theorem planNew_mono_add {a b c : Plan p n} (h : a ≤ b) :
    planNew a b + planNew b c = planNew a (b⊔c) := by
  have he := plan_add_rank a b
  have hf := plan_add_rank b c
  have hg := plan_add_rank a (b⊔c)
  rw [sup_eq_right.mpr h] at he
  rw [sup_eq_right.mpr (le_trans h le_sup_left)] at hg
  omega

theorem Pin.combine {a b : Pin p n N} {x y} (ha : a.agree x) (hb : b.agree x) :
    (Pin.make (a.sp ⊔ b.sp) x).agree y ↔ a.agree y ∧ b.agree y := by
  change (∀ i, ∀ v ∈ a.sp i ⊔ b.sp i, images y i *ᵥ v = images x i *ᵥ v) ↔ _
  constructor
  · intro h
    exact ⟨fun i v hv => (h i v (Submodule.mem_sup_left hv)).trans (ha _ v hv),
      fun i v hv => (h i v (Submodule.mem_sup_right hv)).trans (hb _ v hv)⟩
  · rintro ⟨u,w⟩ i v hv
    obtain ⟨l,hl,r,hr,rfl⟩ := Submodule.mem_sup.mp hv
    rw [Matrix.mulVec_add,Matrix.mulVec_add,ha _ _ hl,hb _ _ hr,u _ _ hl,w _ _ hr]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_KeyDirections
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Key Directions -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Finset

variable {I : Type} [Fintype I]
variable {p : Shape} {n N : ℕ}

namespace Volley
variable (v : Volley p n I)

omit [Fintype I] in
theorem keys_loc (t : Tagging p I) (x : UnitType p n N) (i : I) (f : TagStar (t i)) (b : Bool) :
    v.keys t x i f b = images x (f.val,b) *ᵥ v.rayLoc i := by
  rw [rayLoc,mulVec_mulVec, images_ip]; rfl

omit [Fintype I] in
theorem atom_share (v' : Volley p n I) (t : Tagging p I) (x y : UnitType p n N)
    (h : v.keys t x=v'.keys t y) (i : I) :
    Uembed (onSide x (v.obj i)) (v.atomAt t i) = Uembed (onSide y (v'.obj i)) (v'.atomAt t i) := by
  classical
  funext e
  change liftM _ _ (atom p _ _ _ e) = liftM _ _ (atom p _ _ _ e)
  by_cases hs : inc e (t i)
  · simp only [atom_def,hs, ite_true, if_true,mom,liftM_outer]
    exact congrArg₂ vecMulVec (congr_fun (congr_fun (congr_fun h i) (⟨e,hs⟩)) true)
      (congr_fun (congr_fun (congr_fun h i) (⟨e,hs⟩)) false)
  simp only [atom_def,hs,ite_false, if_false,map_zero]

end Volley

/-- Any combination of points with distinct labels has a short-ray representation
on the image label set. -/
theorem point_comb {p : Shape} {A : Type*} (J : Finset A) (s : A → Label p.b)
    (z : A → Base p.g n) (a : A → F) (hs : Set.InjOn s (J : Set A)) :
    ∃ u : LabVals p n, (∀ i∈J,u (s i)=a i • baseV (z i)) ∧
      ∑ i∈J,a i • point p (s i) (z i)=labcomb p n (J.image s) u := by
  classical
  let f := fun j : Label p.b => ∑ i∈J, if s i=j then a i • baseV (z i) else 0
  have he i (hi : i∈J) : f (s i)=a i • baseV (z i) := by
    unfold f
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj he; exact ite_eq_right (fun h => he (hs hj hi h))
    simp [hi]
  refine ⟨f,he,?_⟩
  rw [labcomb_eval,Finset.sum_image hs]
  exact Finset.sum_congr rfl fun i hi => by rw [he i hi,map_smul]; rfl

namespace Volley

variable (v : Volley p n I)

theorem key_miss (t : Tagging p I) {a : Plan p n} {q} (h : v.avoids a q)
    (e : Place p) (x : Vec (visits p t e.1))
    (hx : v.keyM t e.1 *ᵥ x ∈ tabSpace a e) : x=0 := by
  classical
  let M := v.keyM t e.1
  have he : M *ᵥ x = ∑ i : visits p t e.1,x i • (v.rayLoc i.val) := by
    rw [mulVec_eq_sum]
    simp_rw [op_smul_eq_smul]
    rfl
  funext j
  let i := v.obj j.val
  obtain ⟨B,hB,hj,hc,hsel⟩ := h i
  have hT := (tab_mem a e _).mp hx i
  let f (j : visits p t e.1) := v.obj j.val=i
  let J := univ.filter f
  have hg : ∑ j∈J,x j • v.rayAt j.val ∈ sPin a e i := by
    change ((IP p n i)ᵀ.mulVecLin (M *ᵥ x))∈_ at hT
    rw [he,map_sum] at hT
    have hi :
        (∑ j∈J,x j • v.rayAt j.val) =
        ∑ j : visits p t e.1,(IP p n i)ᵀ.mulVecLin (x j • v.rayLoc j.val) := by
      rw [show J = univ.filter f from rfl,Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul,mulVecLin_apply,rayLoc,Matrix.mulVec_mulVec]
      by_cases hj : f j
      · rw [ite_eq_left hj,show v.obj j.val=i from hj,IP_self, Matrix.one_mulVec]
      rw [ite_eq_right hj,IP_cross (show i≠_ from Ne.symm hj), Matrix.zero_mulVec,smul_zero]
    rwa [hi]
  let s (x : visits p t e.1) := v.sel x.val
  have hh {j : visits p t e.1} (h : j∈J) : j.val∈v.here i :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,(mem_filter.mp h).2⟩
  have heq : Set.InjOn s (J : Set _) := fun j hj k hk h => Subtype.ext (hsel (hh hj) (hh hk) h)
  obtain ⟨u,hu,hZ⟩ := point_comb J s (v.par ∘ Subtype.val) x heq
  have hjj : j∈J := mem_filter.mpr ⟨mem_univ _,rfl⟩
  have hx : (J.image s).card ≤ q := by
    refine (card_image_le).trans (le_trans ?_ hc)
    have hsub : J.image Subtype.val ⊆ v.here i := by
      rintro x hx; obtain ⟨i,hi,rfl⟩ := mem_image.mp hx; exact hh hi
    rw [← card_image_of_injective J Subtype.val_injective]; exact card_le_card hsub
  have hz := hB e (J.image s) u (hZ ▸ hg) hx (s j) (mem_image_of_mem s hjj) (hj _ (hh hjj))
  rw [hu j hjj] at hz
  have heq := congr_fun hz none
  simpa only [Pi.zero_apply,Pi.smul_apply,smul_eq_mul,baseV,Option.elim',mul_one] using heq

theorem key_independent (t : Tagging p I) {a : Plan p n} {q} (h : v.avoids a q)
    (e : Place p) : Function.Injective (v.keyM t e.1).mulVec ∧
      Disjoint (v.keyPlan t e) (tabSpace a e) := by
  constructor
  · rw [← Matrix.coe_mulVecLin,← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
    intro x hx
    apply key_miss v t h e
    rw [hx]
    exact Submodule.zero_mem _
  rw [disjoint_iff_inf_le]
  rintro x ⟨⟨y,rfl⟩,hx⟩
  rw [key_miss v t h e y hx,map_zero]
  exact Submodule.zero_mem _
end Volley
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RealizationConditions
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Realization Conditions -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I]

namespace Volley
variable (v w : Volley p n I)

theorem shoots_swap (i j) : v.shoots w.obj i j=w.shoots v.obj j i := by
  ext; simp [shoots,and_comm]

theorem sum_share {t : Tagging p I} {x y : UnitType p n N} (h : v.keys t x=w.keys t y)
    (i j : Bool) : Uembed (onSide x i) (v.sumAt t w.obj i j)=
      Uembed (onSide y j) (w.sumAt t v.obj j i) := by
  classical
  unfold sumAt
  rw [map_sum,map_sum,← shoots_swap v w]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hi := (Finset.mem_filter.mp hk).2
  rw [← hi.1, ← hi.2]
  exact v.atom_share _ _ _ _ h k

theorem sum_mem {t : Tagging p I} (h : v.legal t) (f : I → Bool) (i j : Bool) :
    v.sumAt t f i j∈Xspace p n :=
  Submodule.sum_mem _ fun k _ => atom_mem _ (h k)

theorem realized_conflicts {t : Tagging p I} (m : Mixer p n)
    (x y : UnitType p n N) (hv : v.legal t) (hw : w.legal t)
    (hL : ∀ i, frameLaw m (onSide x i)) (hR : ∀ i, frameLaw m (onSide y i))
    (h : v.keys t x=w.keys t y) (hm : v.roleMatch w t)
    (hA : v.realized w t m (actual p x y)) (hB : w.realized v t m (actual p y x)) :
    (rawHoles m).conflict x y := by
  have hh i j : hole m (onSide x i) (onSide y j) := by
    refine ⟨hL i,hR j,v.sumAt t w.obj i j,w.sumAt t v.obj j i,
      v.sum_mem hv .., w.sum_mem hw .., v.sum_share _ h i j,fun q hq => ?_,fun q hq => ?_,hm i j⟩
    · rw [hA _ _ _ hq,contract_actual]; rfl
    · rw [hB _ _ _ hq,contract_actual]; rfl
  exact ⟨hh true true,hh true false,hh false true,hh false false⟩

end Volley

theorem contract_val (p : Shape) {n} (M : Cross p n) (i j : Bool) (x : Profile p n) :
    contract p M i j x = ∑ e,mpair
      ((scalarBlocks p M (e,true) i j)ᵀ * scalarBlocks p M (e,false) i j) (x e) := by
  change ∑ e : Comp p.g, _ = _
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mpair_liftM]
  simp only [liftM_def,transpose_transpose,scalarBlocks,transpose_mul,Matrix.mul_assoc]

theorem contract_scalars (A M : Cross p n) (h : scalarBlocks p A=scalarBlocks p M) (i j) :
    contract p A i j=contract p M i j := by
  refine LinearMap.ext fun v => ?_
  rw [contract_val,contract_val,h]
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GradientRankBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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

private theorem part_formula_single (i j : Tag p.g) (e : Comp p.g) (M : Moment p n) :
    getPair p n i j (Pi.single e M) =
      (if i=e.val.1 ∧ j=e.val.2 then M else 0) +
      (if i=e.val.2 ∧ j=e.val.1 then M else 0) := by
  classical
  rcases e with ⟨⟨u,v⟩,hu⟩
  by_cases h : i=j
  · subst j
    have hv : u≠v := hu.ne
    have hu : ¬ (i=u ∧ i=v) := fun ⟨e,g⟩ => hv (e.symm.trans g)
    have hw : ¬ (i=v ∧ i=u) := by tauto
    simp [getPair,hu,hw]
  rw [getPair_edge i j h]
  change (Pi.single (⟨(u,v),hu⟩:Comp p.g) M : Profile p n) (edge i j h) = (if i=u ∧ j=v then M else 0)+
    (if i=v ∧ j=u then M else 0)
  rcases lt_or_gt_of_ne h with ht|ht
  · have ha : ¬ (i=v∧j=u) := by
      rintro ⟨rfl,rfl⟩; exact hu.asymm ht
    simp [edge,ht,Pi.single_apply,ha]
  · have ha : ¬ (i=u∧j=v) := by
      rintro ⟨rfl,rfl⟩; exact hu.asymm ht
    simp [edge,not_lt.mpr ht.le,Pi.single_apply,ha,and_comm]

private theorem shared_at (t : Tag p.g) (e : Comp p.g) (M : Moment p n) :
    ∃ s : F,
      s = sharedT p n t (Pi.single e M) ∧
      s = (if t=e.val.2 then etab p n Block.S M else 0) +
        if t=e.val.1 then etab p n Block.S M else 0 := by
  refine ⟨_,rfl,?_⟩
  simp only [sharedT,LinearMap.sum_apply,LinearMap.comp_apply,part_formula_single,
    map_add,Finset.sum_add_distrib]
  let u := fun i => etab p n Block.S i
  have hi (a b : Tag p.g) :
      ∑ l, u (if l=a ∧ t=b then M else 0) =
        if t=b then u M else 0 := by
    rw [Finset.sum_eq_single a]
    · split <;> simp_all [u]
    · intro b _ hb; simp [hb,u]
    simp
  exact congrArg₂ (·+·) (hi _ _) (hi _ _)

private theorem role_at (t : Tag p.g) (e : Comp p.g) (M : Moment p n) :
    roleT p n t (Pi.single e M) =
      mpair (routed p n t e.val.1 e.val.2 + routed p n t e.val.2 e.val.1) M := by
  classical
  simp only [roleT,LinearMap.sum_apply,LinearMap.comp_apply,part_formula_single,map_add,
    Finset.sum_add_distrib,mpair_add]
  let u := fun d => etab p n (Block.O d t)
  have hh (i j : Tag p.g) :
      ∑ (l : Tag p.g), ∑ d ∈ Finset.univ.filter (fun d => allowed d l),
        u d (if l=i ∧ d=j then M else 0) = mpair (routed p n t i j) M := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · by_cases h : allowed j i
        · simp [h,u,routed,etab]
        simp [h,routed]; rw [mpair_comm,map_zero]
      · intro d _ hd
        simp [u,hd]
      simp
    · intro l _ hl
      simp [u,hl]
    simp
  exact congrArg₂ (·+·) (hh _ _) (hh _ _)

private theorem test_rank (d : Block p.g) : (testM p n d).rank ≤ p.r := by
  apply le_trans (mrk_sum_le ..)
  refine (Finset.sum_le_sum (g:=fun _ => 1) (fun i _ => Matrix.rank_vecMulVec_le ..)).trans_eq ?_
  simp

theorem rep_single {m : Profile p n →ₗ[F] F} {A : Profile p n}
    (h : ∀ (e : Comp p.g) (M : Moment p n), m (Pi.single e M)=mpair (A e) M) :
    Represents m A := by
  intro x
  have heq : m x=m (∑ e, Pi.single e (x e)) := by rw [Finset.univ_sum_single]
  rw [heq,map_sum]
  exact Finset.sum_congr rfl fun i _ => h _ _

theorem tmix_small (m : Mixer p n) (x : Profile p n) (K : ℕ) (hK : ∀ e,(x e).rank≤K) :
    ∃ A, Represents (Tmix m x) A ∧ ∀ e,(A e).rank≤2*p.J*Fintype.card (Comp p.g)*K := by
  let f (e) := ∑ (j : Fin p.J), ∑ i : Comp p.g,
    (liftM (m.mixL j i e)ᵀ (m.mixR j i e)ᵀ (x i) +
     liftM (m.mixL j e i) (m.mixR j e i) (x i))
  refine ⟨f,fun y => ?_,fun e => ?_⟩
  · let F j i e := mpair (liftM (m.mixL j i e)ᵀ (m.mixR j i e)ᵀ (x i)) (y e)
    let G j i e := mpair (liftM (m.mixL j e i) (m.mixR j e i) (x i)) (y e)
    have he : Tmix m x y =
        (∑ j,∑ i, ∑ e,F j i e) + ∑ j,∑ e,∑ i,G j i e := by
      change (∑ j,∑ i,∑ e, mpair (x i) (liftM (m.mixL j i e) (m.mixR j i e) (y e)))+
        (∑ j,∑ e,∑ i, mpair (y e) (liftM (m.mixL j e i) (m.mixR j e i) (x i)))=_
      refine congrArg₂ _ ?_ ?_
      · simp_rw [mpair_liftM]; rfl
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => mpair_comm _ _
    rw [he]
    simp only [f,mpair_sum,mpair_add,Finset.sum_add_distrib]
    change _ = (∑ e,∑ j,∑ i,F j i e) + ∑ e,∑ j,∑ i,G j i e
    refine congrArg₂ _ ?_ (Finset.sum_comm)
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  · apply le_trans (mrk_sum_le ..)
    let E := Fintype.card (Comp p.g)
    refine (Finset.sum_le_sum (g:=fun _ => E*(2*K)) (fun j _ => ?_)).trans_eq ?_
    · apply le_trans (mrk_sum_le ..)
      refine (Finset.sum_le_sum (g:=fun _ => 2*K) (fun i _ => ?_)).trans_eq (by simp [E])
      exact (mrk_add_le ..).trans ((Nat.add_le_add ((rank_lift_le ..).trans (hK i))
        ((rank_lift_le ..).trans (hK i))).trans_eq (two_mul _).symm)
    simp [E] <;> ring

set_option maxHeartbeats 800000 in
theorem grad_small {m : Mixer p n} {v : Tag p.g → Moment p n}
    (hg : Odd p.g) (hv : ∀ l,v l∈ Wtag p n l) (hs : parityW v=1)
    (hz : (nonzeroTags v).card ≤ 7) (hr : ∀ e,(cut p n v e).rank ≤ 7) :
    ∃ A, Represents (grad m (cut p n v)) A ∧
      ∀ e,(A e).rank ≤ 15*p.r + 14*p.J * Fintype.card (Comp p.g) := by
  let x := cut p n v
  let d t := etab p n Block.S (v t)
  obtain ⟨A,hA,hR⟩ := tmix_small m x 7 hr
  let h : Profile p n →ₗ[F] F := role p n + T0 p n x
  have hf : h = (∑ t,d t • roleT p n t)+ ∑ t, roleT p n t x • sharedT p n t := by
    have hc : role p n x + ∑ t,d t=1 := by
      simp only [parityW,eta,LinearMap.add_apply,Finset.sum_add_distrib] at hs
      rw [show x=cut p n v from rfl,role_cut _ v hv]
      exact hs
    have hcoef (t : Tag p.g) : 1+role p n x + sharedT p n t x = d t := by
      unfold x
      rw [sharedT_cut p hg]
      change 1+role p n x + ((∑ i,d i)+d t) = _
      rw [←add_assoc,add_assoc 1,hc,char_two,zero_add]
    refine LinearMap.ext fun y => ?_
    change role p n y+T0 p n x y = _
    simp only [T0_val,LinearMap.add_apply,LinearMap.sum_apply,
      Finset.sum_add_distrib,LinearMap.smul_apply,smul_eq_mul]
    calc role p n y +
          (role p n x * role p n y +
          ((∑ x_1 : Tag p.g,roleT p n x_1 x*sharedT p n x_1 y)+
          ∑ x_1 : Tag p.g,sharedT p n x_1 x*roleT p n x_1 y))
      _ = (∑ t : Tag p.g,(1+role p n x+sharedT p n t x)* roleT p n t y)+
        ∑ x_1 : Tag p.g,roleT p n x_1 x*sharedT p n x_1 y := by
          simp only [add_mul,one_mul,Finset.sum_add_distrib,
            ← Finset.mul_sum]; simp only [role,LinearMap.sum_apply] <;> ring
      _ = _ := by simp_rw [hcoef]
  let Y (e : Comp p.g) (i : Tag p.g) :=
    routed p n i e.val.1 e.val.2 + routed p n i e.val.2 e.val.1
  let P (e : Comp p.g) :=
    ∑ i∈nonzeroTags v,d i • Y e i
  let a (e : Comp p.g) := roleT p n e.val.1 x + roleT p n e.val.2 x
  let Q (e : Comp p.g) := a e • testM p n Block.S
  have he : Represents h (fun e => P e+Q e) := by
    apply rep_single
    intro e M
    rw [hf,mpair_add]
    simp only [LinearMap.add_apply,LinearMap.sum_apply,LinearMap.smul_apply,
      smul_eq_mul]
    refine congrArg₂ _ ?_ ?_
    · simp only [P,Y,role_at,mpair_sum,mpair_smul]
      refine (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => ?_)).symm
      have hg : v i=0 := by rwa [mem_nonzeroTags,not_not] at hi
      rw [show d i=0 from (by unfold d; rw [hg,map_zero]),zero_mul]
    · have hh (i : Tag p.g) :
          sharedT p n i (Pi.single e M) =
            (if i=e.val.2 then etab p n Block.S M else 0)+(if i=e.val.1 then
              etab p n Block.S M else 0) := by
        obtain ⟨s,h1,h2⟩ := shared_at i e M; rw [← h1,h2]
      simp_rw [hh,mul_add,Finset.sum_add_distrib,Q,mpair_smul,a,add_mul]
      simp only [mul_ite,mul_zero,Finset.sum_ite_eq',
        Finset.mem_univ,ite_true, if_true,etab]
      exact add_comm _ _
  refine ⟨fun e => P e+Q e+A e,fun y => ?_, fun e => ?_⟩
  · simp only [mpair_add,Finset.sum_add_distrib]
    have hx : grad m x y=h y+Tmix m x y := (add_assoc (role p n y) (T0 p n x y) (Tmix m x y)).symm
    rw [show grad m (cut p n v) y=_ from hx,he y,hA y]
    simp only [mpair_add,Finset.sum_add_distrib]
  · have hi : (P e).rank ≤ 14*p.r := by
      have hr (i a b : Tag p.g) : (routed p n i a b).rank ≤ p.r := by
        unfold routed
        split
        · exact test_rank _
        simp
      have hy (i) : (d i • Y e i).rank ≤ 2*p.r := by
        rcases bit_cases (d i) with h|h
        · simp [h]
        rw [h,one_smul,two_mul]
        exact (mrk_add_le ..).trans (Nat.add_le_add (hr ..) (hr ..))
      refine (mrk_sum_le ..).trans ((Finset.sum_le_sum (fun i _ => hy i)).trans ?_)
      simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id] <;> nlinarith
    have hj : (Q e).rank ≤ p.r := by
      rcases bit_cases (a e) with h|h
      · simp [Q,h]
      unfold Q; rw [h,one_smul]; exact test_rank _
    refine le_trans (mrk_add_le ..) ((Nat.add_le_add ((mrk_add_le (P e) _).trans
      (Nat.add_le_add hi hj)) (hR e)).trans ?_)
    apply le_of_eq; ring

namespace Volley
variable {I : Type} [Fintype I] [DecidableEq I] (v : Volley p n I)

omit [DecidableEq I] in
theorem gradient_rep (m : Mixer p n) {t : Tagging p I} {w : I → Bool} {i j : Bool}
    (hg : Odd p.g) (h : v.legal t) (hb : (v.shoots w i j).card ≤ 7)
    (hd : ∑ a∈v.shoots w i j,v.diagonalAt a=1) :
    ∃ A, Represents (grad m (v.sumAt t w i j)) A ∧
      ∀ e,(A e).rank ≤ 15*p.r+14*p.J*Fintype.card (Comp p.g) := by
  classical
  let S := v.shoots w i j
  let w' (a : I) : Tag p.g → Moment p n :=
    Pi.single (t a) (mom p (v.sel a) (v.par a))
  let C := ∑ i∈S,w' i
  have h1 (a) : atomAt v t a=cut p n (w' a) := rfl
  have he : sumAt v t w i j=cut p n C := by
    change (∑ i∈S,_) = cut p n (∑ i∈S,_)
    simp_rw [h1,map_sum]
  rw [he]
  apply grad_small hg
  · intro l
    change (∑ i∈S, w' i) l ∈ _
    rw [Finset.sum_apply]
    apply Submodule.sum_mem
    intro a _
    by_cases e : l=t a
    · subst l
      simp only [w',Pi.single_eq_same]
      exact Submodule.subset_span ⟨_,_,h a,rfl⟩
    simp [w',Pi.single_eq_of_ne e]
  · unfold parityW
    simp only [C,Finset.sum_apply,map_sum]
    rw [Finset.sum_comm]
    refine (Finset.sum_congr (g:=fun a => v.diagonalAt a) rfl fun a _ => ?_).trans hd
    rw [Finset.sum_eq_single (t a)]
    · rw [show w' a (t a)=_ from Pi.single_eq_same _ _]
      rfl
    · intro l _ hl; simp [w',Pi.single_eq_of_ne hl]
    simp
  · have hC : nonzeroTags C ⊆ S.image t := by
      intro l hl
      by_contra hn
      apply mem_nonzeroTags l C |>.mp hl
      simp only [C,Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro a ha
      simp [w',Pi.single_eq_of_ne (show l≠t a from fun h0 => hn
        (Finset.mem_image.mpr ⟨a,ha,h0.symm⟩))]
    exact (Finset.card_le_card hC).trans (Finset.card_image_le.trans hb)
  intro e
  rw [← he,Volley.sumAt, Finset.sum_apply]
  apply le_trans (mrk_sum_le ..)
  refine le_trans ((Finset.sum_le_sum (g:=fun _ => 1) fun _ _ => ?_).trans_eq ?_) hb
  · rw [atomAt,atom_def]
    split
    · apply Matrix.rank_vecMulVec_le
    · simp
  · simp

theorem here_card {w : I → Bool} (h : v.bounded w) (i : Bool) : (v.here i).card≤14 := by
  have he : v.here i ⊆ v.shoots w i true ∪ v.shoots w i false :=
    fun j hj => by
      have hi : v.obj j=i := (Finset.mem_filter.mp hj).2
      cases h : w j <;> simp [shoots,hi,h]
  exact le_trans ((Finset.card_le_card he).trans (Finset.card_union_le _ _))
    (Nat.add_le_add (h _ _).2 (h _ _).2)

theorem call_count {w : I→Bool} (h : v.bounded w) : Fintype.card I ≤ 28 := by
  have he : Finset.univ ⊆ v.here true ∪ v.here false :=
    fun j _ => by cases h : v.obj j <;> simp [here,h]
  have hh := (Finset.card_le_card he).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add (here_card _ h true) (here_card _ h false)))
  exact (Finset.card_univ.symm.le.trans hh)

end Volley
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PrimalChannelDecomposition
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Primal Channel Decomposition -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Submodule
variable {I : Type} [Fintype I]

theorem rank_maps {J : Type} [Fintype J] {A : Mat I J} (S : Space (Vec I))
    (ha : ∀ x,A *ᵥ x∈ S) : A.rank ≤ dim S :=
  Submodule.finrank_mono (show colSp A ≤ S by
    rintro x ⟨x,rfl⟩; exact ha x)

theorem evmat_addM {J : Type} [Fintype J] (A B : Mat I J) (x y) :
    evmat (A+B) x y = evmat A x y+evmat B x y := by rw [←mpair_outer,mpair_add,
      mpair_outer,mpair_outer]

theorem evmat_subM {J : Type} [Fintype J] (A B : Mat I J) (x y) :
    evmat (A-B) x y = evmat A x y-evmat B x y := by
  rw [ZModModule.sub_eq_add, ZModModule.sub_eq_add, evmat_addM]

variable {p : Shape} {n : ℕ}

theorem ip_le_primal (b : Bool) : colSp (IP p n b)≤primal p n := by
  cases b; exact le_sup_right; exact le_sup_left

theorem channels_proj (b : Bool) : channels p n ≤ LinearMap.ker (IP p n b)ᵀ.mulVecLin := by
  have hi (i : Bool) : colSp (IH p n i) ≤ LinearMap.ker (IP p n b)ᵀ.mulVecLin := by
    rintro x ⟨y,rfl⟩
    change (IP p n b)ᵀ *ᵥ (IH p n i *ᵥ y) = _
    rw [mulVec_mulVec, IP_IH, Matrix.zero_mulVec]
  exact sup_le (hi _) (hi _)

theorem primal_proj (b : Bool) : primal p n ≤ LinearMap.ker (IH p n b)ᵀ.mulVecLin := by
  have hi (i : Bool) : colSp (IP p n i) ≤ LinearMap.ker (IH p n b)ᵀ.mulVecLin := by
    rintro x ⟨y,rfl⟩
    change (IH p n b)ᵀ *ᵥ (IP p n i *ᵥ y) = _
    rw [mulVec_mulVec, IH_IP, Matrix.zero_mulVec]
  exact sup_le (hi _) (hi _)

theorem channels_disjoint : Disjoint (primal p n) (channels p n) := by
  rw [disjoint_iff_inf_le]
  rintro x ⟨hx,hy⟩
  have he (b : Bool) : (IP p n b)ᵀ *ᵥ x = 0 := channels_proj b hy
  have hf (b : Bool) : (IH p n b)ᵀ *ᵥ x = 0 := primal_proj b hx
  have hh := ip_decomp (show Dir p n from x)
  simp_rw [he,hf,mulVec_zero,add_zero, Finset.sum_const_zero] at hh
  rw [← hh]
  exact Submodule.zero_mem _

theorem prSmall_le (a : Plan p n) (z : Place p) : prSmall a z≤primal p n := by
  apply sup_le_sup <;> rintro x ⟨x,h,rfl⟩ <;> exact ⟨x,rfl⟩

theorem prSmall_dim (a : Plan p n) (z : Place p) :
    dim (prSmall a z)≤2 * planRank a := by
  rw [two_mul]
  have hh (i : Bool) :
      dim ((sPin a z i).map (IP p n i).mulVecLin) ≤ planRank a :=
    (Submodule.finrank_map_le ..).trans ((sPin_dim ..).trans (dim_le_plan a z))
  exact (Submodule.finrank_add_le_finrank_add_finrank ..).trans (Nat.add_le_add (hh _) (hh _))

theorem prSmall_table (a : Plan p n) (z : Place p) :
    tabSpace a z = prSmall a z ⊔ channels p n := by
  unfold tabSpace halfTable prSmall channels
  ac_rfl

theorem keyPlane (v : Volley p n I) (t : Tagging p I) (z : Place p) :
    v.keyPlan t z≤ primal p n := by
  unfold Volley.keyPlan colSp
  rw [range_mulVecLin]
  apply Submodule.span_le.mpr
  rintro x ⟨j,rfl⟩
  exact (show colSp (IP p n _) ≤ primal p n from ip_le_primal (v.obj j.val))
    (show v.rayLoc j.val∈colSp (IP p n _) from ⟨_,rfl⟩)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BaselineExtension
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Baseline Extension -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Submodule

variable {p : Shape} {n : ℕ}

theorem project_table (a : Plan p n) (z : Place p) (Q : Space (Dir p n))
    (hq : Q ≤ primal p n) (hd : Disjoint (tabSpace a z) Q) :
    ∃ B, ProjData (tabSpace a z) Q B ∧ ∀ x∈ primal p n, B*ᵥx∈prSmall a z := by
  classical
  let H := channels p n
  let A := primal p n
  let P := prSmall a z
  have hp : P≤ A := prSmall_le _ _
  have he : tabSpace a z=P ⊔ H := prSmall_table a z
  obtain ⟨X,hX⟩ := proj_exists H A channels_disjoint.symm
  have hj : Disjoint P (Q⊔H) := by
    rw [disjoint_iff_inf_le]
    rintro v ⟨hv,hv'⟩
    obtain ⟨y,hy,w,hw,g⟩ := Submodule.mem_sup.mp hv'
    have h := (show w=v-y by rw [←g]; abel) ▸
      A.sub_mem (hp hv) (hq hy)
    have hz : w∈ A ⊓ H := ⟨h,hw⟩
    rw [channels_disjoint.eq_bot] at hz
    have hi : w=0 := by simpa using hz
    rw [hi,add_zero] at g
    have ht : v∈tabSpace a z ⊓ Q :=
      ⟨he.symm ▸ Submodule.mem_sup_left hv,g ▸ hy⟩
    rwa [hd.eq_bot] at ht
  obtain ⟨Y,hY⟩ := proj_exists P (Q⊔H) hj
  refine ⟨X+Y,⟨fun x => ?_,fun x hx => ?_,fun x hx => ?_⟩, fun x hx => ?_⟩
  · rw [add_mulVec,he,add_comm]; exact add_mem_sup (hY.onto _) (hX.onto _)
  · rw [he] at hx
    obtain ⟨v,hv,w,hw,rfl⟩ := Submodule.mem_sup.mp hx
    rw [add_mulVec,mulVec_add,mulVec_add,hX.kills v (hp hv),hX.fixes _ hw,hY.fixes _ hv,
      hY.kills _ (Submodule.mem_sup_right hw),add_zero,zero_add,add_comm]
  · rw [add_mulVec,hX.kills x (hq hx),hY.kills x (Submodule.mem_sup_left hx),zero_add]
  · rw [add_mulVec,hX.kills x hx,zero_add]; exact hY.onto _

set_option maxHeartbeats 800000 in
theorem base_pair (a b : Plan p n) (u v : Place p)
    (K J : Space (Dir p n)) (hk : K≤primal p n) (hj : J≤primal p n)
    (hK : Disjoint (tabSpace a u) K) (hJ : Disjoint (tabSpace b v) J)
    (A B : CrossM p n)
    (heq : ∀ x∈ tabSpace a u,∀ y∈tabSpace b v,x∈a u ∨ y∈b v → evmat A x y=evmat B x y) :
    ∃ M : CrossM p n,
      (∀ x∈tabSpace a u,∀ y∈tabSpace b v,evmat M x y=evmat B x y) ∧
      (∀ x y, x∈ (a u⊔K) ∨ y∈(b v⊔J) → evmat M x y=evmat A x y) ∧
      (∀ i,(Mᵀ*IP p n i).rank ≤ dim (a u⊔K : Submodule _ _) + dim (b v⊔J : Submodule _ _) +
        2*planRank a) ∧
      (∀ i,(M*IP p n i).rank ≤ dim (a u⊔K : Submodule _ _) + dim (b v⊔J : Submodule _ _) +
        2*planRank b) := by
  let P := a u⊔K
  let Q := b v⊔J
  obtain ⟨X,hX⟩ := proj_exists P ⊥ disjoint_bot_right
  obtain ⟨Y,hY⟩ := proj_exists Q ⊥ disjoint_bot_right
  obtain ⟨L,hL,gL⟩ := project_table a u K hk hK
  obtain ⟨R,hR,gR⟩ := project_table b v J hj hJ
  let C := pullM X (1:CrossM p n) A + pullM (1-X) Y A
  let M := C + pullM L R (B-C)
  have h1 (x y) (hx : x∈P ∨ y∈Q) : evmat C x y=evmat A x y := by
    rw [show C=_ from rfl,evmat_addM,evmat_pull,evmat_pull,sub_mulVec,Matrix.one_mulVec,
      Matrix.one_mulVec]
    rcases hx with h|h
    · rw [hX.fixes _ h,sub_self]; simp [evmat]
    rw [hY.fixes _ h]
    simp [evmat,sub_dotProduct]
  have h2 (x y) : evmat M x y=evmat C x y+
      (evmat B (L *ᵥ x) (R *ᵥ y)-evmat C (L*ᵥ x) (R*ᵥ y)) := by
    rw [show M=_ from rfl,evmat_addM,evmat_pull,evmat_subM]
  have hRank : C.rank≤dim P+dim Q := by
    apply (mrk_add_le ..).trans
    have hx : X.rank≤dim P := rank_maps _ hX.onto
    have hy : Y.rank≤dim Q := rank_maps _ hY.onto
    apply Nat.add_le_add
    · rw [pullM_def]
      refine ((Matrix.rank_mul_le_left ..).trans (Matrix.rank_mul_le_left ..)).trans ?_
      rwa [Matrix.rank_transpose]
    · rw [pullM_def]; exact (Matrix.rank_mul_le_right ..).trans hy
  have hr (i) {a : Plan p n} (u)
      (R : CrossM p n) (h : ∀ x∈primal p n,R*ᵥ x∈prSmall a u) :
      (R*IP p n i).rank≤ 2*planRank a := by
    apply le_trans (rank_maps (prSmall a u) _)
      (prSmall_dim a u)
    intro x
    rw [← Matrix.mulVec_mulVec]
    exact h _ (ip_le_primal i (show IP p n i*ᵥx∈colSp (IP p n i) from ⟨x,rfl⟩))
  refine ⟨M, fun x hx y hy => ?_, fun x y h => ?_, fun i => ?_, fun i => ?_⟩
  · rw [h2,hL.fixes x hx,hR.fixes y hy,add_sub_cancel]
  · have hi : L*ᵥ x ∈ a u ∨ R *ᵥ y ∈ b v := by
      rcases h with h|h
      · left; obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp h
        rwa [Matrix.mulVec_add,hL.kills _ hy,hL.fixes _ (pin_le_table _ _ hx),add_zero]
      right; obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp h
      rwa [Matrix.mulVec_add,hR.kills _ hy,hR.fixes _ (pin_le_table _ _ hx),add_zero]
    have he : L*ᵥx ∈ P ∨ R*ᵥy∈Q := hi.imp Submodule.mem_sup_left Submodule.mem_sup_left
    rw [h2,h1 _ _ h,h1 _ _ he,heq _ (hL.onto _) _ (hR.onto _) hi,sub_self,add_zero]
  · unfold M
    rw [transpose_add,Matrix.add_mul]
    refine (mrk_add_le ..).trans (Nat.add_le_add ?_ ?_)
    · exact (Matrix.rank_mul_le_left ..).trans ((Matrix.rank_transpose _).trans_le hRank)
    rw [pullM_def,transpose_mul,transpose_mul,transpose_transpose,Matrix.mul_assoc,
      Matrix.mul_assoc]
    exact ((Matrix.rank_mul_le_right ..).trans (Matrix.rank_mul_le_right ..)).trans (hr i u L gL)
  · unfold M
    rw [Matrix.add_mul]
    refine (mrk_add_le ..).trans (Nat.add_le_add ?_ ?_)
    · exact (Matrix.rank_mul_le_left ..).trans hRank
    rw [pullM_def,Matrix.mul_assoc]
    exact (Matrix.rank_mul_le_right ..).trans (hr i v R gR)

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

set_option maxHeartbeats 800000 in
theorem start_form (a b : Pin p n N) (x y : UnitType p n N) (T : Cross p n)
    (ka kb : Plan p n)
    (hA : ∀ z,ka z≤primal p n) (hB : ∀ z,kb z≤primal p n)
    (hd : ∀ z, Disjoint (tabSpace a.sp z) (ka z))
    (hd' : ∀ z, Disjoint (tabSpace b.sp z) (kb z))
    (ha : a.agree x) (hb : b.agree y) (h1 : tableFlag a b T x)
    (h2 : tableFlag b a (reciprocal p T) y)
    (K : ℕ) (hk : planRank a.sp ≤ K) (hk' : planRank b.sp ≤ K)
    (hv : ∀ z, dim (ka z) ≤ 28) (hv' : ∀ z, dim (kb z) ≤ 28) :
    ∃ M : Cross p n, fitsTable a.sp b.sp M T ∧
      rowAgree (a.sp ⊔ ka) M (actual p x y) ∧
      rowAgree (b.sp ⊔ kb) (reciprocal p M) (actual p y x) ∧
      lowCross (blin K) M ∧ lowCross (blin K) (reciprocal p M) := by
  let A := actual p x y
  have hh (z : Place p) (u v) (hu : u∈tabSpace a.sp z) (hv : v∈tabSpace b.sp (flipZ p z))
      (h : u∈a.sp z ∨ v∈b.sp (flipZ p z)) : evmat (A z) u v=evmat (T z) u v := by
    rcases h with h|h
    · have h' : u ∈ a.sp (flipZ p (flipZ p z)) := by rwa [flipZ_flip]
      have he := h2 _ v hv u h'
      have hf := flag_actual (a:=b) y x ha (flipZ p z) v hv u h'
      have hg := hf.trans he.symm
      rw [← reciprocal_actual x y] at hg
      simp only [reciprocal,flipZ_flip,evmat_transpose] at hg
      exact hg
    exact (flag_actual (a:=a) x y hb _ u hu v h).trans (h1 _ u hu v h).symm
  choose M hC hD hE hF using fun z =>
    base_pair a.sp b.sp z (flipZ p z) (ka z) (kb (flipZ p z)) (hA _) (hB _) (hd _) (hd' _)
      (A z) (T z) (fun u hu v hv g => hh z u v hu hv g)
  have hr (z) {a s : Plan p n} (h : planRank a≤K) (hg : ∀ z,dim (s z)≤28) :
      dim (a z ⊔ s z : Submodule _ _) ≤ K+28 :=
    (Submodule.finrank_add_le_finrank_add_finrank ..).trans
      (Nat.add_le_add ((dim_le_plan a _).trans h) (hg _))
  have hm z {L} (hl : L≤K) : dim (a.sp z ⊔ ka z : Submodule _ _)+
      dim (b.sp (flipZ p z) ⊔ kb (flipZ p z):Submodule _ _)+2*L ≤ blin K := by
    apply le_trans (Nat.add_le_add (Nat.add_le_add (hr z hk hv) (hr _ hk' hv'))
      (Nat.mul_le_mul_left 2 hl))
    unfold blin; omega
  refine ⟨M,hC,(fun z u hu v => hD z u v (Or.inl hu)),?_,
    fun z i => (hE z i).trans (hm z hk),?_⟩
  · rw [← reciprocal_actual x y]
    intro z v hv u
    unfold reciprocal; rw [evmat_transpose,evmat_transpose]
    apply hD
    right
    rw [flipZ_flip]; exact hv
  intro z i
  unfold reciprocal; rw [transpose_transpose]
  exact (hF (flipZ p z) i).trans (hm _ hk')

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

variable {I : Type} [Fintype I]

theorem frozen_contract_key {M T : Cross p n} {a} (v : Volley p n I) (t : Tagging p I)
    (h : rowAgree (a⊔v.keyPlan t) M T) (i : I) (j : Bool) :
    contract p M (v.obj i) j (v.atomAt t i)=contract p T (v.obj i) j (v.atomAt t i) := by
  classical
  change ∑ e : Comp p.g, _ = _
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases he : inc e (t i)
  · have hx b :
        v.rayLoc i ∈ (v.keyPlan t (e,b)) := colSp_mem (P:=v.keyM t e)
          (⟨i,he⟩ : Volley.visits p t e)
    have hE (b : Bool) : channelOut p M j (e,b) *ᵥ v.rayLoc i =
        channelOut p T j (e,b) *ᵥ v.rayLoc i :=
      channel_same j _ _ (fun y => h _ _ (Submodule.mem_sup_right (hx b)) _)
    simp only [Volley.atomAt,atom_def,he, ite_true, if_true,mom,liftM_outer,mpair_outer]
    rw [cout_ev,cout_ev]
    exact congrArg₂ dotProduct (hE true) (hE false)
  simp only [Volley.atomAt,atom_def,he,ite_false, if_false,map_zero]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_LinearResponse
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear Response -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module
open scoped BigOperators
variable {p : Shape} {n : ℕ}

theorem pureSpace_mem {f : Plan p n} (P : PureForms p n) :
    P∈pureSpace p f ↔ ∀ e : Comp p.g,
      P e∈box (annih (f (e,true))) (annih (f (e,false))) := by simp [pureSpace,Submodule.mem_pi]
theorem deltaSpace_mem {b f : Plan p n} {j} (C : ChanOut p n) :
    C∈deltaSpace p f b j ↔ ∀ e : Place p,
      C e∈box (annih (hPin b (flipZ p e) j)) (annih (f e)) := by simp [deltaSpace,Submodule.mem_pi]

theorem solve_by_dual {f b : Plan p n} {C : ChanOut p n} {j : Bool}
    (G : Module.Dual F (Xpair p n))
    (h : ∀ x, orth p C f b j x → G x = 0) :
    ∃ D∈deltaSpace p f b j,∃ A∈ pureSpace p f,react p C (D,A) = G := by
  classical
  let S := ((deltaSpace p f b j).prod (pureSpace p f)).map (react p C)
  by_cases he : G∈S
  · obtain ⟨⟨D,A⟩,⟨h1,h2⟩,hh⟩ := he
    exact ⟨D,h1,A,h2,hh⟩
  obtain ⟨g,hg,hk⟩ := S.exists_le_ker_of_notMem he
  let x := (Module.evalEquiv F (Xpair p n)).symm g
  have ht (f : Module.Dual F (Xpair p n)) : f x=g f :=
    apply_evalEquiv_symm_apply ..
  have h1 : orth p C f b j x := by
    intro D hd A ha
    rw [ht]; exact hk (show react p C (D,A)∈S from ⟨_,⟨hd,ha⟩,rfl⟩)
  exact (hg ((ht G).symm.trans (h x h1))).elim

/-- Pure test annihilation vanishes in the factor quotients. -/
theorem orth_pure {f b : Plan p n} {x : Xpair p n} {C : ChanOut p n} {j}
    (h : orth p C f b j x) (e : Comp p.g) :
    vanish (f (e,true)) (f (e,false)) (purePair p n x e) := by
  classical
  intro y hy z hz
  let m : Mat (JointIdx p n) (JointIdx p n) := vecMulVec y z
  let a : PureForms p n := Pi.single e m
  have he : a∈pureSpace p f := by
    refine (pureSpace_mem _).mpr (fun i => ?_)
    by_cases h : i = e
    · subst i; rw [show a e=m from Pi.single_eq_same _ _]; exact outer_in_box _ _ hy hz
    simp [a,h]
  have hx := h 0 (Submodule.zero_mem _) a he
  change ∑ i, mpair ((chanDeriv p C 0+a) i) (purePair p n x i) = _ at hx
  have ha : chanDeriv p C 0=0 := by
    unfold chanDeriv chanInner; ext; simp
  rw [ha,zero_add,Finset.sum_eq_single e] at hx
  · rw [←mpair_outer,mpair_comm]
    rw [show a e=m from Pi.single_eq_same _ _] at hx
    exact hx
  · intro i _ h
    rw [show a i=0 from Pi.single_eq_of_ne h _,mpair_comm,map_zero]
  simp

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FrozenProjections
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frozen Projections -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset
open scoped BigOperators
variable {p : Shape} {n : ℕ}

variable {I : Type} [Fintype I]
namespace Volley
variable (v : Volley p n I)

theorem marked_mem (x : I) : v.sel x ∈ v.marked (v.obj x)  := by
  classical exact Finset.mem_image_of_mem _ (by simp [here])

theorem marked_card {w : I → Bool} (hv : v.bounded w) (i : Bool) :
    (v.marked i).card ≤14 := by
  classical exact Finset.card_image_le.trans (v.here_card hv i)

theorem visitH_here (t : Tagging p I) (i : Bool) (e : Comp p.g)
    {j : visits p t e} :
    j ∈ v.visitH t i e ↔ j.val ∈ v.here i := by simp [visitH,here]

theorem visitH_card {w : I → Bool} (hv : v.bounded w)
    (t : Tagging p I) (i : Bool) (e : Comp p.g) :
    (v.visitH t i e).card ≤14 := by
  classical
  rw [← Finset.card_image_of_injective _ (@Subtype.val_injective _ _)]
  refine (Finset.card_le_card ?_).trans (v.here_card hv i)
  rintro x hx
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
  exact (v.visitH_here ..).mp hj

theorem key_proj (t : Tagging p I) (i : Bool) (e : Comp p.g) (x : Vec (visits p t e)) :
    (IP p n i)ᵀ *ᵥ (v.keyM t e *ᵥ x)= ∑ j∈v.visitH t i e,x j • v.rayAt j.val := by
  classical
  have he : v.keyM t e *ᵥ x = ∑ j : visits p t e,x j • (v.rayLoc j.val) := by
    rw [mulVec_eq_sum]
    simp_rw [op_smul_eq_smul]
    rfl
  change ((IP p n i)ᵀ.mulVecLin _) = _
  rw [he,map_sum,visitH,Finset.sum_filter]
  refine sum_congr rfl fun j _ => ?_
  rw [map_smul,mulVecLin_apply,rayLoc,mulVec_mulVec]
  by_cases hj : v.obj j.val=i
  · rw [ite_eq_left hj,hj,IP_self,one_mulVec]
  rw [ite_eq_right hj,IP_cross (Ne.symm hj),zero_mulVec,smul_zero]

theorem key_here_dim {w : I→Bool} (hv : v.bounded w) (t : Tagging p I)
    (i : Bool) (z : Place p) :
    dim (sPin (v.keyPlan t) z i) ≤14 := by
  classical
  let S := v.visitH t i z.1
  let M : Mat (Row p n) S := Matrix.of fun i j => v.rayAt j.val.val i
  have hM : M.rank ≤14 := M.rank_le_card_width.trans
    (Fintype.card_coe S ▸ (v.visitH_card hv t i z.1))
  refine (Submodule.finrank_mono (show sPin (v.keyPlan t) z i ≤ colSp M from ?_)).trans hM
  rintro y ⟨x,⟨a,rfl⟩,rfl⟩
  let b (j:S) := a j.val
  refine ⟨b,?_⟩
  change M *ᵥ b=(IP p n i)ᵀ *ᵥ _
  rw [mulVecLin_apply,v.key_proj,mulVec_eq_sum]
  simp_rw [op_smul_eq_smul]
  change (∑ j:S,b j • v.rayAt j.val.val)=∑ j∈S,a j • v.rayAt j.val
  exact Finset.sum_coe_sort S (fun i => a i • v.rayAt i.val)

theorem key_dim {w : I→Bool} (hv : v.bounded w) (t : Tagging p I) (z : Place p) :
    dim (v.keyPlan t z) ≤28 := by
  classical
  exact (v.keyM t z.1).rank_le_card_width.trans ((Fintype.card_le_of_injective (@Subtype.val _ _) Subtype.val_injective).trans (v.call_count hv))

theorem sPin_frozen (a : Plan p n) (t : Tagging p I) (i : Bool) (z : Place p) :
    sPin (v.frozen a t) z i=sPin a z i⊔sPin (v.keyPlan t) z i :=
  Submodule.map_sup _ _ _

theorem hPin_frozen (a : Plan p n) (t : Tagging p I) (i : Bool) (z : Place p) :
    hPin (v.frozen a t) z i=hPin a z i := by
  have h : hPin (v.keyPlan t) z i≤(⊥ : Space _) := by
    rintro x ⟨y,hy,rfl⟩
    have he := primal_proj i ((keyPlane v t z) hy)
    rw [LinearMap.mem_ker] at he
    rw [he]; exact Submodule.zero_mem _
  change hPin (v.frozen a t) z i=hPin a z i
  rw [show hPin (v.frozen a t) z i=hPin a z i⊔ hPin (v.keyPlan t) z i from
    Submodule.map_sup _ _ _, le_bot_iff.mp h,sup_bot_eq]

theorem frozen_here_dim {w : I→ Bool} (hv : v.bounded w)
    (a : Plan p n) (t : Tagging p I) (i z) :
    dim (sPin (v.frozen a t) z i) ≤ planRank a + 14 := by
  rw [v.sPin_frozen]
  exact (Submodule.finrank_add_le_finrank_add_finrank ..).trans
    (Nat.add_le_add ((sPin_dim ..).trans (dim_le_plan ..)) (v.key_here_dim hv t i z))
end Volley

theorem ip_annih {f : Plan p n} (i : Bool) (z : Place p) (x : Ray p n) :
    IP p n i *ᵥ x∈annih (f z) ↔ x∈ annih (sPin f z i) := by
  rw [annih_mem,annih_mem]
  have hh (y : Dir p n) : dotProduct (IP p n i *ᵥ x) y= dotProduct x ((IP p n i)ᵀ *ᵥ y) := by
    rw [dotProduct_transpose_mulVec,dotProduct_comm]
  constructor
  · rintro he y ⟨y,hy,rfl⟩
    rw [mulVecLin_apply,← hh]
    exact he y hy
  intro h y hy
  rw [hh]
  exact h _ ⟨y,hy,rfl⟩

theorem orth_pair_sym (x : Xpair p n) (e : Comp p.g) (i : Bool) :
    ((x i).val e)ᵀ=(x i).val e := by
  obtain ⟨w,h,hx⟩ := mem_X.mp (x i).property
  rw [←hx]
  exact Wspace_sym ((Wspace p n).add_mem ((Wtag_le _) (h e.val.1)) ((Wtag_le _) (h e.val.2)))

theorem purePair_sym (x : Xpair p n) (e : Comp p.g) :
    (purePair p n x e)ᵀ = purePair p n x e := by
  simp only [purePair,Finset.sum_apply,Fintype.sum_bool,transpose_add,liftM_transpose,
    orth_pair_sym]

theorem pure_ip (x : Xpair p n) (e : Comp p.g) (i : Bool) (v : Ray p n) :
    purePair p n x e *ᵥ (IP p n i *ᵥ v)=IP p n i *ᵥ ((x i).val e *ᵥ v) := by
  classical
  simp only [purePair,Finset.sum_apply,Fintype.sum_bool,Matrix.add_mulVec,liftM_def,
    ← Matrix.mulVec_mulVec]
  cases i <;>
   (simp_rw [Matrix.mulVec_mulVec v (IP p n _)ᵀ]
    simp only [IP_self,IP_cross (show false≠true by decide),IP_cross (show true≠false by decide),
      Matrix.zero_mulVec, Matrix.one_mulVec,Matrix.mulVec_zero,zero_add,add_zero])

theorem vanish_one {f b : Plan p n} {x : Xpair p n} {C : ChanOut p n} {j}
    (h : orth p C f b j x) (i : Bool) (e : Comp p.g) :
    vanish (sPin f (e,true) i) (sPin f (e,false) i) ((x i).val e) := by
  intro u hu v hv
  have he := orth_pure h e (IP p n i *ᵥ u) ((ip_annih i _ u).mpr hu) (IP p n i *ᵥ v)
    ((ip_annih i _ v).mpr hv)
  rw [evmat,pure_ip, ← dotProduct_transpose_mulVec, mulVec_mulVec,
    IP_self, Matrix.one_mulVec,dotProduct_comm] at he
  exact he

/-- For an annihilator cut pair, testing a right or left primal
functional on endpoint i annihilating projected pins-and-keys produces
an entire vector in the opposite frozen space. -/
theorem orth_ip_frozen {f b : Plan p n} {x : Xpair p n} {C : ChanOut p n} {j}
    (h : orth p C f b j x) (i : Bool) (z : Place p) (φ : Ray p n)
    (hh : φ∈annih (sPin f (flipZ p z) i)) :
    IP p n i *ᵥ ((x i).val z.1 *ᵥ φ) ∈ f z := by
  rw [← pure_ip,← annih_annih (f z),annih_mem]
  intro ψ hψ
  have hr := (ip_annih i _ _).mpr hh
  rw [dotProduct_comm]
  rcases z with ⟨e,c|c⟩
  · have he := orth_pure h e _ hr _ hψ
    rw [← evmat_transpose,purePair_sym] at he
    exact he
  exact orth_pure h e _ hψ _ hr

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ResponseAnnihilators
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

private theorem protection_test {S : Space (Ray p n)} {q} {E L : Finset (Label p.b)}
    (h : protectedBy p S q E) {s} (hs : s∈L) (he : s∉E) (hl : L.card≤q)
    (ψ : Vec (AIdx p.g n)) :
    ∃ x ∈ annih S,∀ j∈L,(labMat p n j)ᵀ *ᵥ x= if j=s then ψ else 0 := by
  classical
  let P := S.subtype.coprod (labcomb p n L)
  let Q := dotL ψ ∘ₗ LinearMap.proj s ∘ₗ (LinearMap.snd F S (LabVals p n))
  obtain ⟨f,hf⟩ : ∃ f,f ∘ₗ P=Q := by
    refine HadwigerCounterexample.mem_range_comp (show LinearMap.ker P≤LinearMap.ker Q from ?_)
    rintro ⟨w,z⟩ hw
    change w.val + labcomb p n L z=0 at hw
    have hb : labcomb p n L z ∈ S := by
      rw [show labcomb p n L z=w.val from add_left_cancel (hw.trans (char_two w.val).symm)]
      exact w.property
    change dotProduct ψ (z s)=0
    rw [h L z hb hl s hs he,dotProduct_zero]
  obtain ⟨x,rfl⟩ := dotL_surj f
  refine ⟨x,?_,fun j hj => ?_⟩
  · rw [annih_mem]; intro y hy
    have hh := LinearMap.congr_fun hf (⟨y,hy⟩,0)
    change dotProduct x (y+labcomb p n L 0)=dotProduct ψ 0 at hh
    rw [map_zero,add_zero,dotProduct_zero] at hh
    exact hh
  have h1 (z : Vec (AIdx p.g n)) : dotProduct z ((labMat p n j)ᵀ *ᵥ x)=
      if j=s then dotProduct ψ z else 0 := by
    let y : LabVals p n := Pi.single j z
    have hh := LinearMap.congr_fun hf (0,y)
    change dotProduct x (0+labcomb p n L y)=dotProduct ψ (y s) at hh
    have hh' : labcomb p n L y = putLab p n j z := by
      rw [labcomb_eval,Finset.sum_eq_single j]
      · simp [y]
      · intro k _ hk; simp [y,Pi.single_eq_of_ne hk]
      simp [hj]
    rw [dotProduct_transpose_mulVec,labMat_act]
    rw [zero_add,hh'] at hh
    rw [hh]
    by_cases h : j = s
    · simp [y,h]
    simp [y,h]
  funext i
  have h2 := h1 (Pi.single i 1)
  by_cases hh : j = s
  · simpa only [hh,ite_true, if_true,dotProduct_single,single_dotProduct,mul_one,one_mul] using h2
  simpa only [ite_eq_right hh,Pi.zero_apply,single_dotProduct,one_mul] using h2

namespace Volley
variable {v : Volley p n I}

private theorem mark_test {w : I → Bool} (hb : v.bounded w)
    (t : Tagging p I) {a : Plan p n} {q} (hv : v.avoids a q)
    (j : I) (z : Place p) (L : Finset (Label p.b)) (hl : L.card+14 ≤ q)
    (ψ : Vec (AIdx p.g n))
    (hh : inc z.1 (t j) → dotProduct ψ (baseV (v.par j)) = 0) :
    ∃ x ∈ annih (sPin (v.frozen a t) z (v.obj j)),∀ k∈L,(labMat p n k)ᵀ *ᵥ x=
      if k=v.sel j then ψ else 0 := by
  classical
  let i := v.obj j
  obtain ⟨B,hB,hj,hc,hsel⟩ := hv i
  let T := L∪v.marked i
  have hT : T.card ≤ q :=
    (Finset.card_union_le _ _).trans ((Nat.add_le_add_left (v.marked_card hb i) L.card).trans hl)
  have hjj : j ∈ v.here i := by simp [here,i]
  obtain ⟨x,hx,hX⟩ := protection_test (L:=T) (hB z)
    (mem_union_right L (v.marked_mem j)) (hj _ hjj) hT ψ
  refine ⟨x, ?_, fun k hk => hX k (mem_union_left _ hk)⟩
  have he : sPin (v.frozen a t) z i ≤ LinearMap.ker (dotL x) := by
    rw [v.sPin_frozen]
    refine sup_le (fun y hy => (annih_mem ..).mp hx y hy) ?_
    rintro y ⟨y,⟨u,rfl⟩,rfl⟩
    rw [LinearMap.mem_ker]
    rw [mulVecLin_apply,mulVecLin_apply,v.key_proj,map_sum]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [map_smul]
    suffices h : dotL x (v.rayAt k.val)=0 by rw [h,smul_zero]
    change dotProduct x (point p (v.sel k.val) (v.par k.val))= _
    have hh' : k.val ∈ v.here i := (v.visitH_here ..).mp hk
    have hx' : v.sel k.val ∈ T := mem_union_right _ (Finset.mem_image_of_mem _ hh')
    rw [point,←labMat_act, ←dotProduct_transpose_mulVec,hX _ hx']
    by_cases h : v.sel k.val=v.sel j
    · have he' : k.val=j := hsel hh' hjj h
      rw [ite_eq_left h,dotProduct_comm,he']
      exact hh (he' ▸ k.property)
    rw [ite_eq_right h,dotProduct_zero]
  rw [annih_mem]
  exact fun y hy => he hy

private theorem ev_mput (s : Label p.b) (M : BaseMat p n) (x y : Ray p n) :
    evmat (mput p s M) x y = evmat M ((labMat p n s)ᵀ *ᵥ x) ((labMat p n s)ᵀ *ᵥ y) := by
  rw [← evmat_pull]
  unfold mput pullM
  rw [transpose_transpose]

/-- Diagnostic for the two quotients by one affine ray. -/
private theorem mark_diag {J : Type} [Fintype J] (Z : Mat (Option J) (Option J))
    (hZ : Zᵀ = Z) (hd : ∀ i,Z i i=Z none i) (v : Vec (Option J))
    (hv : v none=1) (he : ∀ φ, dotProduct φ v = 0 → ∀ ψ, dotProduct ψ v = 0 →
      evmat Z φ ψ=0) :
    Z = (Z none none) • vecMulVec v v := by
  classical
  let θ (i : Option J) := Pi.single i 1 + (Pi.single none (v i) : Vec (Option J))
  have hθ (i) : dotProduct (θ i) v=0 := by
    rw [show θ i=_+_ from rfl,add_dotProduct,single_dotProduct,single_dotProduct,
      hv,one_mul,mul_one,char_two]
  have hg (i j : Option J) :
      Z i j + Z i none * v j + (v i*(Z none j)+v i * (Z none none * v j)) = 0 := by

    have hh := he _ (hθ i) _ (hθ j)
    simp only [θ,evmat,Matrix.mulVec_add,add_dotProduct,dotProduct_add, single_dotProduct,Matrix.mulVec_single,op_smul_eq_smul, one_mul,one_smul,Pi.smul_apply,smul_eq_mul,col_apply] at hh
    simpa only [mul_comm,mul_left_comm,mul_assoc,add_comm,add_left_comm,add_assoc] using hh
  have hf i : Z i none=Z none i := congr_fun (congr_fun hZ none) i
  have h0 (i : Option J) : Z none i=Z none none * v i := by
    have h := hg i i
    rw [hd i,hf,mul_comm (Z none i),show v i*(Z none none*v i)=Z none none*v i from
      (by rw [mul_left_comm,bit_sq])] at h
    have h' : Z none i+Z none none*v i=0 := calc
      _ = Z none i + ((v i * Z none i+v i * Z none i)+Z none none*v i) := by rw [char_two,zero_add]
      _ = 0 := (by simpa only [add_assoc] using h)
    exact add_right_cancel (h'.trans (char_two _).symm)
  ext i j
  change Z i j=Z none none*(v i*v j)
  have h := hg i j
  rw [h0 j,char_two,add_zero,hf,h0, mul_assoc] at h
  exact add_right_cancel (h.trans (char_two _).symm)

set_option maxHeartbeats 600000 in
theorem mark_atom {w : I → Bool} (hb : v.bounded w)
    (t : Tagging p I) {a : Plan p n} {q} (hv : v.avoids a q)
    (j : I) (e : Comp p.g)
    (L : Finset (Label p.b)) (hl : L.card+14≤q)
    (Z : Label p.b → BaseMat p n)
    (ht : ∀ s,s∉L → Z s=0) (hh : ∀ s∈L,(Z s)ᵀ=Z s ∧ ∀ i,Z s i i=Z s none i)
    (hg : vanish (sPin (v.frozen a t) (e,true) (v.obj j))
      (sPin (v.frozen a t) (e,false) (v.obj j)) (labelSum p L Z)) :
    Z (v.sel j) = if inc e (t j) then
      Z (v.sel j) none none • vecMulVec (baseV (v.par j)) (baseV (v.par j)) else 0 := by
  classical
  let s := v.sel j
  change Z s = if inc e (t j) then _ else _
  by_cases hs : s∈L
  · let y := baseV (v.par j)
    have he (φ ψ : Vec (AIdx p.g n)) (hφ : inc e (t j) → dotProduct φ y=0)
        (hψ : inc e (t j) → dotProduct ψ y=0) :
        evmat (Z s) φ ψ=0 := by
      obtain ⟨x,hx,hX⟩ := mark_test hb t hv j (e,true) L hl φ hφ
      obtain ⟨y,hy,hY⟩ := mark_test hb t hv j (e,false) L hl ψ hψ
      have h := hg x hx y hy
      unfold labelSum at h
      rw [←mpair_outer,mpair_sum,Finset.sum_eq_single s] at h
      · rwa [mpair_outer,ev_mput,hX _ hs,hY _ hs,ite_eq_left rfl,ite_eq_left rfl] at h
      · intro i hi he; rw [mpair_outer,ev_mput,hX _ hi,hY _ hi,ite_eq_right he,ite_eq_right he]
        simp [evmat]
      simp [hs]
    by_cases h : inc e (t j)
    · rw [ite_eq_left h]
      exact mark_diag _ (hh s hs).1 (hh s hs).2 y rfl (fun φ hφ ψ hψ => he φ ψ (fun _ => hφ)
        (fun _ => hψ))
    rw [ite_eq_right h]
    apply evmat_ext
    intro φ ψ
    rw [he φ ψ (fun e => (h e).elim) (fun e => (h e).elim)]
    simp [evmat]
  change Z s = if inc e (t j) then Z s none none • _ else _
  rw [ht s hs]
  simp

end Volley
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AttackCutDecomposition
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Attack Cut Decomposition -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Submodule LinearMap Module Finset
open scoped BigOperators
variable {p : Shape} {n : ℕ}
variable {I J : Type} [Fintype I] [Fintype J]

theorem colSp_kill (S : Space (Vec I)) (M : Mat I J) :
    colSp M ≤ annih S ↔ ∀ x∈S,Mᵀ *ᵥ x=0 := by
  constructor
  · intro h x hx
    refine dot_ext_zero fun y => ?_
    rw [dotProduct_transpose_mulVec,dotProduct_comm]
    exact (annih_mem ..).mp (h ⟨y,rfl⟩) x hx
  rintro h z ⟨y,rfl⟩
  rw [annih_mem]; intro x hx
  rw [dotProduct_comm,mulVecLin_apply,←dotProduct_transpose_mulVec,h x hx,dotProduct_zero]

theorem box_kill {S : Space (Vec I)} {T : Space (Vec J)} {M : Mat I J} :
    M∈box (annih S) (annih T) ↔ (∀ x∈S,Mᵀ *ᵥ x=0) ∧ (∀ y ∈ T,M *ᵥ y=0) := by
  rw [box_mem,colSp_kill,colSp_kill,transpose_transpose]

theorem orth_sub {f b : Plan p n} {x y : Xpair p n} {C : ChanOut p n} {j}
    (hx : orth p C f b j x) (hy : orth p C f b j y) : orth p C f b j (x-y) := by
  intro D hd A ha; rw [map_sub,hx _ hd _ ha,hy _ hd _ ha,sub_self]

theorem orth_sum {f b : Plan p n} (x : I→Xpair p n) (c : I→F) {C : ChanOut p n} {j}
    (hx : ∀ i,orth p C f b j (x i)) : orth p C f b j (∑ i,c i • x i) := by
  intro D hd A ha
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul,hx i _ hd _ ha,smul_zero]

namespace Volley
variable (v : Volley p n I)

theorem strike_here (t : Tagging p I) (ht : v.legal t)
    (c : I → F) (i : Bool) :
    ((∑ j : I, c j • v.strike t ht j) i).val=∑ j∈v.here i,c j • v.atomAt t j := by
  classical
  rw [Finset.sum_apply]
  simp only [Submodule.coe_sum, Pi.smul_apply,Submodule.coe_smul,here,Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : v.obj j=i
  · simp only [ite_eq_left h]
    unfold strike
    rw [h,Pi.single_eq_same]
  simp [strike,h]

omit [Fintype I] in
theorem strike_pair (t : Tagging p I) (ht : v.legal t) (j : I) (e : Comp p.g) :
    purePair p n (v.strike t ht j) e=
    if inc e (t j) then vecMulVec (v.rayLoc j) (v.rayLoc j) else 0 := by
  classical
  simp only [purePair, Finset.sum_apply]
  rw [Finset.sum_eq_single (v.obj j)]
  · rw [strike,Pi.single_eq_same]
    change liftM _ _ (atom p _ _ _ e)=_
    rw [atom_def]; split
    · exact liftM_outer _ _ _ _
    rw [map_zero]
  · intro i _ hi; rw [strike,Pi.single_eq_of_ne hi]; exact map_zero _
  simp

theorem strike_orth {a b : Plan p n} {C : ChanOut p n} {i : Bool}
    (t : Tagging p I) (ht : v.legal t) (j : I) :
    orth p C (v.frozen a t) b i (v.strike t ht j) := by
  intro D hd A ha
  change ∑ e, _ = _
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [v.strike_pair]
  by_cases h : inc e (t j)
  · have hy (z) : v.rayLoc j ∈ (v.frozen a t (e,z)) :=
      Submodule.mem_sup_right (colSp_mem (P:=v.keyM t e) (⟨j,h⟩ : visits p t e))
    let V := v.rayLoc j
    have h1 : A e *ᵥ V=0 := (box_kill.mp ((pureSpace_mem _).mp ha e)).2 V (hy false)
    have h2 (z) : D (e,z) *ᵥ V=0 :=
      (box_kill.mp ((deltaSpace_mem _).mp hd _)).2 V (hy z)
    rw [ite_eq_left h,mpair_outer,evmat]
    change dotProduct V (((C (e,true))ᵀ * D (e,false)+
      (D (e,true))ᵀ * C (e,false)+A e) *ᵥ V)=_
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec,h1,h2,mulVec_zero,
      dotProduct_zero,zero_add,add_zero,dotProduct_transpose_mulVec]
  rw [ite_eq_right h,map_zero]
end Volley

private theorem struct_tri {M1 M2 M3 : Moment p n} {R : ℕ}
    {L1 L2 L3 : Finset (Label p.b)} {Z1 Z2 Z3 : Label p.b→BaseMat p n}
    (h1 : labStruct p n M1 R L1 Z1)
    (h2 : labStruct p n M2 R L2 Z2)
    (h3 : labStruct p n M3 R L3 Z3)
    (hr : 3*R≤p.j) (hm : M1+M2+M3=0) (s : Label p.b) :
    Z1 s+Z2 s+Z3 s=0 := by
  classical
  let W := L1∪L2∪L3
  have hs1 : L1⊆W := subset_trans subset_union_left subset_union_left
  have hs2 : L2⊆W := subset_trans subset_union_right subset_union_left
  have hs3 : L3⊆W := subset_union_right
  have hh : W.card ≤ p.j+1 :=
    (Finset.card_union_le (L1∪L2) L3).trans ((add_le_add
      ((Finset.card_union_le L1 L2).trans (add_le_add h1.2.1 h2.2.1)) h3.2.1).trans (by omega))
  by_cases hs : s∈W
  · have hv {M : Moment p n} {L Z} (h : labStruct p n M R L Z) (hL : L ⊆ W)
        (i j : AIdx p.g n) (r : SelIdx p.b p.j) :
        (∑ s∈W,Z s i j*monoBit s r.val) = M (r,i) (emptySel,j) := by
      rw [h.1,labelSum, Matrix.sum_apply,←Finset.sum_subset hL]
      · simp only [mput_apply,emptySel,monoBit,Finset.prod_empty,mul_one,mul_comm]
      intro y _ hy
      simp [h.2.2.1 y hy]
    ext i j
    refine selector_indep W (fun s => (Z1 s i j+Z2 s i j+Z3 s i j)) p.j hh ?_ s hs
    intro T hT
    let r : SelIdx p.b p.j := ⟨T,hT⟩
    simp only [add_mul,Finset.sum_add_distrib]
    rw [hv h1 hs1 i j r,hv h2 hs2 i j r,hv h3 hs3 i j r]
    exact congr_fun (congr_fun hm (r,i)) (emptySel,j)
  rw [h1.2.2.1 s (fun h => hs (hs1 h)), h2.2.2.1 s (fun h => hs (hs2 h)),
    h3.2.2.1 s (fun h => hs (hs3 h)), zero_add,zero_add]

namespace Volley
variable {v : Volley p n I}

private theorem orth_structure {x : Xpair p n} {a b : Plan p n}
    {C : ChanOut p n} {t : Tagging p I} {w : I→Bool} {j : Bool}
    (hb : v.bounded w) (ho : orth p C (v.frozen a t) b j x)
    (R : ℕ) (hr : 2*planRank a+28≤R) (hj : 6*R+4 ≤ p.j)
    (i : Bool) (e : Comp p.g) :
    ∃ L Z,labStruct p n ((x i).val e) R L Z := by
  classical
  have h (z) := v.frozen_here_dim hb a t i z
  have he : ((x i).val e).rank ≤ R :=
    (rank_vanish (vanish_one ho i e)).trans
      ((Nat.add_le_add (h (e,true)) (h (e,false))).trans (by omega))
  have hf : ((x i).val e)∈ Wspace p n := by
    obtain ⟨w,h,hx⟩ := mem_X.mp (x i).property
    rw [← hx]
    exact ((Wspace p n).add_mem ((Wtag_le _) (h e.val.1)) ((Wtag_le _) (h e.val.2)))
  obtain ⟨L,Z,hL,_,hZ,hA⟩ := label_support hf R hj he
  let g (s : Label p.b) := if s∈L then Z s else 0
  refine ⟨L,g,?_,hL,(fun s hs => ite_eq_right hs), fun s hs => ?_⟩
  · rw [hZ]
    exact Finset.sum_congr rfl fun s hs => by simp [g,hs]
  simp only [g,ite_eq_left hs]
  exact hA _ hs

private theorem edge_at (l : Tag p.g) (e : Comp p.g) (h : inc e l) :
    ∃ (k : Tag p.g) (h : l≠k),e = edge l k h := by
  rcases e with ⟨⟨i,j⟩,hj⟩
  change i=l∨j=l at h
  rcases h with rfl|rfl
  · exact ⟨j,hj.ne,(edge_eq hj).symm⟩
  exact ⟨i,hj.ne.symm, by rw [edge_symm,edge_eq hj]⟩

private theorem cut_tri {x : Profile p n} (hx : x∈Xspace p n)
    (l k j : Tag p.g) (h : l≠k) (h' : l ≠ j) (h'' : k≠j) :
    x (edge l k h)+x (edge l j h')+x (edge k j h'')=0 := by
  obtain ⟨w,hv,rfl⟩ := mem_X.mp hx
  rw [← getPair_edge l k h (cut p n w), ←getPair_edge l j h' (cut p n w), ←getPair_edge k j h'' (cut p n w),
    getPair_cut,getPair_cut,getPair_cut]
  have he (x y z : Moment p n) : x+y+(x+z)+(y+z)=0 := calc
    _ = (x+x)+(y+y)+(z+z) := by ac_rfl
    _ = _ := by simp only [char_two]
  exact he _ _ _

private theorem structure_mark {x : Xpair p n} {a b : Plan p n}
    {C : ChanOut p n} {t : Tagging p I} {w : I→Bool} {j : Bool}
    {q R : ℕ} (hb : v.bounded w) (ho : orth p C (v.frozen a t) b j x) (hv : v.avoids a q)
    (hr : 6*R+4≤p.j) (hq : R+14≤q)
    (l : I)
    {L : Comp p.g → Finset (Label p.b)} {Z : Comp p.g → Label p.b → BaseMat p n}
    (he : ∀ e,labStruct p n ((x (v.obj l)).val e) R (L e) (Z e)) :
    ∃ c : F, ∀ e,mput p (v.sel l) (Z e (v.sel l))=c • v.atomAt t l e := by
  classical
  let s := v.sel l
  let u := t l
  let M := vecMulVec (baseV (v.par l)) (baseV (v.par l))
  let coeff := fun e : Comp p.g => Z e s none none
  have h1 (e : Comp p.g) : Z e s= if inc e u then coeff e • M else 0 := by
    have ⟨hE,hL,hT,hH⟩ := he e
    exact mark_atom hb t hv l e _ (le_trans (Nat.add_le_add_right hL 14) hq)
      _ hT hH (hE ▸ vanish_one ho (v.obj l) e)
  have h2 (e f : Comp p.g) (h : inc e u) (h' : inc f u) :
      coeff e=coeff f := by
    by_cases hi : e=f
    · rw [hi]
    obtain ⟨k,hk,rfl⟩ := edge_at u e h
    obtain ⟨u2,hl,rfl⟩ := edge_at u f h'
    have hj : k ≠ u2 := by rintro rfl; exact hi rfl
    have hh := cut_tri (x (v.obj l)).property u k u2 hk hl hj
    have heq := struct_tri (he (edge u k hk)) (he (edge u u2 hl)) (he (edge k u2 hj))
      (by omega) hh s
    have hn : ¬ inc (edge k u2 hj) u := fun he => by
      rcases (inc_edge_iff _).mp he with h|h; exact hk h.symm; exact hl h.symm
    rw [h1 (edge k u2 hj), ite_eq_right hn,add_zero] at heq
    have h0 := congr_fun (congr_fun heq none) none
    change coeff _ + coeff _ = 0 at h0
    exact add_right_cancel (h0.trans (char_two _).symm)
  have h3 (e) : mput p s (Z e s)= coeff e • v.atomAt t l e := by
    rw [h1,atomAt,atom_def]
    by_cases hf : inc e u
    · rw [ite_eq_left hf,ite_eq_left hf,map_smul]
      change coeff e • liftM (labMat p n s) (labMat p n s) M=_
      unfold M
      rw [liftM_outer,labMat_act]; rfl
    rw [ite_eq_right hf,ite_eq_right hf,map_zero,smul_zero]
  by_cases hh : ∃ e,inc e u
  · obtain ⟨f,hf⟩ := hh
    refine ⟨coeff f,fun e => ?_⟩
    by_cases h : inc e u
    · exact (h3 e).trans (by rw [h2 e f h hf])
    refine (h3 e).trans ?_
    rw [atomAt,atom_def,ite_eq_right h,smul_zero,smul_zero]
  refine ⟨0,fun e => ?_⟩
  refine (h3 e).trans ?_
  rw [atomAt,atom_def,ite_eq_right (show ¬inc e u from fun he => hh ⟨e,he⟩),
    smul_zero,zero_smul]

theorem split_orth {x : Xpair p n} {a b : Plan p n}
    {C : ChanOut p n} {t : Tagging p I} {w : I→Bool} {j : Bool}
    {q R : ℕ} (hb : v.bounded w) (ht : v.legal t)
    (ho : orth p C (v.frozen a t) b j x) (hv : v.avoids a q)
    (hr : 6*R+4≤p.j) (hr' : 2*planRank a+28≤R) (hq : R+14≤q) :
    ∃ (c : I → F) (y : Xpair p n), x=y+∑ i,c i • v.strike t ht i ∧
      orth p C (v.frozen a t) b j y ∧ ∀ i e,v.clean i R ((y i).val e) := by
  classical
  choose L Z hZ using orth_structure hb ho R hr' hr
  choose c hc using fun l => structure_mark hb ho hv hr hq l (hZ (v.obj l))
  let A := ∑ i,c i • v.strike t ht i
  refine ⟨c,x-A,(sub_add_cancel x A).symm,orth_sub ho (orth_sum _ _ (v.strike_orth t ht)),
    fun i e => ?_⟩
  obtain ⟨B,h1,hA,hv',h3⟩ := hv i
  let T := v.marked i
  have he : (A i).val e=labelSum p T (Z i e) := by
    rw [show (A i).val=_ from v.strike_here t ht c i, Finset.sum_apply]
    dsimp only [labelSum,T,marked]
    rw [Finset.sum_image h3]
    refine Finset.sum_congr rfl fun l hl => ?_
    have he : v.obj l=i := (mem_filter.mp hl).2
    exact (he ▸ hc l e).symm
  let W := L i e
  refine ⟨W \ T,Z i e,?_,(Finset.card_le_card sdiff_subset).trans (hZ i e).2.1, ?_⟩
  · change (x i).val e-(A i).val e=_
    rw [(hZ i e).1,he]
    have hz : labelSum p W (Z i e)=labelSum p (W∪T) (Z i e) := by
      refine Finset.sum_subset subset_union_left fun s _ hs => ?_
      rw [(hZ i e).2.2.1 s hs,map_zero]
    rw [hz]
    have hS : (W∪T)=(W \ T) ∪ T := by ext i; simp
    rw [hS,labelSum,Finset.sum_union (show Disjoint (W \ T) T from Disjoint.symm disjoint_sdiff)]
    exact add_sub_cancel_right _ _
  exact Disjoint.symm disjoint_sdiff

end Volley
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

namespace Volley
variable {v : Volley p n I}

omit [Fintype I] in
private theorem B1_eval {s : Script p I} (t : Tagging p I) (m : Mixer p n)
    (ha : v.reads s m) {x y : I} (hg : x ≠ y) (hh : v.obj x=v.obj y) :
    B1 m (v.atomAt t x) (v.atomAt t y)=prescribedB p t s x y := by
  classical
  change ∑ i : Fin p.J, _ = _
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun e _ =>
    Finset.sum_congr rfl fun f _ => ?_
  by_cases he : inc e (t x)
  · by_cases hf : inc f (t y)
    · rw [ite_eq_left ⟨he,hf⟩,ha x y hg hh,ha x y hg hh]
      simp only [atomAt,atom_def,he,hf,ite_true, if_true,mom,liftM_outer,pair_outers]
      rfl
    rw [ite_eq_right (show ¬ (_ ∧ _) from fun h => hf h.2)]
    simp only [atomAt,atom_def,hf,ite_false, if_false,map_zero]
  rw [ite_eq_right (show ¬ (_ ∧ _) from fun h => he h.1)]
  simp only [atomAt,atom_def,he,ite_false, if_false]
  rw [mpair_comm,map_zero]

theorem grads_by_script (t : Tagging p I) (m : Mixer p n) (w : Volley p n I)
    (y : UnitType p n N) {d f : Vec I} {u : Mat I I} {s : Script p I}
    (h : fulfills p t d f u s v.obj w.obj) (hs : v.reads s m)
    (hd : ∀ x,role p n (v.atomAt t x)=d x)
    (hf : ∀ x,innerP p y (w.obj x) (w.atomAt t x)=f x)
    (hu : ∀ x y : I,T0 p n (v.atomAt t x) (v.atomAt t y)=u x y) :
    v.attackGrad w t m y := by
  classical
  intro x j
  rw [grad_val,hd,hf,sumAt,map_sum,LinearMap.sum_apply]
  rw [← h x j]; congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  unfold prescribedT
  split
  · rename_i he
    subst x
    rw [T_diag,hd]
  rename_i he
  have hx := (Finset.mem_filter.mp hi).2.1
  rw [Tsym_val,hu, B1_eval t m hs he hx,B1_eval t m hs (Ne.symm he) hx.symm]
end Volley

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CellPruning
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
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

theorem sum_pr_cells (w : Wgt (A × B)) (P : A × B → Prop) (f : A→I) (g : B→J) :
    ∑ i:I,∑ j:J,pr w (fun x => P x ∧ f x.1=i ∧ g x.2=j) = pr w P := by
  classical
  rw [← sum_pr_tag w P (fun x => (f x.1,g x.2)), Fintype.sum_prod_type]
  simp only [Prod.mk.injEq]

/-- restore the full pair-event probability in a specified cell. -/
theorem pair_restore (u : Wgt A) (v : Wgt B) (P : A → Prop) (Q : B → Prop)
    (hP : 0 < pr u P) (hQ : 0 < pr v Q)
    (c : A × B → Prop) :
    pr (pairW u v) (fun x => P x.1 ∧ Q x.2 ∧ c x)=
      pr u P * pr v Q * pr (pairW (onW u P) (onW v Q)) c := by
  classical
  let D := pr u P * pr v Q
  let d := pairW (onW u P) (onW v Q)
  change avg _ _ = D*avg d _
  unfold avg
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [pairW,d,onW_val,D,ind_and]
  field_simp

/-- heavy cells criterion. Loss charged to τ times opposite mass
rather than τ alone (key q fixed). -/
theorem prune_pairs (w : Wgt A) (v : Wgt B) (hw : SubLaw w) (hv : SubLaw v)
    (P : A → Prop) (Q : B→Prop) (f : A→I) (g : B→J)
    (C : A×B→Prop) (H T : ℝ) (hH : 0≤H) (hT : 0<T)
    {L : ℝ} (hi : (Fintype.card I : ℝ) ≤ L)
    (hj : (Fintype.card J : ℝ) ≤ L)
    (h : ∀ i j,T ≤ pr w (memberC P f i) → T ≤ pr v (memberC Q g j) →
      H≤ pr (pairW (onW w (memberC P f i)) (onW v (memberC Q g j))) C) :
    H * (pr w P * pr v Q) ≤ pr (pairW w v) (fun x => P x.1 ∧ Q x.2 ∧ C x) +
      (H*T*L)*(pr w P+pr v Q) := by
  classical
  let a (i:I) := pr w (memberC P f i)
  let b (i:J) := pr v (memberC Q g i)
  let d (i:I) (j:J) := pr (pairW w v) (fun x => memberC P f i x.1 ∧ memberC Q g j x.2 ∧ C x)
  have ha i : 0≤a i := pr_nonneg hw.nz
  have hb i : 0≤b i := pr_nonneg hv.nz
  have he i j : H*(a i*b j) ≤ d i j+ H*T*b j + H*T*a i := by
    have hz : 0≤ d i j := pr_nonneg (subLaw_pair hw hv).nz
    have ha' := mul_nonneg (mul_nonneg hH hT.le) (ha i)
    have hb' := mul_nonneg (mul_nonneg hH hT.le) (hb j)
    by_cases ht : T ≤ a i
    · by_cases hh : T ≤ b j
      · have hc := mul_le_mul_of_nonneg_right (h i j ht hh) (mul_nonneg (ha i) (hb j))
        have h1 := pair_restore w v _ _ (lt_of_lt_of_le hT ht) (lt_of_lt_of_le hT hh) C
        refine hc.trans ?_
        rw [mul_comm (pr _ C)]
        change _ ≤ d i j + _ + _
        unfold d
        rw [h1]
        change _ ≤ a i*b j * _ + _+_
        linarith
      · have hg := mul_le_mul_of_nonneg_left (le_of_not_ge hh) (mul_nonneg hH (ha i))
        calc H*(a i*b j) ≤ H*T*a i := by linarith only [hg]
             _ ≤ _ := by linarith only [hb',hz]
    have hg := mul_le_mul_of_nonneg_left (le_of_not_ge ht) (mul_nonneg hH (hb j))
    calc H*(a i*b j) ≤ H*T*b j := by linarith only [hg]
         _ ≤ _ := by linarith only [ha',hz]
  have hA : pr w P=∑ i,a i := (sum_pr_tag w P f).symm
  have hB : pr v Q=∑ j,b j := (sum_pr_tag v Q g).symm
  have hC :
      pr (pairW w v) (fun x => P x.1 ∧ Q x.2 ∧ C x) = ∑ i,∑ j,d i j := by
    rw [← sum_pr_cells (pairW w v) _ f g]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    unfold d; congr 1; unfold memberC; ext; tauto
  have h1 : H * (pr w P * pr v Q)=∑ i,∑ j,H*(a i*b j) := by
    rw [hA,hB]
    simp only [Finset.sum_mul,Finset.mul_sum]
    exact Finset.sum_comm;
  have h2 : ∑ i:I,∑ j:J,H*T*b j=(Fintype.card I:ℝ)*(H*T*pr v Q) := by
    simp only [← Finset.mul_sum,←hB,Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have h3 : ∑ i:I,∑ j:J,H*T*a i=(Fintype.card J:ℝ)*(H*T*pr w P) := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,←hA,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    ring
  rw [h1]
  refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => he i j).trans ?_
  simp only [Finset.sum_add_distrib]
  rw [h2,h3,← hC]
  have hh := mul_le_mul_of_nonneg_right hj (show 0≤H*T*pr w P from
    mul_nonneg (mul_nonneg hH hT.le) (pr_nonneg hw.nz))
  have hh' := mul_le_mul_of_nonneg_right hi (show 0≤H*T*pr v Q from
    mul_nonneg (mul_nonneg hH hT.le) (pr_nonneg hv.nz))
  linarith only [hh,hh']

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ResidualCutPairs
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Residual Cut Pairs -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix LinearMap Submodule Module Finset
variable {p : Shape} {n : ℕ} {I : Type} [Fintype I]
namespace Volley

variable {v : Volley p n I}
private theorem clean_apply {i : Bool} {R : ℕ} {M : Moment p n} (h : v.clean i R M) (x : Ray p n) :
    v.CleanRay i R (M *ᵥ x) := by
  classical
  obtain ⟨L,Z,rfl,hL,ht⟩ := h
  refine ⟨L,(fun s => Z s *ᵥ ((labMat p n s)ᵀ *ᵥ x)),?_,hL,ht⟩
  rw [labcomb_eval,labelSum,Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mput,liftM_def,←Matrix.mulVec_mulVec]
  rw [labMat_act]

private theorem clean_zero (v : Volley p n I) (i : Bool) (R : ℕ) :
    v.CleanRay i R 0 :=
  ⟨∅,0,(map_zero _).symm,by simp,by simp⟩

/-- Key coefficients cannot contribute to a short nonattack primal
combination even if only the primal projection is specified. -/
private theorem clean_proj {w : I → Bool} {a : Plan p n} (t : Tagging p I) {R q : ℕ}
    (hb : v.bounded w) (hv : v.avoids a q) (hr : R+14 ≤ q)
    (x : Ray p n) (z : Place p) (i : Bool) (hx : v.CleanRay i R x)
    (b : Vec (visits p t z.1)) (he : x-(IP p n i)ᵀ *ᵥ (v.keyM t z.1 *ᵥ b) ∈ sPin a z i) :
    ∀ j∈v.visitH t i z.1,b j = 0 := by
  classical
  let K := v.visitH t i z.1
  obtain ⟨B,hB,hE,hG,hsel⟩ := hv i
  obtain ⟨L,u,hx,hL,hdis⟩ := hx
  let s (j : visits p t z.1) := v.sel j.val
  let T := K.image s
  have hk (i' : visits p t z.1) (h : i'∈K) : i'.val∈v.here i :=
    (v.visitH_here ..).mp h
  have hs : Set.InjOn s (K : Set _) := by
    intro x hx y hy h
    exact Subtype.ext (hsel (hk _ hx) (hk _ hy) h)
  obtain ⟨y,hy,hZ⟩ := point_comb K s (v.par ∘ Subtype.val) b hs
  rw [key_proj] at he
  let r : LabVals p n := withinL p L u - withinL p T y
  have h : labcomb p n (L∪T) r∈sPin a z i := by
    rw [show r =_ - _ from rfl,map_sub,← within_eq subset_union_left u,
      ← within_eq subset_union_right y,← hx, show labcomb p n T y =_ from hZ.symm]
    exact he
  have hh : (L∪T).card≤q :=
     (Finset.card_union_le ..).trans ((Nat.add_le_add hL (Finset.card_image_le.trans
       (v.visitH_card hb t i z.1))).trans hr)
  intro j hj
  have hj' : s j ∈ T := mem_image_of_mem s hj
  have hj'' : s j ∉ L := fun hh => Finset.disjoint_left.mp hdis hh
    (mem_image_of_mem _ (hk j hj))
  have hy' := hB z (L∪T) r h hh _ (mem_union_right _ hj') (hE _ (hk _ hj))
  unfold r withinL at hy'
  simp only [Pi.sub_apply,ite_eq_right hj'',ite_eq_left hj',hy j hj,zero_sub,neg_eq_zero] at hy'
  simpa only [Function.comp_apply,Pi.zero_apply,Pi.smul_apply,smul_eq_mul,baseV,
    Option.elim',mul_one] using congr_fun hy' none

private theorem clean_sPin {w : I → Bool} {a : Plan p n} (t : Tagging p I) {R q : ℕ}
    (hb : v.bounded w) (hv : v.avoids a q) (hr : R+14 ≤ q)
    (x : Ray p n) (z : Place p) (i : Bool) (hx : v.CleanRay i R x)
    (hg : x∈sPin (v.frozen a t) z i) :
    x∈sPin a z i := by
  classical
  rw [sPin_frozen,Submodule.mem_sup] at hg
  obtain ⟨y,hy,q',⟨q',⟨b,rfl⟩,rfl⟩,hX⟩ := hg
  have he : x - ((IP p n i)ᵀ *ᵥ (v.keyM t z.1 *ᵥ b))=y := by
    rw [← hX]; exact add_sub_cancel_right _ _
  have h := clean_proj t hb hv hr x z i hx b (he ▸ hy)
  rw [key_proj,Finset.sum_eq_zero (fun j hj => by rw [h j hj,zero_smul]),sub_zero] at he
  rwa [he]

private theorem clean_Pin {w : I→Bool} {a : Plan p n} (t : Tagging p I)
    {R q : ℕ} (hb : v.bounded w) (hv : v.avoids a q) (hr : R+14 ≤ q)
    (x : Ray p n) (z : Place p) (i : Bool) (hx : v.CleanRay i R x)
    (hg : IP p n i *ᵥ x ∈ v.frozen a t z) :
    IP p n i *ᵥ x∈a z := by
  classical
  obtain ⟨d,hd,q',⟨b,rfl⟩,hX⟩ := Submodule.mem_sup.mp
    (show IP p n i *ᵥ x∈a z ⊔ v.keyPlan t z from hg)
  let f (k : Bool) := (IP p n k)ᵀ
  have hzero : b=0 := by
    funext j
    let k := v.obj j.val
    let x' := f k *ᵥ (IP p n i *ᵥ x)
    have h : x' - ((IP p n k)ᵀ *ᵥ (v.keyM t z.1 *ᵥ b))∈sPin a z k := by
      unfold x'
      rw [← hX,Matrix.mulVec_add]
      change f k *ᵥ d + _ - f k *ᵥ (_ *ᵥ _) ∈ _
      rw [mulVecLin_apply,add_sub_cancel_right]
      exact ⟨d,hd,rfl⟩
    have h' : v.CleanRay k R x' := by
      unfold x' f; rw [Matrix.mulVec_mulVec]
      by_cases h : k=i
      · rw [h,IP_self,Matrix.one_mulVec]
        exact hx
      rw [IP_cross h,Matrix.zero_mulVec]; exact clean_zero v k R
    exact clean_proj t hb hv hr x' z k h' b h j (mem_filter.mpr ⟨mem_univ _,rfl⟩)
  rw [hzero,map_zero,add_zero] at hX
  rwa [← hX]

end Volley

theorem orth_delta_probe {f b : Plan p n} {x : Xpair p n} {C : ChanOut p n} {j}
    (h : orth p C f b j x) (i : Bool) (z : Place p) (φ : Ray p n)
    (hφ : φ∈annih (sPin f (flipZ p z) i)) :
    C z *ᵥ (IP p n i *ᵥ ((x i).val z.1 *ᵥ φ)) ∈ hPin b z j := by
  classical
  rw [← annih_annih (hPin b z j), annih_mem]
  intro y hy
  rw [← pure_ip]
  let Q := IP p n i *ᵥ φ
  have hQ := (ip_annih ..).mpr hφ
  let D : ChanOut p n := Pi.single (flipZ p z) (vecMulVec y Q)
  have hD : D∈deltaSpace p f b j := by
    refine (deltaSpace_mem _).mpr (fun z' => ?_)
    by_cases hz : z'=flipZ p z
    · subst z'
      unfold D; rw [Pi.single_eq_same,flipZ_flip]
      exact outer_in_box y Q hy hQ
    simp [D,hz]
  have hg := h D hD 0 (Submodule.zero_mem _)
  change ∑ i, mpair ((chanDeriv p C D+0) i) (purePair p n x i) = _ at hg
  rw [add_zero,Finset.sum_eq_single z.1] at hg
  · let T := (C z)ᵀ * vecMulVec y Q
    let X := purePair p n x z.1
    have hh : mpair T X = dotProduct (C z *ᵥ (X *ᵥ Q)) y := by
      unfold T; rw [mul_vecMulVec,mpair_comm,mpair_outer,evmat]
      rw [dotProduct_comm, dotProduct_transpose_mulVec,dotProduct_comm]
    change dotProduct (C z *ᵥ (X *ᵥ Q)) y = _
    rw [← hh]
    have hZ : z≠flipZ p z := by cases z with | mk e c => cases c <;> simp [flipZ]
    have h1 : D z=0 := Pi.single_eq_of_ne hZ _
    have h2 : D (flipZ p z)=vecMulVec y Q := Pi.single_eq_same _ _
    rcases z with ⟨e,c|c⟩
    · change mpair ((C (e,true))ᵀ * D (e,false)+(D (e,true))ᵀ * C (e,false)) X=0 at hg
      change D (e,true)=_ at h2
      rw [h1,h2,Matrix.mul_zero,zero_add,transpose_vecMulVec,vecMulVec_mul] at hg
      unfold T; rw [mul_vecMulVec, Matrix.mulVec_transpose,mpair_comm,mpair_outer,
        ←evmat_transpose, show Xᵀ=X from purePair_sym x e]
      rw [mpair_comm,mpair_outer] at hg
      exact hg
    change mpair ((C (e,true))ᵀ * D (e,false)+(D (e,true))ᵀ * C (e,false)) X=0 at hg
    change D (e,false)=_ at h2
    rw [h1,Matrix.transpose_zero,Matrix.zero_mul,add_zero,h2] at hg
    exact hg
  · intro k _ hk
    have h1 (i : Bool) : D (k,i)=0 := Pi.single_eq_of_ne (show (_,_)≠flipZ p z from
      fun hh => hk (congrArg Prod.fst hh)) _
    simp only [chanDeriv,chanInner,Pi.add_apply,h1,Matrix.transpose_zero,Matrix.mul_zero,
      Matrix.zero_mul,zero_add]
    rw [mpair_comm,map_zero]
  simp

namespace Volley
variable {v : Volley p n I}
theorem clean_effective {w : I→Bool} {a b : Plan p n} (t : Tagging p I)
    {q R : ℕ} (hb : v.bounded w) (hv : v.avoids a q) (hr : R+14≤q)
    {j : Bool} (M : Cross p n) (x : Xpair p n)
    (hh : orth p (channelOut p M j) (v.frozen a t) b j x)
    (hg : tableInj a b M) (i : Bool) (hx : ∀ e,v.clean i R ((x i).val e)) :
    (x i).val∈effective a i := by
  classical
  refine effective_mem.mpr ⟨(x i).property,fun e => ?_⟩
  let A := (x i).val e
  let S (z) := sPin (v.frozen a t) (e,z) i
  have hd (c : Bool) (φ : Ray p n) (hφ : φ∈annih (S (!c))) : A *ᵥ φ=0 := by
    have hray := clean_apply (hx e) φ
    have hm := orth_ip_frozen hh i (e,c) φ hφ
    exact hg (e,c) i j (A *ᵥ φ) (clean_Pin t hb hv hr _ _ i hray hm)
      (orth_delta_probe hh i (e,c) φ hφ)
  have hsym : Aᵀ=A := orth_pair_sym x e i
  have h (c : Bool) : colSp A ≤ sPin a (e,c) i := by
    have hh' : colSp A ≤ S c := by
      have hf : colSp A ≤ annih (annih (S c)) := (colSp_kill ..).mpr (fun φ hφ => by
        rw [hsym]
        exact hd (!c) φ (by simpa using hφ))
      rwa [annih_annih] at hf
    rintro x' ⟨y,rfl⟩
    exact clean_sPin t hb hv hr _ _ i (clean_apply (hx e) y) (hh' ⟨y,rfl⟩)
  change A∈box _ _
  rw [box_mem,hsym]
  exact ⟨h _,h _⟩

end Volley
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ResponseSolvability
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Response Solvability -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Finset Submodule
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I]

theorem combineF_val (f : OnForms p n) (x : Xpair p n) :
    combineF p f x= ∑ i, f i (x i).val := by
  simp only [combineF,LinearMap.coe_mk,AddHom.coe_mk,LinearMap.sum_apply]; rfl

theorem combineF_single (f : OnForms p n) (i : Bool) (x : Xspace p n) :
    combineF p f (Pi.single i x)=f i x.val := by
  rw [combineF_val,Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj; simp [hj]
  simp

theorem combineF_same (f g : OnForms p n) : combineF p f=combineF p g ↔
    ∀ i,∀ x ∈ Xspace p n,f i x=g i x := by
  constructor
  · intro h i x hx
    exact (combineF_single f i ⟨x,hx⟩).symm.trans (h ▸ combineF_single g i ⟨x,hx⟩)
  intro h
  apply LinearMap.ext; intro x
  rw [combineF_val,combineF_val]
  exact Finset.sum_congr rfl fun i _ => h i _ (x i).property

theorem obsPair_val (A : PureForms p n) (x : Xpair p n) :
    obsPair p A x=∑ i,mpair (A i) (purePair p n x i) := by
  change ∑ i : Comp p.g, _ = _
  refine Finset.sum_congr rfl fun i _ => ?_
  change mpair ((chanDeriv p (n:=n) 0 0+A) _) _=_
  simp only [chanDeriv,chanInner,Pi.add_apply,Pi.zero_apply,Matrix.transpose_zero,Matrix.zero_mul,
    zero_add]

theorem each_sumF (A : Individual p n) : eachF p (sumF p A)=A := by
  classical
  funext i e
  change pullM _ _ (∑ j,_) = _
  rw [map_sum,Finset.sum_eq_single i]
  · unfold pullM; rw [liftM_comp,IP_self]
    simp [liftM_def]
  · intro j _ hj
    unfold pullM
    rw [liftM_comp,IP_cross (Ne.symm hj)]
    simp [liftM_def]
  simp

theorem obsPair_each (P : PureForms p n) :
    obsPair p P=combineF p (repF p (eachF p P)) := by
  apply LinearMap.ext
  intro x
  rw [obsPair_val,combineF_val]
  simp_rw [purePair,Finset.sum_apply,map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [repF_rep]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mpair_liftM]; rfl

theorem obsPair_chan (B : Cross p n) (j : Bool) :
    obsPair p (chanInner p (channelOut p B j) (channelOut p B j))=
    combineF p (fun i => contract p B i j) := by
  apply LinearMap.ext; intro x
  rw [obsPair_val,combineF_val]
  simp_rw [purePair,Finset.sum_apply,map_sum]
  rw [Finset.sum_comm]; rfl

theorem each_chan_val (B C : ChanOut p n) (i) (e : Comp p.g) :
    eachF p (chanInner p B C) i e=(B (e,true) * IP p n i)ᵀ * (C (e,false)*IP p n i) := by
  change pullM _ _ _=_
  simp only [pullM_def,chanInner,transpose_mul,Matrix.mul_assoc]

theorem obsPair_chan_change (B C : ChanOut p n) :
    obsPair p (chanInner p (B+C) (B+C))=
    obsPair p (chanInner p B B)+ obsPair p (chanDeriv p B C) + obsPair p (chanInner p C C) := by
  rw [←map_add,←map_add]
  congr 1
  unfold chanInner chanDeriv
  funext i
  simp only [chanInner,Pi.add_apply,Matrix.transpose_add,Matrix.add_mul,Matrix.mul_add,add_assoc]
  ac_rfl

theorem react_obsPair (B C : ChanOut p n) (D : PureForms p n) :
    react p B (C,D)=obsPair p (chanDeriv p B C) + obsPair p D := by
  rw [←map_add]
  exact LinearMap.ext (fun x => (obsPair_val _ x).symm)

namespace Volley
variable (v w : Volley p n I)

theorem realize_linear {t : Tagging p I} (m : Mixer p n)
    (x y : UnitType p n N) (a b : Plan p n) (t' B : Cross p n)
    (hb : v.bounded w.obj) (ht : v.legal t)
    (q R : ℕ) (hv : v.avoids a q) (hj : 6*R+4≤p.j)
    (hr : 2*planRank a+28≤R) (hq : R+14≤q)
    (hB : fitsTable a b B t') (hT : tableInj a b t')
    (hf : rowAgree (v.frozen a t) B (actual p x y))
    (hR : v.scalarRecipe w t m x a t') (hk : v.keys t x=w.keys t y)
    (hL : ∀ i, frameLaw m (onSide y i))
    (hS : v.attackGrad w t m y) (j : Bool) :
    ∃ C∈deltaSpace p (v.frozen a t) b j,
    ∃ P∈pureSpace p (v.frozen a t),
      obsPair p (chanInner p (channelOut p B j) (channelOut p B j))+
      obsPair p (chanDeriv p (channelOut p B j) C) + obsPair p P=
        combineF p (v.demand w t m j) := by
  classical
  let G := v.demand w t m j
  let K : OnForms p n := fun i => contract p B i j
  let CC := channelOut p B j
  have h1 (i : I) : G (v.obj i) (v.atomAt t i) = K (v.obj i) (v.atomAt t i) := by
    change grad m (v.sumAt t w.obj (v.obj i) j) _ = contract p B _ _ _
    rw [frozen_contract_key v t hf,contract_actual,LinearMap.comp_apply,hS i j,
      v.atom_share w t x y hk]
    by_cases h : j=w.obj i
    · rw [ite_eq_left h,h,ufun_self (hL _)]
    have hh : (! (w.obj i))=j := by cases j <;> cases e : w.obj i <;> simp_all
    rw [ite_eq_right h, innerP, hh]; rfl
  have hg (z : Xpair p n) (h : orth p CC (v.frozen a t) b j z) :
      combineF p (G-K) z=0 := by
    obtain ⟨c,z,rfl,ho,hy⟩ := split_orth hb ht h hv hj hr hq
    have he (i : Bool) := clean_effective t hb hv hq B z ho (fits_inj hB hT) i (hy i)
    rw [map_add,map_sum]
    have h2 : combineF p (G-K) z = 0 := by
      rw [combineF_val]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Pi.sub_apply,LinearMap.sub_apply]
      exact sub_eq_zero.mpr ((hR.gradient i j _ (he i)).trans (fits_contract hB i j _ (he i)).symm)
    rw [h2,zero_add]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul,strike,combineF_single,Pi.sub_apply,LinearMap.sub_apply,
      h1 i,sub_self,smul_zero]

  obtain ⟨C,hC,P,hP,h⟩ := solve_by_dual _ hg
  rw [react_obsPair,map_sub] at h
  rw [obsPair_chan]
  refine ⟨C,hC,P,hP,?_⟩
  rw [add_assoc,h,add_sub_cancel]
end Volley

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_DerivativeCompression
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derivative Compression -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
variable {I J : Type} [Fintype I] [Fintype J]

theorem mat_mul_fix {A : Mat I I} {B : Mat I J} (h : ∀ x∈colSp B,A *ᵥ x=x) :
    A*B=B := by
  apply coe_mv_inj
  refine LinearMap.ext fun x => ?_
  change _ *ᵥ x=_ *ᵥ _
  rw [← Matrix.mulVec_mulVec]; exact h (B *ᵥ x) ⟨x,rfl⟩

/-- Endomorphism taking V into V, preserving dot product against S,
of rank bounded by the observer space S. -/
private theorem compress_observer (V S : Space (Vec I)) :
    ∃ A : Mat I I,(∀ v∈V,A *ᵥ v∈V) ∧
      (∀ v∈V,∀ y∈S, dotProduct y (A *ᵥ v) = dotProduct y v) ∧
      A.rank≤dim S := by
  classical
  obtain ⟨Q,hQ⟩ := mat_left_inv (pack_inj V)
  let P := (pack S)ᵀ * pack V
  obtain ⟨B,hB⟩ := proj_exists (colSp Pᵀ) ⊥ disjoint_bot_right
  let A := pack V * Bᵀ * Q
  have hh (t) : A *ᵥ (pack V *ᵥ t)=pack V *ᵥ (Bᵀ *ᵥ t) := by
    simp only [A,← Matrix.mulVec_mulVec]
    rw [Matrix.mulVec_mulVec t Q,hQ, Matrix.one_mulVec]
  refine ⟨A,fun x hx => ?_,fun x hx y hy => ?_,?_⟩
  · obtain ⟨t,rfl⟩ := (pack_mem_iff x _).mp hx
    rw [hh]
    exact (pack_mem_iff ..).mpr ⟨_,rfl⟩
  · obtain ⟨t,rfl⟩ := (pack_mem_iff x _).mp hx
    obtain ⟨u,rfl⟩ := (pack_mem_iff y _).mp hy
    rw [hh]
    have he : P * Bᵀ=P := by
      have h1 := congrArg Matrix.transpose (mat_mul_fix (A:=B) hB.fixes)
      simpa only [transpose_mul,transpose_transpose] using h1
    have hg (t') : dotProduct (pack S *ᵥ u) (pack V *ᵥ t')=dotProduct u (P *ᵥ t') := by
      rw [show P=_*_ from rfl,← Matrix.mulVec_mulVec,dotProduct_transpose_mulVec,dotProduct_comm]
    rw [hg,hg,Matrix.mulVec_mulVec,he]
  · refine ((Matrix.rank_mul_le_left ..).trans (Matrix.rank_mul_le_right ..)).trans ?_
    rw [Matrix.rank_transpose]
    exact (rank_maps (colSp Pᵀ) hB.onto).trans (by
      rw [colSp_dim,Matrix.rank_transpose]
      exact P.rank_le_card_height.trans_eq (Fintype.card_fin _))

variable {p : Shape} {n : ℕ}

theorem le_priOut (C : ChanOut p n) (z : Place p) (i) :
    colSp (C z * IP p n i)≤priOut p C z := by
  cases i; exact le_sup_right; exact le_sup_left
theorem dim_priOut {C : ChanOut p n} {H} (h : outSmall H C) (z : Place p) :
    dim (priOut p C z) ≤2*H := by
  rw [two_mul]
  exact (Submodule.finrank_add_le_finrank_add_finrank ..).trans (Nat.add_le_add (h z true) (h z false))

theorem outSmall_low {B : Cross p n} {H} (h : lowCross H B) (j : Bool) :
    outSmall H (channelOut p B j) := by
  intro z i
  rw [channelOut, Matrix.transpose_mul,Matrix.mul_assoc]
  exact (Matrix.rank_mul_le_right ..).trans (h z i)

theorem ev_duom {K : Type} [Fintype K] (P : Mat K I) (Q : Mat K J) (v : Vec I)
    (w : Vec J) :
    evmat (Pᵀ*Q) v w = dotProduct (P *ᵥ v) (Q *ᵥ w) := by
  rw [evmat,← Matrix.mulVec_mulVec,dotProduct_transpose_mulVec,dotProduct_comm]

theorem deriv_compress {C D : ChanOut p n} {f b : Plan p n} {j : Bool} {H}
    (h : outSmall H C) (hd : D∈deltaSpace p f b j) :
    ∃ B∈deltaSpace p f b j,(∀ z,(B z).rank ≤2*H) ∧
      obsPair p (chanDeriv p C D)=obsPair p (chanDeriv p C B) := by
  classical
  let S (z) := priOut p C (flipZ p z)
  let V (z) := annih (hPin b (flipZ p z) j)
  choose A hA hS hT using fun z => compress_observer (V z) (S z)
  let B := fun z : Place p => A z * D z
  have he z : colSp (D z) ≤ V z ∧ colSp (D z)ᵀ≤ annih (f z) :=
    (box_mem ..).mp ((deltaSpace_mem _).mp hd z)
  refine ⟨B,(deltaSpace_mem _).mpr ?_,fun z => ?_,?_⟩
  · intro z
    rw [box_mem]
    constructor
    · rintro x ⟨y,rfl⟩
      rw [mulVecLin_apply]
      unfold B; rw [← mulVec_mulVec]
      exact hA z _ ((he z).1 ⟨y,rfl⟩)
    · rw [colSp_kill,transpose_transpose]
      intro x hx
      have h1 : D z *ᵥ x=0 := (box_kill.mp ((deltaSpace_mem _).mp hd z)).2 _ hx
      rw [show B z=A z * D z from rfl,←mulVec_mulVec,h1,Matrix.mulVec_zero]
  · exact (Matrix.rank_mul_le_left ..).trans ((hT z).trans (dim_priOut h (flipZ p z)))
  · rw [obsPair_each,obsPair_each]
    have hE (z : Place p) (i l : Bool) (x y : Ray p n) :
        dotProduct ((C (flipZ p z) * IP p n i) *ᵥ x) ((B z * IP p n l) *ᵥ y)=
        dotProduct ((C (flipZ p z) * IP p n i) *ᵥ x) ((D z * IP p n l) *ᵥ y) := by
      let u := (C (flipZ p z)* IP p n i)*ᵥ x
      have hu : u∈S z := le_priOut _ _ _ ⟨x,rfl⟩
      let v := D z *ᵥ (IP p n l *ᵥ y)
      have hv : v∈V z := (he z).1 ⟨_,rfl⟩
      unfold B
      unfold u at hu
      rw [← Matrix.mulVec_mulVec] at hu
      simp only [← Matrix.mulVec_mulVec]
      exact hS z _ hv _ hu
    have h1 : eachF p (chanInner p C B)=eachF p (chanInner p C D) := by
      funext i e
      rw [each_chan_val, each_chan_val]
      refine evmat_ext fun x y => ?_
      rw [ev_duom, ev_duom]
      exact hE (e,false) i i x y
    have h2 : eachF p (chanInner p B C)=eachF p (chanInner p D C) := by
      funext i e
      rw [each_chan_val,each_chan_val]
      refine evmat_ext fun x y => ?_
      rw [ev_duom,ev_duom,dotProduct_comm,dotProduct_comm ((D _ * IP p n i) *ᵥ x)]
      exact hE (e,true) i i y x
    rw [chanDeriv,chanDeriv,map_add,map_add,h1,h2]

theorem chanInner_pure {C D : ChanOut p n} {f b : Plan p n} {j : Bool}
    (h : C∈deltaSpace p f b j) (h' : D∈deltaSpace p f b j) :
    chanInner p C D∈pureSpace p f := by
  classical
  refine (pureSpace_mem _).mpr (fun e => ?_)
  have h1 : ∀ x ∈ f (e,true), C (e,true) *ᵥ x=0 :=
    (box_kill.mp ((deltaSpace_mem _).mp h _)).2
  have h2 : ∀ x ∈ f (e,false), D (e,false) *ᵥ x=0 :=
    (box_kill.mp ((deltaSpace_mem _).mp h' _)).2
  rw [box_kill]
  constructor
  · intro x hx
    unfold chanInner
    rw [Matrix.transpose_mul,Matrix.transpose_transpose,←mulVec_mulVec,h1 x hx,mulVec_zero]
  intro x hx
  unfold chanInner; rw [←mulVec_mulVec,h2 x hx,mulVec_zero]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RankEfficientDecomposition
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rank Efficient Decomposition -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n : ℕ} {I : Type} [Fintype I]

theorem obsI_each (P : PureForms p n) :
    obsI p (eachF p P)=obsPair p P :=
  (obsPair_each P).symm

private theorem mrk_sub {I J : Type} [Fintype I] [Fintype J] (A B : Mat I J) :
    (A-B).rank ≤ A.rank+B.rank := by rw [ZModModule.sub_eq_add]; exact mrk_add_le A B

theorem primary_initial (M : Individual p n) (f : Plan p n) (H R : ℕ)
    (hF : ∀ z i,dim (sPin f z i) ≤ H) (hR : ∀ i e, (M i e).rank≤R) :
    ∃ P∈pureSpace p f, (∀ e,(P e).rank ≤ 2*R) ∧
      (∀ i e, ((M-eachF p P) i e).rank≤2*H) := by
  classical
  let S := sPin f
  choose A hA using fun z i => proj_exists (S z i) ⊥ disjoint_bot_right
  let B (z i) := 1-A z i
  let T : Individual p n := fun i e => pullM (B (e,true) i) (B (e,false) i) (M i e)
  refine ⟨sumF p T,?_,fun e => ?_, fun i e => ?_⟩
  · refine (pureSpace_mem _).mpr fun e => ?_
    apply Submodule.sum_mem
    intro i _
    let P z := B (e,z) i * (IP p n i)ᵀ
    have he (z : Bool) (x : Dir p n) (hx : x∈f (e,z)) : P z *ᵥ x=0 := by
      unfold P B
      let y := (IP p n i)ᵀ *ᵥ x
      have hh : y∈ S (e,z) i := ⟨_,hx,rfl⟩
      rw [←Matrix.mulVec_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec]
      change y - A (e,z) i *ᵥ y=0
      rw [(hA _ _).fixes _ hh,sub_self]
    have hh : liftM (IP p n i) (IP p n i) (T i e)=(P true)ᵀ * M i e * P false := by
      simp only [liftM_def,T,pullM_def,P,Matrix.transpose_mul,Matrix.transpose_transpose,
        Matrix.mul_assoc]
    rw [hh,box_kill]
    constructor
    · intro x hx
      simp only [transpose_mul,transpose_transpose,←mulVec_mulVec,he true x hx,mulVec_zero]
    intro x hx
    rw [← Matrix.mulVec_mulVec,he false x hx,mulVec_zero]
  · refine (mrk_sum_le ..).trans ?_
    have ht i : (liftM (IP p n i) (IP p n i) (T i e)).rank≤R := (rank_lift_le ..).trans
      ((rank_lift_le ..).trans (hR i e))
    exact (Fintype.sum_bool _).le.trans ((Nat.add_le_add (ht _) (ht _)).trans_eq (two_mul R).symm)
  · rw [each_sumF]
    let z : Place p := (e,true)
    let z' : Place p := (e,false)
    let C := M i e
    change (C-(T i e)).rank≤2*H
    have he : C-T i e=(A z i)ᵀ*C+(B z i)ᵀ*C*A z' i := by
      unfold T; rw [pullM_def]
      dsimp only [B]
      simp only [transpose_sub,Matrix.transpose_one,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,
        Matrix.one_mul,C,z,z']
      abel
    have hh (z) : (A z i).rank ≤ H := (rank_maps (S z i) ((hA z i).onto)).trans (hF z i)
    rw [he,two_mul]
    refine (mrk_add_le ..).trans ?_
    exact Nat.add_le_add ((Matrix.rank_mul_le_left ..).trans (Matrix.rank_transpose (A z i) ▸ hh z))
      ((Matrix.rank_mul_le_right ..).trans (hh z'))

set_option maxHeartbeats 800000 in
theorem split_linear {M : Individual p n} {f b : Plan p n} {j : Bool}
    {C D : ChanOut p n} {P : PureForms p n}
    (R T H : ℕ) (ht : ∀ z i,dim (sPin f z i)≤T) (hm : ∀ i e,(M i e).rank≤R)
    (hc : outSmall H C)
    (hd : D∈deltaSpace p f b j) (hp : P∈pureSpace p f)
    (hh : obsPair p (chanInner p C C)+obsPair p (chanDeriv p C D)+obsPair p P=obsI p M) :
    ∃ (B : ChanOut p n) (P' P0 : PureForms p n) (Mr : Individual p n),
      B∈deltaSpace p f b j ∧ P'∈pureSpace p f ∧ P0∈pureSpace p f ∧
      outSmall (3*H) (C+B) ∧ (∀ e,(P0 e).rank≤2*R) ∧
      obsPair p (chanInner p (C+B) (C+B))+obsPair p (P'+P0)=obsI p M ∧
      obsPair p P'=obsI p Mr ∧ ∀ i e, (Mr i e).rank ≤2*T+3*H := by
  classical
  obtain ⟨B,hB,hK,hZ⟩ := deriv_compress hc hd
  obtain ⟨P0,hQ,hA,hL⟩ := primary_initial M f T R ht hm
  let P' := P-chanInner p B B-P0
  let CI := chanInner p (C+B) (C+B)
  let E := eachF p CI
  refine ⟨B,P',P0,M-eachF p P0-E,hB,(pureSpace p f).sub_mem
    ((pureSpace p f).sub_mem hp (chanInner_pure hB hB)) hQ,hQ,?_⟩
  have hsmall : outSmall (3*H) (C+B) := by
    intro z i
    rw [Pi.add_apply,Matrix.add_mul]
    apply le_trans (mrk_add_le ..)
    exact (Nat.add_le_add (hc z i) ((Matrix.rank_mul_le_left ..).trans (hK z))).trans
      (by omega)
  have hg : obsPair p (chanInner p (C+B) (C+B)) + obsPair p (P'+P0)=obsI p M := by
    rw [obsPair_chan_change,←hZ,show P'=P-chanInner p B B-P0 from rfl,sub_add_cancel,map_sub]
    exact (show _=obsPair p (chanInner p C C)+obsPair p (chanDeriv p C D)+obsPair p P by
      abel).trans hh
  refine ⟨hsmall,hA,hg,?_,fun i e => ?_⟩
  · rw [map_sub (obsI p) (M-eachF p P0) E,map_sub (obsI p),← hg]
    rw [obsI_each,show E= eachF p CI from rfl,obsI_each]
    unfold CI
    rw [map_add]; abel
  rw [Pi.sub_apply,Pi.sub_apply]
  exact (mrk_sub ..).trans (Nat.add_le_add (hL i e) (show (E i e).rank≤_ from by
    unfold E CI; rw [each_chan_val]; exact (Matrix.rank_mul_le_right ..).trans (hsmall _ i)))
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PrimalSpaceCompression
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Primal Space Compression -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n : ℕ} {I J : Type} [Fintype I] [Fintype J]

private theorem exists_cover (S : J→Space (Vec I)) (D : ℕ) (h : ∀ j,dim (S j)≤D) :
    ∃ A : Space (Vec I),(∀ j,S j ≤ A) ∧ dim A≤Fintype.card J*D := by
  classical
  have hh (s : Finset J) :
      ∃ A : Space (Vec I),(∀ j∈s,S j≤A) ∧ dim A ≤ s.card*D := by
    induction s using Finset.induction with
    | empty => exact ⟨⊥,by simp, by simp [dim]⟩
    | insert a s ha ih =>
      obtain ⟨A,hA,hD⟩ := ih
      refine ⟨S a⊔A,fun j hj => ?_,?_⟩
      · rcases Finset.mem_insert.mp hj with rfl|g
        · exact le_sup_left
        exact (hA _ g).trans le_sup_right
      simpa only [Finset.card_insert_of_notMem ha,Nat.add_mul,one_mul,add_comm D] using
        ((Submodule.finrank_add_le_finrank_add_finrank (S a) A).trans (add_le_add (h a) hD))
  simpa only [Finset.mem_univ,true_imp_iff,card_univ] using hh Finset.univ

theorem compact_endo (S T : Space (Vec I)) :
    ∃ A : Mat I I,(∀ x∈S,A *ᵥ x=x) ∧ (∀ x∈T,Aᵀ *ᵥ x=x) ∧ A.rank≤dim S+dim T := by
  classical
  obtain ⟨A,hA⟩ := proj_exists S ⊥ disjoint_bot_right
  obtain ⟨B,hB⟩ := proj_exists T ⊥ disjoint_bot_right
  refine ⟨A+Bᵀ * (1-A),fun x hx => ?_,fun x hx => ?_,?_⟩
  · rw [Matrix.add_mulVec,←Matrix.mulVec_mulVec,Matrix.sub_mulVec,hA.fixes x hx,
      Matrix.one_mulVec,sub_self,Matrix.mulVec_zero,add_zero]
  · rw [Matrix.transpose_add,Matrix.add_mulVec,Matrix.transpose_mul,Matrix.transpose_transpose,
      ← mulVec_mulVec,hB.fixes x hx,Matrix.transpose_sub,Matrix.sub_mulVec,Matrix.transpose_one,
      Matrix.one_mulVec,add_sub_cancel]
  exact (mrk_add_le ..).trans (add_le_add (rank_maps S hA.onto) ((Matrix.rank_mul_le_left ..).trans
    (by rw [Matrix.rank_transpose]; exact rank_maps T hB.onto)))

theorem readCoeff_val (s : Sel p) (d : Block p.g) (v : Ray p n) :
    (iCoeff p n s d)ᵀ *ᵥ v=readCoeff p s d v := embedMatT _ _

theorem shrink_transpose (A : Nendo p n) :
    (rowShrink p A)ᵀ=rowShrink p (fun i => (A i)ᵀ) := by
  simp only [rowShrink,Matrix.transpose_add,Matrix.transpose_mul,
    Matrix.transpose_sum,Matrix.transpose_transpose,Matrix.mul_assoc]

private theorem coeff_none (A : Nendo p n) (v : Ray p n) (s : Sel p) :
    (rowShrink p A *ᵥ v) (s,none)=v (s,none) := by
  classical
  simp only [rowShrink,Matrix.add_mulVec, Matrix.sum_mulVec,←Matrix.mulVec_mulVec,readCoeff_val]
  unfold iFix iCoeff
  rw [embedMatT]
  simp [embedMat,Matrix.mulVec,dotProduct,Finset.sum_apply,Matrix.mul_apply]

set_option maxHeartbeats 600000 in
private theorem coeff_some (A : Nendo p n) (v : Ray p n) (s : Sel p)
    (d : Block p.g) (i : Fin n) :
    (rowShrink p A *ᵥ v) (s,some (d,i))=(A d *ᵥ (readCoeff p s d v)) i := by
  classical
  simp only [rowShrink,Matrix.add_mulVec, Matrix.sum_mulVec,←Matrix.mulVec_mulVec,readCoeff_val]
  simp only [Pi.add_apply,Finset.sum_apply]
  have hz (x) : (iFix p n *ᵥ x) (s,some (d,i))=0 := by
    simp [iFix,embedMat,Matrix.mulVec,dotProduct]
  rw [hz,zero_add]
  have hh (t : Sel p) (a : Block p.g) (x : Vec (Fin n)) :
      (iCoeff p n t a *ᵥ x) (s,some (d,i)) =
      if s=t then (if d=a then x i else 0) else 0 := by
    by_cases e : s=t <;> by_cases g : d=a <;> simp [iCoeff,embedMat,Matrix.mulVec,dotProduct,e,g]
  simp_rw [hh]
  rw [Finset.sum_eq_single s]
  · simp only [ite_true, if_true,Finset.sum_ite_eq,mem_univ]
  · intro a _ ha; simp only [ite_eq_right (Ne.symm ha),Finset.sum_const_zero]
  simp

private theorem coeff_fixes (A : Nendo p n) (v : Ray p n)
    (h : ∀ d s, A d *ᵥ (readCoeff p s d v) = readCoeff p s d v) :
    rowShrink p A *ᵥ v=v := by
  funext i
  rcases i with ⟨s, _|⟨d,i⟩⟩
  · rw [coeff_none]
  rw [coeff_some,h]
  rfl

theorem shrink_rank (A : Nendo p n) (D : ℕ) (h : ∀ i,(A i).rank ≤ D) :
    (rowShrink p A).rank≤ psize p+ psize p* (nbBlock p*D) := by
  apply le_trans (mrk_add_le ..)
  apply add_le_add
  · exact (Matrix.rank_mul_le_left ..).trans (iFix p n).rank_le_card_width
  refine (mrk_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _ => nbBlock p*D) (fun i _ => ?_)).trans_eq
    (by simp [psize,Sel]))
  refine (mrk_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _ => D) (fun i _ => ?_)).trans_eq
    (by simp [nbBlock]))
  exact ((Matrix.rank_mul_le_left ..).trans (Matrix.rank_mul_le_right ..)).trans (h i)

theorem shrink_both (S T : Place p → Space (Ray p n)) (K R : ℕ)
    (hk : ∀ z,dim (S z) ≤K) (hr : ∀ z,dim (T z)≤R) :
    ∃ A : Nendo p n,
      (∀ z,∀ x∈S z,rowShrink p A *ᵥ x=x) ∧
      (∀ z,∀ x∈T z,(rowShrink p A)ᵀ *ᵥ x=x) ∧
      (rowShrink p A).rank ≤ drow p K R := by
  classical
  let W := Place p×Sel p
  have hp : Fintype.card (Place p×Sel p)=ncComp p*2*psize p := by
    simp only [Place,Fintype.card_prod,ncComp,Fintype.card_bool,psize,Sel]
  let G d (S : Place p → Space (Ray p n)) (z : Place p×Sel p) :=
    (S z.1).map (iCoeff p n z.2 d)ᵀ.mulVecLin
  obtain ⟨A,hA,hT,hL⟩ :
      ∃ A : Nendo p n,
        (∀ d z,∀ x∈G d S z,A d *ᵥ x=x) ∧
        (∀ d z,∀ x∈G d T z,(A d)ᵀ *ᵥ x=x) ∧ ∀ i,(A i).rank≤dbits p K R := by
    have he (d : Block p.g) :
        ∃ A : Mat (Fin n) (Fin n), (∀ z,∀ x∈G d S z,A *ᵥ x=x) ∧
        (∀ z,∀ x∈G d T z,Aᵀ *ᵥ x=x) ∧ A.rank≤dbits p K R := by
      obtain ⟨X,hX,hD⟩ := exists_cover (G d S) K (fun j => (Submodule.finrank_map_le ..).trans
        (hk j.1))
      obtain ⟨Y,hY,hD'⟩ := exists_cover (G d T) R (fun j => (Submodule.finrank_map_le ..).trans
        (hr j.1))
      obtain ⟨A,hA,hZ,hL⟩ := compact_endo X Y
      refine ⟨A,(fun z x hx => hA x (hX z hx)),(fun z x hx => hZ x (hY z hx)),?_⟩
      rw [hp] at hD hD'
      exact hL.trans ((add_le_add hD hD').trans_eq (Nat.mul_add ..).symm)
    choose A hA hZ hL using he
    exact ⟨A,hA,hZ,hL⟩
  have he (X : Place p → Space (Ray p n)) (z)
      (x : Ray p n) (hx : x∈X z) (d s) : readCoeff p s d x∈ G d X (z,s) :=
    ⟨x,hx,readCoeff_val ..⟩
  refine ⟨A,fun z x hx => ?_,fun z x hx => ?_,shrink_rank A _ hL⟩
  · exact coeff_fixes A x (fun d s => hA _ (z,s) _ (he S z x hx d s))
  rw [shrink_transpose]
  exact coeff_fixes _ _ (fun d s => hT _ (z,s) _ (he T z x hx d s))

private theorem shrink_point (A : Nendo p n) (s : Label p.b) (z : Base p.g n) :
    rowShrink p A *ᵥ point p s z=point p s (shrinkBase (p:=p) A z) := by
  classical
  funext i
  rcases i with ⟨r,_|⟨d,i⟩⟩
  · rw [coeff_none]; rfl
  rw [coeff_some]
  simp only [point_eval,readCoeff,shrinkBase,Matrix.mulVec,dotProduct,
    baseV,Option.elim',Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_left_comm ..

private theorem shrink_tag (A : Nendo p n) (l : Tag p.g) (M : Moment p n) (h : M∈Wtag p n l) :
    liftM (rowShrink p A) (rowShrink p A) M∈Wtag p n l := by
  classical
  unfold Wtag at h
  induction h using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨s,z,hz,rfl⟩ := hm
    simp only [mom,liftM_outer,shrink_point]
    apply Submodule.subset_span
    refine ⟨s,shrinkBase (p:=p) A z,?_,rfl⟩
    intro d t hd i
    change (A (Block.O d t) *ᵥ _) i = _
    simp only [Matrix.mulVec,dotProduct,hz _ _ hd,mul_zero,Finset.sum_const_zero]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ih ih' => rw [map_add]; exact Submodule.add_mem _ ih ih'
  | smul a x hx ih => rw [map_smul]; exact Submodule.smul_mem _ _ ih

theorem shrink_X (A : Nendo p n) (M : Profile p n) (h : M∈Xspace p n) :
    (fun e : Comp p.g => liftM (rowShrink p A) (rowShrink p A) (M e))∈Xspace p n := by
  obtain ⟨w,hw,rfl⟩ := mem_X.mp h
  refine mem_X.mpr ⟨_,(fun l => shrink_tag A l _ (hw l)),?_⟩
  funext i
  exact (map_add (liftM (rowShrink p A) (rowShrink p A)) _ _).symm

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BilinearCompression
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bilinear Compression -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset
open scoped BigOperators

variable {p : Shape} {n : ℕ} {I J : Type} [Fintype I] [Fintype J]

private theorem pullM_fix (A : Mat I I) (P : Mat I I)
    (h : ∀ x ∈ colSp P,Aᵀ *ᵥ x=x) (h' : ∀ x∈colSp Pᵀ,Aᵀ *ᵥ x=x) :
    pullM A A P=P := by
  rw [pullM_def,mat_mul_fix h]
  have he := congrArg Matrix.transpose (mat_mul_fix h')
  simpa only [Matrix.transpose_mul,Matrix.transpose_transpose] using he

private theorem dualSpace_dim (M : Profile p n) (z : Place p) :
    dim (dualSpace M z)=(M z.1).rank := by
  cases z with
  | mk i b =>
    cases b; exact Matrix.rank_transpose _; rfl

private theorem joint_ip (A : Bool → Nendo p n) (B : Place p → Bool → Mat (Chan p) (Chan p))
    (z : Place p) (i : Bool) :
    jointShrink A B z * IP p n i = IP p n i * rowShrink p (A i) := by
  classical
  simp only [jointShrink,Fintype.sum_bool,liftM_def,Matrix.add_mul,Matrix.mul_assoc,
    IH_IP,Matrix.mul_zero,add_zero]
  cases i <;> simp only [IP_self,IP_cross (show true≠false by decide),
    IP_cross (show false≠true by decide),Matrix.mul_zero,Matrix.mul_one,add_zero,zero_add]

set_option maxHeartbeats 800000 in
theorem shrink_pure {f : Plan p n} {M : Individual p n} {P : PureForms p n}
    (T H R : ℕ) (ht : ∀ z i,dim (sPin f z i)≤T) (hh : ∀ z i,dim (hPin f z i)≤H)
    (hr : ∀ i e,(M i e).rank≤R)
    (hp : P∈pureSpace p f) (he : obsPair p P=obsI p M) :
    ∃ Q∈pureSpace p f,obsPair p Q=obsPair p P ∧ ∀ e,(Q e).rank≤dqBound p T H R := by
  classical
  choose A hA hL hT using fun i => shrink_both (fun z => sPin f z i) (dualSpace (M i)) T R
    (fun z => ht z i) (fun z => by rw [dualSpace_dim]; exact hr i z.1)
  choose B hB using fun z i => proj_exists (hPin f z i) ⊥ disjoint_bot_right
  let D := jointShrink A B
  have hf (z : Place p) (x : Dir p n) (hx : x∈f z) : D z *ᵥ x=x := by
    have h1 (i : Bool) : rowShrink p (A i) *ᵥ ((IP p n i)ᵀ *ᵥ x)=(IP p n i)ᵀ *ᵥ x :=
      hA i z _ ⟨_,hx,rfl⟩
    have h2 (i : Bool) : B z i *ᵥ ((IH p n i)ᵀ *ᵥ x)=(IH p n i)ᵀ *ᵥ x :=
      (hB z i).fixes _ ⟨_,hx,rfl⟩
    unfold D jointShrink
    simp only [Matrix.sum_mulVec,Matrix.add_mulVec,liftM_def,← Matrix.mulVec_mulVec,h1,h2]
    exact ip_decomp x
  have hR (z : Place p) : (D z).rank ≤ dqBound p T H R := by
    apply le_trans (mrk_sum_le ..)
    have hx i :
        (liftM (IP p n i) (IP p n i) (rowShrink p (A i))+
          liftM (IH p n i) (IH p n i) (B z i)).rank ≤ drow p T R+H :=
      (mrk_add_le ..).trans (add_le_add
        ((rank_lift_le ..).trans (hT i)) ((rank_lift_le ..).trans
        ((rank_maps (hPin f z i) (hB z i).onto).trans (hh z i))))
    rw [Fintype.sum_bool,dqBound,two_mul]; exact add_le_add (hx _) (hx _)
  let Q (e : Comp p.g) := pullM (D (e,true)) (D (e,false)) (P e)
  have hG (i : Bool) (e : Comp p.g) : pullM (rowShrink p (A i)) (rowShrink p (A i)) (M i e)=
      M i e := pullM_fix _ _ (hL i (e,true)) (hL i (e,false))
  have hY (i : Bool) (e : Comp p.g) : eachF p Q i e=
      pullM (rowShrink p (A i)) (rowShrink p (A i)) (eachF p P i e) := by
    change pullM _ _ (Q e)=pullM _ _ (pullM _ _ _)
    let G := IP p n i
    have hw {I J K U V W : Type} [Fintype U] [Fintype V] [Fintype W] [Fintype I]
        [Fintype J] [Fintype K] (L : Mat U I) (R : Mat V J)
        (L' : Mat I K) (R' : Mat J W) (P : Mat U V) :
        pullM L' R' (pullM L R P) = pullM (L*L') (R*R') P := by
      unfold pullM
      rw [liftM_comp,Matrix.transpose_mul,Matrix.transpose_mul]
    unfold Q
    rw [hw,hw]
    have h (b) := joint_ip A B (e,b) i
    rw [show D (e,true)*IP p n i=_ from h true, show D (e,false)*IP p n i=_ from h false]

  refine ⟨Q,?_,?_,fun e => ?_⟩
  · refine (pureSpace_mem _).mpr fun e => ?_
    obtain ⟨h1,h2⟩ := box_kill.mp ((pureSpace_mem _).mp hp e)
    unfold Q; rw [box_kill,pullM_def]; constructor
    · intro x hx
      simp only [transpose_mul,transpose_transpose,←Matrix.mulVec_mulVec,hf (e,true) x hx,h1 x hx,
        mulVec_zero]
    intro x hx
    rw [← mulVec_mulVec,hf (e,false) x hx]
    rw [← mulVec_mulVec,h2 x hx,mulVec_zero]
  · rw [he,obsPair_each]
    rw [obsPair_each] at he
    change combineF p _=combineF p _
    change combineF p _=combineF p _ at he
    have he := (combineF_same ..).mp he
    apply (combineF_same ..).mpr
    intro i x hx
    let y : Profile p n := fun e => liftM (rowShrink p (A i)) (rowShrink p (A i)) (x e)
    rw [repF_rep,repF_rep]
    have hv := he i y (shrink_X (A i) x hx)
    rw [repF_rep,repF_rep] at hv
    have hu (F : Individual p n) : (∑ e,mpair (F i e) (y e))=
        ∑ e,mpair (pullM (rowShrink p (A i)) (rowShrink p (A i)) (F i e)) (x e) :=
      Finset.sum_congr rfl fun e _ => mpair_liftM ..
    rw [hu,hu] at hv
    simp_rw [← hY,hG] at hv
    exact hv
  unfold Q; rw [pullM_def]
  exact ((Matrix.rank_mul_le_left ..).trans (Matrix.rank_mul_le_left ..)).trans
    (by rw [Matrix.rank_transpose]; exact hR _)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ChannelFactorization
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Channel Factorization -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module
open scoped BigOperators
variable {p : Shape} {n : ℕ}
variable {I J : Type} [Fintype I] [Fintype J]

/-- Pairing rank after imposing orthogonality constraints. -/
theorem biorth_exists (S T : Space (Vec I)) (r : ℕ)
    (h : r+dim S+dim T≤Fintype.card I) :
    ∃ A B : Mat I (Fin r), colSp A≤ annih S ∧ colSp B≤ annih T ∧ Aᵀ*B=1 := by
  classical
  let V := annih S
  let W := annih T
  let M := (pack V)ᵀ * pack W
  let t := M.rank
  have ht : r≤t := by
    have h1 := rank_ge_mul (pack V)ᵀ (pack W)
    rw [Matrix.rank_transpose,mrk_inj.mp (pack_inj V),mrk_inj.mp (pack_inj W),
      Fintype.card_fin,Fintype.card_fin] at h1
    have h2 : dim S+dim V=Fintype.card I := annih_dim S
    have h3 : dim T+dim W=Fintype.card I := annih_dim T
    have he (a b c d t r e : ℕ) (h : r+a+b ≤ e) (hx : a+c=e) (hy : b+d=e) (ht : c+d≤t+e) :
        r≤t := by omega
    exact he _ _ _ _ _ _ _ h h2 h3 h1
  obtain ⟨A,B,hA,hB,hM⟩ := rank_product M
  obtain ⟨L,hL⟩ := mat_left_inv hA
  obtain ⟨R,hR⟩ := mat_left_inv (P:=Bᵀ) (transpose_surj_iff.mp (by rw [Matrix.transpose_transpose]; exact hB))
  let E := embedMat (Fin.castLE ht)
  refine ⟨pack V * (Lᵀ * E),pack W*(Rᵀ*E),?_,?_,?_⟩
  · rintro x ⟨x,rfl⟩
    rw [Matrix.mulVecLin_apply,← Matrix.mulVec_mulVec]
    exact (pack_mem_iff ..).mpr ⟨_,rfl⟩
  · rintro x ⟨x,rfl⟩
    rw [Matrix.mulVecLin_apply,← Matrix.mulVec_mulVec]
    exact (pack_mem_iff ..).mpr ⟨_,rfl⟩
  have he : L*M*Rᵀ=1 := by
    have hg : B*Rᵀ=1 := by
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] using
        congrArg Matrix.transpose hR
    refine (congrArg (fun X => L*X*Rᵀ) hM).symm.trans ?_
    rw [← Matrix.mul_assoc L,hL,Matrix.one_mul,hg]
  have heq : Eᵀ * E=1 := embedMat_self (Fin.castLE_injective ht)
  rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose]
  calc _ = Eᵀ*(L*M*Rᵀ)*E := by simp only [M,Matrix.mul_assoc]
       _ = _ := by rw [he,Matrix.mul_one,heq]

/-- split desired respective bounded-rank bilinear form -/
theorem pure_chan_split (M : Mat J J) (S T : Space (Vec I)) (X Y : Space (Vec J))
    (h : M∈box (annih X) (annih Y)) (ht : M.rank+dim S+dim T ≤ Fintype.card I) :
    ∃ A ∈ box (annih S) (annih X),∃ B∈box (annih T) (annih Y), Aᵀ * B=M := by
  classical
  obtain ⟨P,Q,hP,hQ,hM⟩ := rank_product M
  obtain ⟨A,B,hA,hB,he⟩ := biorth_exists S T M.rank ht
  obtain ⟨hx,hy⟩ := box_kill.mp h
  refine ⟨A * Pᵀ,?_,B*Q,?_,?_⟩
  · rw [box_kill]
    constructor
    · intro x hx; rw [Matrix.transpose_mul,← Matrix.mulVec_mulVec,(colSp_kill ..).mp hA x hx,
        Matrix.mulVec_zero]
    intro x hv
    have hv' : Pᵀ *ᵥ x=0 := by
      have hqi := (transpose_surj_iff (P:=Qᵀ)).mp (by rw [Matrix.transpose_transpose]; exact hQ)
      apply hqi
      rw [Matrix.mulVec_mulVec,← Matrix.transpose_mul,hM,hx x hv,Matrix.mulVec_zero]
    rw [←Matrix.mulVec_mulVec,hv',mulVec_zero]
  · rw [box_kill]
    constructor
    · intro x hv; rw [Matrix.transpose_mul,←Matrix.mulVec_mulVec,(colSp_kill ..).mp hB x hv,
        Matrix.mulVec_zero]
    intro y hv
    have hv' : Q *ᵥ y=0 := by
      apply hP
      rw [Matrix.mulVec_mulVec,hM,hy y hv,mulVec_zero]
    rw [←Matrix.mulVec_mulVec,hv',mulVec_zero]
  · rw [Matrix.transpose_mul,Matrix.transpose_transpose,← Matrix.mul_assoc _ B, Matrix.mul_assoc P,
      he,Matrix.mul_one,hM]

/-- The final channel change for fixed B endpoint. -/
theorem chan_factor {f b : Plan p n} {P : PureForms p n} {C : ChanOut p n} {j : Bool}
    (H T K : ℕ) (hc : outSmall H C) (hK : ∀ z,dim (hPin b z j)≤K)
    (hh : T+2*(K+2*H)≤p.h)
    (hP : P∈pureSpace p f) (ht : ∀ e,(P e).rank≤T) :
    ∃ D∈deltaSpace p f b j,obsPair p (chanInner p (C+D) (C+D))=
      obsPair p (chanInner p C C)+obsPair p P := by
  classical
  let S (z : Place p) := hPin b (flipZ p z) j ⊔ priOut p C (flipZ p z)
  have h (z : Place p) : dim (S z) ≤ K+2*H :=
    (Submodule.finrank_add_le_finrank_add_finrank ..).trans
      (add_le_add (hK _) (dim_priOut hc _))
  choose A hA B hB hQ using fun e : Comp p.g =>
    pure_chan_split (P e) (S (e,true)) (S (e,false)) (f (e,true)) (f (e,false))
      ((pureSpace_mem _).mp hP e) ((add_le_add
        (add_le_add (ht e) (h (e,true))) (h (e,false))).trans
        (by
          rw [Fintype.card_fin]
          rwa [two_mul, ← add_assoc] at hh))
  let D : ChanOut p n := fun z => if z.2 then A z.1 else B z.1
  have h1 (z : Place p) : D z∈box (annih (S z)) (annih (f z)) := by
    cases z with | mk e c => cases c; exact hB e; exact hA e
  refine ⟨D,(deltaSpace_mem _).mpr ?_,?_⟩
  · intro z
    refine box_le ?_ le_rfl (h1 z)
    intro x hx
    rw [annih_mem]
    exact fun y hy => (annih_mem ..).mp hx y (Submodule.mem_sup_left hy)
  have hg : chanInner p D D=P := funext (fun e => hQ e)
  have he (z : Place p) (i l : Bool) (x y : Ray p n) :
      dotProduct ((C (flipZ p z)*IP p n i) *ᵥ x) ((D z*IP p n l)*ᵥ y)=0 := by
    have hq : ((C (flipZ p z)*IP p n i) *ᵥ x) ∈ S z :=
      Submodule.mem_sup_right (le_priOut C _ i ⟨x,rfl⟩)
    have hl : ((D z * IP p n l)*ᵥ y) ∈ annih (S z) := by
      rw [←Matrix.mulVec_mulVec]
      exact ((box_mem ..).mp (h1 z)).1 ⟨_,rfl⟩
    rw [dotProduct_comm]
    exact (annih_mem ..).mp hl _ hq
  have hd : obsPair p (chanDeriv p C D)=0 := by
    rw [←obsI_each]
    have hz : eachF p (chanDeriv p C D)=0 := by
      unfold chanDeriv; rw [map_add]
      funext i e
      rw [Pi.add_apply,Pi.add_apply,each_chan_val,each_chan_val]
      refine evmat_ext fun x y => ?_
      rw [evmat_addM,ev_duom,ev_duom]
      have hh1 := he (e,false) i i x y
      have hh2 := he (e,true) i i y x
      simp only [flipZ,Bool.not_false,Bool.not_true] at hh1 hh2
      rw [hh1,
        dotProduct_comm ((D (e,true) * IP p n i) *ᵥ _),hh2]
      simp [evmat]
    rw [hz,map_zero]
  rw [obsPair_chan_change,hd,add_zero,hg]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GradientRealization
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gradient Realization -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

variable {I : Type} [Fintype I]
namespace Volley
set_option maxHeartbeats 600000 in
private theorem realize_one (v w : Volley p n I) {t : Tagging p I} (m : Mixer p n)
    (x y : UnitType p n N) (a b : Plan p n) (T B : Cross p n)
    (K : ℕ) (h : realizeAssum p K)
    (hb : v.bounded w.obj) (ht : v.legal t)
    (hv : v.avoids a (qorth K)) (hK : planRank a≤K) (hL : planRank b≤K)
    (hB : fitsTable a b B T) (hT : tableInj a b T)
    (hf : rowAgree (v.frozen a t) B (actual p x y)) (hC : lowCross (blin K) B)
    (hR : v.scalarRecipe w t m x a T) (hk : v.keys t x=w.keys t y)
    (hy : ∀ i, frameLaw m (onSide y i))
    (hS : v.attackGrad w t m y) (j : Bool) :
    ∃ D∈deltaSpace p (v.frozen a t) b j,
      obsPair p (chanInner p (channelOut p B j+D) (channelOut p B j+D))=
        combineF p (v.demand w t m j) := by
  classical
  let G := v.demand w t m j
  let L := blin K
  let R := rankInit p
  obtain ⟨D,hD,P,hP,hZ⟩ := v.realize_linear w m x y a b T B hb ht (qorth K) (Rorth K) hv h.sel
    (by unfold Rorth; omega) (Nat.le_refl (qorth K)) hB hT hf hR hk hy hS j
  let C := channelOut p B j
  let f := v.frozen a t
  have he (z i) : dim (sPin f z i) ≤ K+14 :=
    (v.frozen_here_dim hb a t i z).trans (Nat.add_le_add_right hK 14)
  obtain ⟨M,hM,hA⟩ :
      ∃ M : Individual p n, obsI p M=combineF p G ∧ ∀ i e,(M i e).rank≤R := by
    choose M hM hA using fun i : Bool =>
      v.gradient_rep (w:=w.obj) (i:=i) (j:=j) m h.odd ht (hb _ _).2 (hR.summ i j)
    refine ⟨M,?_,hA⟩
    have he : repF p M=G := by
      funext i
      exact LinearMap.ext fun x => (repF_rep M i x).trans (hM i x).symm
    change combineF p (repF p M)=_
    rw [he]
  obtain ⟨D,Q,V,X,hV,hQ,hW,hU,hX,hG,hF,hE⟩ := split_linear R (K+14) L he hA
    (outSmall_low hC j) hD hP (hZ.trans hM.symm)
  obtain ⟨Q',hq,hO,hN⟩ := shrink_pure (K+14) K (rankRes K) he (fun z i => by
      unfold f; rw [v.hPin_frozen]; exact ((hPin_dim ..).trans (dim_le_plan a z)).trans hK)
    hE hQ hF
  have hJ (i) : ((Q'+V) i).rank ≤ rankAll p K := (mrk_add_le ..).trans ((add_le_add
    (hN i) (hX i)).trans_eq (add_comm _ _))
  obtain ⟨Z,hY,hZ⟩ := chan_factor (3*L) (rankAll p K) K hU
    (fun z => ((hPin_dim ..).trans (dim_le_plan b z)).trans hL) h.cap
    ((pureSpace p f).add_mem hq hW) hJ
  refine ⟨D+Z,(deltaSpace p f b j).add_mem hV hY,?_⟩
  rw [← add_assoc,hZ,map_add,hO,←map_add,hG,hM]

end Volley

private theorem addChan_val (M : Cross p n) (D : Bool → ChanOut p n) (i : Bool) :
    channelOut p (M+addChan p D) i= channelOut p M i+D i := by
  funext z
  unfold addChan channelOut
  simp only [Fintype.sum_bool,Pi.add_apply,Matrix.transpose_add,Matrix.add_mul,Matrix.mul_assoc]
  cases i <;> simp only [IH_self,IH_cross (show false≠true by decide),
    IH_cross (show true≠false by decide),Matrix.mul_zero,Matrix.mul_one,transpose_zero,
    transpose_transpose,zero_add,add_zero]

theorem row_add {M B C : Cross p n} {f : Plan p n} (h : rowAgree f B C)
    (hf : zeroRow p f M) :
    rowAgree f (B+M) C := by
  intro z v hv u
  rw [Pi.add_apply, evmat_addM,h z v hv,← evmat_transpose (M z),evmat,evmat,hf z v hv,
    dotProduct_zero,add_zero]

private theorem addChan_zero {D : Bool → ChanOut p n} {f b : Plan p n}
    (h : ∀ i,D i∈deltaSpace p f b i) :
    zeroRow p f (addChan p D) ∧ zeroRow p b (reciprocal p (addChan p D)) := by
  have hh (z : Place p) (i : Bool) :=
    box_kill.mp ((deltaSpace_mem _).mp (h i) z)
  constructor
  · intro z v hv
    unfold addChan
    simp only [Fintype.sum_bool,transpose_add, transpose_mul,transpose_transpose,
      Matrix.add_mulVec,← Matrix.mulVec_mulVec,(hh z _).2 v hv,mulVec_zero,zero_add]
  intro z v hv
  unfold reciprocal addChan
  have ht (i) : (IH p n i)ᵀ *ᵥ v ∈ hPin b (flipZ p (flipZ p z)) i := by
    rw [flipZ_flip]; exact ⟨v,hv,rfl⟩
  have he i := (hh (flipZ p z) i).1 _ (ht i)
  simp only [Fintype.sum_bool, Matrix.transpose_transpose,Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec,he,zero_add]

private theorem recip_effect (B : Cross p n) (D : Bool → ChanOut p n) :
    scalarBlocks p (B+reciprocal p (addChan p D))=scalarBlocks p B := by
  funext z i j
  unfold scalarBlocks channelOut reciprocal addChan
  simp only [Pi.add_apply,Fintype.sum_bool,Matrix.transpose_add,Matrix.add_mul,Matrix.transpose_mul,
    Matrix.transpose_transpose,Matrix.mul_assoc,IH_IP,Matrix.mul_zero,add_zero]

private theorem delta_frozen {b f : Plan p n} (v : Volley p n I) (t : Tagging p I) (i : Bool) :
    deltaSpace p f (v.frozen b t) i=deltaSpace p f b i := by
  unfold deltaSpace
  simp_rw [v.hPin_frozen]

private theorem recip_add (B C : Cross p n) :
    reciprocal p (B+C) = reciprocal p B+reciprocal p C := by
  funext i; exact Matrix.transpose_add _ _

namespace Volley
private theorem realized_changes (v w : Volley p n I) (t : Tagging p I)
    (m : Mixer p n) {D E : Bool → ChanOut p n} {B : Cross p n}
    (h : ∀ j,obsPair p (chanInner p (channelOut p B j+D j) (channelOut p B j+D j))=
      combineF p (v.demand w t m j)) :
    v.realized w t m (B+addChan p D+reciprocal p (addChan p E)) := by
  intro i j x hx
  let B' := B+addChan p D
  have he := h j
  rw [← addChan_val B D j,obsPair_chan] at he
  rw [contract_scalars _ _ (recip_effect _ E)]
  exact ((combineF_same ..).mp he i x hx).symm
end Volley

set_option maxHeartbeats 800000 in
theorem gradient_realization (v w : Volley p n I) {t : Tagging p I} (m : Mixer p n)
    (x y : UnitType p n N) (a b : Pin p n N) (T : Cross p n) (K : ℕ)
    (h : realizeAssum p K)
    (hA : v.bounded w.obj) (hB : w.bounded v.obj)
    (ht : v.legal t) (ht' : w.legal t)
    (hv : v.avoids a.sp (qorth K)) (hw : w.avoids b.sp (qorth K))
    (hK : planRank a.sp ≤ K) (hL : planRank b.sp ≤ K)
    (h1 : a.agree x) (h2 : b.agree y)
    (h3 : tableFlag a b T x) (h4 : tableFlag b a (reciprocal p T) y)
    (hT : tableInj a.sp b.sp T) (hT' : tableInj b.sp a.sp (reciprocal p T))
    (hR : v.scalarRecipe w t m x a.sp T) (hR' : w.scalarRecipe v t m y b.sp (reciprocal p T))
    (hk : v.keys t x=w.keys t y)
    (hx : ∀ i,frameLaw m (onSide x i)) (hy : ∀ i, frameLaw m (onSide y i))
    (hS : v.attackGrad w t m y) (hS' : w.attackGrad v t m x) :
    ∃ Q : Cross p n, v.realized w t m Q ∧ w.realized v t m (reciprocal p Q) ∧
    rowAgree (v.frozen a.sp t) Q (actual p x y) ∧
    rowAgree (w.frozen b.sp t) (reciprocal p Q) (actual p y x) := by
  classical
  obtain ⟨M,hQ,hD,hD',hM,hM'⟩ := start_form a b x y T
    (v.keyPlan t) (w.keyPlan t) (keyPlane v t) (keyPlane w t)
    (fun z => (v.key_independent t hv z).2.symm) (fun z => (w.key_independent t hw z).2.symm)
    h1 h2 h3 h4 K hK hL (v.key_dim hA t) (w.key_dim hB t)
  choose D hDA hG using fun j => Volley.realize_one v w m x y a.sp b.sp T M K h
    hA ht hv hK hL hQ hT hD hM hR hk hy hS j
  choose E hEA hF using fun j => Volley.realize_one w v m y x b.sp a.sp (reciprocal p T)
    (reciprocal p M) K h hB ht' hw hL hK (fits_recip hQ) hT' hD' hM' hR' hk.symm hx hS' j
  let Q := M+addChan p D+reciprocal p (addChan p E)
  have he : reciprocal p Q = reciprocal p M+addChan p E+reciprocal p (addChan p D) := by
    unfold Q
    rw [recip_add,recip_add,reciprocal_twice]; ac_rfl
  obtain ⟨hN,hN'⟩ := addChan_zero (D:=D) (f:=v.frozen a.sp t) (b:=w.frozen b.sp t)
    (fun i => by rw [delta_frozen w t i]; exact hDA i)
  obtain ⟨hO,hO'⟩ := addChan_zero (D:=E) (f:=w.frozen b.sp t) (b:=v.frozen a.sp t)
    (fun i => by rw [delta_frozen v t i]; exact hEA i)
  refine ⟨Q,Volley.realized_changes v w t m hG,?_,row_add (row_add hD hN) hO',?_⟩
  · rw [he]
    exact Volley.realized_changes w v t m hF
  rw [he]; exact row_add (row_add hD' hO) hN'

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConditionalCellEntropy
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional Cell Entropy -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

theorem plan_add_disjoint (a b : Plan p n) (h : ∀ z, Disjoint (a z) (b z)) :
    planRank (a⊔b)=planRank a+planRank b := by
  unfold planRank
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have he := Submodule.finrank_sup_add_finrank_inf_eq (a i) (b i)
  rw [(h i).eq_bot,finrank_bot,add_zero] at he
  exact he

theorem plan_new_disjoint (a b : Plan p n) (h : ∀ z,Disjoint (a z) (b z)) :
    planNew a b=planRank b := by rw [planNew,plan_add_disjoint a b h,Nat.add_sub_cancel_left]

variable {I : Type} [Fintype I]

theorem slots_budget {w : I→Bool} (v : Volley p n I)
    (hb : v.bounded w) : kslots p I ≤ kmax p := by
  classical
  have h := v.call_count hb
  unfold kslots kmax; nlinarith

theorem dim_keys (t : Tagging p I) :
    dim (Keys (p:=p) t N) = kslots p I * N := by
  have h (l : Tag p.g) :
      dim (AtomKey (p:=p) l N)=(p.g-1)*(2*N) := by
    unfold AtomKey dim

    rw [finrank_pi_fintype]
    have he : finrank F (Bool → Vec (Fin N))=2*N := by
      rw [finrank_pi_fintype]
      simp_rw [show finrank F (Vec (Fin N))=_ from dim_vec _]
      simp
    simp_rw [he]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_star]; rfl
  unfold dim Keys kslots
  rw [finrank_pi_fintype]
  have hx i : finrank F (AtomKey (p:=p) (t i) N)=(p.g-1)*(2*N) := h (t i)
  simp_rw [hx]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
  ring

namespace Volley
variable {v : Volley p n I}

theorem key_slots (t : Tagging p I) {q} {a : Plan p n}
    (h : v.avoids a q) :
    planNew a (v.keyPlan t) = kslots p I := by
  classical
  let Y := visits p t
  have hh i := key_independent v t h i
  have he (z : Place p) : dim (keyPlan v t z)=Fintype.card (Y z.1) :=
    mrk_inj.mp (hh z).1
  rw [plan_new_disjoint a _ (fun i => Disjoint.mono_left (pin_le_table a i)
    (hh i).2.symm), planRank,Fintype.sum_prod_type]
  simp_rw [Fintype.sum_bool,he,←two_mul,←Finset.mul_sum]
  have hE : ∑ i : Comp p.g,Fintype.card (Y i)=Fintype.card I*(p.g-1) := by
    have hf {A : Type} [Fintype A] (p : A → Prop) [DecidablePred p] :
        Fintype.card {i:A//p i}=∑ i:A, if p i then (1:ℕ) else 0 := by
      rw [Fintype.card_subtype,←Finset.sum_filter]; simp

    have hY (i) : Fintype.card (Y i)=∑ j:I,if inc i (t j) then (1:ℕ) else 0 := hf _
    simp_rw [hY]
    rw [Finset.sum_comm]
    simp_rw [← hf (fun i => inc i _)]
    have hz (j) : Fintype.card {i:Comp p.g//inc i (t j)}=p.g-1 := card_star (t j)
    simp_rw [hz]
    simp
  rw [hE]; unfold kslots; ring

/-- chosen reference x fixes the pin made of a and all key directions
for every y in the same pin which agrees on query key. -/
theorem key_pin (t : Tagging p I) {a : Pin p n N} {x y : UnitType p n N}
    (hx : a.agree x) (hy : a.agree y) (h : v.keys t x=v.keys t y) :
    (Pin.make (v.frozen a.sp t) x).agree y := by
  classical
  intro i u hu
  obtain ⟨l,hl,r,⟨z,rfl⟩,rfl⟩ := Submodule.mem_sup.mp
    (show u∈a.sp i⊔v.keyPlan t i from hu)
  have hZ : images y i * v.keyM t i.1 = images x i * v.keyM t i.1 := by
    ext b j
    obtain ⟨k,hk⟩ := j
    have ht := congr_fun (congr_fun (congr_fun h k) (⟨i.1,hk⟩ : TagStar _)) i.2
    rw [v.keys_loc,v.keys_loc] at ht
    exact congr_fun ht.symm b
  change images y i *ᵥ _ = images x i *ᵥ _
  rw [Matrix.mulVec_add,Matrix.mulVec_add,hx _ _ hl,hy _ _ hl]
  rw [mulVecLin_apply,mulVec_mulVec,mulVec_mulVec,hZ]
end Volley

theorem in_clear {a f : Pin p n N} {k : ℕ} {ζ : ℝ} {w : Wgt (UnitType p n N)}
    (hz : ζ ≤ 0.004) (hkz : ζ*k ≤ 0.004)
    (hw : SubLaw w) (h : a.clear ζ w) (hF : a.sp≤f.sp) (hk : planRank f.sp=planRank a.sp+k)
    (S : UnitType p n N → Prop)
    (hS : ∀ x,S x → f.agree x) (ht : tau N k ≤ pr w S) :
    IsLaw (onW w S) ∧ f.clear 0.05 (onW w S) := by
  classical
  have hpos : 0 < pr w S := lt_of_lt_of_le (bp_pos _) ht
  have hh : IsLaw (onW w S) := normW_law (subW_nonneg hw.nz _) hpos
  refine ⟨hh,fun b => ?_⟩
  let t := planNew f.sp b.sp
  by_cases he : t=0
  · change pr _ _ ≤ fee N _ t
    rw [he,fee]
    simp only [Nat.cast_zero,mul_zero,zero_mul,bp_zero]
    exact (pr_le_tot hh.nz).trans hh.total.le
  let R := fun x => S x ∧ b.agree x
  by_cases hf : 0 < pr w R
  · obtain ⟨x,⟨hx,hB⟩,_⟩ := exists_of_pr_pos hw.nz hf
    let c := Pin.make (f.sp⊔b.sp) x
    have hc : pr w R≤ fee N ζ (planNew a.sp c.sp) := (pr_mono hw.nz (q:=c.agree)
      (fun y hy => ((Pin.combine (hS x hx) hB).mpr ⟨hS _ hy.1,hy.2⟩))).trans (h c)
    have hN : planNew a.sp c.sp=k+t := by
      have hh : planNew a.sp f.sp+t=planNew a.sp c.sp := planNew_mono_add hF
      rw [← hh]
      rw [planNew, sup_eq_right.mpr hF,hk, Nat.add_sub_cancel_left]
    rw [hN] at hc
    rw [pr_on]
    refine ((div_le_div₀ (bp_pos _).le hc (bp_pos _) ht)).trans ?_
    unfold fee
    rw [←bp_sub]
    refine bp_le ?_
    have h1 : 1 ≤ (t:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr he
    have hg := mul_le_mul_of_nonneg_right hz (show 0≤(t:ℝ) from Nat.cast_nonneg _)
    rw [Nat.cast_add]
    change _ ≤ -(1-0.05)*(t : ℝ)*N
    rw [← sub_mul]
    exact mul_le_mul_of_nonneg_right (by linarith only [hkz,h1,hg]) (Nat.cast_nonneg _)
  · rw [pr_on]
    exact (div_nonpos_of_nonpos_of_nonneg (not_lt.mp hf) hpos.le).trans (bp_pos _).le

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ImageCharacterBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Image Character Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

variable {r : Place p→ℕ}

theorem tuple_dim :
    dim (DTuple (p:=p) r N)=N*∑ z : Place p,r z := by
  unfold DTuple dim
  rw [finrank_pi_fintype,Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (dim_mat _ _).trans (by simp)

theorem cap_tuple (p : Shape) {n N} (r : Place p → ℕ) (A : WTuple (p:=p) r n)
    (x : Place p ≃ Place p) {w : Wgt (UnitType p n N)} {f : Pin p n N} {ζ : ℝ}
    (h : ∀ z, Function.Injective (A z).mulVec)
    (hf : ∀ z, Disjoint (colSp (A z)) (f.sp (x z)))
    (hw : SubLaw w) (hc : f.clear ζ w) :
    ∀ y, mapW w (projTuple p r A x) y ≤ fee N ζ (∑ z,r z) := by
  classical
  intro y
  let P := fun z : UnitType p n N => projTuple p r A x z=y
  change pr w P ≤ _
  by_cases hP : 0 < pr w P
  · obtain ⟨a,ha,hA⟩ := exists_of_pr_pos hw.nz hP
    let D : Plan p n := fun z => colSp (A (x.symm z))
    let c := Pin.make D a
    have h1 : pr w P ≤ pr w c.agree := by
      refine pr_mono hw.nz fun w hw z t ht => ?_
      change t∈colSp (A (x.symm z)) at ht
      obtain ⟨u,rfl⟩ := ht
      change _ *ᵥ _ = images a z *ᵥ _
      have hh := congr_fun (hw.trans ha.symm) (x.symm z)
      unfold projTuple at hh; rw [x.apply_symm_apply] at hh
      rw [mulVecLin_apply,mulVec_mulVec,mulVec_mulVec,hh]
    have h2 : planNew f.sp D=∑ z,r z := by
      rw [plan_new_disjoint f.sp D]
      · have hh (z) : dim (D z)=r (x.symm z) := (mrk_inj.mp (h (x.symm z))).trans
          (Fintype.card_fin _)
        unfold planRank
        simp_rw [hh]
        exact Equiv.sum_comp _ _
      · intro z
        have hh := hf (x.symm z)
        rw [x.apply_symm_apply] at hh; exact hh.symm
    rw [← h2]
    exact h1.trans (hc c)
  exact (not_lt.mp hP).trans (bp_pos _).le

variable {I J : Type} [Fintype I] [Fintype J]
theorem mpair_nondeg (M : Mat I J) (h : mpair M=0) : M=0 := by
  classical
  apply evmat_ext; intro x y
  rw [←mpair_outer,h]; simp [evmat]

theorem tupleB_val (x y : DTuple (p:=p) r N) :
    tupleB p r N x y=∑ z,mpair (x z) (y z) := by
  simp only [tupleB,LinearMap.sum_apply,LinearMap.coe_mk,AddHom.coe_mk]; rfl

theorem tupleB_inj (p : Shape) (r : Place p→ℕ) (N : ℕ) :
    Function.Injective (tupleB p r N) := by
  classical
  rw [← LinearMap.ker_eq_bot]
  refine le_bot_iff.mp (fun x hx => ?_)
  change tupleB p r N x = 0 at hx
  have hh (z : Place p) : mpair (x z)=0 := by
    refine LinearMap.ext (fun M => ?_)
    have he := LinearMap.congr_fun hx (Pi.single z M)
    rw [tupleB_val,Finset.sum_eq_single z] at he
    · rwa [Pi.single_eq_same] at he
    · intro i _ hi; simp [hi]
    simp
  have h' : x=0 := funext fun z => mpair_nondeg _ (hh z)
  rw [h']; exact Submodule.zero_mem _

theorem charImages (p : Shape) {n N} (r : Place p → ℕ) (A B : WTuple (p:=p) r n)
    {u w : Wgt (UnitType p n N)} (hu : IsLaw u) (hw : IsLaw w) {f b : Pin p n N}
    (hc : f.clear 0.05 u) (hd : b.clear 0.05 w)
    (hA : ∀ z,Function.Injective (A z).mulVec ∧ Disjoint (colSp (A z)) (f.sp z))
    (hB : ∀ z,Function.Injective (B z).mulVec ∧ Disjoint (colSp (B z)) (b.sp (flipZ p z)))
    (hr : 1 ≤ ∑ z,r z) :
    |avg (pairW u w) (fun x => wsign (tupleB p r N (projTuple p r A (Equiv.refl _) x.1)
      (projTuple p r B (flipEquiv p) x.2)))| ≤ bp (-0.45*N) := by
  classical
  let H := tupleB p r N
  let g := projTuple p r A (Equiv.refl _) (N:=N)
  let g' := projTuple p r B (flipEquiv p) (N:=N)
  let q := mapW u g
  let v := mapW w g'
  let t := ∑ i,r i
  have he :
      avg (pairW u w) (fun x => wsign (H (g x.1) (g' x.2))) =
        avg v (fun y => avg q (fun x => wsign (H x y))) := by
    rw [pairW_avg]
    unfold q v
    rw [mapW_avg]
    simp_rw [mapW_avg]
    exact avg_avg ..
  have hp (x) : q x ≤ fee N 0.05 t :=
    cap_tuple p r A (Equiv.refl _) (fun z => (hA z).1) (fun z => (hA z).2) hu.sub hc x
  have hq (x) : v x ≤ fee N 0.05 t :=
    cap_tuple p r B (flipEquiv p) (fun z => (hB z).1) (fun z => (hB z).2) hw.sub hd x
  have hh := walsh_mass H (tupleB_inj p r N) q v (fun _ => 1) (fun _ => 1)
    (fun _ => by norm_num) (fun _ => by norm_num) (mapW_law hu g).sub (mapW_law hw g').sub hp hq
  change |avg (pairW u w) _|≤_
  rw [he]
  let R := avg v (fun y => avg q (fun x => wsign (H x y)))
  have hi : R^2 ≤ (bp (-0.45*N))^2 := by
    simp only [one_mul] at hh
    apply le_trans hh
    rw [card_space,tuple_dim]
    unfold fee
    change bp (↑(N*t))* _ * _ ≤ _
    rw [←bp_add,←bp_add,pow_two,←bp_add]
    apply bp_le
    have h' : 1 ≤ (t:ℝ) := by exact_mod_cast hr
    push_cast
    have hx := mul_le_mul_of_nonneg_left h' (show 0≤(N:ℝ) from Nat.cast_nonneg _)
    linarith only [hx]
  exact le_of_pow_le_pow_left₀ (show (2:ℕ) ≠ 0 by decide) (bp_pos _).le
    (sq_abs R ▸ hi)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GramCharacterQuotients
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gram Character Quotients -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

theorem cpDual_val (A B : Cross p n) :
    cpDual p A B=∑ z,mpair (A z) (B z) := by
  unfold cpDual; rw [LinearMap.sum_apply]; rfl

variable {I J L U : Type} [Fintype I] [Fintype J] [Fintype L] [Fintype U]

private theorem pair_trace (A B : Mat I J) : mpair A B=(A*Bᵀ).trace := by
  change ∑ i:I, ∑ j:J,A i j * B i j = _
  rfl

private theorem pair_transfer (X : Mat U I) (Y : Mat U J) (A : Mat I L) (B : Mat J L) :
    mpair (A*Bᵀ) (Xᵀ*Y)=mpair (X*A) (Y*B) := by
  rw [pair_trace,pair_trace,Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose]
  rw [← Matrix.mul_assoc _ Yᵀ X,Matrix.trace_mul_comm _ X]
  simp only [Matrix.mul_assoc]

private theorem proj_opposite [DecidableEq I] (S : Space (Vec I)) :
    ∃ A : Mat I I,(∀ x,x-A *ᵥ x∈S) ∧ Disjoint (colSp A) S := by
  classical
  obtain ⟨B,hB⟩ := proj_exists S ⊥ disjoint_bot_right
  refine ⟨1-B,fun x => ?_,?_⟩
  · rw [Matrix.sub_mulVec,Matrix.one_mulVec,sub_sub_cancel]
    exact hB.onto x
  rw [disjoint_iff_inf_le]
  rintro x ⟨⟨y,rfl⟩,hy⟩
  rw [mulVecLin_apply,Matrix.sub_mulVec,Matrix.one_mulVec] at hy ⊢
  have hx := hB.fixes _ hy
  rw [Matrix.mulVec_sub,hB.fixes (B *ᵥ y) (hB.onto _),sub_self] at hx
  rw [←hx]; exact Submodule.zero_mem _

private theorem free_pull (p : Shape) {n} (A : Cross p n) (s t : Plan p n) :
    ∃ P : Cross p n,(∀ z, Disjoint (colSp (P z)) (s z) ∧
        Disjoint (colSp (P z)ᵀ) (t (flipZ p z))) ∧
      ∀ X Y, rowAgree s X Y → rowAgree t (reciprocal p X) (reciprocal p Y) →
        cpDual p A (X-Y) = cpDual p P (X-Y) := by
  classical
  choose S hS hL using fun z => proj_opposite (s z)
  choose T hT hR using fun z => proj_opposite (t (flipZ p z))
  let P (z : Place p) := liftM (S z) (T z) (A z)
  refine ⟨P,fun z => ⟨(hL z).mono_left (colSp_lift_le ..),by
    unfold P; rw [liftM_transpose]; exact (hR z).mono_left (colSp_lift_le ..)⟩,fun X Y hX hY => ?_⟩
  rw [cpDual_val,cpDual_val]
  refine Finset.sum_congr rfl fun z _ => ?_
  let M := X z-Y z
  have he : pullM (S z) (T z) M=M := by
    apply evmat_ext; intro x y
    rw [evmat_pull]
    let x' := S z *ᵥ x
    let y' := T z *ᵥ y
    have hL : evmat M (x-x') y=0 := by
      rw [show M=X z-Y z from rfl,evmat_subM,hX z _ (hS z x),sub_self]
    have hR : evmat M x' (y-y')=0 := by
      have h := hY (flipZ p z) _ (hT z y) x'
      simp only [reciprocal,flipZ_flip,evmat_transpose] at h
      rw [show M=X z-Y z from rfl,evmat_subM,h,sub_self]
    unfold evmat at hL hR ⊢
    rw [sub_dotProduct,sub_eq_zero] at hL
    rw [Matrix.mulVec_sub, dotProduct_sub,sub_eq_zero] at hR
    exact hR.symm.trans hL.symm
  change mpair (A z) M=mpair (liftM _ _ _) M
  rw [mpair_comm (A z)]
  rw [mpair_comm (liftM _ _ _),mpair_liftM,show liftM (S z)ᵀ (T z)ᵀ M=M from he]

theorem factor_free {A : Cross p n} (s t : Plan p n)
    (h : ∀ z, Disjoint (colSp (A z)) (s z) ∧ Disjoint (colSp (A z)ᵀ) (t (flipZ p z))) :
    ∃ (r : Place p→ℕ) (B C : WTuple (p:=p) r n), (∀ z,r z=(A z).rank) ∧
      (∀ z,Function.Injective (B z).mulVec ∧ Disjoint (colSp (B z)) (s z)) ∧
      (∀ z,Function.Injective (C z).mulVec ∧ Disjoint (colSp (C z)) (t (flipZ p z))) ∧
      (∀ z,A z=B z * (C z)ᵀ) := by
  classical
  choose B C hB hC hA using fun z => rank_product (A z)
  let G (z : Place p) := (C z)ᵀ
  have ht z : Function.Injective (G z).mulVec :=
    transpose_surj_iff.mp (by unfold G; rw [Matrix.transpose_transpose]; exact hC _)
  refine ⟨_,B,G,fun _ => rfl,fun z => ⟨hB z,(h z).1.mono_left ?_⟩,
     fun z => ⟨ht z,(h z).2.mono_left ?_⟩,
     fun z => by unfold G; rw [Matrix.transpose_transpose,hA]⟩
  · rintro x ⟨v,rfl⟩
    obtain ⟨w,rfl⟩ := hC z v
    refine ⟨w,?_⟩
    rw [mulVecLin_apply,mulVecLin_apply,Matrix.mulVec_mulVec,hA]
  · rintro x ⟨v,rfl⟩
    obtain ⟨w,rfl⟩ := (transpose_surj_iff.mpr (hB z)) v
    refine ⟨w,?_⟩
    rw [mulVecLin_apply,mulVecLin_apply]
    unfold G; rw [Matrix.mulVec_mulVec,← transpose_mul,hA]

theorem gramCharacter (Q M : Cross p n) {u w : Wgt (UnitType p n N)}
    (hu : IsLaw u) (hw : IsLaw w) {f b : Pin p n N}
    (hc : f.clear 0.05 u) (hd : b.clear 0.05 w)
    (h : ∀ x,u x≠0 → ∀ y,w y≠0 → rowAgree f.sp (actual p x y) Q ∧
      rowAgree b.sp (actual p y x) (reciprocal p Q)) :
    let Y := avg (pairW u w) (fun x =>
      wsign (cpDual p M (actual p x.1 x.2-Q)))
    Y=1 ∨ |Y| ≤ bp (-0.45*N) := by
  classical
  dsimp only
  obtain ⟨P,hP,hX⟩ := free_pull p M f.sp b.sp
  obtain ⟨r,B,C,hr,hB,hC,hY⟩ := factor_free f.sp b.sp hP
  let s := pairW u w
  have he :
      avg s (fun x => wsign (cpDual p M (actual p x.1 x.2-Q))) =
      avg s (fun x => wsign (cpDual p P (actual p x.1 x.2-Q))) := by
    refine avg_congr fun ⟨x,y⟩ hxy => ?_
    rw [show cpDual p M (actual p x y-Q)=_ from hX _ _ _ _]
    · exact (h x (left_ne_zero_of_mul hxy) y (right_ne_zero_of_mul hxy)).1
    rw [reciprocal_actual]; exact (h x (left_ne_zero_of_mul hxy) y (right_ne_zero_of_mul hxy)).2
  rw [he]
  by_cases hh : 1≤∑ z,r z
  · right
    let g := projTuple p r B (Equiv.refl _) (N:=N)
    let g' := projTuple p r C (flipEquiv p) (N:=N)
    let X (x : UnitType p n N × UnitType p n N) := tupleB p r N (g x.1) (g' x.2)
    have hi x :
        wsign (cpDual p P (actual p x.1 x.2-Q))=wsign (X x) * wsign (cpDual p P Q) := by
      simp only [ZModModule.sub_eq_add,map_add,wsign_add]
      have hv : cpDual p P (actual p x.1 x.2)=X x := by
        unfold X; rw [cpDual_val,tupleB_val]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [hY,actual,pair_transfer]; rfl
      rw [hv]
    simp_rw [hi]; rw [avg_mul,abs_mul,wsign_abs,mul_one]
    exact charImages p r B C hu hw hc hd hB hC hh
  left
  have hZ z : P z=0 := by
    have hc : r z ≤ ∑ i,r i := Finset.single_le_sum (fun z _ => Nat.zero_le (r z))
      (Finset.mem_univ _)
    rw [hY]
    have hz : r z=0 := by omega
    have : IsEmpty (Fin (r z)) := hz ▸ Fin.isEmpty'
    ext i j; simp [Matrix.mul_apply]
  have hk x : wsign (cpDual p P x)=1 := by
    rw [cpDual_val]
    have hf z : mpair (P z) (x z)=0 := by rw [hZ,mpair_comm,map_zero]
    simp_rw [hf]
    simp
  simp_rw [hk]; exact (pairW_law hu hw).avg_const _

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PrimalChannelTests
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Primal Channel Tests -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

private theorem cp_rep (f : Module.Dual F (Cross p n)) :
    ∃ M : Cross p n,cpDual p M=f := by
  classical
  let B : Cross p n →ₗ[F] Module.Dual F (Cross p n) := {
    toFun := cpDual p
    map_add' := by
      intro x y
      refine LinearMap.ext fun w => ?_
      rw [LinearMap.add_apply]
      simp only [cpDual_val,Pi.add_apply,mpair_add, Finset.sum_add_distrib]
    map_smul' := by
      intro a x
      refine LinearMap.ext fun w => ?_
      rw [LinearMap.smul_apply]
      simp only [cpDual_val,Pi.smul_apply,mpair_smul,RingHom.id_apply,smul_eq_mul,Finset.mul_sum] }
  have hb : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot]
    refine le_bot_iff.mp (fun x hx => ?_)
    have h1 : x = 0 := by
      funext i
      apply mpair_nondeg
      refine LinearMap.ext fun y => ?_
      change cpDual p x=0 at hx
      have h := LinearMap.congr_fun hx (Pi.single i y)
      rw [cpDual_val,Finset.sum_eq_single i] at h
      · rwa [Pi.single_eq_same] at h
      · intro j _ hj; simp [hj]
      simp
    rw [h1]; exact Submodule.zero_mem _
  exact rk_surj.mpr ((rk_inj.mp hb).trans Subspace.dual_finrank_eq.symm) f

theorem indicator_test {V A : Type} [Fintype A] [AddCommGroup V] [Module F V]
    [Fintype V] (s : A → V) (w : Wgt A) (hw : IsLaw w) (ε : ℝ) (he : 0≤ε)
    (hc : ∀ f : Module.Dual F V, let Y := avg w (fun x => wsign (f (s x))); Y=1 ∨ |Y|≤ε) :
    bp (-(dim V:ℝ))- ε ≤ pr w (fun x => s x=0) := by
  classical
  let T := Module.Dual F V
  have : Finite T := Finite.of_injective _ DFunLike.coe_injective
  let : Fintype T := Fintype.ofFinite T
  have h (v : V) : ind (v=0) = avg unif (fun f : T => wsign (f v)) := by
    have h := wsign_lin (Module.evalEquiv F V v)
    rw [map_eq_zero_iff _ (Module.evalEquiv F V).injective] at h
    exact h.symm
  unfold pr
  simp_rw [h]
  rw [avg_avg]
  let E (v : T) := ind (v=0)
  have hE : avg unif E = bp (-(dim V:ℝ)) := by
    change pr unif (fun v : T => v=0)=_
    rw [pr_point',unif_apply,card_space,
      show dim T=dim V from Subspace.dual_finrank_eq,bp_neg]
  rw [← hE,show avg unif E - ε= avg unif (fun v : T => E v-ε) from (by
    rw [avg_sub,unif_law.avg_const])]
  refine avg_mono unif_law.nz fun x => ?_
  by_cases hh : x=0
  · subst x
    change ind (0= (0:T))-ε ≤ avg w (fun _ => wsign 0)
    rw [ind_one rfl,hw.avg_const,wsign_zero]; linarith
  unfold E
  rw [ind_zero hh,zero_sub]
  rcases hc x with hi|hi
  · rw [hi]; linarith
  exact (abs_le.mp hi).1

theorem gram_hit (Q : Cross p n) {u w : Wgt (UnitType p n N)}
    (hu : IsLaw u) (hw : IsLaw w) {f b : Pin p n N}
    (hc : f.clear 0.05 u) (hd : b.clear 0.05 w)
    (h : ∀ x,u x≠0 → ∀ y,w y≠0 → rowAgree f.sp (actual p x y) Q ∧
      rowAgree b.sp (actual p y x) (reciprocal p Q))
    (hN : 100 ≤ N) (hT : (dim (CheckGram p n) : ℝ)≤0.01*N) :
    hit N ≤ pr (pairW u w) (fun x =>
      testgram p (actual p x.1 x.2)=testgram p Q) := by
  classical
  let v := pairW u w
  let s (x : UnitType p n N × UnitType p n N) := testgram p (actual p x.1 x.2 - Q)
  have hh (g : Module.Dual F (CheckGram p n)) :
      let Y := avg v (fun x => wsign (g (s x)))
      Y=1 ∨ |Y|≤bp (-0.45*N) := by
    obtain ⟨M,hM⟩ := cp_rep (g ∘ₗ testgram p)
    have hf x := LinearMap.congr_fun hM x
    have he x : g (s x) = cpDual p M _ := (hf (actual p x.1 x.2-Q)).symm
    dsimp only
    simp_rw [he]
    exact gramCharacter Q M hu hw hc hd h
  have hg := indicator_test s v (pairW_law hu hw) (bp (-0.45*N)) (bp_pos _).le hh
  have he : pr v (fun x => s x=0)=pr v (fun x => testgram p (actual p x.1 x.2)=testgram p Q) := by
    apply congrArg (pr v)
    funext x; apply propext
    unfold s
    have he (A : Cross p n) : testgram p (A+Q) = testgram p A+testgram p Q := (testgram p).map_add' _ _
    rw [show actual p x.1 x.2-Q=actual p x.1 x.2+Q from ZModModule.sub_eq_add ..,he, ← ZModModule.sub_eq_add,sub_eq_zero]
  rw [he] at hg
  refine le_trans ?_ hg
  have hn : 100≤(N:ℝ) := by exact_mod_cast hN
  unfold hit
  have heq := bp_le (show -0.45*N≤-0.02*(N:ℝ) by linarith only [hn])
  have heq' : 2*bp (-0.02*N) ≤ bp (-(dim (CheckGram p n):ℝ)) := by
    rw [← bp_one,← bp_add]; apply bp_le; linarith only [hn,hT]
  linarith only [heq,heq']

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_UnaryRecords
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unary Records -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

theorem ledger_dim (f : Plan p n) :
    dim (Ledger f)=planRank f*Fintype.card (JointIdx p n) := by
  unfold Ledger dim planRank
  rw [finrank_pi_fintype,Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => (dim_mat _ _).trans (by simp)

theorem entries_val (f : Pin p n N) {x y : UnitType p n N} (h : f.agree y)
    (z) : entries f x z= (pack (f.sp z))ᵀ * actual p y x z := by
  have he := Pin.agree_pack.mp h z
  unfold entries actual
  rw [← transpose_mul,← he,transpose_mul,Matrix.mul_assoc]

theorem entries_rows (f : Pin p n N) {x y x' y' : UnitType p n N}
    (h : f.agree y) (h' : f.agree y') (hg : entries f x=entries f x') :
    rowAgree f.sp (actual p y x) (actual p y' x') := by
  intro z u hu v
  have he : (pack (f.sp z))ᵀ * actual p y x z= (pack (f.sp z))ᵀ * actual p y' x' z := by
    rw [←entries_val f h, ←entries_val f h',hg]
  obtain ⟨r,rfl⟩ := (pack_mem_iff ..).mp hu
  have hE (P : Mat (JointIdx p n) (JointIdx p n)) :
      evmat P (pack (f.sp z) *ᵥ r) v=evmat ((pack (f.sp z))ᵀ * P) r v := by
    unfold evmat
    rw [←Matrix.mulVec_mulVec,dotProduct_transpose_mulVec,dotProduct_comm]
  rw [hE,hE,he]

theorem rowAgree_step {a : Plan p n} {X Y Z}
    (h : rowAgree a X Y) (he : rowAgree a Z Y) :
    rowAgree a X Z := fun z u hu v => (h z u hu v).trans (he z u hu v).symm

variable {I : Type} [Fintype I]
namespace Volley
variable (v w : Volley p n I)

private theorem carried_heavy {T : Type} [Fintype T] {w : Wgt T} {p : T→Prop}
    (x) (hx : onW w p x ≠ 0) : p x :=
  Classical.byContradiction fun h => hx (normW_carried (subW_carried w p) x h)

set_option maxHeartbeats 800000 in
theorem record_hit {t : Tagging p I} (m : Mixer p n)
    {a b : Pin p n N} {μ δ : Wgt (UnitType p n N)}
    (U V : UnitType p n N → Prop) (u : Keys (p:=p) t N)
    (ha : ∀ x, U x → a.agree x ∧ (∀ i,frameLaw m (onSide x i)) ∧ v.keys t x=u)
    (hb : ∀ x, V x → b.agree x ∧ (∀ i,frameLaw m (onSide x i)) ∧ w.keys t x=u)
    {ζ : ℝ} {q : ℕ}
    (h : ∀ x,U x → ∀ y,V y → v.promised w t m a.sp b.sp x y)
    (hv : v.avoids a.sp q) (hw : w.avoids b.sp q)
    (hz : ζ ≤ 0.004) (hK : ζ*(kslots p I) ≤ 0.004)
    (hμ : SubLaw μ) (hδ : SubLaw δ)
    (hA : a.clear ζ μ) (hB : b.clear ζ δ)
    (hN : 100 ≤ N) (hT : (dim (CheckGram p n) : ℝ) ≤ 0.01*N)
    (L : ℝ)
    (hLf : bp (dim (Ledger (v.frozen a.sp t))) ≤ L)
    (hLg : bp (dim (Ledger (w.frozen b.sp t))) ≤ L) :
    hit N * (pr μ U * pr δ V) ≤ pr (pairW μ δ) (fun x => U x.1 ∧ V x.2 ∧
      (rawHoles m).conflict x.1 x.2) +
      (hit N*tau N (kslots p I)*L)*(pr μ U+pr δ V) := by
  classical
  let k := kslots p I
  obtain ⟨x0,hx⟩ :
      ∃ x0 : UnitType p n N,∀ x,U x → (Pin.make (v.frozen a.sp t) x0).agree x := by
    by_cases he : ∃ x,U x
    · obtain ⟨x0,hx0⟩ := he
      exact ⟨x0,fun x hx => key_pin t (ha x0 hx0).1 (ha x hx).1
        ((ha x0 hx0).2.2.trans (ha x hx).2.2.symm)⟩
    exact ⟨0,fun x h => (he ⟨x,h⟩).elim⟩
  let f := Pin.make (v.frozen a.sp t) x0
  obtain ⟨y0,hy⟩ :
      ∃ y0 : UnitType p n N,∀ y,V y → (Pin.make (w.frozen b.sp t) y0).agree y := by
    by_cases he : ∃ y,V y
    · obtain ⟨y0,hy0⟩ := he
      exact ⟨y0,fun y hy => key_pin t (hb y0 hy0).1 (hb y hy).1
        ((hb y0 hy0).2.2.trans (hb y hy).2.2.symm)⟩
    exact ⟨0,fun y h => (he ⟨y,h⟩).elim⟩
  let g := Pin.make (w.frozen b.sp t) y0
  apply prune_pairs μ δ hμ hδ U V (entries g) (entries f)
    (fun x => (rawHoles m).conflict x.1 x.2) (hit N) (tau N k)
    (bp_pos _).le (bp_pos _) _ _
  · intro i j hi hj
    let F := memberC U (entries g) i
    let G := memberC V (entries f) j
    let α := onW μ F
    let β := onW δ G
    change tau N k≤pr μ F at hi
    change tau N k≤pr δ G at hj
    have hL (v : Volley p n I) {a} (h : v.avoids a q) :
        planRank (v.frozen a t)=planRank a+k := by
      unfold k
      rw [← v.key_slots (t:=t) h]; exact (plan_add_rank a (v.keyPlan t)).symm
    obtain ⟨hα,hF⟩ := in_clear (f:=f) hz hK hμ hA le_sup_left (hL v hv)
      F (fun x h => hx x h.1) hi
    obtain ⟨hβ,hG⟩ := in_clear (f:=g) hz hK hδ hB le_sup_left (hL w hw)
      G (fun x h => hy x h.1) hj
    obtain ⟨x,xX,_⟩ := exists_of_pr_pos hμ.nz (lt_of_lt_of_le (bp_pos _) hi)
    obtain ⟨y,yY,_⟩ := exists_of_pr_pos hδ.nz (lt_of_lt_of_le (bp_pos _) hj)
    have h1 x (h : α x≠0) : F x := carried_heavy _ h
    have h2 y (h : β y≠0) : G y := carried_heavy _ h
    obtain ⟨hr,ht,hL,Q,hZ,hI,hQ,hQ'⟩ := h x xX.1 y yY.1
    have he x' (hs : α x'≠0) y' (hs' : β y'≠0) :
        rowAgree f.sp (actual p x' y') Q ∧
        rowAgree g.sp (actual p y' x') (reciprocal p Q) := by
      have ha := h1 x' hs
      have hb := h2 y' hs'
      exact ⟨rowAgree_step (entries_rows f (hx x' ha.1) (hx x xX.1) (hb.2.trans yY.2.symm)) hQ,
        rowAgree_step (entries_rows g (hy y' hb.1) (hy y yY.1) (ha.2.trans xX.2.symm)) hQ'⟩
    refine (gram_hit Q hα hβ hF hG he hN hT).trans (pr_on_mono (pairW_law hα hβ).nz ?_)
    rintro ⟨x,y⟩ hxy heq
    obtain ⟨_,hx,hX⟩ := ha x (h1 x (left_ne_zero_of_mul hxy)).1
    obtain ⟨_,hy,hY⟩ := hb y (h2 y (right_ne_zero_of_mul hxy)).1
    have he : scalarBlocks p (actual p x y) = scalarBlocks p Q := congrArg Prod.fst heq
    have he' : scalarBlocks p (actual p y x) = scalarBlocks p (reciprocal p Q) := by
      rw [← reciprocal_actual x y]; exact congrArg Prod.snd heq
    apply v.realized_conflicts w m x y hr ht hx hy (hX.trans hY.symm) hL
    · intro i j μ hμ; rw [contract_scalars _ _ he]; exact hZ i j _ hμ
    · intro i j μ hμ; rw [contract_scalars _ _ he']; exact hI i j _ hμ
  · rw [card_space]; exact hLg
  rw [card_space]; exact hLf
end Volley
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CollisionInequality
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Collision Inequality -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Finset Filter
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
variable {I A B : Type} [Fintype I] [Fintype A] [Fintype B]

theorem overlap_count (P : I→Prop) (p q : Wgt I) (h : ∀ x, 0 ≤ p x) (h' : ∀ x, 0≤ q x) :
    overlap (unifOn P) p q ≤ (Fintype.card I:ℝ) * (∑ i, p i*q i) := by
  classical
  simp only [overlap,density, avg,Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hg := mul_nonneg (h i) (h' i)
  have hw : 0 ≤ (↑(Fintype.card I) : ℝ) := Nat.cast_nonneg _
  by_cases he : P i
  · have hh : 0 < nbr P := by
      have hpos : 0 < Fintype.card {x//P x} := Fintype.card_pos_iff.mpr ⟨⟨i,he⟩⟩
      rw [nbr_eq_card]; exact_mod_cast hpos
    have hd : unifOn P i * (p i/unifOn P i * (q i / unifOn P i))=nbr P*(p i*q i) := by
      rw [unifOn_val,ind_one he]
      field_simp
    rw [hd]
    apply mul_le_mul_of_nonneg_right _ hg
    rw [nbr_eq_card]
    exact_mod_cast Fintype.card_le_of_injective _ (@Subtype.val_injective _ P)
  rw [unifOn_carried P i he,zero_mul]
  exact mul_nonneg hw hg

namespace Volley

set_option maxHeartbeats 800000 in
private theorem record_sum (v w : Volley p n I) {t : Tagging p I} (m : Mixer p n)
    {a b : Pin p n N} {μ δ : Wgt (UnitType p n N)}
    (U V : UnitType p n N → Prop)
    (ha : ∀ x, U x → a.agree x ∧ (∀ i,frameLaw m (onSide x i)))
    (hb : ∀ x, V x → b.agree x ∧ (∀ i,frameLaw m (onSide x i)))
    {ζ : ℝ} {q : ℕ}
    (h : ∀ x,U x → ∀ y,V y → v.keys t x=w.keys t y → v.promised w t m a.sp b.sp x y)
    (hv : v.avoids a.sp q) (hw : w.avoids b.sp q)
    (hz : ζ ≤ 0.004) (hK : ζ*(kslots p I) ≤ 0.004)
    (hμ : SubLaw μ) (hδ : SubLaw δ)
    (hA : a.clear ζ μ) (hB : b.clear ζ δ)
    (hN : 100 ≤ N) (hT : (dim (CheckGram p n) : ℝ) ≤ 0.01*N)
    (L : ℝ)
    (hLf : bp (dim (Ledger (v.frozen a.sp t))) ≤ L)
    (hLg : bp (dim (Ledger (w.frozen b.sp t))) ≤ L) :
    hit N *
      (∑ u : Keys (p:=p) t N, pr μ (fun x => U x ∧ v.keys t x=u) *
        pr δ (fun x => V x ∧ w.keys t x=u)) ≤
      pr (pairW μ δ) (fun x => (rawHoles m).conflict x.1 x.2)+
      2*(hit N*tau N (kslots p I)*L) := by
  classical
  let X := UnitType p n N
  let T := Keys (p:=p) t N
  let K (u : T) (x : X) := U x ∧ v.keys t x=u
  let K' (u : T) (x : X) := V x ∧ w.keys t x=u
  let H := hit N*tau N (kslots p I)*L
  let P := pairW μ δ
  let C (x : X × X) := (rawHoles m).conflict x.1 x.2
  let G (u : T) (x : X × X) := K u x.1 ∧ K' u x.2 ∧ C x
  rw [Finset.mul_sum]
  have hh (i : Keys (p:=p) t N) :
      hit N * (pr μ (K i) * pr δ (K' i))≤ pr P (G i)+H*(pr μ (K i)+pr δ (K' i)) := by
    apply record_hit v w m (K i) (K' i) i _ _ _ hv hw hz hK hμ hδ hA hB hN hT L hLf hLg
    · exact fun x h => ⟨(ha x h.1).1,(ha x h.1).2,h.2⟩
    · exact fun x h => ⟨(hb x h.1).1,(hb x h.1).2,h.2⟩
    exact fun x hx y hy => h x hx.1 y hy.1 (hx.2.trans hy.2.symm)
  refine (Finset.sum_le_sum fun i _ => hh i).trans ?_
  rw [Finset.sum_add_distrib]
  have hi : (∑ i : Keys (p:=p) t N, pr P (G i)) ≤ pr P C := by
    rw [← sum_pr_tag P C (v.keys t ∘ Prod.fst)]
    exact Finset.sum_le_sum fun i _ => pr_mono (subLaw_pair hμ hδ).nz (fun x h => ⟨h.2.2,h.1.2⟩)
  refine add_le_add hi ?_
  have hU : (∑ i : Keys (p:=p) t N, pr μ (K i))≤1 :=
    (sum_pr_tag μ U (v.keys t)).trans_le ((pr_le_tot hμ.nz).trans hμ.total)
  have hV : (∑ i : Keys (p:=p) t N, pr δ (K' i))≤1 :=
    (sum_pr_tag δ V (w.keys t)).trans_le ((pr_le_tot hδ.nz).trans hδ.total)
  have hz : 0 ≤ H := mul_nonneg (mul_nonneg (bp_pos _).le (bp_pos _).le) ((bp_pos _).le.trans hLf)
  rw [← Finset.mul_sum,Finset.sum_add_distrib,mul_comm 2]
  exact mul_le_mul_of_nonneg_left (by linarith only [hU,hV]) hz

set_option maxHeartbeats 1200000 in
theorem collision (v : A→Volley p n I) (w : B→Volley p n I)
    {t : Tagging p I} (m : Mixer p n)
    {a b : Pin p n N} {μ δ : Wgt (UnitType p n N)}
    (rhoA : Wgt A) (rhoB : Wgt B)
    (U : A → UnitType p n N → Prop) (V : B → UnitType p n N → Prop)
    (ha : ∀ i x, U i x → a.agree x ∧ (∀ i,frameLaw m (onSide x i)))
    (hb : ∀ i x, V i x → b.agree x ∧ (∀ i,frameLaw m (onSide x i)))
    {ζ : ℝ} {q K : ℕ}
    (h : ∀ i j x,U i x → ∀ y,V j y → (v i).keys t x=(w j).keys t y →
      (v i).promised (w j) t m a.sp b.sp x y)
    (hv : ∀ i, (v i).avoids a.sp q) (hw : ∀ i, (w i).avoids b.sp q)
    (hκ : planRank a.sp≤K) (hκ' : planRank b.sp≤K)
    (hz : ζ ≤ 0.004) (hK : ζ*(kslots p I) ≤ 0.004) (hslots : kslots p I≤kmax p)
    (hμ : SubLaw μ) (hδ : SubLaw δ) (hu : SubLaw rhoA) (hu' : SubLaw rhoB)
    (hA : a.clear ζ μ) (hB : b.clear ζ δ)
    (hN : 100 ≤ N) (hT : (dim (CheckGram p n) : ℝ) ≤ 0.01*N)
    (hL : (K+(kmax p:ℝ))*num (JointIdx p n) ≤ 0.005*N)
    (J : Keys (p:=p) t N → Prop) :
    overlap (unifOn J) (hist v t μ rhoA U) (hist w t δ rhoB V) ≤
      bp (((kslots p I:ℝ)+0.02)*N)*pr (pairW μ δ) (fun x =>
        (rawHoles m).conflict x.1 x.2) + 2*bp (-0.005*N) := by
  classical
  let k := kslots p I
  let L := bp (0.005*N)
  let C := fun (x : UnitType p n N × _) => (rawHoles m).conflict x.1 x.2
  let X := hist v t μ rhoA U
  let Y := hist w t δ rhoB V
  let H := hit N*tau N k*L
  let D := pr (pairW μ δ) C
  let α (u : Keys (p:=p) t N) i := pr μ (fun x => U i x ∧ (v i).keys t x=u)
  let β (u : Keys (p:=p) t N) i := pr δ (fun x => V i x ∧ (w i).keys t x=u)
  have hX u : 0≤ X u := avg_nonneg hu.nz (fun i => pr_nonneg hμ.nz)
  have hY u : 0≤ Y u := avg_nonneg hu'.nz (fun i => pr_nonneg hδ.nz)
  have hW (f : Plan p n) (hk : planRank f ≤ K) (v : Volley p n I) (hv : v.avoids f q) :
      bp (dim (Ledger (v.frozen f t)))≤L := by
    apply bp_le
    rw [ledger_dim]
    push_cast
    have ht : (planRank (v.frozen f t) : ℝ) ≤ K+(kmax p:ℝ) := by
      have hh := plan_add_rank f (v.keyPlan t)
      rw [key_slots t hv] at hh
      exact_mod_cast (show planRank (f⊔v.keyPlan t) ≤ K+kmax p from
        hh.symm ▸ add_le_add hk hslots)
    exact le_trans (mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg _)) hL
  have hf (x : A × B) :
      hit N * (∑ u : Keys (p:=p) t N, α u x.1*β u x.2) ≤ D+ 2*H :=
    record_sum (v x.1) (w x.2) m (U _) (V _) (ha x.1) (hb x.2) (h x.1 x.2)
      (hv x.1) (hw x.2) hz hK hμ hδ hA hB hN hT L (hW a.sp hκ _ (hv _)) (hW _ hκ' _ (hw _))
  have hh : hit N * (∑ u : Keys (p:=p) t N,X u * Y u) ≤ D + 2*H := by
    let F := pairW rhoA rhoB
    have hh' : 0 ≤ D+2*H := by
      apply add_nonneg (pr_nonneg (subLaw_pair hμ hδ).nz)
      exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (bp_pos _).le (bp_pos _).le)
        (bp_pos _).le)
    have hl := (subLaw_pair hu hu').avg_le hh' hf
    rw [avg_mul',avg_sum] at hl
    have ht (u : Keys (p:=p) t N) :
        X u*Y u=avg F (fun x : A×B => α u x.1*β u x.2) := (pairW_separate ..).symm
    simp_rw [ht]; exact hl
  apply (overlap_count J X Y hX hY).trans
  rw [card_space,dim_keys,Nat.cast_mul]
  let Z := bp (((k:ℝ)+0.02)*N)
  have he : Z*hit N = bp ((k:ℝ)*N) := by
    unfold Z hit; rw [← bp_add]; congr 1; ring
  have he' : Z*H = bp (-0.005*N) := by
    unfold H; rw [← mul_assoc,← mul_assoc,he]
    unfold L tau
    rw [← bp_add,← bp_add]; congr 1; ring
  change bp ((k:ℝ)*N)*_≤ Z*D+_
  rw [← he, mul_assoc,← he']
  refine (mul_le_mul_of_nonneg_left hh (bp_pos _).le).trans_eq ?_
  ring
end Volley

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

theorem etaScan (p : Shape) {n} (l s f) (x : Knobs p.g n) :
    (scan p l f x).sumBit=eta p n (mom p s (lit f l x)) := by
  simp only [Digest.sumBit,Digest.diagO,eta,etaO,LinearMap.add_apply,LinearMap.sum_apply]
  simp_rw [scan_is p l s]
  rfl

theorem spins_law (p : Shape) (n : ℕ) : IsLaw (spins p n) := draws_law unif_law

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

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BoundedQueryTemplates
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded Query Templates -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Function
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

namespace Template
variable (v : Template p I)

omit [Fintype I] [DecidableEq I] in
theorem draw_legal (y : Inputs p n I) : (v.draw y).legal v.t :=
  fun _ => lit_allows _ _ _
end Template

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_DependentPairConcentration
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dependent Pair Concentration -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset Function
open scoped BigOperators
variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

omit [Fintype A] [Fintype B] in
theorem mix_data (f : X → Wgt A) (g : Y → Wgt B) (u : Wgt X) (v : Wgt Y) :
    mixW (pairW u v) (fun x => pairW (f x.1) (g x.2))=pairW (mixW u f) (mixW v g) := by
  classical
  funext i
  unfold mixW
  exact pairW_separate u (fun j => f j i.1) v (fun j => g j i.2)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_TesterFourierSupport
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tester Fourier Support -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Submodule Function LinearMap Finset
open scoped BigOperators
variable {p : Shape} {n : ℕ}

theorem roleT_scan (p : Shape) (i l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (x : Knobs p.g n) :
    roleT p n i (useAtom p l s f x) = ∑ d:Tag p.g,scan p l f x (.inl (d,i)) := by
  classical
  unfold useAtom atom
  let M := mom p s (lit f l x)
  have h (t : Tag p.g) : (Pi.single l M : Tag p.g→ Moment p n) t ∈Wtag p n t := by
    by_cases ht : t=l
    · subst t; rw [Pi.single_eq_same]; exact Submodule.subset_span ⟨_,_,lit_allows f l x,rfl⟩
    simp [ht]
  rw [roleT_cut p i _ h,Finset.sum_eq_single l,Pi.single_eq_same]
  · simp_rw [scan_is p l s]; rfl
  · intro i _ hi; simp [hi]
  simp

theorem sharedT_scan (p : Shape) (hg : Odd p.g) (i l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (x : Knobs p.g n) :
    let r := scan p l f x (.inr ())
    sharedT p n i (useAtom p l s f x)= r+(if l=i then r else 0) := by
  classical
  intro r
  unfold r useAtom atom
  rw [sharedT_cut _ hg,Finset.sum_eq_single l]
  · rw [Pi.single_eq_same,scan_is p l s f]; by_cases h : i=l <;> simp [h,asBlock,Ne.symm]
  · intro i _ hi; simp [hi]
  simp

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_StatusRecipes
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Status Recipes -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function LinearMap Module Submodule
open scoped BigOperators
namespace StatusAnalysis
variable {p : Shape} {n N : ℕ} {q : Format} {d e : Rates}

theorem funds_reg (t : Tagging p (Messenger q)) (b : Bool) (v : Charts p n d)
    (m : Mixer p n) (o : UnitType p n N) (l f x) (a : Amounts p q d b)
    (h : printed b v t l f m o x=a) (i : Grid) :
    let j := sendId b i
    let w := (manager b t l f).draw x
    funds a i = registers p j (v j) m o (unionAt (w.atomAt t) i) := by
  rw [←h]; intro j w
  unfold funds unionAt
  rw [map_sum]
  rfl

theorem sumAtSend (b : Bool) (w : Volley p n (Messenger q)) (t : Tagging p (Messenger q))
    (i : Grid) (h : w.obj=parcel b) :
    w.sumAt t (parcel (!b)) (sendId b i) (sendId (!b) i)=unionAt (w.atomAt t) i :=
  sum_shots b w _ h _

set_option maxHeartbeats 800000 in
theorem still_recipe (t : Tagging p (Messenger q)) (b : Bool) (S : Plan p n)
    (M : Cross p n) (v : Charts p n d) (ha : charted v S)
    (m : Mixer p n) (o : UnitType p n N) (l f x) (a : Amounts p q d b)
    (h : printed b v t l f m o x=a)
    (w : Volley p n (Messenger q)) (hw : w.obj=parcel (!b))
    (z : Messenger q→F) (hz : owing p b a z) (hq : ∀ i,fullq z i=1)
    (hh : still b a v M) :
    let u:=(manager b t l f).draw x
    u.scalarRecipe w t m o S M := by
  classical
  intro u
  have hi := funds_reg t b v m o l f x a h
  have ho : u.obj=parcel b := rfl
  have he (i j) (t : Grid) (h : t=transit b (i,j)) : sendId b t=i ∧ sendId (!b) t=j := by
    have hh := (sendPair b t).trans (show transit b t=(i,j) by rw [h,transit_inv])
    exact ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩
  have ht (i j) : u.sumAt t w.obj i j=unionAt (u.atomAt t) (transit b (i,j)) := by
    obtain ⟨h1,h2⟩ := he i j _ rfl
    rw [hw,←sumAtSend b u t _ ho,h1,h2]
  have hd i j :
      ((innerP p o i)+role p n) (u.sumAt t w.obj i j)=
        couple _ (funds a (transit b (i,j))) := by
    rw [ht,hi]
    let W:= unionAt (u.atomAt t) (transit b (i,j))
    change innerP p o i W+role p n W=role p n W+innerP p o (sendId b _) W
    rw [(he _ _ _ rfl).1,add_comm]
  constructor
  · have hu (i) : u.diagonalAt i=z i :=
      (etaScan p (t i) (l i) (f i) (x i)).symm.trans (by
        rw [← h] at hz; exact hz i)
    intro i j
    obtain ⟨h1,h2⟩:= he i j _ rfl
    let T:= transit b (i,j)
    simp_rw [hu]
    have hm:=sum_shots b u (transit b (i,j)) ho z
    rw [h1,h2,←hw] at hm; exact hm.trans (hq T)
  · intro j; rw [hd,hd, hh.2]
  intro i j z hz
  let Z := transit b (i,j)
  obtain ⟨h1,h2⟩ : sendId b Z=i ∧ sendId (!b) Z=j := he _ _ _ rfl
  let t':=sendId b Z
  obtain ⟨y,hy⟩ : z ∈ LinearMap.range (v t') := by rw [(ha _).1]; rwa [show t'=i from h1]
  have hg := hh.1 Z
  rw [hi] at hg
  let W:= unionAt (u.atomAt t) Z
  have hh : Tsym m W z=contract p M i j z + role p n z := by
    change roll (v t') (Tsym m W)=roll (v t') (contract p M t' (sendId (!b) Z) + _) at hg
    have ht := congrArg (fun x=>dotProduct x y) hg
    simp_rw [←roll_project,hy] at ht
    change Tsym m W z=contract p M _ _ z+_ at ht
    rwa [show t'=i from h1,h2] at ht
  rw [ht,grad_val,hh,add_left_comm,char_two,add_zero]

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

theorem tmill_formula {b} (t : Tagging p (Messenger q)) (hg : Odd p.g) (v : Charts p n d)
    (l f) (x : Inputs p n (Messenger q)) (m : Mixer p n) (o : UnitType p n N)
    (a : Amounts p q d b) (h : printed b v t l f m o x=a) (i j : Messenger q) :
    T0 p n (useAtom p (t i) (l i) (f i) (x i)) (useAtom p (t j) (l j) (f j) (x j)) =
      TMill p t a i j := by
  classical
  rw [← h]
  simp_rw [T0_val, roleT_scan,sharedT_scan _ hg]
  rfl

theorem procl_grad (t : Tagging p (Messenger q))
    {b} (a : Amounts p q d b) (w : Amounts p q e (!b))
    (hg : Odd p.g) (v : Charts p n d) (v' : Charts p n e)
    (l f l' f') (x y : Inputs p n (Messenger q))
    (m : Mixer p n) (o z : UnitType p n N)
    (h : printed b v t l f m o x=a) (hz : printed (!b) v' t l' f' m z y=w)
    (s : Script p (Messenger q)) (hs : proclaims p a w t s) :
    let u:=(manager b t l f).draw x
    u.reads s m → u.attackGrad ((manager (!b) t l' f').draw y) t m z := by
  intro u hu
  apply Volley.grads_by_script (v:=u) t m ((manager (!b) t l' f').draw y) z (d:=mailRole a) (f:=mailBias w) (u:=TMill p t a) (s:=s) hs hu
  · rw [← h]; intro; rfl
  · rw [←hz]; intro; rfl
  exact tmill_formula t hg v l f x m o a h

set_option maxHeartbeats 600000 in
theorem rhyme_match (t : Tagging p (Messenger q)) (a : Amounts p q d true)
    (w : Amounts p q e false)
    (v : Charts p n d) (v' : Charts p n e)
    (l f l' f') (x y : Inputs p n (Messenger q))
    (m : Mixer p n) (o z : UnitType p n N)
    (h : printed true v t l f m o x=a) (hz : printed false v' t l' f' m z y=w)
    (he : rhyme a w) :
    let u:=(manager true t l f).draw x
    u.roleMatch ((manager false t l' f').draw y) t := by
  classical
  intro u i j
  let q:= (i,j)
  let s:= (manager false t l' f').draw y
  have hh : u.sumAt t s.obj i j=unionAt (u.atomAt t) (i,j) :=
    sumAtSend true u t (i,j) rfl
  have hf : s.sumAt t u.obj j i=unionAt (s.atomAt t) (i,j) := sumAtSend false s t (i,j) rfl
  change _ + role _ _ (s.sumAt _ _ _ _)=_
  rw [hh,hf]
  specialize he (i,j)
  change (funds a (i,j)).1.1+(funds w (i,j)).1.1=1 at he
  rw [funds_reg t true v m o l f x a h,funds_reg t false v' m z l' f' y w hz] at he
  exact he
end StatusAnalysis
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

namespace ExpSmall
theorem bp_n {c : ℝ} (hc : 0 < c) : ExpSmall l z (fun n=>bp (-c*z n)) :=
  ⟨_,hc,.of_forall (fun _ => (abs_of_pos (bp_pos _)).le)⟩

end ExpSmall

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

variable {s : LeafMixture p n N} {w μ : Wgt (X p n N)}
variable {D E ζ η : ℝ} {K L : ℕ}

theorem sapLaw (h : 0 < s.amount w) (hw : IsLaw w) : IsLaw (s.sap w) := on_law hw.nz h

theorem upper_sap (hw : IsLaw w) (hp : 0 < s.amount w) (x) :
    s.sap w x ≤ (s.amount w)⁻¹*w x :=
  on_mon hw.nz hp le_rfl x

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

namespace Quill
variable {b : Bool} (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)

theorem canDraw {w : Quill p q d b} (h : w.moral t z) (i : Messenger q) :
    canDial p (t i) (w.flav i) (z i) :=
  ⟨_,h.2.2 i,h.2.1 i⟩

end Quill

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PairedCollisionBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Paired Collision Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Finset Submodule Filter
open scoped BigOperators Topology
namespace StatusAnalysis
variable {p : Shape} {n N K : ℕ} {q : Format} {d e : Rates}

theorem quillState {i : Bool} {w : Quill p q d i} {t z} (h : w.moral t z) (hr : 1≤p.r)
    (hn : 2*p.r ≤ n) :
    IsLaw ((w.pen t).state z n) := prodW_law (fun j=> dial_law p n _ _ _ hr hn (Quill.canDraw _ _ h j))

namespace Station
variable {s : LeafMixture p n N} (v : Station p n N K s)

set_option maxHeartbeats 1400000 in
theorem sellPoint (w : Typus p q d e)
    (m :Mixer p n) (μ : Wgt (UnitType p n N)) (i j : s.T) (k : Fin (2^deckMax p K))
    {C ζ : ℝ} (hp : s.strength μ (PreparationParameters.usual p m N) C ζ K) (hw : IsLaw μ)
    (he : earnsScore p n N K ζ) :
    matchScore v w m μ i j k ≤ beamPrice p N *
      pr (pairW (partW μ i.val) (partW μ j.val)) (clash p m N)+2* bp (-0.005*N) := by
  classical
  have hA := hp.leaf i.val i.property; have hB := hp.leaf j.val j.property
  let a:=w.qA.pen w.t; let b:=w.qB.pen w.t
  let ia:=s.pin i.val; let ib:=s.pin j.val
  let u:=partW μ i.val; let u':=partW μ j.val
  let F:=frontPage v w m i j k; let G:=backPage v w m i j k
  let T:=v.mails i j k; let x:=v.cAxes i d; let y:=v.cAxes j e
  let Q (z : Inputs p n (Messenger q)) (o : UnitType p n N) :=
    F o ∧ w.qA.deposit w.t w.z m o x z
  let R (z : Inputs p n (Messenger q)) (o : UnitType p n N) :=
    G o ∧ w.qB.deposit w.t w.z m o y z
  have hu : IsLaw u:= on_law hw.nz hA.pos
  have hu' : IsLaw u':= on_law hw.nz hB.pos
  let δ := pr (pairW u u') (clash p m N)
  have hδ : 0≤δ := pr_nonneg (pairW_law hu hu').nz
  change overlap (lawNu p N w.t w.z)
    (Volley.hist a.draw w.t u (a.state w.z n) Q) (Volley.hist b.draw w.t u' (b.state w.z n) R) ≤
      beamPrice p N*δ+ _
  by_cases hg : news v w i j k
  · obtain ⟨⟨hf,hE,hF,hQ,hR,hr,hr'⟩,⟨hX,ha,hS,hT⟩,hY,hb,hS',hT'⟩:=hg
    have hq : kslots p (Messenger q) ≤ kmax p :=
      slots_budget (a.draw (n:=n) (fun _=>0)) (shots_ok true (a.draw (fun _ => 0)) rfl hf)
    apply le_trans (Volley.collision a.draw b.draw m (a:=ia) (b:=ib) (q:=qorth K) (K:=K)
      (a.state w.z n) (b.state w.z n) Q R (fun i x (h:Q i x)=> ⟨h.1.2.1,h.1.2.2.1⟩)
      (fun i x (h:R i x)=>⟨h.1.2.1,h.1.2.2.1⟩)
      _ ha hb hA.bound hB.bound he.low (le_trans
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hq) he.smooth) he.light) hq hu.sub hu'.sub
      (quillState hE he.hr he.hn).sub (quillState hF he.hr he.hn).sub hA.clear hB.clear
      he.hN he.gram he.budget (ownPart w.t w.z))
    · refine add_le_add_left (mul_le_mul_of_nonneg_right (bp_le ?_) hδ) _
      exact mul_le_mul_of_nonneg_right (add_le_add_left (Nat.cast_le.mpr hq) _) (by positivity)
    intro u v o ho z hz hv
    have h1 (u:Inputs p n (Messenger q)) (v:Inputs p n (Messenger q)) : (a.draw u).bounded
        (b.draw v).obj := shots_ok true _ rfl hf
    have h2 (u:Inputs p n (Messenger q)) (v:Inputs p n (Messenger q)) : (b.draw v).bounded
        (a.draw u).obj := shots_ok false _ rfl hf
    obtain ⟨⟨_,ha',ha0,ham⟩,hG,hh',_⟩:= ho
    obtain ⟨⟨_,hb',hb0,hbm⟩,hH,hh0,_⟩:= hz
    refine ⟨a.draw_legal _, b.draw_legal _,rhyme_match _ _ _ x y _ _ _ _ u v m o z hG hH hR,?_⟩
    apply gradient_realization (a.draw u) (b.draw v) m o z ia ib T K he.solid (h1 u v) (h2 u v)
      (a.draw_legal _) (b.draw_legal _) (ha _) (hb _) hA.bound hB.bound ha' hb' ham hbm hT hT'
      _ _ hv ha0 hb0 _ _
    · exact still_recipe _ true _ _ _ hX _ _ _ _ _ _ hG _ rfl w.z hE.2.1 hQ hS
    · exact still_recipe _ false _ _ _ hY _ _ _ _ _ _ hH _ rfl w.z hF.2.1 hQ hS'
    · exact procl_grad _ _ _ he.solid.odd _ _ _ _ _ _ _ _ m _ _ hG hH w.qA.script hr hh'
    exact procl_grad _ _ _ he.solid.odd _ _ _ _ _ _ _ _ m _ _ hH hG w.qB.script hr' hh0
  · have hh (x): Volley.hist a.draw w.t u (a.state w.z n) Q x=0 := by
      unfold Volley.hist
      have ht y : pr u (fun i=> Q y i ∧ (a.draw y).keys w.t i=x)=0 := by
        simp [Q,F,frontPage,notified,hg,pr_false]
      simp_rw [ht] <;> simp
    unfold overlap
    simp only [density,hh,zero_div,zero_mul]
    have hz : 0≤ beamPrice p N*δ:=mul_nonneg (bp_pos _).le hδ
    rw [show avg (lawNu p N w.t w.z) (fun _ => 0) = 0 from (by simp only [avg_const,mul_zero])]
    exact add_nonneg hz (mul_nonneg (by norm_num) (bp_pos _).le)

set_option maxHeartbeats 800000 in
theorem arena_bound (w : Typus p q d e)
    (m: Mixer p n) (μ : Wgt (UnitType p n N)) (k : Fin (2^deckMax p K))
    {C ζ : ℝ} (hp : s.strength μ (PreparationParameters.usual p m N) C ζ K) (hw : IsLaw μ)
    (h : 0 < s.amount μ) (he : earnsScore p n N K ζ) :
    arena v w m μ k ≤ beamPrice p N *
      pr (pairW (s.sap μ) (s.sap μ)) (clash p m N)+ 2*bp (-0.005*N) := by
  classical
  obtain ⟨hx,hy⟩:=rebuild hw.nz hp.part (fun i hi=>(hp.leaf _ hi).pos) h
  let t:=portionW μ s.T
  let S := pairW t t
  have hm : IsLaw S:=pairW_law hx hx
  refine (avg_mono hm.nz (fun x=>sellPoint v w m μ x.1 x.2 k hp hw he)).trans_eq ?_
  rw [avg_add,avg_mul',hm.avg_const]
  change s.sap μ=_ at hy
  rw [hy,←mix_data]
  unfold pr
  congr 1; rw [mixW_avg]

end Station
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PairedMassIdentities
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Paired Mass Identities -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Finset Submodule Filter
open scoped BigOperators Topology
namespace StatusAnalysis
variable {p : Shape} {n N K M: ℕ} {q : Format} {d e : Rates}

namespace Quill
variable {i:Bool} (w : Quill p q d i)
    (μ : Wgt (UnitType p n N)) (s : Charts p n d)
    (t : Tagging p (Messenger q)) (z : Messenger q → F)
    (m : Mixer p n)
    (P : UnitType p n N→Prop)

theorem sales_pos (h : ∀ x,0≤μ x) (x) : 0≤ w.sales t z μ P m s x :=
  avg_nonneg (prodW_nonneg (fun _=> normW_nonneg (subW_nonneg (spins_law ..).nz _)))
    (fun _=> pr_nonneg h)
end Quill

namespace Station
variable {s : LeafMixture p n N} (v : Station p n N K s)

theorem arena_pos (w : Typus p q d e)
    (m: Mixer p n) (μ : Wgt (UnitType p n N)) (k : Fin (2^deckMax p K))
    (h : 0 < s.amount μ) (hw : IsLaw μ) : 0 ≤ arena v w m μ k := by
  classical
  have hf (i:s.T) : 0≤portionW μ s.T i := div_nonneg (pr_nonneg hw.nz) h.le
  have hg (S : CTile p n N) i : 0≤partW μ S i := normW_nonneg (subW_nonneg hw.nz _) _
  refine avg_nonneg (fun _=>mul_nonneg (hf _) (hf _)) (fun i=>avg_nonneg
    (unifOn_sub _).nz (fun x=>mul_nonneg ?_ ?_))
  · exact div_nonneg (w.qA.sales_pos _ _ _ _ m _ (hg _) x) ((unifOn_sub _).nz _)
  exact div_nonneg (w.qB.sales_pos _ _ _ _ m _ (hg _) x) ((unifOn_sub _).nz _)

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

theorem beam_cost (p : Shape) (N : ℕ) (h : 3≤p.g) :
    beamPrice p N * bp (-100*p.g*(N:ℝ)) ≤ bp (-(N:ℝ)) := by
  unfold beamPrice; rw [←bp_add]; refine bp_le ?_
  have hh : kmax p ≤56*p.g := by unfold kmax; omega
  have ht : (kmax p:ℝ)≤56*p.g := by exact_mod_cast hh
  have hg : 3 ≤ (p.g:ℝ) := by exact_mod_cast h
  apply le_trans ?_ (le_of_eq (neg_one_mul _))
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (by linarith only [ht,hg]) (by positivity)

set_option maxHeartbeats 1200000 in
theorem veil.score_cost_oai (h : veil p M b r l m s w)
    (v : Stations p M b.pins s) :
    ∃ δ : ℕ → ℝ,ExpSmall l (fun n=> ((M*n:ℕ):ℝ)) δ ∧
      ∀ᶠ n in l, ∀ (q : Format) (d e : Rates) (x : Typus p q d e) (k : Fin (2^deckMax p b.pins)),
        |arena (v n) x (m n) (w n) k|≤δ n := by
  let N:=fun n : ℕ=> M*n; let z:=fun n=>((N n):ℝ)
  have hq := h.easel
  have ht := hq.enter.first
  have hz : Tendsto z l atTop := (trend_sizes l h.timeL ht.hM).2
  let C n:= ((s n).amount (w n))⁻¹
  have hc := h.durableS.mass.inv_cap
  let δ n := bp (-1*z n)*C n*C n + bp (-0.005*z n)*2
  have hd : ExpSmall l z δ :=
    (((ExpSmall.bp_n zero_lt_one).mul hc).mul hc).add hz
      ((ExpSmall.bp_n (by norm_num)).mul (expO_const hz _))
  refine ⟨δ,hd,?_⟩
  filter_upwards [h.moment,h.durableS.mass.positive,h.durableS.shape,hq.secure.filter_mono h.timeL]
    with n hn hN hA hB q d e x k
  have hm := hn.1.law
  rw [abs_of_nonneg (arena_pos _ _ _ _ _ hN hm)]
  let u:=(s n).sap (w n)
  refine (arena_bound (v n) x _ _ k hA.1 hm hN hB).trans ?_
  have hμ i : 0≤u i := (LeafMixture.sapLaw hN hm).nz _
  have hk i : u i ≤ C n*w n i := LeafMixture.upper_sap hm hN i
  have hv (x:UnitType p n (N n) × UnitType p n (N n)) :
      pairW u u x ≤ (C n*C n)*pairW (w n) (w n) x :=
    (mul_le_mul (hk _) (hk _) (hμ _) ((hμ _).trans (hk _))).trans_eq (by unfold pairW; ring)
  have hf : pr (pairW u u) (clash p (m n) (N n)) ≤
      (C n*C n)*bp (-100*p.g * (z n)) := (pr_cap hv _).trans
        (mul_le_mul_of_nonneg_left hn.2.2.2.le (mul_self_nonneg _))
  unfold δ
  rw [mul_comm _ 2]
  refine add_le_add_left ((mul_le_mul_of_nonneg_left hf (bp_pos _).le).trans ?_) _
  calc _ = (beamPrice p (N n) * bp (-100 * p.g * z n))*(C n*C n) := by unfold beamPrice N; ring
       _ ≤ _ := (mul_le_mul_of_nonneg_right (beam_cost p (N n) ht.hG) (mul_self_nonneg _)).trans_eq
            (by unfold z; rw [neg_one_mul,mul_assoc])

end PreparationParameters
end HadwigerCounterexample

end

end OAI
end

theorem solution : type_of% @OAI.HadwigerCounterexample.PreparationParameters.veil.score_cost_oai := @OAI.HadwigerCounterexample.PreparationParameters.veil.score_cost_oai
