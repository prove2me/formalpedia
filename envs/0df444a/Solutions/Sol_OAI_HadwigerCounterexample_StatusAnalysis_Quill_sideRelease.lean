-- Prove2me | solution 1 for OAI.HadwigerCounterexample.StatusAnalysis.Quill.sideRelease
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T23:06:51.077795+00:00
-- url     : https://prove2.me/submissions/0c16b64d-6bc7-49d4-8eb1-fd7553a51b3a

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
import Theorems.Thm_OAI_HadwigerCounterexample_Template_shade_calendar
import Theorems.Thm_OAI_HadwigerCounterexample_litFire_calendar

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

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MatrixFactorization
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
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

variable {p : Shape} {n : ℕ}

theorem labMat_act (s) (z : Vec (AIdx p.g n)) :
    labMat p n s *ᵥ z = putLab p n s z := by
  funext i
  simp [Matrix.mulVec,dotProduct,labMat,putLab,monoBit,selV]

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

theorem sharpM_point {n} (hj : 1 ≤ p.j) (Y) (s s') (z z' : Base p.g n) :
    mpair (sharpM p n Y) (vecMulVec (point p s z) (point p s' z')) =
      ∑ a : Fin p.b, (s a + s' a) *
        evmat (Y a) (fun i => z (Block.sharp,i)) (fun i => z' (Block.sharp,i)) := by
  simp only [sharpM,mpair_sum,mpair_smul,mpair_add,pair_outers,
    sharpPick,dite_eq_left hj,pick_point,readBit,dite_eq_left (Fin.isLt _)]
  simp [selV,emptySel,evmat,dotProduct,mulVec,Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

theorem selfM_pair {n} (hj : 1 ≤ p.j) (Y) {m : Moment p n} (hm : m ∈ Wspace p n) :
    mpair (selfM p n Y) m = eta p n m := by
  unfold Wspace at hm
  induction hm using Submodule.span_induction with
  | mem m h =>
    obtain ⟨s,z,rfl⟩ := h
    simp only [selfM,mpair_sum,mpair_add,mom,sharpM_point p hj,char_two,zero_mul,
      Finset.sum_const_zero, add_zero,eta,etaO,etab,LinearMap.add_apply,
      LinearMap.sum_apply]
  | zero => simp only [map_zero]
  | add _ _ _ _ h g => rw [map_add,h,g,map_add]
  | smul _ _ _ h => rw [map_smul,h,map_smul]

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

theorem IsLaw.sub [Fintype α] {w : Wgt α} (hw : IsLaw w) : SubLaw w where
  nz := hw.nz
  total := hw.total.le

section Basic
variable [Fintype α] {w v f g : Wgt α} {p q : α → Prop}

theorem tot_nonneg (hw : ∀ x, 0 ≤ w x) : 0 ≤ tot w := Finset.sum_nonneg fun x _ => hw x

theorem weight_le_tot (hw : ∀ x, 0 ≤ w x) (x) : w x ≤ tot w :=
  Finset.single_le_sum (fun y _ => hw y) (Finset.mem_univ x)

theorem avg_comm (w f : Wgt α) : avg w f = avg f w := by simp only [avg, mul_comm]

theorem avg_mono (hw : ∀ x, 0 ≤ w x) (h : ∀ x, f x ≤ g x) : avg w f ≤ avg w g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (hw x)

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

theorem carried_iff_pr (hw : ∀ x, 0 ≤ w x) : carried w p ↔ pr w p = tot w := by
  constructor
  · intro h
    unfold pr
    have e : avg w (fun x => ind (p x)) = avg w (fun _ => 1) := by
      refine avg_congr fun x hx => ind_one (Classical.byContradiction fun hn => hx (h x hn))
    rw [e, avg_const, mul_one]
  · intro he x hx
    have h := weight_le_pr (p:=fun x => ¬p x) hw hx
    rw [pr_not, he, sub_self] at h
    exact le_antisymm h (hw x)

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

theorem subLaw_sub (hw : SubLaw w) (p : α → Prop) : SubLaw (subW w p) :=
  ⟨subW_nonneg hw.nz p, (pr_le_tot hw.nz).trans hw.total⟩

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

theorem unif_subLaw : SubLaw (unif : Wgt α) :=
  normW_subLaw (fun _ => zero_le_one)

theorem unif_law [Nonempty α] : IsLaw (unif : Wgt α) := by
  refine normW_law (fun _ => zero_le_one) ?_
  simp [tot, Fintype.card_pos]

theorem unifOn_law (h : ∃ x, p x) : IsLaw (unifOn p) := by
  refine normW_law (fun _ => ind_nonneg _) ?_
  obtain ⟨x, hx⟩ := h
  have := weight_le_tot (fun x => ind_nonneg (p x)) x
  change 0 < tot _
  rw [ind_one hx] at this
  exact lt_of_lt_of_le zero_lt_one this

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

theorem nbr_eq_card (p : A → Prop) [Fintype {x // p x}] :
    nbr p = (Fintype.card {x // p x}:ℝ) := by
  classical
  rw [Fintype.card_subtype]
  simp [nbr,tot,ind]

theorem pr_unif (p : A → Prop) :
    pr unif p = nbr p / Fintype.card A := by
  simp only [pr, avg, nbr, tot, unif_apply, div_eq_mul_inv]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem unifOn_val (p : A → Prop) (x) :
    unifOn p x = ind (p x) / nbr p := rfl

theorem unifOn_sub (p : A → Prop) : SubLaw (unifOn p) :=
  normW_subLaw fun x => ind_nonneg (p x)

theorem unifOn_carried (p : A → Prop) : carried (unifOn p) p :=
  fun x h => by rw [unifOn_val,ind_zero h,zero_div]

theorem on_unif [Nonempty A] (p : A → Prop) : onW unif p = unifOn p := by
  have h : (0:ℝ)<Fintype.card A := by exact_mod_cast Fintype.card_pos
  funext x
  simp only [onW, normW, subW_tot,subW,pr_unif,unifOn_val,unif_apply]
  by_cases hx : nbr p = 0
  · simp [hx]
  · field_simp

theorem unifOn_true : unifOn (fun _ : A => True) = unif := by
  simp [unifOn, unif]

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

/-- Being a probability with support p and all point masses there equal
uniquely characterizes unifOn. -/
theorem uniform_support {w : Wgt A} {p : A → Prop} (hw : IsLaw w)
    (hp : carried w p) (he : ∀ x y, p x → p y → w x = w y) :
    w = unifOn p := by
  have h := (carried_iff_pr hw.nz).mp hp
  rw [hw.total] at h
  obtain ⟨x,hx,_⟩ := exists_of_pr_pos hw.nz (h.trans_gt zero_lt_one)
  have e : ∀ y, w y = w x * ind (p y) := by
    intro y; by_cases h : p y
    · rw [ind_one h, mul_one, he _ _ h hx]
    · rw [hp y h,ind_zero h,mul_zero]
  have hsum : w x * nbr p = 1 := by
    calc w x * nbr p = tot w := by
           unfold nbr tot; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => (e y).symm
         _ = 1 := hw.total
  have hn : nbr p ≠ 0 := right_ne_zero_of_mul (hsum.trans_ne one_ne_zero)
  funext y; rw [e,unifOn_val,eq_div_iff hn,mul_right_comm,hsum,one_mul]

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

/-- Pointwise transitivity transfer of a uniform law under observation. -/
theorem uniform_orbit {p : A → Prop} {q : B → Prop} (f : A → B) (hp : ∃ x, p x)
    (hq : ∀ x, p x → q (f x))
    (h : ∀ y z, q y → q z → ∃ e : A ≃ A, (∀ x, p x ↔ p (e x))
      ∧ ∀ x, f x = y ↔ f (e x)=z) :
    mapW (unifOn p) f = unifOn q := by
  refine uniform_support (mapW_law (unifOn_law hp) _) (mapW_carried (unifOn_carried p) hq)
    (fun y z hy hz => ?_)
  obtain ⟨e,he,hE⟩ := h y z hy hz
  unfold mapW pr
  rw [← avg_bij e (unifOn p) (fun x => ind (f x = z))]
  simp_rw [unifOn_val,← he,← hE]
  rfl

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

theorem pair_unif :
    unif (α:=A×B) = pairW unif unif := by
  funext x; simp [pairW,unif_apply,mul_comm]

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

theorem bp_tendsto_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => bp (-a*x)) atTop (𝓝 0) := by
  simp_rw [neg_mul,bp_neg]
  exact (bp_tendsto ha).inv_tendsto_atTop

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteAffineLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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

/-- Equally likely images along every direction of an indexed family. The
translation hypothesis is before testing the specified targets. -/
theorem translate_cap [Fintype V] [Fintype W] {T : Type*} [Fintype T] [Nonempty T]
    {w : Wgt V} (hw : SubLaw w)
    (f : V →ₗ[F] W) (g : T ↪ W) (h : ∀ t, ∃ v, f v = g t ∧ ∀ x, w (x+v) = w x) (y : W) :
    pr w (fun x => f x=y) ≤ (Fintype.card T : ℝ)⁻¹ := by
  classical
  let u := mapW w f
  have h1 (t : T) : u (y+g t) = u y := by
    obtain ⟨v,hv,he⟩ := h t
    change avg w _ = avg w _
    let E : V ≃ V := ⟨(·+v),(·+v),add_polar v,add_polar v⟩
    rw [← avg_bij E w (fun x => ind (f x = y+g t))]
    change (avg (fun x => w (x+v)) (fun x => ind (f (x+v)=y+g t))) = _
    simp_rw [he,map_add,hv]
    simp
  have hu' : ∀ x, 0 ≤ u x := fun _ => pr_nonneg hw.nz
  have hut : tot u ≤ 1 := by
    have h : tot u = tot w := by simpa [u] using mapW_pr w f (fun _ => True)
    exact h.le.trans hw.total
  let k : T ↪ W := ⟨fun t => y+g t, fun i j h => g.injective (add_left_cancel h)⟩
  have h2 : (Fintype.card T:ℝ)*u y ≤ tot u := calc
    _ = ∑ t : T, u (y+g t) := by simp [h1]
    _ = ∑ x ∈ Finset.univ.map k, u x := by rw [Finset.sum_map]; rfl
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hu' i)
  change u y ≤ _
  rw [←one_div,le_div_iff₀ (by exact_mod_cast Fintype.card_pos)]
  rw [mul_comm]
  exact h2.trans hut

theorem unif_lin [Fintype V] [Fintype W] (f : V →ₗ[F] W) :
    mapW unif f = unifOn (fun y => y ∈ range f) := by
  rw [← unifOn_true]
  refine uniform_orbit _ ⟨0,trivial⟩ (fun x _ => ⟨x,rfl⟩) ?_
  rintro _ _ ⟨y,rfl⟩ ⟨z,rfl⟩
  let d := z-y
  let E : V ≃ V := ⟨(·+d),(·+d),add_polar d,add_polar d⟩
  refine ⟨E,fun _ => Iff.rfl, fun x => ?_⟩
  change f x = f y ↔ f (x+(z-y))=f z
  rw [map_add,map_sub]
  constructor
  · intro h; rw [h,add_sub_cancel]
  · intro h
    apply add_right_cancel (b := f z-f y)
    rw [h,add_sub_cancel]

theorem pr_unif_lin [Fintype V] [Fintype W] (f : V →ₗ[F] W) (y : W) :
    pr unif (fun x => f x=y) = ind (y ∈ range f) * bp (-(rk f:ℝ)) := by
  classical
  change mapW unif f y = _
  rw [unif_lin,unifOn_val,nbr_eq_card]
  rw [card_space,bp_neg,div_eq_mul_inv]

end General

theorem dim_mat (I J : Type) [Fintype I] [Fintype J] :
    dim (Mat I J) = Fintype.card I * Fintype.card J := by
  simp only [dim,Mat,finrank_matrix,finrank_self,mul_one]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GramProbabilities
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gram Probabilities -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Function LinearMap

variable {I J U : Type} [Fintype I] [Fintype J] [Fintype U]

omit [Fintype U] in
theorem outer_act (x : Vec U) (v z : Vec I) :
    vecMulVec x v *ᵥ z = dotProduct v z • x := by rw [vecMulVec_mulVec,op_smul_eq_smul]

omit [Fintype U] in
theorem colSp_outer {x : Vec U} {T : Space (Vec U)} (h : x ∈ T) (v : Vec I) :
    colSp (vecMulVec x v) ≤ T := by
  rintro y ⟨z,rfl⟩
  rw [mulVecLin_apply,outer_act]
  exact T.smul_mem _ h

variable [DecidableEq U] [DecidableEq I] [DecidableEq J]

theorem shift_pmax {w : Wgt (Mat U I)} (hw : SubLaw w) (T : Space (Vec U))
    (h : columnInv (w:=w) T) {x : Vec I} (hx : x ≠ 0) (y : Vec U) :
    pr w (fun M => M *ᵥ x = y) ≤ bp (-(dim T:ℝ)) := by
  classical
  have hh : ∃ v : Vec I, dotProduct v x = 1 := by
    simp only [ne_eq,funext_iff,Pi.zero_apply, not_forall] at hx
    obtain ⟨i,hi⟩ := hx
    exact ⟨Pi.single i 1,(single_one_dotProduct _ _).trans ((bit_cases _).resolve_left hi)⟩
  obtain ⟨v,hv⟩ := hh
  let f : Mat U I →ₗ[F] Vec U := (Matrix.mulVecBilin F F).flip x
  let g : T ↪ Vec U := ⟨Subtype.val,Subtype.val_injective⟩
  have he : ∀ (t:T), ∃ A : Mat U I, f A = g t ∧ ∀ B, w (B+A)=w B := fun t =>
    ⟨vecMulVec t.val v,by change vecMulVec t.val v *ᵥ x = t.val; rw [outer_act,hv,one_smul],
      fun B => h B _ (colSp_outer t.property _)⟩
  have h' := translate_cap hw f g he y
  rw [bp_neg,← card_space]
  exact h'

theorem shift_fail {w : Wgt (Mat U I)} (hw : SubLaw w) (T : Space (Vec U))
    (h : columnInv (w:=w) T) :
    pr w (fun M => ¬ Injective M.mulVec) ≤ bp (num I - dim T) := by
  classical
  let p (x : Vec I) (M : Mat U I) := x ≠ 0 ∧ M *ᵥ x = 0
  have e1 : pr w (fun M => ¬ Injective M.mulVec) ≤ ∑ i : Vec I, pr w (p i) := by
    refine le_trans (pr_mono hw.nz (fun M hm => ?_)) (pr_exists_le hw.nz p)
    rw [← coe_mulVecLin,← ker_eq_bot,ker_mulVecLin_eq_bot_iff] at hm
    push Not at hm
    obtain ⟨x,h1,h2⟩ := hm
    exact ⟨x,h2,h1⟩
  have he (i : Vec I) : pr w (p i) ≤ bp (-(dim T:ℝ)) := by
    by_cases hi : i = 0
    · simp only [p,hi,ne_eq,not_true,false_and,pr_false]
      exact (bp_pos _).le
    · simpa only [p,hi,true_and, ne_eq, not_false_eq_true] using shift_pmax hw T h hi 0
  refine e1.trans ((Finset.sum_le_sum (fun i _ => he i)).trans_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ,nsmul_eq_mul,card_space,
    dim_vec,sub_eq_add_neg,bp_add,num]

theorem unif_fail :
    pr (unif : Wgt (Mat U I)) (fun M => ¬ Injective M.mulVec) ≤ bp (num I - num U) := by
  have h := shift_fail (@unif_subLaw (Mat U I) _) ⊤ (fun _ _ _ => rfl)
  unfold dim at h
  rw [finrank_top,show Module.finrank F (Vec U) = Fintype.card U from dim_vec _] at h
  exact h

omit [DecidableEq U] in
theorem gramL_surj (J : Type) {P : Mat U I} (h : Injective P.mulVec) :
    Surjective (GramL J P) := by
  obtain ⟨Q,hQ⟩ := mat_left_inv h
  intro x
  exact ⟨Qᵀ * x,by change Pᵀ * (Qᵀ * x) = x; rw [← Matrix.mul_assoc,← transpose_mul,
    hQ,Matrix.transpose_one, Matrix.one_mul]⟩

theorem pr_gram_fixed {P : Mat U I} (h : Injective P.mulVec) (G : Mat I J) :
    pr unif (fun Q : Mat U J => Pᵀ * Q = G) = bp (-num I * num J) := by
  have hh := gramL_surj J h
  have hf := pr_unif_lin (GramL J P) G
  rw [ind_one (show G ∈ range _ from hh G),one_mul,rk_surj.mp hh,dim_mat] at hf
  change pr unif _ = _
  exact hf.trans (congrArg bp (by push_cast; unfold num; ring))

omit [Fintype I] [DecidableEq I] in
/-- Conditional minus columns: adding columns in the annihilator of P
doesn't change the pre-injectivity Gram law. -/
theorem gram_shift (P : Mat U I) (G : Mat I J) :
    columnInv (w:=unifOn (fun Q : Mat U J => Pᵀ * Q = G)) (ker (Pᵀ.mulVecLin)) := by
  intro M A hA
  have h : Pᵀ * A = 0 := by
    apply coe_mv_inj
    change (Pᵀ * A).mulVecLin = (0:Mat I J).mulVecLin
    rw [mulVecLin_mul,mulVecLin_zero]
    exact LinearMap.ext fun x => hA (show A.mulVecLin x ∈ colSp A from ⟨x,rfl⟩)
  rw [unifOn_val, Matrix.mul_add,h,add_zero,unifOn_val]

theorem pr_gram_inj_fixed {P : Mat U I} (h : Injective P.mulVec) (G : Mat I J) :
    bp (-num I * num J) * (1 - bp (num I + num J - num U)) ≤
      pr unif (fun Q : Mat U J => Pᵀ * Q = G ∧ Injective Q.mulVec) := by
  let q (Q : Mat U J) := Pᵀ*Q = G
  let f := unifOn q
  have hf := unifOn_law (show ∃ Q : Mat U J, q Q from gramL_surj J h G)
  let T := ker (Pᵀ.mulVecLin)
  have hh := shift_fail hf.sub T (gram_shift _ _)
  have he : num U = num I + dim T := by
    have hj := Pᵀ.mulVecLin.finrank_range_add_finrank_ker
    change rk (Pᵀ.mulVecLin)+dim T = dim (Vec U) at hj
    have h' : Surjective Pᵀ.mulVecLin := transpose_surj_iff.mpr h
    rw [rk_surj.mp h',dim_vec,dim_vec] at hj
    exact_mod_cast hj.symm
  have hi (p : Mat U J → Prop) : pr f (fun x => ¬p x) = 1-pr f p := by
    rw [pr_not,hf.total]
  change bp _ * (1-_) ≤ pr unif (fun x => q x ∧ Injective x.mulVec)
  rw [pr_of_on unif_subLaw.nz q, on_unif, show pr unif q = _ from pr_gram_fixed h G]
  apply mul_le_mul_of_nonneg_left _ (bp_pos _).le
  change pr f _ ≤ _ at hh
  rw [hi (fun x => Injective x.mulVec)] at hh
  rw [show num I+num J-num U = num J - dim T by rw [he]; ring]
  linarith only [hh]

/-- Uniform lower and upper estimates including the full Gram normalization. -/
theorem gram_norm (G : Mat I J) (hsize : num I + num J ≤ num U) :
    let v := (pairW unif unif : Wgt (Mat U I × Mat U J))
    let p := bp (- num I * num J)
    pr v (gramGood G) ≤ p ∧
      p * (1-bp (num I-num U)) * (1-bp (num I+num J-num U)) ≤
      pr v (gramGood G) := by
  let f (P : Mat U I) := pr unif (fun Q : Mat U J => gramGood G (P,Q))
  let a := bp (-num I*num J)
  let b := bp (num I+num J-num U)
  dsimp only
  rw [pr,pairW_avg]
  change avg unif f ≤ a ∧ _ ≤ avg unif f
  have h (P : Mat U I) :
      f P ≤ a ∧ a*(1-b) * ind (Injective P.mulVec) ≤ f P := by
    by_cases hp : Injective P.mulVec
    · have e : f P = pr unif (fun Q : Mat U J => Pᵀ * Q = G ∧ Injective Q.mulVec) := by
        simp [f,gramGood,hp]
      rw [e,ind_one hp,mul_one]
      exact ⟨(pr_mono unif_subLaw.nz fun _ => And.left).trans_eq (pr_gram_fixed hp G),
        pr_gram_inj_fixed hp _⟩
    · have e : f P = 0 := by simp [f,gramGood,hp]
      rw [e,ind_zero hp,mul_zero]
      exact ⟨(bp_pos _).le,le_rfl⟩
  refine ⟨unif_law.avg_le (fun i => (h i).1),?_⟩
  apply le_trans _ (avg_mono unif_subLaw.nz fun i => (h i).2)
  rw [avg_mul']
  have hi := @unif_fail I U _ _ _ _
  rw [pr_not,unif_law.total] at hi
  have ha : 0 ≤ a*(1-b) := by
    refine mul_nonneg (bp_pos _).le (sub_nonneg.mpr ?_)
    simpa [b] using bp_le (show num I+num J-num U ≤ 0 by linarith)
  have hh : 1 - bp (num I-num U) ≤ pr unif (fun M : Mat U I => Injective M.mulVec) := by
    linarith only [hi]
  exact (by
    change a * (1 - bp _) * (1-b) ≤ a * (1-b) * pr _ _
    rw [mul_right_comm]; exact mul_le_mul_of_nonneg_left hh ha)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RawFrameLaws
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

theorem bp_sum {A : Type*} (s : Finset A) (f : A → ℝ) :
    bp (∑ i ∈ s, f i) = ∏ i ∈ s, bp (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha hi => rw [Finset.sum_insert ha, Finset.prod_insert ha,bp_add,hi]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MatrixQuotients
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

theorem evmat_transpose (M : Mat I J) (x : Vec I) (y : Vec J) :
    evmat Mᵀ y x=evmat M x y := dotProduct_transpose_mulVec _ _ _
theorem evmat_pull (P : Mat K I) (Q : Mat L J) (A : Mat K L) (x : Vec I) (y : Vec J) :
    evmat (pullM P Q A) x y=evmat A (P *ᵥ x) (Q *ᵥ y) := by
  rw [←mpair_outer,←mpair_outer,← liftM_outer,mpair_liftM]; rfl

theorem evmat_ext {M N : Mat I J} (h : ∀ x y, evmat M x y=evmat N x y) : M=N := by
  classical
  ext i j
  simpa [evmat] using h (Pi.single i 1) (Pi.single j 1)

theorem dot_ext_zero {x : Vec I} (h : ∀ y, dotProduct y x=0) : x=0 := by
  classical funext i
            simpa using h (Pi.single i 1)

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ChannelFrameLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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

theorem gram_norm_quarter {I J L : Type} [Fintype I] [Fintype J] [Fintype L]
    [DecidableEq I] [DecidableEq J] [DecidableEq L] (G : Mat I J)
    (h : num I + num J-num L ≤ -1) :
    bp (-num I * num J)/4 ≤ pr unif (gramGood (U:=L) G) := by
  have hn := (gram_norm G (by linarith : num I+num J≤num L)).2
  rw [pair_unif]
  refine le_trans ?_ hn
  have he {x : ℝ} (hx : x ≤ -1) : (1/2 : ℝ)≤ 1-bp x := by
    have ht := bp_le hx
    rw [bp_neg,bp_one] at ht
    linarith only [ht]
  let d := bp (-num I*num J)
  change d/4 ≤ d* _ * _
  have hk : 0 < d := bp_pos _
  have h1 := he (x:= num I-num L) (by
    have hg : 0≤num J := Nat.cast_nonneg _
    linarith)
  calc d/4 = d*(1/2)*(1/2) := by ring
       _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left h1 hk.le) (he h) (by norm_num)
         (mul_nonneg hk.le (le_trans (by norm_num) h1))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AtomFlavors
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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

theorem keepZ (f : Flavor g) (x : Tag g) : keeps f x Block.Z := by
  rcases f with (_|_|_) <;> simp [keeps]
theorem keepSharp (f : Flavor g) (x : Tag g) : keeps f x Block.sharp := by
  rcases f with (_|_|_) <;> simp [keeps]

end Flavor

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_WalshBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
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

theorem avg_CS {w : Wgt A} (h : ∀ x, 0 ≤ w x) (f g : Wgt A) :
    (avg w (fun x => f x*g x))^2 ≤ avg w (fun x => f x^2)*avg w (fun x => g x^2) := by
  let F (f : Wgt A) (x) := Real.sqrt (w x)*f x
  have hg (f : Wgt A) (x) : (F f x)^2=w x*f x^2 := by
    unfold F; rw [mul_pow, Real.sq_sqrt (h x)]
  have hx (x) : F f x*F g x=w x*(f x*g x) := by
    unfold F; rw [mul_mul_mul_comm,← pow_two,Real.sq_sqrt (h _)]
  have he := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (F f) (F g)
  simp_rw [hg,hx] at he
  exact he

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

private theorem bp_half_le {x a : ℝ} (h : x^2 ≤ bp a) : |x| ≤ bp (a/2) := by
  have hh : bp (a/2)^2 = bp a := by rw [pow_two,←bp_add]; congr 1; ring
  exact le_of_pow_le_pow_left₀ (show (2:ℕ) ≠ 0 by decide) (bp_pos _).le (by rwa [sq_abs,hh])

/-- Correlation with arbitrary bounded unary tests. -/
theorem walsh_bound (b : V →ₗ[F] W →ₗ[F] F) (f : Wgt V) (g : Wgt W)
    (hf : ∀ x, |f x|≤1) (hg : ∀ x, |g x|≤1) :
    |avg unif (fun w => g w * avg unif (fun x => f x*wsign (b x w)))| ≤ bp (-(rk b:ℝ)/2) := by
  classical
  have : Finite (W →ₗ[F] F) := Finite.of_injective _ DFunLike.coe_injective
  let := Fintype.ofFinite (W →ₗ[F] F)
  apply bp_half_le
  let F w := avg unif (fun x => f x*wsign (b x w))
  have h1 :
      avg unif (fun w => g w^2) ≤ 1 := unif_law.avg_le (fun x => by
    have h := abs_le.mp (hg x); nlinarith [h.1,h.2])
  have h2 :
      avg unif (fun w => (F w)^2) ≤ bp (-(rk b:ℝ)) := by
    unfold F; rw [avg_wsq]
    have hx : avg (pairW unif unif) (fun (x : V × V) => ind (b x.1 = b x.2))
        = bp (-(rk b:ℝ)) := by
      rw [pairW_avg]
      have hh x :
          avg unif (fun z => ind (b x = b z)) = bp (-(rk b:ℝ)) := by
        have h' : b x ∈ LinearMap.range b := ⟨x,rfl⟩
        have heq := pr_unif_lin b (b x)
        rw [ind_one h',one_mul] at heq
        change pr unif _ = _
        simp_rw [eq_comm (a:=b x)]
        exact heq
      simp_rw [hh]
      exact unif_law.avg_const _
    rw [← hx]
    refine avg_mono (pairW_law unif_law unif_law).nz fun ⟨x,y⟩ => ?_
    have hh : f x*f y ≤ 1 := by
      have hh := mul_le_mul (hf x) (hf y) (abs_nonneg _) (by norm_num : 0 ≤ (1:ℝ))
      rw [← abs_mul,one_mul] at hh
      exact (le_abs_self _).trans hh
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (ind_nonneg (b x=b y))
  apply le_trans (avg_CS unif_law.nz _ F)
  exact (mul_le_mul h1 h2 (avg_nonneg unif_law.nz fun _ => sq_nonneg _) (by norm_num)).trans_eq
    (one_mul _)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ImageCharacterBounds
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

variable {I J : Type} [Fintype I] [Fintype J]
theorem mpair_nondeg (M : Mat I J) (h : mpair M=0) : M=0 := by
  classical
  apply evmat_ext; intro x y
  rw [←mpair_outer,h]; simp [evmat]

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

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AmbientBatchSlots
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ambient Batch Slots -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Finset Function
open scoped BigOperators
variable {I J G A B : Type} [Fintype I] [Fintype J] [Fintype A] [Fintype B]
variable {p : Shape} {n N : ℕ}

omit [Fintype B] in
theorem mapW_equiv_val (e : A≃B) (w : Wgt A) (y : B) :
    mapW w e y=w (e.symm y) := by
  classical
  have h : (fun x => e x=y)=(fun x => x=e.symm y) := by
    funext x; apply propext
    exact ⟨fun h => by rw [← h,Equiv.symm_apply_apply],fun h => by rw [h,Equiv.apply_symm_apply]⟩
  unfold mapW; rw [h]; simp

theorem unif_equiv (e : A≃B) : mapW unif e = unif := by
  funext x; rw [mapW_equiv_val, unif_apply, unif_apply, Fintype.card_congr e]

theorem on_equiv (e : A≃B) (p : B→Prop) :
    mapW (unifOn (fun x => p (e x))) e = unifOn p := by
  classical
  have h : nbr (fun x => p (e x))=nbr p := Equiv.sum_comp e (fun y => ind (p y))
  funext x
  rw [mapW_equiv_val,unifOn_val,unifOn_val]; simp only [Equiv.apply_symm_apply,h]

variable [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
variable {f : Route I G}

omit [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G] in
theorem part_scores (x : Rack I N) (A : GeoM f) :
    gramPart A x↔ ∀ i, ∀ a b : Port f i,scoreR x a.val b.val=A i a b := by
  constructor
  · intro h i a b; exact congr_fun (congr_fun (h i) a) b
  intro h i; exact Matrix.ext (fun a b => h i a b)

omit [Fintype G] [DecidableEq I] in
theorem both_test (A : GeoM f) (x : Rack I N) :
    bothPart A x↔ gramPart A x ∧injPart f x := by simp [gramPart,injPart,bothPart,gramGood,forall_and]

private theorem pi_unif {I : Type} [Fintype I] [DecidableEq I]
    {A : I→Type} [∀ i,Fintype (A i)] :
    unif (α:=(∀ i,A i)) = prodW (fun i => unif (α:=A i)) := by
  classical
  funext x
  simp [unif_apply,prodW,Fintype.card_pi]

omit [DecidableEq I] in
theorem netFact_pos : 0<netFact f := mul_pos (pow_pos (by norm_num) _) (bp_pos _)

theorem net_norm (A : GeoM f) (N : ℕ)
    (h : ∀ i,2*num (Port f i)-N≤ -1) :
    (netFact f)⁻¹ ≤ pr unif (bothPart (N:=N) A) ∧
      pr unif (bothPart (N:=N) A) ≤ bp (-netSize f) := by
  classical
  let p := fun i => gramGood (U:=Fin N) (A i)
  have hnum (t : ℕ) : num (Fin t)=(t:ℝ) := by simp [num]
  have ht i : num (Port f i) + num (Port f i)-num (Fin N)≤ -1 := by rw [←two_mul,hnum]; exact h _
  have he : pr unif (bothPart (N:=N) A) = ∏ i,pr unif (p i) := by
    unfold bothPart
    rw [←mapW_pr unif (rackEquiv f N) (fun x => ∀ i,p i (x i)), unif_equiv]
    conv_lhs => rw [pi_unif]
    exact prodW_pr ..
  rw [he]; constructor
  · let h' (i : G) := bp (-(num (Port f i))*num (Port f i))/4
    have hh i : h' i ≤ pr unif (p i) := gram_norm_quarter _ (ht _)
    refine le_trans ?_ (Finset.prod_le_prod (fun i _ => div_nonneg (bp_pos _).le
      (by norm_num)) fun i _ => hh i)
    unfold netFact
    rw [_root_.mul_inv_rev,Finset.prod_div_distrib,←bp_sum,netSize,Finset.prod_const,
      ← bp_neg, ← Finset.sum_neg_distrib]
    simp_rw [neg_mul, Finset.card_univ,div_eq_mul_inv]
    exact le_rfl
  · have h i :=
      (gram_norm (U:=Fin N) (A i) (show _≤ _ by linarith only [ht i])).1
    unfold netSize
    rw [← Finset.sum_neg_distrib, bp_sum]
    apply Finset.prod_le_prod (fun i _ => pr_nonneg unif_law.nz)
    intro i _
    rw [pair_unif,←neg_mul]
    exact h i

theorem wave_norm (A : GeoM f) (N : ℕ)
    (h : ∀ i,2*num (Port f i)-N≤ -1) :
    (netFact f)⁻¹ ≤ pr unif (gramPart (N:=N) A) :=
  ((net_norm A N h).1).trans
    (pr_mono unif_law.nz (fun _ hx => ((both_test ..).mp hx).1))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BoundedQueryTemplates
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

omit [Fintype I] in
theorem ownPart_def (t : Tagging p I) (q : I→F) {N : ℕ} (x : Keys (p:=p) t N) :
    ownPart (p:=p) t q x ↔
    (∀ i, ownOne p (t i) (q i) (x i)) ∧
      ∀ (i j : I) (e : Comp p.g) (hi : inc e (t i)) (hj : inc e (t j)), i≠j →
        dotProduct (x i ⟨e,hi⟩ true) (x j ⟨e,hj⟩ false)=0 := by
  classical
  let Q := ownPort (p:=p) t
  unfold ownPart
  rw [part_scores]
  have he i j (e : Comp p.g) (hi : inc e (t i)) (hj : inc e (t j)) :
      let a : Port Q e := ⟨⟨i,⟨e,hi⟩⟩,rfl⟩
      let b : Port Q e := ⟨⟨j,⟨e,hj⟩⟩,rfl⟩
      scoreR (scatter t N x) a b=dotProduct (x i ⟨e,hi⟩ true) (x j ⟨e,hj⟩ false) := rfl
  constructor
  · intro h
    constructor
    · rintro i ⟨e,hi⟩
      let a : Port Q e := ⟨⟨i,⟨e,hi⟩⟩,rfl⟩
      exact (he i i e hi hi).symm.trans ((h e a a).trans (Matrix.diagonal_apply_eq ..))
    intro i j e hi hj heq
    let a : Port Q e := ⟨⟨i,⟨e,hi⟩⟩,rfl⟩
    let b : Port Q e := ⟨⟨j,⟨e,hj⟩⟩,rfl⟩
    have hh : a≠b := fun h => heq (congrArg (fun x:Port Q e => x.val.1) h)
    exact (he i j e hi hj).symm.trans ((h e a b).trans (Matrix.diagonal_apply_ne _ hh))
  · rintro ⟨h,h'⟩ e ⟨⟨i,v⟩,ha⟩ ⟨⟨j,w⟩,hb⟩
    rcases v with ⟨v,hv⟩; rcases w with ⟨w,hw⟩
    change v = e at ha; change w=e at hb
    subst v; subst w
    let a : Port Q e := ⟨⟨i,⟨e,hv⟩⟩,rfl⟩
    let b : Port Q e := ⟨⟨j,⟨e,hw⟩⟩,rfl⟩
    by_cases he : i=j
    · subst j
      refine (show scoreR (scatter t N x) a.val a.val=_ from h i ⟨e,hv⟩).trans ?_
      exact (Matrix.diagonal_apply_eq (fun j : Port Q e => q j.val.1) a).symm
    have hh : a≠b := fun h => he (congrArg (fun x:Port Q e => x.val.1) h)
    refine Eq.trans (h' i j e hv hw he) ?_
    exact (Matrix.diagonal_apply_ne (fun j : Port Q e => q j.val.1) hh).symm

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CrossPatternCorrelation
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cross Pattern Correlation -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Submodule Finset Function
variable {p : Shape} {n N : ℕ}
variable {I J K A B : Type} [Fintype I] [Fintype J] [Fintype K]
variable [DecidableEq I] [DecidableEq J] [DecidableEq K]

omit [DecidableEq I] [DecidableEq J] in
theorem layer_form (M : Mat I J) (X : PlusRack I N) (Y : PlusRack J N) :
    layerPhase M N X Y=mpair M (Xᵀ*Y) := by
  change (X*M*Yᵀ).trace=(M*(Xᵀ*Y)ᵀ).trace
  rw [Matrix.transpose_mul,Matrix.transpose_transpose,
    ← Matrix.mul_assoc M,Matrix.trace_mul_comm _ X,Matrix.mul_assoc]

omit [DecidableEq I] [DecidableEq J] in
theorem layer_rank (M : Mat I J) (N : ℕ) :
    rk (layerPhase M N)=N*M.rank := by
  classical
  obtain ⟨A,B,hA,hB,hM⟩ := rank_product M
  let t := M.rank
  let P := layerPhase B N
  let X := rmult (Fin N) A
  have h1 : P ∘ₗ X=layerPhase M N := by
    refine LinearMap.ext fun W => ?_
    change mpair ((W*A)*B)=mpair (W*M)
    rw [Matrix.mul_assoc,hM]
  have hp : Injective P := by
    rw [←LinearMap.ker_eq_bot]
    refine le_bot_iff.mp (fun V hV => ?_)
    change mpair (V*B)=0 at hV
    have hg := mpair_nondeg _ hV
    have hh : Injective Bᵀ.mulVec := transpose_surj_iff.mp (by rwa [transpose_transpose])
    obtain ⟨D,hD⟩ := mat_left_inv hh
    have hf : B*Dᵀ=1 := by
      rw [←transpose_transpose B,← transpose_mul,hD,transpose_one]
    have he : V=0 := calc
      V = V*1 := (Matrix.mul_one _).symm
      _ = _ := by rw [←hf,←Matrix.mul_assoc,hg,Matrix.zero_mul]
    rw [he]; exact Submodule.zero_mem _
  have hx : Surjective X := by
    obtain ⟨D,hD⟩ := mat_left_inv hA
    intro v
    exact ⟨v*D,by change v*D*A=v; rw [Matrix.mul_assoc,hD,Matrix.mul_one]⟩
  have hf : rk (P ∘ₗ X)=rk P := by
    unfold rk; rw [LinearMap.range_comp,LinearMap.range_eq_top.mpr hx,Submodule.map_top]
  rw [←h1,hf]
  exact (rk_inj.mp hp).trans ((dim_mat _ _).trans (by simp))

omit [DecidableEq J] [DecidableEq K] in
theorem shifted_sub (M : Mat I I) (f : J→I) (g : K→I) (x : PlusRack J N) (y : PlusRack K N) :
    layerPhase M N (upliftR f x) (upliftR g y)=layerPhase (M.submatrix f g) N x y := by
  rw [layer_form,layer_form]
  let X := embedMat f
  let Y := embedMat g
  have he : (upliftR f x)ᵀ* upliftR g y=liftM X Y (xᵀ*y) := by
    simp only [upliftR,transpose_mul,transpose_transpose,liftM_def,X,Y,Matrix.mul_assoc]
  rw [he,mpair_liftM]
  rw [show liftM Xᵀ Yᵀ M=M.submatrix f g from (by
    unfold X Y; rw [liftM_def,transpose_transpose,embedMat_mul,mul_embedMat]; rfl)]

private theorem uniform_shift {A : Type} [AddGroup A] [Fintype A] (f : Wgt A) (x : A) :
    avg unif f=avg unif (fun y => f (y+x)) := by
  let e : A≃ A :=
    { toFun := (·+x)
      invFun := (·-x)
      left_inv a := add_sub_cancel_right ..
      right_inv a := sub_add_cancel .. }
  have h := avg_bij e unif f
  rw [show (fun y => unif (e y))=unif from (by ext; simp [unif_apply])] at h
  exact h.symm

set_option maxHeartbeats 600000 in
theorem layerLeak (M : Mat I I) (f g r : Wgt (Rack I N)) (U : J→I) (V : K→I)
    (hf : ∀ x, |f x|≤1) (hg : ∀ x,|g x|≤1)
    (h1 : ∀ x y, f (x+(0,upliftR V y))=f x)
    (h2 : ∀ x y,g (x+(upliftR U y,0))=g x)
    (h3 : ∀ x y z,r (x+(upliftR U y,upliftR V z))=r x) :
    |avg unif (fun x => phasedBy M x*f x*g x*r x)| ≤
      bp (- (N:ℝ)*(M.submatrix U V).rank / 2) * avg unif (fun x => |r x|) := by
  classical
  let A x := phasedBy M x*f x*g x*r x
  let D : Wgt (PlusRack J N × PlusRack K N) := pairW unif unif
  have hD : IsLaw D := pairW_law unif_law unif_law
  have he :
      avg unif A=avg unif (fun x => avg D (fun q => A (x+pairedShift U V q.1 q.2))) := by
    rw [avg_avg]; refine (hD.avg_const (avg unif A)).symm.trans
      (avg_congr fun q _ => uniform_shift A _)
  let E := bp (- (N:ℝ)*(M.submatrix U V).rank /2)
  let c (x : Rack I N) := layerPhase M N x.1 x.2
  have hQ (x) : |avg D (fun q => A (x+pairedShift U V q.1 q.2))|≤E*|r x| := by
    let S (y : PlusRack J N) := f (x+(upliftR U y,0))*wsign (layerPhase M N (upliftR U y) x.2)
    let T (y : PlusRack K N) := g (x+(0,upliftR V y))*wsign (layerPhase M N x.1 (upliftR V y))
    let L (q : PlusRack J N × PlusRack K N) :=
      S q.1*(T q.2*wsign (layerPhase (M.submatrix U V) N q.1 q.2))
    have hx q : A (x+pairedShift U V q.1 q.2)=L q*(r x*wsign (c x)) := by
      rcases q with ⟨y,z⟩
      let Y := upliftR U y
      let Z := upliftR V z
      have hfg : f (x+(Y,Z))=f (x+(Y,0)) := by
        rw [show x+(Y,Z)=x+(Y,0)+(0,Z) from by
          rw [add_assoc]; apply congrArg
          apply Prod.ext <;> simp,h1]
      have hgg : g (x+(Y,Z))=g (x+(0,Z)) := by
        rw [show x+(Y,Z)=x+(0,Z)+(Y,0) from by
          rw [add_assoc]; apply congrArg
          apply Prod.ext <;> simp,h2]
      unfold A L phasedBy; dsimp only
      change wsign (layerPhase M N (x.1+Y) (x.2+Z))*f (x+(Y,Z))*g (x+(Y,Z))*r (x+(Y,Z))=_
      rw [hfg,hgg,h3]
      unfold S T c
      simp only [map_add,LinearMap.add_apply,wsign_add]
      rw [show layerPhase M N Y Z=_ from shifted_sub M U V y z]
      dsimp only [Y,Z] <;> ring
    have hs x : |S x|≤ 1 := by simpa only [S,abs_mul,wsign_abs,mul_one] using hf _
    have ht x : |T x|≤ 1 := by simpa only [T,abs_mul,wsign_abs,mul_one] using hg _
    have hl : |avg D L|≤ E := by
      unfold D L
      rw [pairW_avg,avg_avg]
      simp_rw [mul_left_comm (S _),avg_mul']
      refine (walsh_bound _ S T hs ht).trans_eq ?_
      unfold E; rw [layer_rank,Nat.cast_mul,neg_mul]
    simp_rw [hx]
    rw [avg_mul,abs_mul,abs_mul,wsign_abs,mul_one]
    exact mul_le_mul_of_nonneg_right hl (abs_nonneg _)
  change |avg unif A| ≤_
  rw [he]
  exact ((abs_avg_le unif_law.nz).trans (avg_mono unif_law.nz hQ)).trans_eq (avg_mul' ..)

omit [DecidableEq I] in
theorem layer_zero (x : Rack I N) : phasedBy 0 x=1 := by unfold phasedBy; simp [layerPhase,mpair]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GramCharacterExpansion
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gram Character Expansion -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Function Finset
open scoped BigOperators
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {N : ℕ}

theorem vector_expand (x y : Vec I) :
    ind (x=y)=avg unif (fun z => vectorPhase z x*vectorPhase z y) := by
  classical
  have hh (z : Vec I) : vectorPhase z x * vectorPhase z y = wsign (dotL (x+y) z) := by
    unfold vectorPhase
    rw [← wsign_add]
    change _ = wsign (dotProduct _ _)
    rw [dotProduct_comm (x+y),dotProduct_add]
  have hi : dotL (x+y)=0 ↔ x=y := by
    have he : dotL (x+y)=0 ↔ x+y=0 := by
      constructor
      · intro h
        refine dot_ext_zero fun z => ?_
        rw [dotProduct_comm]; exact LinearMap.congr_fun h z
      intro h; rw [h]; exact LinearMap.ext fun z => zero_dotProduct z
    rw [he,←ZModModule.sub_eq_add,sub_eq_zero]
  simp_rw [hh,wsign_lin]
  rw [hi]

variable {E : Rail I}

omit [Fintype I] in
theorem inLedger (E : Rail I) (v : Vec E) : railsM E (ledgerM E v)=v := by
  classical
  funext i; rcases i with ⟨⟨i,j⟩,h⟩
  simp [ledgerM,railsM,h]

theorem rail_charge (x : Rack I N) (E : Rail I) (v : Vec E) :
    vectorPhase v (railsM E (x.1ᵀ*x.2))=phasedBy (ledgerM E v) x := by
  classical
  unfold vectorPhase phasedBy
  rw [layer_form]
  let A := x.1ᵀ*x.2
  let r (i : I × I) := ledgerM E v i.1 i.2 * A i.1 i.2
  change wsign _ = wsign (∑ i:I,∑ j:I,r (i,j))
  rw [←Fintype.sum_prod_type]
  congr 1
  change ∑ i:E,_ = ∑ i:I × I,r i
  calc (∑ i:E,_) = ∑ i:E, r i.val := by
                      refine Finset.sum_congr rfl fun i _ => ?_
                      unfold r
                      rw [show ledgerM E v i.val.1 i.val.2 =v i from congr_fun (inLedger E v) i]
                      rfl
       _ = ∑ i ∈ E,r i := Finset.sum_coe_sort ..
       _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
         rcases i with ⟨i,j⟩
         unfold r
         simp only [ledgerM,Matrix.of_apply,dite_eq_right hi,zero_mul])

theorem rail_expand (x : Rack I N) (E : Rail I) (Z : Vec E) :
    ind (traced x E Z) =
      avg unif (fun v : Vec E => phasedBy (ledgerM E v) x*vectorPhase v Z) := by
  unfold traced
  rw [vector_expand]
  simp_rw [rail_charge]

omit [Fintype I] in
theorem ledger_zero (E : Rail I) : ledgerM E 0=0 := by
  classical ext; simp [ledgerM]

omit [Fintype J] [DecidableEq I] in
theorem match_crowd (x : Rack I N) (g : Route I J) (A : GeoM g) :
    traced x (crowded g) (directions g A) ↔ gramPart A x := by
  classical
  rw [part_scores]
  constructor
  · intro h i a b
    obtain ⟨a,ha⟩ := a
    obtain ⟨b,hb⟩ := b
    subst i
    let y : crowded g := ⟨(a,b), mem_filter.mpr ⟨mem_univ _, hb.symm⟩⟩
    exact congr_fun h y
  · intro h
    funext i
    exact h _ ⟨_,rfl⟩ ⟨i.val.2,(mem_filter.mp i.property).2.symm⟩

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BatchCharacters
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Batch Characters -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Function Finset
variable {I J A B : Type} [Fintype I] [Fintype J] [Fintype A] [Fintype B]
variable [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq B]
variable {n N t : ℕ}

theorem led_uniform (F : Wgt (I→Rack J N)) :
    avg (unif : Wgt (Rack (I×J) N)) (fun x => F (fun i => led i x))=
    avg (draws I unif) F := by
  change avg unif (fun x => F (relay I J N x))=_
  rw [← mapW_avg,unif_equiv,← draws_unif]

omit [Fintype I] [Fintype J] [DecidableEq A] in
theorem heard_fresh {T : A→I × J} {i : I} (B : PlusRack A N) (h : i∉heard T) (j : J) (k) :
    upliftR T B k (i,j)=0 := by
  classical
  unfold upliftR
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  have he : (i,j)≠T x := fun e => h (mem_image.mpr
    ⟨x,mem_univ _, (congrArg Prod.fst e).symm⟩)
  simp [embedMat,he]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_IndependentWeightCorrelation
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent Weight Correlation -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Function Finset
open scoped BigOperators
variable {I J T : Type} [Fintype I] [Fintype J] [Fintype T]
variable [DecidableEq I] [DecidableEq J] [DecidableEq T]
variable {N : ℕ}

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem lane_abs (f : I → Wgt (Rack J N)) (hf : ∀ i x,|f i x|≤1) (T : Finset I) (x) :
    |∏ i∈T,f i (led i x)|≤1 := by
  rw [Finset.abs_prod]; exact (Finset.prod_le_prod (fun i _ => abs_nonneg _)
    (fun i _ => hf i _)).trans_eq (by simp)

omit [Fintype I] [Fintype J] [DecidableEq T] in
private theorem unchanged_true (i : I) {x : Rack (I×J) N} (e : T → I×J)
    (h : i ∉ heard e) (v : PlusRack T N) : led i (x+(upliftR e v,0)) = led i x := by
  apply Prod.ext
  · ext
    simp only [led,sectionR,Prod.fst_add,Matrix.submatrix_apply,Matrix.add_apply,
      heard_fresh v h,add_zero]
  ext; simp [led,sectionR]
omit [Fintype I] [Fintype J] [DecidableEq T] in
private theorem unchanged_false (i : I) {x : Rack (I×J) N}
    (e : T → I×J) (h : i ∉ heard e) (v : PlusRack T N) :
    led i (x+(0,upliftR e v)) = led i x := by
  apply Prod.ext
  · ext; simp [led,sectionR]
  ext
  simp only [led,sectionR,Prod.snd_add,Matrix.submatrix_apply,Matrix.add_apply,
    heard_fresh v h,add_zero]

theorem speed (M : Avenue I J)
    {i j : I} (hi : i ≠ j) {x y : J} (h : M (i,x) (j,y)=1)
    (f : I→ Wgt (Rack J N)) (hf : ∀ i x,|f i x|≤1) :
    |avg unif (fun x => phasedBy M x * brightProd f x)|≤ bp (- (N:ℝ)/2) := by
  classical
  let g (q : Rack (I×J) N) := f i (led i q)
  let P := Finset.univ.erase i
  let l (q : Rack (I×J) N) := ∏ i∈P,f i (led i q)
  have he q : brightProd f q=g q*l q := (Finset.mul_prod_erase _ _ (Finset.mem_univ _)).symm
  let X := fun _ : Unit => (i,x)
  let Y := fun _ : Unit => (j,y)
  have hr : M.submatrix X Y=1 := by ext a b; cases a; cases b; rw [Matrix.one_apply_eq]; exact h
  let r := fun _ : Rack (I×J) N => (1:ℝ)
  have hh q : phasedBy M q * brightProd f q=phasedBy M q*g q*l q*r q := by
    unfold r; rw [he]; ring
  simp_rw [hh]
  have hg q w : g (q+(0,upliftR Y w))=g q := by
    unfold g
    rw [unchanged_false i Y (by simp [heard,Y,hi]) w]
  have hl (q) w : l (q+(upliftR X w,0))=l q := Finset.prod_congr rfl (fun z hz => by
    rw [unchanged_true z X (by
      have hh := (Finset.mem_erase.mp hz).1
      simp [X,heard,hh]) w])
  refine (layerLeak M g l r X Y (fun q => hf i _) (lane_abs f hf P) hg hl (fun _ _ _ => rfl)).trans_eq ?_
  rw [hr,Matrix.rank_one]
  simp only [r,abs_one, Fintype.card_unit, Nat.cast_one,mul_one,unif_law.avg_const]

theorem speed_expand (f : I→ Wgt (Rack J N)) (hf : ∀ i x,|f i x|≤1)
    (E : Rail (I×J)) (Z : Vec E) (hx : ∀ i∈E,i.1.1≠i.2.1) :
    |avg unif (fun x => ind (traced x E Z)*brightProd f x)- bp (-(E.card:ℝ))*avg unif (brightProd f)| ≤
      bp (- (N:ℝ)/2) := by
  classical
  let F (v : Vec E) :=
    vectorPhase v Z * avg unif (fun x => phasedBy (ledgerM E v) x*brightProd f x)
  have hh : avg unif (fun x => ind (traced x E Z)*brightProd f x)=avg unif F := by
    simp_rw [rail_expand,←avg_mul]
    rw [avg_avg]; apply avg_congr
    intro x _
    unfold F
    rw [← avg_mul']
    refine avg_congr (fun i _ => ?_); ring
  let L := bp (- (N:ℝ)/2)
  let B (x : Vec E) := ind (x=0)*avg unif (brightProd f)
  have he x : |F x-B x| ≤ L := by
    unfold F B
    by_cases ht : x=0
    · subst x
      simp only [ledger_zero,layer_zero,one_mul,vectorPhase,zero_dotProduct,
        wsign_zero,ind_true,sub_self,abs_zero]
      exact (bp_pos _).le
    rw [ind_zero ht,zero_mul, sub_zero, abs_mul]
    obtain ⟨y,hy⟩ : ∃ y,x y=1 := by
      by_contra! h; exact ht (funext fun i => (bit_cases _).resolve_right (h _))
    let M := ledgerM E x
    obtain ⟨⟨⟨i,j⟩,k,l⟩,hY⟩ := y
    have hA : M (i,j) (k,l)=1 := by
      simp only [M,ledgerM,Matrix.of_apply,dite_eq_left hY]
      exact hy
    rw [vectorPhase,wsign_abs,one_mul]
    exact speed M (hx _ hY) hA f hf
  rw [hh]
  have hk :
      bp (-(E.card:ℝ))*avg unif (brightProd f)=avg unif B := by
    unfold B; rw [avg_mul]
    congr 1
    symm
    change pr unif (fun x : Vec E => x=0)=_
    rw [pr_point',unif_apply,card_space,dim_vec, Fintype.card_coe,bp_neg]
  rw [hk,← avg_sub]
  exact (abs_avg_le unif_law.nz).trans (unif_law.avg_le he)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConditionedBatchLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditioned Batch Laws -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Submodule Function Finset
variable {I J G H : Type} [Fintype I] [Fintype J] [Fintype G] [Fintype H]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
variable {N : ℕ}

variable {g : Route (I×J) G}

omit [DecidableEq I] in
theorem lane_norm (Z : GeoM g) (hN : ∀ i, 2*num (Port g i)-(N:ℝ)≤ -1)
    (i : I) : 0<pr unif (bothPart (laneM Z i) (N:=N)) := by
  have he j : Injective (condLane g i j) := by intro a b h; exact Subtype.ext (congrArg
    (fun x : Port g j => x.val.2) h)
  have hx j : num (Port (street g i) j)≤num (Port g j) := by
    exact_mod_cast Fintype.card_le_of_injective _ (he j)
  refine lt_of_lt_of_le (inv_pos_of_pos netFact_pos) (net_norm (laneM Z i) N (fun j => ?_)).1
  linarith only [hx j,hN j]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GroupedQueryIndependence
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouped Query Independence -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix LinearMap Module Submodule Function Finset
variable {p : Shape} {n N : ℕ}
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]

theorem spin_scan_free (p : Shape) (n) (l) (f : Flavor p.g) :
    ∀ (x : Knobs p.g n) y,scan p l f (x+Pi.single Block.Z y)=scan p l f x := by
  classical
  intro x y; funext i
  have hx : asBlock i ≠ Block.Z := by rcases i with (⟨i,j⟩|_) <;> simp [asBlock]
  simp only [scan,Pi.add_apply,Pi.single_eq_of_ne hx,add_zero]

theorem fresh_Z (p : Shape) (n) (P : Knobs p.g n→ Prop)
    (h : frozenZ p P) (hh : IsLaw (onW (spins p n) P)) :
    mapW (onW (spins p n) P) (freePart p) = unif := by
  classical
  let w := onW (spins p n) P
  have he (c : Vec (Fin n)) (x : Knobs p.g n) :
      w (x+Pi.single Block.Z c)=w x := by
    have hv (x : Knobs p.g n) : spins p n x=unif x := congr_fun
      (Eq.symm draws_unif) x
    simp only [w,onW_val,hv,unif_apply,← h x c]
  have hv (x y : Vec (Fin n)) :
      mapW w (freePart p) x=mapW w (freePart p) y := by
    let t : Knobs p.g n := Pi.single Block.Z (x-y)
    let e : Knobs p.g n ≃ Knobs p.g n :=
      { toFun := (·+t)
        invFun := (·-t)
        left_inv a := add_sub_cancel_right ..
        right_inv a := sub_add_cancel .. }
    have hh (b : Knobs p.g n) :
        freePart p (e b)=x ↔ freePart p b=y := by
      unfold freePart
      change b Block.Z+t Block.Z=x ↔ _
      rw [show t Block.Z=x-y from Pi.single_eq_same _ _]; constructor <;> intro h
      · apply add_right_cancel (b:=x-y)
        rw [h,add_sub_cancel]
      rw [h,add_sub_cancel]
    unfold mapW pr
    rw [← avg_bij e]
    have hf i : w (e i)=w i := he _ i
    simp_rw [hf,hh]
  rw [←unifOn_true (A:=Vec (Fin n))]
  exact uniform_support (mapW_law hh _) (by intro x h; exact (h trivial).elim) (fun i j _ _ => hv i j)

theorem scopedZ_bit (p : Shape) (n l f x) (h : IsLaw (scopedBit p n l f x)) :
    mapW (scopedBit p n l f x) (freePart p)=unif :=
  fresh_Z p n _ (fun v y => by
    simp only [dialed,spin_scan_free]) h

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConcentrationScales
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concentration Scales -/

noncomputable section
namespace HadwigerCounterexample

open Matrix LinearMap Module Finset Filter Real Function
open scoped BigOperators Topology
variable {X : Type*}

/-- pay slack for any fixed multiple of exponentially smaller term. -/
theorem pay_nat {a b : ℝ} (c : ℝ) (hab : b < a) :
    ∀ᶠ n : ℕ in atTop,c * bp (-a*n) ≤ bp (-b*n) := by
  have h := (bp_tendsto (sub_pos.mpr hab)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [h.eventually (eventually_ge_atTop c)] with n hn
  change c ≤ bp ((a-b)*n) at hn
  refine (mul_le_mul_of_nonneg_right hn (bp_pos _).le).trans_eq ?_
  rw [← bp_add, show (a-b)*n + -a*n= -b*n by ring]

theorem cast_tops (M : ℕ) (hM : 1≤M) :
    Tendsto (fun n : ℕ => (↑(M*n):ℝ)) atTop atTop := by
  simp_rw [Nat.cast_mul]; exact
    (tendsto_const_mul_atTop_of_pos (show 0<(M:ℝ) from by
      exact_mod_cast (show 0 < M from hM))).mpr tendsto_natCast_atTop_atTop

variable {p : Shape} {M n N : ℕ}
variable {I J K G A B : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq G]
variable [Fintype A] [Fintype B]
variable {g : Route J G}

omit [Fintype G] [DecidableEq J] in
theorem port_limit (g : Route J G) (i : G) :
    num (Port g i) ≤ num J := by
  exact_mod_cast Fintype.card_subtype_le _

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GramConditionedLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gram Conditioned Laws -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Submodule Function Finset
variable {I J G H : Type} [Fintype I] [Fintype J] [Fintype G] [Fintype H]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
variable {g : Route (I×J) G} {N : ℕ}

omit [Fintype G] in
private theorem wav_iff (Z : GeoM g) (x : Rack (I×J) N) :
    gramPart Z x ↔ (traced x (crossroads g) (outsideZ Z) ∧
      (∀ i,gramPart (laneM Z i) (led i x))) := by
  classical
  constructor
  · intro h
    constructor
    · funext i
      exact congr_fun ((match_crowd x g Z).mpr h) (⟨i.val,Finset.sdiff_subset i.property⟩ :
      ↑(crowded g))
    intro i; refine (part_scores ..).mpr fun q a b => ?_
    exact (part_scores ..).mp h q (condLane g i q a) (condLane g i q b)
  rintro ⟨ht,hH⟩
  refine (part_scores ..).mpr ?_
  intro i a b
  rcases a with ⟨⟨l,x'⟩,hl⟩
  rcases b with ⟨⟨t,y⟩,hr⟩
  subst i
  let j := g (l,x')
  by_cases hh : l=t
  · subst t
    let a : Port (street g l) j := ⟨x',rfl⟩
    let b : Port (street g l) j := ⟨y,hr⟩
    exact (part_scores ..).mp (hH l) j a b
  let z : I×J := (l,x')
  let v : I×J := (t,y)
  have hv : (z,v)∈crossroads g := Finset.mem_sdiff.mpr
    ⟨Finset.mem_filter.mpr ⟨mem_univ _,hr.symm⟩,fun h => hh (mem_filter.mp h).2⟩
  exact congr_fun ht (⟨(z,v),hv⟩ : ↑(crossroads g))

theorem part_reset [Nonempty H] (p : H→Prop) (f : Wgt H) (h : 0<pr unif p) :
    partMean p f=pr unif p * avg (unifOn p) f := by
  rw [←on_unif]; unfold onW
  rw [avg_norm,subW_tot]
  have he : partMean p f = avg (subW unif p) f := by simp only [avg,subW,mul_assoc]; rfl
  rw [he]
  field_simp

omit [Fintype G] in
set_option maxHeartbeats 600000 in
private theorem wav_means (Z : GeoM g) (f : I → Wgt (Rack J N)) (hf : ∀ i x,|f i x|≤1) :
    |partMean (gramPart Z) (brightProd f) - bp (-( (crossroads g).card:ℝ)) *
      ∏ i,partMean (gramPart (laneM Z i)) (f i)|≤bp (-(N:ℝ)/2) := by
  classical
  let E := crossroads g
  let F i (x : Rack J N) := ind (gramPart (laneM Z i) x)*f i x
  have hF i x : |F i x|≤1 := by
    unfold F; by_cases h : gramPart (laneM Z i) x <;> simp only [h,ind_true,ind_false,one_mul,
      zero_mul]; exact hf i x; norm_num
  have hE i (h : i∈E) : i.1.1≠i.2.1 := fun he =>
    (mem_sdiff.mp h).2 (mem_filter.mpr ⟨(mem_sdiff.mp h).1,he⟩)
  have ht := speed_expand F hF E (outsideZ Z) hE
  have hP : avg unif (brightProd F)=∏ i, partMean (gramPart (laneM Z i)) (f i) :=
    (led_uniform (prodW F)).trans (prodW_avg _ _)
  let A x := ind (traced x E (outsideZ Z))*brightProd F x
  have hi x :
      ind (gramPart Z x) * brightProd f x= A x := by
    rw [wav_iff]; unfold A F E
    simp only [ind_and, ind_all,brightProd,Finset.prod_mul_distrib]
    ring
  rw [hP] at ht
  change |avg unif _-_ *∏ i,partMean _ _|≤_
  simp_rw [hi]
  exact ht

omit [DecidableEq I] in
theorem wave_lane_norm (Z : GeoM g) (hN : ∀ i, 2*num (Port g i)-(N:ℝ)≤ -1)
    (i : I) : 0<pr unif (gramPart (laneM Z i) (N:=N)) :=
  (lane_norm Z hN i).trans_le (pr_mono unif_law.nz fun _ hx => ((both_test ..).mp hx).1)

theorem lane_collapse (A P u V e C : ℝ)
    (h0 : 0<C) (hA : C⁻¹ ≤ A) (hV : |V|≤1)
    (h1 : |A*u-P*V|≤e) (h2 : |A-P|≤e) :
    |u-V|≤2*C*e := by
  have hg : A * |u-V|≤2*e := by
    have hh : |(A-P)*V|≤e := by
      rw [abs_mul]; exact ((mul_le_mul_of_nonneg_left hV (abs_nonneg _)).trans_eq (mul_one _)).trans h2
    calc A*|u-V|= |(A*u-P*V)-(A-P)*V| := by
                 rw [show A*u-P*V-(A-P)*V=(A*(u-V)) by ring,abs_mul,abs_of_nonneg
                   (le_trans ((inv_pos_of_pos h0).le) hA)]
         _ ≤ _ := ((abs_sub ..).trans (add_le_add h1 hh)).trans_eq (two_mul _).symm
  apply le_of_mul_le_mul_left _ (inv_pos_of_pos h0)
  exact ((mul_le_mul_of_nonneg_right hA (abs_nonneg _)).trans hg).trans_eq (by field_simp)

set_option maxHeartbeats 800000 in
theorem compare_waves (Z : GeoM g) (f : I→ Wgt (Rack J N)) (hf : ∀ i x,|f i x|≤1)
    (hN : ∀ i,2*num (Port g i)-(N:ℝ)≤ -1) :
    |avg (rackWave Z N) (brightProd f)- ∏ i,avg (rackWave (laneM Z i) N) (f i)|≤
      2*netFact g*bp (-(N:ℝ)/2) := by
  classical
  let A := pr unif (gramPart (N:=N) Z)
  let B i := pr unif (gramPart (N:=N) (laneM Z i))
  let u := avg (rackWave Z N) (brightProd f)
  let v i := avg (rackWave (laneM Z i) N) (f i)
  let P := bp (- ((crossroads g).card:ℝ))*(∏ i, B i)
  let V := ∏ i,v i
  have hV : |V|≤1 := by
    unfold V
    rw [Finset.abs_prod]
    have he (i) :
        SubLaw (rackWave (laneM Z i) N) := unifOn_sub _
    refine (Finset.prod_le_prod (fun i _ => abs_nonneg _)
      (fun i _ => (abs_avg_le (he i).nz).trans ((he i).avg_le zero_le_one (hf i)))).trans_eq ?_
    simp
  have hh := wave_norm Z N hN
  have h0 : 0<A := (inv_pos_of_pos netFact_pos).trans_le hh
  let e := bp (-(N:ℝ)/2)
  have h1 : |A*u-P*V|≤e := by
    have hb := wave_lane_norm (N:=N) Z hN
    have ht := wav_means Z f hf
    rw [part_reset (gramPart (N:=N) Z) _ h0] at ht
    simp_rw [part_reset _ _ (hb _)] at ht; rw [Finset.prod_mul_distrib] at ht
    simpa only [A,B,u,v,P,V,rackWave,mul_assoc] using ht
  have h2 : |A-P|≤ e := by
    let F (i:I) := fun _ : Rack J N => (1:ℝ)
    have ht := wav_means Z F (by intro i x; simp [F])
    have he (i : I) :
        partMean (gramPart (laneM Z i)) (F i)=B i := by simp only [F,partMean,mul_one]; rfl
    have hx :
        partMean (gramPart (N:=N) Z) (brightProd F)=A := by
      simp only [F,brightProd,partMean,Finset.prod_const_one,mul_one,A,pr]
    simp_rw [he,hx] at ht; exact ht
  exact lane_collapse A P u V e _ netFact_pos hh hV h1 h2

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_KeyReferenceLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Key Reference Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Function
open scoped BigOperators
variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape} {n N : ℕ}

theorem channelTag_inj (p : Shape) (l : Tag p.g) : Injective (channelTag p l) :=
  Subtype.val_injective.comp (outlet p l).injective

omit [DecidableEq I] in
theorem tray_sips (p : Shape) (t : Tagging p I) (N : ℕ) (x : Keys (p:=p) t N) (i : I) :
    led i (tray p t N x)=mug p (t i) N (x i) := by apply Prod.ext <;> rfl

theorem tray_wave (p : Shape) (t : Tagging p I) (q : I→ F) (x : Keys (p:=p) t N) :
    ownPart (p:=p) t q x↔ gramPart (trayMap p t q) (tray p t N x) := by
  classical
  unfold ownPart
  rw [part_scores,part_scores]
  let y := scatter t N x
  let z := tray p t N x
  let A := trayMap p t q
  let g := handles p t
  have hi i j : scoreR z i j=scoreR y (g i) (g j) := rfl
  constructor
  · exact fun h i a b => h i (trayJoin p t i a) (trayJoin p t i b)
  intro hh i a b
  obtain ⟨a,rfl⟩ := (trayJoin p t i).surjective a
  obtain ⟨b,rfl⟩ := (trayJoin p t i).surjective b
  exact hh i a b
theorem lawtray (p : Shape) (t : Tagging p I) (q : I → F) :
    mapW (lawNu p N t q) (tray p t N) = rackWave (trayMap p t q) N := by
  unfold lawNu
  have h : ownPart (p:=p) t q (N:=N)=(fun x => gramPart (trayMap p t q) (tray p t N x)) :=
    funext fun i => propext (tray_wave ..)
  rw [h]
  exact on_equiv ..

omit [Fintype I] in
theorem mug_wave (p : Shape) (t : Tagging p I) (q : I→F) (i : I)
    (x : AtomKey (p:=p) (t i) N) :
    ownOne p (t i) (q i) x ↔ gramPart (laneM (trayMap p t q) i) (mug p (t i) N x) := by
  classical
  rw [part_scores]
  let g := trayPort p t; let b := street g i
  let X := mug p (t i) N x
  let A := laneM (trayMap p t q) i
  have hi {j} (a : Port b j) :
      scoreR X a.val a.val=dotProduct (x (outlet p (t i) a.val) true)
        (x (outlet p (t i) a.val) false) := rfl
  have hj {j} (a : Port b j) : A j a a=q i := by
    let s := trayJoin p t j (condLane (trayPort p t) i j a)
    exact Matrix.diagonal_apply_eq (fun i : Port (ownPort (p:=p) t) j => q i.val.1) s
  have hh (a c : Toast p) (h : b a=b c) : a=c := channelTag_inj p (t i) h
  constructor
  · intro he j a c
    have h : c=a := Subtype.ext (hh _ _ (c.property.trans a.property.symm)); subst c
    exact (hi a).trans ((he _).trans (hj a).symm)
  intro h j
  obtain ⟨a,rfl⟩ := (outlet p (t i)).surjective j
  let e := b a
  let c : Port b e := ⟨a,rfl⟩
  exact (hi c).symm.trans ((h e c c).trans (hj c))

omit [Fintype I] in
theorem lawmug (p : Shape) (t : Tagging p I) (q : I → F) (i : I) :
    mapW (lawOmega p N (t i) (q i)) (mug p (t i) N) = rackWave (laneM (trayMap p t q) i) N := by
  unfold lawOmega
  rw [show ownOne p (t i) (q i) (N:=N)=
    (fun x => gramPart (laneM (trayMap p t q) i) (mug p (t i) N x)) from
    funext fun x => propext (mug_wave ..)]
  exact on_equiv ..
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ReferenceProductTests
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reference Product Tests -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module Function Finset Filter
variable {p : Shape} {I : Type} [Fintype I] [DecidableEq I] {n N : ℕ}

set_option maxHeartbeats 600000 in
theorem reference_product (t : Tagging p I) (q : I → F)
    (f : ∀ i,Wgt (AtomKey (p:=p) (t i) N))
    (hf : ∀ i x,|f i x|≤1) (hN : 2*num (I×Toast p)-(N:ℝ)≤ -1) :
    |avg (lawNu p N t q) (prodW f)- ∏ i,avg (lawOmega p N (t i) (q i)) (f i)|≤
      2*netFact (trayPort p t)*bp (-(N:ℝ)/2) := by
  classical
  let F (i : I) := (f i)∘(mug p (t i) N).symm
  let g := trayPort p t
  let A := trayMap p t q
  have hpL i := show 2*num (Port g i)-(N:ℝ)≤ -1 by linarith only [hN,port_limit g i]
  have he :
      avg (rackWave A N) (brightProd F) =avg (lawNu p N t q) (prodW f) := by
    unfold A; rw [←lawtray,mapW_avg]
    have hh x : brightProd F (tray p t N x)=prodW f x := by
      simp_rw [brightProd,tray_sips,F,Function.comp_apply,Equiv.symm_apply_apply]
      rfl
    simp_rw [hh]
  have hw i : avg (rackWave (laneM A i) N) (F i)=avg (lawOmega p N (t i) (q i)) (f i) := by
    unfold A; rw [←lawmug,mapW_avg]
    simp_rw [F,Function.comp_apply, Equiv.symm_apply_apply]
  have h := compare_waves A F (fun i x => hf _ _) hpL
  simp_rw [he,hw] at h; exact h

theorem priceNu (t : Tagging p I) (q : I→F) (hN : 2*num (I×Toast p)-(N:ℝ) ≤ -1) :
    (netFact (trayPort p t))⁻¹ ≤ pr unif (ownPart (p:=p) t q (N:=N)) := by
  classical
  let g := trayPort p t; let A := trayMap p t q
  have hpL i := show 2*num (Port g i)-(N:ℝ)≤ -1 by linarith only [hN,port_limit g i]
  have he : pr unif (gramPart A (N:=N))=pr unif (ownPart (p:=p) t q (N:=N)) := by
    rw [← unif_equiv (tray p t N),mapW_pr]
    unfold A
    congr 1; ext i
    exact (tray_wave ..).symm
  rw [←he]
  exact wave_norm A N hpL
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ProductCoordinateReplacement
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product Coordinate Replacement -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function
open scoped BigOperators
variable {I J K : Type} {A : Type} [Fintype I] [DecidableEq I] [Fintype A]

set_option maxHeartbeats 600000 in
theorem update_avg (p : I→ Wgt A) (i : I) (f : Wgt (I→A)) (hp : IsLaw (p i)) :
    avg (prodW p) f = avg (prodW p) (fun x => avg (p i) (fun y => f (update x i y))) := by
  classical

  let e : ((I→A)×A)≃ ((I→A)×A) := {
    toFun x := (update x.1 i x.2,x.1 i)
    invFun x := (update x.1 i x.2,x.1 i)
    left_inv x := by simp
    right_inv x := by simp }
  let μ := pairW (prodW p) (p i)
  have he (x : (I→A)×A) : μ (e x)=μ x := by
    unfold μ pairW prodW
    let s := Finset.univ.erase i
    rw [←Finset.mul_prod_erase _ _ (mem_univ i),←Finset.mul_prod_erase _
      (fun i => p i (x.1 i)) (mem_univ i)]
    have h :
        ∏ j∈s,p j (update x.1 i x.2 j)=∏ j∈s,p j (x.1 j) := by
      refine prod_congr rfl fun j hj => ?_
      rw [update_of_ne ((mem_erase.mp hj).1)]
    change p i _ * (∏ j∈s,p j (update x.1 i x.2 j))*p i (x.1 i)=_
    rw [h]
    change p i (Function.update x.1 i (x.2) i) * _ * _=_
    rw [Function.update_self]; ac_rfl
  have ht := avg_bij e μ (fun x => f x.1)
  simp_rw [he] at ht
  unfold μ at ht; simp only [pairW_avg,hp.avg_const] at ht
  exact ht.symm

theorem update2_avg (p q : I→Wgt A) (i : I) (f : Wgt ((I→A)×(I→A))) (hp : IsLaw (p i))
    (hq : IsLaw (q i)) :
    let u := pairW (prodW p) (prodW q)
    avg u f = avg u (fun x => avg (pairW (p i) (q i))
      (fun y => f (update x.1 i y.1,update x.2 i y.2))) := by
  intro u
  simp only [u,pairW_avg]
  conv_lhs => rw [update_avg p i _ hp]
  apply avg_congr; intro x _

  conv_rhs => rw [avg_avg]
  exact avg_congr (fun _ _ => update_avg q i _ hq)
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BilinearBlockCorrelation
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bilinear Block Correlation -/

noncomputable section
namespace HadwigerCounterexample
open Finset LinearMap Module Matrix Function
open scoped BigOperators
variable {p : Shape} {I J A : Type} [Fintype I] [Fintype J] [Fintype A]
variable {n : ℕ}

theorem spring_update (p : Shape) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (y : Knobs p.g n) (B) (h : f.keeps l B) (z : Vec (Fin n)) :
    spring p l s f (update y B z)= spring p l s f (update y B 0)+
      blockRay p n s B *ᵥ z := by
  classical
  have he : baseV (lit f l (update y B z))=baseV (lit f l (update y B 0))+blockA p n B *ᵥ z := by
    funext a
    rcases a with _|⟨d,j⟩
    · simp [baseV,blockA,mulVec,dotProduct,embedMat]
    by_cases hk : d=B
    · subst d; simp [baseV,blockA,mulVec,dotProduct,embedMat,lit,h]
    simp [baseV,blockA,mulVec,dotProduct,embedMat,lit,hk]
  unfold spring point blockRay
  rw [he,map_add,←Matrix.mulVec_mulVec,labMat_act]

theorem spark_walsh [DecidableEq I] [DecidableEq J] (M : Mat I J) (p : Wgt (Vec I)) (q : Wgt (Vec J))
    (hp : ∀ i, |p i|≤1) (hq : ∀ i, |q i|≤1) :
    |avg (pairW unif unif) (fun i => wsign (evmat M i.1 i.2)*(p i.1*q i.2))| ≤
      bp (-(M.rank:ℝ)/2) := by
  classical
  let Q := dotLB I
  let L := Q ∘ₗ M.mulVecLin
  have he (i j) : evmat M i j=L j i := dotProduct_comm ..
  have hh : Injective Q := fun x y h => funext (fun i => by
    have hg := LinearMap.congr_fun h (Pi.single i 1)
    change dotProduct x (Pi.single i 1)=dotProduct y (Pi.single i 1) at hg
    simpa using hg)
  have ht : rk L=M.rank := by
    have h : LinearMap.ker L=LinearMap.ker M.mulVecLin := by
      ext x; change Q (M.mulVecLin x)=0 ↔ M.mulVecLin x=0
      rw [← map_zero Q,hh.eq_iff]
    have hv := L.finrank_range_add_finrank_ker
    rw [h, ← M.mulVecLin.finrank_range_add_finrank_ker] at hv
    exact Nat.add_right_cancel hv
  rw [pairW_avg]
  have hz (x : Vec I) (y : Vec J) : wsign (evmat M x y)*(p x*q y)=p x*(q y*wsign (L y x)) := by
    rw [he]; ring
  simp_rw [hz,avg_mul']
  rw [←ht]
  exact walsh_bound _ q p hq hp

set_option maxHeartbeats 800000 in
theorem spark_uncap (p : Shape) (M : Moment p n) (s t : Label p.b) (l j : Tag p.g)
    (f g : Flavor p.g) (B) (hB : f.keeps l B) (hB' : g.keeps j B)
    (w u : Wgt (Knobs p.g n)) (hw : ∀ i,|w i| ≤ 1) (hu : ∀ i,|u i|≤1) :
    let Q i z := evmat M (spring p l s f i) (spring p j t g z)
    |avg (pairW unif unif) (fun x => wsign (Q x.1 x.2)*(w x.1*u x.2))|≤
      bp (-(blockRank B s t M:ℝ)/2) := by
  classical
  intro Q
  let F (x : Knobs p.g n × _) := wsign (Q x.1 x.2)*(w x.1*u x.2)
  let K := Wgt (Vec (Fin n))
  let v : Block p.g→ K := fun _ => unif
  have ht := update2_avg v v B F unif_law unif_law
  have he : prodW v=unif := draws_unif.symm
  let R := blockRay p n s B; let S:=blockRay p n t B
  let H := pullM R S M
  have hi (x y : Knobs p.g n) :
      |avg (pairW (v B) (v B)) (fun i => F (update x B i.1,update y B i.2))|≤
      bp (-(blockRank B s t M:ℝ)/2) := by
    let X := spring p l s f (update x B 0); let Y := spring p j t g (update y B 0)
    let A i := evmat M (R *ᵥ i) Y; let D j := evmat M X (S *ᵥ j)+evmat M X Y
    let Z i := wsign (A i)*w (update x B i); let W j := wsign (D j)*u (update y B j)
    have hp i j' :
        Q (update x B i) (update y B j')= evmat H i j'+(A i+D j') := by
      unfold Q; rw [spring_update _ _ _ _ _ _ hB,spring_update _ _ _ _ _ _ hB']
      unfold H A D X Y; rw [evmat_pull]
      simp only [evmat,mulVec_add,add_dotProduct,dotProduct_add,R,S]; ac_rfl
    have hh i j : F (update x B i,update y B j)=wsign (evmat H i j)*(Z i*W j) := by
      unfold F Z W; dsimp only; rw [hp,wsign_add,wsign_add]; ring
    have hz i : |Z i|≤1 := by unfold Z; rw [abs_mul,wsign_abs,one_mul]; exact hw _
    have hy i : |W i|≤1 := by unfold W; rw [abs_mul,wsign_abs,one_mul]; exact hu _
    simp_rw [hh]
    exact spark_walsh _ Z W hz hy
  simp only [he] at ht
  change |avg (pairW unif unif) F|≤_
  rw [ht]
  let hq := pairW_law (α:=Knobs p.g n) (β:=Knobs p.g n) unif_law unif_law
  exact (abs_avg_le hq.nz).trans (hq.avg_le fun x => hi x.1 x.2)
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConditionedCorrelations
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditioned Correlations -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Filter Matrix LinearMap Function
open scoped BigOperators
variable {p : Shape} {I A : Type} [Fintype I] [Fintype A]
variable {n : ℕ}

set_option maxHeartbeats 600000 in
theorem spark_condition (p : Shape) (M : Moment p n) (s t : Label p.b) (l j : Tag p.g)
    (f g : Flavor p.g) (B) (hB : f.keeps l B) (hB' : g.keeps j B)
    (w u : Wgt (Knobs p.g n)) (hw : ∀ i,|w i|≤1) (hu : ∀ i,|u i|≤1)
    (μ δ : Wgt (Knobs p.g n)) (hμ : IsLaw μ) (hδ : IsLaw δ)
    (C : ℝ) (hC : 0<C)
    (hc : ∀ i,μ i ≤ C*unif i) (hc' : ∀ i,δ i ≤ C*unif i)
    (hM : n ≤ 5*blockRank B s t M) :
    let Q i z := evmat M (spring p l s f i) (spring p j t g z)
    |avg (pairW μ δ) (fun x => wsign (Q x.1 x.2)*(w x.1*u x.2))|≤
      C^2*bp (-(n:ℝ)/10) := by
  classical
  intro Q
  let V := Knobs p.g n
  let fit (f p : Wgt V) := fun i => p i*f i/(C*unif i)
  have h0 (i : V) : 0<C*unif i := by rw [unif_apply]; positivity
  have hh (t p : Wgt V) (ht : ∀ i, |t i|≤1) (hp : IsLaw p) (h : ∀ i,p i≤C*unif i) i :
      |fit t p i|≤1 := by
    unfold fit; rw [abs_div,abs_of_pos (h0 i),abs_mul,abs_of_nonneg (hp.nz _)]
    refine (div_le_one (h0 i)).mpr ?_
    exact ((mul_le_mul_of_nonneg_left (ht _) (hp.nz _)).trans_eq (mul_one _)).trans (h _)
  let F (x : V×V) := wsign (Q x.1 x.2)*(w x.1*u x.2)
  let Z (x : V×V) := wsign (Q x.1 x.2)*(fit w μ x.1*fit u δ x.2)
  have he :
      avg (pairW μ δ) F=C^2 * avg (pairW unif unif) Z := by
    unfold avg; rw [Finset.mul_sum]
    refine sum_congr rfl fun i _ => ?_
    unfold Z F fit pairW
    have h1 := h0 i.1; have h2 := h0 i.2
    have h3 : unif i.1 ≠ 0 := by rw [unif_apply]; positivity
    have h4 : unif i.2 ≠ 0 := by rw [unif_apply]; positivity
    field_simp
  change |avg (pairW μ δ) F|≤_
  rw [he,abs_mul,abs_of_nonneg (sq_nonneg _)]
  have hi : (n:ℝ)≤5*blockRank B s t M := by exact_mod_cast hM
  exact mul_le_mul_of_nonneg_left ((spark_uncap p M s t l j f g B hB hB'
    _ _ (hh w μ hw hμ hc) (hh u δ hu hδ hc')).trans (bp_le (by linarith only [hi]))) (sq_nonneg _)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ProductCharacterTests
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product Character Tests -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Filter Function
open scoped BigOperators
variable {I J A Z D : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable [Fintype A]

omit [Fintype I] [Fintype A] in
private theorem pipe_prod (s : Finset I) (P : I → A→Z→ℝ)
    (h : ∀ i∈s,Pipe (P i)) :
    Pipe (fun x y => ∏ i∈s,P i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨fun _ =>1,fun _=>1,(by simp),(by simp),fun _ _=>by simp⟩
  | @insert i s hi ih =>
    obtain ⟨f,g,hf,hg,hH⟩ := h i (by simp)
    obtain ⟨u,v,hu,hv,hU⟩ := ih (fun j hj => h j (mem_insert_of_mem hj))
    have he (f g : ℝ) (hf : |f|≤1) (hg : |g|≤1) :
        |f*g|≤1 := by rw [abs_mul]; exact (mul_le_mul hf hg (abs_nonneg _) zero_le_one).trans_eq
                                            (by ring)
    exact ⟨fun x => f x*u x,fun x => g x*v x,(fun x=>he _ _ (hf x) (hu x)),
      (fun x => he _ _ (hg x) (hv x)),fun x y => by dsimp only at *; rw [prod_insert hi,hH,hU]; ring⟩

variable (s : Stage I J)

set_option maxHeartbeats 600000 in
theorem far_avg (w : I→Wgt A) (hw : ∀ i,IsLaw (w i)) (F : Wgt (I→A)) (i j : I)
    (_ : i ≠ j) :
    let U := prodW w
    avg U F = avg U (fun x => avg (pairW (w i) (w j)) (fun y => F (update (update x i y.1) j y.2))) := by
  classical
  intro U
  rw [update_avg w j F (hw j),update_avg w i _ (hw i)]
  simp only [U,pairW_avg]

set_option maxHeartbeats 800000 in
theorem band_res (w : I→ Wgt A) (hw : ∀ i,IsLaw (w i))
    (f : I→ Wgt A) (hf : ∀ i x,|f i x|≤1)
    (u : J→ A→ A→ℝ) (hu : ∀ k x y,|u k x y|≤1)
    (k : J) (η : ℝ)
    (h : ∀ p q : Wgt A,(∀ i, |p i|≤1)→(∀ i,|q i|≤1) →
      |avg (pairW (w (s.first k)) (w (s.nextP k))) (fun x =>
        u k x.1 x.2 * (p x.1*q x.2))|≤η) :
    |avg (prodW w) (fun x => (∏ j:J,u j (x (s.first j)) (x (s.nextP j)))*prodW f x)|≤η := by
  classical
  let i:=s.first k; let j:=s.nextP k
  have hj : i≠ j := s.diff k
  let W (x : I→ A) := (∏ j':J,u j' (x (s.first j')) (x (s.nextP j')))*prodW f x
  have hi (z : I→A) :
      |avg (pairW (w i) (w j)) (fun x => W (moveInputs i j z x.1 x.2))|≤ η := by
    let C a b := moveInputs i j z a b
    let g (v : J⊕I) (a b : A) :=
      match v with
      | .inl t => if t=k then 1 else u t (C a b (s.first t)) (C a b (s.nextP t))
      | .inr t => f t (C a b t)
    have he a b :
        W (C a b)=u k a b * ∏ l:J ⊕ I,g l a b := by
      unfold W prodW; rw [Fintype.prod_sum_type]
      rw [← mul_prod_erase _ _ (mem_univ k),←mul_prod_erase _
        (fun t:J=>g (.inl t) a b) (mem_univ k)]
      have he (t:J) (h : t∈univ.erase k) :
          g (Sum.inl t) a b=u t (C a b (s.first t)) (C a b (s.nextP t)) :=
        ite_eq_right (mem_erase.mp h).1
      rw [Finset.prod_congr rfl (g:=fun t:J => u t (C a b (s.first t)) (C a b (s.nextP t))) he]
      change (u k (C a b i) (C a b j)*_) *_=_
      rw [show C a b i=a from (by simp [C,moveInputs,hj]),
        show C a b j=b from (by simp [C,moveInputs]),show g (.inl k) a b=1 from
        (by simp [g]),one_mul,mul_assoc]
    let d := z i
    have hp : ∀ x:J ⊕ I,Pipe (g x) := by
      have he (t : I) (h : t ≠ j) (a b : A) : C a b t=C a d t := by
        unfold C moveInputs; rw [update_of_ne h,update_of_ne h]
      have hu' (t : I) (h : t ≠ i) (a b : A) : C a b t=C d b t := by
        unfold C moveInputs
        by_cases hx : t=j <;> simp [hx,h]
      have h1 (x:J⊕I) (h : ∀ a b,|g x a b|≤1)
          (e : (∀ a b,g x a b=g x a d)∨(∀ a b,g x a b=g x d b)) :
          Pipe (g x) := by
        rcases e with e|e
        · exact ⟨fun a=>g x a d,fun _=>1,fun i=>h _ _,(by simp),fun i j=> (e i j).trans
            (by rw [mul_one])⟩
        exact ⟨fun _=>1,g x d,(by simp),h d,fun i j=> (e i j).trans (by rw [one_mul])⟩
      rintro (l|l)
      · by_cases hh : l=k
        · subst l; exact h1 (Sum.inl k) (by simp [g]) (Or.inl (by simp [g]))
        apply h1 (Sum.inl l) (fun a b => by simp only [g,ite_eq_right hh]; exact hu _ _ _)
        have hh1 :
            (s.first l≠j∧s.nextP l≠j) ∨(s.first l≠i∧s.nextP l≠i) := by
          by_contra! ha
          by_cases hx : s.first l=j
          · have hy : s.first l≠i := hx ▸ Ne.symm hj
            exact s.anti l k hx (ha.2 hy)
          have ht := ha.1 hx
          have hs : s.first l=i := by_contra (fun h=>hj ((ha.2 h).symm.trans ht))
          exact hh (s.once l k hs ht)
        simp only [g,ite_eq_right hh]; rcases hh1 with ⟨h,h'⟩|⟨h,h'⟩
        · left; intro a b; rw [he _ h,he _ h']
        right; intro a b; rw [hu' _ h,hu' _ h']
      apply h1 (Sum.inr l) (fun a b => hf _ _)
      unfold g
      by_cases h : l=i
      · exact Or.inl fun a b => congrArg _ (he _ (h.symm ▸ hj) _ _)
      exact Or.inr fun a b=> congrArg _ (hu' l h a b)
    obtain ⟨p,q,hp,hq,ht⟩ := pipe_prod univ g (fun i _ => hp i)
    have heq (x : A×A) : W (moveInputs i j z x.1 x.2)=u k x.1 x.2*(p x.1*q x.2) := by
      change W (C _ _)=_
      rw [he]; exact congrArg (_ * ·) (ht x.1 x.2)
    simp_rw [heq]
    exact h p q hp hq
  change |avg _ W|≤η
  rw [far_avg w hw W i j hj]
  exact (abs_avg_le (prodW_law hw).nz).trans ((prodW_law hw).avg_le hi)
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PairIndexedTests
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
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

omit [Fintype I] [DecidableEq I] [Fintype A] in
theorem prism_expand (s : Stage I J) (F : ∀ i,A→A→Vec (B i)) (v : ∀ i,Vec (B i)) (x : I→A) :
    ind (listen s F x=v)=avg (prism B) (fun u => ∏ i:J,
      (vectorPhase (u i) (F i (x (s.first i)) (x (s.nextP i)))*vectorPhase (u i) (v i))) := by
  classical
  rw [funext_iff, ind_all]; simp_rw [listen,vector_expand]
  exact (prodW_avg (fun i => unif) (fun i u =>
    vectorPhase u (F i (x (s.first i)) (x (s.nextP i)))*vectorPhase u (v i))).symm

set_option maxHeartbeats 800000 in
theorem hear_band (s : Stage I J) (F : ∀ i,A→A→Vec (B i)) (v : ∀ i,Vec (B i))
    (w : I → Wgt A) (hw : ∀ i,IsLaw (w i))
    (η : ℝ) (hη : 0≤η)
    (h : ∀ i:J,∀ u:Vec (B i),u≠0 → ∀ p q : Wgt A,(∀ i,|p i|≤1) → (∀ i,|q i|≤1) →
      |avg (pairW (w (s.first i)) (w (s.nextP i))) (fun x =>
        vectorPhase u (F i x.1 x.2)*(p x.1*q x.2))|≤η) :
    ∀ p : I→ Wgt A,(∀ i x,|p i x|≤1) →
    |avg (prodW w) (fun x => ind (listen s F x=v)*prodW p x)-
      wavelength B*∏ i:I,avg (w i) (p i)|≤η := by
  classical
  intro p hp
  let P (u : ∀ i, Vec (B i)) (i:J) (x y : A) := vectorPhase (u i) (F i x y)
  let Q (u : ∀ i,Vec (B i)) := ∏ i:J,vectorPhase (u i) (v i)
  let U (u:∀ i,Vec (B i)) := avg (prodW w) (fun x =>
    (∏ i:J,P u i (x (s.first i)) (x (s.nextP i)))*prodW p x)
  have he :
      avg (prodW w) (fun x => ind (listen s F x=v)*prodW p x)=
        avg (prism B) (fun u => Q u*U u) := by
    simp_rw [prism_expand,←avg_mul]
    rw [avg_avg]; unfold Q U P; simp_rw [←avg_mul',Finset.prod_mul_distrib]
    apply avg_congr; intro x _; refine avg_congr fun i _ => ?_
    ring
  have hU : U 0=∏ i:I,avg (w i) (p i) := by
    unfold U P
    simp only [vectorPhase,Pi.zero_apply,zero_dotProduct,wsign_zero,prod_const_one,one_mul]
    exact prodW_avg ..
  have hQ : Q 0=1 := by simp [Q,vectorPhase]
  have hq u : |Q u|=1 := by simp [Q,abs_prod,vectorPhase]
  let V := ∏ i:I,avg (w i) (p i)
  let L (u : ∀ i,Vec (B i)) := ind (u=0)*V
  have hi : avg (prism B) L=wavelength B*V := by
    unfold L; rw [avg_mul,show avg (prism B) (fun i => ind (i=0))= _ from pr_point' (prism B) 0]; rfl
  have hh u : |Q u*U u-L u| ≤ η := by
    by_cases hg : u=0
    · subst u; unfold L V; rw [ind_one (show (0:∀ i,Vec (B i))=0 from rfl),hU,hQ,sub_self,abs_zero]
      exact hη
    obtain ⟨i,ha⟩ := Function.ne_iff.mp hg
    unfold L; rw [ind_zero hg,zero_mul,sub_zero,abs_mul,hq,one_mul]
    exact band_res s w hw p hp (P u) (by intro k x y; simp [P,vectorPhase]) i η (h i (u i) ha)
  have h0 : IsLaw (prism B) := prodW_law (fun _ => unif_law)
  rw [he]; change |_ - wavelength B * V|≤_
  rw [←hi,←avg_sub]
  exact (abs_avg_le h0.nz).trans (h0.avg_le hh)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_EndpointEvaluations
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Endpoint Evaluations -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

namespace Template
variable (v : Template p I)

omit [DecidableEq I] in
theorem chime_seq (m : Mixer p n) (x : UnitType p n N) (i)
    (y : Vec (v.Abbey i)) (u z : Knobs p.g n) :
    dotProduct y (v.chime m x i u z)=evmat (v.chorusM m x i y)
      (v.croon (v.choral.first i) u) (v.croon (v.choral.nextP i) z) := by
  unfold chorusM dotProduct chime
  simp_rw [←mpair_outer, mpair_sum,mpair_smul]

omit [DecidableEq I] in
theorem chorus_same (m : Mixer p n) (x : UnitType p n N) (i : v.SameDuet)
    (y : Vec (v.Abbey (.inl i))) :
    v.chorusM m x (.inl i) y=indexedSum m (fun j => y (Sum.inl j)) + selfSum m (fun j => y (Sum.inr j)) := by
  unfold chorusM

  change ∑ j:Harm p,y j • monks v m x (.inl i) j=_
  rw [Fintype.sum_sum_type]; rfl

set_option maxHeartbeats 600000 in
omit [DecidableEq I] in
theorem chorus_cross (m : Mixer p n) (x : UnitType p n N) (i : v.OppDuet)
    (y : Vec (v.Abbey (.inr i))) (hy : y≠0) :
    ∃ w : Vec (Notches p), w≠0 ∧ v.chorusM m x (.inr i) y=issue p w x := by
  classical
  let T (j : Notches p) := inc j.1 (v.t i.val.1)∧inc j.1 (v.t i.val.2)
  let w (j : Notches p) := if h:T j then y (⟨j,h⟩ : Crossing p _ _) else 0
  have he (j : Crossing p (v.t i.val.1) (v.t i.val.2)) : w j.val=y j := dite_eq_left j.property
  have hz : w≠0 := fun h => hy (funext (fun j : Crossing p _ _ => by rw [←he,h]; rfl))
  refine ⟨w,hz,?_⟩
  let f (j : Notches p) := w j • duel p (x.1 j.1) (x.2 j.1) j.2
  have h : issue p w x=∑ i : Notches p,f i := by
    rw [Fintype.sum_prod_type]; rfl
  rw [h]
  have ht : ∑ j : {j:Notches p//T j},f j.val = ∑ j : Notches p,f j := by
    let s := univ.filter T
    rw [← Finset.sum_subtype s (by simp [s]) f]
    refine Finset.sum_subset (subset_univ _) (fun i _ hi => ?_)
    have hh : ¬T i := fun h => hi (mem_filter.mpr ⟨mem_univ _,h⟩)
    unfold f w; rw [dite_eq_right hh,zero_smul]
  rw [← ht]
  change (∑ j:{j:Notches p//T j},_) = _
  exact Finset.sum_congr rfl fun j _ => by unfold f; rw [he]; rfl
end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ScriptGramCorrespondence
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Script Gram Correspondence -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix LinearMap Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

namespace Template
variable (v : Template p I)

omit [DecidableEq I] in
theorem across_duet (v : Template p I) {i j} (h : i ≠ j) :
    ∃ k : v.Chorus,v.verses k=(i,j)∨v.verses k=(j,i) := by
  classical
  let e := Fintype.equivFin I
  by_cases hg : v.aim i=v.aim j
  · rcases lt_or_gt_of_ne (e.injective.ne h) with hh|hh
    · exact ⟨.inl ⟨⟨i,j⟩,hg,hh⟩,Or.inl rfl⟩
    exact ⟨.inl ⟨⟨j,i⟩,hg.symm,hh⟩,Or.inr rfl⟩
  cases hi : v.aim i <;> cases hj : v.aim j
  · simp [hi,hj] at hg
  · exact ⟨.inr ⟨⟨j,i⟩,hj,hi⟩,Or.inr rfl⟩
  · exact ⟨.inr ⟨⟨i,j⟩,hi,hj⟩,Or.inl rfl⟩
  simp [hi,hj] at hg

omit [Fintype I] [DecidableEq I] in
theorem voice_note (v : Template p I) (x : UnitType p n N) (z : Inputs p n I)
    (e : Comp p.g) (i j) (a : inc e (v.t i)) (b : inc e (v.t j)) (q : Bool) :
    v.voices ((v.draw z).keys v.t x) i j e a b q=evmat
      (duel p (onSide x (v.aim i) e) (onSide x (v.aim j) e) q)
        (v.croon i (z i)) (v.croon j (z j)) := by
  let P := primary (takeSign (p:=p) (onSide x (v.aim i) e) q)
  let Q := primary (takeSign (p:=p) (onSide x (v.aim j) e) (!q))
  let u := v.croon i (z i); let t := v.croon j (z j)
  change dotProduct (P *ᵥ u) (Q *ᵥ t)=dotProduct u ((Pᵀ *Q)*ᵥ t)
  rw [← mulVec_mulVec,dotProduct_transpose_mulVec]
  exact dotProduct_comm _ _

omit [Fintype I] [DecidableEq I] in
theorem voice_same (v : Template p I) (x : UnitType p n N) (z : Inputs p n I)
    (m : Mixer p n) (hw : ∀ i,frameLaw m (onSide x i))
    (e : Comp p.g) (i j) (a : inc e (v.t i)) (b : inc e (v.t j))
    (h : v.aim i=v.aim j) (q : Bool) :
    v.voices ((v.draw z).keys v.t x) i j e a b q=evmat
      (eitherM q (selfM p n m.mixM)) (v.croon i (z i)) (v.croon j (z j)) := by
  rw [voice_note,h]
  let y := onSide x (v.aim j) e
  have he : (primary y.1)ᵀ*primary y.2=selfM p n m.mixM := (hw (v.aim j) e).2.2.1
  congr 1
  unfold duel
  cases q
  · change (primary y.2)ᵀ*primary y.1=_
    rw [←he]; simp only [eitherM,Bool.false_eq_true,ite_false, if_false, transpose_mul,transpose_transpose]
  exact he

omit [Fintype I] [DecidableEq I] in
theorem verges_rev (v : Template p I) {x : Keys (p:=p) v.t N} {i j}
    (h : v.verges x i j) : v.verges x j i := by
  intro e a b q
  have ht := h e b a (!q)
  unfold voices at *; rw [dotProduct_comm]; rwa [Bool.not_not] at ht

omit [Fintype I] [DecidableEq I] in
theorem voices_diag (v : Template p I) (m : Mixer p n) (x : UnitType p n N)
    (w : Inputs p n I) (hw : ∀ i,frameLaw m (onSide x i)) (hj : 1≤p.j) (i : I) :
    ownOne p (v.t i) (dialed p (v.t i) (v.f i) (w i))
      ((v.draw w).keys v.t x i) := by
  intro e
  let y := (v.draw w).par i
  let A := mom p (v.s i) y
  have h : A∈Wspace p n := Submodule.subset_span ⟨_,_,rfl⟩
  have he := v.voice_same x w m hw e.val i i e.property e.property rfl true
  let E := selfM p n m.mixM
  change v.voices _ i i e.val e.property e.property true=_
  rw [he]
  change evmat E (point p _ y) (point p _ y)=_
  rw [← mpair_outer]
  exact (selfM_pair p hj m.mixM h).trans (etaScan p (n:=n) (v.t i) (v.s i) _ (w i)).symm

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_KeyTestCorrespondence
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Key Test Correspondence -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix LinearMap
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

namespace Template
variable (v : Template p I)

omit [Fintype I] [DecidableEq I] in
theorem knows_rev (v : Template p I) {s : Script p I} {m : Mixer p n} {z} {i j}
    (h : v.knows s m z i j) : v.knows s m z j i := fun ht => (h ht.symm).symm

omit [DecidableEq I] in
theorem voice_agreement (v : Template p I) (s : Script p I) (m : Mixer p n)
    (x : UnitType p n N) (z : Inputs p n I) (hw : ∀ i,frameLaw m (onSide x i))
    (hg : 2≤p.g) (j : v.Chorus) :
    listen v.choral (v.chime m x) z j = v.lyrics s j ↔
      v.verges ((v.draw z).keys v.t x) (v.verses j).1 (v.verses j).2 ∧
        v.knows s m z (v.verses j).1 (v.verses j).2 := by
  classical
  let y := (v.draw z).keys v.t x
  cases j with
  | inr k =>
    let a := k.val.1; let b := k.val.2
    have he : v.aim a≠v.aim b := by rw [k.property.1,k.property.2]; decide
    have hh e ha hb q :
        listen v.choral (v.chime m x) z (.inr k) (⟨(e,q),ha,hb⟩ :
          Crossing p (v.t a) (v.t b))=v.voices y a b e ha hb q := by
      change evmat (duel p (x.1 e) (x.2 e) q) _ _=_
      rw [voice_note,k.property.1,k.property.2]; rfl
    constructor
    · intro h
      exact ⟨fun e ha hb q => (hh e ha hb q).symm.trans (congr_fun h _),fun ht => (he ht).elim⟩
    rintro ⟨h,_⟩
    apply funext
    rintro ⟨⟨e,q⟩,ha,hb⟩
    exact (hh e ha hb q).trans (h e ha hb q)
  | inl k =>
    let a := k.val.1; let b:= k.val.2
    have he : v.aim a=v.aim b := k.property.1
    let u := listen v.choral (v.chime m x) z (.inl k)
    let d := v.lyrics s (.inl k)
    have hi1 i :
        u (Sum.inl (i,true))=d (Sum.inl (i,true)) ↔
          s a b i=evmat (orderedM m i) (v.croon a (z a)) (v.croon b (z b)) := Eq.comm
    have hi2 i :
        u (Sum.inl (i,false))=d (Sum.inl (i,false)) ↔
          s b a i=evmat (orderedM m i) (v.croon b (z b)) (v.croon a (z a)) := by
      change evmat (orderedM m i)ᵀ _ _=s b a i ↔ _
      rw [evmat_transpose]; exact Eq.comm
    have ht e ha hb q :
        u (Sum.inr q)=d (Sum.inr q) ↔ v.voices y a b e ha hb q=0 := by
      rw [voice_same _ x z m hw e a b ha hb he q]; rfl
    change u=d↔v.verges y a b ∧ v.knows s m z a b
    constructor
    · intro h
      exact ⟨fun e ha hb q => (ht e ha hb q).mp (congr_fun h _),
        fun _ => ⟨fun i => (hi1 i).mp (congr_fun h _),fun i => (hi2 i).mp (congr_fun h _)⟩⟩
    have hk : ∃ e : Comp p.g,inc e (v.t a) ∧ inc e (v.t b) := by
      by_cases hx : v.t a=v.t b
      · rw [hx]
        have h : 0<Fintype.card (TagStar (v.t b)) := by rw [card_star]; omega
        obtain ⟨⟨i,hi⟩⟩ := Fintype.card_pos_iff.mp h
        exact ⟨i,hi,hi⟩
      refine ⟨edge _ _ hx,inc_edge_fst hx,(inc_edge_iff hx).mpr (Or.inr rfl)⟩
    rintro ⟨h1,h2⟩; specialize h2 he
    apply funext
    rintro (⟨i,_|_⟩|q)
    · exact (hi2 i).mpr (h2.2 i)
    · exact (hi1 i).mpr (h2.1 i)
    obtain ⟨i,hi,hj⟩ := hk
    exact (ht i hi hj q).mpr (h1 ..)

omit [DecidableEq I] in
theorem neigh_voice (v : Template p I) (s : Script p I) (m : Mixer p n)
    (x : UnitType p n N) (z : Inputs p n I) (hw : ∀ i,frameLaw m (onSide x i))
    (hg : 2 ≤ p.g) :
    v.performs s m x z ↔ v.neigh s m x z := by
  classical
  let y := (v.draw z).keys v.t x
  let g i j := v.verges y i j∧ v.knows s m z i j
  have h1 :
      v.performs s m x z ↔ ∀ i j,i≠j→ g i j := by
    unfold performs; rw [funext_iff]; simp_rw [voice_agreement _ _ _ _ _ hw hg]
    change (∀ i,g (v.verses i).1 (v.verses i).2) ↔_
    constructor
    · intro h i j hh
      obtain ⟨k,h'|h'⟩ := across_duet v hh
      · specialize h k; rwa [h'] at h
      specialize h k; rw [h'] at h
      exact ⟨v.verges_rev h.1,v.knows_rev h.2⟩
    exact fun h _ => h _ _ (v.choral.diff _)
  rw [h1]; unfold g neigh
  constructor
  · intro h; exact ⟨fun i j e he => ((h i j e).2 he).1,fun i j e => (h i j e).1⟩
  rintro ⟨h,h'⟩ i j he
  exact ⟨h' i j he,fun e => ⟨h i j he e,h j i (Ne.symm he) (Eq.symm e)⟩⟩

theorem performs_own (v : Template p I) (s : Script p I) (m : Mixer p n)
    (x : UnitType p n N) (z : Inputs p n I) (hw : ∀ i,frameLaw m (onSide x i))
    (hg : 2 ≤ p.g) (hj : 1 ≤ p.j)
    (q : I→F) (hq : ∀ i,dialed p (v.t i) (v.f i) (z i)=q i) :
    v.performs s m x z ↔ (v.draw z).reads s m ∧
      ownPart (p:=p) v.t q ((v.draw z).keys v.t x) := by
  rw [neigh_voice _ _ _ _ _ hw hg,ownPart_def]
  unfold neigh
  apply and_congr Iff.rfl
  have ht (i : I) := v.voices_diag m x z hw hj i
  simp_rw [hq] at ht
  let y := (v.draw z).keys v.t x
  constructor
  · intro h; exact ⟨ht,fun i j e hi hj hh => h i j hh e hi hj true⟩
  rintro ⟨_,h⟩ i j hh e hi hj (b|b)
  · unfold voices; rw [dotProduct_comm]; exact h j i e hj hi (Ne.symm hh)
  exact h i j e hi hj hh

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BinaryMixingBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
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

omit [DecidableEq I] in
theorem choral_live (v : Template p I) (m : Mixer p n) (hm : binaryGood m)
    (x : UnitType p n N) (hx : litFire p x) (hv : v.diffsel)
    (i : v.Chorus) (c : Vec (v.Abbey i)) (hc : c≠0) :
    let j := v.choral.first i; let l := v.choral.nextP i
    ∃ B, (v.f j).keeps (v.t j) B ∧ (v.f l).keeps (v.t l) B ∧
      n≤5*blockRank B (v.s j) (v.s l) (v.chorusM m x i c) := by
  classical
  rcases i with i|i
  · intro j l
    let a : Vec (MBits p) := fun y => c (.inl y)
    let b : Vec Bool := fun y => c (.inr y)
    have hh : v.s j≠v.s l := hv j l (v.choral.diff (.inl i)) i.property.1
    by_cases h : a=0
    · refine ⟨Block.sharp,Flavor.keepSharp ..,Flavor.keepSharp ..,?_⟩
      have he : indexedSum m a=0 := by simp [h,indexedSum]
      rw [chorus_same]
      change n ≤ 5*blockRank _ _ _ (indexedSum m a+selfSum m b)
      rw [he,zero_add]
      have hz : b≠0 := by
        intro hb; apply hc; funext y
        cases y
        next l => exact congr_fun h l
        next l => exact congr_fun hb l
      exact (hm _ _ hh).2 b hz
    refine ⟨Block.Z,Flavor.keepZ ..,Flavor.keepZ ..,?_⟩
    rw [chorus_same]; exact (hm _ _ hh).1 a b h
  intro j l; refine ⟨Block.Z,Flavor.keepZ ..,Flavor.keepZ ..,?_⟩
  obtain ⟨w,hw,hh⟩ := chorus_cross v m x i c hc
  rw [hh]; exact hx _ _ w hw

theorem resonant (v : Template p I) (m : Mixer p n) (hm : binaryGood m)
    (x : UnitType p n N) (hx : litFire p x) (hv : v.diffsel)
    (w : I → Wgt (Knobs p.g n)) (hw : ∀ i,IsLaw (w i))
    (C : ℝ) (hC : 0 < C) (hc : ∀ i j,w i j ≤ C*unif j)
    (s : Script p I) :
    ∀ u : I → Wgt (Knobs p.g n),(∀ i x, |u i x|≤1) →
    |avg (prodW w) (fun z => ind (v.performs s m x z)*prodW u z) -
      v.kappa * ∏ i:I,avg (w i) (u i)|≤ C^2*bp (-(n:ℝ)/10) := by
  classical
  refine hear_band v.choral (v.chime m x) (v.lyrics s) w hw _
    (mul_nonneg (sq_nonneg _) (bp_pos _).le) ?_
  intro i c hc' p q hp hq
  obtain ⟨b,hb,hb',hz⟩ := v.choral_live m hm x hx hv i c hc'
  simp_rw [vectorPhase,v.chime_seq]
  exact spark_condition _ (v.chorusM m x i c) _ _ _ _ _ _ b hb hb' p q hp hq
    _ _ (hw _) (hw _) C hC (hc _) (hc _) hz

end Template

theorem dialCap (p : Shape) {n : ℕ} (l : Tag p.g) (z : F)
    (f : Flavor p.g) (hr : 1 ≤ p.r) (hn : 2*p.r≤n) (h : canDial p l f z) :
    ∀ x,scopedBit p n l f z x≤(scanPrice p)⁻¹*unif x := by
  intro x
  refine (on_mon (spins_law p n).nz (scanPrice_pos p) (dial_fraction p n _ _ _ hr hn h)
    x).trans_eq ?_
  rw [spins,← draws_unif]
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ProjectionEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projection Energy -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]

omit [Fintype B] in
theorem lsupp_witness {p : Wgt A} {f : A→B} {i}
    (h : mapW p f i≠0) : ∃ x,p x≠0 ∧ f x=i := by
  classical
  by_contra! hh
  refine h (Finset.sum_eq_zero (fun x _ => ?_))
  by_cases h : p x=0
  · change p x * ind _=0
    rw [h,zero_mul]
  exact (congrArg (p x * ·) (ind_zero (hh x h))).trans (mul_zero _)

omit [Fintype B] in
theorem lsupp_hit {p : Wgt A} (hp : ∀ i,0 ≤ p i) (f : A→B) (x : A) (h : p x≠0) :
    mapW p f (f x)≠0 := by
  have h' := lt_of_le_of_ne (hp x) (Ne.symm h)
  have he := weight_le_tot (fun y => mul_nonneg (hp y) (ind_nonneg (f y = f x))) x
  simp only [ind_true,mul_one] at he
  exact (h'.trans_le he).ne'

omit [Fintype B] in
theorem lsupp.map {p q : Wgt A} (h : lsupp p q) (hq : ∀ i,0 ≤ q i)
    (f : A→B) : lsupp (mapW p f) (mapW q f) := by
  intro i hi
  obtain ⟨x,hx,rfl⟩ := lsupp_witness hi
  exact lsupp_hit hq f x (h x hx)

omit [Fintype B] in
theorem map_resize (p : Wgt A) (f : A→B) (u : Wgt B) :
    mapW (fun i => p i*u (f i)) f = (fun i => mapW p f i * u i) := by
  funext i
  unfold mapW pr avg
  rw [Finset.sum_mul]
  apply sum_congr rfl
  intro j _
  by_cases h : f j=i
  · simp only [h,ind_true,mul_one]
  simp only [ind_zero h,mul_zero,zero_mul]

omit [Fintype B] in
theorem map_pour (q : Wgt A) (f : A → B) (w : Wgt B) (h : lsupp w (mapW q f)) :
    mapW (pour q f w) f=w := by
  unfold pour
  rw [map_resize (u:=fun i => w i / mapW q f i)]
  funext i
  by_cases he : w i=0
  · simp only [he,zero_div,mul_zero]
  have hm := h i he
  field_simp

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConditionalFlags
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

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PhaseParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Phase Parameters -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators Topology
open Filter
variable {p : Shape} {n N : ℕ}

theorem bp_nat_vanish {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => bp (-c*n)) atTop (𝓝 0) :=
  (bp_tendsto_zero hc).comp tendsto_natCast_atTop_atTop

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConditionalProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional Projection -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Function
open scoped BigOperators
variable {A B C K : Type} [Fintype A] [Fintype B] [Fintype C]

theorem ode_nonneg {μ : Wgt A} (hμ : ∀ i,0 ≤ μ i) (f : Wgt A) : 0≤ ode μ f :=
  avg_nonneg hμ (fun _ => mul_self_nonneg _)
theorem ode_upper {μ : Wgt A} (hμ : SubLaw μ) (f : Wgt A) (B : ℝ)
    (hf : ∀ i,|f i|≤B) : ode μ f ≤ B^2 := by
  apply hμ.avg_le (sq_nonneg _)
  intro i
  exact (le_of_eq (Eq.symm (pow_two _))).trans
    ((le_of_eq (sq_abs (f i)).symm).trans (pow_le_pow_left₀ (abs_nonneg _) (hf i) 2))

theorem dip_sub (μ f g h : Wgt A) :
    dip μ (fun i=> f i-g i) h=dip μ f h-dip μ g h := by
  unfold dip; simp only [sub_mul,avg_sub]

omit [Fintype B] in
theorem cashbook_bound (μ : Wgt A) (hμ : ∀ i,0≤ μ i) (f : A→B) (g : Wgt A)
    (b : ℝ) (hb : 0≤b) (h : ∀ i,|g i|≤b) (i) : |cashbook μ f g i| ≤ b := by
  have he : cashbook μ f g i=avg (onW μ (fun x=>f x=i)) g := by
    unfold cashbook onW
    rw [avg_norm,subW_tot]
    unfold mapW pr avg subW; congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have hw : SubLaw (onW μ (fun x=>f x=i)) := normW_subLaw (subW_nonneg hμ _)
  rw [he]
  exact (abs_avg_le hw.nz).trans (hw.avg_le hb h)

theorem cash_orth (μ : Wgt A) (hμ : ∀ i,0≤ μ i) (f : A→B) (g : Wgt A) (h : Wgt B) :
    dip μ (banner μ f g) (h ∘ f)=dip μ g (h ∘ f) := by
  classical
  let w := fun x=> μ x*g x
  have he : pour μ f (mapW w f) = fun i => μ i*banner μ f g i := rfl
  have hz : lsupp w μ := fun _ hi => left_ne_zero_of_mul hi
  have ht := map_pour μ f _ (hz.map hμ f)
  rw [he] at ht
  have hi := congrArg (fun w' => avg w' h) ht
  simp_rw [mapW_avg] at hi
  simpa only [w,dip,avg,mul_assoc,Function.comp_apply] using hi

theorem ode_step (μ : Wgt A) (hμ : ∀ i,0≤ μ i) (f : Wgt A)
    (p : A→B) (q : B→C) :
    ode μ (banner μ p f)=ode μ (banner μ (q∘p) f)+
      ode μ (fun i => banner μ p f i - banner μ (q∘p) f i) := by
  classical
  let g := banner μ p f; let h := banner μ (q ∘ p) f
  have hh : ode μ h=dip μ g h :=
    (cash_orth μ hμ (q∘p) f (cashbook μ (q∘p) f)).trans
      (cash_orth μ hμ p f (cashbook μ (q∘p) f ∘ q)).symm
  have hi i : (g i - h i)*(g i-h i)=g i*g i - 2*(g i*h i)+h i*h i := by ring
  change ode μ g=ode μ h+dip μ (fun i => g i-h i) (fun i=>g i-h i)
  unfold dip
  simp_rw [hi,avg_add,avg_sub,avg_mul']
  change ode μ g=ode μ h+(ode μ g-2*dip μ g h + ode μ h)
  linarith only [hh]

theorem archive_gain {μ : Wgt A} (hw : SubLaw μ) (f : Wgt A)
    (p : A→B) (q : B→ C)
    (h : Wgt B) (hh : ∀ i:A,|h (p i)| ≤1) :
    (dip μ (fun i => f i - banner μ (q∘p) f i) (h ∘ p))^2 ≤
      ode μ (banner μ p f)-ode μ (banner μ (q∘p) f) := by
  let u := banner μ p f; let v := banner μ (q∘p) f
  let w i := u i-v i
  rw [ode_step μ hw.nz f p q]
  have he : dip μ (fun i=> f i - banner μ (q∘p) f i) (h∘p)=dip μ w (h∘p) := by
    unfold w
    rw [dip_sub,dip_sub,cash_orth μ hw.nz p f h]
  have ht : ode μ (h∘p) ≤ 1 := (ode_upper hw (h∘p) 1 hh).trans_eq (by ring)
  have hq : dip μ w (h∘p)^2≤ode μ w*ode μ (h∘p) := by
    simpa only [ode,dip,pow_two] using avg_CS hw.nz w (h∘p)
  rw [he]
  apply le_trans hq
  refine (mul_le_mul_of_nonneg_left ht (ode_nonneg hw.nz w)).trans_eq ?_
  unfold w u v
  ring
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RectangleRegularity
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rectangle Regularity -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Function
open scoped BigOperators
variable {A B C K : Type} [Fintype A] [Fintype B] [Fintype C]

theorem swab_abs (x) : |swab x|=1 := by cases x <;> simp [swab]

private theorem sign_mass (w : Wgt A) (f : A→B) (u : Wgt B) (h : ∀ i,|u i|≤1) :
    ∃ y : B→Bool,|avg w (u ∘ f)|≤|avg w (swab ∘ y ∘ f)| := by
  classical
  let p := mapW w f
  let y (i) := decide (0≤p i)
  have he i :
      p i*swab (y i)=|p i| := by
    by_cases hh : 0≤p i <;> simp [swab,y,hh,abs_of_nonneg,abs_of_neg,lt_of_not_ge]
  have hu :
      |avg p u| ≤ ∑ i,|p i| := by
    unfold avg; refine (Finset.abs_sum_le_sum_abs ..).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)).trans_eq (mul_one _)
  have hz : avg p (swab ∘ y) = ∑ i, |p i| := Finset.sum_congr rfl fun i _=> he i
  refine ⟨y,?_⟩
  rw [show avg w (u∘f)=avg p u from (mapW_avg w f u).symm,show avg w (swab∘y∘f)=
    avg p (swab∘y) from (mapW_avg w f (swab ∘ y)).symm]
  exact hu.trans (hz.symm.le.trans (le_abs_self _))

theorem cut_witness (μ f : Wgt A) {x : A→B} {y : A→C} {ε : ℝ} (h : ¬ thinCut μ f x y ε) :
    ∃ (i : B→Bool) (j : C→Bool), ε < |avg μ (fun z=>f z*(swab (i (x z))*swab (j (y z))))| := by
  classical
  unfold thinCut at h
  push Not at h
  obtain ⟨u,hu,v,hv,h⟩ := h
  let Q (u : Wgt B) (v : Wgt C) := avg μ (fun z=>f z*(u (x z)*v (y z)))
  let U z := μ z*f z*v (y z)
  obtain ⟨i,hi⟩ := sign_mass U x u hu
  have hx (u) : Q u v=avg U (u∘x) := Finset.sum_congr rfl (fun z _=>by unfold U Function.comp; ring)
  let V z := μ z*f z*swab (i (x z))
  obtain ⟨j,hj⟩ := sign_mass V y v hv
  have hy (v) : Q (swab ∘ i) v=avg V (v∘y) := Finset.sum_congr rfl (fun z _=>by
    unfold V Function.comp; ring)
  rw [←hx u,show avg U (swab ∘ i ∘ x)=Q (swab ∘ i) v from (hx (swab ∘ i)).symm] at hi
  rw [←hy v,show avg V (swab ∘ j ∘ y)=Q (swab ∘ i) (swab∘j) from (hy (swab ∘ j)).symm] at hj
  exact ⟨i,j, lt_of_lt_of_le h (hi.trans hj)⟩

set_option maxHeartbeats 800000 in
theorem plenty_cuts (δ M : ℝ) (hδ : 0<δ) (hM : 0≤M) :
    ∃ r:ℕ,∀ (A B C : Type) [Fintype A] [Fintype B] [Fintype C]
      (μ f : Wgt A) (x : A→B) (y : A→C),SubLaw μ → (∀ i,|f i| ≤ M) →
        weakRank μ f x y δ r := by
  classical
  obtain ⟨l,hl⟩ := exists_nat_gt (M^2 / δ^2)
  refine ⟨2^l,fun A B C _ _ _ μ f x y hw hf => ?_⟩
  by_contra h
  have hh (i : ℕ) (hi : i≤l) :
      ∃ (a:B→Fin (2^i)) (b:C→Fin (2^i)), i*δ^2 ≤ ode μ (banner μ (doubleBook x y a b) f) := by
    induction i with
    | zero => exact ⟨fun _=>0,fun _=>0, by simpa using ode_nonneg hw.nz _⟩
    | succ i ih =>
      obtain ⟨a,b,he⟩ := ih (by omega)
      let T := doubleBook x y a b
      let d := fun z => f z-banner μ T f z
      obtain ⟨u,v,e⟩ := cut_witness μ d (x:=x) (y:=y) (ε:=δ) (fun p =>
        h ⟨_,Nat.pow_le_pow_right (by decide) (by omega),a,b,p⟩)
      let r := 2^i
      let E : Fin r × Bool ≃ Fin (2^(i+1)) := Fintype.equivFinOfCardEq (by simp [r,pow_succ])
      let a' z := E (a z,u z); let b' z := E (b z,v z)
      let S := doubleBook x y a' b'
      let U (z j : Fin (2^(i+1))) := ((E.symm z).1,(E.symm j).1)
      let V (z j : Fin (2^(i+1))) := swab (E.symm z).2*swab (E.symm j).2
      have hz : uncurry U ∘ S=T := by
        funext i; simp only [doubleBook,a',b',Function.comp_apply,U,S,uncurry_apply_pair,
          Equiv.symm_apply_apply]; rfl
      have hH (i) : uncurry V (S i)=swab (u (x i))*swab (v (y i)) := by
        simp only [S,doubleBook,a',b',V,uncurry_apply_pair,Equiv.symm_apply_apply]
      have hh (i) : |uncurry V (S i)| ≤ 1 := by rw [hH,abs_mul,swab_abs,swab_abs,mul_one]
      have hq := archive_gain hw f S (uncurry U) (uncurry V) hh
      rw [hz] at hq
      have ht : dip μ d (uncurry V ∘ S)=
          avg μ (fun z => d z*(swab (u (x z))*swab (v (y z)))) :=
        avg_congr (fun i _=> congrArg _ (hH i))
      change (dip μ d _)^2≤_ at hq
      rw [←ht] at e
      refine ⟨a',b',?_⟩
      change ↑(i+1)*δ^2≤ode μ (banner μ S f)
      change ↑i*δ^2≤ode μ (banner μ T f) at he
      push_cast
      nlinarith only [he,hq,e,sq_abs (dip μ d (uncurry V ∘ S)),hδ]
  obtain ⟨a,b,he⟩ := hh l le_rfl
  let F := doubleBook x y a b
  have hb := cashbook_bound μ hw.nz F f M hM hf
  have ht := he.trans (ode_upper hw _ M (fun i : A=> hb (F i)))
  exact not_lt_of_ge ht ((div_lt_iff₀ (by positivity)).mp hl)
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SinglePositionExpansion
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Single Position Expansion -/

noncomputable section
namespace HadwigerCounterexample
open Finset Function Matrix
open scoped BigOperators
variable {I A B C : Type} [Fintype I] [DecidableEq I]
variable {p : Shape} {n N : ℕ}
variable {X : I → Type}

theorem chair_split (p : ∀ i,Wgt (X i)) (x : ∀ i,X i) (a : I) :
    prodW p x = p a (x a) *
      prodW (fun i : Aside a=>p i.val) ((chair X a x).2) := by
  exact Fintype.prod_eq_mul_prod_subtype_ne _ _

variable [∀ i,Fintype (X i)]
set_option maxHeartbeats 600000 in
theorem chair_weight (p : ∀ i,Wgt (X i)) (a : I) :
    mapW (prodW p) (chair X a)= pairW (p a)
      (prodW (fun i : Aside a=>p i.val)) := by
  funext i
  obtain ⟨i,rfl⟩ := (chair X a).surjective i
  rw [mapW_equiv_val,Equiv.symm_apply_apply]; exact chair_split p i a

namespace Template
variable (v : Template p I)

omit [Fintype I] in
theorem key_split (v : Template p I) (x : I) (o : UnitType p n N)
    (z : Inputs p n I) :
    chairK v x N (v.resultKey o z) = (v.callOne x (z x) (onSide o (v.aim x)),
      (v.beyond x).resultKey o (fun i=>z i.val)) := by
  apply Prod.ext <;> rfl

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_UnaryCellComparisons
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unary Cell Comparisons -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Finset Function Filter
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I J A : Type} [Fintype I] [DecidableEq I] [Fintype J]

namespace Template
variable (v : Template p I)

theorem astonish_val (v : Template p I) (q : I→F) (U : Wgt (Keys (p:=p) v.t N))
    (s : Script p I) (m : Mixer p n) (w f : I→Wgt (Knobs p.g n)) (o) :
    astonish v q U s m w f o=
      avg (prodW w) (fun i => ind (earns v s m q o i)*U (resultKey v o i)*prodW f i) := by
  unfold astonish earns scene protean curtain propel
  simp_rw [ind_and]; exact avg_congr fun i _=>by ring

omit [DecidableEq I] in
theorem design_mono (v : Template p I) (w : Wgt (Keys (p:=p) v.t N))
    (M : ℝ) (r s : ℕ) (hM : 0 ≤ M) (h : r ≤ s) (hr : design v w M r) :
    design v w M s := by
  classical
  obtain ⟨f,hf,hg⟩ := hr
  let g (i : Fin s) : Paint v N := if h:i.val < r then f ⟨i.val,h⟩ else ⟨0,fun _ _=>True⟩
  let k := Fin.castLE h
  have hi i : g (k i)=f i := by unfold g k; simp
  refine ⟨g,funext fun x=>?_,fun i=>?_⟩
  · rw [hf]
    unfold mural
    have h1 :
        ∑ i:Fin r, (f i).cost x =∑ i∈ Finset.univ.image k,(g i).cost x := by
      rw [Finset.sum_image (Fin.castLE_injective h).injOn]
      exact Finset.sum_congr rfl (fun i _ => congrArg (fun t=> t.cost x) (hi i).symm)
    rw [h1]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hh
    have hp : ¬i.val < r := fun he => hh (mem_image.mpr ⟨⟨i.val,he⟩,mem_univ _,rfl⟩)
    unfold g Paint.cost; simp only [dite_eq_right hp,zero_mul]
  unfold g; split
  next h => exact hg _
  next h => simpa using hM

theorem join_cost (v : Template p I) (x : I) (d : AtomKey (p:=p) (v.t x) N → Prop)
    (w : Paint (v.beyond x) N) (k) :
    (paintJoin v x d w).cost k=ind (d (k x))*w.cost ((v.chairK x N k).2) := by
  classical
  unfold Paint.cost
  rw [chair_split _ _ x]
  let f := paintJoin v x d w
  have ht : f.flies x=d := by unfold f paintJoin; simp
  have hi (i:Aside x) : f.flies i.val=w.flies i :=
    dite_eq_right i.property
  rw [ht]
  have hh : prodW (fun i : Aside x => fun j => ind (f.flies i.val j))
      ((v.chairK x N k).2)=prodW (fun i j => ind (w.flies i j)) ((v.chairK x N k).2) :=
    Finset.prod_congr rfl (fun i _=>congrArg _ (congr_fun (hi i) _))
  change w.coeff* (_ * prodW (fun i : Aside x => fun j => ind (f.flies i.val j))
      ((v.chairK x N k).2))=_
  rw [hh]
  ring

set_option maxHeartbeats 600000 in
theorem design_patch (v : Template p I) (x : I) (r s : ℕ)
    (a : AtomKey (p:=p) (v.t x) N → Fin r)
    (B : Fin r → Wgt (Keys (p:=p) (v.beyond x).t N)) (M : ℝ)
    (h : ∀ i,design (v.beyond x) (B i) M s) :
    design v (patched v x a B) M (r*s) := by
  classical
  choose p' hg hp using h
  let g : Fin r × Fin s ≃ Fin (r*s) := Fintype.equivFinOfCardEq (by simp)
  let f (i : Fin r × Fin s) :=
    paintJoin v x (fun j=>a j=i.1) (p' i.1 i.2)
  refine ⟨f ∘ g.symm,?_,fun i => hp _ _⟩
  funext i; unfold patched mural
  rw [← Equiv.sum_comp g]
  simp_rw [Function.comp_apply,Equiv.symm_apply_apply,f,join_cost]
  rw [Fintype.sum_prod_type]; simp_rw [← Finset.mul_sum]
  rw [Finset.sum_eq_single (a (i x))]
  · rw [ind_one (show a (i x)=a (i x) from rfl),one_mul,hg]
    rfl
  · intro j _ hj; rw [ind_zero (Ne.symm hj),zero_mul]
  simp
end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FixedPositionTests
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed Position Tests -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

namespace Template
variable (v : Template p I)

omit [Fintype I] in
theorem bolts_split (v : Template p I) (j : I) (q : I→F)
    (x : Keys (p:=p) v.t N) :
    ownPart (p:=p) v.t q x ↔
      ownOne p (v.t j) (q j) (x j) ∧ (∀ i:Aside j,v.bolts (x j) (x i.val)) ∧
      ownPart (p:=p) (v.beyond j).t (v.boundTail j q) ((v.chairK j N x).2) := by
  classical
  rw [ownPart_def,ownPart_def]
  let f (i k : I) := ∀ (e : Comp p.g) (h : inc e (v.t i)) (h' : inc e (v.t k)),
    i≠k→dotProduct (x i ⟨e,h⟩ true) (x k ⟨e,h'⟩ false)=0
  let r := v.beyond j
  constructor
  · rintro ⟨h1,h2⟩
    refine ⟨h1 j,fun k e a b=> ⟨h2 j k.val e a b (Ne.symm k.property),
      h2 k.val j e b a k.property⟩,fun i=> h1 i.val,?_⟩
    intro i k e a b hh; exact h2 _ _ e a b (fun ht=>hh (Subtype.ext ht))
  rintro ⟨h1,h2,h,h'⟩
  constructor
  · intro i
    by_cases hh:i=j
    · subst i; exact h1
    exact h ⟨i,hh⟩
  intro i k e a b hi
  by_cases he : i=j
  · subst i; exact (h2 ⟨k,Ne.symm hi⟩ e a b).1
  by_cases hh : k=j
  · subst k; exact (h2 ⟨i,hi⟩ e b a).2
  exact h' (⟨i,he⟩) (⟨k,hh⟩) e a b (fun h=>hi (congrArg Subtype.val h))

omit [Fintype I] in
theorem read_split (v : Template p I) (j:I) (m : Mixer p n) (s : Script p I)
    (z : Inputs p n I) :
    (v.draw z).reads s m ↔
      (∀ i:Aside j,v.huts m s j i.val (z j) (z i.val)) ∧
      ((v.beyond j).draw (fun i => z i.val)).reads (scriptTail s j) m := by
  constructor
  · intro h
    constructor
    · exact fun i hA v=> ⟨h j i.val (Ne.symm i.property) hA v,h i.val j i.property
        (Eq.symm hA) v⟩
    intro x y he ha i; exact h x.val y.val (fun ht=>he (Subtype.ext ht)) ha i
  rintro ⟨h1,h2⟩ i k he ha d
  by_cases hh:i=j
  · subst i; exact (h1 ⟨k,Ne.symm he⟩ ha d).1
  by_cases hz:k=j
  · subst k; exact (h1 ⟨i,hh⟩ (Eq.symm ha) d).2
  exact h2 (⟨i,hh⟩) (⟨k,hz⟩) (fun h=>he (congrArg Subtype.val h)) ha d

omit [Fintype I] in
theorem earns_split (v : Template p I) (j : I) (q : I→F) (m : Mixer p n) (s : Script p I)
    (o : UnitType p n N) (z : Inputs p n I) :
    earns v s m q o z↔ ownOne p (v.t j) (q j) (nib v o j (z j)) ∧
      (∀ i:Aside j,v.lintel j m s o (z j) i (z i.val)) ∧
      earns (v.beyond j) (scriptTail s j) m (v.boundTail j q) o
        (fun i:Aside j => z i.val) := by
  unfold earns lintel
  rw [read_split v j,bolts_split v j, key_split]
  have he (i : I) : resultKey v o z i=nib v o i (z i) := rfl
  simp_rw [he,forall_and]
  tauto
end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FullTemplateComparison
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full Template Comparison -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I J A B : Type} [Fintype I] [DecidableEq I]

theorem ab_cut (p : Prop) (x : ℝ) (hx : |x|≤1) : |ind p*x|≤1 := by
  classical
  by_cases h : p
  · rwa [ind_one h,one_mul]
  rw [ind_zero h,zero_mul]; norm_num

theorem lift_window [Fintype A] [Fintype B] {u : Wgt A} (hu : IsLaw u)
    (v : Wgt B) (r : Wgt (A×B)) (s : Wgt A) (g : A→ Wgt B)
    (hr : ∀ i, r i = s i.1*g i.1 i.2) (hs : ∀ i, |s i|≤1) (ε : ℝ)
    (hh : ∀ i, |avg v (g i)| ≤ ε) : |avg (pairW u v) r|≤ ε := by
  rw [pairW_avg]
  simp_rw [hr,avg_mul']
  apply (abs_avg_le hu.nz).trans
  exact hu.avg_le (fun i => by
    rw [abs_mul]; exact (mul_le_mul (hs _) (hh _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _))

namespace Template
variable (v : Template p I)

set_option maxHeartbeats 800000 in
theorem patched_board (v : Template p I) (j : I) (q : I→ F) (a : AtomKey (p:=p) (v.t j) N→ J)
    (B : J → Wgt (Keys (p:=p) (v.beyond j).t N)) (ε : ℝ)
    (h : ∀ i, shadowed (v.beyond j) (v.boundTail j q) (B i) ε) :
    shadowed v q (patched v j a B) ε := by
  classical
  intro f hf
  let t:=v.beyond j; let Q:=v.boundTail j q
  let E := chairK v j N
  let F (x : Keys (p:=p) v.t N) :=
    v.curtain q (v.patched j a B) x * prodW f x
  let s (x : AtomKey (p:=p) (v.t j) N) := ind (ownOne p _ (q j) x)*f j x
  let g (x : AtomKey (p:=p) (v.t j) N) : Localist t N := fun i z=> ind (v.bolts x z)*f i.val z
  let G x (y : Keys (p:=p) t.t N) := curtain t Q (B (a x)) y * prodW (g x) y
  have he k : (F ∘ E.symm) k=s k.1 * G k.1 k.2 := by
    obtain ⟨k,rfl⟩ := E.surjective k
    simp only [Function.comp_apply,Equiv.symm_apply_apply]
    unfold F curtain
    rw [bolts_split v j,chair_split _ _ j]; simp only [ind_and,ind_all]
    change _ * v.patched _ _ _ k * (f j (k j)* _)=s (k j)*G (k j) (E k).2
    unfold s G patched curtain g
    unfold prodW
    rw [Finset.prod_mul_distrib]
    exact (show ∀ (a b c d e f : ℝ), a*(b*c)*d*(e*f)=(a*e)*(c*d*(b*f)) from by intro a b c d e f; ring) _ _ _ _ _ _
  have hh (x) : |avg unif (G x)|≤ε := h (a x) _ (fun i y=>ab_cut _ _ (hf _ _))
  have hz (x) : |s x|≤1 := ab_cut _ _ (hf _ _)
  have ht : mapW unif E= pairW unif unif := by rw [←pair_unif,unif_equiv]
  have hl := lift_window unif_law unif _ _ _ he hz ε hh
  rw [←ht,mapW_avg] at hl
  simp only [Function.comp_apply,Equiv.symm_apply_apply] at hl; exact hl

set_option maxHeartbeats 800000 in
theorem patched_exceed (v : Template p I) (j : I) (q : I→F) (a : AtomKey (p:=p) (v.t j) N→J)
    (B : J → Wgt (Keys (p:=p) (v.beyond j).t N)) (ε : ℝ)
    (w : I→Wgt (Knobs p.g n)) (hw : ∀ i,IsLaw (w i))
    (s : Script p I) (m : Mixer p n) (o : UnitType p n N)
    (h : ∀ i,¬ exceeds (v.beyond j) (v.boundTail j q) (B i) (scriptTail s j)
      m (fun i => w i.val) ε o) :
    ¬ exceeds v q (patched v j a B) s m w ε o := by
  classical
  rintro ⟨f,hf,hZ⟩
  let x' := patched v j a B
  apply not_lt_of_ge _ hZ
  change |astonish v q x' s m w f o|≤ε
  rw [astonish_val]
  let v' := v.beyond j; let Q := v.boundTail j q
  let E := chairI v j n
  let R := scriptTail s j
  let U (i : Inputs p n I) := ind (earns v s m q o i)*x' (v.resultKey o i)*prodW f i
  let K := Knobs p.g n
  let x (z : K) := nib v o j z
  let g (i : K) (t : Aside j) (z : K) := ind (v.lintel j m s o i t z)*f t.val z
  let C (i) := ind (ownOne p _ (q j) (x i))*f j i
  let G i (y : Inputs p n (Aside j)) :=
    ind (earns v' R m Q o y)*B (a (x i)) (v'.resultKey o y)*prodW (g i) y
  have he k : (U ∘ E.symm) k=C k.1*G k.1 k.2 := by
    obtain ⟨k,rfl⟩ := E.surjective k
    simp only [Function.comp_apply,Equiv.symm_apply_apply]
    unfold U
    rw [earns_split v j,chair_split _ _ j]; simp only [ind_and,ind_all]
    unfold x' patched; rw [key_split]
    unfold C G g prodW
    rw [Finset.prod_mul_distrib]
    dsimp only [x,E,v',R,chairI,chair]
    change _ * B (a (nib v o j (k j))) _ * _ = _
    unfold nib
    dsimp only [Q,Equiv.piSplitAt,Equiv.coe_fn_mk]
    ring
  let W := prodW (fun i:Aside j=> w i.val)
  have hh (i) : |avg W (G i)|≤ ε := by
    have hz (k z) : |g i k z|≤1 := ab_cut _ _ (hf _ _)
    have hb : |astonish v' Q (B (a (x i))) R m (fun i=>w i.val) (g i) o|≤ε :=
      le_of_not_gt (fun hb=>h (a (x i)) ⟨g i,hz,hb⟩)
    rw [astonish_val] at hb; exact hb
  have hC i : |C i|≤1 := ab_cut _ _ (hf _ _)
  have ht : mapW (prodW w) E=pairW (w j) W := chair_weight w j
  have hz := lift_window (hw j) W _ _ _ he hC ε hh
  rw [←ht,mapW_avg] at hz
  simp only [Function.comp_apply,Equiv.symm_apply_apply] at hz
  exact hz

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_HeadPartitionComparison
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Head Partition Comparison -/

noncomputable section
namespace HadwigerCounterexample
open Finset Filter Function
open scoped BigOperators
variable {p : Shape} {n N M : ℕ} {I : Type} [Fintype I] [DecidableEq I]

namespace Template
variable (v : Template p I)

set_option maxHeartbeats 800000 in
theorem shattered (v : Template p I) (j : I)
    (B L δ : ℝ) (hL : 0<L) (hB : 0≤B) (h : 2*B≤L) (hd : 0<δ) :
    ∃ r : ℕ,∀ N : ℕ,∀ q : I→F, ∀ U : Wgt (Keys (p:=p) v.t N),(∀ i, |U i|≤B) →
      ∃ l : ℕ,l ≤ r ∧ ∃ (a : AtomKey (p:=p) (v.t j) N→ Fin l)
        (b : Fin l→ Wgt (Keys (p:=p) (v.beyond j).t N)),
      (∀ i x,|b i x|≤B)∧
      let R i := curtain v q (U-patched v j a b) i / L
      (∀ i,|R i|≤1) ∧ chairCut v j R δ ∧ carried R (ownPart (p:=p) v.t q) := by
  classical
  obtain ⟨r,hr⟩ := plenty_cuts (δ*L) B (by positivity) hB
  refine ⟨r,fun N q U hU=>?_⟩
  let A:=Keys (p:=p) v.t N
  let E:=chairK v j N
  let f := Prod.fst ∘ E; let g:=Prod.snd ∘ E
  let P := ownPart (p:=p) v.t q (N:=N)
  let w := subW unif P
  have hw : SubLaw w := subLaw_sub unif_law.sub _
  obtain ⟨l,hl,a,b,he⟩ := hr A _ _ w U f g hw hU
  let T:= doubleBook f g a b
  let B' (i : Fin l) (x) := cashbook w T U (i,b x)
  have hx (i x) : |B' i x|≤B := cashbook_bound w hw.nz T U B hB hU _
  refine ⟨l,hl,a,B',hx,?_,?_,?_⟩
  · intro k
    change |ind (P k)* (U k-B' (a (k j)) ((E k).2))/L|≤1
    rw [abs_div,abs_of_pos hL,div_le_iff₀ hL,one_mul]
    by_cases hz : P k
    · rw [ind_one hz,one_mul]
      exact ((abs_sub ..).trans ((add_le_add (hU _) (hx _ _)).trans_eq (two_mul _).symm)).trans h
    rw [ind_zero hz,zero_mul,abs_zero]; exact hL.le
  · intro u hu t ht
    have hi :
        patched v j a B'=banner w T U := rfl
    let W (k:A) := (U k-banner w T U k)*(u (f k)*t (g k))
    have hh :
        avg unif (fun k:A=> curtain v q (U - patched v j a B') k / L * (u (f k)*t (g k))) =
          avg w W/L := by
      rw [hi]
      unfold avg curtain W w P; simp only [div_eq_mul_inv,Finset.sum_mul]; unfold subW
      exact sum_congr rfl fun i _=> by simp only [Pi.sub_apply] <;> ring
    change |avg unif (fun k:A=> curtain v q (U - patched v j a B') k / L * (u (f k)*t (g k)))|≤_
    rw [hh,abs_div,abs_of_pos hL,div_le_iff₀ hL]
    exact he u hu t ht
  intro i hi
  change ind _ * _/L=0; rw [ind_zero hi,zero_mul,zero_div]

theorem chair_board (v : Template p I) (j : I) (q : I→F) (U : Wgt (Keys (p:=p) v.t N))
    (L δ : ℝ) (hL : 0<L) (h : chairCut v j (fun i=> curtain v q U i/L) δ) :
    shadowed v q U (δ*L) := by
  classical
  intro f hf
  let E:=chairK v j N; let t:=fun i : Aside j=> f i.val
  let g := prodW t
  have hg (x): |g x|≤1 := by
    unfold g prodW; rw [abs_prod]
    exact (Finset.prod_le_prod (fun _ _=>abs_nonneg _) (fun i _=>hf _ _)).trans_eq (by simp)
  let R := fun i=> curtain v q U i/L
  let V (i:Keys (p:=p) v.t N) := R i*(f j (E i).1*g (E i).2)
  have hh : |avg unif V|≤δ := h (f j) (hf j) g hg
  have hi : board v q U f=avg unif V*L := by
    unfold board; rw [←avg_mul]
    apply avg_congr; intro i _
    rw [chair_split _ _ j]
    change curtain v q U i*(f j (E i).1*g (E i).2)=_
    unfold V R; field_simp
  rw [hi,abs_mul,abs_of_pos hL]
  exact mul_le_mul_of_nonneg_right hh hL.le

theorem put_back (v : Template p I) (q : I→F) (U : Wgt (Keys (p:=p) v.t N)) (L : ℝ)
    (s : Script p I) (m : Mixer p n) (w f : I→Wgt (Knobs p.g n))
    (o : UnitType p n N) :
    scene v (propel v s m) (fun i=> curtain v q U i/L) w f o=
      astonish v q U s m w f o / L := by
  unfold astonish scene; rw [← avg_div]; exact avg_congr fun x _=>by unfold protean; ring
end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RecursiveComparisonErrors
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recursive Comparison Errors -/

noncomputable section
namespace HadwigerCounterexample
open Finset Function Filter Matrix
open scoped BigOperators
variable {p : Shape} {I : Type} [Fintype I] [DecidableEq I] {n N : ℕ}
namespace Template
variable (v : Template p I)

theorem board_add (v : Template p I) (q : I→F) (U V : Wgt (Keys (p:=p) v.t N)) f :
    board v q (U+V) f=board v q U f+board v q V f := by
  unfold board curtain; simp only [Pi.add_apply,mul_add,add_mul,avg_add]

theorem shadow_add (v : Template p I) (q : I→F) (U V : Wgt (Keys (p:=p) v.t N))
    (r s : ℝ) (h : shadowed v q U r) (h' : shadowed v q V s) :
    shadowed v q (U+V) (r+s) := fun f hf => by
  rw [board_add]
  exact (abs_add_le _ _).trans (add_le_add (h f hf) (h' f hf))

theorem scene_join (v : Template p I) (q : I→ F) (U V : Wgt (Keys (p:=p) v.t N))
    (s : Script p I) (m : Mixer p n) (w : I→Wgt (Knobs p.g n))
    (x y : ℝ) (o : UnitType p n N)
    (h : exceeds v q (U+V) s m w (x+y) o) :
    exceeds v q U s m w x o ∨ exceeds v q V s m w y o := by
  classical
  obtain ⟨f,hf,h'⟩ := h
  have he :
      astonish v q (U+V) s m w f o=astonish v q U s m w f o+astonish v q V s m w f o := by
    simp only [astonish_val,Pi.add_apply,mul_add,add_mul,avg_add]
  change x+y < |astonish v q (U+V) s m w f o| at h'
  rw [he] at h'
  by_contra! hh
  have ht : |astonish v q U s m w f o|≤x := le_of_not_gt (fun h=>hh.1 ⟨f,hf,h⟩)
  have hv : |astonish v q V s m w f o|≤y := le_of_not_gt (fun h=>hh.2 ⟨f,hf,h⟩)
  exact not_lt_of_ge ((abs_add_le _ _).trans (add_le_add ht hv)) h'

set_option maxHeartbeats 800000 in
theorem gild_play (v : Template p I) (j : I) (q : I→F) (n N r : ℕ)
    (a : AtomKey (p:=p) (v.t j) N→Fin r) (B B' : Fin r→ Wgt (Keys (p:=p) (v.beyond j).t N))
    (U : Wgt (Keys (p:=p) v.t N)) (C ε x y : ℝ)
    (hs : shadowed v q (U-patched v j a B) ε)
    (h : engaged v q (U-patched v j a B) n C x ε)
    (hg : ∀ i,shadowed (v.beyond j) (v.boundTail j q) (B i-B' i) ε)
    (hh : ∀ i,engaged (v.beyond j) (v.boundTail j q) (B i-B' i) n C y ε) :
    let d:=U-patched v j a B'
    shadowed v q d (ε+ε) ∧ engaged v q d n C (x+r*y) (ε+ε) := by
  classical
  intro d
  let f:=U-patched v j a B
  let V z := B z - B' z
  let g:=patched v j a V
  have hd : d=f+g := by
    unfold d f g V; ext i; unfold patched; simp only [Pi.add_apply,Pi.sub_apply]
    ring
  rw [hd]
  refine ⟨shadow_add v q f g ε ε hs (patched_board v j q a V ε hg),?_⟩
  intro m hN w hw s u hu hz
  let W (i) := exceeds (v.beyond j) (v.boundTail j q) (V i) (scriptTail s j) m
    (fun i=>u i.val) ε
  have he (o) (hf : exceeds v q g s m u ε o) : ∃ i,W i o := by
    by_contra! hx
    exact patched_exceed v j q a V ε u hu s m o hx hf
  have hn := hw.1
  have hi :
      pr w (fun x => ∃ i:Fin r,W i x) ≤ (r:ℝ)*y := by
    refine (pr_exists_le hn.nz W).trans ((Finset.sum_le_sum
      (g:=fun _=>y) (fun i _=>?_)).trans_eq (by simp))
    exact hh i m hN w hw (scriptTail s j) _ (fun i =>hu i.val) (fun i =>hz i.val)
  apply (le_trans (pr_mono hn.nz (fun i => scene_join v q f g s m u _ _ i)) (pr_or_le hn.nz)).trans
  exact add_le_add (h m hN w hw s u hu hz) ((pr_mono hn.nz he).trans hi)
end Template
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

end Appearance
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ProductComparisonScales
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product Comparison Scales -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Function Finset Filter
open scoped BigOperators
variable {p : Shape} {n N M : ℕ} {I : Type} [Fintype I] [DecidableEq I]
namespace Template
variable (v : Template p I)

theorem play_empty (v : Template p I) (M : ℕ) (C b ε : ℝ) [IsEmpty I]
    (hε : 0≤ε) :
    play v M C b ε := by
  classical
  refine ⟨1,1,zero_lt_one,.of_forall (fun n => ?_)⟩
  intro N q U hU
  let i : Keys (p:=p) v.t N := 0
  refine ⟨U, ⟨fun _ => ⟨U i,fun _ _=> True⟩,?_,fun _=>hU _⟩,fun f h=>?_,
    fun m hN w hw s x h hh =>?_⟩
  · funext x
    simp only [mural,Paint.cost,prodW,ind_true,prod_const_one,mul_one,sum_const,
      card_univ,Fintype.card_fin,one_smul]
    exact congrArg U (Subsingleton.elim x i)
  · simp only [board,sub_self,curtain,Pi.zero_apply,mul_zero,zero_mul,avg_zero,abs_zero]
    exact hε
  · have ht o : ¬ exceeds v q (U-U) s m x ε o := by
      rintro ⟨f,_,hh⟩
      simp only [scene,protean,curtain,sub_self,Pi.zero_apply,mul_zero,zero_mul,avg_zero,
        abs_zero] at hh
      exact (not_lt_of_ge hε) hh
    rw [show exceeds _ _ _ _ _ _ _=(fun _=>False) from funext fun i=>propext ⟨ht i,False.elim⟩,
      pr_false]; exact (bp_pos _).le

set_option maxHeartbeats 1200000 in
theorem play_step (v : Template p I) (j : I) (M : ℕ) (hM : 1≤ M) (C b ε : ℝ)
    (hb : 0≤b) (hε : 0<ε)
    (h : play (v.beyond j) M C b (ε/2)) :
    play v M C b ε := by
  classical
  let u:= ε/2; let L:=1+2*b; have hu : 0<u := by positivity
  have hL : 0<L := by positivity
  obtain ⟨δ,hδ,hh⟩ := shade_calendar v j M hM C (u/L) (by positivity)
  let d := min δ (u/L)
  have hd : 0<d := lt_min hδ (by positivity)
  obtain ⟨s,hs⟩ := shattered v j b L d hL hb (by unfold L; linarith) hd
  obtain ⟨r,c,hc,h⟩ := h
  let t := min (1/16:ℝ) c
  have ht : 0<t := lt_min (by norm_num) hc
  refine ⟨s*r,t/2,by linarith,?_⟩
  filter_upwards [hh,h,pay_nat (a:=t) (b:=t/2) ((s:ℝ)+1) (by linarith)]
    with n hn h ha N q U hU
  obtain ⟨l,hl,a,B,hb',hs,hQ,hW⟩ := hs N q U hU
  let V:= patched v j a B
  let W := U-V
  let R i := curtain v q W i/L
  let T:=v.beyond j
  let Q:= v.boundTail j q
  choose g h1 h2 h3 using fun i=> h Q (B i) (hb' i)
  let D := patched v j a g
  have hT : shadowed v q W u := by
    have he := chair_board v j q W L d hL hQ
    have hm : d*L ≤ u := (le_div_iff₀ hL).mp (min_le_right ..)
    exact fun i hi => (he i hi).trans hm
  have hx : engaged v q W n C (bp (-(1/16:ℝ)*n)) u := by
    intro m hN w hw s x hx hz
    have he : chairCut v j R δ :=
      fun i hi k hk=> (hQ i hi k hk).trans (min_le_left ..)
    have hg (x) : |propel v s m x|≤1 := by
      unfold propel; rw [abs_of_nonneg (ind_nonneg _)]
      exact ind_le_one _
    obtain ⟨hw,hv,h',hm'⟩ := hw
    have h4 := hn q R (propel v s m) x hs he hW hg hx hz m hN w hw hv h' hm'
    refine (pr_mono hw.nz (fun i hh => ?_)).trans h4
    obtain ⟨f,hf,hg⟩ := hh
    refine ⟨f,hf,?_⟩
    unfold R
    rw [put_back v q W L,abs_div,abs_of_pos hL]
    exact div_lt_div_of_pos_right hg hL
  have hg := gild_play v j q n N l a B g U C u _ _ hT hx h2 h3
  have heq : u+u=ε := by unfold u; ring
  dsimp only at hg
  rw [heq] at hg
  refine ⟨D,design_mono v D b _ (s*r) hb (Nat.mul_le_mul_right r hl)
    (design_patch v j l r a g b h1),hg.1,?_⟩
  intro m hN w hw s' x hx hz
  apply (hg.2 m hN w hw s' x hx hz).trans
  apply le_trans ?_ ha
  let z := bp (-t*n)
  have h1 : bp (-c*n)≤ z := bp_le (by gcongr; exact min_le_right ..)
  have h2 : bp (-(1/16:ℝ)*n)≤ z := bp_le (by gcongr; exact min_le_left ..)
  exact (add_le_add h2 (mul_le_mul (by exact_mod_cast hl) h1 (bp_pos _).le
    (Nat.cast_nonneg s))).trans_eq (by ring)

theorem plays_calendar (p : Shape) (M : ℕ) (hM : 1≤M) (C b : ℝ) (hb : 0 ≤ b)
    (r : ℕ) :
    ∀ (I : Type) [Fintype I] [DecidableEq I],Fintype.card I ≤ r →
      ∀ v : Template p I,∀ ε : ℝ,0< ε→play v M C b ε := by
  classical
  induction r with
  | zero =>
    intro I inst h hi v ε he
    have : IsEmpty I := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hi)
    exact play_empty v M C b ε he.le
  | succ r ih =>
    intro I _ _ h v ε he
    cases isEmpty_or_nonempty I
    next => exact play_empty v M C b ε he.le
    next hi =>
      obtain ⟨i⟩:=hi
      apply play_step v i M hM C b ε hb he
      refine ih _ ?_ _ _ (half_pos he)
      have hh : Fintype.card (Aside i)+1=Fintype.card I := by
        have hg := Fintype.card_congr (Equiv.optionSubtypeNe i)
        simpa only [Aside,Fintype.card_option] using hg
      omega
end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_WeakProductComparison
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.mem_fieldRad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weak Product Comparison -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix LinearMap Function Filter
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]
namespace Template
variable (v : Template p I)

theorem shadow_norm (v : Template p I) (q : I→F) (U : Wgt (Keys (p:=p) v.t N))
    (ε : ℝ) (h : shadowed v q U ε)
    (hN : 2*num (I × Toast p)-(N:ℝ)≤ -1) :
    let W := netFact (trayPort p v.t)
    ∀ f : v.Localist N,(∀ i j,|f i j|≤1) →
      |avg (lawNu p N v.t q) (fun x=> U x*prodW f x)| ≤ W*ε := by
  classical
  intro W f hf
  let B := pr unif (ownPart (p:=p) v.t q (N:=N))
  have ht := priceNu v.t q hN
  have hW : 0<W := netFact_pos
  have hb : 0<B := (inv_pos_of_pos hW).trans_le ht
  let F i := U i * prodW f i
  have hh :
      board v q U f=B*avg (lawNu p N v.t q) F := by
    change _=pr _ (ownPart (p:=p) v.t q)*avg (unifOn _) _
    rw [← part_reset _ F hb]
    unfold board curtain F partMean
    simp only [mul_assoc]
  have he := h f hf; rw [hh,abs_mul,abs_of_pos hb] at he
  apply le_of_mul_le_mul_left _ (inv_pos_of_pos hW)
  exact ((mul_le_mul_of_nonneg_right ht (abs_nonneg _)).trans he).trans_eq (by field_simp)

set_option maxHeartbeats 600000 in
theorem weakly (v : Template p I) (M : ℕ) (hM : 1 ≤ M)
    (C ε b : ℝ) (hε : 0<ε) (hb : 0≤ b) :
    ∃ (r : ℕ) (c : ℝ), 0 < c ∧ ∀ᶠ n : ℕ in atTop, let N:= M*n
    ∀ (q : I→F) (U : Wgt (Keys (p:=p) v.t N)), (∀ i, |U i|≤ b) →
    ∃ T, design v T b r ∧
      (∀ f : v.Localist N,(∀ i j, |f i j|≤1) →
        |avg (lawNu p N v.t q) (fun x=> (U x-T x)*prodW f x)|≤ ε) ∧
      engaged v q (U-T) n C (bp (-c*n)) ε := by
  classical
  let W:=netFact (trayPort p v.t)
  have hW : 0<W := netFact_pos
  let u := min ε (ε/W)
  have hu : 0<u := lt_min hε (by positivity)
  obtain ⟨r,c,hc,h⟩ := plays_calendar p M hM C b hb (Fintype.card I) I (le_refl _) v u hu
  refine ⟨r,c,hc,?_⟩
  filter_upwards [h,(cast_tops M hM).eventually
    (eventually_ge_atTop (2*num (I × Toast p)+1))]
    with n hn hN N q U hU
  change 2*num (I×Toast p)+1 ≤ (N:ℝ) at hN
  obtain ⟨T,hT,hQ,h⟩:=hn q U hU
  refine ⟨T,hT,fun f hf=>?_,?_⟩
  · have he := shadow_norm v q (U-T) u hQ (by linarith only [hN]) f hf
    have hh : W*u≤ ε := by rw [mul_comm]; exact (le_div_iff₀ hW).mp (min_le_right ..)
    exact he.trans hh
  intro m hN w hw s x hx hz
  refine (pr_mono hw.1.nz (fun i hh=>?_)).trans (h m hN w hw s x hx hz)
  obtain ⟨f,hf,hg⟩ := hh
  exact ⟨f,hf,lt_of_le_of_lt (min_le_left ..) hg⟩
end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SurrogateQueryScores
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Surrogate Query Scores -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
open Template
variable {p : Shape} {n N K M r : ℕ}
namespace StatusAnalysis
variable {q:Format} {d : Rates} {b:Bool}
namespace Quill

variable (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q → F)

theorem allure_apt (h : w.moral t z) (i : Messenger q) :
    (w.allure t z i).apt := canDraw t z h i

variable (o : UnitType p n N)

theorem stencil_floor (s : Charts p n d) (m : Mixer p n) (i v) :
    |w.stencil t z o s m i v|≤1 := by
  unfold stencil; dsimp only; rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _

variable (m : Mixer p n)

theorem seraphFloor (s : Charts p n d) (Y:Silhouette p N r) (i:Messenger q)
    (hw : IsLaw (w.policies t z n i)) (x) :
    0≤ seraph w t z o m s Y i x ∧ seraph w t z o m s Y i x≤1 :=
  let h:= Appearance.reflectedLaw (w.allure t z i) Y hw (parcel b i) o m _ (Y _ (z i) x)

  ⟨h.nz _,(weight_le_tot h.nz _).trans h.total.le⟩

theorem kappaTop : (w.pen t).kappa ≤1 := by
  unfold kappa wavelength
  classical
  have hh : IsLaw (prism (w.pen t).Abbey) := prodW_law (fun _ => unif_law)
  exact (weight_le_tot hh.nz _).trans hh.total.le

theorem painted (s : Charts p n d)
    (x:Inputs p n (Messenger q)) :
    prodW (w.stencil t z o s m) x=
    ind (printed b s t w.sel w.flav m o x=w.amp) := by
  classical
  rw [funext_iff,ind_all]; rfl

theorem prowl_astonish (s : Charts p n d) (W : Wgt (Keys (p:=p) t N)) :
    w.prowl s t z m o W=astonish (w.pen t) z W w.script m (w.policies t z n)
      (w.stencil t z o s m) o := by
  classical

  let v:=w.pen t
  have ht : astonish v z W w.script m (w.policies t z n) (w.stencil t z o s m) o=
    avg (v.state z n) (fun x=> ind (earns v w.script m z o x)*W (v.resultKey o x)*prodW
      (w.stencil t z o s m) x) := astonish_val v z _ _ m _ _ _
  rw [ht]; unfold prowl; apply avg_congr
  intro i _
  rw [painted]
  simp_rw [deposit, earns,ind_and]
  let a:=ind (printed b s t w.sel w.flav m o i=w.amp); let b0:=ind ((v.draw i).reads w.script m)
  let x:= v.resultKey o i; let c:= ind (ownPart v.t z x)
  change a*(b0*c)*W x= (b0*c)*W x*a
  ring

theorem sheen_sun (s : Charts p n d) (Y:Silhouette p N r) (W:Wgt (Keys (p:=p) t N)) :
    w.sheen t z o m s Y W=
      (w.pen t).kappa * avg (lawNu p N t z) (fun x=>W x*prodW (w.seraph t z o m s Y) x) := by
  unfold sheen mirror; rw [←avg_mul']
  apply avg_congr; intro i _; ring

end Quill
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SurrogateProductBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Surrogate Product Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
variable {p:Shape} {n N K r:ℕ} {A:Type} [Fintype A]
open Template
namespace StatusAnalysis

omit [Fintype A] in
theorem cottonError (s : Finset A) (p q : Wgt A) (ε:ℝ)
    (hp : ∀ x,|p x|≤1) (hq : ∀ x,|q x|≤1)
    (hh : ∀ x,|p x-q x|≤ε) :
    |(∏ x∈s,p x) - (∏ x∈s,q x)| ≤ s.card*ε := by
  classical
  have ht (s : Finset A) : |∏ i∈s, q i| ≤1 := by
    rw [Finset.abs_prod]
    refine (Finset.prod_le_prod (g:=fun _=>1) (fun i _=>abs_nonneg _) (fun i _=>hq i)).trans_eq (by simp)
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s h ih =>
    let Q:= ∏ i∈s,q i
    let P:= ∏ i∈s,p i
    rw [Finset.prod_insert h,Finset.prod_insert h,Finset.card_insert_of_notMem h]
    have he : p x*P-q x*Q=p x*(P-Q)+(p x-q x)*Q:=by ring
    push_cast; rw [he]
    have hf : |p x*(P-Q)|≤ (s.card:ℝ)*ε := by rw [abs_mul]; exact
      (mul_le_mul (hp _) ih (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    have hg : |(p x-q x)*Q|≤ ε := by
      rw [abs_mul]
      exact (mul_le_mul (hh x) (ht s) (abs_nonneg Q) ((abs_nonneg _).trans (hh x))).trans_eq (mul_one _)
    refine ((abs_add_le _ _).trans (add_le_add hf hg)).trans_eq (by ring)

namespace Quill
variable {q : Format} {d : Rates} {b : Bool} (w : Quill p q d b)
  (t : Tagging p (Messenger q)) (z : Messenger q→F)
  (o : UnitType p n N) (m:Mixer p n)

theorem suedeFloor (s f i x) :
    |w.suede t z o m s f i x| ≤ 1 := by
  unfold suede
  rw [abs_mul,abs_of_nonneg (ind_nonneg _)]
  exact (mul_le_mul (w.stencil_floor t z o s m i x) (ind_le_one _) (ind_nonneg _) zero_le_one).trans_eq
    (one_mul _)

theorem paintFloor (s Y) (f:Paint (w.pen t) N) (i x)
    (hw : IsLaw (w.policies t z n i)) :
    |insidePaint w t z o m s (r:=r) Y f i x|≤1 := by
  unfold insidePaint; have hh:= w.seraphFloor t z o m s Y i hw x
  rw [abs_mul,abs_of_nonneg (ind_nonneg _),abs_of_nonneg hh.1]
  exact (mul_le_mul (ind_le_one _) hh.2 hh.1 zero_le_one).trans_eq (one_mul _)

set_option maxHeartbeats 700000 in
theorem surrogate_close (s :Charts p n d) (Y:Silhouette p N r) (f: Paint (w.pen t) N)
    (hf : pigments z Y f) (i:Messenger q) (hw:IsLaw (w.policies t z n i))
    {ε:ℝ} (h : (w.allure t z i).close Y (onSide o (parcel b i)) ε) :
    |avg (lawOmega p N (t i) (z i)) (w.insidePaint t z o m s Y f i)-
      avg (w.policies t z n i) (w.suede t z o m s f i)|≤ε := by
  classical
  let l:=w.allure t z i; let I:=parcel b i
  obtain ⟨H,hf⟩:=hf i
  let u (x : Fin r) (a:Magazine p (d I)) := ind (H x)*ind (a=w.amp i)
  have hu x i : |u x i|≤1 := by unfold u; rw [←ind_and,abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _
  have hh:= l.close_expect Y I o m (s I) hw u hu h
  let Ω:= lawOmega p N l.l l.q
  let E x:= avg (l.reflected Y I o m (s I) x) (u x)
  have he : avg (l.reference Y) E=avg Ω (insidePaint w t z o m s Y f i) := by
    unfold Appearance.reference
    rw [mapW_avg]; refine avg_congr fun k _=>?_
    have hx : f.flies i k ↔ H (Y l.l l.q k) := hf k
    let G:= l.reflected Y I o m (s I) (Y l.l l.q k)
    change avg G _=ind (f.flies i k)* G (w.amp i)
    rw [hx]; unfold u; rw [avg_mul']; change _*pr _ _=_; rw [pr_point']
  have hc (x:Knobs p.g n) :
      u (l.showTag Y (onSide o I) x) (l.profile I o m (s I) x)=w.suede t z o m s f i x := by
    let k : AtomKey (p:=p) ((w.pen t).t i) N := l.face (onSide o I) x
    change ind (H (Y ((w.pen t).t i) (z i) k)) *
      ind (l.profile I o m (s I) x=w.amp i) =
      ind (l.profile I o m (s I) x=w.amp i) * ind (f.flies i k)
    rw [hf]; exact mul_comm _ _
  change |avg (l.reference Y) E- _| ≤ _ at hh
  rw [he] at hh; simp_rw [hc] at hh; exact hh

set_option maxHeartbeats 800000 in
theorem score_sheen (s : Charts p n d) (Y:Silhouette p N r)
    (f : Paint (w.pen t) N) :
    w.sheen t z o m s Y f.cost=
    f.coeff*((w.pen t).kappa * avg (lawNu p N t z) (prodW (w.insidePaint t z o m s Y f))) := by
  classical
  let cost : Wgt (Keys (p:=p) t N) := f.cost
  let flies : ∀ i : Messenger q, AtomKey (p:=p) (t i) N → Prop := f.flies
  change w.sheen t z o m s Y cost = _
  rw [sheen_sun]
  let v:= w.pen t
  let h x := prodW (w.insidePaint t z o m s Y f) x
  let F := w.seraph t z o m s Y
  have hf (x: Keys (p:=p) t N) : cost x * prodW F x = f.coeff*h x := by
    change f.coeff * (∏ i : Messenger q, ind (flies i (x i))) *
      (∏ i : Messenger q, F i (x i)) =
      f.coeff * (∏ i : Messenger q, ind (flies i (x i)) * F i (x i))
    rw [Finset.prod_mul_distrib, mul_assoc]
  change v.kappa * avg _ _=_
  let μ:=lawNu p N t z
  calc
    _ = v.kappa * (f.coeff * avg μ h) := congrArg (fun x=>v.kappa*x) ((avg_congr (w:=μ)
      (fun i _=>hf i)).trans (avg_mul' ..))
    _ = _ := mul_left_comm _ _ _

set_option maxHeartbeats 800000 in
theorem score_prowl (s : Charts p n d) (f : Paint (w.pen t) N)
    (hh : ∀ i,frameLaw m (onSide o i)) (hg : 2≤p.g) (hj : 1≤p.j) :
    w.prowl s t z m o f.cost=
      f.coeff*avg (prodW (w.policies t z n)) (fun x => ind ((w.pen t).performs w.script m o x)*
        prodW (w.suede t z o m s f) x) := by
  classical
  let cost : Wgt (Keys (p:=p) t N) := f.cost
  change w.prowl s t z m o cost = _
  rw [prowl_astonish]
  let v:=w.pen t; let x:=w.policies t z n
  let μ:=prodW x
  let Q (y:Inputs p n (Messenger q)):= v.resultKey o y
  have heq := astonish_val v z f.cost w.script m x (w.stencil t z o s m) o
  change astonish v z f.cost w.script m x (w.stencil t z o s m) o=_
  rw [heq, ← avg_mul']; apply avg_congr
  intro y hy
  have he (i:Messenger q) : dialed p (v.t i) (v.f i) (y i)=z i := by
    have hf i : x i (y i) ≠ 0 := (Finset.prod_ne_zero_iff.mp hy _ (mem_univ i))
    exact (onW_ne (hf i)).1
  let a:= w.stencil t z o s m
  let W i:= ind (f.flies i ((w.allure t z i).face (onSide o (parcel b i)) (y i)))
  have hq : f.cost (Q y)= f.coeff*(∏ i,W i) := rfl
  change ind (v.earns w.script m z o y)* f.cost (Q y)*prodW a y=_
  have hs : (v.performs w.script m o y) ↔ v.earns w.script m z o y :=
    v.performs_own w.script m o y hh hg hj z he
  have hx : prodW (w.suede t z o m s f) y=prodW a y* (∏ i,W i) := by
    change (∏ i, a i (y i) * W i) = (∏ i, a i (y i)) * (∏ i,W i)
    rw [Finset.prod_mul_distrib]
  rw [hs,hq,hx]; ring

end Quill
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RectangleComparisons
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rectangle Comparisons -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
variable {p:Shape} {n N r : ℕ}
open Template
namespace StatusAnalysis

private theorem warm_bound {u v : ℝ} (h : |u|≤1) {r:ℝ}
    (hv : |v| ≤ r) : |u*v| ≤ r := by
  rw [abs_mul]; exact (mul_le_mul h hv (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

namespace Quill
variable {q : Format} {d : Rates} {b : Bool}
    (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)
    (m : Mixer p n)

set_option maxHeartbeats 800000 in
theorem paint_agree (Y:Silhouette p N r) (o: UnitType p n N) (s : Charts p n d)
    (f:Paint (w.pen t) N) (hF : pigments z Y f)
    (hg : 2≤p.g) (hj : 1≤p.j) (hc : |f.coeff|≤1) {u ℓ}
    (he : w.mirrorSpan t z m ℓ u Y o) :
    |w.prowl s t z m o f.cost-w.sheen t z o m s Y f.cost|≤(2+num (Messenger q))*u := by
  classical
  let A:= w.suede t z o m s f; let x:= w.policies t z n
  let V:= w.pen t
  let B:= w.insidePaint t z o m s Y f
  let Q:= avg (prodW x) (fun y=>ind (V.performs w.script m o y)*prodW A y)
  let E:=avg (lawNu p N t z) (prodW B)
  have hb i y := paintFloor w t z o m s Y f i y (he.law _)
  have ha := suedeFloor w t z o m s f
  let h := he.law
  let P i := avg (x i) (A i); let R i:= avg (lawOmega p N (t i) (z i)) (B i)
  have hm : |Q-V.kappa*(∏ i,P i)|≤u := he.ready A ha
  have hf : |E-∏ i,R i|≤u := he.reference B hb
  have hP i : |P i|≤1 := by
    exact (abs_avg_le (h i).nz).trans ((avg_mono (h i).nz (ha i)).trans_eq ((h i).avg_const _))
  have hR i : |R i|≤1 := by
    have hv : SubLaw (lawOmega p N (t i) (z i)) := unifOn_sub _
    exact (abs_avg_le hv.nz).trans (hv.avg_le zero_le_one (hb i))
  have hh : |(∏ i, P i)-(∏ i, R i)|≤num (Messenger q)*u :=
    cottonError _ _ _ _ hP hR (fun i =>(abs_sub_comm ..).trans_le
      (surrogate_close w t z o m s Y f hF _ (h _) (he.close _)))
  have hK : |V.kappa|≤1 := by rw [abs_of_pos V.kappa_pos]; exact w.kappaTop t
  rw [score_prowl w t z o m s f he.frame hg hj,score_sheen w t z o m,←mul_sub]
  apply warm_bound hc
  have hh' : |V.kappa*(∏ i,P i)-V.kappa*E|≤num (Messenger q)*u+u := by
    rw [←mul_sub]; exact warm_bound hK ((abs_sub_le (∏ i,P i) (∏ i,R i) E).trans (add_le_add hh
      ((abs_sub_comm ..).trans_le hf)))
  exact ((abs_sub_le Q _ (V.kappa*E)).trans (add_le_add hm hh')).trans_eq (by ring)

set_option maxHeartbeats 800000 in
theorem paint_set (Y:Silhouette p N r) (o: UnitType p n N) (s : Charts p n d)
    {r' : ℕ}
    (f:Fin r' → Paint (w.pen t) N) (hF : ∀ i,pigments z Y (f i))
    (hg : 2≤p.g) (hj : 1≤p.j) (hc : ∀ i,|(f i).coeff|≤1) {u ℓ}
    (he : w.mirrorSpan t z m ℓ u Y o) :
    |w.prowl s t z m o (mural (w.pen t) f)-w.sheen t z o m s Y (mural (w.pen t) f)|≤
       r' * ((2+num (Messenger q))*u) := by
  classical
  let F i : Wgt (Keys (p:=p) t N) := (f i).cost
  let R := show Wgt (Keys (p:=p) t N) from mural (w.pen t) f
  have hf x : R x=∑ i:Fin r', F i x := rfl
  change |w.prowl _ _ _ _ _ R-w.sheen _ _ _ _ _ _ R|≤_
  have hh :
      w.prowl s t z m o R=∑ i:Fin r',w.prowl s t z m o (F i) := by
    let key : Inputs p n (Messenger q) → Keys (p:=p) t N := (w.pen t).resultKey o
    change avg ((w.pen t).state z n) (fun x => ind (w.deposit t z m o s x) * R (key x)) =
      ∑ i : Fin r', avg ((w.pen t).state z n)
        (fun x => ind (w.deposit t z m o s x) * F i (key x))
    simp_rw [hf, Finset.mul_sum,avg_sum]
  have ht :
      w.sheen t z o m s Y R=∑ i:Fin r',w.sheen t z o m s Y (F i) := by
    unfold sheen; simp_rw [hf,Finset.mul_sum,avg_sum]
  rw [hh,ht,←Finset.sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  exact (Finset.sum_le_sum fun i _=> paint_agree w t z m Y o s (f i) (hF i) hg hj (hc i)
    he).trans_eq (by simp)

set_option maxHeartbeats 800000 in
theorem bare_bridge (Y : Silhouette p N r) (o:UnitType p n N) (s:Charts p n d)
    {r' : ℕ}
    (f:Fin r' → Paint (w.pen t) N) (hF : ∀ i,pigments z Y (f i))
    (hg : 2≤p.g) (hj : 1≤p.j) (hc : ∀ i,|(f i).coeff|≤1) {u ℓ ε}
    (he : w.mirrorSpan t z m ℓ u Y o) (W : Wgt (Keys (p:=p) t N))
    (hw : w.witnessPaint t z m ε W (mural (w.pen t) f) o) :
    |w.prowl s t z m o W-w.sheen t z o m s Y W|≤ 2*ε +r'*((2+num (Messenger q))*u) := by
  classical
  let A:=w.pen t
  let T:= show Wgt (Keys (p:=p) t N) from mural A f
  let x:=w.prowl s t z m o; let y:= w.sheen t z o m s Y
  have h1 : |x W-x T|≤ε := by
    have hz : x W-x T=x (W-T) := by
      let key : Inputs p n (Messenger q) → Keys (p:=p) t N := A.resultKey o
      change avg (A.state z n) (fun x => ind (w.deposit t z m o s x) * W (key x)) -
        avg (A.state z n) (fun x => ind (w.deposit t z m o s x) * T (key x)) =
        avg (A.state z n) (fun x => ind (w.deposit t z m o s x) * (W-T) (key x))
      rw [←avg_sub]
      simp only [Pi.sub_apply,mul_sub]
    rw [hz]
    change |w.prowl _ _ _ _ _ _|≤_
    rw [prowl_astonish]
    exact le_of_not_gt (fun h=> hw.tested ⟨_, stencil_floor w t z o s m,h⟩)
  have h2 : |y W-y T|≤ε := by
    unfold y; rw [sheen_sun,sheen_sun,←mul_sub,←avg_sub]
    let B:= w.seraph t z o m s Y
    have hF (i j): |B i j|≤1 := by
      have hh:= w.seraphFloor t z o m s Y i (he.law i) j; rw [abs_of_nonneg (show 0≤B i j
        from hh.1)]; exact hh.2
    simp_rw [←sub_mul]; exact warm_bound (show |A.kappa|≤1 from (abs_of_pos A.kappa_pos).trans_le
      (w.kappaTop t)) (hw.shadow B hF)
  have h3 := paint_set w t z m Y o s f hF hg hj hc he
  exact (abs_sub_le (x W) (x T) (y W)).trans ((add_le_add h1
    ((abs_sub_le (x T) (y T) (y W)).trans (add_le_add h3 ((abs_sub_comm ..).trans_le h2)))).trans_eq
      (by ring))

end Quill
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CommonPartitionRefinement
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common Partition Refinement -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
variable {p:Shape} {n N K M r : ℕ}

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

namespace StatusAnalysis
variable (v : Template p A)

theorem buildPalette (N : ℕ) (q : A → F) (w : B → Template.Paint v N) :
    ∃ Y : Silhouette p N (paletteSize A B),∀ i,pigments q Y (w i) := by
  classical
  let E := Fintype.equivFin (B × A→Bool)
  let H (l) (q:F) (x : AtomKey (p:=p) l N) (i:B) (j:A) :=
    if h:v.t j=l then decide ((w i).flies j (h ▸ x)) else false
  let Y : Silhouette p N (paletteSize A B) :=
    fun l q x=> E (fun i=> H l q x i.1 i.2)
  refine ⟨Y,fun i j=>⟨fun x=>(E.symm x (i,j)),fun x=>?_⟩⟩
  change _ ↔ E.symm (E (fun i => H (v.t j) (q j) x i.1 i.2)) (i,j)=true
  rw [Equiv.symm_apply_apply]
  unfold H; rw [dite_eq_left rfl]; simp

omit [Fintype A] [DecidableEq A] in
theorem finerPigment {v : Template p A} {r s:ℕ} (Y : Silhouette p N r)
    (Y' : Silhouette p N s) (h : refines Y' Y) {q} (w : Template.Paint v N)
    (hh : pigments q Y w) : pigments q Y' w := by
  intro i
  obtain ⟨g,hg⟩:=hh i; obtain ⟨f,hf⟩:=h (v.t i) (q i)
  exact ⟨g∘ f,fun x=> (hg x).trans (by rw [hf]; rfl)⟩

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_UniformSideComparisons
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform Side Comparisons -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
open Template
variable {p:Shape} {M n N r s0 : ℕ}
namespace StatusAnalysis
namespace Quill
variable {q : Format} {d : Rates} {b:Bool}
    (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)
variable {b' : PreparationParameters}

private theorem resolve_ready (M:ℕ) (h : AnalyticParameters p M b' s0)
    (hw : w.moral t z) (δ : ℝ) (hd:0<δ) :
    ∀ᶠ n : ℕ in atTop, let N:=M*n; ∀ m : Mixer p n, (2*num (Full p n)<(N:ℝ)) →
      binaryGood m → ∀ r:ℕ,∀ Y:Silhouette p N r, ∀ o:UnitType p n N,
      PreparationParameters.frameSide p m o → w.matchesArea t z Y o δ →
      litFire p o → w.mirrorSpan t z m 0 δ Y o := by
  classical
  let v:= w.pen t
  have ht:=h.enter.first; let a:=(scanPrice p)⁻¹
  have ha : 0<a:=inv_pos_of_pos (scanPrice_pos p)
  let L:=2*netFact (trayPort p t)
  let N (n:ℕ):=M*n
  have hz := (trend_sizes atTop (le_refl _) ht.hM).2
  have h1 :
      ∀ᶠ n : ℕ in atTop, a^2*bp (-(n:ℝ)/10) ≤ δ := by
    have he := (bp_nat_vanish (by norm_num : 0<(1/10:ℝ))).const_mul (a^2)
    have hh : ∀ᶠ n:ℕ in atTop,a^2*bp (-(1/10:ℝ)*n) ≤ δ :=
      he.eventually (eventually_le_nhds (by rw [mul_zero]; exact hd))
    filter_upwards [hh] with n hn
    rw [show -(n:ℝ)/10= -(1/10:ℝ)*n from by ring]; exact hn
  have h2 :
      ∀ᶠ n:ℕ in atTop,L*bp (-(N n:ℝ)/2) ≤ δ := by
    have he:=(((bp_tendsto_zero (by norm_num : 0<(1/2:ℝ))).comp hz).const_mul L)
    have hh : ∀ᶠ n:ℕ in atTop,L*bp (-(1/2:ℝ)*(N n:ℝ))≤δ :=
      he.eventually (eventually_le_nhds (by rw [mul_zero]; exact hd))
    filter_upwards [hh] with n hn
    rw [show -(N n:ℝ)/2= -(1/2:ℝ)*(N n:ℝ) from by ring]; exact hn
  filter_upwards [eventually_ge_atTop (2*p.r), h1,h2,hz.eventually
    (eventually_ge_atTop (2*num (Messenger q×Toast p) +1))]
    with n hn hi hj hB N m hN hm r Y o hp hv hf
  let W:=w.policies t z n; let f:=w.allure t z
  have he i: (f i).apt:=w.allure_apt t z hw i
  have hW i : IsLaw (W i):=Appearance.witLaw (he i) ht.hR hn
  have hC i j : W i j ≤ a * unif j := dialCap p _ _ _ ht.hR hn (he i) j
  have hy : v.diffsel := fun i j h _ =>fun ht=>h (hw.1 ht)
  refine ⟨hW,hp,hv,fun z hz=>(v.resonant m hm o hf hy W hW a ha hC w.script z hz).trans hi,
    fun f hf=> (reference_product t z f hf ?_).trans hj⟩
  change _≤(N:ℝ) at hB; linarith only [hB]

set_option maxHeartbeats 1600000 in
theorem sideRelease_oai (M:ℕ) (h : AnalyticParameters p M b' s0) (hw : w.moral t z) (ε:ℝ) (he:0<ε) :
    ∃ (l:ℕ) (u c:ℝ),0<u∧0 < c∧∀ᶠ n : ℕ in atTop,let N:=M*n;∀ W:Wgt (Keys (p:=p) t N),
      (∀ x, |W x|≤ 1) → ∃ X: Silhouette p N l,w.markedTest t z M b' s0 n X W (bp (-c*n)) u ε := by
  classical
  let a := ε/4; have ha : 0<a:=by unfold a; positivity
  let v:=w.pen t; have ht := h.enter.first
  obtain ⟨r,c,hc,hV⟩:= weakly v M ht.hM b'.spJoint a 1 ha zero_le_one
  let x:=2+num (Messenger q)
  let u:=a/((r+1:ℝ)*x)
  have hx : 0<x := by unfold x num; positivity
  have hU : 0<u := by unfold u; positivity
  refine ⟨paletteSize (Messenger q) (Fin r),u,c/2,hU,half_pos hc,?_⟩
  filter_upwards [hV, resolve_ready w t z M h hw u hU, litFire_calendar p b'.spJoint M h.thickness,
    pay_nat (a:=c) 2 (half_lt_self hc),tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (8*c))] with n hn hR hG hQ hD N W hW
  obtain ⟨Z,⟨F,hf,hf'⟩,hM,h⟩:= hn z W hW
  obtain ⟨X,hX⟩:=buildPalette v N z F
  subst Z
  refine ⟨X,?_⟩; intro r' Y hy m U hm
  let P := w.flunk t z Y W m u ε
  let μ:= w.policies t z n
  have hμ i : IsLaw (μ i) := Appearance.witLaw (w.allure_apt t z hw i) ht.hR hm.age
  let T := exceeds v z ((show Wgt (Keys (p:=p) v.t (M*n)) from W)-mural v F) w.script m μ a
  let Q (o:UnitType p n N) := ¬ litFire p o
  have hi o (h : P o) : T o ∨ Q o := by
    by_contra! hh
    obtain ⟨hj,hv,s,h⟩:=h
    have heq : w.witnessPaint t z m a W (mural v F) o :=
      ⟨fun f hf=>hM f hf, hh.1⟩
    have hg := bare_bridge w t z m Y o s F (fun i=> finerPigment X Y hy _ (hX _))
      (by linarith only [ht.hG]) ht.hJ hf' (hR m hm.cols hm.rum _ Y o hj hv (not_not.mp hh.2)) W heq
    refine not_lt_of_ge (hg.trans ?_) h
    have hf : (r:ℝ)*(x*u)≤a := by
      have ht : ((r:ℝ)+1)*(x*u) = a := by unfold u; field_simp
      rw [←ht]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    unfold x a at *
    linarith only [hf,he]
  have hU : IsLaw U:=hm.drain.1
  have hT :=
    h m hm.cols U hm.drain w.script μ hμ (fun i=>scopedZ_bit p n _ _ _ (hμ i))
  have hD' : bp (-(n:ℝ)*n/8) ≤ bp (-c*n) := by
    change _ ≤ (n:ℝ) at hD
    apply bp_le
    nlinarith only [mul_le_mul_of_nonneg_right hD (show 0≤ (n:ℝ) from Nat.cast_nonneg _)]
  have hH : pr U Q≤ bp (-c*n) := (hG m hm.cols U hm.drain.2.2.2).trans hD'
  change pr U T≤bp (-c*n) at hT
  exact ((pr_mono hU.nz hi).trans ((pr_or_le hU.nz).trans (add_le_add hT hH))).trans
     (by rw [two_mul] at hQ; exact hQ)

end Quill
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

theorem solution : type_of% @OAI.HadwigerCounterexample.StatusAnalysis.Quill.sideRelease_oai := @OAI.HadwigerCounterexample.StatusAnalysis.Quill.sideRelease_oai
