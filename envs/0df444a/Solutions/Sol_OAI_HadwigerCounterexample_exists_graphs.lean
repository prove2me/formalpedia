-- Prove2me | solution 1 for OAI.HadwigerCounterexample.exists_graphs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T23:08:13.595181+00:00
-- url     : https://prove2.me/submissions/6d197491-f59f-4e2e-a198-abb650f0d177

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
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
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
import Mathlib.Tactic.SplitIfs
import Definitions.Def_HadwigerMatching_Defs
import Definitions.Def_OAIQ430Hc000
import Theorems.Thm_OAI_HadwigerCounterexample_eventual_conflict_lower_bound
import Theorems.Thm_OAI_HadwigerCounterexample_exists_parameters

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

theorem liftM_outer (P : Mat K I) (Q : Mat L J) (x : Vec I) (y : Vec J) :
    liftM P Q (vecMulVec x y) = vecMulVec (P *ᵥ x) (Q *ᵥ y) := by
  rw [liftM_def,mul_vecMulVec,vecMulVec_mul,vecMul_transpose]

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

omit [Fintype I] in
theorem colSp_dim (P : Mat I J) : dim (colSp P) = P.rank := rfl

omit [Fintype I] in
/-- Matrix multiplication cancels when a left factor is injective. -/
theorem inj_comp_mat [Fintype K] (A : Mat I J) (B : Mat J K)
    (hA : Injective A.mulVec) (hB : Injective B.mulVec) :
    Injective (A*B).mulVec := by
  rw [← coe_mulVecLin,mulVecLin_mul]
  exact hA.comp hB

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MomentCoordinates
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice
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

theorem card_row (p : Shape) (n : ℕ) :
    Fintype.card (Row p n) = psize p * (1 + (p.g*p.g+3)*n) := by
  simp [Row,AIdx,psize,add_comm]

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

theorem labMat_act (s) (z : Vec (AIdx p.g n)) :
    labMat p n s *ᵥ z = putLab p n s z := by
  funext i
  simp [Matrix.mulVec,dotProduct,labMat,putLab,monoBit,selV]

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
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
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

omit [Fintype I] in
theorem embedMat_self [DecidableEq I] [DecidableEq U] {f : I → U} (h : Injective f) :
    (embedMat f)ᵀ * embedMat f = 1 := by
  ext i j
  rw [embedMat_mul]
  simp only [embedMat,Matrix.submatrix_apply,Matrix.of_apply,id_eq,
    Matrix.one_apply,h.eq_iff]

theorem embedMat_inj [DecidableEq U] {f : I → U} (h : Injective f) :
    Injective (embedMat f).mulVec := by
  classical
  intro x y g
  change embedMat f *ᵥ x = embedMat f *ᵥ y at g
  have he (x : Vec I) : (embedMat f)ᵀ *ᵥ (embedMat f *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec,embedMat_self h,Matrix.one_mulVec]
  rw [← he x,g,he]

/-- Specify an arbitrary cross Gram bilinear form between independent columns. -/
theorem prescribe_between {A : Mat U I} {B : Mat V J}
    (hA : Injective A.mulVec) (hB : Injective B.mulVec) (M : Mat I J) :
    ∃ L : Mat U V, Aᵀ*L*B=M := by
  classical
  obtain ⟨a,ha⟩ := mat_left_inv hA
  obtain ⟨b,hb⟩ := mat_left_inv hB
  refine ⟨aᵀ*(M*b),?_⟩
  rw [← Matrix.mul_assoc Aᵀ,←transpose_mul,ha,transpose_one,Matrix.one_mul,
    Matrix.mul_assoc,hb,Matrix.mul_one]

/-- Two opposite-direction restrictions are specifiable on disjoint bases. -/
theorem prescribe_opposite {A : Mat U I} {B : Mat V J} {C : Mat U K} {D : Mat V T}
    (hc : Injective (fromCols A C).mulVec) (hd : Injective (fromCols B D).mulVec)
    (M : Mat I J) (N : Mat T K) :
    ∃ L : Mat U V, Aᵀ*L*B=M ∧ Dᵀ*Lᵀ*C=N := by
  obtain ⟨L,hL⟩ := prescribe_between hc hd (fromBlocks M 0 0 Nᵀ)
  rw [transpose_fromCols, fromRows_mul, fromRows_mul_fromCols] at hL
  have hi : Cᵀ*L*D=Nᵀ := congrArg Matrix.toBlocks₂₂ hL
  refine ⟨L, congrArg Matrix.toBlocks₁₁ hL, ?_⟩
  have hg := congrArg Matrix.transpose hi
  rwa [transpose_mul,transpose_mul,transpose_transpose,transpose_transpose,← Matrix.mul_assoc] at hg

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

theorem rank_ge_congr (A : Mat I I) (B : Mat J I) :
    A.rank + 2*B.rank ≤ (liftM B B A).rank + 2*Fintype.card I := by
  have h1 := rank_ge_mul B A
  have h2 := rank_ge_mul (B*A) Bᵀ
  rw [Matrix.rank_transpose] at h2
  rw [liftM_def]; omega

/-- Choose a large space in the domain which becomes disjoint from S in the target. -/
theorem choose_free {A : Mat I J} (hA : Injective A.mulVec) (S : Space (Vec I)) :
    ∃ T : Space (Vec J), Fintype.card J ≤ dim T+dim S ∧
      Disjoint S (colSp (A*pack T)) := by
  let U := S.comap A.mulVecLin
  obtain ⟨T,hT⟩ := U.exists_isCompl
  refine ⟨T,?_,?_⟩
  · have hi : dim U ≤ dim S := by
      let q := A.mulVecLin ∘ₗ U.subtype
      have he (x : U) : q x∈S := x.property
      let B := q.codRestrict S he
      have hb : Injective B := fun x y h => Subtype.ext (hA
        (show q x=q y from congrArg Subtype.val h))
      exact LinearMap.finrank_le_finrank_of_injective hb
    have he := (U.prodEquivOfIsCompl T hT).finrank_eq
    rw [finrank_prod,show finrank F (Vec J)=Fintype.card J from dim_vec _] at he
    change dim U + dim T = Fintype.card J at he
    rw [← he]
    exact (Nat.add_le_add_right hi _).trans_eq (Nat.add_comm _ _)
  rw [colSp,mulVecLin_mul,LinearMap.range_comp,show LinearMap.range (pack T).mulVecLin = T from
    colSp_pack T]
  rw [disjoint_iff_inf_le]
  rintro x ⟨hx,y,hy,rfl⟩
  have hh : y∈U⊓T := ⟨hx,hy⟩
  rw [hT.inf_eq_bot] at hh
  have he : y=0 := by simpa using hh
  rw [he,map_zero]; exact Submodule.zero_mem _

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CoordinateBlocks
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
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

theorem lab_inj (s : Label p.b) : Function.Injective (labMat p n s).mulVec := by
  intro x y he
  funext i
  rw [labMat_act,labMat_act] at he
  have h := congr_fun he (emptySel,i)
  simpa [putLab,selV,emptySel] using h

theorem joined_lab_inj {s t : Label p.b} (hj : 1≤p.j) (hs : s≠t) :
    Function.Injective (fromCols (labMat p n s) (labMat p n t)).mulVec := by
  apply inj_fromCols (lab_inj _) (lab_inj _)
  classical
  rw [disjoint_iff_inf_le]
  rintro x ⟨⟨v,rfl⟩,w,h⟩
  simp only [mulVecLin_apply,labMat_act] at h
  let Z : Label p.b → Vec (AIdx p.g n) := fun i => if i=s then v else -w
  have he : ∑ i ∈ ({s,t} : Finset _), putLab p n i (Z i)=0 := by
    simp [Z,hs,hs.symm,map_neg,h]
  have hi : ({s,t}:Finset _).card ≤ p.j+1 := by
    have hh : ({s,t}:Finset _).card=2 := by simp [hs]
    omega
  have hg := ray_indep _ _ hi he s (by simp)
  have hv : v=0 := by simpa [Z] using hg
  rw [hv,map_zero]; exact Submodule.zero_mem _

theorem block_inj (B : Block p.g) : Function.Injective (blockA p n B).mulVec :=
  embedMat_inj (show Function.Injective (fun i => some (B,i)) from
    fun _ _ h => congrArg Prod.snd (Option.some.inj h))

theorem blockRay_inj (p : Shape) (n) (s) (B) :
    Function.Injective (blockRay p n s B).mulVec :=
  inj_comp_mat _ _ (lab_inj _) (block_inj B)

theorem joined_block_inj {s t : Label p.b} (hj : 1 ≤ p.j) (hs : s ≠ t) (B : Block p.g) :
    Function.Injective (fromCols (blockRay p n s B) (blockRay p n t B)).mulVec := by
  classical
  apply inj_fromCols (blockRay_inj ..) (blockRay_inj ..)
  rw [disjoint_iff_inf_le]
  rintro x ⟨⟨v,rfl⟩,w,h⟩
  simp only [Matrix.mulVecLin_apply,blockRay,← Matrix.mulVec_mulVec] at h
  let a := Sum.elim (blockA p n B *ᵥ v) (0 : Vec (AIdx p.g n))
  let b := Sum.elim (0 : Vec (AIdx p.g n)) (blockA p n B *ᵥ w)
  have heq : a=b := joined_lab_inj hj hs (by
    dsimp only [a,b]
    rw [fromCols_mulVec_sumElim,fromCols_mulVec_sumElim,Matrix.mulVec_zero,
      Matrix.mulVec_zero,zero_add,add_zero,h])
  have hg : blockA p n B *ᵥ v = 0 := funext (fun x => congr_fun heq (.inl x))
  change blockRay p n s B *ᵥ v ∈ _
  rw [blockRay,← Matrix.mulVec_mulVec,hg,Matrix.mulVec_zero]
  exact Submodule.zero_mem _

theorem blockRay_eval (p : Shape) (s : Label p.b) (B) (i) (j : Fin n) :
    blockRay p n s B i j = if i.2=some (B,j) then monoBit s i.1.val else 0 := by
  rw [blockRay,blockA,mul_embedMat]; rfl

theorem project_pick {d B : Block p.g} (hd : d ≠ B) (a) (s) (i) :
    (blockRay p n s B)ᵀ *ᵥ pick p n a d i = 0 := by
  classical
  unfold pick
  split
  · rename_i hi
    rw [Matrix.mulVec_single_one]
    ext j
    change blockRay p n s B (a,some (d,⟨i,hi⟩)) j=0
    simp [blockRay_eval,hd]
  rw [Matrix.mulVec_zero]

theorem project_same (B : Block p.g) (a s) (i : Fin n) :
    (blockRay p n s B)ᵀ *ᵥ pick p n a B i.val = Pi.single i (monoBit s a.val) := by
  classical
  rw [pick,dite_eq_left i.isLt,Matrix.mulVec_single_one]
  ext j
  change blockRay p n s B _ j=_
  rw [blockRay_eval]
  simp [Pi.single_apply, eq_comm]

theorem pullM_def {I J V U : Type} [Fintype V] [Fintype U] (P : Mat V I)
    (Q : Mat U J) (M : Mat V U) : pullM P Q M=Pᵀ*M*Q := rfl

theorem pull_test {d B : Block p.g} (h : d≠B) (s s') :
    pullM (blockRay p n s B) (blockRay p n s' B) (testM p n d) = 0 := by
  unfold testM pullM
  simp only [map_sum,liftM_outer,project_pick h]
  simp

theorem pull_self_Z (M) (s s' : Label p.b) :
    pullM (blockRay p n s Block.Z) (blockRay p n s' Block.Z) (selfM p n M)=0 := by
  let L := pullM (blockRay p n s Block.Z) (blockRay p n s' Block.Z)
  have hx (i j : Tag p.g) := pull_test (n:=n) (d:=Block.O i j)
    (B:=Block.Z) (by simp [Block.O,Block.Z]) s s'
  have hs := pull_test (p:=p) (n:=n) (d:=Block.S) (B:=Block.Z) (by simp [Block.S,Block.Z]) s s'
  have h (a : SelIdx p.b p.j) (s : Label p.b) (i) :=
    project_pick (n:=n) (p:=p) (d:=Block.sharp) (B:=Block.Z) (by simp [Block.sharp,Block.Z]) a s i
  rw [selfM]; simp only [map_add,map_sum,hx,hs,Finset.sum_const_zero,zero_add]
  unfold sharpM sharpPick pullM
  by_cases he : 1 ≤ p.j
  · simp only [map_sum,map_smul,map_add, dite_eq_left he,liftM_outer,h]
    simp
  · simp only [dite_eq_right he] <;> simp

theorem pull_self_sharp (M) (s s' : Label p.b) (hj : 1≤p.j) :
    pullM (blockRay p n s Block.sharp) (blockRay p n s' Block.sharp) (selfM p n M) =
      ∑ i, (s i+s' i) • M i := by
  classical
  have hx (i j : Tag p.g) := pull_test (n:=n) (d:=Block.O i j)
    (B:=Block.sharp) (by simp [Block.O,Block.sharp]) s s'
  have hs := pull_test (p:=p) (n:=n) (d:=Block.S) (B:=Block.sharp) (by simp [Block.S,Block.sharp]) s s'
  rw [selfM]; simp only [map_add,map_sum,hx,hs,Finset.sum_const_zero,zero_add]
  unfold sharpM sharpPick pullM
  simp only [map_sum,map_add,map_smul, dite_eq_left hj,liftM_outer,project_same]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext a b
  simp only [Matrix.sum_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    vecMulVec_apply,monoBit,emptySel,Finset.prod_empty,Finset.prod_singleton,Pi.single_apply]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp <;> ring
    · intro j _ h; simp [h.symm]
    · simp
  · intro j _ h; simp [h.symm]
  simp
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerMatching_BasicMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HadwigerMatching

open scoped BigOperators

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- The empty family is a touching matching. -/
theorem isTouchingMatching_empty (G : SimpleGraph V) :
    IsTouchingMatching G ∅ := by
  simp [IsTouchingMatching]

/-- Every member contributes exactly two vertices. -/
theorem IsTouchingMatching.sum_card_eq {M : Finset (Finset V)}
    (hM : IsTouchingMatching G M) :
    (∑ e ∈ M, e.card) = 2 * M.card := by
  rw [Finset.sum_const_nat (fun e he => (hM.1 e he).1)]
  exact Nat.mul_comm M.card 2

/-- Disjointness bounds twice the number of matching edges by the graph order. -/
theorem IsTouchingMatching.two_mul_card_le [Fintype V]
    {M : Finset (Finset V)} (hM : IsTouchingMatching G M) :
    2 * M.card ≤ Fintype.card V := by
  classical
  have hd : (M : Set (Finset V)).PairwiseDisjoint (fun e => e) := by
    intro e he f hf hne
    exact hM.2.1 e he f hf hne
  have hc : (M.biUnion (fun e => e)).card = 2 * M.card := by
    rw [Finset.card_biUnion hd]
    exact hM.sum_card_eq
  rw [← hc]
  exact Finset.card_le_univ _

/-- Touching matching cardinalities are bounded on a finite vertex type. -/
theorem connectedMatchingNumber_bddAbove [Fintype V] (G : SimpleGraph V) :
    BddAbove {n : ℕ | ∃ M : Finset (Finset V),
      IsTouchingMatching G M ∧ M.card = n} := by
  refine ⟨Fintype.card V, ?_⟩
  rintro n ⟨M, hM, rfl⟩
  have h : M.card + M.card ≤ Fintype.card V := by
    simpa only [two_mul] using hM.two_mul_card_le
  exact (Nat.le_add_right M.card M.card).trans h

/-- The connected matching number is realized by a touching matching. -/
theorem exists_matching_card_eq_number [Fintype V] (G : SimpleGraph V) :
    ∃ M : Finset (Finset V), IsTouchingMatching G M ∧
      M.card = connectedMatchingNumber G := by
  have hne : Set.Nonempty {n : ℕ | ∃ M : Finset (Finset V),
      IsTouchingMatching G M ∧ M.card = n} :=
    ⟨0, ∅, isTouchingMatching_empty G, rfl⟩
  exact Nat.sSup_mem hne (connectedMatchingNumber_bddAbove G)

end HadwigerMatching

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SampledGraphs
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sampled Graphs -/

noncomputable section
namespace HadwigerCounterexample
open HadwigerMatching Finset
variable {A V : Type*}

namespace Holes

variable (H : Holes A)

theorem no_self_conflict (p : A × A) : ¬ H.conflict p p := fun h => H.irr p.1 h.1

theorem indepNum_graph_le [Fintype V] (x : V → A) : (graph H x).indepNum ≤ 2 := by
  classical
  obtain ⟨S, hS, he⟩ := (graph H x).exists_isNIndepSet_indepNum
  rw [← he]
  by_contra h
  have hr : Fintype.card (Fin 3) ≤ Fintype.card S := by simp; omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hr
  let f : Fin 3 → V := fun i => e i
  have hf {i j} (h : i ≠ j) : H.rel (x (f i)) (x (f j)) := by
    by_contra hp
    apply hS (show f i ∈ (S : Set V) from (e i).property)
      (show f j ∈ (S : Set V) from (e j).property)
      (show f i ≠ f j from fun g => h (e.injective (Subtype.ext g)))
    exact ⟨fun g => h (e.injective (Subtype.ext g)), hp⟩
  exact H.ntri (hf (i:=0) (j:=1) (by decide)) (hf (j:=2) (by decide))
    (hf (by decide))

/-- Enumerate endpoints of an actual maximum connected matching on positions to
obtain pairwise disjoint ordered pairs; their raw unit types do not conflict. -/
theorem matching_pairs [Fintype V] (x : V → A) :
    let t := connectedMatchingNumber (graph H x)
    ∃ e : (Fin t ⊕ Fin t) → V, Function.Injective e ∧
      let f : Fin t → A × A := fun i => (x (e (.inl i)), x (e (.inr i)))
      (∀ i, H.unit (f i)) ∧ (∀ i j, ¬H.conflict (f i) (f j)) := by
  classical
  let G := graph H x
  let t := connectedMatchingNumber G
  obtain ⟨M,hM,hc⟩ := exists_matching_card_eq_number G
  have ht : Fintype.card M = t := by rw [Fintype.card_coe,hc]
  let m := (Fintype.equivFinOfCardEq ht).symm
  let m' (i : Fin t) : Finset V := (m i).val
  have hm i : m' i ∈ M := (m i).property
  have hex (i : Fin t) : ∃ v w : V, v ≠ w ∧ m' i = {v,w} :=
    card_eq_two.mp (hM.1 _ (hm i)).1
  choose v w hv he using hex
  let e := Sum.elim v w
  have hmem (i : Fin t ⊕ Fin t) : e i ∈ m' (Sum.elim id id i) := by
    cases i <;> simp [e,he]
  have hminj : Function.Injective m' := fun i j g => m.injective (Subtype.ext g)
  have hei : Function.Injective e := by
    intro i j h
    have hi : Sum.elim id id i = Sum.elim id id j := by
      by_contra hn
      have hh := hM.2.1 _ (hm _) _ (hm _) (hminj.ne hn)
      exact Finset.disjoint_left.mp hh (hmem i) (by rw [h]; exact hmem j)
    cases i <;> cases j <;> simp_all [e]
    exact hv _ h.symm
  refine ⟨e, hei, fun i => ?_, fun i j => ?_⟩
  · have h1 : v i ∈ m' i := by simp [he]
    have h2 : w i ∈ m' i := by simp [he]
    exact ((hM.1 _ (hm i)).2 h1 h2 (hv i)).2
  · by_cases h : i = j
    · subst j; exact no_self_conflict _ _
    · obtain ⟨a,ha,b,hb,hadj⟩ := hM.2.2 _ (hm i) _ (hm j) (hminj.ne h)
      have ha' : a = v i ∨ a = w i := by simpa [he] using ha
      have hb' : b = v j ∨ b = w j := by simpa [he] using hb
      intro hz
      apply hadj.2
      rcases ha' with h1|h1 <;> rcases hb' with h2|h2 <;> rw [h1,h2]
      · exact hz.1
      · exact hz.2.1
      · exact hz.2.2.1
      · exact hz.2.2.2
end Holes
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

theorem tot_mono (h : ∀ x, w x ≤ v x) : tot w ≤ tot v :=
  Finset.sum_le_sum fun x _ => h x

theorem weight_le_tot (hw : ∀ x, 0 ≤ w x) (x) : w x ≤ tot w :=
  Finset.single_le_sum (fun y _ => hw y) (Finset.mem_univ x)

theorem SubLaw.weight_le_one (hw : SubLaw w) (x) : w x ≤ 1 :=
  (weight_le_tot hw.nz x).trans hw.total

theorem IsLaw.weight_le_one (hw : IsLaw w) (x) : w x ≤ 1 := hw.sub.weight_le_one x

theorem avg_comm (w f : Wgt α) : avg w f = avg f w := by simp only [avg, mul_comm]

theorem avg_mono (hw : ∀ x, 0 ≤ w x) (h : ∀ x, f x ≤ g x) : avg w f ≤ avg w g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (hw x)

theorem avg_nonneg (hw : ∀ x, 0 ≤ w x) (hf : ∀ x, 0 ≤ f x) : 0 ≤ avg w f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (hf x)

theorem avg_const (w : Wgt α) (a : ℝ) : avg w (fun _ => a) = tot w * a := by
  rw [avg, tot, Finset.sum_mul]

theorem IsLaw.avg_const (hw : IsLaw w) (a : ℝ) : avg w (fun _ => a) = a := by
  rw [HadwigerCounterexample.avg_const, hw.total, one_mul]

theorem IsLaw.avg_le (hw : IsLaw w) {b : ℝ} (h : ∀ x, f x ≤ b) : avg w f ≤ b :=
  (avg_mono hw.nz h).trans (hw.avg_const _).le

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

/-- Mapping to ordered pairs along a disjoint family of positions. -/
theorem prodW_map_pairs (e : ι ⊕ ι → κ) (he : Function.Injective e)
    {w : Wgt α} (hw : IsLaw w) :
    mapW (prodW (fun _ : κ => w))
      (fun x i => (x (e (.inl i)), x (e (.inr i)))) =
      prodW (fun _ : ι => pairW w w) := by
  funext y
  let p (j : ι ⊕ ι) (x : α) := j.elim (fun i => x = (y i).1) (fun i => x = (y i).2)
  have heq (x : κ → α) :
      ((fun i => (x (e (.inl i)), x (e (.inr i)))) = y) ↔ ∀ j, p j (x (e j)) := by
    simp [funext_iff, Prod.ext_iff, p, Sum.forall, forall_and]
  unfold mapW
  simp_rw [heq]
  have h := prodW_pr_inj he (w:=fun _ => w) (fun _ => hw) p
  rw [h]
  simp [Fintype.prod_sum_type, p, prodW, pairW, Finset.prod_mul_distrib]

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
theorem bp_mul_nat (x : ℝ) (n : ℕ) : bp (x*n) = bp x ^ n := by
  unfold bp; rw [Real.rpow_mul (by norm_num)]; simp
theorem log_bp (x : ℝ) : log (bp x) = x * log 2 := Real.log_rpow (by norm_num) _

theorem bp_poly_dom {a : ℝ} (ha : 0 < a) (c d : ℝ) :
    ∀ᶠ x : ℝ in atTop, c*x^d < bp (a*x) := by
  have hla : 0 < Real.log 2 * a := mul_pos (Real.log_pos (by norm_num)) ha
  have h := tendsto_exp_mul_div_rpow_atTop d _ hla
  filter_upwards [h.eventually (eventually_gt_atTop c), eventually_gt_atTop (0:ℝ)] with x hx hx'
  change c < Real.exp ((Real.log 2*a)*x)/x^d at hx
  rw [lt_div_iff₀ (by positivity)] at hx
  rwa [bp, Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2), ← mul_assoc]

theorem bp_poly_dom_nat {a : ℝ} (ha : 0 < a) (c : ℝ) (d : ℕ) :
    ∀ᶠ n : ℕ in atTop, c*(n:ℝ)^d < bp (a*n) := by
  have h := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (bp_poly_dom ha c d)
  simpa using h

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

theorem map_unif_surjective [Fintype V] [Fintype W] (f : V →ₗ[F] W)
    (h : Function.Surjective f) : mapW unif f = unif := by
  rw [unif_lin,range_eq_top.mpr h]
  simp only [Submodule.mem_top,unifOn_true]

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FrameOrbitLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frame Orbit Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Function

variable {U I J R S : Type} [Fintype U] [Fintype I] [Fintype J] [Fintype R] [Fintype S]
    [DecidableEq U]

/-- Nonempty matrix family if super-dimension slack. -/
theorem framesAt_exists [DecidableEq I] [DecidableEq J]
    {C : Mat I J → Prop} (h : ∃ G, C G) (hn : num I+num J < num U) :
    ∃ x : Mat U I × Mat U J, FramesAt C x := by
  obtain ⟨G,hG⟩ := h
  let v := (pairW unif unif : Wgt (Mat U I × Mat U J))
  have he (a : ℝ) (h : a < 0) : 0 < 1-bp a := sub_pos.mpr
    ((bp_lt h).trans_eq bp_zero)
  have hpos : 0 < pr v (gramGood G) := by
    refine lt_of_lt_of_le ?_ (gram_norm G hn.le).2
    have hi : num I - num U < 0 := by
      have hh : 0 ≤ num J := by unfold num; positivity
      linarith
    exact mul_pos (mul_pos (bp_pos _) (he _ hi)) (he _ (by linarith only [hn]))
  obtain ⟨x,hx,_⟩ := exists_of_pr_pos (pairW_law unif_law unif_law).nz hpos
  exact ⟨x,hx.1.symm ▸ hG,hx.2⟩

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RawFrameLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice
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

theorem gramCond_exists (m : Mixer p n) : ∃ G, gramCond m G := by
  refine ⟨fromBlocks (selfM p n m.mixM) 0 0 0,?_,?_,?_⟩ <;> rfl

theorem raw_law (m : Mixer p n) (hN : 2*num (Full p n)<N) : IsLaw (raw m N) :=
  prodW_law (fun _ => unifOn_law (framesAt_exists (gramCond_exists m)
    (show num (Full p n) + num (Full p n) < num (Fin N) by
      rw [← two_mul]; simpa [num] using hN)))

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConstructionScales
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Construction Scales -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Filter

theorem unit_size (p : Shape) (n N : ℕ) :
    num (UnitType p n N) = bp (num (Comp p.g) * 4 * N * num (Full p n)) := by
  have hc :
      (Fintype.card (UnitType p n N)) =
        ((Fintype.card (Mat (Fin N) (Full p n)))^2)^(Fintype.card (Comp p.g)) *
        ((Fintype.card (Mat (Fin N) (Full p n)))^2)^(Fintype.card (Comp p.g)) := by
    simp [UnitType, Orient, Oframe, RawFrame, pow_two]
  unfold num
  rw [hc]
  push_cast
  rw [card_space,dim_mat,Fintype.card_fin]
  push_cast
  simp only [← bp_mul_nat,← bp_add]
  push_cast <;> ring_nf

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
theorem rank_lift_le (P : Mat U I) (Q : Mat L J) (A : Mat I J) :
    (liftM P Q A).rank ≤ A.rank :=
  (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

end Rank

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FrameIntersectionBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frame Intersection Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap
open scoped BigOperators

/-- Standard embedding padded by zeros. -/
theorem pad_matrix_inj (a b : ℕ) (h : a ≤ b) :
    ∃ M : Mat (Fin b) (Fin a), Function.Injective M.mulVec := by
  let M : Mat (Fin b) (Fin a) := (1:Mat (Fin b) (Fin b)).submatrix _root_.id (Fin.castLE h)
  have hf : Function.Injective (1:Mat (Fin b) (Fin b)).mulVec := by intro i j he; simpa using he
  refine ⟨M,Matrix.mulVec_injective_iff.mpr ?_⟩
  exact (Matrix.mulVec_injective_iff.mp hf).comp (Fin.castLE h) (Fin.castLE_injective h)

theorem bounded_pack {I : Type} [Fintype I] (S : Space (Vec I)) (k : ℕ) :
    ∃ M : Mat I (Fin k), colSp M ≤ S ∧ dim (colSp M) = min (dim S) k := by
  have h (M : Mat (Fin (dim S)) (Fin k)) : colSp (pack S*M) ≤ S := by
    rw [colSp,mulVecLin_mul,LinearMap.range_comp]
    apply le_trans (Submodule.map_mono (show _ ≤ ⊤ from le_top))
    rw [←LinearMap.range_eq_map]
    exact (colSp_pack S).le
  by_cases hs : dim S ≤ k
  · obtain ⟨M,hM⟩ := pad_matrix_inj _ _ hs
    refine ⟨pack S * Mᵀ,h _,?_⟩
    have hg : Function.Surjective Mᵀ.mulVecLin := transpose_surj_iff.mpr hM
    have hh : colSp (pack S * Mᵀ) = S := by
      rw [colSp,mulVecLin_mul,LinearMap.range_comp,
        LinearMap.range_eq_top.mpr hg,← LinearMap.range_eq_map]; exact colSp_pack S
    rw [hh,min_eq_left hs]
  · obtain ⟨M,hM⟩ := pad_matrix_inj _ _ (by omega : k ≤ dim S)
    refine ⟨pack S * M,h _,?_⟩
    have hh := mrk_inj.mp (inj_comp_mat _ _ (pack_inj S) hM)
    rw [colSp_dim,hh,Fintype.card_fin,min_eq_right (by omega)]

open Filter

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MatrixRankCounting
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matrix Rank Counting -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap
open scoped BigOperators

theorem cast_mat (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] :
    num (Mat I J)=bp (num I*num J) := by
  unfold num
  rw [card_space,dim_mat]
  push_cast; rfl

theorem nbr_nonneg {A : Type} [Fintype A] (p : A → Prop) : 0 ≤ nbr p :=
  tot_nonneg fun _ => ind_nonneg _

theorem nbr_le_sum {A B : Type} [Fintype A] [Fintype B] (p : A → Prop)
    (q : B → A → Prop) (h : ∀ i, p i → ∃ j,q j i) :
    nbr p ≤ ∑ j, nbr (q j) := by
  have hp (p : A → Prop) : nbr p = pr (fun _ => 1) p := by simp [nbr,pr,avg,tot]
  rw [hp]
  simp_rw [hp]
  exact (pr_mono (fun _ => zero_le_one) h).trans (pr_exists_le (fun _ => zero_le_one) q)

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]

omit [DecidableEq I] [DecidableEq J] in
theorem mul_factor (M : Mat I J) (r : ℕ) (h : M.rank ≤ r) :
    ∃ A : Mat I (Fin r),∃ B : Mat (Fin r) J,A*B=M := by
  obtain ⟨A,B,_,_,hg⟩ := rank_product M
  obtain ⟨a,ha⟩ := pad_matrix_inj M.rank r h
  obtain ⟨b,hb⟩ := mat_left_inv ha
  refine ⟨A*b,a*B,?_⟩
  rw [←Matrix.mul_assoc,Matrix.mul_assoc A b,hb,Matrix.mul_one,hg]

theorem nbr_matrix_rank (k : ℕ) :
    nbr (fun M : Mat I J => M.rank ≤ k) ≤ bp ((num I+num J)*k) := by
  classical
  let v := Mat I (Fin k) × Mat (Fin k) J
  let q (x : Mat I (Fin k) × Mat (Fin k) J) (M : Mat I J) := x.1*x.2=M
  refine (nbr_le_sum _ q fun M h => ?_).trans_eq ?_
  · obtain ⟨A,B,hB⟩ := mul_factor M k h
    exact ⟨(A,B),hB⟩
  have h (x : Mat I (Fin k) × Mat (Fin k) J) : nbr (q x) = 1 := by
    unfold nbr tot
    rw [Finset.sum_eq_single (x.1*x.2)]
    · simp [q,ind]
    · intro j _ h; simp [q,ind,h.symm]
    · simp
  simp_rw [h]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,mul_one]
  change num (Mat I (Fin k) × Mat (Fin k) J)=_
  rw [num,Fintype.card_prod,Nat.cast_mul]
  change num (Mat I (Fin k))*num (Mat (Fin k) J)=_
  rw [cast_mat,cast_mat,← bp_add]
  simp [num]
  ring_nf

theorem pr_matrix_rank (k : ℕ) :
    pr unif (fun M : Mat I J => M.rank≤ k) ≤
      bp ((num I+num J)*k-num I*num J) := by
  rw [pr_unif,bp_sub, ← cast_mat]
  exact div_le_div_of_nonneg_right (nbr_matrix_rank k) (Nat.cast_nonneg _)

theorem pr_mult_mat {A : Mat J K} (h : Function.Injective A.mulVec) (B : Mat I K) :
    pr unif (fun M => M*A=B) = bp (-num I*num K) := by
  obtain ⟨P,hP⟩ := mat_left_inv h
  have hh : Function.Surjective (rmult I A) :=
    fun C => ⟨C*P,by change C*P*A=C; rw [Matrix.mul_assoc,hP,Matrix.mul_one]⟩
  change mapW unif (rmult I A) B = _
  rw [map_unif_surjective _ hh, unif_apply, neg_mul,bp_neg,←cast_mat]

theorem pr_deficient (k : ℕ) :
    pr unif (fun M : Mat I J => M.rank + k ≤ Fintype.card J) ≤
      bp ((num J-num I)*k) := by
  classical
  let p (A : Mat J (Fin k)) (M : Mat I J) :=
    Function.Injective A.mulVec ∧ M*A=0
  refine ((pr_mono unif_law.nz fun M hm => ?_).trans
    (pr_exists_le unif_law.nz p)).trans ?_
  · let S := LinearMap.ker M.mulVecLin
    have hx := M.mulVecLin.finrank_range_add_finrank_ker
    change M.rank+dim S=dim (Vec J) at hx
    rw [dim_vec] at hx
    have hle : k ≤ dim S := Nat.le_of_add_le_add_left (hm.trans_eq hx.symm)
    obtain ⟨A,hA,h'⟩ := bounded_pack S k
    refine ⟨A,Matrix.mulVec_injective_iff.mpr ?_,?_⟩
    · apply Matrix.mulVec_injective_iff.mp
      apply mrk_inj.mpr
      rw [← colSp_dim,h',min_eq_right hle,Fintype.card_fin]
    apply coe_mv_inj
    change (M*A).mulVecLin = Matrix.mulVecLin 0
    rw [Matrix.mulVecLin_mul,Matrix.mulVecLin_zero]
    exact LinearMap.ext fun x => hA (show A.mulVecLin x ∈ colSp A from ⟨x,rfl⟩)
  have h (A : Mat J (Fin k)) : pr unif (p A) ≤ bp (-num I*k) := by
    by_cases hh : Function.Injective A.mulVec
    · simp only [p,hh,true_and]
      erw [pr_mult_mat hh]
      simp [num]
    simp only [p,hh,false_and,pr_false]
    exact (bp_pos _).le
  apply (Finset.sum_le_sum fun i _ => h i).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  change num (Mat J (Fin k))*_ = _
  rw [cast_mat,←bp_add]
  congr 1
  unfold num; rw [Fintype.card_fin]; ring

variable (p : Shape)

theorem nbr_profile_rank (K n : ℕ) :
    let d := Fintype.card (Row p n)
    nbr (fun M : Profile p n => totalRank M ≤ K) ≤
      (K+1:ℝ)^Fintype.card (Comp p.g) * bp (2*d*K) := by
  classical
  intro d
  let q (r : Comp p.g → Fin (K+1)) (M : Profile p n) :=
    (∑ i,(r i).val) ≤ K ∧ ∀ i, (M i).rank=(r i).val
  refine le_trans (nbr_le_sum _ q ?_) ?_
  · intro M h
    have hh i : (M i).rank≤K :=
      (Finset.single_le_sum (s:=Finset.univ) (fun i _ => Nat.zero_le ((M i).rank))
        (Finset.mem_univ i)).trans h
    exact ⟨fun i => ⟨_,Nat.lt_succ_of_le (hh i)⟩,h,fun _ => rfl⟩
  have he r : nbr (q r) ≤ bp (2*d*K) := by
    by_cases h : (∑ i:Comp p.g, (r i).val) ≤ K
    · unfold nbr
      let c (i : Comp p.g) (M : Moment p n) := (M.rank=(r i).val)
      simp_rw [q,h,true_and,ind_all]
      change tot (prodW (β:=fun _ => Moment p n) (fun i M => ind (c i M))) ≤ _
      rw [prodW_tot]
      have hx i : nbr (c i) ≤ bp (2*d*(r i).val) := by
        let w := (r i).val
        have h1 := nbr_matrix_rank (I:=Row p n) (J:=Row p n) w
        rw [← two_mul] at h1
        exact le_trans (tot_mono (fun x => ind_mono (p:=x.rank=w) (q:=x.rank≤w) (fun e => e.le))) h1
      refine (Finset.prod_le_prod (fun i _ => nbr_nonneg (c i)) (fun i _ => hx i)).trans ?_
      rw [←bp_sum,← Finset.mul_sum, ← Nat.cast_sum]
      apply bp_le
      gcongr
    · simp only [q,h,false_and,nbr,tot,ind_false,Finset.sum_const_zero]
      exact (bp_pos _).le
  refine (Finset.sum_le_sum fun i _ => he i).trans_eq ?_
  simp

open Filter
theorem profile_count (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, nbr (fun M : Profile p n => totalRank M≤K) ≤ bp ((profileA p K:ℝ)*n) := by
  let B := (K+1:ℝ)^Fintype.card (Comp p.g)
  have h := bp_poly_dom_nat (a:=1) zero_lt_one B 0
  have h1 : 0 < psize p := Fintype.card_pos_iff.mpr ⟨emptySel⟩
  filter_upwards [h,eventually_ge_atTop 1] with n hn hN
  simp only [pow_zero,mul_one,one_mul] at hn
  refine le_trans (nbr_profile_rank p K n) (le_trans
    (mul_le_mul_of_nonneg_right hn.le (bp_pos _).le) ?_)
  rw [← bp_add]
  apply bp_le
  simp only [card_row, profileA]
  push_cast
  let s := psize p
  have he : 1 ≤ s := h1
  have h' :
      n+2*(s*(1+(p.g*p.g+3)*n))*K ≤ 10*(K+1)*s*(p.g*p.g+5)*n := by
    have hi : 1+(p.g*p.g+3)*n ≤ (p.g*p.g+4)*n := by nlinarith
    have hl : s*(1+(p.g*p.g+3)*n) ≤ s*((p.g*p.g+4)*n) := by gcongr
    have hh : n ≤ s*n := by nlinarith
    nlinarith only [Nat.mul_le_mul_right K hl,hh, Nat.zero_le (s*p.g*p.g*n),
      Nat.zero_le (s*n),Nat.zero_le (s*K*p.g*p.g*n),Nat.zero_le (s*K*n)]
  exact_mod_cast h'

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BinaryEvaluationForms
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary Evaluation Forms -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix
variable {p : Shape} {n : ℕ}

theorem pullT {I J V U : Type} [Fintype V] [Fintype U]
    (A : Mat V U) (P : Mat U I) (Q : Mat V J) :
    pullM P Q Aᵀ = (pullM Q P A)ᵀ := by
  rw [pullM_def,pullM_def,transpose_mul,transpose_mul,transpose_transpose,Matrix.mul_assoc]

theorem obsZ_self (s t : Label p.b) (f : Vec Bool) (m : Mixer p n) :
    pullM (blockRay p n s Block.Z) (blockRay p n t Block.Z) (selfSum m f) = 0 := by
  rw [selfSum,Fintype.sum_bool,map_add,map_smul,map_smul]
  change _ • pullM _ _ (selfM p n m.mixM) + _ • pullM _ _ (selfM p n m.mixM)ᵀ = 0
  rw [pullT,pull_self_Z,pull_self_Z]
  simp

private theorem two_eval (s t : Label p.b) (hj : 1≤p.j) (hs : s≠t)
    (x : Bool → Mat (Fin n) (Fin n)) :
    ∃ A : Moment p n, ∀ b, pullM (blockRay p n s Block.Z) (blockRay p n t Block.Z)
      (eitherM b A) = x b := by
  let P := blockRay p n s Block.Z
  let Q := blockRay p n t Block.Z
  have hh : Function.Injective (fromCols P Q).mulVec := joined_block_inj hj hs _
  obtain ⟨L,hL⟩ := prescribe_between hh hh
    (fromBlocks (0:Mat (Fin n) (Fin n)) (x true) (x false)ᵀ (0:Mat (Fin n) (Fin n)))
  rw [transpose_fromCols,fromRows_mul,fromRows_mul_fromCols] at hL
  have hx : pullM P Q L = x true := congrArg Matrix.toBlocks₁₂ hL
  have hy : pullM Q P L = (x false)ᵀ := congrArg Matrix.toBlocks₂₁ hL
  refine ⟨L,fun b => ?_⟩
  cases b
  · change pullM P Q Lᵀ=x false
    rw [pullT,hy,transpose_transpose]
  · exact hx

theorem obsZ_surj (s t : Label p.b) (hj : 1≤p.j) (hs : s≠t)
    {c : Vec (MBits p)} (hc : c ≠ 0) : Function.Surjective (obsZ p n s t c) := by
  classical
  simp only [ne_eq,funext_iff,Pi.zero_apply,not_forall] at hc
  obtain ⟨i,hi⟩ := hc
  intro M
  let y (j : MBits p) := if j=i then M else 0
  choose A hA using fun j : MOne p => two_eval s t hj hs (fun b => y (j,b))
  let D : Draw p n := (fun j => A (j,true), fun j => A (j,false), 0)
  have he (j : MBits p) :
      pullM (blockRay p n s Block.Z) (blockRay p n t Block.Z)
        (eitherM j.2 (orderedM (drawn D) j.1)) = y j := by
    rcases j with ⟨⟨j,_|_⟩,x⟩
    · exact hA _ _
    · exact hA _ _
  refine ⟨D,?_⟩
  simp only [obsZ,indexedSum,map_sum,map_smul,he,LinearMap.coe_mk,AddHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · simp [y,(bit_cases (c i)).resolve_left hi]
  · intro j _ hj; simp [y,hj]
  simp

theorem pull_selfPart (s t : Label p.b) (hj : 1 ≤ p.j) (f : Vec Bool) (D : Draw p n) :
    pullM (blockRay p n s Block.sharp) (blockRay p n t Block.sharp) (selfSum (drawn D) f) =
      selfPartial (p:=p) s t f D := by
  rw [selfSum, Fintype.sum_bool,map_add,map_smul,map_smul]
  change _ • pullM _ _ (selfM p n D.2.2) + _ • pullM _ _ (selfM p n D.2.2)ᵀ = _
  rw [pullT,pull_self_sharp _ _ _ hj,pull_self_sharp _ _ _ hj]
  unfold selfPartial
  congr 2
  simp only [add_comm]

/-- Uniform off-diagonal block even in transpose-character case. -/
theorem obsHalf_surj (s t : Label p.b) (hs : s≠t) {f : Vec Bool} (hf : f≠0) (n : ℕ)
    {l r : Fin (n/2)→Fin n} (hl : Function.Injective l) (hr : Function.Injective r)
    (h : ∀ i j,l i≠r j) : Function.Surjective (obsHalf p s t f n l r) := by
  classical
  intro M
  obtain ⟨a,ha⟩ : ∃ a,s a+t a=1 := by
    obtain ⟨a,ha⟩ := Function.ne_iff.mp hs
    exact ⟨a,(bit_cases _).resolve_left (fun h => ha
      (add_right_cancel (h.trans (char_two _).symm)))⟩
  let m := n/2
  let P := embedMat l
  let Q := embedMat r
  have hi : Function.Injective (fromCols P Q).mulVec := by
    have he : fromCols P Q = embedMat (Sum.elim l r) := by ext i j; cases j <;> rfl
    rw [he]; apply embedMat_inj
    rintro (x|x) (y|y) g
    · rw [hl g]
    · exact (h _ _ g).elim
    · exact (h _ _ g.symm).elim
    · rw [hr g]
  have hv (x y : Mat (Fin m) (Fin m)) :
      ∃ A : Mat (Fin n) (Fin n), A.submatrix l r=x ∧ Aᵀ.submatrix l r=y := by
    obtain ⟨A,hA⟩ := prescribe_between hi hi (fromBlocks (0:Mat (Fin m) (Fin m)) x yᵀ
      (0:Mat (Fin m) (Fin m)))
    rw [transpose_fromCols,fromRows_mul,fromRows_mul_fromCols] at hA
    have h1 : Pᵀ*A*Q=x := congrArg Matrix.toBlocks₁₂ hA
    have h2 : Qᵀ*A*P=yᵀ := congrArg Matrix.toBlocks₂₁ hA
    unfold P Q at *
    rw [embedMat_mul,mul_embedMat] at h1 h2
    exact ⟨A,h1,congrArg Matrix.transpose h2⟩
  obtain ⟨x,y,hx⟩ : ∃ x y : Mat (Fin m) (Fin m), f true • x+f false • y=M := by
    rcases bit_cases (f true) with g|g
    · have hg : f false≠0 := fun hg => hf (funext fun i => by cases i <;> assumption)
      exact ⟨0,M,by rw [(bit_cases _).resolve_left hg]; simp⟩
    · exact ⟨M,0,by rw [g]; simp⟩
  obtain ⟨A,h1,h2⟩ := hv x y
  let D : Draw p n := (0,0,Pi.single a A)
  have hE :
      ∑ i,(s i+t i) • D.2.2 i=A := by
    rw [Finset.sum_eq_single a]
    · simp [D,ha]
    · intro i _ hi; simp [D,Pi.single_eq_of_ne hi]
    simp
  refine ⟨D,?_⟩
  change (selfPartial (p:=p) s t f D).submatrix l r=M
  unfold selfPartial
  rw [hE]
  change (f true • A + f false • Aᵀ).submatrix l r = _
  change f true • A.submatrix l r + f false • Aᵀ.submatrix l r = M
  rw [h1,h2,hx]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Entropy -/

noncomputable section
namespace HadwigerCounterexample

open scoped BigOperators
open Real

variable {α : Type*} [Fintype α]

theorem closed_isLaw : IsClosed {w : Wgt α | IsLaw w} := by
  have he :
      {w : Wgt α | IsLaw w} =
        (⋂ x : α, {w | 0 ≤ w x}) ∩ {w : Wgt α | tot w = 1} := by
    ext w; simp
    constructor
    · intro hw
      exact ⟨hw.nz, hw.total⟩
    · rintro ⟨h,g⟩
      exact ⟨h,g⟩
  rw [he]
  refine (isClosed_iInter (fun x => ?_)).inter (isClosed_eq tot_continuous continuous_const)
  exact isClosed_le continuous_const (continuous_apply x)

theorem compact_isLaw : IsCompact {w : Wgt α | IsLaw w} := by
  refine IsCompact.of_isClosed_subset (s := Set.Icc (0 : Wgt α) 1) isCompact_Icc
    closed_isLaw ?_
  intro w hw
  exact ⟨hw.nz, hw.weight_le_one⟩

theorem negEnt_le_zero {w : Wgt α} (hw : SubLaw w) : negEnt w ≤ 0 := by
  refine Finset.sum_nonpos fun x _ => mul_nonpos_of_nonneg_of_nonpos (hw.nz x) ?_
  exact Real.log_nonpos (hw.nz x) (hw.weight_le_one x)

private theorem log_bound {m x : ℝ} (hm : 0 < m) (hx : 0 ≤ x) :
    x * (1 - Real.log m) - m⁻¹ ≤ x * Real.log x := by
  rcases lt_or_eq_of_le hx with h | h
  · have hp := Real.self_sub_one_le_mul_log (show 0 ≤ m*x from mul_nonneg hm.le hx)
    rw [Real.log_mul hm.ne' h.ne'] at hp
    apply (mul_le_mul_iff_right₀ hm).mp

    have hi := mul_inv_cancel₀ hm.ne'
    nlinarith only [hp, hi]
  · rw [← h]
    have := inv_pos.mpr hm
    linarith

theorem log_card_le_negEnt [Nonempty α] {w : Wgt α} (hw : IsLaw w) :
    -Real.log (Fintype.card α) ≤ negEnt w := by
  let m := (Fintype.card α : ℝ)
  have hm : 0 < m := by simp [m, Fintype.card_pos]
  have h1 :
      ∑ x, (w x * (1 - Real.log m) - m⁻¹) ≤ negEnt w :=
    Finset.sum_le_sum fun x _ => log_bound hm (hw.nz x)
  have hs : ∑ x, w x = 1 := hw.total
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul, Finset.sum_const] at h1
  simp only [Finset.card_univ, nsmul_eq_mul] at h1
  change 1 - Real.log m - m * m⁻¹ ≤ _ at h1
  rw [mul_inv_cancel₀ hm.ne'] at h1
  change -Real.log m ≤ _
  linarith

private theorem negEnt_gap_elem {x y : ℝ} (h : 0 ≤ x) (g : 0 ≤ y) :
    0 ≤ x * Real.log x + y * Real.log y
      - 2 * (((x + y)*2⁻¹) * Real.log ((x + y)*2⁻¹)) := by
  have hh := Real.convexOn_mul_log.2 (Set.mem_Ici.mpr h) (Set.mem_Ici.mpr g)
    (by norm_num : 0 ≤ (2:ℝ)⁻¹) (by norm_num : 0 ≤ (2:ℝ)⁻¹) (by norm_num)
  simp only [smul_eq_mul] at hh
  rw [show 2⁻¹*x+2⁻¹*y = (x+y)*2⁻¹ by ring] at hh
  linarith

private theorem negEnt_gap_on_zero {x : ℝ} (hx : 0 ≤ x) :
    x * Real.log x - 2 * ((x * 2⁻¹) * Real.log (x * 2⁻¹)) = x * Real.log 2 := by
  rcases lt_or_eq_of_le hx with h | h
  · rw [Real.log_mul h.ne' (by norm_num), Real.log_inv]; ring
  · rw [← h]; ring

/-- Mixing two laws incurs a quantified entropy gap if one gives mass to a set
missed by the other. This midpoint bound suffices without a support lemma. -/
theorem negEnt_gap {w v : Wgt α} (hw : ∀ x, 0 ≤ w x) (hv : ∀ x, 0 ≤ v x)
    (p : α → Prop) (hp : ∀ x, p x → v x = 0) :
    pr w p * Real.log 2 ≤ negEnt w + negEnt v - 2 * negEnt (midLaw w v) := by
  unfold pr avg negEnt
  rw [Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hx : p x
  · simp only [hp x hx, ind_one hx, mul_one, midLaw, add_zero, zero_mul]
    rw [negEnt_gap_on_zero (hw x)]
  · simp only [ind_zero hx, mul_zero, zero_mul]
    exact negEnt_gap_elem (hw _) (hv _)

theorem mid_tot (w v : Wgt α) : tot (midLaw w v) = (tot w + tot v) * 2⁻¹ := by
  rw [tot, tot, tot, ← Finset.sum_add_distrib, Finset.sum_mul]
  rfl

theorem midLaw_pr (w v : Wgt α) (p : α → Prop) :
    pr (midLaw w v) p = (pr w p + pr v p) * 2⁻¹ := by
  unfold pr
  rw [avg_comm, avg_comm w, avg_comm v]
  change avg _ (fun x => (w x + v x) * 2⁻¹) = _
  rw [avg_mul, avg_add]

theorem mid_isLaw {w v : Wgt α} (hw : IsLaw w) (hv : IsLaw v) : IsLaw (midLaw w v) := by
  refine ⟨fun x => mul_nonneg (add_nonneg (hw.nz x) (hv.nz x)) (by norm_num), ?_⟩
  rw [mid_tot, hw.total, hv.total]; norm_num

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_EntropyContainers
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entropy Containers -/

noncomputable section
open scoped BigOperators
open Real Finset
namespace HadwigerCounterexample

variable {α : Type*} [Fintype α]

private theorem avg_reached {w f : Wgt α} (hw : IsLaw w) :
    ∃ x, 0 < w x ∧ avg w f ≤ f x := by
  by_contra! hn
  have hp := exists_of_pr_pos (p:=fun _ => True) hw.nz (by rw [pr_true, hw.total]; norm_num)
  obtain ⟨x, _, hx⟩ := hp
  have h : avg w f < avg w (fun _ => avg w f) := by
    unfold avg
    apply Finset.sum_lt_sum
    · intro y _
      by_cases h : 0 < w y
      · exact mul_le_mul_of_nonneg_left (hn y h).le h.le
      · rw [le_antisymm (le_of_not_gt h) (hw.nz _), zero_mul, zero_mul]
    · exact ⟨x, mem_univ _, mul_lt_mul_of_pos_left (hn x hx) hx⟩
  rw [hw.avg_const] at h
  exact lt_irrefl _ h

omit [Fintype α] in
theorem closed_carried (p : α → Prop) : IsClosed {w : Wgt α | carried w p} := by
  have he : {w : Wgt α | carried w p} = ⋂ (x : α) (_ : ¬ p x), {w | w x = 0} := by
    ext; simp [carried]
  rw [he]
  exact isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_eq (continuous_apply x)
    continuous_const

/-- Cover the conflict-independent sets in R by a small family of terminal sets. -/
theorem containers {ok : Set (Wgt α)} (hcomp : IsCompact ok) (hok : ∀ w ∈ ok, IsLaw w)
    (hmid : ∀ w ∈ ok, ∀ v ∈ ok, midLaw w v ∈ ok) (rel : α → α → Prop)
    {e : ℝ} (he : 0 < e) (R : Finset α)
    (hsat : ∀ w ∈ ok, carried w (· ∈ R) →
      e ≤ pr (pairW w w) (fun x => rel x.1 x.2))
    (L : ℕ) (hL : ∀ w ∈ ok, carried w (· ∈ R) →
      0 < negEnt w + L * (e * Real.log 2)) :
    ∃ C : Finset (Finset α),
      C.card ≤ (R.card + 1)^L ∧
      (∀ r ∈ C, r ⊆ R ∧ ¬∃ w ∈ ok, carried w (· ∈ r)) ∧
      ∀ I : Finset α, I ⊆ R → (∀ v ∈ I, ∀ u ∈ I, ¬rel v u) →
        ∃ r ∈ C, I ⊆ r := by
  classical
  induction R using Finset.strongInductionOn generalizing L with | _ R ih
  by_cases h : ∃ w ∈ ok, carried w (· ∈ R)
  · let T := ok ∩ {w : Wgt α | carried w (· ∈ R)}
    have hn : T.Nonempty := h
    obtain ⟨w, hw, hwmin⟩ := (hcomp.inter_right (closed_carried (· ∈ R))).exists_isMinOn hn
      negEnt_continuous.continuousOn
    have hwL := hok w hw.1
    obtain ⟨v,hv,hv'⟩ := avg_reached (w:=w) (f:=fun x => pr w (rel x)) hwL
    have hvR : v ∈ R := Classical.byContradiction (fun h => hv.ne' (hw.2 v h))
    have he' : e ≤ pr w (rel v) := by
      have h := hsat w hw.1 hw.2
      unfold pr at *
      rw [pairW_avg] at h
      exact h.trans hv'
    have hwl : 0 < negEnt w + L * (e * Real.log 2) := hL w hw.1 hw.2
    cases L with
    | zero =>
      have hnonpos := negEnt_le_zero hwL.sub
      simp [show ¬ (0 < negEnt w) from not_lt.mpr hnonpos] at hwl
    | succ L =>
      let R₁ := R.erase v
      let R₂ := R.filter (fun x => ¬rel v x)
      have hr₁ : R₁ ⊂ R := Finset.erase_ssubset hvR
      have hr₂ : R₂ ⊂ R := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
        obtain ⟨x,hx,hx'⟩ := exists_of_pr_pos hwL.nz (lt_of_lt_of_le he he')
        intro h
        have hxr : x ∈ R := Classical.byContradiction fun h => hx'.ne' (hw.2 _ h)
        rw [← h] at hxr
        exact (mem_filter.mp hxr).2 hx
      have hm {r : Finset α} (hr : r ⊂ R) {w : Wgt α}
          (h : carried w (· ∈ r)) : carried w (· ∈ R) :=
        fun x hx => h x (fun hxr => hx (subset_of_ssubset hr hxr))
      obtain ⟨C, hC, htC, hcovC⟩ := ih R₁ hr₁ (fun w hw h => hsat w hw (hm hr₁ h))
        (L+1) (fun w hw h => hL w hw (hm hr₁ h))
      obtain ⟨D, hD, htD, hcovD⟩ := ih R₂ hr₂ (fun w hw h => hsat w hw (hm hr₂ h)) L (by
        intro u hu hRu
        have hmidT : midLaw w u ∈ T := by
          refine ⟨hmid w hw.1 u hu, fun x hx => ?_⟩
          simp [midLaw, hw.2 x hx, hm hr₂ hRu x hx]
        have hle : negEnt w ≤ negEnt (midLaw w u) := hwmin hmidT
        have hh := negEnt_gap hwL.nz (hok u hu).nz (rel v) (fun x hx =>
          hRu x (fun h => (mem_filter.mp h).2 hx))
        have hy : e * Real.log 2 ≤ pr w (rel v) * Real.log 2 := by
          gcongr
        push_cast at hwl
        linarith)
      refine ⟨C ∪ D, ?_, ?_, ?_⟩
      · refine (card_union_le _ _).trans ?_
        have h₁ : C.card ≤ R.card^(L+1) :=
          hC.trans (by gcongr; exact card_lt_card hr₁)
        have h₂ : D.card ≤ R.card^L :=
          hD.trans (by gcongr; exact card_lt_card hr₂)
        refine (add_le_add h₁ h₂).trans ?_
        rw [pow_succ, pow_succ]
        calc R.card ^ L * R.card + R.card ^ L = R.card ^ L * (R.card + 1) := by ring
             _ ≤ _ := by gcongr; omega
      · intro r hr
        rcases mem_union.mp hr with hr|hr
        · exact ⟨(htC r hr).1.trans (subset_of_ssubset hr₁), (htC r hr).2⟩
        · exact ⟨(htD r hr).1.trans (subset_of_ssubset hr₂), (htD r hr).2⟩
      · intro I hIR hI
        by_cases h : v ∈ I
        · have h' : I ⊆ R₂ := fun x hx => mem_filter.mpr ⟨hIR hx,hI v h x hx⟩
          obtain ⟨r,h1,h2⟩ := hcovD I h' hI
          exact ⟨r,mem_union_right _ h1,h2⟩
        · have h' : I ⊆ R₁ := fun x hx => mem_erase.mpr ⟨fun hxv => h (hxv ▸ hx),hIR hx⟩
          obtain ⟨r,h1,h2⟩ := hcovC I h' hI
          exact ⟨r,mem_union_left _ h1,h2⟩
  · refine ⟨{R}, ?_, ?_, ?_⟩
    · rw [card_singleton]
      exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    · simpa using h
    · intro I hIR _; exact ⟨R, mem_singleton_self _, hIR⟩

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_TerminalCut
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Terminal Cut -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem closed_pairCaps (μ : Wgt α) (m d : ℝ) :
    IsClosed {w : Wgt (α × α) | pairCaps μ m d w} := by
  have e :
    {w : Wgt (α × α) | pairCaps μ m d w} =
      (⋂ x, {w | mapW w Prod.fst x ≤ m * μ x}) ∩
      ((⋂ x, {w | mapW w Prod.snd x ≤ m * μ x}) ∩
       (⋂ p, {w | w p ≤ d * pairW μ μ p})) := by ext; simp [pairCaps]
  rw [e]
  exact (isClosed_iInter fun _ => isClosed_le (pr_continuous _) continuous_const).inter
    ((isClosed_iInter fun _ => isClosed_le (pr_continuous _) continuous_const).inter
      (isClosed_iInter fun _ => isClosed_le (continuous_apply _) continuous_const))

theorem mid_pairCaps {μ : Wgt α} {m d : ℝ} {w v : Wgt (α × α)}
    (hw : pairCaps μ m d w) (hv : pairCaps μ m d v) :
    pairCaps μ m d (midLaw w v) := by
  have h1 (f : α × α → α) (x : α) :
      mapW (midLaw w v) f x = (mapW w f x + mapW v f x) * 2⁻¹ := midLaw_pr w v _
  constructor
  · intro x
    rw [h1]
    linarith only [hw.1 x, hv.1 x]
  refine ⟨fun x => ?_, fun p => ?_⟩
  · rw [h1]
    linarith only [hw.2.1 x, hv.2.1 x]
  · unfold midLaw
    linarith only [hw.2.2 p, hv.2.2 p]

theorem compact_subLaw : IsCompact {w : Wgt α | SubLaw w} := by
  refine IsCompact.of_isClosed_subset (s:=Set.Icc (0 : Wgt α) 1) isCompact_Icc ?_ ?_
  · have he :
        {w : Wgt α | SubLaw w} =
        (⋂ x, {w | 0 ≤ w x}) ∩ {w : Wgt α | tot w ≤ 1} := by
      ext w
      have : SubLaw w ↔ (∀ x, 0 ≤ w x) ∧ tot w ≤ 1 :=
        ⟨fun h => ⟨h.nz,h.total⟩, fun ⟨h,g⟩ => ⟨h,g⟩⟩
      simp [this]
    rw [he]
    exact (isClosed_iInter fun _ => isClosed_le continuous_const (continuous_apply _)).inter
      (isClosed_le tot_continuous continuous_const)
  · intro w hw
    exact ⟨hw.nz,hw.weight_le_one⟩

private theorem incW_tot (w : Wgt α) (p : α) (b : ℝ) :
    tot (incW w p b) = tot w + b := by
  classical simp [tot, incW, ind, Finset.sum_add_distrib]

private theorem incW_pr (w : Wgt α) (p : α) (b : ℝ) (q : α → Prop) :
    pr (incW w p b) q = pr w q + b * ind (q p) := by
  classical
  simp only [pr, avg, incW, add_mul, Finset.sum_add_distrib, add_right_inj]
  rw [Finset.sum_eq_single p]
  · simp [ind]
  · intro x _ h; simp [ind,h]
  · simp

private theorem sat_le_tot {u v : Wgt α} (hu : ∀ x, 0 ≤ u x) (b : ℝ) :
    b * pr v (fun x => u x = b * v x) ≤ tot u := by
  have e :
      b * pr v (fun x => u x = b * v x) = pr u (fun x => u x = b * v x) := by
    unfold pr avg
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : u x = b * v x <;> simp [ind, h]
  rw [e]; exact pr_le_tot hu

private theorem mapW_tot' {β : Type*} [Fintype β] (w : Wgt α) (f : α → β) :
    tot (mapW w f) = tot w := by simpa using mapW_pr w f (fun _ => True)

theorem terminal {μ : Wgt α} (hu : ∀ x, 0 ≤ μ x)
    {m d : ℝ} (hm : 0 < m) (hd : 0 < d) (R : α × α → Prop)
    (hR : ¬∃ w : Wgt (α × α), IsLaw w ∧ pairCaps μ m d w ∧ carried w R) :
    ∃ (S : α → Prop) (E : α × α → Prop),
      m * pr μ S < 2 ∧ d * pr (pairW μ μ) E < 1 ∧
      ∀ x : α × α, R x → S x.1 ∨ S x.2 ∨ E x := by
  let T := {w : Wgt (α × α) | SubLaw w} ∩
    ({w | pairCaps μ m d w} ∩ {w | carried w R})
  have hc : IsCompact T := compact_subLaw.inter_right
    ((closed_pairCaps _ _ _).inter (closed_carried _))
  have ht : T.Nonempty := by
    refine ⟨(fun _ => 0), ⟨?_,?_⟩, ⟨fun x => ?_, fun x => ?_, fun p => ?_⟩, fun _ _ => rfl⟩
    · exact fun _ => le_rfl
    · simp [tot]
    · simpa [mapW,pr,avg] using mul_nonneg hm.le (hu x)
    · simpa [mapW,pr,avg] using mul_nonneg hm.le (hu x)
    · exact mul_nonneg hd.le (mul_nonneg (hu _) (hu _))
  obtain ⟨w,hw,hwmax⟩ := hc.exists_isMaxOn ht tot_continuous.continuousOn
  have hwL : SubLaw w := hw.1
  have hwC : pairCaps μ m d w := hw.2.1
  have hw' : tot w < 1 := lt_of_le_of_ne hwL.total (fun he =>
    hR ⟨w,⟨hwL.nz,he⟩,hwC,hw.2.2⟩)
  let hit (f : α × α → α) (x : α) := mapW w f x = m * μ x
  let EH (p : α × α) := w p = d * pairW μ μ p
  refine ⟨fun x => hit Prod.fst x ∨ hit Prod.snd x, EH, ?_, ?_, ?_⟩
  · have hh (f : α × α → α) : m * pr μ (hit f) < 1 := by
      apply lt_of_le_of_lt _ hw'
      rw [← mapW_tot' w f]
      exact sat_le_tot (fun _ => pr_nonneg hwL.nz) m
    have h := mul_le_mul_of_nonneg_left
      (pr_or_le (p:=hit Prod.fst) (q:=hit Prod.snd) hu) hm.le
    linarith only [h, hh Prod.fst, hh Prod.snd]
  · exact lt_of_le_of_lt (sat_le_tot hwL.nz d) hw'
  intro x hx
  by_contra hn
  push Not at hn
  have hg : 0 < m * μ x.1 - mapW w Prod.fst x.1 :=
    sub_pos.mpr (lt_of_le_of_ne (hwC.1 _) hn.1.1)
  have hi : 0 < m * μ x.2 - mapW w Prod.snd x.2 :=
    sub_pos.mpr (lt_of_le_of_ne (hwC.2.1 _) hn.2.1.2)
  have hj : 0 < d * pairW μ μ x - w x := sub_pos.mpr
    (lt_of_le_of_ne (hwC.2.2 _) hn.2.2)
  obtain ⟨b,hb,h1,h2,h3,h4⟩ : ∃ b : ℝ, 0 < b ∧ b ≤ 1 - tot w ∧
      b ≤ m * μ x.1 - mapW w Prod.fst x.1 ∧
      b ≤ m * μ x.2 - mapW w Prod.snd x.2 ∧ b ≤ d * pairW μ μ x - w x := by
    let b := min (min (1 - tot w) (m * μ x.1 - mapW w Prod.fst x.1))
      (min (m * μ x.2 - mapW w Prod.snd x.2) (d * pairW μ μ x - w x))
    refine ⟨b, lt_min (lt_min (sub_pos.mpr hw') hg) (lt_min hi hj), ?_,?_,?_,?_⟩
    · exact le_trans (min_le_left _ _) (min_le_left _ _)
    · exact le_trans (min_le_left _ _) (min_le_right _ _)
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hmap (f : α × α → α) (y : α) : mapW (incW w x b) f y =
      mapW w f y + b * ind (f x = y) := incW_pr w x b _
  have hm : incW w x b ∈ T := by
    refine ⟨⟨fun _ => add_nonneg (hwL.nz _) (mul_nonneg hb.le (ind_nonneg _)),?_⟩,
      ⟨fun y => ?_, fun y => ?_, fun p => ?_⟩, fun y hy => ?_⟩
    · rw [incW_tot]; linarith only [h1]
    · by_cases h : x.1 = y
      · subst y
        rw [hmap]
        simp only [ind_true, mul_one]
        linarith only [h2]
      · rw [hmap, ind_zero h, mul_zero, add_zero]
        exact hwC.1 y
    · by_cases h : x.2 = y
      · subst y
        rw [hmap]
        simp only [ind_true, mul_one]
        linarith only [h3]
      · rw [hmap, ind_zero h, mul_zero, add_zero]
        exact hwC.2.1 y
    · by_cases h : p = x
      · subst p
        simp only [incW, ind_true, mul_one]
        linarith only [h4]
      · rw [incW, ind_zero h, mul_zero, add_zero]
        exact hwC.2.2 p
    · have h : y ≠ x := fun he => hy (he.symm ▸ hx)
      rw [incW, hw.2.2 y hy, ind_zero h, mul_zero, add_zero]
  have hle : tot (incW w x b) ≤ tot w := hwmax hm
  rw [incW_tot] at hle
  linarith only [hb, hle]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteGraphTransfer
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Graph Transfer -/

noncomputable section

namespace HadwigerCounterexample
open Finset Real HadwigerMatching
open scoped BigOperators
variable {A V : Type*}

private theorem badS_pr [Fintype A] {μ : Wgt A} (hμ : IsLaw μ)
    (S : A → Prop) (k m : ℕ) :
    pr (prodW (fun _ : Fin m => μ)) (badS S k) ≤
      2 ^ m * (pr μ S)^k := by
  classical
  let q := prodW (fun _ : Fin m => μ)
  have hp (T : Finset (Fin m)) :
      pr q (fun x => T.card = k ∧ ∀ v ∈ T, S (x v)) ≤ (pr μ S)^k := by
    by_cases h : T.card = k
    · have e (x : Fin m → A) : (∀ v ∈ T, S (x v)) ↔ ∀ v : T, S (x v.val) := by simp
      have h' := prodW_pr_inj (e:=fun v : T => v.val) Subtype.val_injective
        (w:=fun _ => μ) (fun _ => hμ) (fun _ : T => S)
      simp_rw [h, true_and, e]
      simp only [prod_const, Finset.card_univ, Fintype.card_coe,h] at h'
      exact h'.le
    · have hn : 0 ≤ pr μ S := pr_nonneg hμ.nz
      simp only [h, false_and, pr_false]
      positivity
  have he := pr_exists_le (prodW_nonneg (w:=fun _ : Fin m => μ) (fun _ => hμ.nz))
    (fun T : Finset (Fin m) => (fun x => T.card = k ∧ ∀ v ∈ T, S (x v)))
  refine he.trans ((sum_le_sum (fun i _ => hp i)).trans_eq ?_)
  simp

private theorem badE_pr [Fintype A] {μ : Wgt A} (hμ : IsLaw μ)
    (E : A × A → Prop) (k m : ℕ) :
    pr (prodW (fun _ : Fin m => μ)) (badE E k) ≤
      (m : ℝ)^(k+k) * (pr (pairW μ μ) E)^k := by
  classical
  let Q := prodW (fun _ : Fin m => μ)
  let P (e : Fin k ⊕ Fin k → Fin m) (x : Fin m → A) :=
    Function.Injective e ∧ ∀ i, E (x (e (.inl i)), x (e (.inr i)))
  have hp (e : Fin k ⊕ Fin k → Fin m) :
      pr Q (P e) ≤ (pr (pairW μ μ) E)^k := by
    by_cases h : Function.Injective e
    · have h' := prodW_map_pairs e h hμ
      let f (x : Fin m → A) (i : Fin k) := (x (e (.inl i)), x (e (.inr i)))
      have hp : P e = (fun x => ∀ i, E (f x i)) := by simp [P,h,f]
      rw [hp, ← mapW_pr Q f (fun x => ∀ i, E (x i))]
      change mapW Q f = _ at h'
      rw [h']
      have hb := prodW_pr (w:=fun _ : Fin k => pairW μ μ) (p:=fun _ => E)
      simpa using hb.le
    · have hn : 0 ≤ pr (pairW μ μ) E := pr_nonneg (pairW_law hμ hμ).nz
      simp only [P,h,false_and,pr_false] <;> positivity
  have he := pr_exists_le (prodW_nonneg (w:=fun _ : Fin m => μ) (fun _ => hμ.nz)) P
  refine he.trans ((sum_le_sum (fun i _ => hp i)).trans_eq ?_)
  simp

private theorem many_bad {x : V → A} (S : A → Prop) (E : A × A → Prop)
    {k t : ℕ} (ht : k + k ≤ t + 1)
    {e : Fin t ⊕ Fin t → V} (he : Function.Injective e)
    (hp : ∀ i, S (x (e (.inl i))) ∨ S (x (e (.inr i))) ∨
      E (x (e (.inl i)), x (e (.inr i)))) :
    badS S k x ∨ badE E k x := by
  classical
  let p (i : Fin t) := S (x (e (.inl i))) ∨ S (x (e (.inr i)))
  let I := univ.filter p
  let J := univ.filter (fun i => ¬ p i)
  by_cases hI : k ≤ I.card
  · left
    obtain ⟨r⟩ := Function.Embedding.nonempty_of_card_le
      (show Fintype.card (Fin k) ≤ Fintype.card I by simpa using hI)
    let f : Fin k → Fin t := fun i => r i
    have hf : Function.Injective f := fun i j g => r.injective (Subtype.ext g)
    let y : Fin k → Fin t ⊕ Fin t :=
      fun i => if S (x (e (.inl (f i)))) then .inl (f i) else .inr (f i)
    have hy (i : Fin k) : S (x (e (y i))) := by
      have h : p (f i) := (mem_filter.mp (r i).property).2
      unfold p at h
      unfold y
      split
      · assumption
      · rename_i hn; exact h.resolve_left hn
    have hid i : Sum.elim id id (y i) = f i := by unfold y; split <;> rfl
    have hy' : Function.Injective y := fun i j g =>
      hf (by rw [←hid,←hid,g])
    refine ⟨univ.image (e ∘ y), by rw [card_image_of_injective _ (he.comp hy')]; simp,?_⟩
    intro v hv
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    exact hy i
  · right
    have hJ : k ≤ J.card := by
      have hsum : I.card + J.card = t := by
        simpa using Finset.card_filter_add_card_filter_not (s:=univ) p
      omega
    obtain ⟨r⟩ := Function.Embedding.nonempty_of_card_le
      (show Fintype.card (Fin k) ≤ Fintype.card J by simpa using hJ)
    let f : Fin k → Fin t := fun i => r i
    have hf : Function.Injective f := fun i j g => r.injective (Subtype.ext g)
    refine ⟨e ∘ Sum.map f f, he.comp (Sum.map_injective.mpr ⟨hf,hf⟩),?_⟩
    intro i
    have h : ¬p (f i) := (mem_filter.mp (r i).property).2
    exact ((hp _).resolve_left (fun g => h (Or.inl g))).resolve_left
      (fun g => h (Or.inr g))

/-- Finite transfer with an explicit error term. If T denotes the terminal count
bound, it suffices that
T*(2^m*(2/M)^k + m^(2*k)*(1/D)^k) < 1.
The rate version just instantiates these inequalities. -/
theorem transfer [Fintype A] [Nonempty A] (H : Holes A) {μ : Wgt A} (hμ : IsLaw μ)
    {M D ε : ℝ} (hM : 0 < M) (hD : 0 < D) (hε : 0 < ε)
    (hsat : ∀ w : Wgt (A × A), IsLaw w → pairCaps μ M D w → carried w H.unit →
      ε ≤ pr (pairW w w) (fun x => H.conflict x.1 x.2))
    {L m k : ℕ} (hL : Real.log (Fintype.card (A × A)) < L * (ε * Real.log 2))
    (hk : 200*k < m+200)
    (herr :
      ((Fintype.card (A × A) : ℝ) + 1)^L *
        (2^m * (2/M)^k + (m:ℝ)^(k+k) * D⁻¹^k) < 1) :
    ∃ x : Fin m → A,
      (H.graph x).indepNum ≤ 2 ∧
      (connectedMatchingNumber (H.graph x) : ℚ) < (m : ℚ)/100 := by
  classical
  let R := univ.filter H.unit
  let O := {w : Wgt (A × A) | IsLaw w} ∩ {w | pairCaps μ M D w}
  obtain ⟨C,hC,hTC,hCC⟩ := containers (ok:=O)
    (compact_isLaw.inter_right (closed_pairCaps _ _ _)) (fun _ h => h.1)
    (fun _ h _ g => ⟨mid_isLaw h.1 g.1, mid_pairCaps h.2 g.2⟩)
    H.conflict hε R (fun w hw g => hsat w hw.1 hw.2 (by simpa [carried,R] using g))
    L (fun w hw _ => by
      have h := log_card_le_negEnt hw.1
      linarith)
  have hx (r : C) :
      ∃ (S : A → Prop) (E : A × A → Prop), M* pr μ S < 2 ∧
        D * pr (pairW μ μ) E < 1 ∧ ∀ x : A × A, x ∈ r.val → S x.1 ∨ S x.2 ∨ E x :=
    terminal hμ.nz hM hD _ (fun ⟨w,h,g,k⟩ => (hTC _ r.property).2 ⟨w,⟨h,g⟩,k⟩)
  choose S E hs hq hcover using hx
  let P (r : C) (x : Fin m → A) := badS (S r) k x ∨ badE (E r) k x
  let W := prodW (fun _ : Fin m => μ)
  have hw : IsLaw W := prodW_law fun _ => hμ
  let b := (2:ℝ)^m * (2/M)^k + (m:ℝ)^(k+k) * D⁻¹^k
  have hp (r : C) : pr W (P r) ≤ b := by
    have h₁ := badS_pr hμ (S r) k m
    have h₂ := badE_pr hμ (E r) k m
    refine (pr_or_le hw.nz).trans ((add_le_add h₁ h₂).trans ?_)
    have hi : 0 ≤ pr μ (S r) := pr_nonneg hμ.nz
    have hj : 0 ≤ pr (pairW μ μ) (E r) := pr_nonneg (pairW_law hμ hμ).nz
    have hk : pr μ (S r) ≤ 2/M := (le_div_iff₀ hM).mpr (by linarith only [hs r])
    have hn : pr (pairW μ μ) (E r) ≤ D⁻¹ := by
      rw [← one_div]
      apply (le_div_iff₀ hD).mpr
      linarith only [hq r]
    unfold b; gcongr
  have hf : pr W (fun x => ∃ r, P r x) < 1 := by
    have h : pr W (fun x => ∃ r, P r x) ≤ (C.card : ℝ) * b := by
      refine (pr_exists_le hw.nz P).trans ((sum_le_sum (fun i _ => hp i)).trans_eq ?_)
      simp
    apply lt_of_le_of_lt h
    apply lt_of_le_of_lt _ herr
    have hg : C.card ≤ (Fintype.card (A × A) + 1)^L :=
      hC.trans (by gcongr; exact card_le_univ _)
    have hb : 0 ≤ b := by unfold b; positivity
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hg) hb
  have hg : 0 < pr W (fun x => ¬∃ r, P r x) := by rw [pr_not, hw.total]; linarith only [hf]
  obtain ⟨x,hx,_⟩ := exists_of_pr_pos hw.nz hg
  refine ⟨x, H.indepNum_graph_le _,?_⟩
  let t := connectedMatchingNumber (H.graph x)
  by_contra! hn
  obtain ⟨e,he,he₁,he₂⟩ := H.matching_pairs x
  let f (i : Fin t) : A × A := (x (e (.inl i)), x (e (.inr i)))
  let I := univ.image f
  have hIR : I ⊆ R := by
    intro y hy; obtain ⟨i,_,rfl⟩ := mem_image.mp hy
    exact mem_filter.mpr ⟨mem_univ _, he₁ i⟩
  have hI (v) (hv : v ∈ I) (w) (hw : w ∈ I) : ¬ H.conflict v w := by
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    obtain ⟨j,_,rfl⟩ := mem_image.mp hw
    exact he₂ i j
  obtain ⟨r,hr,g⟩ := hCC I hIR hI
  have ht : m ≤ t * 100 := by
    change (m:ℚ)/100 ≤ (t:ℚ) at hn
    have h : (m:ℚ) ≤ (t:ℚ)*100 := by linarith
    exact_mod_cast h
  apply hx
  let r' : C := ⟨r,hr⟩
  refine ⟨r', many_bad (S r') (E r') (by omega) he fun i =>
    hcover r' (f i) (g (mem_image_of_mem f (mem_univ i)))⟩
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ExponentialGraphTransfer
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential Graph Transfer -/

noncomputable section
namespace HadwigerCounterexample
open HadwigerMatching Real Filter

theorem cast_ord (g N : ℕ) : ((ord g N : ℕ):ℝ) = bp (1000*g*N) := by
  unfold ord
  have h := bp_nat (1000*g*N)
  push_cast at *
  exact h.symm

theorem tendsto_ord {g : ℕ} (hg : 0 < g) : Tendsto (ord g) atTop atTop := by
  have hl : Tendsto (fun n : ℕ => bp (1000*g*n)) atTop atTop :=
    (bp_tendsto (show (0:ℝ)<1000*g by positivity)).comp tendsto_natCast_atTop_atTop
  rw [tendsto_atTop]
  intro b
  filter_upwards [hl.eventually (eventually_ge_atTop (b:ℝ))] with i hi
  change _ ≤ bp _ at hi
  rw [← cast_ord] at hi
  exact_mod_cast hi

/-- Raw supersaturation ⇒ existence for the sampled order. Takes any fixed
polynomial bit-count bound of degree two for the raw unit space. In particular
the eventual N-bound is independent of every law and graph. -/
theorem transfer_scales {g : ℕ} (hg : 0 < g) {B : ℝ} (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Type) [Fintype A] [Nonempty A]
      (H : Holes A) (μ : Wgt A), IsLaw μ →
      (Fintype.card (A × A) : ℝ) ≤ bp (B * (N:ℝ)^2) →
      (∀ w : Wgt (A × A), IsLaw w → pairCaps μ (bp 1000) (bp (4000*g*N)) w →
        carried w H.unit → bp (-100*g*N) ≤ pr (pairW w w) (fun x => H.conflict x.1 x.2)) →
      ∃ x : Fin (ord g N) → A,
        (H.graph x).indepNum ≤ 2 ∧
        (connectedMatchingNumber (H.graph x) : ℚ) < (ord g N : ℚ)/100 := by
  have hg' : (1:ℝ) ≤ g := by exact_mod_cast hg
  have hh := bp_poly_dom_nat (a:=100*g) (by positivity) (B+1) 2
  filter_upwards [hh, eventually_ge_atTop 1,
    (tendsto_ord hg).eventually (eventually_ge_atTop 2)] with N hN hN' hord
  intro A _ _ H μ hμ hA hs
  let y : ℝ := g * (N:ℝ)
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN'
  have hy : 1 ≤ y := by unfold y; nlinarith
  let m := ord g N
  let L : ℕ := 2^(200*g*N)
  have hm : (m:ℝ) = bp (1000*y) := by rw [cast_ord]; unfold y; ring_nf
  have hl : (L:ℝ) = bp (200*y) := by
    have h := (bp_nat (200*g*N)).symm
    push_cast at h
    dsimp only [L]
    push_cast
    unfold y
    rwa [← mul_assoc]
  let z : ℝ := B*(N:ℝ)^2
  have hz : 0 ≤ z := by unfold z; positivity
  have hb : z + 1 < bp (100*y) := by
    have hh : (B+1)*(N:ℝ)^2 < bp (100*y) := by simpa only [y, mul_assoc] using hN
    unfold z
    nlinarith only [hh,hNr]
  let k := (m+199)/200
  refine transfer H hμ (bp_pos _) (bp_pos _) (bp_pos _) hs (L:=L) (k:=k) ?_ ?_ ?_
  · have hi : log (Fintype.card (A × A) : ℝ) ≤ z * Real.log 2 := by
      rw [← log_bp]
      exact Real.log_le_log (by exact_mod_cast Fintype.card_pos) hA
    apply lt_of_le_of_lt hi
    calc z * log 2 < bp (100*y)*log 2 :=
           mul_lt_mul_of_pos_right (by linarith only [hb]) (Real.log_pos (by norm_num))
         _ = _ := by
           rw [hl,← mul_assoc (bp (200 * y)),← bp_add]
           unfold y; ring_nf
  · change 200*((m+199)/200) < m+200
    omega
  · have hk : (m:ℝ) ≤ 200*k := by
      have hk : m ≤ 200*k := by unfold k; omega
      exact_mod_cast hk
    have hm' : (2:ℝ) ≤ m := by exact_mod_cast hord
    let a := (Fintype.card (A × A):ℝ)+1
    have ha : a ≤ bp (z+1) := by
      rw [bp_add,bp_one]
      have hx : 1 ≤ bp z := by simpa only [bp_zero] using bp_le hz
      change _ ≤ bp z at hA
      dsimp only [a]
      linarith only [hx,hA]
    have hal : a^L ≤ bp (m:ℝ) := calc
      a^L ≤ bp (z+1)^L := by
        have hp : 0 ≤ a := by dsimp [a] <;> positivity
        gcongr
      _ = bp ((z+1)*L) := (bp_mul_nat _ _).symm
      _ ≤ bp (m:ℝ) := bp_le (by
        rw [hm,hl]
        calc (z+1)*bp (200*y) ≤ bp (100*y)*bp (200*y) :=
               mul_le_mul_of_nonneg_right hb.le (bp_pos _).le
             _ ≤ bp (1000*y) := by rw [← bp_add]; apply bp_le; linarith only [hy])
    let d := bp (4000*(g:ℝ)*(N:ℝ))
    have ha1 : bp (m:ℝ) * ((2:ℝ)^m * (2/bp 1000)^k) ≤ bp (-(m:ℝ)) := by
      rw [← bp_nat, show 2/bp 1000 = bp (1-1000) by simp only [bp_sub,bp_one],
        ← bp_mul_nat, ← bp_add, ← bp_add]
      apply bp_le
      linarith
    have ha2 : bp (m:ℝ) * ((m:ℝ)^(k+k) * (d⁻¹)^k) ≤ bp (-(m:ℝ)) := by

      have he : (m:ℝ)^(k+k) = bp ((1000*y)*(k+k:ℕ)) := by
        rw [hm,bp_mul_nat]
      rw [he, show d⁻¹ = bp (-(4000*y)) by simp only [bp_neg,d,y,mul_assoc],
        ← bp_mul_nat, ← bp_add, ← bp_add]
      apply bp_le
      push_cast
      have hx : (k:ℝ) ≤ y*k := by
        have : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
        nlinarith
      linarith
    have hx : bp (-(m:ℝ)) < 1/2 := by
      rw [show (1:ℝ)/2 = bp (-1) by simp only [one_div,bp_neg,bp_one]]
      exact bp_lt (by linarith only [hm'])
    change a^L * (2^m * (2/bp 1000)^k + (m:ℝ)^(k+k) * d⁻¹^k) < 1
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right hal (by
      have h := bp_pos 1000
      have h' : 0 < d := bp_pos _
      positivity)) ?_
    linarith only [ha1,ha2,hx]

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
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_InitialPartitionExistence
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Initial Partition Existence -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset
open scoped BigOperators Topology
namespace PreparationParameters

variable {p : Shape} {n N M : ℕ} {q : PreparationParameters}

theorem born (w : Wgt (UnitType p n N)) (hw : IsLaw w) (m : Mixer p n)
    (h : pairCaps (raw m N) q.L (bp ((q.D:ℝ)*N)) w) :
    nascent q p N w m := by
  refine ⟨hw,fun i x=>?_, h.2.2⟩
  cases i
  · exact h.2.1 _
  exact h.1 _

end PreparationParameters
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RandomBinaryMixing
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Random Binary Mixing -/

noncomputable section
namespace HadwigerCounterexample

open Filter Matrix Function
open scoped BigOperators Topology

variable {p : Shape} {n : ℕ}

theorem rank_fifth_bound (m n : ℕ) (hm : n/2 ≤ m) (hn : 100 ≤ n) :
    pr unif (fun M : Mat (Fin m) (Fin m) => 5*M.rank<n) ≤ bp (- (n:ℝ)) := by
  apply le_trans (pr_mono unif_law.nz (q:=fun M => M.rank≤ n/5) (fun M h => by omega))
  refine (pr_matrix_rank _).trans ?_
  apply bp_le
  simp only [num,Fintype.card_fin]
  let r := n/5
  have h1 : 5*r≤n := by unfold r; omega
  have h2 : n≤2*m+1 := by omega
  have h3 : 45 ≤ m := by omega
  have hi : (m+m)*r+n ≤ m*m := by
    nlinarith only [h1,h2,h3,
      Nat.mul_le_mul_left m h1,Nat.mul_le_mul_left m h2,Nat.mul_le_mul_left m h3]
  have hh : ((m:ℝ)+m)*r+n ≤ m*(m:ℝ) := by exact_mod_cast hi
  unfold r at hh; linarith only [hh]

theorem pr_surj_rank {m} (hn : 100≤n) (hm : n/2 ≤ m)
    (A : Draw p n →ₗ[F] Mat (Fin m) (Fin m))
    (h : Function.Surjective A) :
    pr unif (fun x => 5*(A x).rank < n) ≤ bp (- (n:ℝ)) := by
  classical
  have he := mapW_pr unif A (fun x => 5*x.rank<n)
  rw [map_unif_surjective A h] at he
  exact he.symm.le.trans (rank_fifth_bound m n hm hn)

theorem ztest_prob (p : Shape) (s t : Label p.b) (hj : 1≤p.j)
    (c : Vec (MBits p)) (b : Vec Bool) (hn : 100≤n) :
    pr unif (fun x : Draw p n => s ≠ t ∧ c≠0 ∧
      5*blockRank Block.Z s t (indexedSum (drawn x) c+selfSum (drawn x) b)<n)
      ≤ bp (- (n:ℝ)) := by
  classical
  by_cases h : s≠t ∧ c≠0
  · simp only [← and_assoc (a:=s≠t),blockRank,map_add,obsZ_self,add_zero]
    refine le_trans (pr_mono unif_law.nz ?_) (pr_surj_rank hn (by omega) (obsZ p n s t c) (obsZ_surj _ _ hj h.1 h.2))
    exact fun x hx => hx.2
  simp_rw [← and_assoc (a:=s≠t),h,false_and,pr_false]
  exact (bp_pos _).le

theorem stest_prob (p : Shape) (s t : Label p.b) (hj : 1≤p.j)
    (b : Vec Bool) (hn : 100≤n) :
    pr unif (fun x : Draw p n => s ≠ t ∧ b≠0 ∧
      5*blockRank Block.sharp s t (selfSum (drawn x) b)<n)
      ≤ bp (- (n:ℝ)) := by
  classical
  by_cases h : s≠t ∧ b≠0
  · simp only [← and_assoc (a:=s≠t),blockRank,pull_selfPart _ _ hj]
    let l := Fin.castLE (show n/2≤n by omega)
    let r (i : Fin (n/2)) : Fin n := ⟨n/2+i.val,by have := i.isLt; omega⟩
    have he : Function.Surjective (obsHalf p s t b n l r) := by
      refine obsHalf_surj _ _ h.1 h.2 _ (Fin.castLE_injective _) (fun i j h => ?_) ?_
      · exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))
      intro i j h
      have he : i.val = n/2+j.val := congrArg Fin.val h
      have hg := i.isLt; omega
    apply le_trans _ (pr_surj_rank hn (by omega) (obsHalf p s t b n l r) he)
    refine pr_mono unif_law.nz fun x hx => lt_of_le_of_lt ?_ hx.2
    exact Nat.mul_le_mul_left _ ((selfPartial (p:=p) s t b x).rank_submatrix_le l r)
  simp_rw [← and_assoc (a:=s≠t),h,false_and,pr_false]
  exact (bp_pos _).le

theorem binary_likely (p : Shape) (hj : 1≤p.j) :
    ∀ᶠ n : ℕ in atTop,
      pr unif (fun x : Draw p n => ¬binaryGood (drawn x)) < 1/4 := by
  classical
  let I := Label p.b × Label p.b × Vec (MBits p) × Vec Bool
  let J := Label p.b × Label p.b × Vec Bool
  let T := I⊕J
  let m := num T
  have h : Tendsto (fun n:ℕ=>m*bp (- (n:ℝ))) atTop (𝓝 0) := by
    have h : Tendsto (fun n:ℕ=>bp (-(1:ℝ)*(n:ℝ))) atTop (𝓝 0) :=
      (bp_tendsto_zero zero_lt_one).comp tendsto_natCast_atTop_atTop
    simpa using h.const_mul m
  filter_upwards [h.eventually (gt_mem_nhds (show (0:ℝ)<1/4 by norm_num)),
    eventually_ge_atTop 100] with n hn hg
  let bad (i : T) (x : Draw p n) :=
    match i with
    | .inl (s,t,c,b) => s≠t ∧ c≠0 ∧ 5*blockRank Block.Z s t
        (indexedSum (drawn x) c+selfSum (drawn x) b)<n
    | .inr (s,t,b) => s≠t ∧ b≠0 ∧ 5*blockRank Block.sharp s t (selfSum (drawn x) b)<n
  have he (i : T) : pr unif (bad i) ≤ bp (- (n:ℝ)) := by
    rcases i with ⟨s,t,c,b⟩|⟨s,t,b⟩
    · exact ztest_prob _ _ _ hj _ _ hg
    exact stest_prob _ _ _ hj _ hg
  have hi : pr unif (fun x => ∃ i, bad i x) ≤ m*bp (- (n:ℝ)) :=
    (pr_exists_le unif_law.nz bad).trans ((Finset.sum_le_sum (fun i _ => he i)).trans_eq (by
      rw [Finset.sum_const, Finset.card_univ,nsmul_eq_mul]))
  apply lt_of_le_of_lt (le_trans (pr_mono unif_law.nz ?_) hi) hn
  intro x hx
  by_contra! H
  apply hx
  intro s t hst
  constructor
  · intro c b hc
    exact le_of_not_gt fun e => H (Sum.inl (s,t,c,b)) ⟨hst,hc,e⟩
  intro b hb
  exact le_of_not_gt fun e => H (Sum.inr (s,t,b)) ⟨hst,hb,e⟩
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MixerProductVariables
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mixer Product Variables -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix
variable {p : Shape} {n : ℕ} {r : Comp p.g → ℕ}

theorem qmix_eq (P Q : Parts p n r) (l : Tag p.g) (d : Draw p n) {x : Profile p n}
    (hx : ∀ e, x e=P e*(Q e)ᵀ) :
    qmix (drawn d) x l=formCol P l d.1 * (formCol Q l d.2.1)ᵀ := by
  classical
  have h (j : Fin p.J) (f : TagStar l) (e) (L R : Moment p n) :
      liftM L R (x e) = L*P e * (R*Q e)ᵀ := by
    rw [liftM_def,hx]
    simp only [Matrix.mul_assoc,transpose_mul]
  ext i k
  let A := formCol P l d.1
  let B := formCol Q l d.2.1
  change _ = ∑ t : Terms p l r, A i t*B k t
  unfold qmix
  simp_rw [Matrix.sum_apply, Fintype.sum_prod_type, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl
    fun e _ => ?_
  simp_rw [Matrix.add_apply,h j f]
  let a := (drawn d).mixL j e f.val
  let b := (drawn d).mixR j e f.val
  let a' := (drawn d).mixL j f.val e
  let b' := (drawn d).mixR j f.val e
  change (∑ t, (aᵀ * P e) i t * (bᵀ * Q e) k t)+
    (∑ t, (a' * P e) i t * (b' * Q e) k t) = _
  rw [←Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun t _ => ?_
  rw [Fintype.sum_bool]; rfl

variable {U : Type}

variable [Fintype U]

/-- Well away from the profile factors all the formal variables from a given
side can be specified independently. -/
theorem formCol_onto (P : Parts p n r) (l : Tag p.g) (W : Mat (Row p n) U)
    (hw : Function.Injective W.mulVec)
    (hP : ∀ i, Function.Injective (P i).mulVec)
    (h : ∀ i, Disjoint (colSp (P i)) (colSp W))
    (A : Mat U (Terms p l r)) :
    ∃ d : MArr p n, Wᵀ * formCol P l d=A := by
  classical
  let tgt (b : Bool) (j : Fin p.J) (e f : Comp p.g) :
      Mat (Fin (r e)) U :=
    if h : inc f l then Matrix.of (fun k i => A i (j,⟨f,h⟩,⟨e,k⟩,b)) else 0
  have ho (j : Fin p.J) (e f : Comp p.g) :
      ∃ L : Moment p n, (P e)ᵀ * L * W=tgt true j e f ∧
                         (P f)ᵀ * Lᵀ * W=tgt false j f e :=
    prescribe_opposite (inj_fromCols (hP _) hw (h e)) (inj_fromCols hw (hP _) (h f).symm) _ _
  choose D hD hd using ho
  let d : MArr p n := fun ⟨j,e,f⟩ => D j e f
  refine ⟨d,?_⟩
  ext i j
  rcases j with ⟨j,f,⟨e,k⟩,_|_⟩
  · have he : Wᵀ * (D j f e * P e)=(tgt false j e f.val)ᵀ := by
      rw [← hd]; simp only [transpose_mul,transpose_transpose]
    change ∑ q, Wᵀ i q * formCol P l d q (j,f,⟨e,k⟩,false) = _
    simp only [formCol_false]
    change (Wᵀ*(D j f e * P e)) i k=_
    rw [he]; simp [tgt,f.property]
  · have he : Wᵀ*((D j e f)ᵀ*P e)=(tgt true j e f.val)ᵀ := by
      rw [← hD]; simp only [transpose_mul,transpose_transpose]
    change ∑ q, Wᵀ i q * formCol P l d q (j,f,⟨e,k⟩,true) = _
    simp only [formCol_true]
    change (Wᵀ*((D j e f)ᵀ*P e)) i k=_
    rw [he]; simp [tgt,f.property]

theorem stack_surj (P Q : Parts p n r) (l : Tag p.g) (W : Mat (Row p n) U)
    (hw : Function.Injective W.mulVec)
    (hP : ∀ i, Function.Injective (P i).mulVec) (hQ : ∀ i, Function.Injective (Q i).mulVec)
    (h1 : ∀ i, Disjoint (colSp (P i)) (colSp W))
    (h2 : ∀ i, Disjoint (colSp (Q i)) (colSp W)) :
    Function.Surjective (stackL P Q l W) := by
  intro A
  obtain ⟨d,hd⟩ := formCol_onto P l W hw hP h1 A.toCols₁
  obtain ⟨f,hf⟩ := formCol_onto Q l W hw hQ h2 A.toCols₂
  refine ⟨(d,f,0),?_⟩
  change Wᵀ * fromCols (formCol P l d) (formCol Q l f)=_
  rw [mul_fromCols,hd,hf,fromCols_toCols]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PolarRankBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polar Rank Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators

variable {I J U : Type} [Fintype I] [Fintype J]

theorem swapM_rank [DecidableEq I] :
    (swapM I).rank = Fintype.card (I⊕I) := by
  have h : swapM I * swapM I = 1 := by simp [swapM, fromBlocks_multiply]
  apply mrk_inj.mp
  intro x y hxy
  have he (x) : swapM I *ᵥ (swapM I *ᵥ x)=x := by rw [mulVec_mulVec, h, Matrix.one_mulVec]
  change swapM I*ᵥx=swapM I*ᵥy at hxy
  rw [← he x,hxy,he]

theorem alt_of_forms [Fintype U] [DecidableEq J] (P Q : Mat I J) (W : Mat I U) :
    pullM W W (P*Qᵀ + (P*Qᵀ)ᵀ) =
      liftM (Wᵀ * fromCols P Q) (Wᵀ * fromCols P Q) (swapM J) := by
  have hh : P*Qᵀ+(P*Qᵀ)ᵀ = liftM (fromCols P Q) (fromCols P Q) (swapM J) := by
    simp only [liftM_def,swapM,fromCols_mul_fromBlocks,
      Matrix.mul_one,Matrix.mul_zero,add_zero,transpose_fromCols,
      fromCols_mul_fromRows, transpose_mul,transpose_transpose,add_comm]
  rw [hh]
  apply liftM_comp

variable {p : Shape} {n : ℕ}

theorem flarge {r : Comp p.g→ℕ} (P Q : Parts p n r) :
    ∃ S : Space (Ray p n), (∀ i,colSp (P i) ≤ S ∧ colSp (Q i) ≤ S) ∧
      dim S ≤ 2*(∑ i, r i) := by
  classical
  have he (J : Finset (Comp p.g)) :
      ∃ S : Space (Ray p n), (∀ i∈J,colSp (P i) ≤ S ∧ colSp (Q i) ≤ S) ∧
        dim S ≤ 2*∑ i∈J,r i := by
    induction J using Finset.induction with
    | empty => exact ⟨⊥,fun _ h => (Finset.notMem_empty _ h).elim,
        (finrank_bot _ _).le.trans (Nat.zero_le _)⟩
    | insert i J hi ih =>
      obtain ⟨S,hS,h⟩ := ih
      let T := colSp (P i) ⊔ colSp (Q i)
      refine ⟨S⊔T,fun j hj => ?_, ?_⟩
      · rcases Finset.mem_insert.mp hj with rfl|hj
        · exact ⟨le_trans (show colSp _ ≤ T from le_sup_left) le_sup_right,
            le_trans (show colSp _ ≤ T from le_sup_right) le_sup_right⟩
        · exact ⟨(hS j hj).1.trans le_sup_left,(hS j hj).2.trans le_sup_left⟩
      have hh : dim T ≤ 2*r i := by
        have hp (P : Parts p n r) : dim (colSp (P i)) ≤ r i := by
          rw [colSp_dim]
          exact (Matrix.rank_le_card_width (P i)).trans_eq (Fintype.card_fin _)
        rw [two_mul]
        exact (Submodule.finrank_add_le_finrank_add_finrank ..).trans (Nat.add_le_add (hp _) (hp _))
      rw [Finset.sum_insert hi]
      apply le_trans (Submodule.finrank_add_le_finrank_add_finrank ..)
      exact (Nat.add_le_add h hh).trans (by omega)
  obtain ⟨S,h,g⟩ := he Finset.univ
  exact ⟨S,fun i => h _ (Finset.mem_univ i),g⟩

theorem urBad_cap (K s0 : ℕ) (hg : 2≤p.g) (hj : s0≤p.J)
    (x : Profile p n) (l : Tag p.g) (s : Label p.b) :
    pr unif (urBad K s0 x l s) ≤
      bp (((prodBound p K : ℝ)+2*K-n)*(s0+1)) := by
  classical
  by_cases h : totalRank x≤K ∧ totalRank x>0
  swap
  · rw [show urBad K s0 x l s = fun _ => False by
      funext d; exact propext ⟨fun g => h ⟨g.1,g.2.1⟩,False.elim⟩,pr_false]
    exact (bp_pos _).le
  let R := blockRay p n s Block.Z
  let r i := (x i).rank
  obtain ⟨P,Q,h1,h2,h3⟩ :
      ∃ (P Q : Parts p n r), (∀ i,Function.Injective (P i).mulVec) ∧
        (∀ i,Function.Injective (Q i).mulVec) ∧ (∀ i,x i=P i*(Q i)ᵀ) := by
    choose A B h1 h2 h3 using fun i => rank_product (x i)
    refine ⟨A,fun i => (B i)ᵀ,h1,fun i => ?_,fun i => (h3 i).symm⟩
    rw [← transpose_surj_iff]; exact h2 i
  obtain ⟨S,hS,hrS⟩ := flarge P Q
  obtain ⟨T,hT,hv⟩ := choose_free (blockRay_inj p n s Block.Z) S
  let W := R*pack T
  let V := (Terms p l r)
  let A := stackL P Q l W
  have hb : Function.Surjective A := by
    apply stack_surj _ _ _ _
      (inj_comp_mat _ _ (blockRay_inj p n s Block.Z) (pack_inj T)) h1 h2
    · exact fun i => hv.mono_left (hS i).1
    exact fun i => hv.mono_left (hS i).2
  have hc : Fintype.card (V⊕V)=prodBound p (totalRank x) := by
    simp only [Fintype.card_sum,Terms,Fintype.card_prod,
      Fintype.card_fin,Fintype.card_sigma,V,Fintype.card_bool,card_star]
    unfold prodBound totalRank r; ring
  have hcard : 2*p.J ≤ Fintype.card (V⊕V) := by
    have he : 1 ≤ p.g-1 := by omega
    have hx : 1 ≤ totalRank x := h.2
    rw [hc]; unfold prodBound
    nlinarith only [Nat.mul_le_mul_left (p.J*(p.g-1)) hx,
      Nat.mul_le_mul_left p.J he, Nat.zero_le p.J]
  let Y (M : Mat (Fin (dim T)) (V ⊕ V)) :=
    M.rank+(s0+1) ≤ Fintype.card (V⊕V)
  have he (d) (hh : urBad K s0 x l s d) : Y (A d) := by
    let B := qmix (drawn d) x l + (qmix (drawn d) x l)ᵀ
    have hineq := rank_ge_congr (swapM V) (A d)
    have hx : pullM W W B=liftM (A d) (A d) (swapM V) := by
      dsimp only [B]
      rw [qmix_eq P Q l d h3]
      exact alt_of_forms _ _ W
    rw [← hx, swapM_rank] at hineq
    have hp : (pullM W W B).rank ≤ (pullM R R B).rank := by
      calc _ = (pullM (pack T) (pack T) (pullM R R B)).rank := by
                 unfold W pullM
                 rw [liftM_comp, Matrix.transpose_mul]
           _ ≤ _ := rank_lift_le _ _ _
    have hh1 : (pullM R R B).rank < 2*(p.J-s0) := hh.2.2
    change _+_ ≤ _
    omega
  have hpr := pr_mono (w:=unif) unif_subLaw.nz he
  change pr unif (urBad K s0 x l s) ≤ pr unif (fun d => Y (A d)) at hpr
  rw [← mapW_pr unif A Y,map_unif_surjective _ hb] at hpr
  apply le_trans (hpr.trans (pr_deficient _))
  apply bp_le
  have hp : num (V ⊕ V) ≤ prodBound p K := by
    have he : Fintype.card (V⊕V) ≤ prodBound p K := by rw [hc]; unfold prodBound; gcongr; exact h.1
    exact_mod_cast he
  have hx : n ≤ num (Fin (dim T)) + 2*(K:ℝ) := by
    rw [Fintype.card_fin] at hT
    have he : n ≤ Fintype.card (Fin (dim T)) + 2*K := by
      rw [Fintype.card_fin]
      exact hT.trans (Nat.add_le_add_left (hrS.trans (Nat.mul_le_mul_left _ h.1)) _)
    exact_mod_cast he
  push_cast; apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith only [hp,hx]
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MixerExistence
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.mem_fieldRad _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_abs _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mixer Existence -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Filter
open scoped BigOperators Topology

theorem polar_likely (p : Shape) (K s0 : ℕ) (hA : profileA p K ≤ s0)
    (hg : 2≤p.g) (hj : s0≤p.J) :
    ∀ᶠ n : ℕ in atTop,
      pr unif (fun x : Draw p n => ¬unaryGood (drawn x) K s0)<1/4 := by
  classical
  let A := profileA p K
  let U := Tag p.g × Label p.b
  let c : ℝ := (prodBound p K+2*K:ℕ)
  let b := num U * bp (c*(s0+1))
  have h : Tendsto (fun n:ℕ => b*bp (-(n:ℝ))) atTop (𝓝 0) := by
    have h : Tendsto (fun n:ℕ=>bp (-(1:ℝ)*(n:ℝ))) atTop (𝓝 0) :=
      (bp_tendsto_zero zero_lt_one).comp tendsto_natCast_atTop_atTop
    simpa using h.const_mul b
  filter_upwards [h.eventually (gt_mem_nhds (show (0:ℝ)<1/4 by norm_num)),profile_count p K]
    with n hn hP
  let T := {x : Profile p n // totalRank x≤K}
  let bad (i : T × U) (d : Draw p n) := urBad K s0 i.1.val i.2.1 i.2.2 d
  apply lt_of_le_of_lt (le_trans (pr_mono unif_law.nz ?_) (pr_exists_le _ bad))
  show (∑ i,pr unif (bad i)) < 1/4
  · have hi i : pr unif (bad i) ≤ bp ((c-n)*(s0+1)) := by
      have hi := urBad_cap K s0 hg hj (i: T × U).1.val i.2.1 i.2.2
      unfold c; push_cast; exact hi
    apply lt_of_le_of_lt (Finset.sum_le_sum (s:=Finset.univ) fun i _ => hi i)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    apply lt_of_le_of_lt _ hn
    change _ ≤ b * bp _
    have hpc : num T ≤ bp (A*n) := by rw [nbr_eq_card] at hP; exact hP
    rw [Fintype.card_prod,Nat.cast_mul]
    change num T * num U * _ ≤ _
    have hh : (A:ℝ)*n - (s0+1:ℝ)*n ≤ -(n:ℝ) := by
      have hx : (A:ℝ) ≤ s0 := by exact_mod_cast hA
      have hd := mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg n : (0:ℝ) ≤ n)
      linarith only [hd]
    have hnum : (0:ℝ) ≤ num U := Nat.cast_nonneg _
    calc num T * num U * bp ((c-n)*(s0+1))
      _ ≤ bp (A*n) * num U * bp ((c-n)*(s0+1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpc hnum) (bp_pos _).le
      _ = b * bp ((A:ℝ)*n - (s0+1:ℝ)*n) := by
        dsimp only [b]
        rw [mul_comm _ (num U),mul_assoc, ← bp_add, mul_assoc, ← bp_add]; ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left (bp_le hh) (mul_nonneg hnum (bp_pos _).le)
  · intro x hx
    unfold unaryGood at hx
    push Not at hx
    obtain ⟨i,l,s,h1,h2,h3⟩ := hx
    exact ⟨(⟨i,h1⟩,l,s),h1,h2,h3⟩
  · exact unif_law.nz;

theorem goodMixers (p : Shape) (K s0 : ℕ) (hg : 2≤p.g)
    (hj : 1≤p.j) (h0 : profileA p K ≤ s0) (hJ : s0≤p.J) :
    ∀ᶠ n : ℕ in atTop,
      ∃ m : Mixer p n, unaryGood m K s0 ∧ binaryGood m := by
  classical
  filter_upwards [polar_likely p _ _ h0 hg hJ, binary_likely p hj] with n hn hm
  let q (x : Draw p n) := ¬ unaryGood (drawn x) K s0
  let r (x : Draw p n) := ¬ binaryGood (drawn x)
  have hh : 0<pr unif (fun x => ¬ (q x ∨ r x)) := by
    rw [pr_not,unif_law.total]
    have h := pr_or_le (w:=unif) (p:=q) (q:=r) unif_law.nz
    change pr unif q<_ at hn; change pr unif r<_ at hm
    linarith only [hn,hm,h]
  obtain ⟨x,hx,_⟩ := exists_of_pr_pos unif_law.nz hh
  unfold q r at hx
  exact ⟨drawn (p:=p) x, Classical.not_not.mp (fun h => hx (Or.inl h)), Classical.not_not.mp (fun h => hx (Or.inr h))⟩
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Counterexamples to Hadwiger's conjecture

The binary frame construction yields arbitrarily large graphs with independence
number at most two and small touching matchings. The matching–minor inequality
then separates their complete-minor order from their ordinary chromatic number.

This formalizes the construction theorem and the ordinary chromatic consequence
in OpenAI, *A counterexample to Hadwiger's conjecture* (September 23, 2026).
-/

noncomputable section
namespace HadwigerCounterexample
open Matrix Filter Finset
open scoped BigOperators Topology

variable {p:Shape} {n N M s0 :ℕ} {b: PreparationParameters}
open PreparationParameters

open HadwigerMatching

/-- Arbitrarily large finite graphs of independence number at most two and
touching-matching number less than one hundredth of the number of vertices. -/
theorem exists_graphs_oai (M : ℕ) : ∃ m:ℕ, max M 5 ≤ m ∧
    ∃ G : SimpleGraph (Fin m), G.indepNum ≤ 2 ∧
      (connectedMatchingNumber G:ℚ) < (m:ℚ)/100 := by
  classical
  obtain ⟨p,b,k,r,h,hg,hd,he⟩:= exists_parameters
  have ht:=h.enter.first
  let B:=4*num (Comp p.g)
  let Y (n:ℕ):=k*n
  have hy := (trend_sizes atTop le_rfl ht.hM).1
  have hp : 0 < p.g := lt_of_lt_of_le (by norm_num) ht.hG
  have hs : ∀ᶠ n:ℕ in atTop, ∃ m:ℕ, max M 5 ≤ m ∧
      ∃ G : SimpleGraph (Fin m), G.indepNum ≤ 2 ∧ (connectedMatchingNumber G:ℚ)<(m:ℚ)/100 := by
    filter_upwards [eventual_conflict_lower_bound h,ht.wrap,goodMixers p b.pins r (by linarith only [ht.hG])
      ht.hJ (by have hi:=h.profiles; omega) h.bigJ,hy.eventually
      (transfer_scales hp (show 0≤B from mul_nonneg (by norm_num) (Nat.cast_nonneg _))),
      ((tendsto_ord hp).comp hy).eventually (eventually_ge_atTop (max M 5))] with n hn ht hl hq hN
    let N:=Y n
    obtain ⟨m,hm,he'⟩:=hl
    have hT:= hn m hm he'; have hV:2*num (Full p n)<(N:ℝ):=ht.1
    have hC : num (UnitType p n N)≤bp (B*N^ (2:ℕ)) := by
      rw [unit_size]; apply bp_le
      have hf : num (Full p n) ≤ N := by linarith only [hV,(Nat.cast_nonneg N : 0≤(N:ℝ))]
      unfold B
      calc _ ≤ num (Comp p.g)*4*(N:ℝ)*N := mul_le_mul_of_nonneg_left hf (by unfold num; positivity)
           _ = _ := by ring
    obtain ⟨x,hx,hX⟩:=hq (Orient p n N) (rawHoles m) (raw m N) (raw_law m hV) hC (by
      intro w hw hC hU
      apply hT w _ hU
      apply born w hw m
      rw [hd,he]; simpa only [N,Y,Nat.cast_mul,Nat.cast_ofNat] using hC)
    exact ⟨ord p.g N,hN,(rawHoles m).graph x,hx,hX⟩
  obtain ⟨n,hn⟩:=hs.exists; exact hn

end HadwigerCounterexample

end

end OAI
end

theorem solution : type_of% @OAI.HadwigerCounterexample.exists_graphs_oai := @OAI.HadwigerCounterexample.exists_graphs_oai
