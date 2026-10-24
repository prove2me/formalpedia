-- Prove2me | solution 1 for OAI.ExactFourier.finite_win
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T22:09:26.072991+00:00
-- url     : https://prove2.me/submissions/e4d2ecec-8f3e-4570-8ba6-92b28aeb2a7e

import Mathlib
import Definitions.Def_OAIQWEXF000
import Theorems.Thm_OAI_ExactFourier_GraphReflection_lower_bound_blocks
import Theorems.Thm_OAI_ExactFourier_MatrixPrice_scalar_pivot
import Theorems.Thm_OAI_ExactFourier_SparseReflection_exists_reflection_nnz

section
-- module Solutions.OAIQW_ExactFourier.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.PortMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe fourierU1 fourierU2

section
namespace ExactFourier
open scoped Kronecker

namespace Reindexed

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem mul (e : ι ≃ κ) (A B : Matrix ι ι ℂ) :
    Matrix.reindex e e (A * B) = Matrix.reindex e e A * Matrix.reindex e e B :=
  (Matrix.reindexAlgEquiv ℂ ℂ e).map_mul A B

end Reindexed

end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.PivotAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier.Pivot
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem solve (A : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (hD : IsUnit D) :
    matrix A C B D*Matrix.fromBlocks (1 : Matrix α α ℂ) 0 B D=
      Matrix.fromBlocks A C 0 (1 : Matrix β β ℂ) := by
  have hi := Matrix.nonsing_inv_mul D ((Matrix.isUnit_iff_isUnit_det _).mp hD)
  simp [matrix,Matrix.fromBlocks_multiply,Matrix.mul_assoc,hi]

end ExactFourier.Pivot

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.PivotJoin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier
namespace BasisExchange
variable {α : Type} [Fintype α] [DecidableEq α]

theorem mix_mul
    {α : Type} [Fintype α] [DecidableEq α] (U V W : Matrix (α⊕PUnit) (α⊕PUnit) ℂ) :
    mix U V*W=mix (U*W) (V*W) := by
  ext i j
  cases i <;> cases j <;>
    simp [mix,Matrix.fromBlocks,Matrix.toBlocks₁₁,Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₁,Matrix.toBlocks₂₂,Matrix.mul_apply,Fintype.sum_sum_type,Sum.elim]

theorem mix_one_left
    {α : Type} [Fintype α] [DecidableEq α] (T : Matrix (α⊕PUnit) (α⊕PUnit) ℂ) :
    mix 1 T=Matrix.fromBlocks 1 0 T.toBlocks₂₁ T.toBlocks₂₂ := by
  ext i j; cases i <;> cases j <;> simp [mix,Matrix.fromBlocks,Matrix.toBlocks₁₁,
    Matrix.toBlocks₁₂,Matrix.toBlocks₂₁,Matrix.toBlocks₂₂,Matrix.one_apply]

theorem mix_one_right
    {α : Type} [Fintype α] [DecidableEq α] (T : Matrix (α⊕PUnit) (α⊕PUnit) ℂ) :
    mix T 1=Matrix.fromBlocks T.toBlocks₁₁ T.toBlocks₁₂ 0 1 := by
  ext i j; cases i <;> cases j <;> simp [mix,Matrix.fromBlocks,Matrix.toBlocks₁₁,
    Matrix.toBlocks₁₂,Matrix.toBlocks₂₁,Matrix.toBlocks₂₂]

theorem price_split (p : MatrixPrice) (U V : Matrix (α⊕PUnit) (α⊕PUnit) ℂ)
    (hU : IsUnit U) (hV : IsUnit V) (hU' : IsUnit (mix U V)) (hV' : IsUnit (mix V U)) :
    p.value (mix V U*(mix U V)⁻¹)=p.value (V*U⁻¹) := by
  let T := V*U⁻¹
  have hi := Matrix.isUnit_nonsing_inv_iff.mpr hU
  have hT : IsUnit T := hV.mul hi
  have hUinv := Matrix.mul_nonsing_inv U ((Matrix.isUnit_iff_isUnit_det _).mp hU)
  have hrel : T*U=V := Matrix.nonsing_inv_mul_cancel_right _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)
  have hL : mix U V*U⁻¹=mix 1 T := by rw [mix_mul,hUinv]
  have hR : mix V U*U⁻¹=mix T 1 := by rw [mix_mul,hUinv]
  have huL : IsUnit (mix 1 T) := by rw [← hL]; exact hU'.mul hi
  have huR : IsUnit (mix T 1) := by rw [← hR]; exact hV'.mul hi
  rw [mix_one_left] at huL
  rw [mix_one_right] at huR
  have hD := (Matrix.isUnit_fromBlocks_zero₁₂.mp huL).2
  have hA := (Matrix.isUnit_fromBlocks_zero₂₁.mp huR).1
  have hP : Pivot.ofMatrix T*(mix U V)=mix V U := by
    have hl : mix U V=mix 1 T*U := by rw [mix_mul,Matrix.one_mul,hrel]
    have hr : mix V U=mix T 1*U := by rw [mix_mul,Matrix.one_mul,hrel]
    rw [hl,hr,← Matrix.mul_assoc,mix_one_left,mix_one_right]
    rw [Pivot.ofMatrix,Pivot.solve _ _ _ _ hD]
  have he : mix V U*(mix U V)⁻¹=Pivot.ofMatrix T := by
    rw [← hP,Matrix.mul_nonsing_inv_cancel_right _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hU')]
  rw [he]
  exact p.scalar_pivot T.toBlocks₁₁ T.toBlocks₁₂ T.toBlocks₂₁ T.toBlocks₂₂ hA hD
    (by rwa [Matrix.fromBlocks_toBlocks]) |>.trans (by rw [Matrix.fromBlocks_toBlocks])

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem update_isolate
    {ι : Type} [Fintype ι] [DecidableEq ι] (U V : Matrix ι ι ℂ) (i : ι) :
    Matrix.reindex (isolate i) (isolate i) (U.updateRow i (V i))=
      mix (Matrix.reindex (isolate i) (isolate i) U) (Matrix.reindex (isolate i) (isolate i) V) := by
  ext a b
  rcases a with ⟨a,ha⟩|⟨⟩ <;> rcases b with ⟨b,hb⟩|⟨⟩ <;>
    simp_all [Matrix.reindex_apply,isolate,mix,Matrix.fromBlocks,Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂,Matrix.toBlocks₂₁,Matrix.toBlocks₂₂,Matrix.updateRow_apply]

/-- Exchange any corresponding members of two bases, assuming exactly that
both original and both exchanged lists are bases. -/
theorem price (p : MatrixPrice) (U V : Matrix ι ι ℂ) (i : ι)
    (hU : IsUnit U) (hV : IsUnit V)
    (hU' : IsUnit (U.updateRow i (V i))) (hV' : IsUnit (V.updateRow i (U i))) :
    p.value (V.updateRow i (U i)*(U.updateRow i (V i))⁻¹)=p.value (V*U⁻¹) := by
  let e := isolate i
  have h := price_split p (Matrix.reindex e e U) (Matrix.reindex e e V)
    (TensorTools.unit_reindex _ _ hU) (TensorTools.unit_reindex _ _ hV)
    (by rw [← update_isolate]; exact TensorTools.unit_reindex _ _ hU')
    (by rw [← update_isolate]; exact TensorTools.unit_reindex _ _ hV')
  rw [← update_isolate,← update_isolate,Matrix.inv_reindex,← Reindexed.mul,
    Matrix.inv_reindex,← Reindexed.mul] at h
  rw [p.reindex _ _ (hV'.mul (Matrix.isUnit_nonsing_inv_iff.mpr hU')),
    p.reindex _ _ (hV.mul (Matrix.isUnit_nonsing_inv_iff.mpr hU))] at h
  exact h

end BasisExchange
end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.MonomialTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier.MonomialMatrix
open scoped Kronecker
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem pow {A : Matrix α α ℂ} (hA : MonomialMatrix A) (n : ℕ) : MonomialMatrix (A^n) := by
  induction n with
  | zero => simpa using (one (ι := α))
  | succ n ih => simpa [pow_succ] using ih.mul hA

theorem tensor
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] {A : Matrix α α ℂ} {B : Matrix β β ℂ}
    (hA : MonomialMatrix A) (hB : MonomialMatrix B) : MonomialMatrix (A⊗ₖB) := by
  obtain ⟨σ,d,hd,ha⟩ := hA
  obtain ⟨τ,e,he,hb⟩ := hB
  refine ⟨σ.prodCongr τ,fun j => d j.1*e j.2,fun j => mul_ne_zero (hd _) (he _),?_⟩
  rintro ⟨i,k⟩ ⟨j,l⟩
  simp only [Matrix.kronecker_apply,ha,hb,Equiv.prodCongr_apply]
  split_ifs <;> simp_all

/-- A direct sum of signed monomials, indexed in (internal,block) order. -/
theorem blockDiagonal
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (A : β → Matrix α α ℂ) (hA : ∀ b,MonomialMatrix (A b)) :
    MonomialMatrix (Matrix.blockDiagonal A) := by
  classical
  choose σ d hd ha using hA
  let e : Equiv.Perm (α×β) :=
    { toFun := fun x => (σ x.2 x.1,x.2)
      invFun := fun x => ((σ x.2).symm x.1,x.2)
      left_inv := by rintro ⟨a,b⟩; simp
      right_inv := by rintro ⟨a,b⟩; simp }
  refine ⟨e,fun j => d j.2 j.1,fun j => hd _ _,?_⟩
  rintro ⟨i,k⟩ ⟨j,l⟩
  by_cases hk : k=l
  · subst l
    simp [Matrix.blockDiagonal_apply,ha,e]
  · simp [Matrix.blockDiagonal_apply,e,hk]

end ExactFourier.MonomialMatrix

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.MultiWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} (D : τ→Type) [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
  (A : ∀ t,Matrix (D t) (D t) ℂ)

variable {D A} {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem pattern_word (t : τ) {H : Matrix (D t) (D t) ℂ} {k : ℕ}
    (h : PositiveGeneration.Pattern (A t) k H) :
    ∃ W : Word D A (D t),W.matrix=H ∧ W.calls=List.replicate k t := by
  induction h with
  | zero M hm => exact ⟨monoWord M hm,by simp,by simp⟩
  | @succ k H h M hm ih =>
    obtain ⟨W,hW,hcalls⟩ := ih
    refine ⟨W++callWord t (Function.Embedding.refl _)++monoWord M hm,?_,?_⟩
    · rw [Word.matrix_append,Word.matrix_append,matrix_monoWord,matrix_callWord,hW]
      have he : Embedded.matrix (Function.Embedding.refl (D t)) (A t)=A t := by
        ext i j
        exact Embedded.matrix_on (Function.Embedding.refl _) (A t) i j
      rw [he]
    · simp [hcalls,List.replicate_succ']

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Embedded
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem card_complement
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (e : β ↪ α) :
    Fintype.card β+Fintype.card (complement e)=Fintype.card α := by
  simpa using Fintype.card_congr (coordinates e)

/-- Complete a prescribed active-tuple matching with untouched spectator wires. -/
theorem exists_completion (e : β ↪ α) (f : β ↪ γ)
    (hcard : Fintype.card α≤Fintype.card γ) :
    ∃ g : α ↪ γ,e.trans g=f := by
  have hc : Fintype.card (complement e)≤Fintype.card (complement f) := by
    have he := card_complement e
    have hf := card_complement f
    omega
  obtain ⟨h⟩ := (Function.Embedding.nonempty_of_card_le hc)
  let s : (β⊕complement e) ↪ (β⊕complement f) := Function.Embedding.sumMap (Function.Embedding.refl _) h
  let g := (coordinates e).symm.toEmbedding.trans (s.trans (coordinates f).toEmbedding)
  refine ⟨g,?_⟩
  ext i
  change coordinates f (s ((coordinates e).symm (e i)))=f i
  rw [← coordinates_inl e i,Equiv.symm_apply_apply]
  rfl

theorem realize_active (e : β ↪ α) (f : β ↪ γ) (A : Matrix β β ℂ)
    (hcard : Fintype.card α≤Fintype.card γ) :
    ∃ g : α ↪ γ,matrix g (matrix e A)=matrix f A := by
  obtain ⟨g,hg⟩ := exists_completion e f hcard
  exact ⟨g,by rw [matrix_comp,hg]⟩

variable {π : Type} [Fintype π] [DecidableEq π]
 {δ ε : π→Type} [∀ p,Fintype (δ p)] [∀ p,Fintype (ε p)]
 [∀ p,DecidableEq (δ p)] [∀ p,DecidableEq (ε p)]

theorem matrix_sigmaEmbed (e : ∀ p,δ p ↪ ε p) (A : ∀ p,Matrix (δ p) (δ p) ℂ) :
    matrix (sigmaEmbed e) (Matrix.blockDiagonal' A)=
      Matrix.blockDiagonal' (fun p=>matrix (e p) (A p)) := by
  classical
  ext ⟨p,a⟩ ⟨q,b⟩
  by_cases hpq : p=q
  · subst q
    rw [Matrix.blockDiagonal'_apply_eq]
    by_cases ha : a∈Set.range (e p)
    · obtain ⟨a,rfl⟩ := ha
      by_cases hb : b∈Set.range (e p)
      · obtain ⟨b,rfl⟩ := hb
        change matrix (sigmaEmbed e) (Matrix.blockDiagonal' A)
          (sigmaEmbed e ⟨p,a⟩) (sigmaEmbed e ⟨p,b⟩)=_
        rw [matrix_on,Matrix.blockDiagonal'_apply_eq,matrix_on]
      · rw [matrix_off_col (e p) _ _ _ hb,matrix_off_col]
        · simp
        · rintro ⟨⟨q,b'⟩,h⟩
          have hq := congrArg Sigma.fst h
          change q=p at hq
          subst q
          exact hb ⟨b',eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩
    · rw [matrix_off_row (e p) _ _ _ ha,matrix_off_row]
      · simp
      · rintro ⟨⟨q,a'⟩,h⟩
        have hq := congrArg Sigma.fst h
        change q=p at hq
        subst q
        exact ha ⟨a',eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hpq]
    by_cases ha : (⟨p,a⟩ : Σ p,ε p)∈Set.range (sigmaEmbed e)
    · obtain ⟨i,hi⟩ := ha
      by_cases hb : (⟨q,b⟩ : Σ p,ε p)∈Set.range (sigmaEmbed e)
      · obtain ⟨j,hj⟩ := hb
        rw [← hi,← hj,matrix_on]
        apply Matrix.blockDiagonal'_apply_ne
        have hi' := congrArg Sigma.fst hi
        have hj' := congrArg Sigma.fst hj
        change i.1=p at hi'
        change j.1=q at hj'
        simpa [hi',hj'] using hpq
      · rw [matrix_off_col _ _ _ _ hb]
        simp [hpq]
    · rw [matrix_off_row _ _ _ _ ha]
      simp [hpq]

end ExactFourier.Embedded

end
end

section
noncomputable section
namespace ExactFourier.Packing

/-- Deleting only identity factors preserves a noncommutative product. -/
theorem prod_filter_map {X M : Type*} [Monoid M] (L : List X) (p : X→Prop)
    [DecidablePred p] (f : X→M) (hf : ∀ x∈L,¬p x → f x=1) :
    ((L.filter p).map f).prod=(L.map f).prod := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    have ih' := ih (fun y hy=>hf y (List.mem_cons_of_mem _ hy))
    by_cases hp : p x
    · simp [hp,ih']
    · simp [hp,ih',hf x (by simp) hp]

/-- Physical slot padding retains every local program's exact multiplication order. -/
theorem ordered_padding {M : Type*} [Monoid M] {k T : ℕ} (time : Fin k→Fin T)
    (ht : StrictMono time) (f : Fin k→M) :
    (List.ofFn (Function.extend time f (fun _=>1))).prod=(List.ofFn f).prod := by
  classical
  let P : Fin T→Prop := fun t=>t∈Set.range time
  have hs : ((List.finRange T).filter P)=((List.finRange k).map time) := by
    have h₁ : ((List.finRange T).filter P).SortedLT :=
      ((List.sortedLT_finRange T).pairwise.filter _).sortedLT
    have h₂ : ((List.finRange k).map time).SortedLT := by
      apply List.Pairwise.sortedLT
      rw [List.pairwise_map]
      exact (List.sortedLT_finRange k).pairwise.imp (fun hab=>ht hab)
    apply h₁.eq_of_mem_iff h₂
    intro x
    simp [P,Set.mem_range,List.mem_map]
  let g := Function.extend time f (fun _=>1)
  rw [List.ofFn_eq_map,List.ofFn_eq_map]
  rw [← prod_filter_map (List.finRange T) P g]
  · rw [hs,List.map_map]
    congr 2
    funext x
    exact ht.injective.extend_apply f (fun _=>1) x
  · intro x hx hp
    exact Function.extend_apply' f (fun _=>1) x hp

end ExactFourier.Packing

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.WordScheduling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier
variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

theorem reindex_comp
    {α : Type} {β : Type} {γ : Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (e : α≃β) (f : β≃γ) (M : Matrix α α ℂ) :
 Matrix.reindex f f (Matrix.reindex e e M)=Matrix.reindex (e.trans f) (e.trans f) M := rfl

theorem reindex_sum
    {α : Type} {β : Type} {γ : Type} {δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ] (e : α≃β) (f : γ≃δ) (M : Matrix α α ℂ) (N : Matrix γ γ ℂ) :
 Matrix.reindex (e.sumCongr f) (e.sumCongr f) (Matrix.fromBlocks M 0 0 N)=
 Matrix.fromBlocks (Matrix.reindex e e M) 0 0 (Matrix.reindex f f N) := by
 ext x y
 cases x <;> cases y <;> rfl

end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.PiTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.Packing
variable {σ : Type} [Fintype σ] [DecidableEq σ]
 {E : σ→Type} [∀ s,Fintype (E s)] [∀ s,DecidableEq (E s)]

theorem inventory_tensor_sectors
    {σ : Type} [Fintype σ] [DecidableEq σ] {E : σ → Type} [(s : σ) → Fintype (E s)] [(s : σ) → DecidableEq (E s)] (k : σ→ℕ) (B : ∀ s,Matrix (E s) (E s) ℂ) :
 Matrix.kronecker (speciesInventory k B) (speciesInventory k B)=
   Matrix.reindex (sectorCoordinates k) (sectorCoordinates k) (sectorMatrix k B) := by
 classical
 ext ⟨⟨s,i,a⟩,⟨t,j,b⟩⟩ ⟨⟨s',i',a'⟩,⟨t',j',b'⟩⟩
 by_cases hs : s=s'
 · subst s'
   by_cases ht : t=t'
   · subst t'
     by_cases hi : i=i'
     · subst i'; by_cases hj : j=j'
       · subst j'; simp [speciesInventory,sectorMatrix,Matrix.reindex_apply,sectorCoordinates]
       · simp [speciesInventory,sectorMatrix,Matrix.reindex_apply,sectorCoordinates,hj]
     · simp [speciesInventory,sectorMatrix,Matrix.reindex_apply,sectorCoordinates,hi]
   · simp [speciesInventory,sectorMatrix,Matrix.reindex_apply,sectorCoordinates,
       Matrix.blockDiagonal'_apply,ht]
 · simp [speciesInventory,sectorMatrix,Matrix.reindex_apply,sectorCoordinates,
     Matrix.blockDiagonal'_apply,hs]

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ π ρ : Type} [Fintype π] [Fintype ρ] [DecidableEq π] [DecidableEq ρ]
  {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
  {A : ∀ t,Matrix (D t) (D t) ℂ}

theorem color_cast_apply
    {τ : Type} {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} {i j : τ} (h : i=j) (a b : D i) :
    A j (cast (congrArg D h) a) (cast (congrArg D h) b)=A i a b := by cases h; rfl

theorem coloredBlock_on
    {τ : Type} {π : Type} {ρ : Type} [Fintype π] [Fintype ρ] [DecidableEq π] [DecidableEq ρ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} (u : π→τ) (v : ρ→τ) (e : π≃ρ) (he : ∀ p,u p=v (e p))
    (x y : Σ p,D (u p)) :
    Matrix.blockDiagonal' (fun r=>A (v r)) (colorEquiv u v e he x) (colorEquiv u v e he y)=
      Matrix.blockDiagonal' (fun p=>A (u p)) x y := by
  rcases x with ⟨p,a⟩; rcases y with ⟨q,b⟩
  by_cases h : p=q
  · subst q
    change Matrix.blockDiagonal' (fun r=>A (v r))
      ⟨e p,cast (congrArg D (he p)) a⟩ ⟨e p,cast (congrArg D (he p)) b⟩=_
    rw [Matrix.blockDiagonal'_apply_eq,Matrix.blockDiagonal'_apply_eq]
    exact color_cast_apply (he p) a b
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    apply Matrix.blockDiagonal'_apply_ne
    exact fun hp=>h (e.injective hp)

theorem coloredBlock_reindex (u : π→τ) (v : ρ→τ) (e : π≃ρ) (he : ∀ p,u p=v (e p)) :
    Matrix.reindex (colorEquiv u v e he) (colorEquiv u v e he)
      (Matrix.blockDiagonal' (fun p=>A (u p)))=Matrix.blockDiagonal' (fun r=>A (v r)) := by
  ext x y
  obtain ⟨x,rfl⟩ := (colorEquiv u v e he).surjective x
  obtain ⟨y,rfl⟩ := (colorEquiv u v e he).surjective y
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
  exact (coloredBlock_on u v e he x y).symm

/-- Equal multiplicities give an exact color-preserving matching of call blocks. -/
theorem exists_colorEquiv
    {τ : Type} {π : Type} {ρ : Type} [Fintype π] [Fintype ρ] [DecidableEq π] [DecidableEq ρ] [Fintype τ] [DecidableEq τ] (u : π→τ) (v : ρ→τ)
    (h : ∀ t,Fintype.card {p // u p=t}=Fintype.card {r // v r=t}) :
    ∃ e : π≃ρ,∀ p,u p=v (e p) := by
  let f := fun t=>Fintype.equivOfCardEq (h t)
  let e := (Equiv.sigmaFiberEquiv u).symm.trans
    ((Equiv.sigmaCongrRight f).trans (Equiv.sigmaFiberEquiv v))
  refine ⟨e,?_⟩
  intro p
  exact (f (u p) ⟨p,rfl⟩).property.symm

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
  {A : ∀ t,Matrix (D t) (D t) ℂ}

variable {α : Type} [Fintype α] [DecidableEq α]

theorem Step.monoPart_monomial
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} {α : Type} [Fintype α] [DecidableEq α] (s : Step D A α) : MonomialMatrix s.monoPart := by
  cases s with
  | mono M h => exact h
  | call t e => exact MonomialMatrix.one

theorem Step.decompose
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} {α : Type} [Fintype α] [DecidableEq α] (s : Step D A α) :
    s.matrix=s.monoPart*Embedded.matrix s.activeTuple (optionalMatrix A s.kind) := by
  cases s with
  | mono M hm =>
    let e : Empty ↪ α := ⟨Empty.elim,by intro a; exact a.elim⟩
    change M=M*Embedded.matrix e (1 : Matrix Empty Empty ℂ)
    rw [Embedded.matrix_one,mul_one]
  | call t e =>
    change Embedded.matrix e (A t)=1*Embedded.matrix e (A t)
    rw [one_mul]

variable {π : Type} [Fintype π] [DecidableEq π]

theorem activeEquiv_on (u : π→Option τ) (x y : Σ c : CallIndex u,D c.1) :
    Matrix.blockDiagonal' (fun p=>optionalMatrix A (u p)) (activeEquiv u x) (activeEquiv u y)=
      Matrix.blockDiagonal' (fun c : CallIndex u=>A c.1) x y := by
  rcases x with ⟨⟨i,p,hp⟩,a⟩; rcases y with ⟨⟨j,q,hq⟩,b⟩
  by_cases hpq : p=q
  · subst q
    have hij : i=j := Option.some.inj (hp.symm.trans hq)
    subst j
    change Matrix.blockDiagonal' _ ⟨p,_⟩ ⟨p,_⟩=_
    rw [Matrix.blockDiagonal'_apply_eq,Matrix.blockDiagonal'_apply_eq]
    exact color_cast_apply (A := optionalMatrix A) hp.symm a b
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (show (⟨i,p,hp⟩ : CallIndex u)≠⟨j,q,hq⟩ from
        fun h=>hpq (congrArg (fun c : CallIndex u=>c.2.1) h))]
    exact Matrix.blockDiagonal'_apply_ne _ _ _ hpq

theorem activeEquiv_reindex (u : π→Option τ) :
    Matrix.reindex (activeEquiv (D := D) u) (activeEquiv u)
      (Matrix.blockDiagonal' (fun c : CallIndex u=>A c.1))=
      Matrix.blockDiagonal' (fun p=>optionalMatrix A (u p)) := by
  ext x y
  obtain ⟨x,rfl⟩ := (activeEquiv (D := D) u).surjective x
  obtain ⟨y,rfl⟩ := (activeEquiv (D := D) u).surjective y
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
  exact (activeEquiv_on u x y).symm

end ExactFourier.Packing

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.SlotAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {π : Type} [Fintype π] [DecidableEq π]
 {β : π→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]

theorem layer_decompose (S : ∀ p,Step D A (β p)) :
    Matrix.blockDiagonal' (fun p=>(S p).matrix)=
      Matrix.blockDiagonal' (fun p=>(S p).monoPart)*
      Embedded.matrix (Embedded.sigmaEmbed (fun p=>(S p).activeTuple))
        (Matrix.blockDiagonal' (fun p=>optionalMatrix A (S p).kind)) := by
  rw [Embedded.matrix_sigmaEmbed,← Matrix.blockDiagonal'_mul]
  congr 1
  funext p
  exact (S p).decompose

theorem gather_active (k : τ→ℕ) (S : ∀ p,Step D A (β p))
    (hc : ∀ t,Fintype.card {p // (S p).kind=some t}=k t) :
    ∃ e : ActiveSpace D k ↪ (Σ p,β p),
      Embedded.matrix e (inventoryMatrix (A := A) k)=
        Embedded.matrix (Embedded.sigmaEmbed (fun p=>(S p).activeTuple))
          (Matrix.blockDiagonal' (fun p=>optionalMatrix A (S p).kind)) := by
  let u := fun p=>(S p).kind
  let f := fun t=>Fintype.equivOfCardEq (show Fintype.card (Fin (k t))=Fintype.card {p // u p=some t} by simpa using (hc t).symm)
  let e : Inventory k≃CallIndex u := Equiv.sigmaCongrRight f
  let ce := colorEquiv (D := D) (fun i : Inventory k=>i.1) (fun i : CallIndex u=>i.1) e (fun _=>rfl)
  let ae := activeEquiv (D := D) u
  let se := Embedded.sigmaEmbed (fun p=>(S p).activeTuple)
  refine ⟨ce.toEmbedding.trans (ae.toEmbedding.trans se),?_⟩
  rw [← Embedded.matrix_comp,← Embedded.matrix_comp,Embedded.matrix_equiv,Embedded.matrix_equiv]
  have he : Matrix.reindex ce ce (inventoryMatrix (A := A) k)=
      Matrix.blockDiagonal' (fun i : CallIndex u=>A i.1) := coloredBlock_reindex _ _ e _
  rw [he,activeEquiv_reindex]

variable {ν : Type} [Fintype ν] [DecidableEq ν]

theorem embedded_inl {α γ : Type} [Fintype α] [Fintype γ] [DecidableEq α] [DecidableEq γ]
    (M : Matrix α α ℂ) : Embedded.matrix (Function.Embedding.inl : α↪α⊕γ) M=Matrix.fromBlocks M 0 0 1 := by
  ext i j
  cases i with
  | inl i => cases j with
    | inl j => exact Embedded.matrix_on Function.Embedding.inl M i j
    | inr j => rw [Embedded.matrix_off_col]; simp; rintro ⟨a,h⟩; cases h
  | inr i => rw [Embedded.matrix_off_row]; cases j <;> simp [Matrix.one_apply]; rintro ⟨a,h⟩; cases h

/-- One full slot, with spectators carrying arbitrary data, is exactly one J call. -/
theorem assemble_slot (k : τ→ℕ) (S : ∀ p,Step D A (β p))
    (hc : ∀ t,Fintype.card {p // (S p).kind=some t}=k t)
    (hw : Fintype.card (ActiveSpace D k ⊕ ν)≤Fintype.card (Σ p,β p)) :
    ∃ (M : Matrix (Σ p,β p) (Σ p,β p) ℂ) (e : ActiveSpace D k ⊕ ν ↪ (Σ p,β p)),
      MonomialMatrix M ∧ Matrix.blockDiagonal' (fun p=>(S p).matrix)=
        M*Embedded.matrix e (inventoryWithIdentity (A := A) (ν := ν) k) := by
  obtain ⟨f,hf⟩ := gather_active k S hc
  obtain ⟨g,hg⟩ := Embedded.realize_active Function.Embedding.inl f (inventoryMatrix (A := A) k) hw
  rw [embedded_inl] at hg
  refine ⟨Matrix.blockDiagonal' (fun p=>(S p).monoPart),g,
    MonomialMatrix.blockDiagonal' _ (fun p=>(S p).monoPart_monomial),?_⟩
  rw [layer_decompose,← hf]
  exact congrArg (Matrix.blockDiagonal' (fun p=>(S p).monoPart)*·) hg.symm

end ExactFourier.Packing

end
end
section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}

theorem speciesCoordinates_matrix
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} (k : τ→ℕ) (I : ℕ) :
 Matrix.reindex (speciesCoordinates (D := D) k I) (speciesCoordinates k I)
   (inventoryWithIdentity (A := A) (ν := Fin I) k)=
 speciesInventory (speciesCopies k I) (speciesMatrix (A := A)) := by
 ext ⟨s,i,a⟩ ⟨t,j,b⟩
 cases s with
 | none => cases t with
  | none => simp [Matrix.reindex_apply,speciesCoordinates,speciesInventory,speciesMatrix,
      inventoryWithIdentity,Matrix.one_apply]
  | some t => simp [Matrix.reindex_apply,speciesCoordinates,speciesInventory,speciesMatrix,
      inventoryWithIdentity,Matrix.blockDiagonal'_apply]
 | some s => cases t with
  | none => simp [Matrix.reindex_apply,speciesCoordinates,speciesInventory,speciesMatrix,
      inventoryWithIdentity,Matrix.blockDiagonal'_apply]
  | some t =>
   by_cases h : s=t
   · subst t; by_cases hij : i=j
     · subst j; simp [Matrix.reindex_apply,speciesCoordinates,speciesInventory,speciesMatrix,
        inventoryWithIdentity,inventoryMatrix]
     · simp [Matrix.reindex_apply,speciesCoordinates,speciesInventory,speciesMatrix,
        inventoryWithIdentity,inventoryMatrix,Matrix.blockDiagonal'_apply,hij]
   · simp [Matrix.reindex_apply,speciesCoordinates,speciesInventory,speciesMatrix,
       inventoryWithIdentity,inventoryMatrix,Matrix.blockDiagonal'_apply,h]

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}

theorem pair_baseline_price
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] (p : τ→ℝ) (s : LivePair τ) :
 (∑ t,p t*(pairBaseline (D := D) s t : ℝ))=pairPrice (D := D) p s := by
 simp only [pairBaseline,Nat.cast_add,Nat.cast_mul,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,mul_add,Finset.sum_add_distrib,pairPrice]
 have he : ∀ a : Option τ, ∀ n : ℕ,
   (∑ t,p t*((n : ℝ)*(if a=some t then 1 else 0)))=(n : ℝ)*speciesPrice p a := by
  intro a n
  cases a with
  | none => simp
  | some a =>
   simp only [Option.some.injEq,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
   ring
 rw [he,he]

theorem comparison_ineq (p : τ→ℝ) (c : PairComparison (A := A)) :
 (∑ t,p t*((c.delta t : ℤ) : ℝ))≤0 ↔ pairPrice (D := D) p c.pair≤c.word.weight p := by
 simp only [PairComparison.delta,Int.cast_sub,Int.cast_natCast,mul_sub,Finset.sum_sub_distrib]
 rw [pair_baseline_price,Word.weight_count]
 have he : (∑ t,p t*(c.word.count t : ℝ))=∑ t,(c.word.count t : ℝ)*p t := by
  apply Finset.sum_congr rfl
  intro t ht
  ring
 rw [he]
 exact sub_nonpos

end ExactFourier.Packing

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.ComparisonRename
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Kronecker
namespace ExactFourier.Packing
variable {τ σ : Type}
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {E : σ→Type} [∀ t,Fintype (E t)] [∀ t,DecidableEq (E t)]
 {B : ∀ t,Matrix (E t) (E t) ℂ}

theorem pairPrice_map
    {τ : Type} {σ : Type} {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {E : σ → Type} [(t : σ) → Fintype (E t)] [(t : σ) → DecidableEq (E t)] (f : τ→σ) (e : ∀ t,D t≃E (f t)) (v : σ→ℝ) (p : LivePair τ) :
 pairPrice (D := E) v (mapPair f p)=pairPrice (D := D) (v∘f) p := by
 have hc : ∀ s : Option τ,Fintype.card (SpeciesDomain E (s.map f))=Fintype.card (SpeciesDomain D s) :=
  fun s=>(Fintype.card_congr (speciesEquiv f e s)).symm
 have hp : ∀ s : Option τ,speciesPrice v (s.map f)=speciesPrice (v∘f) s := by
  intro s; cases s <;> rfl
 dsimp [pairPrice,mapPair]
 rw [hc,hc,hp,hp]

@[simp] theorem PairComparison.rename_ineq (f : τ→σ) (e : ∀ t,D t≃E (f t))
 (he : ∀ t,Matrix.reindex (e t) (e t) (A t)=B (f t)) (c : PairComparison (A := A)) (v : σ→ℝ) :
 (pairPrice (D := E) v (c.rename f e he).pair≤(c.rename f e he).word.weight v) ↔
 pairPrice (D := D) (v∘f) c.pair≤c.word.weight (v∘f) := by
 dsimp only [PairComparison.rename]
 rw [pairPrice_map f e,Word.weight_reindex,Word.weight_rename]
end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing

theorem Word.continuous_weight {τ : Type} {D : τ→Type}
 [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ} {α : Type} [Fintype α] [DecidableEq α]
 (f : τ→GMatrix) (W : Word D A α) : Continuous (fun p : GMatrix→ℝ=>W.weight (p∘f)) := by
 induction W with
 | nil => exact continuous_const
 | cons s W ih =>
  cases s with
  | mono M h => exact ih
  | call t e => exact (continuous_apply (f t)).add ih

theorem GlobalComparison.closed (c : GlobalComparison) : IsClosed {p : GMatrix→ℝ|c.holds p} := by
 apply isClosed_le _ (Word.continuous_weight c.family c.comparison.word)
 have hp : ∀ s : Option (Fin c.num),Continuous (fun p : GMatrix→ℝ=>speciesPrice (p∘c.family) s) := by
  intro s; cases s with
  | none => exact continuous_const
  | some t => exact continuous_apply (c.family t)
 exact (continuous_const.mul (hp _)).add (continuous_const.mul (hp _))

variable {τ : Type} [Fintype τ] [DecidableEq τ]
 (f : τ→GMatrix)

theorem GlobalConstraints.apply {p : GMatrix→ℝ} (hp : GlobalConstraints p)
 (c : PairComparison (D := fun t=>(f t).domain) (A := fun t=>(f t).mat)) :
 pairPrice (D := fun t=>(f t).domain) (p∘f) c.pair≤c.word.weight (p∘f) := by
 have hh := hp (toGlobalComparison f c)
 dsimp only [GlobalComparison.holds,toGlobalComparison] at hh
 have hh' := (PairComparison.rename_ineq (Fintype.equivFin τ)
  (fun t=>Equiv.cast (congrArg (fun t=>(f t).domain) ((Fintype.equivFin τ).symm_apply_apply t).symm))
  (fun t=>family_cast_matrix f ((Fintype.equivFin τ).symm_apply_apply t).symm)
  c (p∘f∘(Fintype.equivFin τ).symm)).mp hh
 simpa only [Function.comp_def,Equiv.symm_apply_apply] using hh'
end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]

theorem pair_baseline_sum
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] (k : τ→ℕ) (I : ℕ) (t : τ) :
 (∑ p : LivePair τ,speciesCopies k I p.1.1*speciesCopies k I p.1.2*
    pairBaseline (D := D) p t)=2*k t*((∑ i,k i*Fintype.card (D i))+I) := by
 let f : (Option τ×Option τ)→ℕ := fun p=>
  speciesCopies k I p.1*speciesCopies k I p.2*
   (Fintype.card (SpeciesDomain D p.2)*(if p.1=some t then 1 else 0)+
    Fintype.card (SpeciesDomain D p.1)*(if p.2=some t then 1 else 0))
 have he : (∑ p : LivePair τ,f p.val)=∑ p,f p := by
  have h := Fintype.sum_subtype_add_sum_subtype (fun p : Option τ×Option τ=>p≠(none,none)) f
  have hz : (∑ p : {p : Option τ×Option τ // ¬p≠(none,none)},f p.val)=0 := by
   apply Finset.sum_eq_zero
   intro p hp
   have h : p.val=(none,none) := Classical.not_not.mp p.property
   simp [h,f,speciesCopies]
  rw [hz,add_zero] at h
  exact h
 change (∑ p : LivePair τ,f p.val)=_
 rw [he,Fintype.sum_prod_type]
 simp only [f,mul_add,Finset.sum_add_distrib]
 have hleft : (∑ s : Option τ,∑ r : Option τ,
    speciesCopies k I s*speciesCopies k I r*
     (Fintype.card (SpeciesDomain D r)*(if s=some t then 1 else 0)))=
    k t*((∑ i,k i*Fintype.card (D i))+I) := by
  have he : ∀ s r : Option τ,
      speciesCopies k I s*speciesCopies k I r*
       (Fintype.card (SpeciesDomain D r)*(if s=some t then 1 else 0))=
      if s=some t then k t*(speciesCopies k I r*Fintype.card (SpeciesDomain D r)) else 0 := by
   intro s r
   by_cases h : s=some t
   · subst s; simp only [ite_true,speciesCopies,mul_one]; ring
   · simp [h]
  simp_rw [he]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [← Finset.mul_sum,Fintype.sum_option]
  simp only [speciesCopies,SpeciesDomain,Fintype.card_unit,mul_one]
  congr 1
  omega
 rw [hleft]
 have hright : (∑ s : Option τ,∑ r : Option τ,
    speciesCopies k I s*speciesCopies k I r*
     (Fintype.card (SpeciesDomain D s)*(if r=some t then 1 else 0)))=
    k t*((∑ i,k i*Fintype.card (D i))+I) := by
  rw [Finset.sum_comm]
  convert hleft using 1
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  ring
 rw [hright]
 ring

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {ρ : Type} [Fintype ρ] [DecidableEq ρ]

theorem familyProgram_matrix
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} {ρ : Type} [Fintype ρ] [DecidableEq ρ] (c : ρ→PairComparison (A := A)) (p : LivePair τ⊕ρ) :
 (familyProgram c p).matrix (A := A)=pairMatrix (A := A) (familyKey c p) := by
 cases p with
 | inl p => exact (Word.matrix_framed _).trans (standardPair_matrix p)
 | inr r => exact (Word.matrix_framed _).trans (c r).correct

theorem familyMultiplicity_key
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} {ρ : Type} [Fintype ρ] [DecidableEq ρ] (c : ρ→PairComparison (A := A)) (n : LivePair τ→ℕ) (a : ρ→ℕ)
 (h : ∀ p,(∑ r,if (c r).pair=p then a r else 0)≤n p) (s : LivePair τ) :
 (∑ p,if familyKey c p=s then familyMultiplicity c n a p else 0)=n s := by
 rw [Fintype.sum_sum_type]
 simp only [familyKey,familyMultiplicity]
 simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
 exact Nat.sub_add_cancel (h s)

theorem family_saving
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} {ρ : Type} [Fintype ρ] [DecidableEq ρ] (c : ρ→PairComparison (A := A)) (n : LivePair τ→ℕ) (a : ρ→ℕ)
 (h : ∀ p,(∑ r,if (c r).pair=p then a r else 0)≤n p) (t : τ) :
 (∑ p,(n p : ℤ)*pairBaseline (D := D) p t)-
 (∑ p,(familyMultiplicity c n a p : ℤ)*(familyProgram c p).types.count t)=
 ∑ r,(a r : ℤ)*(c r).delta t := by
 rw [Fintype.sum_sum_type]
 simp only [familyMultiplicity,familyProgram,Word.types_framed]
 simp only [show ∀ p : LivePair τ,((standardPair (A := A) p).calls).count t=pairBaseline (D := D) p t from fun p=>standardPair_count p t]
 simp only [Nat.cast_sub (h _),Finset.sum_sub_distrib,sub_mul]
 have hswap : (∑ p,(∑ r,if (c r).pair=p then (a r : ℤ) else 0)*pairBaseline (D := D) p t)=
      ∑ r,(a r : ℤ)*pairBaseline (D := D) (c r).pair t := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
 simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_zero] at *
 rw [hswap]
 simp only [PairComparison.delta,Word.count,mul_sub,Finset.sum_sub_distrib]
 ring

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {α : Type} [Fintype α] [DecidableEq α]

theorem slotMono_monomial
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {α : Type} [Fintype α] [DecidableEq α] (f : Option (Frame D α)) : MonomialMatrix (slotMono f) := by
 cases f with
 | none => exact MonomialMatrix.one
 | some f => exact f.monomial

theorem slotMatrix_extend
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} {α : Type} [Fintype α] [DecidableEq α] (W : FramedWord D α) {T : ℕ} (time : Fin W.frames.length→Fin T)
 (ht : Function.Injective time) (t : Fin T) :
 slotMatrix (A := A) (framedSlot W time t)=
   Function.extend time (fun i=>(W.frames.get i).matrix (A := A)) (fun _=>1) t := by
 classical
 by_cases h : ∃ i,time i=t
 · obtain ⟨i,rfl⟩ := h
   simp [framedSlot,ht.extend_apply,slotMatrix,slotMono,slotCall,Step.matrix,Frame.matrix]
 · simp [framedSlot,Function.extend_apply' _ _ _ h,slotMatrix,slotMono,slotCall,Step.matrix]

theorem slotMatrix_product (W : FramedWord D α) {T : ℕ} (time : Fin W.frames.length→Fin T)
 (ht : StrictMono time) :
 (List.ofFn (fun t=>slotMatrix (A := A) (framedSlot W time t))).prod * W.tail=W.matrix (A := A) := by
 simp_rw [slotMatrix_extend W time ht.injective]
 rw [ordered_padding time ht]
 change (List.ofFn (Frame.matrix∘W.frames.get)).prod*W.tail=(W.frames.map Frame.matrix).prod*W.tail
 rw [← List.map_ofFn]
 simp

variable {π : Type} [Fintype π] [DecidableEq π]
 {β : π→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]

theorem framedLayer_product (W : ∀ p,FramedWord D (β p)) {T : ℕ}
 (time : ∀ p,Fin (W p).frames.length→Fin T) (ht : ∀ p,StrictMono (time p)) :
 (List.ofFn (framedLayer (A := A) W time)).prod * Matrix.blockDiagonal' (fun p=>(W p).tail)=
   Matrix.blockDiagonal' (fun p=>(W p).matrix (A := A)) := by
 let φ := Matrix.blockDiagonal'RingHom (m' := β) (α := ℂ)
 let f := fun t p=>slotMatrix (A := A) (framedSlot (W p) (time p) t)
 change (List.ofFn (φ∘f)).prod*φ (fun p=>(W p).tail)=φ (fun p=>(W p).matrix)
 rw [← List.map_ofFn,← map_list_prod,← map_mul]
 apply congrArg φ
 funext p
 change (List.ofFn f).prod p*(W p).tail=_
 have he := map_list_prod (Pi.evalMonoidHom (fun p=>Matrix (β p) (β p) ℂ) p) (List.ofFn f)
 rw [List.map_ofFn] at he
 change (List.ofFn f).prod p=(List.ofFn (fun t=>f t p)).prod at he
 rw [he]
 exact slotMatrix_product (W p) (time p) (ht p)

variable {ν : Type} [Fintype ν] [DecidableEq ν]

theorem gather_framed_slot (k : τ→ℕ) (S : ∀ p,Option (Frame D (β p)))
 (hc : ∀ t,Fintype.card {p // (slotCall (A := A) (S p)).kind=some t}=k t)
 (hw : Fintype.card (ActiveSpace D k ⊕ ν)≤Fintype.card (Σ p,β p)) :
 ∃ (M : Matrix (Σ p,β p) (Σ p,β p) ℂ) (e : ActiveSpace D k ⊕ ν ↪ (Σ p,β p)),
 MonomialMatrix M ∧ Matrix.blockDiagonal' (fun p=>slotMatrix (A := A) (S p))=
   M*Embedded.matrix e (inventoryWithIdentity (A := A) (ν := ν) k) := by
 obtain ⟨M,e,hM,he⟩ := assemble_slot (ν := ν) k (fun p=>slotCall (S p)) hc hw
 refine ⟨Matrix.blockDiagonal' (fun p=>slotMono (S p))*M,e,
   (MonomialMatrix.blockDiagonal' _ (fun p=>slotMono_monomial (S p))).mul hM,?_⟩
 change Matrix.blockDiagonal' (fun p=>slotMono (S p)*(slotCall (A := A) (S p)).matrix)=_
 rw [Matrix.blockDiagonal'_mul,he,mul_assoc]

end ExactFourier.Packing

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.PackedSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.Packing
variable {α γ : Type} [Fintype α] [Fintype γ] [DecidableEq α] [DecidableEq γ]

/-- Convert exact slot factorizations to a literal word, retaining the precise call count. -/
theorem pack_list (J : Matrix γ γ ℂ) (L : List (Matrix α α ℂ))
 (hL : ∀ B∈L,∃ (M : Matrix α α ℂ) (e : γ↪α),MonomialMatrix M ∧ B=M*Embedded.matrix e J) :
 ∃ W : Word (fun _ : Unit=>γ) (fun _=>J) α,W.matrix=L.prod ∧ W.calls.length=L.length := by
 induction L with
 | nil => exact ⟨[],rfl,rfl⟩
 | cons B L ih =>
   obtain ⟨M,e,hM,hB⟩ := hL B (List.mem_cons_self ..)
   obtain ⟨W,hW,hcount⟩ := ih (fun X hX=>hL X (List.mem_cons_of_mem _ hX))
   refine ⟨monoWord M hM++callWord () e++W,?_,?_⟩
   · simp only [Word.matrix_append,matrix_monoWord,matrix_callWord,hW,List.prod_cons,hB]
   · simp [hcount]

variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {π : Type} [Fintype π] [DecidableEq π]
 {β : π→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]
 {ν : Type} [Fintype ν] [DecidableEq ν]

theorem packed_schedule (k : τ→ℕ) (W : ∀ p,FramedWord D (β p)) {T : ℕ}
 (time : ∀ p,Fin (W p).frames.length→Fin T) (ht : ∀ p,StrictMono (time p))
 (hc : ∀ s t,Fintype.card {p // (slotCall (A := A) (framedSlot (W p) (time p) s)).kind=some t}=k t)
 (hw : Fintype.card (ActiveSpace D k ⊕ ν)≤Fintype.card (Σ p,β p)) :
 ∃ V : Word (fun _ : Unit=>ActiveSpace D k ⊕ ν)
   (fun _=>inventoryWithIdentity (A := A) (ν := ν) k) (Σ p,β p),
 V.matrix=Matrix.blockDiagonal' (fun p=>(W p).matrix (A := A)) ∧ V.calls.length=T := by
 let J := inventoryWithIdentity (A := A) (ν := ν) k
 obtain ⟨V,hV,hcount⟩ := pack_list J (List.ofFn (framedLayer (A := A) W time)) (by
   intro B hB
   obtain ⟨s,rfl⟩ := List.mem_ofFn.mp hB
   exact gather_framed_slot k (fun p=>framedSlot (W p) (time p) s) (hc s) hw)
 let M := Matrix.blockDiagonal' (fun p=>(W p).tail)
 have hM : MonomialMatrix M := MonomialMatrix.blockDiagonal' _ (fun p=>(W p).tail_monomial)
 refine ⟨V++monoWord M hM,?_,?_⟩
 · rw [Word.matrix_append,matrix_monoWord,hV]
   exact framedLayer_product W time ht
 · simpa using hcount

end ExactFourier.Packing

end
end

section
namespace ExactFourier.Packing

private theorem quotient_lt {m F : ℕ} (j : Fin m) : j.val / F < m / F + 1 := by
  have h : j.val / F ≤ m / F := Nat.div_le_div_right (Nat.le_of_lt j.isLt)
  omega

/-- Within any one residue class, division by F is an injective label. -/
theorem same_remainder_card {m F : ℕ} (S : Finset (Fin m))
    (hS : ∀ i ∈ S, ∀ j ∈ S, i.val % F = j.val % F) : S.card ≤ m / F + 1 := by
  let q : Fin m → Fin (m / F + 1) := fun j => ⟨j.val / F, quotient_lt j⟩
  have hq : Set.InjOn q (↑S : Set (Fin m)) := by
    intro i hi j hj hij
    have hdiv : i.val / F = j.val / F := congrArg Fin.val hij
    have hmod := hS i hi j hj
    apply Fin.ext
    calc
      i.val = i.val % F + F * (i.val / F) := (Nat.mod_add_div i.val F).symm
      _ = j.val % F + F * (j.val / F) := by rw [hdiv, hmod]
      _ = j.val := Nat.mod_add_div j.val F
  rw [← Finset.card_image_of_injOn hq]
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)

/-- Every occurrence of a fixed program has at most floor(m/F)+1 copies in a slot. -/
theorem occurrence_card {m F o t : ℕ} :
    (Finset.univ.filter (fun j : Fin m => cyclicStart F j + o = t)).card ≤ m / F + 1 := by
  apply same_remainder_card (F := F)
  intro i hi j hj
  have hi' : cyclicStart F i + o = t := (Finset.mem_filter.mp hi).2
  have hj' : cyclicStart F j + o = t := (Finset.mem_filter.mp hj).2
  change i.val % F + o = t at hi'
  change j.val % F + o = t at hj'
  omega

theorem occurrence_card_real {m F o t : ℕ} (hF : 0 < F) :
    ((Finset.univ.filter (fun j : Fin m => cyclicStart F j + o = t)).card : ℝ) ≤
      (m : ℝ) / F + 1 := by
  have h := occurrence_card (m := m) (F := F) (o := o) (t := t)
  have hcast : ((Finset.univ.filter (fun j : Fin m => cyclicStart F j + o = t)).card : ℝ) ≤
      (m / F : ℕ) + 1 := by exact_mod_cast h
  have hf : (0 : ℝ) < F := by exact_mod_cast hF
  have hdiv : ((m / F : ℕ) : ℝ) ≤ (m : ℝ) / F := by
    apply (le_div_iff₀ hf).mpr
    exact_mod_cast Nat.div_mul_le_self m F
  linarith

variable {π τ : Type*} [Fintype π] [DecidableEq τ]

/-- The additive discrepancy is a constant depending only on the fixed program family,
not on sector multiplicities or on the number of slots. -/
theorem scheduledLoad_bound (P : π → List τ) (m : π → ℕ) (F : ℕ) (hF : 0 < F)
    (i : τ) (t : ℕ) :
    (scheduledLoad P m F i t : ℝ) ≤ (totalCalls P m i : ℝ) / F + ∑ p, ((P p).length : ℝ) := by
  classical
  have h : (scheduledLoad P m F i t : ℝ) ≤
      ∑ p, ((m p : ℝ) / F + 1) * (occurrences (P p) i).card := by
    simp only [scheduledLoad, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro p hp
    calc
      _ ≤ ∑ _o ∈ occurrences (P p) i, ((m p : ℝ) / F + 1) := by
        apply Finset.sum_le_sum
        intro o ho
        exact occurrence_card_real hF
      _ = _ := by simp [mul_comm]; ring
  have hlen : (∑ p, ((occurrences (P p) i).card : ℝ)) ≤ ∑ p, ((P p).length : ℝ) := by
    apply Finset.sum_le_sum
    intro p hp
    exact_mod_cast (Finset.card_le_univ (occurrences (P p) i)).trans_eq (Fintype.card_fin _)
  calc
    _ ≤ ∑ p, ((m p : ℝ) / F + 1) * (occurrences (P p) i).card := h
    _ = (totalCalls P m i : ℝ) / F + ∑ p, ((occurrences (P p) i).card : ℝ) := by
      simp [totalCalls, add_mul, Finset.sum_add_distrib, Finset.sum_div,
        div_mul_eq_mul_div]
    _ ≤ _ := by linarith

end ExactFourier.Packing

end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {α : Type} [Fintype α] [DecidableEq α]

theorem framedSlot_type
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} {α : Type} [Fintype α] [DecidableEq α] (W : FramedWord D α) {T : ℕ}
 (time : Fin W.frames.length→Fin T) (ht : Function.Injective time) (s : Fin T) (t : τ) :
 (slotCall (A := A) (framedSlot W time s)).kind=some t ↔
   ∃ i,time i=s ∧ (W.frames.get i).type=t := by
 classical
 by_cases h : ∃ i,time i=s
 · obtain ⟨i,rfl⟩ := h
   simp only [framedSlot,ht.extend_apply,slotCall,Step.kind,Option.some.injEq]
   constructor
   · intro h; exact ⟨i,rfl,h⟩
   · rintro ⟨j,hj,hj'⟩; exact ht hj ▸ hj'
 · simp only [framedSlot,Function.extend_apply' _ _ _ h,slotCall,Step.kind]
   constructor
   · intro hh; cases hh
   · rintro ⟨i,hi,_⟩; exact h ⟨i,hi⟩ |>.elim

theorem card_subtype_sigma {π : Type} [Fintype π] {β : π→Type} [∀ p,Fintype (β p)]
 (P : ∀ p,β p→Prop) [∀ p,DecidablePred (P p)] :
 Fintype.card {x : Σ p,β p // P x.1 x.2}=∑ p,Fintype.card {x : β p // P p x} := by
 rw [Fintype.card_congr (subtypeSigmaAll P),Fintype.card_sigma]

variable {π : Type} [Fintype π] [DecidableEq π]
 {β : π→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]

theorem slot_card
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} {π : Type} [Fintype π] [DecidableEq π] {β : π → Type} [(p : π) → Fintype (β p)] [(p : π) → DecidableEq (β p)] (W : ∀ p,FramedWord D (β p)) {T : ℕ}
 (time : ∀ p,Fin (W p).frames.length→Fin T) (ht : ∀ p,Function.Injective (time p))
 (s : Fin T) (t : τ) :
 Fintype.card {p // (slotCall (A := A) (framedSlot (W p) (time p) s)).kind=some t}=
 Fintype.card {v : Σ p,Fin (W p).frames.length //
   time v.1 v.2=s ∧ ((W v.1).frames.get v.2).type=t} := by
 classical
 let f : {v : Σ p,Fin (W p).frames.length //
   time v.1 v.2=s ∧ ((W v.1).frames.get v.2).type=t} →
   {p // (slotCall (A := A) (framedSlot (W p) (time p) s)).kind=some t} :=
   fun v=>⟨v.val.1,(framedSlot_type _ _ (ht _) _ _).mpr ⟨v.val.2,v.property⟩⟩
 apply (Fintype.card_congr (Equiv.ofBijective f ?_)).symm
 constructor
 · rintro ⟨⟨p,i⟩,hi⟩ ⟨⟨q,j⟩,hj⟩ h
   have hpq := congrArg Subtype.val h
   change p=q at hpq; subst q
   have hij := ht p (hi.1.trans hj.1.symm)
   change i=j at hij
   subst j; rfl
 · rintro ⟨p,hp⟩
   obtain ⟨i,hi⟩ := (framedSlot_type _ _ (ht _) _ _).mp hp
   exact ⟨⟨⟨p,i⟩,hi⟩,rfl⟩

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
open Finset

/-- A monotone chronological listing cannot repeat a time after more than its capacity. -/
theorem monotone_fiber_gap {n T d : ℕ} (f : Fin n→Fin T) (hm : Monotone f)
 (hc : ∀ t,Fintype.card {i // f i=t}<d) {a b : Fin n}
 (hab : a.val+d≤b.val) : f a<f b := by
 have hab' : a≤b := by exact Fin.le_iff_val_le_val.mpr (by omega)
 have hle := hm hab'
 apply lt_of_le_of_ne hle
 intro he
 have hi : Icc a b ⊆ (univ.filter fun i=>f i=f a) := by
  intro i hi
  obtain ⟨hai,hib⟩ := mem_Icc.mp hi
  simp only [mem_filter,mem_univ,true_and]
  exact (hm hib |>.trans_eq he.symm).antisymm (hm hai)
 have hcard := card_le_card hi
 have hc' := hc (f a)
 rw [Fintype.card_subtype] at hc'
 rw [Fin.card_Icc] at hcard
 omega

theorem vacancy_listing {T n : ℕ} (c : Fin T→ℕ) (hn : ∑ t,c t=n) :
 ∃ f : Fin n→Fin T,Monotone f ∧ (∀ t,Fintype.card {i // f i=t}=c t) := by
 let V := Lex (Σ t,Fin (c t))
 have hV : Fintype.card V=n := by simpa [V,Fintype.card_sigma] using hn
 let e := Fintype.orderIsoFinOfCardEq V hV
 refine ⟨fun i=>(e i).1,?_,?_⟩
 · intro i j hij
   have hh := e.monotone hij
   rcases Sigma.Lex.le_def.mp hh with h|⟨h,_⟩
   · exact h.le
   · exact le_of_eq h
 · intro t
   let ef : {i : Fin n // (e i).1=t}≃{v : V // v.1=t} :=
     e.toEquiv.subtypeEquiv (fun _=>Iff.rfl)
   calc
    _ = Fintype.card {v : V // v.1=t} := Fintype.card_congr ef
    _ = Fintype.card (Fin (c t)) := Fintype.card_congr (sigmaFiberEquiv t)
    _ = c t := Fintype.card_fin _

/-- Cyclic vacancy allocation; no distribution assumption on the clustering of vacancies. -/
theorem exists_dummy_schedule {T d h k : ℕ} (c : Fin T→ℕ)
 (hc : ∀ t,c t≤k) (hkd : k<d) (hsum : ∑ t,c t=d*h) :
 ∃ time : Fin d→Fin h→Fin T,(∀ j,StrictMono (time j)) ∧
   ∀ t,Fintype.card {v : Fin d×Fin h // time v.1 v.2=t}=c t := by
 obtain ⟨f,hf,hfc⟩ := vacancy_listing c (hsum.trans (Nat.mul_comm d h))
 let e : Fin d×Fin h≃Fin (h*d) := (Equiv.prodComm _ _).trans finProdFinEquiv
 let time := fun j o=>f (e (j,o))
 refine ⟨time,?_,?_⟩
 · intro j a b hab
   apply monotone_fiber_gap f hf (fun t=>(hfc t).trans_lt ((hc t).trans_lt hkd))
   change (finProdFinEquiv (a,j)).val+d≤(finProdFinEquiv (b,j)).val
   change j.val+d*a.val+d≤j.val+d*b.val
   have hh : a.val+1≤b.val := hab
   have hm := Nat.mul_le_mul_left d hh
   rw [Nat.mul_add,Nat.mul_one] at hm
   omega
 · intro t
   let ef : {v : Fin d×Fin h // time v.1 v.2=t}≃{i : Fin (h*d) // f i=t} :=
     e.subtypeEquiv (fun _=>Iff.rfl)
   exact (Fintype.card_congr ef).trans (hfc t)

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}

theorem exists_dummy_framed (W : ∀ t,FramedWord D (D t))
 (hW : ∀ t (o : Fin (W t).frames.length),((W t).frames.get o).type=t)
 {T : ℕ} (c : τ→Fin T→ℕ) (k d : τ→ℕ)
 (hc : ∀ t s,c t s≤k t) (hkd : ∀ t,k t<d t)
 (hsum : ∀ t,∑ s,c t s=d t*(W t).frames.length) :
 ∃ time : ∀ v : Σ t,Fin (d t),Fin (W v.1).frames.length→Fin T,
 (∀ v,StrictMono (time v)) ∧ ∀ s t,
 Fintype.card {v : Σ t,Fin (d t) //
   (slotCall (A := A) (framedSlot (W v.1) (time v) s)).kind=some t}=c t s := by
 classical
 choose time ht hcount using fun t=>exists_dummy_schedule (c t) (hc t) (hkd t) (hsum t)
 refine ⟨fun v=>time v.1 v.2,fun v=>ht v.1 v.2,?_⟩
 intro s t
 rw [slot_card _ _ (fun v=>(ht v.1 v.2).injective)]
 rw [card_subtype_sigma (fun (v : Σ t,Fin (d t)) (o : Fin (W v.1).frames.length)=>
   time v.1 v.2 o=s ∧ ((W v.1).frames.get o).type=t)]
 simp only [Fintype.sum_sigma]
 have he : ∀ i,(∑ j : Fin (d i),Fintype.card {o : Fin (W i).frames.length //
     time i j o=s ∧ ((W i).frames.get o).type=t})=if i=t then c t s else 0 := by
  intro i
  simp only [hW]
  by_cases h : i=t
  · subst i
    simp only [and_true,ite_true]
    have hh := hcount t s
    simpa only [Fintype.card_subtype,Finset.card_filter,Fintype.sum_prod_type] using hh
  · simp [h]
 simp only [he]
 simp

end ExactFourier.Packing

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.SumFramed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {π ρ : Type} [Fintype π] [Fintype ρ] [DecidableEq π] [DecidableEq ρ]
 {β : π→Type} {γ : ρ→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]
 [∀ r,Fintype (γ r)] [∀ r,DecidableEq (γ r)]

theorem sumTime_strict
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {π : Type} {ρ : Type} [Fintype π] [Fintype ρ] [DecidableEq π] [DecidableEq ρ] {β : π → Type} {γ : ρ → Type} [(p : π) → Fintype (β p)] [(p : π) → DecidableEq (β p)] [(r : ρ) → Fintype (γ r)] [(r : ρ) → DecidableEq (γ r)] (W : ∀ p,FramedWord D (β p)) (V : ∀ r,FramedWord D (γ r)) {T : ℕ}
 (timeW : ∀ p,Fin (W p).frames.length→Fin T)
 (timeV : ∀ r,Fin (V r).frames.length→Fin T)
 (hW : ∀ p,StrictMono (timeW p)) (hV : ∀ r,StrictMono (timeV r)) :
 ∀ v,StrictMono (sumTime W V timeW timeV v) := by
 intro v; cases v with
 | inl p => exact hW p
 | inr r => exact hV r

theorem sum_slot_card
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} {π : Type} {ρ : Type} [Fintype π] [Fintype ρ] [DecidableEq π] [DecidableEq ρ] {β : π → Type} {γ : ρ → Type} [(p : π) → Fintype (β p)] [(p : π) → DecidableEq (β p)] [(r : ρ) → Fintype (γ r)] [(r : ρ) → DecidableEq (γ r)] (W : ∀ p,FramedWord D (β p)) (V : ∀ r,FramedWord D (γ r)) {T : ℕ}
 (timeW : ∀ p,Fin (W p).frames.length→Fin T)
 (timeV : ∀ r,Fin (V r).frames.length→Fin T) (s : Fin T) (t : τ) :
 Fintype.card {v //
   (slotCall (A := A) (framedSlot (sumFramed W V v) (sumTime W V timeW timeV v) s)).kind=some t}=
 Fintype.card {p // (slotCall (A := A) (framedSlot (W p) (timeW p) s)).kind=some t}+
 Fintype.card {r // (slotCall (A := A) (framedSlot (V r) (timeV r) s)).kind=some t} := by
 rw [Fintype.card_congr Equiv.subtypeSum,Fintype.card_sum]
 rfl

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {π ρ : Type} [Fintype π] [Fintype ρ] [DecidableEq π] [DecidableEq ρ]
 {β : π→Type} {γ : ρ→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]
 [∀ r,Fintype (γ r)] [∀ r,DecidableEq (γ r)]

theorem matrix_sumFramed
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} {π : Type} {ρ : Type} [Fintype π] [Fintype ρ] [DecidableEq π] [DecidableEq ρ] {β : π → Type} {γ : ρ → Type} [(p : π) → Fintype (β p)] [(p : π) → DecidableEq (β p)] [(r : ρ) → Fintype (γ r)] [(r : ρ) → DecidableEq (γ r)] (W : ∀ p,FramedWord D (β p)) (V : ∀ r,FramedWord D (γ r)) :
 Matrix.reindex (Equiv.sumSigmaDistrib (SumDomain β γ)) (Equiv.sumSigmaDistrib (SumDomain β γ))
   (Matrix.blockDiagonal' (fun v=>(sumFramed W V v).matrix (A := A)))=
 Matrix.fromBlocks (Matrix.blockDiagonal' (fun p=>(W p).matrix (A := A))) 0 0
   (Matrix.blockDiagonal' (fun r=>(V r).matrix (A := A))) := by
 ext x y
 rcases x with ⟨p,a⟩|⟨r,a⟩ <;> rcases y with ⟨q,b⟩|⟨s,b⟩ <;>
   dsimp only [SumDomain,Sum.elim] at a b
 · change Matrix.blockDiagonal' (fun v=>(sumFramed W V v).matrix (A := A))
     ⟨Sum.inl p,a⟩ ⟨Sum.inl q,b⟩=Matrix.blockDiagonal' (fun p=>(W p).matrix (A := A)) ⟨p,a⟩ ⟨q,b⟩
   by_cases h : p=q
   · subst q; rw [Matrix.blockDiagonal'_apply_eq,Matrix.blockDiagonal'_apply_eq]; rfl
   · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (by simpa using h),Matrix.blockDiagonal'_apply_ne _ _ _ h]
 · change Matrix.blockDiagonal' (fun v=>(sumFramed W V v).matrix (A := A))
     ⟨Sum.inl p,a⟩ ⟨Sum.inr s,b⟩=0
   exact Matrix.blockDiagonal'_apply_ne _ _ _ (by simp)
 · change Matrix.blockDiagonal' (fun v=>(sumFramed W V v).matrix (A := A))
     ⟨Sum.inr r,a⟩ ⟨Sum.inl q,b⟩=0
   exact Matrix.blockDiagonal'_apply_ne _ _ _ (by simp)
 · change Matrix.blockDiagonal' (fun v=>(sumFramed W V v).matrix (A := A))
     ⟨Sum.inr r,a⟩ ⟨Sum.inr s,b⟩=Matrix.blockDiagonal' (fun r=>(V r).matrix (A := A)) ⟨r,a⟩ ⟨s,b⟩
   by_cases h : r=s
   · subst s; rw [Matrix.blockDiagonal'_apply_eq,Matrix.blockDiagonal'_apply_eq]; rfl
   · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (by simpa using h),Matrix.blockDiagonal'_apply_ne _ _ _ h]

variable (D) (α : Type) [Fintype α] [DecidableEq α]

theorem emptyTime_strict
    {τ : Type} [Fintype τ] [DecidableEq τ] (D : τ → Type) [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] (α : Type) [Fintype α] [DecidableEq α] (T : ℕ) : StrictMono (emptyTime D α T) := by
 intro i; exact Fin.elim0 i

end ExactFourier.Packing

end
end

section
namespace ExactFourier.Packing

theorem list_count_get {τ : Type} [DecidableEq τ] (L : List τ) (t : τ) :
 (∑ i : Fin L.length,if L.get i=t then 1 else 0)=L.count t := by
 induction L with
 | nil => simp
 | cons a L ih =>
   simp only [List.length_cons]
   rw [Fin.sum_univ_succ]
   change (if a=t then 1 else 0)+(∑ i : Fin L.length,if L.get i=t then 1 else 0)=_
   rw [ih]
   simp [List.count_cons,add_comm]

theorem list_card_get {τ : Type} [DecidableEq τ] (L : List τ) (t : τ) :
 Fintype.card {i : Fin L.length // L.get i=t}=L.count t := by
 rw [Fintype.card_subtype,Finset.card_filter]
 exact list_count_get L t

theorem list_count_map_get {α τ : Type} [DecidableEq τ] (L : List α) (f : α→τ) (t : τ) :
 (∑ i : Fin L.length,if f (L.get i)=t then 1 else 0)=(L.map f).count t := by
 induction L with
 | nil => simp
 | cons a L ih =>
   simp only [List.length_cons]
   rw [Fin.sum_univ_succ]
   change (if f a=t then 1 else 0)+(∑ i : Fin L.length,if f (L.get i)=t then 1 else 0)=_
   rw [ih]
   simp [List.count_cons,add_comm]

end ExactFourier.Packing

end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {π : Type} [Fintype π] [DecidableEq π]
 {β : π→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]

theorem slot_card_sum (W : ∀ p,FramedWord D (β p)) {T : ℕ}
 (time : ∀ p,Fin (W p).frames.length→Fin T) (ht : ∀ p,Function.Injective (time p))
 (s : Fin T) (t : τ) :
 Fintype.card {p // (slotCall (A := A) (framedSlot (W p) (time p) s)).kind=some t}=
 ∑ p,∑ o : Fin (W p).frames.length,
   if time p o=s ∧ ((W p).frames.get o).type=t then 1 else 0 := by
 rw [slot_card W time ht]
 simp only [Fintype.card_subtype,Finset.card_filter,Fintype.sum_sigma]

theorem slot_card_total (W : ∀ p,FramedWord D (β p)) {T : ℕ}
 (time : ∀ p,Fin (W p).frames.length→Fin T) (ht : ∀ p,Function.Injective (time p)) (t : τ) :
 (∑ s : Fin T,Fintype.card {p // (slotCall (A := A) (framedSlot (W p) (time p) s)).kind=some t})=
 ∑ p,(W p).types.count t := by
 simp_rw [slot_card_sum W time ht]
 rw [Finset.sum_comm]
 apply Finset.sum_congr rfl
 intro p hp
 rw [Finset.sum_comm]
 have he : (∑ o : Fin (W p).frames.length,∑ s : Fin T,
     if time p o=s ∧ ((W p).frames.get o).type=t then 1 else 0)=
     ∑ o : Fin (W p).frames.length,if ((W p).frames.get o).type=t then 1 else 0 := by
  apply Finset.sum_congr rfl
  intro o ho
  simp only [List.get_eq_getElem]
  by_cases h : (W p).frames[o.val].type=t <;> simp [h]
 rw [he]
 exact list_count_map_get (W p).frames Frame.type t

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {π : Type} [Fintype π] [DecidableEq π]
 {β : π→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]
 {ν : Type} [Fintype ν] [DecidableEq ν]

theorem complete_and_pack (k : τ→ℕ) (W : ∀ p,FramedWord D (β p))
 (dummy : ∀ t,FramedWord D (D t))
 (hdummy : ∀ t,(dummy t).matrix (A := A)=1)
 (hdtype : ∀ t (o : Fin (dummy t).frames.length),((dummy t).frames.get o).type=t)
 {T : ℕ} (time : ∀ p,Fin (W p).frames.length→Fin T)
 (htime : ∀ p,StrictMono (time p))
 (hload : ∀ s t,Fintype.card {p //
   (slotCall (A := A) (framedSlot (W p) (time p) s)).kind=some t}≤k t)
 (d : τ→ℕ) (hkd : ∀ t,k t<d t)
 (hdef : ∀ t,k t*T-(∑ p,(W p).types.count t)=d t*(dummy t).frames.length)
 (R : ℕ) (hR : ∑ t,d t*Fintype.card (D t)≤R)
 (hw : Fintype.card (ActiveSpace D k ⊕ ν)≤Fintype.card (Σ p,β p)+R) :
 ∃ V : Word (fun _ : Unit=>ActiveSpace D k ⊕ ν)
   (fun _=>inventoryWithIdentity (A := A) (ν := ν) k) ((Σ p,β p)⊕Fin R),
 V.matrix=Matrix.fromBlocks (Matrix.blockDiagonal' (fun p=>(W p).matrix (A := A))) 0 0 1 ∧
 V.calls.length=T := by
 classical
 let load := fun s t=>Fintype.card {p //
   (slotCall (A := A) (framedSlot (W p) (time p) s)).kind=some t}
 let c := fun t s=>k t-load s t
 have hc : ∀ t s,c t s≤k t := fun _ _=>Nat.sub_le ..
 have hsum : ∀ t,∑ s,c t s=d t*(dummy t).frames.length := by
  intro t
  unfold c
  rw [Finset.sum_tsub_distrib _ (fun s _=>hload s t)]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  rw [Nat.mul_comm T (k t)]
  change k t*T-(∑ s,load s t)=_
  have he := slot_card_total (A := A) W time (fun p=>(htime p).injective) t
  rw [he,hdef t]
 obtain ⟨dt,hdt,hdc⟩ := exists_dummy_framed dummy hdtype c k d hc hkd hsum
 let r := R-∑ t,d t*Fintype.card (D t)
 let E := fun _ : Unit=>emptyFramed D (Fin r)
 let Vd := fun v : Inventory d=>dummy v.1
 let B := sumFramed Vd E
 let bt := sumTime Vd E dt (fun _=>emptyTime D (Fin r) T)
 have hbt : ∀ v,StrictMono (bt v) := sumTime_strict Vd E dt _ hdt (fun _=>emptyTime_strict D _ _)
 have hbc : ∀ s t,Fintype.card {v //
     (slotCall (A := A) (framedSlot (B v) (bt v) s)).kind=some t}=c t s := by
  intro s t
  rw [sum_slot_card]
  change Fintype.card {v : Inventory d //
   (slotCall (A := A) (framedSlot (dummy v.1) (dt v) s)).kind=some t}+
   Fintype.card {v : Unit //
   (slotCall (A := A) (framedSlot (emptyFramed D (Fin r)) (emptyTime D (Fin r) T) s)).kind=some t}=_
  rw [hdc,empty_slot_card,add_zero]
 let Γ := SumDomain (fun v : Inventory d=>D v.1) (fun _ : Unit=>Fin r)
 have hΓ : Fintype.card (Σ v,Γ v)=R := by
  simp only [Fintype.card_sigma,Fintype.sum_sum_type]
  simp only [Γ,SumDomain,Fintype.sum_sigma,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul]
  simp only [Fintype.card_unit,one_mul]
  change (∑ t,∑ _ : Fin (d t),Fintype.card (D t))+r=R
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  exact Nat.add_sub_of_le hR
 let eb : (Σ v,Γ v)≃Fin R := Fintype.equivOfCardEq (hΓ.trans (Fintype.card_fin R).symm)
 let all := sumFramed W B
 let atime := sumTime W B time bt
 have hat : ∀ v,StrictMono (atime v) := sumTime_strict W B time bt htime hbt
 have hac : ∀ s t,Fintype.card {v //
     (slotCall (A := A) (framedSlot (all v) (atime v) s)).kind=some t}=k t := by
  intro s t
  rw [sum_slot_card,hbc]
  exact Nat.add_sub_of_le (hload s t)
 let es := Equiv.sumSigmaDistrib (SumDomain β Γ)
 let e : (Σ v,SumDomain β Γ v)≃((Σ p,β p)⊕Fin R) :=
   es.trans ((Equiv.refl _).sumCongr eb)
 have hwidth : Fintype.card (ActiveSpace D k ⊕ ν)≤Fintype.card (Σ v,SumDomain β Γ v) := by
  rw [Fintype.card_congr e]
  simpa only [Fintype.card_sum,Fintype.card_fin] using hw

 obtain ⟨V,hV,hcount⟩ := packed_schedule k all atime hat hac hwidth
 refine ⟨V.reindex e,?_,by simpa using hcount⟩
 rw [Word.matrix_reindex,hV]
 have hB : Matrix.blockDiagonal' (fun v=>(B v).matrix (A := A))=1 := by
  have hh : (fun v=>(B v).matrix (A := A))=1 := by
   funext v
   cases v with
   | inl v => exact hdummy v.1
   | inr v => exact emptyFramed_matrix D _
  rw [hh]
  exact Matrix.blockDiagonal'_one
 have hydro := matrix_sumFramed (A := A) W B
 rw [hB] at hydro
 change Matrix.reindex ((Equiv.refl _).sumCongr eb) ((Equiv.refl _).sumCongr eb)
   (Matrix.reindex es es (Matrix.blockDiagonal' (fun v=>(all v).matrix (A := A))))=_
 rw [hydro]
 ext x y
 cases x <;> cases y <;> simp [Matrix.reindex_apply,Matrix.one_apply]

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {π : Type} [Fintype π] [DecidableEq π]
 {β : π→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]

theorem cyclicTime_strict
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {π : Type} [Fintype π] [DecidableEq π] {β : π → Type} [(p : π) → Fintype (β p)] [(p : π) → DecidableEq (β p)] (W : ∀ p,FramedWord D (β p)) (m : π→ℕ) (F L : ℕ)
 (hF : 0<F) (hL : ∀ p,(W p).frames.length≤L) (v : Σ p,Fin (m p)) :
 StrictMono (cyclicTime W m F L hF hL v) := by
 intro a b hab
 exact Nat.add_lt_add_left hab _

theorem cyclic_slot_card (W : ∀ p,FramedWord D (β p)) (m : π→ℕ) (F L : ℕ)
 (hF : 0<F) (hL : ∀ p,(W p).frames.length≤L) (s : Fin (F+L-1)) (t : τ) :
 Fintype.card {v : Σ p,Fin (m p) //
   (slotCall (A := A) (framedSlot (W v.1) (cyclicTime W m F L hF hL v) s)).kind=some t}=
 scheduledLoad (fun p=>(W p).types) m F t s.val := by
 rw [slot_card_sum _ _ (fun v=>(cyclicTime_strict W m F L hF hL v).injective)]
 simp only [Fintype.sum_sigma,scheduledLoad]
 apply Finset.sum_congr rfl
 intro p hp
 change (∑ j : Fin (m p),∑ o : Fin (W p).frames.length,
   if cyclicTime W m F L hF hL ⟨p,j⟩ o=s ∧ ((W p).frames.get o).type=t then 1 else 0)=_
 rw [Finset.sum_comm]
 simp only [occurrences,FramedWord.types]
 simp only [Finset.sum_filter,List.get_eq_getElem,List.getElem_map,
   Finset.card_filter,cyclicTime,Fin.ext_iff]
 refine Finset.sum_equiv (finCongr (List.length_map (as := (W p).frames) (f := Frame.type)).symm) (fun _=>by constructor <;> intro _ <;> exact Finset.mem_univ _) ?_
 intro o ho
 by_cases h : ((W p).frames.get o).type=t
 · simp only [List.get_eq_getElem] at h
   simp only [finCongr,Equiv.coe_fn_mk,Fin.val_cast,h,and_true,ite_true]
   rfl
 · simp only [List.get_eq_getElem] at h
   simp only [finCongr,Equiv.coe_fn_mk,Fin.val_cast,h,and_false,ite_false,Finset.sum_const_zero]

theorem cyclic_slot_bound (W : ∀ p,FramedWord D (β p)) (m : π→ℕ) (F L : ℕ)
 (hF : 0<F) (hL : ∀ p,(W p).frames.length≤L) (s : Fin (F+L-1)) (t : τ) :
 (Fintype.card {v : Σ p,Fin (m p) //
   (slotCall (A := A) (framedSlot (W v.1) (cyclicTime W m F L hF hL v) s)).kind=some t} : ℝ)≤
 (∑ p,m p*(W p).types.count t : ℕ)/ (F : ℝ)+∑ p,((W p).frames.length : ℝ) := by
 rw [cyclic_slot_card W m F L hF hL]
 have he : totalCalls (fun p=>(W p).types) m t=∑ p,m p*(W p).types.count t := by
  unfold totalCalls
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  exact (Fintype.card_subtype _).symm.trans (list_card_get _ _)
 have h := scheduledLoad_bound (fun p=>(W p).types) m F hF t s.val
 rw [he] at h
 simpa only [FramedWord.types,List.length_map] using h

end ExactFourier.Packing

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.LiveSectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}

theorem live_matrix_on (k : τ→ℕ) (I : ℕ)
 (x y : LiveSpace D k I⊕(Fin I×Fin I)) :
 Matrix.kronecker (speciesInventory (speciesCopies k I) (speciesMatrix (A := A)))
   (speciesInventory (speciesCopies k I) (speciesMatrix (A := A)))
   (liveCoordinates k I x) (liveCoordinates k I y)=
 Matrix.fromBlocks (liveMatrix (A := A) k I) 0 0 1 x y := by
 rw [inventory_tensor_sectors]
 rcases x with ⟨p,ij,a⟩|ij <;> rcases y with ⟨q,kl,b⟩|kl
 · change Matrix.blockDiagonal' (fun p : Option τ×Option τ=>Matrix.kronecker
     (1 : Matrix (Fin (speciesCopies k I p.1)×Fin (speciesCopies k I p.2))
       (Fin (speciesCopies k I p.1)×Fin (speciesCopies k I p.2)) ℂ)
     (Matrix.kronecker (speciesMatrix (A := A) p.1) (speciesMatrix (A := A) p.2)))
     ⟨p.val,ij,a⟩ ⟨q.val,kl,b⟩=liveMatrix k I ⟨p,ij,a⟩ ⟨q,kl,b⟩
   by_cases h : p=q
   · subst q; rw [Matrix.blockDiagonal'_apply_eq]
     change _=Matrix.blockDiagonal' (fun p : LivePair τ=>Matrix.kronecker
       (1 : Matrix (Fin (speciesCopies k I p.1.1)×Fin (speciesCopies k I p.1.2))
         (Fin (speciesCopies k I p.1.1)×Fin (speciesCopies k I p.1.2)) ℂ)
       (pairMatrix (A := A) p)) ⟨p,ij,a⟩ ⟨p,kl,b⟩
     rw [Matrix.blockDiagonal'_apply_eq]
     rfl
   · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (fun hh=>h (Subtype.ext hh))]
     exact (Matrix.blockDiagonal'_apply_ne (fun p : LivePair τ=>Matrix.kronecker
       (1 : Matrix (Fin (speciesCopies k I p.1.1)×Fin (speciesCopies k I p.1.2))
         (Fin (speciesCopies k I p.1.1)×Fin (speciesCopies k I p.1.2)) ℂ)
       (pairMatrix (A := A) p)) _ _ h).symm
 · change Matrix.blockDiagonal' (fun p : Option τ×Option τ=>Matrix.kronecker
     (1 : Matrix (Fin (speciesCopies k I p.1)×Fin (speciesCopies k I p.2))
       (Fin (speciesCopies k I p.1)×Fin (speciesCopies k I p.2)) ℂ)
     (Matrix.kronecker (speciesMatrix (A := A) p.1) (speciesMatrix (A := A) p.2)))
     ⟨p.val,ij,a⟩ ⟨(none,none),kl,(),()⟩=0
   exact Matrix.blockDiagonal'_apply_ne _ _ _ p.property
 · change Matrix.blockDiagonal' (fun p : Option τ×Option τ=>Matrix.kronecker
     (1 : Matrix (Fin (speciesCopies k I p.1)×Fin (speciesCopies k I p.2))
       (Fin (speciesCopies k I p.1)×Fin (speciesCopies k I p.2)) ℂ)
     (Matrix.kronecker (speciesMatrix (A := A) p.1) (speciesMatrix (A := A) p.2)))
     ⟨(none,none),ij,(),()⟩ ⟨q.val,kl,b⟩=0
   exact Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm q.property)
 · change Matrix.blockDiagonal' (fun p : Option τ×Option τ=>Matrix.kronecker
     (1 : Matrix (Fin (speciesCopies k I p.1)×Fin (speciesCopies k I p.2))
       (Fin (speciesCopies k I p.1)×Fin (speciesCopies k I p.2)) ℂ)
     (Matrix.kronecker (speciesMatrix (A := A) p.1) (speciesMatrix (A := A) p.2)))
     ⟨(none,none),ij,(),()⟩ ⟨(none,none),kl,(),()⟩=(1 : Matrix _ _ ℂ) ij kl
   simp [Matrix.blockDiagonal'_apply_eq,speciesMatrix]

theorem live_matrix_reindex (k : τ→ℕ) (I : ℕ) :
 Matrix.reindex (liveCoordinates k I) (liveCoordinates k I)
   (Matrix.fromBlocks (liveMatrix (A := A) k I) 0 0 (1 : Matrix (Fin I×Fin I) _ ℂ))=
 Matrix.kronecker (speciesInventory (speciesCopies k I) (speciesMatrix (A := A)))
   (speciesInventory (speciesCopies k I) (speciesMatrix (A := A))) := by
 ext x y
 obtain ⟨x,rfl⟩ := (liveCoordinates (D := D) k I).surjective x
 obtain ⟨y,rfl⟩ := (liveCoordinates (D := D) k I).surjective y
 simpa only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply] using
  (live_matrix_on (A := A) k I x y).symm

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {σ π : Type} [Fintype σ] [DecidableEq σ] [Fintype π] [DecidableEq π]
 {E : σ→Type} [∀ s,Fintype (E s)] [∀ s,DecidableEq (E s)]
 {B : ∀ s,Matrix (E s) (E s) ℂ}

theorem copy_fiber_card
    {σ : Type} {π : Type} [Fintype σ] [DecidableEq σ] [Fintype π] [DecidableEq π] (key : π→σ) (m : π→ℕ) (s : σ) :
 Fintype.card {v : Σ p,Fin (m p) // key v.1=s}=∑ p,if key p=s then m p else 0 := by
 rw [Fintype.card_congr (subtypeSigmaAll (fun p (_ : Fin (m p))=>key p=s))]
 simp only [Fintype.card_sigma]
 apply Finset.sum_congr rfl
 intro p hp
 by_cases h : key p=s
 · simp [h]
 · simp [h]

theorem copies_equiv {κ : σ→Type} [∀ s,Fintype (κ s)] [∀ s,DecidableEq (κ s)]
 (key : π→σ) (m : π→ℕ)
 (h : ∀ s,(∑ p,if key p=s then m p else 0)=Fintype.card (κ s)) :
 ∃ e : (Σ v : Σ p,Fin (m p),E (key v.1))≃(Σ v : Σ s,κ s,E v.1),
 Matrix.reindex e e (Matrix.blockDiagonal' (fun v : Σ p,Fin (m p)=>B (key v.1)))=
   Matrix.blockDiagonal' (fun v : Σ s,κ s=>B v.1) := by
 obtain ⟨f,hf⟩ := exists_colorEquiv (fun v : Σ p,Fin (m p)=>key v.1) (fun v : Σ s,κ s=>v.1) (by
  intro s
  rw [copy_fiber_card]
  rw [Fintype.card_congr (sigmaFstFiber κ s)]
  exact h s)
 exact ⟨colorEquiv _ _ f hf,coloredBlock_reindex _ _ f hf⟩

theorem copyCoordinates_matrix
    {σ : Type} [Fintype σ] [DecidableEq σ] {E : σ → Type} [(s : σ) → Fintype (E s)] [(s : σ) → DecidableEq (E s)] {B : (s : σ) → Matrix (E s) (E s) ℂ} (κ : σ→Type) [∀ s,Fintype (κ s)] [∀ s,DecidableEq (κ s)] :
 Matrix.reindex (copyCoordinates (E := E) κ) (copyCoordinates κ)
   (Matrix.blockDiagonal' (fun v : Σ s,κ s=>B v.1))=
 Matrix.blockDiagonal' (fun s=>Matrix.kronecker (1 : Matrix (κ s) _ ℂ) (B s)) := by
 ext ⟨s,i,a⟩ ⟨t,j,b⟩
 change Matrix.blockDiagonal' (fun v : Σ s,κ s=>B v.1) ⟨⟨s,i⟩,a⟩ ⟨⟨t,j⟩,b⟩=_
 by_cases h : s=t
 · subst t
   rw [Matrix.blockDiagonal'_apply_eq]
   by_cases hij : i=j
   · subst j; rw [Matrix.blockDiagonal'_apply_eq]; simp
   · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (fun hh=>hij (eq_of_heq (Sigma.mk.inj_iff.mp hh).2))]
     simp [hij]
 · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (fun hh=>h (congrArg Sigma.fst hh)),
     Matrix.blockDiagonal'_apply_ne _ _ _ h]

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {α : Type} [Fintype α] [DecidableEq α]

theorem embeddedCall_eq {q w : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (e : Fin q↪Fin w) :
 embeddedCall A e=Embedded.matrix e A := by
 classical
 ext i j
 by_cases hi : ∃ a,e a=i
 · obtain ⟨a,rfl⟩ := hi
   by_cases hj : ∃ b,e b=j
   · obtain ⟨b,rfl⟩ := hj
     simp [embeddedCall,e.injective.eq_iff,Embedded.matrix_on]
   · rw [Embedded.matrix_off_col e A _ _ (by simpa [Set.mem_range] using hj)]
     have hij : e a≠j := fun h=>hj ⟨a,h⟩
     simp [embeddedCall,e.injective.eq_iff,hij]
     exact Finset.sum_eq_zero (fun b _=>by simp [show e b≠j from fun h=>hj ⟨b,h⟩])
 · rw [Embedded.matrix_off_row e A _ _ (by simpa [Set.mem_range] using hi)]
   have hz : (∑ a : Fin q,∑ b : Fin q,if e a=i then (if e b=j then A a b else 0) else 0)=0 := by
    apply Finset.sum_eq_zero
    intro a _
    simp [show e a≠i from fun h=>hi ⟨a,h⟩]
   simp only [embeddedCall,hz,hi,not_false_eq_true,and_true,zero_add]

theorem singleStepFin_matrix (e : α≃Fin (Fintype.card α))
 (f : (α×α)≃Fin (Fintype.card α^2)) (A : Matrix α α ℂ)
 (s : Step (fun _ : Unit=>α) (fun _=>A) (α×α)) :
 (singleStepFin e f A s).matrix=Matrix.reindex f f s.matrix := by
 cases s with
 | mono M hM => rfl
 | call t g =>
  simp only [singleStepFin,WordStep.matrix,embeddedCall_eq,Step.matrix]
  rw [← Embedded.matrix_comp,← Embedded.matrix_comp,Embedded.matrix_equiv]
  have he : Matrix.reindex e.symm e.symm (Matrix.reindex e e A)=A := by
   ext i j; simp [Matrix.reindex_apply]
  rw [Embedded.matrix_equiv,he]

theorem squareFinEquiv_tensor
    {α : Type} [Fintype α] [DecidableEq α] (e : α≃Fin (Fintype.card α)) (A : Matrix α α ℂ) :
 Matrix.reindex (squareFinEquiv e) (squareFinEquiv e) (Matrix.kronecker A A)=
 tensorPower (Matrix.reindex e e A) 2 := by
 ext i j
 simp [squareFinEquiv,Matrix.reindex_apply,tensorPower,Fin.prod_univ_two]

theorem square_win_implies_finite_win (A : Matrix α α ℂ) (hA : IsUnit A)
 (hna : ¬MonomialMatrix A)
 (W : Word (fun _ : Unit=>α) (fun _=>A) (α×α))
 (hW : W.matrix=Matrix.kronecker A A) (hc : W.calls.length<2*Fintype.card α) :
 FiniteWinStatement := by
 let q := Fintype.card α
 let e := Fintype.equivFin α
 let f := squareFinEquiv e
 let V := (W.map (singleStepFin e f A)).reverse
 refine ⟨q,Matrix.reindex e e A,?_,?_,2,by omega,V,?_,?_⟩
 · exact hA.map (Matrix.reindexAlgEquiv ℂ ℂ e).toMonoidHom
 · intro hm
   have h := (show MonomialMatrix (Matrix.reindex e e A) from hm).reindex e.symm
   apply hna
   have he : Matrix.reindex e.symm e.symm (Matrix.reindex e e A)=A := by
    ext i j; simp [Matrix.reindex_apply]
   rw [he] at h
   exact h
 · simp only [wordMatrix,V,List.map_reverse,List.reverse_reverse,List.map_map]
   simp only [Function.comp_def,singleStepFin_matrix]
   rw [show W.map (fun x=>Matrix.reindex f f x.matrix)=
     (W.map Step.matrix).map (Matrix.reindexAlgEquiv ℂ ℂ f).toMonoidHom from (List.map_map ..).symm]
   rw [← map_list_prod]
   change Matrix.reindex f f W.matrix=_
   rw [hW]
   exact squareFinEquiv_tensor e A
 · have he : (W.map (fun s=>(singleStepFin e f A s).calls)).sum=W.calls.length := by
    clear hW hc V
    induction W with
    | nil => rfl
    | cons s W ih =>
      cases s with
      | mono M hm => simpa only [List.map_cons,List.sum_cons,singleStepFin,WordStep.calls,
          Word.calls,List.filterMap_cons,Step.kind,zero_add] using ih
      | call t g =>
        change 1+(W.map (fun s=>(singleStepFin e f A s).calls)).sum=(Word.calls W).length+1
        omega
   simpa only [wordCalls,V,List.map_reverse,List.sum_reverse,List.map_map,Function.comp_def,he,
     Nat.reduceSub,pow_one] using hc

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {π : Type} [Fintype π] [DecidableEq π]

theorem family_square_win (k : τ→ℕ) (I : ℕ)
 (key : π→LivePair τ) (W : ∀ p,FramedWord D (PairDomain D (key p))) (m : π→ℕ)
 (hW : ∀ p,(W p).matrix (A := A)=pairMatrix (A := A) (key p))
 (hnum : ∀ s,(∑ p,if key p=s then m p else 0)=
   speciesCopies k I s.1.1*speciesCopies k I s.1.2)
 (dummy : ∀ t,FramedWord D (D t))
 (hdummy : ∀ t,(dummy t).matrix (A := A)=1)
 (hdtype : ∀ t (o : Fin (dummy t).frames.length),((dummy t).frames.get o).type=t)
 {T : ℕ} (time : ∀ v : Σ p,Fin (m p),Fin (W v.1).frames.length→Fin T)
 (htime : ∀ v,StrictMono (time v))
 (hload : ∀ s t,Fintype.card {v : Σ p,Fin (m p) //
   (slotCall (A := A) (framedSlot (W v.1) (time v) s)).kind=some t}≤k t)
 (d : τ→ℕ) (hkd : ∀ t,k t<d t)
 (hdef : ∀ t,k t*T-(∑ p,m p*(W p).types.count t)=d t*(dummy t).frames.length)
 (hR : ∑ t,d t*Fintype.card (D t)≤I^2)
 (hJ : IsUnit (inventoryWithIdentity (A := A) (ν := Fin I) k))
 (hnJ : ¬MonomialMatrix (inventoryWithIdentity (A := A) (ν := Fin I) k))
 (hT : T<2*Fintype.card (ActiveSpace D k⊕Fin I)) : FiniteWinStatement := by
 classical
 let κ := fun s : LivePair τ=>Fin (speciesCopies k I s.1.1)×Fin (speciesCopies k I s.1.2)
 obtain ⟨ec,hec⟩ := copies_equiv (B := pairMatrix (A := A)) (κ := κ) key m
   (by intro s; simpa [κ] using hnum s)
 let ep := ec.trans (copyCoordinates κ)
 have hep : Matrix.reindex ep ep (Matrix.blockDiagonal' (fun v : Σ p,Fin (m p)=>(W v.1).matrix (A := A)))=
   liveMatrix (A := A) k I := by
  simp only [hW]
  rw [← reindex_comp,hec,copyCoordinates_matrix]
  rfl
 let er : Fin (I^2)≃(Fin I×Fin I) := (finCongr (pow_two I)).trans finProdFinEquiv.symm
 let ej := speciesCoordinates (D := D) k I
 let e := ((ep.sumCongr er).trans (liveCoordinates k I)).trans (ej.symm.prodCongr ej.symm)
 have he : Matrix.reindex e e
   (Matrix.fromBlocks (Matrix.blockDiagonal' (fun v : Σ p,Fin (m p)=>(W v.1).matrix (A := A))) 0 0
     (1 : Matrix (Fin (I^2)) _ ℂ))=
   Matrix.kronecker (inventoryWithIdentity (A := A) (ν := Fin I) k)
     (inventoryWithIdentity (A := A) (ν := Fin I) k) := by
  rw [show e=((ep.sumCongr er).trans (liveCoordinates k I)).trans (ej.symm.prodCongr ej.symm) from rfl,
    ← reindex_comp,← reindex_comp,reindex_sum,hep]
  rw [show Matrix.reindex er er (1 : Matrix (Fin (I^2)) _ ℂ)=1 from (Matrix.reindexAlgEquiv ℂ ℂ er).map_one]
  rw [live_matrix_reindex,reindex_tensor,← speciesCoordinates_matrix]
  rw [reindex_inverse]
 have hw : Fintype.card (ActiveSpace D k⊕Fin I)≤
     Fintype.card (Σ v : Σ p,Fin (m p),PairDomain D (key v.1))+I^2 := by
  have hc := Fintype.card_congr e
  simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_prod] at hc
  have hh : ∀ n : ℕ,n≤n*n := by intro n; nlinarith
  rw [hc]
  simpa only [Fintype.card_sum,Fintype.card_fin] using hh (Fintype.card (ActiveSpace D k⊕Fin I))
 have hd : ∀ t,k t*T-(∑ v : Σ p,Fin (m p),(W v.1).types.count t)=d t*(dummy t).frames.length := by
  intro t
  have hs : (∑ v : Σ p,Fin (m p),(W v.1).types.count t)=∑ p,m p*(W p).types.count t := by
   rw [Fintype.sum_sigma]
   apply Finset.sum_congr rfl
   intro p hp
   change (∑ j : Fin (m p),(W p).types.count t)=_
   simp
  rw [hs]
  exact hdef t
 obtain ⟨V,hV,hcount⟩ := complete_and_pack (ν := Fin I) k (fun v : Σ p,Fin (m p)=>W v.1)
   dummy hdummy hdtype time htime hload d hkd hd (I^2) hR hw
 apply square_win_implies_finite_win _ hJ hnJ (V.reindex e)
 · rw [Word.matrix_reindex,hV]
   exact he
 · simpa [hcount] using hT

end ExactFourier.Packing

end
end

section
namespace ExactFourier.Packing

/-- Quantitative slack for the deterministic cyclic schedule, using square sectors. -/
theorem square_schedule_margin {K W G S u F L C : ℝ}
 (hK : 1≤K) (hS : 2*K≤S) (hu : L+2*C*W≤u)
 (hu0 : 0≤u) (hC : 0≤C) (hW : 0≤W)
 (hGF : G+S=2*K*W) (hF : F=(2*W-1)*u+1-L) (hFu : F≤2*W*u) :
 G*u^2+C*F≤K*u*F := by
 have hG : G=2*K*W-S := by linarith
 have he : K*u*F-G*u^2-C*F=
   (S-2*K)*u^2+K*u*(u-L-2*C*W)+2*C*W*u*(K-1)+K*u+C*(2*W*u-F) := by
  rw [hG,hF]
  ring
 have h1 : 0≤(S-2*K)*u^2 := mul_nonneg (sub_nonneg.mpr hS) (sq_nonneg u)
 have h2 : 0≤K*u*(u-L-2*C*W) := mul_nonneg
   (mul_nonneg (by linarith) hu0) (by linarith)
 have h3 : 0≤2*C*W*u*(K-1) := mul_nonneg (by positivity) (by linarith)
 have h4 : 0≤K*u := mul_nonneg (by linarith) hu0
 have h5 : 0≤C*(2*W*u-F) := mul_nonneg hC (sub_nonneg.mpr hFu)
 linarith

theorem square_inventory_parameters {K W G S h u L C : ℕ}
 (hK : 0<K) (hW : 0<W) (hh : 0<h)
 (hS : 2*K≤S) (hGS : G+S=2*K*W)
 (hdK : h∣K) (hdS : h∣S)
 (hu : L+2*C*W≤u) (huh : h<u) :
 let T := (2*W-1)*u
 let F := T+1-L
 0<F ∧ F+L-1=T ∧ T<2*(W*u) ∧
 (G*u^2 : ℝ)/(F : ℝ)+(C : ℝ)≤(K*u : ℕ) ∧
 ∃ d : ℕ,K*u<d ∧ K*u*T-G*u^2=d*h ∧ d≤K*u*T := by
 dsimp
 let T := (2*W-1)*u
 let F := T+1-L
 change 0<F ∧ F+L-1=T ∧ T<2*(W*u) ∧
  (G*u^2 : ℝ)/(F : ℝ)+(C : ℝ)≤(K*u : ℕ) ∧
  ∃ d : ℕ,K*u<d ∧ K*u*T-G*u^2=d*h ∧ d≤K*u*T
 have hu0 : 0<u := hh.trans huh
 have hLu : L≤u := (Nat.le_add_right L _).trans hu
 have hcoeff : 1≤2*W-1 := by omega
 have huT : u≤T := by simpa only [one_mul] using Nat.mul_le_mul_right u hcoeff
 have hLF : L≤T := hLu.trans huT
 have hF : F+L=T+1 := Nat.sub_add_cancel (hLF.trans (Nat.le_succ T))
 have hFp : 0<F := by omega
 have hT : T+u=2*W*u := by
  dsimp [T]
  calc
   (2*W-1)*u+u=((2*W-1)+1)*u := by ring
   _ = 2*W*u := ?_
  congr 1
  omega
 have hFu : F≤2*W*u := by omega
 have hKr : (1 : ℝ)≤K := by exact_mod_cast hK
 have hFr : (F : ℝ)=(2*(W : ℝ)-1)*u+1-L := by
  have ht : (T : ℝ)+(u : ℝ)=2*(W : ℝ)*u := by exact_mod_cast hT
  have hf : (F : ℝ)+(L : ℝ)=(T : ℝ)+1 := by exact_mod_cast hF
  nlinarith
 have hmargin : (G : ℝ)*(u : ℝ)^2+(C : ℝ)*F≤(K : ℝ)*u*F :=
  square_schedule_margin (S := (S : ℝ)) hKr (by exact_mod_cast hS) (by exact_mod_cast hu)
   (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
   (by exact_mod_cast hGS) hFr (by exact_mod_cast hFu)
 have hdiv : (G*u^2 : ℝ)/(F : ℝ)+(C : ℝ)≤(K*u : ℕ) := by
  have hh := (div_le_iff₀ (show (0 : ℝ)<F by exact_mod_cast hFp)).mpr hmargin
  simpa only [add_div,mul_div_cancel_right₀ _ (by positivity : (F : ℝ)≠0),Nat.cast_mul] using hh
 refine ⟨hFp,by omega,by nlinarith, hdiv,?_⟩
 have hKS : K≤S := by omega
 have hd : h∣S-K := Nat.dvd_sub hdS hdK
 obtain ⟨e,he⟩ := hd
 let d := e*u^2
 have hD : d*h=(S-K)*u^2 := by dsimp [d]; rw [he]; ring
 have hSK : K≤S-K := by omega
 have hlt : K*u*h<d*h := by
  rw [hD]
  have h1 : K*u*h<K*u*u := Nat.mul_lt_mul_of_pos_left huh (Nat.mul_pos hK hu0)
  have h2 : K*u*u≤(S-K)*u^2 := by
   calc K*u*u=K*u^2 := by ring
        _ ≤(S-K)*u^2 := Nat.mul_le_mul_right _ hSK
  exact h1.trans_le h2
 have hdk : K*u<d := (Nat.mul_lt_mul_right hh).mp hlt
 have hEq : G*u^2+d*h=K*u*T := by
  rw [hD]
  have heq : G+(S-K)+K=2*K*W := by omega
  have heq' := congrArg (fun n=>n*u^2) heq
  have ht' := congrArg (fun n=>K*u*n) hT
  nlinarith [heq',ht']
 refine ⟨d,hdk,?_,?_⟩
 · omega
 · have hdle : d≤d*h := by simpa using Nat.mul_le_mul_left d hh
   exact hdle.trans (by omega)

end ExactFourier.Packing

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.InventoryValidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}

theorem inventory_card
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] (k : τ→ℕ) (I : ℕ) :
 Fintype.card (ActiveSpace D k⊕Fin I)=(∑ t,k t*Fintype.card (D t))+I := by
 rw [Fintype.card_sum,Fintype.card_fin,Fintype.card_sigma,Fintype.sum_sigma]
 congr 1
 apply Finset.sum_congr rfl
 intro t ht
 change (∑ j : Fin (k t),Fintype.card (D t))=_
 simp

theorem inventory_unit (hA : ∀ t,IsUnit (A t)) (k : τ→ℕ) (I : ℕ) :
 IsUnit (inventoryWithIdentity (A := A) (ν := Fin I) k) := by
 apply Matrix.isUnit_fromBlocks_zero₂₁.mpr
 refine ⟨?_,isUnit_one⟩
 exact (Pi.isUnit_iff.mpr (fun i : Inventory k=>hA i.1)).map (Matrix.blockDiagonal'RingHom (fun i : Inventory k=>D i.1) ℂ)

theorem inventory_not_monomial (hA : ∀ t,IsUnit (A t)) (k : τ→ℕ) (I : ℕ)
 (t : τ) (hk : 0<k t) (hn : ¬MonomialMatrix (A t)) :
 ¬MonomialMatrix (inventoryWithIdentity (A := A) (ν := Fin I) k) := by
 intro h
 let e : D t ↪ ActiveSpace D k⊕Fin I :=
  (Embedded.sigmaIn (β := fun i : Inventory k=>D i.1) ⟨t,⟨0,hk⟩⟩).trans Function.Embedding.inl
 have he : (inventoryWithIdentity (A := A) (ν := Fin I) k).submatrix e e=A t := by
  ext i j
  change Matrix.blockDiagonal' (fun i : Inventory k=>A i.1) ⟨⟨t,⟨0,hk⟩⟩,i⟩ ⟨⟨t,⟨0,hk⟩⟩,j⟩=A t i j
  exact Matrix.blockDiagonal'_apply_eq _ _ _ _
 apply hn
 rw [← he]
 exact h.submatrix_unit e e (he.symm ▸ hA t)

theorem exists_positive_dummy
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} (hA : ∀ t,IsUnit (A t)) (t : τ) :
 ∃ W : FramedWord D (D t),0<W.frames.length ∧ W.matrix (A := A)=1 ∧
    ∀ o : Fin W.frames.length,(W.frames.get o).type=t := by
 by_cases hn : MonomialMatrix (A t)
 · let W : Word D A (D t) := callWord t (Function.Embedding.refl _)++monoWord (A t)⁻¹ hn.inverse
   have hm : W.matrix=1 := by
    rw [Word.matrix_append,matrix_callWord,matrix_monoWord]
    have he : Embedded.matrix (Function.Embedding.refl (D t)) (A t)=A t := by
     ext i j; exact Embedded.matrix_on (Function.Embedding.refl _) _ i j
    rw [he]
    exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hA t))
   refine ⟨W.framed,?_,(Word.matrix_framed W).trans hm,?_⟩
   · simp [W,Word.framed,callWord,monoWord,FramedWord.pre]
   · intro o
     have h : W.framed.types=[t] := by simp [W]
     have hh : (W.framed.frames.get o).type∈W.framed.types := List.mem_map.mpr ⟨_,List.get_mem _ _,rfl⟩
     simpa [h] using hh
 · obtain ⟨h,hh,hgen⟩ := PositiveGeneration.positive_generation (A t) (hA t) hn
   obtain ⟨W,hm,hc⟩ := pattern_word t (hgen 1 isUnit_one)
   have hl : W.framed.frames.length=h := by
    have hlen := congrArg List.length ((Word.types_framed W).trans hc)
    simpa [FramedWord.types] using hlen
   refine ⟨W.framed,hl.symm ▸ hh,(Word.matrix_framed W).trans hm,?_⟩
   intro o
   have ht : W.framed.types=List.replicate h t := (Word.types_framed W).trans hc
   have hmem : (W.framed.frames.get o).type∈W.framed.types := by
    exact List.mem_map.mpr ⟨_,List.get_mem _ _,rfl⟩
   rw [ht,List.mem_replicate] at hmem
   exact hmem.2

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {π : Type} [Fintype π] [DecidableEq π]

theorem scalable_square_win (hA : ∀ t,IsUnit (A t)) (k : τ→ℕ) (I : ℕ)
 (hk : ∀ t,0<k t) (anchor : τ) (hn : ¬MonomialMatrix (A anchor))
 (key : π→LivePair τ) (P : ∀ p,FramedWord D (PairDomain D (key p))) (m : π→ℕ)
 (hP : ∀ p,(P p).matrix (A := A)=pairMatrix (A := A) (key p))
 (hnum : ∀ s,(∑ p,if key p=s then m p else 0)=
   speciesCopies k I s.1.1*speciesCopies k I s.1.2)
 (dummy : ∀ t,FramedWord D (D t)) (hdpos : ∀ t,0<(dummy t).frames.length)
 (hdummy : ∀ t,(dummy t).matrix (A := A)=1)
 (hdtype : ∀ t (o : Fin (dummy t).frames.length),((dummy t).frames.get o).type=t)
 (S : τ→ℕ) (hS : ∀ t,2*k t≤S t)
 (hGS : ∀ t,(∑ p,m p*(P p).types.count t)+S t=
    2*k t*((∑ i,k i*Fintype.card (D i))+I))
 (hdK : ∀ t,(dummy t).frames.length∣k t) (hdS : ∀ t,(dummy t).frames.length∣S t)
 (hreservoir : 2*(∑ t,k t*Fintype.card (D t))*((∑ t,k t*Fintype.card (D t))+I)≤I^2) :
 FiniteWinStatement := by
 classical
 let W := (∑ t,k t*Fintype.card (D t))+I
 have hW : 0<W := by
  by_contra hh
  have hzero : W=0 := by omega
  have hc := inventory_not_monomial hA k I anchor (hk anchor) hn
  have hz : Fintype.card (ActiveSpace D k⊕Fin I)=0 := by
   rw [inventory_card]
   exact hzero
  let : IsEmpty (ActiveSpace D k⊕Fin I) := Fintype.card_eq_zero_iff.mp hz
  apply hc
  refine ⟨Equiv.refl _,fun _=>1,fun _=>one_ne_zero,?_⟩
  intro i
  exact isEmptyElim i
 let C := ∑ p,(P p).frames.length
 let L := C+1
 let u := L+2*C*W+(∑ t,(dummy t).frames.length)+1
 have hu : L+2*C*W≤u := by omega
 have huh : ∀ t,(dummy t).frames.length<u := by
  intro t
  have h := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ t) (f := fun t=>(dummy t).frames.length)
  dsimp [u]
  omega
 let T := (2*W-1)*u
 let F := T+1-L
 have hp := fun t=>square_inventory_parameters (hk t) hW (hdpos t) (hS t) (hGS t) (hdK t) (hdS t) hu (huh t)
 have hF : 0<F := (hp anchor).1
 have hFT : F+L-1=T := (hp anchor).2.1
 have hTu : T<2*(W*u) := (hp anchor).2.2.1
 have hbound : ∀ t,((∑ p,m p*(P p).types.count t)*u^2 : ℝ)/(F : ℝ)+(C : ℝ)≤(k t*u : ℕ) :=
  fun t=>(hp t).2.2.2.1
 choose d hkd hdef hdle using fun t=>(hp t).2.2.2.2
 let m' := fun p=>m p*u^2
 have hcount : ∀ t,(∑ p,m' p*(P p).types.count t)=(∑ p,m p*(P p).types.count t)*u^2 := by
  intro t
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intros
  dsimp [m']
  ring
 have hL : ∀ p,(P p).frames.length≤L := by
  intro p
  exact (Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ p)).trans (Nat.le_succ C)
 let time := cyclicTime P m' F L hF hL
 have ht : ∀ v,StrictMono (time v) := cyclicTime_strict P m' F L hF hL
 have hl : ∀ s t,Fintype.card {v : Σ p,Fin (m' p) //
   (slotCall (A := A) (framedSlot (P v.1) (time v) s)).kind=some t}≤k t*u := by
  intro s t
  have hb := cyclic_slot_bound (A := A) P m' F L hF hL s t
  rw [hcount] at hb
  have hc : (∑ p,((P p).frames.length : ℝ))=(C : ℝ) := by simp [C]
  rw [hc] at hb
  simp only [Nat.cast_mul,Nat.cast_pow] at hb
  have hb' := hb.trans (hbound t)
  exact_mod_cast hb'
 have hR : ∑ t,d t*Fintype.card (D t)≤(I*u)^2 := by
  calc
   _ ≤∑ t,(k t*u*T)*Fintype.card (D t) := Finset.sum_le_sum (fun t _=>Nat.mul_le_mul_right _ (hdle t))
   _ = (∑ t,k t*Fintype.card (D t))*(u*T) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intros
    ring
   _ ≤ (∑ t,k t*Fintype.card (D t))*(u*(2*(W*u))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hTu.le)
   _ = (2*(∑ t,k t*Fintype.card (D t))*W)*u^2 := by ring
   _ ≤ I^2*u^2 := Nat.mul_le_mul_right _ hreservoir
   _ = (I*u)^2 := by ring
 refine family_square_win (fun t=>k t*u) (I*u) key P m' hP ?_ dummy hdummy hdtype time ht hl d hkd ?_ hR
   (inventory_unit hA _ _) (inventory_not_monomial hA _ _ anchor (Nat.mul_pos (hk anchor) (lt_trans (hdpos anchor) (huh anchor))) hn) ?_
 · intro s
   have he : ∀ a : Option τ,speciesCopies (fun t=>k t*u) (I*u) a=speciesCopies k I a*u := by intro a; cases a <;> rfl
   simp only [he]
   calc
    (∑ p,if key p=s then m' p else 0)=(∑ p,if key p=s then m p else 0)*u^2 := by
     rw [Finset.sum_mul]
     apply Finset.sum_congr rfl
     intro p hp
     dsimp [m']
     split_ifs <;> simp
    _ = _ := by rw [hnum]; ring
 · intro t
   rw [hcount,hFT]
   exact hdef t
 · rw [hFT]
   have hw : Fintype.card (ActiveSpace D (fun t=>k t*u)⊕Fin (I*u))=W*u := by
    rw [inventory_card]
    dsimp [W]
    rw [add_mul,Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intros
    ring
   rw [hw]
   exact hTu

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing

/-- Strict comparison positivity is preserved by sufficiently fine downward rational rounding. -/
theorem integral_positive_combination {ρ τ : Type} [Fintype ρ] [Fintype τ]
 (Δ : ρ→τ→ℤ) (lam : ρ→ℝ) (hlam : ∀ r,0≤lam r)
 (hpos : ∀ t,0<∑ r,lam r*(Δ r t : ℝ)) :
 ∃ l : ρ→ℕ,∀ t,0<∑ r,(l r : ℤ)*Δ r t := by
 classical
 let s := fun t=>∑ r,lam r*(Δ r t : ℝ)
 let B := fun t=>∑ r,|(Δ r t : ℝ)|
 have hn : ∀ t,∃ n : ℕ,B t<(n : ℝ)*s t := by
  intro t
  obtain ⟨n,hn⟩ := exists_nat_gt (B t/s t)
  exact ⟨n,(div_lt_iff₀ (hpos t)).mp hn⟩
 choose n hn using hn
 let N := (∑ t,n t)+1
 have hN : ∀ t,B t<(N : ℝ)*s t := by
  intro t
  have hnt : n t≤N := by
   exact (Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ t)).trans (Nat.le_add_right _ _)
  exact (hn t).trans_le (mul_le_mul_of_nonneg_right (by exact_mod_cast hnt) (hpos t).le)
 let l := fun r=>⌊(N : ℝ)*lam r⌋₊
 refine ⟨l,?_⟩
 intro t
 have hround : ∀ r,(N : ℝ)*lam r*(Δ r t : ℝ)-|(Δ r t : ℝ)|≤(l r : ℝ)*(Δ r t : ℝ) := by
  intro r
  have hx : 0≤(N : ℝ)*lam r := mul_nonneg (Nat.cast_nonneg _) (hlam r)
  have hlo : (N : ℝ)*lam r<(l r : ℝ)+1 := Nat.lt_floor_add_one _
  have hhi : (l r : ℝ)≤(N : ℝ)*lam r := Nat.floor_le hx
  by_cases hd : 0≤(Δ r t : ℝ)
  · rw [abs_of_nonneg hd]
    have hh := mul_le_mul_of_nonneg_right (show (N : ℝ)*lam r-1≤(l r : ℝ) by linarith) hd
    nlinarith
  · have hd' : (Δ r t : ℝ)≤0 := le_of_not_ge hd
    rw [abs_of_nonpos hd']
    have hh := mul_le_mul_of_nonpos_right hhi hd'
    nlinarith
 have hs := Finset.sum_le_sum (s := Finset.univ) (fun r _=>hround r)
 have he : (∑ r,((N : ℝ)*lam r*(Δ r t : ℝ)-|(Δ r t : ℝ)|))=(N : ℝ)*s t-B t := by
  simp only [s,B,Finset.sum_sub_distrib,Finset.mul_sum,mul_assoc]
 rw [he] at hs
 have hp : 0<∑ r,(l r : ℝ)*(Δ r t : ℝ) := by linarith [hN t]
 exact_mod_cast hp

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {ρ : Type} [Fintype ρ] [DecidableEq ρ]

theorem integer_comparison_win (hA : ∀ t,IsUnit (A t))
 (anchor : τ) (hn : ¬MonomialMatrix (A anchor))
 (c : ρ→PairComparison (A := A)) (l : ρ→ℕ)
 (hpos : ∀ t,0<∑ r,(l r : ℤ)*(c r).delta t) : FiniteWinStatement := by
 classical
 choose dummy hdpos hdm hdt using exists_positive_dummy hA
 let h := fun t=>(dummy t).frames.length
 let H := ∏ t,h t
 have hH : 0<H := Finset.prod_pos (fun t _=>hdpos t)
 have hdH : ∀ t,h t∣H := fun t=>Finset.dvd_prod_of_mem _ (Finset.mem_univ t)
 let Z := 2*(∑ r,l r)+1
 have hZ : 0<Z := by dsimp [Z]; omega
 let K := Z*H
 let B := ∑ t,Fintype.card (D t)
 let R := H*B
 let I0 := 4*R+H+1
 let I := Z*I0
 let k : τ→ℕ := fun _=>K
 let n := fun p : LivePair τ=>speciesCopies k I p.1.1*speciesCopies k I p.1.2
 let a := fun r=>Z*2*H*l r
 let s : τ→ℕ := fun t=>(∑ r,(l r : ℤ)*(c r).delta t).toNat
 have hs : ∀ t,(s t : ℤ)=∑ r,(l r : ℤ)*(c r).delta t := by
  intro t; exact Int.toNat_of_nonneg (hpos t).le
 have hsp : ∀ t : τ,(1 : ℕ)≤ s t := by
  intro t
  have hh := hpos t
  rw [← hs] at hh
  exact_mod_cast hh
 let S := fun t=>2*K*s t
 have hcap : ∀ p,(∑ r,if (c r).pair=p then a r else 0)≤n p := by
  intro p
  have hIK : K≤I := by
   dsimp [K,I,I0]
   exact Nat.mul_le_mul_left Z (by omega)
  have hmin : ∀ x : Option τ,K ≤ speciesCopies k I x := by
   intro x; cases x with
   | none => exact hIK
   | some t => exact le_rfl
  have hKK : (∑ r,a r)≤K*K := by
   have he : (∑ r,a r)=Z*2*H*(∑ r,l r) := by simp only [a,Finset.mul_sum]
   rw [he]
   have hL : 2*(∑ r,l r)≤Z*H := by
    have hz : 2*(∑ r,l r)≤Z := by dsimp [Z]; omega
    exact hz.trans (by simpa using Nat.mul_le_mul_left Z hH)
   calc
    Z*2*H*(∑ r,l r)=K*(2*(∑ r,l r)) := by dsimp [K]; ring
    _ ≤ K*(Z*H) := Nat.mul_le_mul_left _ hL
    _ = K*K := rfl
  calc
   (∑ r,if (c r).pair=p then a r else 0)≤∑ r,a r := Finset.sum_le_sum (fun r _=>by split_ifs <;> omega)
   _ ≤ K*K := hKK
   _ ≤ n p := Nat.mul_le_mul (hmin _) (hmin _)
 let m := familyMultiplicity c n a
 have hsave : ∀ t,(∑ p,m p*(familyProgram c p).types.count t)+S t=
    2*k t*((∑ i,k i*Fintype.card (D i))+I) := by
  intro t
  have he := family_saving c n a hcap t
  have hn : (∑ p,(n p : ℤ)*pairBaseline (D := D) p t)=
    (2*k t*((∑ i,k i*Fintype.card (D i))+I) : ℕ) := by
   exact_mod_cast pair_baseline_sum (D := D) k I t
  have ha : (∑ r,(a r : ℤ)*(c r).delta t)=(S t : ℤ) := by
   simp only [a,Nat.cast_mul,Nat.cast_ofNat,S]
   rw [hs]
   dsimp [K]

   simp only [Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro r hr
   ring
  rw [hn,ha] at he
  have hm : (∑ p,(m p : ℤ)*(familyProgram c p).types.count t)=
      ((∑ p,m p*(familyProgram c p).types.count t : ℕ) : ℤ) := by push_cast; rfl
  rw [hm] at he
  have hh : ((∑ p,m p*(familyProgram c p).types.count t : ℕ) : ℤ)+(S t : ℤ)=
      ((2*k t*((∑ i,k i*Fintype.card (D i))+I) : ℕ) : ℤ) := by omega
  exact_mod_cast hh
 have hR : 2*(∑ t,k t*Fintype.card (D t))*((∑ t,k t*Fintype.card (D t))+I)≤I^2 := by
  have he : (∑ t,k t*Fintype.card (D t))=Z*R := by
   simp only [k,← Finset.mul_sum]
   dsimp [K,R,B]
   ring
  rw [he]
  have hi : 2*R*(R+I0)≤I0^2 := by dsimp [I0]; nlinarith
  have hh := Nat.mul_le_mul_left (Z^2) hi
  dsimp [I]
  nlinarith only [hh]
 apply scalable_square_win hA k I (fun _=>Nat.mul_pos hZ hH) anchor hn
   (familyKey c) (familyProgram c) m (familyProgram_matrix c)
   (familyMultiplicity_key c n a hcap) dummy hdpos hdm hdt S _ hsave _ _ hR
 · intro t
   dsimp [S,k]
   simpa only [mul_one] using Nat.mul_le_mul_left (2*K) (hsp t)
 · intro t
   exact dvd_mul_of_dvd_right (hdH t) Z
 · intro t
   exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (hdH t) Z) 2) (s t)

theorem positive_comparison_win (hA : ∀ t,IsUnit (A t))
 (anchor : τ) (hn : ¬MonomialMatrix (A anchor))
 (c : ρ→PairComparison (A := A)) (lam : ρ→ℝ) (hlam : ∀ r,0≤lam r)
 (hpos : ∀ t,0<∑ r,lam r*((c r).delta t : ℝ)) : FiniteWinStatement := by
 obtain ⟨l,hl⟩ := integral_positive_combination (fun r=>(c r).delta) lam hlam hpos
 exact integer_comparison_win hA anchor hn c l hl

end ExactFourier.Packing

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.FiniteSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.Packing
open scoped Pointwise

/-- Finite comparison alternative, exactly the separator needed for no-win prices. -/
theorem finite_separator {ρ τ : Type} [Fintype ρ] [Fintype τ] [Nonempty τ]
 (Δ : ρ→τ→ℝ)
 (hn : ¬∃ lam : ρ→ℝ,(∀ r,0≤lam r) ∧ ∀ t,0<∑ r,lam r*Δ r t) :
 ∃ v : τ→ℝ,(∀ t,0≤v t) ∧ (∃ t,0<v t) ∧ ∀ r,∑ t,v t*Δ r t≤0 := by
 classical
 let C : Set (τ→ℝ) := {x | ∃ lam : ρ→ℝ,(∀ r,0≤lam r) ∧ x=∑ r,lam r • Δ r}
 let O : Set (τ→ℝ) := {x | ∀ t,0<x t}
 have hC : Convex ℝ C := by
  intro x hx y hy a b ha hb hab
  obtain ⟨lam,hl,rfl⟩ := hx
  obtain ⟨mu,hm,rfl⟩ := hy
  refine ⟨fun r=>a*lam r+b*mu r,fun r=>add_nonneg (mul_nonneg ha (hl r)) (mul_nonneg hb (hm r)),?_⟩
  simp [Finset.smul_sum,add_smul,smul_smul,Finset.sum_add_distrib]
 have hO : Convex ℝ O := by
  intro x hx y hy a b ha hb hab t
  change 0<a*x t+b*y t
  have h1 := mul_nonneg ha (hx t).le
  have h2 := mul_nonneg hb (hy t).le
  rcases lt_or_eq_of_le ha with hp|hp
  · exact add_pos_of_pos_of_nonneg (mul_pos hp (hx t)) h2
  · have hb' : b=1 := by linarith
    simp [← hp,hb',hy t]
 have ho : IsOpen O := by
  rw [show O=⋂ t : τ,{x : τ→ℝ | 0<x t} by ext x; simp [O]]
  exact isOpen_iInter_of_finite (fun t=>isOpen_lt continuous_const (continuous_apply t))
 have hzC : (0 : τ→ℝ)∈C := ⟨0,fun _=>le_rfl,by simp⟩
 have hzero : (0 : τ→ℝ)∉O-C := by
  rintro ⟨x,hx,y,⟨lam,hl,hy⟩,he⟩
  have heq : x=y := sub_eq_zero.mp he
  apply hn
  refine ⟨lam,hl,?_⟩
  intro t
  have hh := hx t
  rw [heq,hy] at hh
  simpa using hh
 obtain ⟨f,hf⟩ := geometric_hahn_banach_point_open (hO.sub hC) (ho.sub_right) hzero
 have hfone : 0<f (fun _ : τ=>1) := by
  simpa only [map_zero] using hf _ (show (fun _ : τ=>1)∈O-C from ⟨_,fun _=>zero_lt_one,0,hzC,by simp⟩)
 have hrep : ∀ x : τ→ℝ,f x=∑ t,x t*f (Pi.single t 1) := by
  intro x
  have he : x=∑ t,x t • Pi.single t (1 : ℝ) := by ext i; simp [Pi.single_apply]
  calc
   f x=f (∑ t,x t • Pi.single t (1 : ℝ)) := congrArg f he
   _ = _ := by simp only [map_sum,map_smul,smul_eq_mul]
 let v : τ→ℝ := fun t=>f (Pi.single t 1)
 have hval : ∀ t,0≤v t := by
  intro t
  by_contra hn
  have hv : v t<0 := lt_of_not_ge hn
  let e := -v t/(2*f (fun _ : τ=>1))
  have he : 0<e := div_pos (neg_pos.mpr hv) (mul_pos (by norm_num) hfone)
  have hp : Pi.single t (1 : ℝ)+e • (fun _ : τ=>1)∈O := by
   intro i
   change 0<(Pi.single t (1 : ℝ) : τ→ℝ) i+e*1
   have hh : 0≤(Pi.single t (1 : ℝ) : τ→ℝ) i := by simp only [Pi.single_apply]; split_ifs <;> norm_num
   simpa only [mul_one] using add_pos_of_nonneg_of_pos hh he
  have hh := hf _ (show Pi.single t (1 : ℝ)+e • (fun _ : τ=>1)∈O-C from ⟨_,hp,0,hzC,by simp⟩)
  simp only [map_zero,map_add,map_smul,smul_eq_mul] at hh
  have heq : e*f (fun _ : τ=>1)= -v t/2 := by dsimp [e]; field_simp
  rw [heq] at hh
  change 0<v t+(-v t/2) at hh
  linarith
 have hnonzero : ∃ t,0<v t := by
  by_contra hn
  push Not at hn
  have hv : ∀ t,v t=0 := fun t=>le_antisymm (hn t) (hval t)
  rw [hrep] at hfone
  change ∀ t,f (Pi.single t 1)=0 at hv
  simp only [hv,mul_zero,Finset.sum_const_zero] at hfone
  exact lt_irrefl _ hfone
 refine ⟨v,hval,hnonzero,?_⟩
 intro r
 have hr : Δ r∈C := by
  refine ⟨Pi.single r 1,fun i=>by simp only [Pi.single_apply]; split_ifs <;> norm_num,?_⟩
  simp [Pi.single_apply]
 have hle : f (Δ r)≤0 := by
  by_contra hn
  have hd : 0<f (Δ r) := lt_of_not_ge hn
  let e := f (Δ r)/(2*f (fun _ : τ=>1))
  have he : 0<e := div_pos hd (mul_pos (by norm_num) hfone)
  have hp : e • (fun _ : τ=>1)∈O := by intro t; simpa using he
  have hh := hf _ (show e • (fun _ : τ=>1)-Δ r∈O-C from ⟨_,hp,_,hr,rfl⟩)
  simp only [map_zero,map_sub,map_smul,smul_eq_mul] at hh
  have heq : e*f (fun _ : τ=>1)= f (Δ r)/2 := by dsimp [e]; field_simp
  rw [heq] at hh
  linarith
 rw [hrep] at hle
 simpa only [v,mul_comm] using hle

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {ρ : Type} [Fintype ρ] [DecidableEq ρ]

theorem no_win_separator (hno : ¬FiniteWinStatement) (hA : ∀ t,IsUnit (A t))
 (u : τ) (hn : ¬MonomialMatrix (A u)) (c : ρ→PairComparison (A := A)) :
 ∃ v : τ→ℝ,(∀ t,0≤v t) ∧ (∃ t,0<v t) ∧
 ∀ r,pairPrice (D := D) v (c r).pair≤(c r).word.weight v := by
 let : Nonempty τ := ⟨u⟩
 obtain ⟨v,hv,hvn,hc⟩ := finite_separator (fun r t=>((c r).delta t : ℝ)) (by
  rintro ⟨lam,hl,hp⟩
  exact hno (positive_comparison_win hA u hn c lam hl hp))
 exact ⟨v,hv,hvn,fun r=>(comparison_ineq v (c r)).mp (hc r)⟩

theorem finite_prices (hno : ¬FiniteWinStatement) (hA : ∀ t,IsUnit (A t))
 (u : τ) (hn : ¬MonomialMatrix (A u)) (c : ρ→PairComparison (A := A))
 (C : τ→ℕ) (upper : ∀ t,Word D A (D t)) (hu : ∀ t,(upper t).matrix=A t)
 (hcost : ∀ t (p : τ→ℝ),(upper t).weight p=(C t : ℝ)*p u) :
 ∃ p : τ→ℝ,(∀ t,0≤p t ∧ p t≤C t) ∧ p u=1 ∧
 ∀ r,pairPrice (D := D) p (c r).pair≤(c r).word.weight p := by
 let cc : ρ⊕τ→PairComparison (A := A) := Sum.elim c (fun t=>singleComparison t (upper t) (hu t))
 obtain ⟨v,hv,⟨t,ht⟩,hc⟩ := no_win_separator hno hA u hn cc
 have hub : ∀ t,v t≤(C t : ℝ)*v u := by
  intro t
  have hh := hc (Sum.inr t)
  change pairPrice (D := D) v (singleComparison t (upper t) (hu t)).pair≤
   (singleComparison t (upper t) (hu t)).word.weight v at hh
  rw [singleComparison_price,singleComparison_weight,hcost] at hh
  exact hh
 have hvu : 0<v u := by
  by_contra hh
  have he : v u=0 := le_antisymm (le_of_not_gt hh) (hv u)
  have h := hub t
  rw [he,mul_zero] at h
  exact (not_lt_of_ge h) ht
 let p : τ→ℝ := fun t=>v t/v u
 refine ⟨p,?_,by dsimp [p]; exact div_self hvu.ne',?_⟩
 · intro t
   refine ⟨div_nonneg (hv t) hvu.le,?_⟩
   exact (div_le_iff₀ hvu).mpr (hub t)
 · intro r
   apply (comparison_ineq p (c r)).mp
   simp only [p,div_mul_eq_mul_div,← Finset.sum_div]
   exact div_nonpos_of_nonpos_of_nonneg ((comparison_ineq v (c r)).mpr (hc (Sum.inl r))) hvu.le

end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing

theorem finite_global_prices (hno : ¬FiniteWinStatement) (Q : Finset GlobalComparison) :
 ∃ p : GMatrix→ℝ,(∀ g,0≤p g ∧ p g≤g.upperCost) ∧ p shearG=1 ∧
 ∀ c∈Q,c.holds p := by
 classical
 let s : Finset GMatrix := insert shearG (Q.biUnion fun c=>Finset.univ.image c.family)
 have hs : ∀ c∈Q,∀ t,c.family t∈s := by
  intro c hc t
  apply Finset.mem_insert_of_mem
  exact Finset.mem_biUnion.mpr ⟨c,hc,Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩⟩
 let D : s→Type := fun g=>g.val.domain
 let A : ∀ g,Matrix (D g) (D g) ℂ := fun g=>g.val.mat
 let u : s := ⟨shearG,Finset.mem_insert_self _ _⟩
 let f : ∀ c : Q,Fin c.val.num→s := fun c t=>⟨c.val.family t,hs c.val c.property t⟩
 let cmp : Q→PairComparison (A := A) := fun c=>c.val.comparison.rename (f c)
   (fun _=>Equiv.refl _) (fun _=>rfl)
 let upper : ∀ g : s,Word D A (D g) := fun g=>g.val.upperWord.rename (fun _:Unit=>u) (fun _=>Equiv.refl _)
 have hu : ∀ g,(upper g).matrix=A g := by
  intro g
  exact (Word.matrix_rename (D := fun _:Unit=>Fin 2) (A := fun _=>shearU)
    (E := D) (B := A) (fun _:Unit=>u) (fun _=>Equiv.refl _)
    (fun _=>rfl) g.val.upperWord).trans g.val.upperWord_matrix
 have hcost : ∀ g (p : s→ℝ),(upper g).weight p=(g.val.upperCost : ℝ)*p u := by
  intro g p
  exact (Word.weight_rename (D := fun _:Unit=>Fin 2) (A := fun _=>shearU)
    (E := D) (B := A) (fun _:Unit=>u) (fun _=>Equiv.refl _) p g.val.upperWord).trans
    (g.val.upperWord_weight (p∘fun _:Unit=>u))
 obtain ⟨v,hv,hvu,hc⟩ := finite_prices hno (fun g : s=>g.val.unit) u shearU_not_monomial
  cmp (fun g=>g.val.upperCost) upper hu hcost
 let p : GMatrix→ℝ := fun g=>if hg:g∈s then v ⟨g,hg⟩ else 0
 have hp : ∀ g : s,p g.val=v g := by intro g; simp [p,g.property]
 refine ⟨p,?_,?_,?_⟩
 · intro g
   by_cases hg:g∈s
   · simpa [p,hg] using hv ⟨g,hg⟩
   · simp [p,hg]
 · exact (hp u).trans hvu
 · intro c hcQ
   let c' : Q := ⟨c,hcQ⟩
   have hh := (PairComparison.rename_ineq (E := D) (B := A) (f c')
     (fun _=>Equiv.refl _) (fun _=>rfl) c'.val.comparison v).mp (hc c')
   have hf : p∘c.family=v∘f c' := by
    funext t
    exact hp (f c' t)
   change pairPrice (p∘c.family) c.comparison.pair≤c.comparison.word.weight (p∘c.family)
   rw [hf]
   exact hh

theorem global_prices_exist (hno : ¬FiniteWinStatement) :
 ∃ p : GMatrix→ℝ,(∀ g,0≤p g ∧ p g≤g.upperCost) ∧ p shearG=1 ∧ GlobalConstraints p := by
 let K : Set (GMatrix→ℝ) := {p|(∀ g,0≤p g ∧ p g≤g.upperCost) ∧ p shearG=1}
 have hK : IsCompact K := by
  have hP : IsCompact {p : GMatrix→ℝ|∀ g,p g∈Set.Icc 0 (g.upperCost : ℝ)} :=
   isCompact_pi_infinite (fun _=>isCompact_Icc)
  exact hP.inter_right (isClosed_eq (continuous_apply shearG) continuous_const)
 have hh := hK.inter_iInter_nonempty (fun c : GlobalComparison=>{p|c.holds p})
  (fun c=>c.closed) (by
   intro Q
   obtain ⟨p,hp,hu,hc⟩ := finite_global_prices hno Q
   refine ⟨p,⟨hp,hu⟩,?_⟩
   simpa only [Set.mem_iInter,Set.mem_ofPred_eq] using hc)
 obtain ⟨p,hp,hc⟩ := hh
 exact ⟨p,hp.1,hp.2,by intro c; exact Set.mem_iInter.mp hc c⟩
end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing

theorem GlobalConstraints.reindex_le {p : GMatrix→ℝ} (hp : GlobalConstraints p)
 (a b : GMatrix) (e : a.domain≃b.domain) (he : Matrix.reindex e e a.mat=b.mat) :
 p b≤p a := by
 let f : Bool→GMatrix := fun t=>cond t b a
 let D : Bool→Type := fun t=>(f t).domain
 let A : ∀ t,Matrix (D t) (D t) ℂ := fun t=>(f t).mat
 let W : Word D A (D true) := callWord false e.toEmbedding
 have hW : W.matrix=A true := by
  rw [matrix_callWord,Embedded.matrix_equiv]
  exact he
 have hh := hp.apply f (singleComparison true W hW)
 rw [singleComparison_price,singleComparison_weight] at hh
 change p b≤Word.weight (p∘f) W at hh
 simpa [W,Word.weight,f] using hh

theorem GlobalConstraints.reindex {p : GMatrix→ℝ} (hp : GlobalConstraints p)
 (a b : GMatrix) (e : a.domain≃b.domain) (he : Matrix.reindex e e a.mat=b.mat) :
 p b=p a := by
 apply le_antisymm (hp.reindex_le a b e he)
 apply hp.reindex_le b a e.symm
 rw [← he,ExactFourier.reindex_inverse]
end ExactFourier.Packing

end
end

section
noncomputable section
namespace ExactFourier.Packing

theorem rawValue_unit (p : GMatrix→ℝ) {α : Type} [Fintype α] [DecidableEq α]
 (M : Matrix α α ℂ) (hM : IsUnit M) : rawValue p M=p (GMatrix.of M hM) := by
 simp only [rawValue,dite_eq_left hM]

theorem rawPrice_exists (hno : ¬FiniteWinStatement) : Nonempty RawPrice := by
 obtain ⟨p,hp,hu,hc⟩ := global_prices_exist hno
 refine ⟨{value:=rawValue p,nonneg:=?_,comparison:=?_,normalized:=?_}⟩
 · intro α _ _ M hM
   rw [rawValue_unit p M hM]
   exact (hp _).1
 · intro τ _ _ D _ _ A hA c
   let f : τ→GMatrix := fun t=>GMatrix.of (A t) (hA t)
   let cc : PairComparison (D := fun t=>(f t).domain) (A := fun t=>(f t).mat) :=
    c.rename id (fun t=>Fintype.equivFin (D t)) (fun _=>rfl)
   have hh := (PairComparison.rename_ineq (E := fun t=>(f t).domain)
    (B := fun t=>(f t).mat) id (fun t=>Fintype.equivFin (D t))
    (fun _=>rfl) c (p∘f)).mp (hc.apply f cc)
   have he : (fun t=>rawValue p (A t))=(p∘f)∘id := by
    funext t; exact rawValue_unit p _ _
   rw [he]
   exact hh
 · rw [rawValue_unit p shearU shearU_unit]
   exact (hc.reindex shearG (GMatrix.of shearU shearU_unit) (Fintype.equivFin (Fin 2)) rfl).trans hu

end ExactFourier.Packing

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.RawPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier.BasisExchange
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem rows_insert (K : Matrix ι ι ℂ) (H : Finset ι) (j : ι) (hj : j∉H) :
    (rows K H).updateRow j (rows K Hᶜ j)=rows K (insert j H) ∧
    (rows K Hᶜ).updateRow j (rows K H j)=rows K (insert j H)ᶜ := by
  constructor <;> ext a b
  all_goals
    by_cases ha : a=j
    · subst a; simp [rows,Matrix.updateRow_apply,hj]
    · simp [rows,Matrix.updateRow_apply,ha]

theorem price_many (p : MatrixPrice) (K : Matrix ι ι ℂ)
    (hU : ∀ H : Finset ι,IsUnit (rows K H)) (H : Finset ι) :
    p.value (rows K Hᶜ*(rows K H)⁻¹)=p.value K := by
  induction H using Finset.induction_on with
  | empty =>
    have he : rows K ∅=1 := by ext i j; simp [rows]
    have hu : rows K Finset.univ=K := by ext i j; simp [rows]
    simp only [Finset.compl_empty,he,hu,inv_one,mul_one]
  | @insert j H hj ih =>
    have he := BasisExchange.price p (rows K H) (rows K Hᶜ) j (hU H) (hU Hᶜ)
      (by rw [(rows_insert K H j hj).1]; exact hU _) (by rw [(rows_insert K H j hj).2]; exact hU _)
    rw [(rows_insert K H j hj).1,(rows_insert K H j hj).2] at he
    exact he.trans ih

variable [LinearOrder ι]

theorem rows_unit (K : Matrix ι ι ℂ) (hl : K.IsLowerTriangular)
    (hd : ∀ i,K i i=1) (H : Finset ι) : IsUnit (rows K H) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  have hl' : (rows K H).IsLowerTriangular := by
    intro i j hij
    by_cases hi : i∈H
    · simp [rows,hi,hl hij]
    · have hij' : i<j := hij
      simp [rows,hi,ne_of_lt hij']
  rw [Matrix.det_of_isLowerTriangular _ hl']
  simp [rows,hd]

theorem price_triangular (p : MatrixPrice) (K : Matrix ι ι ℂ) (hl : K.IsLowerTriangular)
    (hd : ∀ i,K i i=1) (H : Finset ι) :
    p.value (rows K Hᶜ*(rows K H)⁻¹)=p.value K :=
  price_many p K (rows_unit K hl hd) H

end ExactFourier.BasisExchange

end

section
noncomputable section
namespace ExactFourier.SignedBits
open scoped Matrix Kronecker

theorem D_square (m : ℕ) : D m*D m=0 := by
  induction m with
  | zero => simp [D]
  | succ m ih => simp [D,Matrix.fromBlocks_multiply,ih]

theorem T_inv_mul (m : ℕ) : (1-D m)*T m=1 := by
  rw [T,mul_add,sub_mul,sub_mul,one_mul,one_mul,mul_one,D_square]
  abel

theorem T_unit (m : ℕ) : IsUnit (T m) :=
  by
    rw [isUnit_iff_exists_inv']
    exact ⟨1-D m,T_inv_mul m⟩

theorem T_inv (m : ℕ) : (T m)⁻¹=1-D m := Matrix.inv_eq_left_inv (T_inv_mul m)

theorem D_lower (m : ℕ) : (D m).IsLowerTriangular := by
  induction m with
  | zero => intro i j hij; rfl
  | succ m ih =>
    intro i j hij
    change (toLex i : Bits m ⊕ₗ Bits m) < toLex j at hij
    rcases i with i|i <;> rcases j with j|j
    · have hh : i<j := Sum.Lex.inl_lt_inl_iff.mp hij
      exact ih hh
    · rfl
    · exact False.elim (Sum.Lex.not_inr_lt_inl hij)
    · change -(D m i j)=0
      have hh : i<j := Sum.Lex.inr_lt_inr_iff.mp hij
      rw [ih hh,neg_zero]

theorem D_diag (m : ℕ) : ∀ i,D m i i=0 := by
  induction m with
  | zero => intro i; rfl
  | succ m ih => intro i; rcases i with i|i <;> simp [D,ih]

theorem T_lower (m : ℕ) : (T m).IsLowerTriangular := by
  intro i j hij
  have h : i<j := hij
  simp [T,ne_of_lt h,D_lower m hij]

theorem T_diag (m : ℕ) : ∀ i,T m i i=1 := by simp [T,D_diag]

theorem T_succ (m : ℕ) : T (m+1)=Matrix.fromBlocks (T m) 0 1 (T m)⁻¹ := by
  rw [T_inv]
  ext i j; rcases i with i|i <;> rcases j with j|j <;>
    simp [T,D,Matrix.one_apply,Matrix.fromBlocks,sub_eq_add_neg]

end ExactFourier.SignedBits

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.SignedPrice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.SignedBits
open scoped Matrix Kronecker

attribute [local instance] OAI.ExactFourier.SignedBits.instLinearOrderSumBits
attribute [local instance] OAI.ExactFourier.SignedBits.instLTSumBits
theorem start_lower (m : ℕ) : (start m).IsLowerTriangular := by
  intro i j hij
  change (toLex i : Bits m ⊕ₗ Bits m) < toLex j at hij
  rcases i with i|i <;> rcases j with j|j
  · have hh : i<j := Sum.Lex.inl_lt_inl_iff.mp hij
    exact T_lower m hh
  · rfl
  · exact False.elim (Sum.Lex.not_inr_lt_inl hij)
  · have hh : i<j := Sum.Lex.inr_lt_inr_iff.mp hij
    exact T_lower m hh

theorem start_diag (m : ℕ) : ∀ i,start m i i=1 := by
  intro i; rcases i with i|i <;> simp [start,T_diag]

theorem input_rows (m : ℕ) : BasisExchange.rows (start m) (bottom m)=oldInputs m := by
  ext i j; rcases i with i|i <;> rcases j with j|j <;>
    simp [BasisExchange.rows,start,oldInputs,bottom,Matrix.one_apply]

theorem output_rows (m : ℕ) : BasisExchange.rows (start m) (bottom m)ᶜ=oldOutputs m := by
  ext i j; rcases i with i|i <;> rcases j with j|j <;>
    simp [BasisExchange.rows,start,oldOutputs,bottom,Matrix.one_apply]

theorem transition_solve (m : ℕ) : transition m*oldInputs m=oldOutputs m := by
  simp [transition,oldInputs,oldOutputs,Matrix.fromBlocks_multiply,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (T_unit m))]

theorem transition_eq (m : ℕ) : transition m=oldOutputs m*(oldInputs m)⁻¹ := by
  have hU : IsUnit (oldInputs m) := Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨isUnit_one,T_unit m⟩
  rw [← transition_solve,Matrix.mul_nonsing_inv_cancel_right _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)]

theorem zdiag_monomial (m : ℕ) : MonomialMatrix (zdiag m) := by
  apply MonomialMatrix.diagonal
  intro i; rcases i with i|i <;> norm_num

theorem transition_sign (m : ℕ) : zdiag m*transition m*zdiag m=T (m+1) := by
  rw [T_succ]
  ext i j; rcases i with i|i <;> rcases j with j|j <;>
    simp [zdiag,transition,Matrix.diagonal_mul,Matrix.mul_diagonal]

theorem start_tensor (m : ℕ) : start m=Matrix.reindex (twoProdEquiv (Bits m)) (twoProdEquiv (Bits m))
    (Matrix.transvection (1 : Fin 2) 0 (1 : ℂ)⊗ₖT m) := by
  ext i j; rcases i with i|i <;> rcases j with j|j <;>
    simp [start,Matrix.reindex_apply,twoProdEquiv,Matrix.transvection,Matrix.single]

theorem price_step (p : MatrixPrice) (m : ℕ) :
    p.value (T (m+1))=2^m+2*p.value (T m) := by
  have hp := BasisExchange.price_triangular p (start m) (start_lower m) (start_diag m) (bottom m)
  rw [input_rows,output_rows,← transition_eq] at hp
  have hW : IsUnit (transition m) := Matrix.isUnit_fromBlocks_zero₁₂.mpr
    ⟨T_unit m,Matrix.isUnit_nonsing_inv_iff.mpr (T_unit m)⟩
  have hm := p.monomial (transition m) (zdiag m) (zdiag m) hW (zdiag_monomial m) (zdiag_monomial m)
  rw [transition_sign,hp,start_tensor,p.reindex _ _ (TensorTools.unit_tensor _ _
      (MatrixPrice.transvection_isUnit _ _ (by decide) _) (T_unit m)),
    p.tensor _ _ (MatrixPrice.transvection_isUnit _ _ (by decide) _) (T_unit m),p.normalized,bits_card] at hm
  norm_num at hm
  exact hm

theorem price (p : MatrixPrice) (m : ℕ) :
    2*p.value (T m)=(m : ℝ)*2^m := by
  induction m with
  | zero => simp [T,D,p.one]
  | succ m ih => rw [price_step,pow_succ]; push_cast; nlinarith

end ExactFourier.SignedBits

end
end

section
noncomputable section
namespace ExactFourier.SignedBits
open scoped Matrix Kronecker

theorem J_commute (m : ℕ) (b : Bool) :
    J m b*D m=(if b then -(D m).transpose else (D m).transpose)*J m b := by
  induction m generalizing b with
  | zero => simp [J,D]
  | succ m ih =>
    cases b <;>
      simp [J,D,Matrix.fromBlocks_multiply,Matrix.fromBlocks_transpose,ih true,ih false,Matrix.fromBlocks_neg]

theorem J_sign (m : ℕ) (b : Bool) : ∃ s : ℂ,s*s=1 ∧ (J m b).transpose=s•J m b := by
  induction m generalizing b with
  | zero => exact ⟨1,by simp,by simp [J]⟩
  | succ m ih =>
    cases b
    · obtain ⟨s,hs,he⟩ := ih true
      refine ⟨s,hs,?_⟩
      simp [J,Matrix.fromBlocks_transpose,he,Matrix.fromBlocks_smul]
    · obtain ⟨s,hs,he⟩ := ih false
      refine ⟨-s,by simpa using hs,?_⟩
      simp [J,Matrix.fromBlocks_transpose,he,Matrix.fromBlocks_smul,Matrix.fromBlocks_neg]

theorem offDiagonal_monomial {α : Type} [DecidableEq α]
    {A : Matrix α α ℂ} (hA : MonomialMatrix A) (s : ℂ) (hs : s≠0) :
    MonomialMatrix (Matrix.fromBlocks 0 A (s•A) 0) := by
  obtain ⟨σ,d,hd,ha⟩ := hA
  let e : Equiv.Perm (α⊕α) := (Equiv.sumCongr σ σ).trans (Equiv.sumComm α α)
  refine ⟨e,Sum.elim (fun i => s*d i) d,?_,?_⟩
  · intro j; cases j <;> simp [hd,hs]
  · intro i j; rcases i with i|i <;> rcases j with j|j <;>
      simp [Matrix.fromBlocks,ha,e,mul_ite]

theorem J_monomial (m : ℕ) (b : Bool) : MonomialMatrix (J m b) := by
  induction m generalizing b with
  | zero => exact MonomialMatrix.one
  | succ m ih =>
    cases b
    · simpa [J] using offDiagonal_monomial (ih true) 1 one_ne_zero
    · simpa [J] using offDiagonal_monomial (ih false) (-1) (neg_ne_zero.mpr one_ne_zero)

theorem Gamma_square (m : ℕ) : Gamma m*Gamma m=1 := by
  simp [Gamma,Matrix.fromBlocks_multiply,D_square,← Matrix.fromBlocks_one]
theorem Gamma_unit (m : ℕ) : IsUnit (Gamma m) := by
  rw [isUnit_iff_exists_inv']; exact ⟨Gamma m,Gamma_square m⟩

theorem Gamma_symmetry (m : ℕ) : J (m+1) false*Gamma m=(Gamma m).transpose*J (m+1) false := by
  simp [J,Gamma,Matrix.fromBlocks_multiply,Matrix.fromBlocks_transpose,J_commute m true]

theorem D_star (m : ℕ) : ∀ i j,star (D m i j)=D m i j := by
  induction m with
  | zero => simp [D]
  | succ m ih =>
    intro i j; rcases i with i|i <;> rcases j with j|j <;>
      simp [D,Matrix.one_apply,ih]

theorem J_star (m : ℕ) (b : Bool) : ∀ i j,star (J m b i j)=J m b i j := by
  induction m generalizing b with
  | zero => simp [J]
  | succ m ih =>
    cases b <;> intro i j <;> rcases i with i|i <;> rcases j with j|j <;>
      simp [J,ih]

theorem Gamma_star (m : ℕ) : ∀ i j,star (Gamma m i j)=Gamma m i j := by
  intro i j; rcases i with i|i <;> rcases j with j|j <;>
    simp [Gamma,D_star,Matrix.one_apply]

end ExactFourier.SignedBits

end
end

section
noncomputable section
namespace ExactFourier
open scoped Kronecker
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem nnz_add_le (A B : Matrix α β ℂ) : nnz (A+B)≤nnz A+nnz B := by
  apply (Finset.card_le_card (show support (A+B)⊆support A∪support B from ?_)).trans (Finset.card_union_le _ _)
  intro ij hij
  simp only [mem_support,Matrix.add_apply] at hij
  simp only [Finset.mem_union,mem_support]
  by_contra h
  push Not at h
  exact hij (by simp [h.1,h.2])

theorem nnz_sub_le (A B : Matrix α β ℂ) : nnz (A-B)≤nnz A+nnz B := by
  simpa [sub_eq_add_neg] using nnz_add_le A (-B)

theorem nnz_kronecker
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (A : Matrix α α ℂ) (B : Matrix β β ℂ) : nnz (A⊗ₖB)=nnz A*nnz B := by
  classical
  let e : (α×α)×(β×β) ≃ (α×β)×(α×β) := Equiv.prodProdProdComm α α β β
  have he : support (A⊗ₖB)=(support A×ˢsupport B).map e.toEmbedding := by
    ext ⟨⟨i,k⟩,⟨j,l⟩⟩
    simp [support,e,Equiv.prodProdProdComm_apply]
  rw [nnz,he,Finset.card_map,Finset.card_product]
  rfl

theorem nnz_monomial_mul (A B : Matrix α α ℂ) (hA : MonomialMatrix A) : nnz (A*B)=nnz B := by
  classical
  obtain ⟨σ,d,hd,hA⟩ := hA
  have he (i j : α) : (A*B) (σ i) j=d i*B i j := by
    rw [Matrix.mul_apply]
    simp_rw [hA]
    simp
  let e : α×α ≃ α×α := σ.prodCongr (Equiv.refl α)
  have hs : support (A*B)=(support B).map e.toEmbedding := by
    ext ij
    obtain ⟨⟨i,j⟩,rfl⟩ := e.surjective ij
    simp [e,he,hd]
  rw [nnz,hs,Finset.card_map]; rfl

end ExactFourier

end
end

section
noncomputable section
namespace ExactFourier
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem nnz_sum
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (A : Matrix α β ℂ) : nnz A=∑ i,∑ j,if A i j=0 then 0 else 1 := by
  rw [nnz,Finset.card_eq_sum_ones]
  simp only [support,Finset.sum_filter,Fintype.sum_prod_type,ite_not]

theorem nnz_fromBlocks (A : Matrix α α ℂ) (B : Matrix α β ℂ)
    (C : Matrix β α ℂ) (D : Matrix β β ℂ) :
    nnz (Matrix.fromBlocks A B C D)=nnz A+nnz B+nnz C+nnz D := by
  simp [nnz_sum,Fintype.sum_sum_type,Finset.sum_add_distrib,add_assoc,add_left_comm]
  rfl

namespace SignedBits

theorem D_count (m : ℕ) : 2*nnz (D m)=m*2^m := by
  induction m with
  | zero => simp [D]
  | succ m ih =>
    rw [D,nnz_fromBlocks,nnz_zero,nnz_one,nnz_neg,bits_card]
    rw [pow_succ]
    nlinarith

theorem Gamma_count (m : ℕ) : nnz (Gamma m)=(m+2)*2^m := by
  rw [Gamma,nnz_fromBlocks,nnz_one,nnz_neg,bits_card]
  have hh := D_count m
  nlinarith

end SignedBits
end ExactFourier

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.SymmetricLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.SymLap
open scoped Kronecker
variable {α : Type} [Fintype α] [DecidableEq α]

theorem tensor_square (G : Matrix α α ℂ) (hG : G*G=1) : tensor G*tensor G=1 := by
  rw [tensor,← Matrix.mul_kronecker_mul,hG,Matrix.one_kronecker_one]

theorem lap_factor (G : Matrix α α ℂ) (hG : G*G=1) :
    lap G=(G⊗ₖ(1 : Matrix α α ℂ))*(1-tensor G) := by
  rw [mul_sub,mul_one,tensor,← Matrix.mul_kronecker_mul,hG,one_mul]
  rfl

theorem lap_kill (G : Matrix α α ℂ) (hG : G*G=1) : lap G*(1+tensor G)=0 := by
  rw [lap_factor G hG]
  have hm := tensor_square G hG
  calc
    _ = (G⊗ₖ(1 : Matrix α α ℂ))*(1-tensor G*tensor G) := by noncomm_ring
    _ = 0 := by rw [hm,sub_self,mul_zero]

theorem symmetric (G J : Matrix α α ℂ) (s : ℂ) (hs : s*s=1)
    (hJ : J.transpose=s•J) (hc : J*G=G.transpose*J) : (symmetrized G J).IsSymm := by
  change (symmetrized G J).transpose=symmetrized G J
  have hJJ : (J⊗ₖJ).transpose=J⊗ₖJ := by
    rw [← Matrix.kroneckerMap_transpose,hJ,Matrix.smul_kronecker,Matrix.kronecker_smul,smul_smul,hs,one_smul]
  have hh : (lap G).transpose*(J⊗ₖJ)=(J⊗ₖJ)*lap G := by
    simp only [lap,Matrix.transpose_sub,← Matrix.kroneckerMap_transpose,Matrix.transpose_one,
      sub_mul,mul_sub,← Matrix.mul_kronecker_mul,one_mul,mul_one,← hc]
  rw [symmetrized,Matrix.transpose_mul,hJJ,hh]

theorem real_entries (G J : Matrix α α ℂ) (hG : ∀ i j,star (G i j)=G i j)
    (hJ : ∀ i j,star (J i j)=J i j) : ∀ i j,star (symmetrized G J i j)=symmetrized G J i j := by
  intro i j
  change (starRingEnd ℂ) (symmetrized G J i j)=symmetrized G J i j
  have hg : ∀ i j,(starRingEnd ℂ) (G i j)=G i j := hG
  have hj : ∀ i j,(starRingEnd ℂ) (J i j)=J i j := hJ
  simp only [symmetrized,Matrix.mul_apply,lap,Matrix.sub_apply,Matrix.kroneckerMap_apply,
    Matrix.one_apply, map_sum, map_mul, map_sub, apply_ite, map_one, map_zero, hg,hj]

theorem support_bound (G J : Matrix α α ℂ) (hJ : MonomialMatrix J) :
    nnz (symmetrized G J)≤2*nnz G*Fintype.card α := by
  rw [symmetrized,nnz_monomial_mul _ _ (hJ.tensor hJ)]
  have hh := nnz_sub_le (G⊗ₖ(1 : Matrix α α ℂ)) ((1 : Matrix α α ℂ)⊗ₖG)
  rw [nnz_kronecker,nnz_kronecker,nnz_one] at hh
  change nnz (lap G)≤_ at hh
  nlinarith [hh]

end ExactFourier.SymLap

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.SparseSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.SymLap
open scoped Kronecker
variable {α : Type} [Fintype α] [DecidableEq α]

theorem relations (G J R T : Matrix α α ℂ) (M A : Matrix α α ℂ)
    (hJ : IsUnit J) (hG : IsUnit G) (hA : A=J*G*(1-M))
    (hs : A.IsSymm) (hk : A*(1+M)=0) (hp : A*(1+R)=0) (hm : 1-R=A*T) :
    M*(1+R)=1+R ∧ M.transpose*(1-R)=-(1-R) := by
  have hl : (1-M)*(1+R)=0 := by
    apply (hJ.mul hG).mul_left_cancel
    rw [← mul_assoc,← hA,hp,mul_zero]
  have hrt : (1+M.transpose)*A=0 := by
    have ht := congrArg Matrix.transpose hk
    simpa [Matrix.transpose_mul,Matrix.transpose_add,hs.eq] using ht
  constructor
  · rw [sub_mul,one_mul,sub_eq_zero] at hl
    exact hl.symm
  · have ht : (1+M.transpose)*(1-R)=0 := by rw [hm,← mul_assoc,hrt,zero_mul]
    rw [add_mul,one_mul] at ht
    exact eq_neg_of_add_eq_zero_right ht

theorem exists_tensor_reflection (p : MatrixPrice) (G J : Matrix α α ℂ)
    (hG : G*G=1) (hJ : MonomialMatrix J)
    (s : ℂ) (hs : s*s=1) (ht : J.transpose=s•J) (hc : J*G=G.transpose*J)
    (hrG : ∀ i j,star (G i j)=G i j) (hrJ : ∀ i j,star (J i j)=J i j) :
    ∃ R : Matrix (α×α) (α×α) ℂ, R*R=1 ∧ R.IsSymm ∧
      tensor G*(1+R)=1+R ∧ (tensor G).transpose*(1-R)=-(1-R) ∧
      p.value R≤(3:ℝ)/4*(2*nnz G*Fintype.card α)+2*(Fintype.card α)^2 := by
  let ord := LinearOrder.lift' (Fintype.equivFin (α×α)) (Fintype.equivFin (α×α)).injective
  let deq : DecidableEq (α×α) := inferInstance
  let : LinearOrder (α×α) := { ord with
    toDecidableEq := deq
    compare := fun a b => @compareOfLessAndEq _ a b ord.toLT (ord.toDecidableLT a b) deq
    compare_eq_compareOfLessAndEq := by intro a b; rfl }
  let A := symmetrized G J
  have hAs : A.IsSymm := symmetric G J s hs ht hc
  obtain ⟨R,T,hR,hrs,hp,hm,hpr⟩ := SparseReflection.exists_reflection_nnz p A hAs
    (real_entries G J hrG hrJ)
  have huG : IsUnit G := isUnit_iff_exists_inv'.mpr ⟨G,hG⟩
  have huJ := MonomialMatrix.unit J hJ
  have hfactor : A=(J⊗ₖJ)*(G⊗ₖ(1 : Matrix α α ℂ))*(1-tensor G) := by
    dsimp only [A,symmetrized]
    rw [lap_factor G hG,mul_assoc]
  have hk : A*(1+tensor G)=0 := by
    dsimp only [A,symmetrized]
    rw [mul_assoc,lap_kill G hG,mul_zero]
  obtain ⟨hrp,hrm⟩ := relations (G⊗ₖ(1 : Matrix α α ℂ)) (J⊗ₖJ) R T (tensor G) A
    (TensorTools.unit_tensor _ _ huJ huJ) (TensorTools.unit_tensor _ _ huG isUnit_one)
    hfactor hAs hk hp hm
  refine ⟨R,hR,hrs,hrp,hrm,?_⟩
  have hb : (nnz A : ℝ)≤2*nnz G*Fintype.card α := by exact_mod_cast support_bound G J hJ
  simp only [Fintype.card_prod,Nat.cast_mul] at hpr
  nlinarith

end ExactFourier.SymLap

end
end

section
noncomputable section
namespace ExactFourier.SignedBits

theorem D_parity (m : ℕ) : ∀ i j,parity m i=parity m j → D m i j=0 := by
  induction m with
  | zero => simp [D]
  | succ m ih =>
    intro i j hij
    rcases i with i|i <;> rcases j with j|j
    · exact ih i j hij
    · rfl
    · have hn : i≠j := by intro he; subst j; simp [parity] at hij
      simp [D,hn]
    · change -(D m i j)=0
      have he : parity m i=parity m j := by simpa [parity] using hij
      rw [ih i j he,neg_zero]

theorem Gamma_parity (m : ℕ) : ∀ i j,parity (m+1) i=parity (m+1) j → Gamma m i j=0 := by
  intro i j hij
  rcases i with i|i <;> rcases j with j|j
  · exact D_parity m i j hij
  · have hn : i≠j := by intro he; subst j; simp [parity] at hij
    simp [Gamma,hn]
  · have hn : i≠j := by intro he; subst j; simp [parity] at hij
    simp [Gamma,hn]
  · change -(D m i j)=0
    have he : parity m i=parity m j := by simpa [parity] using hij
    rw [D_parity m i j he,neg_zero]

theorem parityEquiv_left (m : ℕ) (i : Bits m) : parity (m+1) (parityEquiv m (.inl i))=false := by
  change parity (m+1) (paritySwitch m (.inl i))=false
  cases he : parity m i <;> simp [paritySwitch,parity,he]

theorem parityEquiv_right (m : ℕ) (i : Bits m) : parity (m+1) (parityEquiv m (.inr i))=true := by
  change parity (m+1) (paritySwitch m (.inr i))=true
  cases he : parity m i <;> simp [paritySwitch,parity,he]

end ExactFourier.SignedBits

end
end

section
noncomputable section
namespace ExactFourier.GraphReflection
open scoped ComplexOrder
variable {α : Type} [Fintype α] [DecidableEq α]

theorem swap_monomial
    {α : Type} [Fintype α] [DecidableEq α] : MonomialMatrix (swap (α := α)) := by
  refine ⟨Equiv.sumComm α α,fun _=>1,by simp,?_⟩
  intro i j; rcases i with i|i <;> rcases j with j|j <;> simp [swap,Matrix.one_apply]

theorem graph_square (B : Matrix α α ℂ) (hB : IsUnit B) : graph B*graph B=1 := by
  have hi := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det _).mp hB)
  have hj := Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det _).mp hB)
  simp [graph,Matrix.fromBlocks_multiply,hi,hj,← Matrix.fromBlocks_one]

theorem graph_price (p : MatrixPrice) (B : Matrix α α ℂ) (hB : IsUnit B) : p.value (graph B)=2*p.value B := by
  have hG : IsUnit (graph B) := isUnit_iff_exists_inv'.mpr ⟨graph B,graph_square B hB⟩
  have hh := p.monomial (graph B) 1 swap hG MonomialMatrix.one swap_monomial
  rw [one_mul] at hh
  have he : graph B*swap=Matrix.fromBlocks B 0 0 B⁻¹ := by simp [graph,swap,Matrix.fromBlocks_multiply]
  rw [he,p.directSum _ _ hB (Matrix.isUnit_nonsing_inv_iff.mpr hB),p.inverse _ hB] at hh
  linarith

end ExactFourier.GraphReflection

end
end

section
noncomputable section
namespace ExactFourier.SignedBits
open scoped Kronecker

theorem parityTensor_square (m : ℕ) : parityTensor m*parityTensor m=1 := by
  rw [parityTensor,Matrix.submatrix_mul_equiv,SymLap.tensor_square _ (Gamma_square m)]
  simp

theorem parityTensor_diag_left (m : ℕ) : (parityTensor m).toBlocks₁₁=0 := by
  ext i j
  change Gamma m (parityEquiv m (.inl i.1)) (parityEquiv m (.inl j.1))*Gamma m i.2 j.2=0
  rw [Gamma_parity m _ _ (by rw [parityEquiv_left,parityEquiv_left]),zero_mul]

theorem parityTensor_diag_right (m : ℕ) : (parityTensor m).toBlocks₂₂=0 := by
  ext i j
  change Gamma m (parityEquiv m (.inr i.1)) (parityEquiv m (.inr j.1))*Gamma m i.2 j.2=0
  rw [Gamma_parity m _ _ (by rw [parityEquiv_right,parityEquiv_right]),zero_mul]

theorem graphB_unit (m : ℕ) : IsUnit (graphB m) := by
  have h := congrArg Matrix.toBlocks₁₁ (parityTensor_square m)
  rw [← Matrix.fromBlocks_toBlocks (parityTensor m),parityTensor_diag_left,parityTensor_diag_right] at h
  simp only [Matrix.fromBlocks_multiply,zero_mul,mul_zero,zero_add,add_zero,
    Matrix.toBlocks_fromBlocks₁₁] at h
  rw [← Matrix.fromBlocks_one,Matrix.toBlocks_fromBlocks₁₁] at h
  exact isUnit_iff_exists_inv.mpr ⟨(parityTensor m).toBlocks₂₁,h⟩

theorem parityTensor_graph (m : ℕ) : parityTensor m=GraphReflection.graph (graphB m) := by
  have h := congrArg Matrix.toBlocks₂₂ (parityTensor_square m)
  rw [← Matrix.fromBlocks_toBlocks (parityTensor m),parityTensor_diag_left,parityTensor_diag_right] at h
  simp only [Matrix.fromBlocks_multiply,zero_mul,mul_zero,zero_add,add_zero,
    Matrix.toBlocks_fromBlocks₂₂] at h
  rw [← Matrix.fromBlocks_one,Matrix.toBlocks_fromBlocks₂₂] at h
  have hi : (parityTensor m).toBlocks₂₁=(graphB m)⁻¹ := (Matrix.inv_eq_left_inv h).symm
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (parityTensor m)]
  rw [parityTensor_diag_left,parityTensor_diag_right,hi]
  rfl

theorem graphB_real (m : ℕ) : ∀ i j,star (graphB m i j)=graphB m i j := by
  intro i j
  change star (Gamma m (parityEquiv m (.inl i.1)) (parityEquiv m (.inr j.1))*Gamma m i.2 j.2)=_
  rw [star_mul,Gamma_star,Gamma_star]
  exact mul_comm _ _

end ExactFourier.SignedBits

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.GraphBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.SignedBits
open scoped Matrix Kronecker

theorem D_weight (m : ℕ) (i j : Bits m) (h : D m i j≠0) :
    weight m i=weight m j+1 := by
  induction m with
  | zero => exact False.elim (h rfl)
  | succ m ih =>
    rcases i with i|i <;> rcases j with j|j
    · exact ih i j h
    · exact False.elim (h rfl)
    · have hij : i=j := by simpa [D,Matrix.one_apply] using h
      subst j; rfl
    · change weight m i+1=weight m j+1+1
      change -(D m i j)≠0 at h
      rw [ih i j (neg_ne_zero.mp h)]

theorem ViV : Vi*V=1 := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Vi,V,Matrix.mul_apply,Fin.sum_univ_two]
theorem Vi_monomial : MonomialMatrix Vi := by
  refine ⟨Equiv.swap 0 1,![-1,1],?_,?_⟩
  · intro j; fin_cases j <;> norm_num
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [Vi]
theorem X_monomial : MonomialMatrix X := by
  refine ⟨Equiv.swap 0 1,fun _ => 1,by simp,?_⟩
  intro i j; fin_cases i <;> fin_cases j <;> norm_num [X]

theorem gauge_monomial (m : ℕ) : MonomialMatrix (gauge m) :=
  MonomialMatrix.blockDiagonal _ (fun _ => Vi_monomial.pow _)

theorem blockDiagonal_mul_apply {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (A : β → Matrix α α ℂ) (B : Matrix (α×β) (α×β) ℂ) (a b : α) (i j : β) :
    (Matrix.blockDiagonal A*B) (a,i) (b,j)=∑ c,A i a c*B (c,i) (b,j) := by
  classical
  simp [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.blockDiagonal_apply]

theorem mul_blockDiagonal_apply {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (A : Matrix (α×β) (α×β) ℂ) (B : β → Matrix α α ℂ) (a b : α) (i j : β) :
    (A*Matrix.blockDiagonal B) (a,i) (b,j)=∑ c,A (a,i) (c,j)*B j c b := by
  classical
  simp [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.blockDiagonal_apply]

theorem gauge_intertwine (m : ℕ) :
    gauge m*Q m=((1 : Matrix (Fin 2) (Fin 2) ℂ)⊗ₖT m)*gauge m := by
  rw [Q,T,Matrix.kronecker_add,Matrix.one_kronecker_one,mul_add,add_mul,mul_one,one_mul]
  congr 1
  ext ⟨a,i⟩ ⟨b,j⟩
  rw [gauge,blockDiagonal_mul_apply,mul_blockDiagonal_apply]
  simp only [Matrix.kronecker_apply,Matrix.one_apply]
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true,← mul_assoc]
  rw [← Finset.sum_mul]
  change (Vi^weight m i*V) a b*D m i j=D m i j*(Vi^weight m j) a b
  by_cases h : D m i j=0
  · simp [h]
  · rw [D_weight m i j h,pow_succ,mul_assoc,ViV,mul_one,mul_comm]

theorem Q_unit (m : ℕ) : IsUnit (Q m) := by
  have hs : (V⊗ₖD m)*(V⊗ₖD m)=0 := by
    rw [← Matrix.mul_kronecker_mul,D_square,Matrix.kronecker_zero]
  rw [Q,isUnit_iff_exists_inv']
  refine ⟨1-V⊗ₖD m,?_⟩
  rw [sub_mul,mul_add,mul_add,one_mul,one_mul,mul_one,hs]
  abel

theorem Q_price (p : MatrixPrice) (m : ℕ) : p.value (Q m)=2*p.value (T m) := by
  have h := p.monomial (Q m) (gauge m) 1 (Q_unit m) (gauge_monomial m) MonomialMatrix.one
  rw [mul_one,gauge_intertwine] at h
  have ht := TensorTools.unit_tensor (1 : Matrix (Fin 2) (Fin 2) ℂ) (T m) isUnit_one (T_unit m)
  rw [← one_mul ((1 : Matrix (Fin 2) (Fin 2) ℂ)⊗ₖT m),
    p.monomial _ 1 (gauge m) ht MonomialMatrix.one (gauge_monomial m),
    p.tensor _ _ isUnit_one (T_unit m),p.one,mul_zero,zero_add] at h
  norm_num at h
  exact h.symm

end ExactFourier.SignedBits

end
end

section
noncomputable section
namespace ExactFourier.SignedBits
open scoped Matrix Kronecker

theorem Gamma_Q (m : ℕ) : Gamma m=Matrix.reindex (twoProdEquiv (Bits m)) (twoProdEquiv (Bits m))
    ((X⊗ₖ(1 : Matrix (Bits m) (Bits m) ℂ))*Q m) := by
  rw [Q,mul_add,mul_one,← Matrix.mul_kronecker_mul,one_mul]
  ext i j; rcases i with i|i <;> rcases j with j|j <;>
    simp [Gamma,Matrix.reindex_apply,twoProdEquiv,X,V
      ]

theorem Gamma_price (p : MatrixPrice) (m : ℕ) :
    p.value (Gamma m)=(m:ℝ)*2^m := by
  have hx := X_monomial.tensor (MonomialMatrix.one (ι := Bits m))
  have hxu := MonomialMatrix.unit _ hx
  rw [Gamma_Q,p.reindex _ _ (hxu.mul (Q_unit m))]
  have hh := p.monomial (Q m) (X⊗ₖ(1 : Matrix (Bits m) (Bits m) ℂ)) 1
    (Q_unit m) hx MonomialMatrix.one
  rw [mul_one] at hh
  rw [hh,Q_price,price]

end ExactFourier.SignedBits

end
end

section
noncomputable section
namespace ExactFourier
open SignedBits
open scoped Kronecker

theorem reflection_inequality (p : MatrixPrice) (m : ℕ) :
    (m:ℝ)*(2^(m+1))^2≤(3:ℝ)/4*(2*((m+2)*2^m)*2^(m+1))+6*(2^(m+1))^2 := by
  let G := Gamma m
  let J₀ := J (m+1) false
  obtain ⟨s,hs,hJs⟩ := J_sign (m+1) false
  obtain ⟨R,hR,hRs,hRp,hRm,hRc⟩ := SymLap.exists_tensor_reflection p G J₀
    (Gamma_square m) (J_monomial (m+1) false) s hs hJs (Gamma_symmetry m)
    (Gamma_star m) (J_star (m+1) false)
  let e := tensorParityEquiv m
  let R' := R.submatrix e e
  have hRu : IsUnit R := isUnit_iff_exists_inv'.mpr ⟨R,hR⟩
  have hR'u : IsUnit R' := (Matrix.isUnit_submatrix_equiv e e).mpr hRu
  have hR's : R'.IsSymm := by
    change (R.submatrix e e).transpose=R.submatrix e e
    rw [Matrix.transpose_submatrix,hRs.eq]
  let φ := (Matrix.reindexAlgEquiv ℂ ℂ e.symm).toAlgHom
  have hφG : φ (SymLap.tensor G)=GraphReflection.graph (graphB m) := parityTensor_graph m
  have hφR : φ R=R' := rfl
  have hφGt : φ (SymLap.tensor G).transpose=(GraphReflection.graph (graphB m)).transpose := by
    rw [← hφG]
    change ((SymLap.tensor G).transpose).submatrix e e=((SymLap.tensor G).submatrix e e).transpose
    exact (Matrix.transpose_submatrix _ e e).symm
  have hp' : GraphReflection.graph (graphB m)*(1+R')=1+R' := by
    simpa only [map_mul,map_add,map_one,hφG,hφR] using congrArg φ hRp
  have hm' : (GraphReflection.graph (graphB m)).transpose*(1-R')=-(1-R') := by
    simpa only [map_mul,map_sub,map_one,map_neg,hφGt,hφR] using congrArg φ hRm
  have heR := Matrix.fromBlocks_toBlocks R'
  have hlow := GraphReflection.lower_bound_blocks p (graphB m) R'.toBlocks₁₁ R'.toBlocks₁₂
    R'.toBlocks₂₁ R'.toBlocks₂₂ (graphB_unit m) (graphB_real m)
    (heR.symm ▸ hR'u) (heR.symm ▸ hR's) (heR.symm ▸ hp') (heR.symm ▸ hm')
  rw [heR] at hlow
  have hpR : p.value R'=p.value R := p.reindex e.symm R hRu
  rw [hpR] at hlow
  have hprice : 2*p.value (graphB m)=(m:ℝ)*(2^(m+1))^2 := by
    rw [← GraphReflection.graph_price p _ (graphB_unit m),← parityTensor_graph]
    have hu := TensorTools.unit_tensor G G (Gamma_unit m) (Gamma_unit m)
    rw [show parityTensor m=Matrix.reindex e.symm e.symm (G⊗ₖG) from rfl,
      p.reindex _ _ hu,p.tensor _ _ (Gamma_unit m) (Gamma_unit m),Gamma_price,bits_card]
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    rw [pow_succ]
    ring
  rw [hprice] at hlow
  have hnnz := Gamma_count m
  change nnz G=(m+2)*2^m at hnnz
  rw [hnnz,bits_card] at hRc
  have hh : Fintype.card (Half m)=2^m*2^(m+1) := by
    rw [Fintype.card_prod,bits_card,bits_card]
  rw [hh] at hlow
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat] at hRc hlow
  rw [show (2:ℝ)^(m+1)=2^m*2 from pow_succ _ _] at hRc hlow ⊢
  nlinarith

theorem no_matrixPrice (p : MatrixPrice) : False := by
  have h := reflection_inequality p 32
  norm_num at h

end ExactFourier

end
end

section
noncomputable section
namespace ExactFourier
/-- The missing finite-win theorem, from exact comparison packing and the sparse
reflection contradiction. No global price is taken as an assumption. -/
theorem finite_win_oai : FiniteWinStatement := by
 by_contra hno
 obtain ⟨p⟩ := Packing.rawPrice_exists hno
 exact no_matrixPrice p.toMatrixPrice
end ExactFourier

end
end

end OAI
end

theorem solution : type_of% @OAI.ExactFourier.finite_win_oai := @OAI.ExactFourier.finite_win_oai
