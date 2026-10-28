-- Prove2me | solution 1 for OAI.MatchingFPRAS.OnlineTrial.sweep_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T18:35:10.923369+00:00
-- url     : https://prove2.me/submissions/114584e7-1863-48bd-9825-d29ecb82f9ce

import Mathlib
import Definitions.Def_MatchingFPRAS
import Definitions.Def_OAIQ051M004
import Theorems.Thm_OAI_MatchingFPRAS_OnlineStage_source_mean
import Theorems.Thm_OAI_MatchingFPRAS_OnlineTrial_work_body

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_EndpointPair
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma PM.card_le_vertices (hinc : ∀ e, ∃ v, inc e v) (A : PM inc) : A.val.card ≤ Fintype.card V := by
  classical
  let vertex : ↥A.val → V := fun e => Classical.choose (hinc e.val)
  have hv (e : ↥A.val) : inc e.val (vertex e) := Classical.choose_spec (hinc e.val)
  have hinj : Function.Injective vertex := by
    intro e f h
    apply Subtype.ext
    exact A.property.unique (Finset.mem_univ (vertex e)) e.property (hv e) f.property (h ▸ hv f)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective vertex hinj

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_MetropolisChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Variation

open Finset
open scoped Classical

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

omit [Fintype C] in
lemma imageLaw_comp_equiv (e : A ≃ B) (f : B → C) : imageLaw (f ∘ e)=imageLaw f := by
  funext c
  unfold imageLaw push uniform
  rw [Fintype.card_congr e,←e.sum_comp (fun b=>if f b=c then (1:ℝ)/Fintype.card B else 0)]
  rfl

lemma uniform_prod (a : A×B) : uniform (A×B) a=uniform A a.1*uniform B a.2 := by
  simp [uniform,Fintype.card_prod,Nat.cast_mul,mul_comm]

variable {D : Type*} [Fintype D]

omit [Fintype C] in
lemma imageLaw_pair (f : A → B → C) :
    imageLaw (fun x : A×B=>f x.1 x.2)=bind (uniform A) (fun a=>imageLaw (f a)) := by
  funext c
  simp only [imageLaw,push,bind,Fintype.sum_prod_type,uniform_prod,mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  split_ifs <;> simp

open Finset
open scoped Classical

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

omit [Fintype C] in
lemma imageLaw_ignore [Nonempty A] (f : B → C) :
    imageLaw (fun x : A×B=>f x.2)=imageLaw f := by
  rw [imageLaw_pair (fun _ b=>f b)]
  funext c
  simp only [bind,←sum_mul,uniform_sum,one_mul]

open scoped Classical

end MatchingFPRAS.Variation

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_RatWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MatchingFPRAS.RealStage

open Finset



open Finset

variable {n : ℕ}

lemma ScaleInvariant.pos {G : Fin n → Fin n → ℝ} {v : Fin n → ℝ}
    (hv : ScaleInvariant G v) (i) : 0 < v i := lt_of_lt_of_le (by norm_num [alpha]) (hv.lower i)

lemma rowMaximum_le (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (hv : ScaleInvariant G v) (i) : rowMaximum hn G v i ≤ v i := by
  apply Finset.sup'_le
  intro j hj
  exact (div_le_iff₀ (hv.pos j)).mpr (hv.feasible i j (mem_erase.mp hj).1.symm)

lemma ratio_le_rowMaximum (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (i j) (hji : j≠i) : G i j/v j ≤ rowMaximum hn G v i :=
  Finset.le_sup' (fun j => G i j/v j) (mem_erase.mpr ⟨hji,mem_univ _⟩)

lemma rowMaximum_lower (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (hG : ∀ i j, i≠j → alpha ≤ G i j) (hv : ScaleInvariant G v) (i) :
    alpha/2 ≤ rowMaximum hn G v i := by
  obtain ⟨j,hj⟩ := others_nonempty hn i
  have hji := (mem_erase.mp hj).1
  apply le_trans _ (ratio_le_rowMaximum hn G v i j hji)
  apply (le_div_iff₀ (hv.pos j)).mpr
  have hGi := hG i j hji.symm
  have hvi := hv.upper j
  norm_num [alpha] at *
  linarith

lemma scaleUpdate_le (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (hv : ScaleInvariant G v) (i j) : scaleUpdate hn G v i j ≤ v j := by
  by_cases hji : j=i
  · subst j; simpa [scaleUpdate] using rowMaximum_le hn G v hv i
  · simp [scaleUpdate,Function.update_of_ne hji]

lemma scaleUpdate_invariant (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (hsym : ∀ i j, G i j=G j i) (hG : ∀ i j, i≠j → alpha ≤ G i j)
    (hv : ScaleInvariant G v) (i) : ScaleInvariant G (scaleUpdate hn G v i) := by
  constructor
  · intro j
    by_cases hji : j=i
    · subst j; simpa [scaleUpdate] using rowMaximum_lower hn G v hG hv i
    · simpa [scaleUpdate,Function.update_of_ne hji] using hv.lower j
  · intro j; exact (scaleUpdate_le hn G v hv i j).trans (hv.upper j)
  · intro a b hab
    by_cases hai : a=i
    · subst a
      have hb := (div_le_iff₀ (hv.pos b)).mp (ratio_le_rowMaximum hn G v i b hab.symm)
      simpa [scaleUpdate,Function.update_of_ne hab.symm] using hb
    · by_cases hbi : b=i
      · subst b
        have ha := (div_le_iff₀ (hv.pos a)).mp (ratio_le_rowMaximum hn G v i a hai)
        simpa [scaleUpdate,Function.update_of_ne hai,hsym i a,mul_comm] using ha
      · simpa [scaleUpdate,Function.update_of_ne hai,Function.update_of_ne hbi] using hv.feasible a b hab

lemma scaleUpdate_tight (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (hv : ScaleInvariant G v) (i) :
    ∃ j, j≠i ∧ scaleUpdate hn G v i i*scaleUpdate hn G v i j=G i j := by
  obtain ⟨j,hj,heq⟩ := Finset.exists_mem_eq_sup' (others_nonempty hn i) (fun j => G i j/v j)
  have hji := (mem_erase.mp hj).1
  refine ⟨j,hji,?_⟩
  change rowMaximum hn G v i = G i j/v j at heq
  simp only [scaleUpdate,Function.update_self,Function.update_of_ne hji]
  rw [heq]
  exact div_mul_cancel₀ _ (hv.pos j).ne'

lemma tight_persists (G : Fin n → Fin n → ℝ) (v v' : Fin n → ℝ)
    (hv : ScaleInvariant G v) (hv' : ScaleInvariant G v') (hdown : ∀ i, v' i ≤ v i)
    (i j) (hji : j≠i) (hij : v i*v j=G i j) : v' i*v' j=G i j := by
  apply le_antisymm
  · calc
      _ ≤ v i*v j := mul_le_mul (hdown i) (hdown j) (hv'.pos j).le (hv.pos i).le
      _ = _ := hij
  · exact hv'.feasible i j hji.symm

end MatchingFPRAS.RealStage

end

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_RowPeak
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MatchingFPRAS.RealStage

open Finset

variable {n : ℕ}

lemma scalingTrace_invariant (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, G i j=G j i) (hG : ∀ i j, i≠j → alpha ≤ G i j ∧ G i j ≤ 3)
    (k : ℕ) : ScaleInvariant G (scalingTrace hn G k) ∧
      ∀ i, i.val<k → ∃ j, j≠i ∧ scalingTrace hn G k i*scalingTrace hn G k j=G i j := by
  induction k with
  | zero =>
    constructor
    · constructor
      · intro i; norm_num [scalingTrace,alpha]
      · intro i; simp [scalingTrace]
      · intro i j h; have := (hG i j h).2; simp only [scalingTrace]; linarith
    · intro i hi; omega
  | succ k ih =>
    by_cases hk : k<n
    · let i : Fin n := ⟨k,hk⟩
      have hinv := scaleUpdate_invariant hn G (scalingTrace hn G k) hsym (fun i j h => (hG i j h).1) ih.1 i
      have htrace : scalingTrace hn G (k+1)=scaleUpdate hn G (scalingTrace hn G k) i := by
        simp [scalingTrace,hk,i]
      rw [htrace]
      refine ⟨hinv,?_⟩
      intro a ha
      by_cases hak : a.val<k
      · obtain ⟨j,hj,he⟩ := ih.2 a hak
        refine ⟨j,hj,?_⟩
        exact tight_persists G _ _ ih.1 hinv (scaleUpdate_le hn G _ ih.1 i) a j hj he
      · have hai : a=i := Fin.ext (by dsimp [i]; omega)
        subst a
        exact scaleUpdate_tight hn G _ ih.1 i
    · have htrace : scalingTrace hn G (k+1)=scalingTrace hn G k := by simp [scalingTrace,hk]
      rw [htrace]
      refine ⟨ih.1,?_⟩
      intro i _
      exact ih.2 i (by have := i.isLt; omega)



open Finset

end MatchingFPRAS.RealStage

end

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_FinitePMF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.StageAnalysis Finset
open scoped Classical

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

variable {n K T S : ℕ} [Nontrivial (Fin n)]

attribute [local instance] OAI.MatchingFPRAS.Enlargement.instDecidableEqSourceLabel_8
lemma StageData.sigma_pos (c : StageData n K T) : 0 < RealStage.sigma (sourceD (V:=Fin n) K) T c.epsilon := by
  unfold RealStage.sigma RealStage.alpha
  have hD : 0 < sourceD (V:=Fin n) K := sourceD_one K
  have ht : 0 < T := c.stages
  have he := c.epsilon_positive
  exact lt_min (by positivity) (by positivity)

lemma StageData.sampleCount_pos (c : StageData n K T) :
    0 < stageSampleCount n (sourceD (V:=Fin n) K) T c.epsilon := by
  unfold stageSampleCount
  apply Nat.ceil_pos.mpr
  have hs := c.sigma_pos
  positivity



open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport Finset
open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder
open scoped Classical

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_AdaptiveLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Trial

open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis
open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder MatchingFPRAS.Adaptive
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]

noncomputable local instance instDecidableEqSourceLabelFinN_1_r4c82d9_1 (w : Fin G.n → Fin G.n → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _
lemma Parameters.S_pos (p : Parameters G) : 0<p.S := p.initialData.sampleCount_pos

attribute [instance] Layer.finite

end MatchingFPRAS.Trial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_ProductBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Variation

open Finset
open scoped Classical

variable {Ω : Type*} [Fintype Ω]

lemma uniform_fun {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] (x : I → A) :
    uniform (I → A) x=∏ i,uniform A (x i) := by
  simp [uniform,Nat.cast_pow]

omit [Fintype Ω] in
lemma imageLaw_componentwise [Fintype Ω] {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (f : I → A → Ω) : imageLaw (fun x : I → A=>fun i=>f i (x i))=
      product (fun i=>imageLaw (f i)) := by
  funext y
  let : DecidableEq (I → Ω) := Classical.decEq _
  have he (x : I → A) : (if (fun i=>f i (x i))=y then uniform (I → A) x else 0)=
      ∏ i,if f i (x i)=y i then uniform A (x i) else 0 := by
    by_cases h : (fun i=>f i (x i))=y
    · rw [ite_eq_left h,uniform_fun]
      apply prod_congr rfl
      intro i _
      rw [ite_eq_left (congrFun h i)]
    · rw [ite_eq_right h]
      obtain ⟨i,hi⟩ : ∃ i,f i (x i)≠y i := by
        by_contra hn
        apply h
        funext i
        exact Classical.not_not.mp (fun hi=>hn ⟨i,hi⟩)
      symm
      exact prod_eq_zero (mem_univ i) (ite_eq_right hi)
  unfold imageLaw push product
  simp_rw [he]
  exact (Fintype.prod_sum (fun i a=>if f i a=y i then uniform A a else 0)).symm

end MatchingFPRAS.Variation

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_Marking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Variation
lemma imageLaw_instances {A B : Type*} (F₁ F₂ : Fintype A) (f : A → B) :
    @imageLaw A B F₁ f=@imageLaw A B F₂ f := by
  cases Subsingleton.elim F₁ F₂
  rfl
end MatchingFPRAS.Variation

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_MarkBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instDecidableEqSourceLabelCastReal_1
noncomputable local instance instDecidableEqBagPMSourceVertexLabelBags_3_r4c82d9_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (BagPM (bags w K)) := Classical.decEq _
lemma sourceEdgeEquiv_central (w : V → V → ℚ) (K : ℕ) (q : LogicalEdge V) :
    sourceEdgeEquiv w K (Enlargement.centralEdge (fun x y=>(w x y:ℝ)) K q)=centralEdge w K q :=
  sourceEdgeEquiv_real w K _
end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_FiniteStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Variation
open Finset

lemma imageLaw_output_equiv {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (e : B ≃ C) (f : A → B) : imageLaw (e ∘ f)=imageLaw f ∘ e.symm := by
  classical
  funext c
  unfold imageLaw push
  apply sum_congr rfl
  intro a _
  simp only [Function.comp_apply,←Equiv.eq_symm_apply]
end MatchingFPRAS.Variation

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RationalScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Counting
open Finset

variable {n : ℕ}
lemma rowMaximum_cast (hn : 2≤n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ) (i : Fin n) :
    (rowMaximum hn G v i:ℝ)=RealStage.rowMaximum hn (fun i j=>(G i j:ℝ)) (fun i=>(v i:ℝ)) i := by
  unfold rowMaximum RealStage.rowMaximum
  rw [Finset.apply_sup'_eq_sup'_comp _ (fun q : ℚ=>(q:ℝ)) (by intro a b; exact Rat.cast_max a b)]
  simp only [Function.comp_apply,Rat.cast_div]
lemma scaleUpdate_cast (hn : 2≤n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ) (i j : Fin n) :
    (scaleUpdate hn G v i j:ℝ)=RealStage.scaleUpdate hn (fun i j=>(G i j:ℝ)) (fun i=>(v i:ℝ)) i j := by
  by_cases h : j=i
  · subst j
    simp only [scaleUpdate,RealStage.scaleUpdate,Function.update_self,rowMaximum_cast]
  · simp only [scaleUpdate,RealStage.scaleUpdate,Function.update_of_ne h]
lemma scalingTrace_cast (hn : 2≤n) (G : Fin n → Fin n → ℚ) (k : ℕ) (i : Fin n) :
    (scalingTrace hn G k i:ℝ)=RealStage.scalingTrace hn (fun i j=>(G i j:ℝ)) k i := by
  induction k generalizing i with
  | zero => norm_num [scalingTrace,RealStage.scalingTrace]
  | succ k ih =>
    simp only [scalingTrace,RealStage.scalingTrace]
    split_ifs with h
    · rw [scaleUpdate_cast]
      have hi : (fun j=>(Counting.scalingTrace hn G k j:ℝ))=RealStage.scalingTrace hn (fun i j=>(G i j:ℝ)) k := by
        funext j
        exact ih j
      rw [hi]
    · exact ih i
lemma upperEstimate_cast (D : ℕ) (d z : ℚ) :
    (upperEstimate D d z:ℝ)=RealStage.upperEstimate D d z := by
  simp only [upperEstimate,RealStage.upperEstimate]
  have hp : (0:ℝ)<d ↔ (0:ℚ)<d := by exact_mod_cast Iff.rfl
  simp only [hp]
  split_ifs <;> push_cast <;> norm_num [alpha,RealStage.alpha]
end MatchingFPRAS.Counting

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RationalObservables
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport
open Finset

variable {V E F I : Type*} [Fintype V] [DecidableEq V]
variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F] [Fintype I]
variable {inc : E → V → Prop} {j : F → V → Prop}
omit [DecidableEq V] [Fintype E] [Fintype F] in
lemma markedEquiv_probe (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (a : Marking.Marked (I:=Fin 3) inc) (u : E) :
    ({e u}⊆(markedEquiv e he a).1.val ∧
      (markedEquiv e he a).2=(fun x=>if x.val∈({e u}:Finset _) then 2 else 0)) ↔
    ({u}⊆a.1.val ∧ a.2=(fun x=>if x.val∈({u}:Finset _) then 2 else 0)) := by
  rw [markedEquiv_marks_eq e he a (fun x=>if x∈({e u}:Finset F) then 2 else 0)]
  rw [singleton_subset_iff,singleton_subset_iff]
  change (e u∈a.1.val.image e ∧ _) ↔ (u∈a.1.val ∧ _)
  simp only [mem_singleton,e.injective.eq_iff,
    mem_image,exists_eq_right]
omit [DecidableEq V] [Fintype E] [Fintype F] in
lemma pmEquiv_product_erase {R : Type*} [CommMonoid R]
    (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v) (M : PM inc) (u : E) (f : F → R) :
    (∏ x ∈ (pmEquiv e he M).val \ {e u},f x)=∏ x ∈ M.val \ {u},f (e x) := by
  have hh : (pmEquiv e he M).val \ {e u}=(M.val \ {u}).image e := by
    change M.val.image e \ {e u}=(M.val \ {u}).image e
    ext x
    simp only [mem_sdiff,mem_image,mem_singleton]
    constructor
    · rintro ⟨⟨y,hy,rfl⟩,hu⟩
      exact ⟨y,⟨hy,fun h=>hu (congrArg e h)⟩,rfl⟩
    · rintro ⟨y,⟨hy,hu⟩,rfl⟩
      exact ⟨⟨y,hy,rfl⟩,fun h=>hu (e.injective h)⟩
  rw [hh]
  exact prod_image (fun _ _ _ _ h=>e.injective h)
end MatchingFPRAS.Transport
namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instDecidableEqSourceLabelCastReal_3
lemma observableProbe_cast (w w₁ : V → V → ℚ) (K : ℕ) (u : LogicalEdge V)
    (a : SourceMarked (fun x y=>(w x y:ℝ)) K) :
    (observableProbe w w₁ K u (sourceMarkedEquiv w K a):ℝ)=
      Enlargement.observableProbe (fun x y=>(w x y:ℝ)) (fun x y=>(w₁ x y:ℝ)) K u a := by
  have hh:=markedEquiv_probe (inc:=BagEdge.Incident (bags:=sourceBags (fun x y=>(w x y:ℝ)) K))
    (j:=BagEdge.Incident (bags:=bags w K)) (sourceEdgeEquiv w K) (sourceEdgeEquiv_incidence w K) a
    (Enlargement.centralEdge (fun x y=>(w x y:ℝ)) K u)
  rw [sourceEdgeEquiv_central] at hh
  change ({centralEdge w K u}⊆(sourceMarkedEquiv w K a).1.val ∧
    (sourceMarkedEquiv w K a).2=(fun e=>if e.val∈({centralEdge w K u}:Finset _) then 2 else 0)) ↔ _ at hh
  simp only [observableProbe,Enlargement.observableProbe,hh]
  simp only [mem_singleton] at hh ⊢
  split_ifs <;> try contradiction
  · push_cast
    rw [←sourceEdgeEquiv_central w K u]
    change (∏ e ∈ (pmEquiv (inc:=BagEdge.Incident (bags:=sourceBags (fun x y=>(w x y:ℝ)) K))
    (j:=BagEdge.Incident (bags:=bags w K)) (sourceEdgeEquiv w K) (sourceEdgeEquiv_incidence w K) a.1).val \
      {sourceEdgeEquiv w K (Enlargement.centralEdge (fun x y=>(w x y:ℝ)) K u)},
      (bagReweight w w₁ K e:ℝ))=_
    rw [pmEquiv_product_erase (sourceEdgeEquiv w K) (sourceEdgeEquiv_incidence w K)]
    refine prod_congr (by ext; simp) ?_
    intro e _
    exact bagReweight_cast w w₁ K e
  · norm_cast
end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RationalEstimator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Finset Enlargement Transport

variable {V : Type*} [LinearOrder V]
lemma estimateMatrix_cast (D : ℕ) (dbar : ℚ) (zbar : LogicalEdge V → ℚ) (i j : V) :
    (estimateMatrix D dbar zbar i j:ℝ)=Enlargement.estimateMatrix D dbar (fun e=>(zbar e:ℝ)) i j := by
  rw [estimateMatrix,Counting.upperEstimate_cast,probeMatrix_cast]
  rfl

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelFinNCastReal_r4c82d9_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
omit [Nontrivial (Fin G.n)] in
lemma sourceD_eq (K : ℕ) : sourceD (G:=G) K=Enlargement.sourceD (V:=Fin G.n) K := by
  simp only [sourceD,Enlargement.sourceD,Fintype.card_fin]

lemma average_Probe (w w₁ : Fin G.n → Fin G.n → ℚ) (K : ℕ) (e : LogicalEdge (Fin G.n))
    (x : Fin S → SourceMarked (fun a b=>(w a b:ℝ)) K) :
    (sampleAverage (RationalSource.observableProbe w w₁ K e) (RationalSource.sourceMarkedEquiv w K ∘ x):ℝ)=
      Enlargement.sampleAverage (Enlargement.observableProbe (fun a b=>(w a b:ℝ)) (fun a b=>(w₁ a b:ℝ)) K e) x := by
  simp only [sampleAverage,Enlargement.sampleAverage,Rat.cast_div,Rat.cast_sum,Rat.cast_natCast,Function.comp_apply,
    RationalSource.observableProbe_cast]
lemma ScaleState.matrix_cast (s : ScaleState G j)
    (x : Fin S → SourceMarked (fun a b=>(s.activity a b:ℝ)) K) :
    (fun a b=>(s.matrix (RationalSource.sourceMarkedEquiv s.activity K ∘ x) a b:ℝ))=
      Enlargement.estimateMatrix (sourceD (G:=G) K)
        (Enlargement.sampleAverage (Enlargement.observableD (fun a b=>(s.activity a b:ℝ))
          (fun a b=>(s.nextActivity a b:ℝ)) K) x)
        (fun e=>Enlargement.sampleAverage (Enlargement.observableProbe (fun a b=>(s.activity a b:ℝ))
          (fun a b=>(s.nextActivity a b:ℝ)) K e) x) := by
  funext a b
  simp only [ScaleState.matrix,estimateMatrix_cast,average_D,average_Probe]
end MatchingFPRAS.FiniteTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_SortedList
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.BitArithmetic
open Finset

lemma FractionBound.mono {B C : ℕ} {x : ℝ} (h : FractionBound B x) (hBC : B≤C) : FractionBound C x := by
  obtain ⟨a,b,hb,ha,hbb,rfl⟩ := h
  exact ⟨a,b,hb,ha.trans hBC,hbb.trans hBC,rfl⟩
lemma FractionBound.zero {B : ℕ} (hB : 1≤B) : FractionBound B 0 :=
  ⟨0,1,by omega,by omega,hB,by simp⟩
lemma FractionBound.one {B : ℕ} (hB : 1≤B) : FractionBound B 1 :=
  ⟨1,1,by omega,hB,hB,by simp⟩
lemma FractionBound.nat (a : ℕ) : FractionBound (a+1) a :=
  ⟨a,1,by omega,by omega,by omega,by simp⟩
lemma FractionBound.mul {B C : ℕ} {x y : ℝ} (hx : FractionBound B x) (hy : FractionBound C y) :
    FractionBound (B*C) (x*y) := by
  obtain ⟨a,b,hb,ha,hbb,rfl⟩ := hx
  obtain ⟨c,d,hd,hc,hdd,rfl⟩ := hy
  refine ⟨a*c,b*d,Nat.mul_pos hb hd,Nat.mul_le_mul ha hc,Nat.mul_le_mul hbb hdd,?_⟩
  push_cast
  ring
lemma FractionBound.div {B C : ℕ} {x y : ℝ} (hx : FractionBound B x) (hy : FractionBound C y)
    (hy0 : 0<y) : FractionBound (B*C) (x/y) := by
  obtain ⟨a,b,hb,ha,hbb,rfl⟩ := hx
  obtain ⟨c,d,hd,hc,hdd,rfl⟩ := hy
  have hc0 : 0 < c := by
    have hd0 : (0:ℝ)<d := by exact_mod_cast hd
    have hcr := (lt_div_iff₀ hd0).mp hy0
    exact_mod_cast (by simpa using hcr : (0:ℝ) < c)
  refine ⟨a*d,b*c,Nat.mul_pos hb hc0,Nat.mul_le_mul ha hdd,Nat.mul_le_mul hbb hc,?_⟩
  push_cast
  field_simp
lemma FractionBound.add {B C : ℕ} {x y : ℝ} (hx : FractionBound B x) (hy : FractionBound C y) :
    FractionBound (2*B*C) (x+y) := by
  obtain ⟨a,b,hb,ha,hbb,rfl⟩ := hx
  obtain ⟨c,d,hd,hc,hdd,rfl⟩ := hy
  refine ⟨a*d+c*b,b*d,Nat.mul_pos hb hd,?_,?_,?_⟩
  · have h₁ := Nat.mul_le_mul ha hdd
    have h₂ := Nat.mul_le_mul hc hbb
    nlinarith
  · have h₁ := Nat.mul_le_mul hbb hdd
    nlinarith
  · have hb0 : (b:ℝ)≠0 := by exact_mod_cast hb.ne'
    have hd0 : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
    push_cast
    field_simp
lemma FractionBound.sup' {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (B : ℕ)
    (h : ∀ i∈s,FractionBound B (f i)) : FractionBound B (s.sup' hs f) := by
  obtain ⟨i,hi,he⟩ := exists_mem_eq_sup' hs f
  rw [he]
  exact h i hi
lemma FractionBound.max {B : ℕ} {x y : ℝ} (hx : FractionBound B x) (hy : FractionBound B y) :
    FractionBound B (max x y) := by
  rcases le_total x y with h|h
  · simpa [max_eq_right h] using hy
  · simpa [max_eq_left h] using hx
lemma FractionBound.min {B : ℕ} {x y : ℝ} (hx : FractionBound B x) (hy : FractionBound B y) :
    FractionBound B (min x y) := by
  rcases le_total x y with h|h
  · simpa [min_eq_left h] using hx
  · simpa [min_eq_right h] using hy
end MatchingFPRAS.BitArithmetic

namespace MatchingFPRAS.Trial
open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis BitArithmetic
open scoped Classical

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
lemma cooling_fraction (n : ℕ) (hn : 0<n) : cooling n=(n:ℝ)/(n+1) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  unfold cooling
  field_simp
omit [Nontrivial (Fin G.n)] in
lemma ScaleState.edge_ratio (s : ScaleState G j) (a b : Fin G.n) :
    s.nextActivity a b/s.activity a b=1 ∨ s.nextActivity a b/s.activity a b=Trial.cooling G.n := by
  have hs₀ := (s.positive a).ne'
  have hs₁ := (s.positive b).ne'
  have hr := (raw_pos G j a b).ne'
  have he : s.nextActivity a b/s.activity a b=raw G (j+1) a b/raw G j a b := by
    unfold ScaleState.nextActivity ScaleState.activity
    field_simp
  rw [he]
  unfold raw GraphBridge.rawActivity
  split_ifs
  · left; simp
  · right
    rw [pow_succ]
    exact mul_div_cancel_left₀ _ (pow_pos (cooling_pos G.n) j).ne'
lemma ScaleState.bag_reweight (s : ScaleState G j) (e : BagEdge (sourceBags s.activity K)) :
    bagReweight s.activity s.nextActivity K e=1 ∨
      bagReweight s.activity s.nextActivity K e=Trial.cooling G.n := by
  unfold bagReweight
  split_ifs with he
  · unfold rawReweight
    split_ifs
    · unfold logicalActivity edgeActivity
      split_ifs <;> exact s.edge_ratio _ _
    · exact Or.inl rfl
  · exact Or.inl rfl
lemma product_binary_power {E : Type*} (A : Finset E) (f : E → ℝ) (c : ℝ)
    (hf : ∀ e∈A,f e=1 ∨ f e=c) : ∃ a≤A.card,∏ e∈A,f e=c^a := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨0,by simp,by simp⟩
  | @insert e A he ih =>
    obtain ⟨a,ha,hea⟩ := ih (fun i hi=>hf i (mem_insert_of_mem hi))
    rcases hf e (mem_insert_self _ _) with h|h
    · refine ⟨a,by simpa [card_insert_of_notMem he] using (Nat.le_succ_of_le ha),?_⟩
      rw [prod_insert he,h,one_mul,hea]
    · refine ⟨a+1,by simpa [card_insert_of_notMem he] using Nat.succ_le_succ ha,?_⟩
      rw [prod_insert he,h,hea,pow_succ,mul_comm]
lemma ScaleState.pm_card (s : ScaleState G j) (a : SourceMarked s.activity K) :
    a.1.val.card≤ Fintype.card (SourceVertex (Fin G.n) K) := by
  let : Fintype (BagEdge (sourceBags s.activity K)) := Fintype.ofFinite _
  apply PM.card_le_vertices
  intro e
  exact ⟨e.val.val.1.out.1,by
    change e.val.val.1.out.1∈e.val.val.1
    exact Sym2.out_fst_mem _⟩
lemma ScaleState.observable_power (s : ScaleState G j) (a : SourceMarked s.activity K) :
    (observableA s.activity K a=0 ∨ observableA s.activity K a=1) ∧
    (observableD s.activity s.nextActivity K a=0 ∨
      ∃ t≤Fintype.card (SourceVertex (Fin G.n) K),observableD s.activity s.nextActivity K a=Trial.cooling G.n^t) ∧
    (∀ e₀,observableProbe s.activity s.nextActivity K e₀ a=0 ∨
      ∃ t≤Fintype.card (SourceVertex (Fin G.n) K),observableProbe s.activity s.nextActivity K e₀ a=Trial.cooling G.n^t) := by
  refine ⟨?_,?_,?_⟩
  · unfold observableA
    split_ifs <;> simp
  · unfold observableD
    split_ifs
    · right
      obtain ⟨t,ht,he⟩ := product_binary_power a.1.val _ (Trial.cooling G.n) (fun e _=>s.bag_reweight e)
      exact ⟨t,ht.trans (s.pm_card a),he⟩
    · exact Or.inl rfl
  · intro e₀
    unfold observableProbe
    split_ifs
    · right
      obtain ⟨t,ht,he⟩ := product_binary_power (a.1.val\{centralEdge s.activity K e₀}) _
        (Trial.cooling G.n) (fun e _=>s.bag_reweight e)
      refine ⟨t,ht.trans ((card_le_card sdiff_subset).trans (s.pm_card a)),?_⟩
      convert he using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ext e
      simp only [mem_sdiff,mem_singleton]
    · exact Or.inl rfl
end MatchingFPRAS.Trial

namespace MatchingFPRAS.BitArithmetic
open Finset

lemma GridFraction.zero (Q : ℕ) : GridFraction Q 0 := ⟨0,Nat.zero_le _,by simp⟩
lemma GridFraction.one {Q : ℕ} (hQ : 0<Q) : GridFraction Q 1 :=
  ⟨Q,le_rfl,(div_self (by exact_mod_cast hQ.ne')).symm⟩
lemma GridFraction.fractionBound {Q : ℕ} {x : ℝ} (hQ : 0<Q) (h : GridFraction Q x) :
    FractionBound Q x := by
  obtain ⟨a,ha,he⟩ := h
  exact ⟨a,Q,hQ,ha,le_rfl,he⟩
lemma GridFraction.average {Ω : Type*} {S Q : ℕ} (f : Ω → ℝ) (x : Fin S → Ω)
    (h : ∀ i,GridFraction Q (f (x i))) :
    GridFraction (S*Q) (Enlargement.sampleAverage f x) := by
  classical
  choose a ha he using h
  refine ⟨∑ i,a i,?_,?_⟩
  · calc
      _ ≤ ∑ _i : Fin S,Q := sum_le_sum fun i _=>ha i
      _ = S*Q := by simp
  · unfold Enlargement.sampleAverage
    simp_rw [he]
    rw [← sum_div]
    push_cast
    ring
lemma GridFraction.cooling_power (n N t : ℕ) (ht : t≤N) :
    GridFraction ((n+1)^N) (((n:ℝ)/(n+1))^t) := by
  refine ⟨n^t*(n+1)^(N-t),?_,?_⟩
  · calc
      _ ≤ (n+1)^t*(n+1)^(N-t) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _)
      _ = (n+1)^N := by rw [←pow_add,Nat.add_sub_of_le ht]
  · have hpos : (0:ℝ)<n+1 := by positivity
    have he : ((n+1:ℕ):ℝ)=n+1 := by push_cast; rfl
    push_cast
    rw [div_pow,show N=t+(N-t) from (Nat.add_sub_of_le ht).symm,pow_add]
    field_simp
    congr 2
    omega

lemma FractionBound.prod {ι : Type*} (A : Finset ι) (f : ι → ℝ) (B : ℕ)
    (h : ∀ i∈A,FractionBound B (f i)) : FractionBound (B^A.card) (∏ i∈A,f i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using FractionBound.one (B:=1) le_rfl
  | @insert i A hi ih =>
    simpa [prod_insert hi,card_insert_of_notMem hi,pow_succ,Nat.mul_comm] using
      (h i (mem_insert_self _ _)).mul (ih (fun j hj=>h j (mem_insert_of_mem hj)))
end MatchingFPRAS.BitArithmetic

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_EmpiricalDenom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Trial
open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis BitArithmetic
open scoped Classical

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
lemma empiricalDenom_pos (G : GraphInput) (K : ℕ) : 0<empiricalDenom G K := by unfold empiricalDenom; positivity
lemma ScaleState.observables_grid (hn : 0<G.n) (s : ScaleState G j) (a : SourceMarked s.activity K) :
    GridFraction (empiricalDenom G K) (observableA s.activity K a) ∧
    GridFraction (empiricalDenom G K) (observableD s.activity s.nextActivity K a) ∧
    ∀ e₀,GridFraction (empiricalDenom G K) (observableProbe s.activity s.nextActivity K e₀ a) := by
  have h := s.observable_power a
  refine ⟨?_,?_,?_⟩
  · rcases h.1 with he|he
    · rw [he]; exact GridFraction.zero _
    · rw [he]; exact GridFraction.one (empiricalDenom_pos G K)
  · rcases h.2.1 with he|⟨t,ht,he⟩
    · rw [he]; exact GridFraction.zero _
    · rw [he,cooling_fraction G.n hn]
      exact GridFraction.cooling_power G.n _ t ht
  · intro e₀
    rcases h.2.2 e₀ with he|⟨t,ht,he⟩
    · rw [he]; exact GridFraction.zero _
    · rw [he,cooling_fraction G.n hn]
      exact GridFraction.cooling_power G.n _ t ht
lemma ScaleState.means_bits (hn : 0<G.n) (s : ScaleState G j)
    (hS : 0<S) (x : Fin S → SourceMarked s.activity K) :
    FractionBound (S*empiricalDenom G K) (sampleAverage (observableA s.activity K) x) ∧
    FractionBound (S*empiricalDenom G K) (sampleAverage (observableD s.activity s.nextActivity K) x) ∧
    ∀ e₀,FractionBound (S*empiricalDenom G K) (sampleAverage (observableProbe s.activity s.nextActivity K e₀) x) := by
  have hpos := Nat.mul_pos hS (empiricalDenom_pos G K)
  refine ⟨?_,?_,?_⟩
  · exact (GridFraction.average _ x (fun i=>(s.observables_grid hn (x i)).1)).fractionBound hpos
  · exact (GridFraction.average _ x (fun i=>(s.observables_grid hn (x i)).2.1)).fractionBound hpos
  · intro e₀
    exact (GridFraction.average _ x (fun i=>(s.observables_grid hn (x i)).2.2 e₀)).fractionBound hpos
end MatchingFPRAS.Trial

namespace MatchingFPRAS.BitArithmetic
open Finset

lemma alpha_bits : FractionBound 100000 RealStage.alpha := by
  exact ⟨1,100000,by norm_num,by norm_num,le_rfl,by norm_num [RealStage.alpha]⟩
lemma matrixBound_large (D B : ℕ) (hB : 1≤B) : 100000 ≤ matrixBound D B := by
  unfold matrixBound
  have hb2 : 1≤B^2 := one_le_pow₀ hB
  nlinarith
lemma ratioEstimate_bits {B : ℕ} {a d : ℝ} (hB : 1≤B)
    (ha : FractionBound B a) (hd : FractionBound B d) :
    FractionBound (B^2) (RealStage.ratioEstimate a d) := by
  unfold RealStage.ratioEstimate
  split_ifs with h
  · simpa [pow_two] using hd.div ha h
  · exact FractionBound.one (one_le_pow₀ hB)
lemma upperEstimate_bits (D : ℕ) {B : ℕ} {d z : ℝ} (hB : 1≤B)
    (hd : FractionBound B d) (hz : FractionBound B z) :
    FractionBound (matrixBound D B) (RealStage.upperEstimate D d z) := by
  have hlarge := matrixBound_large D B hB
  unfold RealStage.upperEstimate
  split_ifs with h
  · have ht : FractionBound (matrixBound D B) ((D:ℝ)*z/d+RealStage.alpha) := by
      convert (((FractionBound.nat D).mul hz).div hd h).add alpha_bits using 1
      all_goals try with_reducible_and_instances rfl
      unfold matrixBound
      ring
    exact (alpha_bits.mono hlarge).max
      ((FractionBound.nat 3 |>.mono (by omega)).min ht)
  · exact FractionBound.one (by omega)
lemma scalingTrace_bits {n : ℕ} (hn : 2≤n) (G : Fin n → Fin n → ℝ)
    (hsym : ∀ i j,G i j=G j i) (hG : ∀ i j,i≠j → RealStage.alpha≤G i j ∧ G i j≤3)
    (B : ℕ) (hB : 2≤B) (hb : ∀ i j,FractionBound B (G i j)) (k : ℕ) :
    ∀ i,FractionBound (B^(k+1)) (RealStage.scalingTrace hn G k i) := by
  have hB1 : 1≤B := by omega
  induction k with
  | zero =>
    intro i
    change FractionBound (B^(0+1)) 2
    simpa using (show FractionBound B (2:ℝ) from ⟨2,1,by omega,hB,hB1,by norm_num⟩)
  | succ k ih =>
    intro i
    have hmono : B^(k+1)≤B^(k+1+1) := Nat.pow_le_pow_right hB1 (by omega)
    dsimp only [RealStage.scalingTrace]
    split_ifs with hk
    · unfold RealStage.scaleUpdate
      by_cases hi : i=⟨k,hk⟩
      · subst i
        simp only [Function.update_self]
        unfold RealStage.rowMaximum
        have hpos := (RealStage.scalingTrace_invariant hn G hsym hG k).1.pos
        convert FractionBound.sup' (univ.erase (⟨k,hk⟩ : Fin n)) (RealStage.others_nonempty hn _)
          (fun j=>G ⟨k,hk⟩ j / RealStage.scalingTrace hn G k j) (B*B^(k+1))
          (fun j _=>(hb ⟨k,hk⟩ j).div (ih j) (hpos j)) using 1
        all_goals try with_reducible_and_instances rfl
        rw [pow_succ,Nat.mul_comm]
      · rw [Function.update_of_ne hi]
        exact (ih i).mono hmono
    · exact (ih i).mono hmono
end MatchingFPRAS.BitArithmetic

namespace MatchingFPRAS.Trial
open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis BitArithmetic
open scoped Classical

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
lemma ScaleState.ratioEstimate_bits (hn : 0<G.n) (s : ScaleState G j)
    (hS : 0<S) (x : Fin S → SourceMarked s.activity K) :
    FractionBound ((S*empiricalDenom G K)^2) (s.ratioEstimate x) := by
  have hb := s.means_bits hn hS x
  exact BitArithmetic.ratioEstimate_bits (Nat.mul_pos hS (empiricalDenom_pos G K)) hb.1 hb.2.1
lemma ScaleState.matrix_bits (hn : 0<G.n) (s : ScaleState G j)
    (hS : 0<S) (x : Fin S → SourceMarked s.activity K) (a b : Fin G.n) :
    FractionBound (matrixBound (sourceD (V:=Fin G.n) K) (S*empiricalDenom G K)) (s.matrix x a b) := by
  have hb := s.means_bits hn hS x
  unfold ScaleState.matrix estimateMatrix
  apply upperEstimate_bits _ (Nat.mul_pos hS (empiricalDenom_pos G K)) hb.2.1
  unfold probeMatrix
  split_ifs
  · exact FractionBound.zero (Nat.mul_pos hS (empiricalDenom_pos G K))
  · exact hb.2.2 _
open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis BitArithmetic
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
omit [Nontrivial (Fin G.n)] in
lemma initial_scale_bits (hn : 2≤G.n) (a : Fin G.n) :
    FractionBound (G.n+1) ((initialScaleState G hn).scale a) := by
  refine ⟨1,Nat.sqrt (G.n-1),?_,by omega,?_,?_⟩
  · exact Nat.le_sqrt.mpr (by omega)
  · exact (Nat.sqrt_le_self _).trans (by omega)
  · change (Initializer.initialScale G.n:ℝ)=_
    simp [Initializer.initialScale]

end MatchingFPRAS.Trial

namespace MatchingFPRAS.FiniteTrial
open Finset Enlargement Transport BitArithmetic
open scoped Classical

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelFinNCastReal_3_r4c82d9_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
lemma ScaleState.ratioEstimate_bits (hn : 0<G.n) (s : ScaleState G j) (hS : 0<S)
    (x : Fin S → SourceMarked (fun a b=>(s.activity a b:ℝ)) K) :
    FractionBound ((S*Trial.empiricalDenom G K)^2)
      (s.ratioEstimate (RationalSource.sourceMarkedEquiv s.activity K ∘ x):ℝ) := by
  have hb := s.toReal.ratioEstimate_bits (K:=K) (S:=S) hn hS
  unfold Trial.ScaleState.ratioEstimate at hb
  rw [←s.activity_cast,←s.nextActivity_cast] at hb
  rw [s.ratioEstimate_cast]
  exact hb x
lemma ScaleState.matrix_bits (hn : 0<G.n) (s : ScaleState G j) (hS : 0<S)
    (x : Fin S → SourceMarked (fun a b=>(s.activity a b:ℝ)) K) (a b : Fin G.n) :
    FractionBound (matrixBound (Enlargement.sourceD (V:=Fin G.n) K) (S*Trial.empiricalDenom G K))
      (s.matrix (RationalSource.sourceMarkedEquiv s.activity K ∘ x) a b:ℝ) := by
  have hb := s.toReal.matrix_bits (K:=K) (S:=S) hn hS
  unfold Trial.ScaleState.matrix at hb
  rw [←s.activity_cast,←s.nextActivity_cast] at hb
  have he := congrFun (congrFun (s.matrix_cast x) a) b
  rw [he,sourceD_eq]
  exact hb x a b
lemma ScaleState.updateVector_bits (hn : 2≤G.n) (s : ScaleState G j) (hS : 0<S)
    (x : Fin S → SourceMarked (fun a b=>(s.activity a b:ℝ)) K) (a : Fin G.n) :
    FractionBound ((matrixBound (Enlargement.sourceD (V:=Fin G.n) K) (S*Trial.empiricalDenom G K))^(G.n+1))
      (s.updateVector hn (RationalSource.sourceMarkedEquiv s.activity K ∘ x) a:ℝ) := by
  rw [ScaleState.updateVector,Counting.scalingTrace_cast]
  apply scalingTrace_bits hn _ _ _ _ _ _ _ a
  · intro a b
    exact_mod_cast s.matrix_symm _ a b
  · intro a b _
    have h:=s.matrix_bounds (RationalSource.sourceMarkedEquiv s.activity K ∘ x) a b
    constructor
    · have hh : ((Counting.alpha:ℚ):ℝ) ≤ (s.matrix (RationalSource.sourceMarkedEquiv s.activity K ∘ x) a b:ℝ) := by exact_mod_cast h.1
      simpa [Counting.alpha,RealStage.alpha] using hh
    · exact_mod_cast h.2
  · have h:=matrixBound_large (Enlargement.sourceD (V:=Fin G.n) K) (S*Trial.empiricalDenom G K)
      (Nat.mul_pos hS (Trial.empiricalDenom_pos G K))
    omega
  · intro a b
    exact s.matrix_bits (by omega) hS x a b
omit [Nontrivial (Fin G.n)] in
lemma initial_scale_bits (hn : 2≤G.n) (a : Fin G.n) :
    FractionBound (G.n+1) ((initialScaleState G hn).scale a:ℝ) := by
  exact Trial.initial_scale_bits hn a
lemma layers_scale_bits (p : Trial.Parameters G) (j : ℕ) (hj : j≤p.K)
    (x : (layers p j hj).Ω) (a : Fin G.n) :
    FractionBound (p.scaleBound j) ((layers p j hj).state x |>.scale a:ℝ) := by
  induction j with
  | zero => simpa [layers,firstLayer,Trial.Parameters.scaleBound] using initial_scale_bits p.hn a
  | succ j ih =>
    change FractionBound _ ((((layers p j (by omega)).state x.1).scale a *
      ((layers p j (by omega)).state x.1).updateVector p.hn
        (RationalSource.sourceMarkedEquiv ((layers p j (by omega)).state x.1).activity p.K ∘ x.2) a:ℚ):ℝ)
    rw [Rat.cast_mul]
    have hv := ((layers p j (by omega)).state x.1).updateVector_bits p.hn p.S_pos x.2 a
    have hh := (ih (by omega) x.1).mul hv
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    change (G.n+1)*p.matrixBound^((j+1)*(G.n+1))=
      ((G.n+1)*p.matrixBound^(j*(G.n+1)))*p.matrixBound^(G.n+1)
    rw [add_mul,one_mul,pow_add]
    ring
lemma layers_ratio_bits (p : Trial.Parameters G) (j : ℕ) (hj : j≤p.K)
    (x : (layers p j hj).Ω) (i : Fin j) :
    FractionBound (p.empiricalBound^2) ((layers p j hj).ratios x i:ℝ) := by
  induction j with
  | zero => exact Fin.elim0 i
  | succ j ih =>
    refine Fin.lastCases ?_ (fun i=>?_) i
    · simpa only [layers,Layer.append,Fin.snoc_last,Trial.Parameters.empiricalBound] using
        ((layers p j (by omega)).state x.1).ratioEstimate_bits (by have := p.hn; omega) p.S_pos x.2
    · simpa only [layers,Layer.append,Fin.snoc_castSucc] using ih (by omega) x.1 i
end MatchingFPRAS.FiniteTrial

namespace MatchingFPRAS.BitArithmetic
lemma FractionBound.num_den {B : ℕ} {q : ℚ} (h : FractionBound B (q:ℝ)) :
    q.num.natAbs≤B ∧ q.den≤B := by
  obtain ⟨a,b,hb,ha,hbb,he⟩:=h
  have hq : q=(a:ℚ)/b := by
    apply Rat.cast_injective (α:=ℝ)
    simpa only [Rat.cast_div,Rat.cast_natCast] using he
  have hq' : q=Rat.divInt (a:ℤ) (b:ℤ) := by simpa only [Rat.divInt_eq_div,Int.cast_natCast] using hq
  have hb0 : (b:ℤ)≠0 := by exact_mod_cast hb.ne'
  have hd : q.den∣b := by
    have hh:=Rat.den_dvd (a:ℤ) (b:ℤ)
    rw [←hq'] at hh
    exact_mod_cast hh
  refine ⟨?_,(Nat.le_of_dvd hb hd).trans hbb⟩
  by_cases ha0 : a=0
  · simp [ha0] at hq
    simp [hq]
  · have hh:=Rat.num_dvd (a:ℤ) hb0
    rw [←hq'] at hh
    have hn : q.num.natAbs∣a := by simpa using Int.natAbs_dvd_natAbs.mpr hh
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hn).trans ha
lemma size_mul_le (a b : ℕ) : (a*b).size≤a.size+b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  have h₁:=Nat.lt_size_self a
  have h₂:=Nat.lt_size_self b
  have h₃ : 0<(2:ℕ)^a.size := by positivity
  nlinarith
lemma size_pow_le (a k : ℕ) : (a^k).size≤k*a.size+1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have h:=size_mul_le (a^k) a
    rw [Nat.succ_mul]
    omega
lemma size_empiricalBound {G : GraphInput} (p : Trial.Parameters G) :
    p.empiricalBound.size≤p.S.size+Fintype.card (Enlargement.SourceVertex (Fin G.n) p.K)*(G.n+1).size+1 := by
  unfold Trial.Parameters.empiricalBound Trial.empiricalDenom
  exact (size_mul_le _ _).trans (by have h:=size_pow_le (G.n+1) (Fintype.card (Enlargement.SourceVertex (Fin G.n) p.K)); omega)
lemma size_matrixBound {G : GraphInput} (p : Trial.Parameters G) :
    p.matrixBound.size≤19+(p.D+1).size+2*p.empiricalBound.size := by
  unfold Trial.Parameters.matrixBound matrixBound
  have h₁:=size_mul_le (200000*(p.D+1)) (p.empiricalBound^2)
  have h₂:=size_mul_le 200000 (p.D+1)
  have h₃:=size_pow_le p.empiricalBound 2
  have h₄ : (200000:ℕ).size=18 := by decide
  omega
lemma size_scaleBound {G : GraphInput} (p : Trial.Parameters G) (j : ℕ) :
    (p.scaleBound j).size≤(G.n+1).size+j*(G.n+1)*p.matrixBound.size+1 := by
  unfold Trial.Parameters.scaleBound
  have h₁:=size_mul_le (G.n+1) (p.matrixBound^(j*(G.n+1)))
  have h₂:=size_pow_le p.matrixBound (j*(G.n+1))
  omega
end MatchingFPRAS.BitArithmetic

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeBits
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.instCodecData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeData

lemma bits_length (A : List Bool) : (encode (bits A)).length≤4*A.length+1 := by
  induction A with
  | nil => simp [encode]
  | cons b A ih => cases b <;> simp only [bits_cons,encode,bit,Bool.false_eq_true,↓reduceIte,
      List.length_cons,List.length_append,List.length_nil] <;> omega
end MatchingFPRAS.TreeData

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeFraction
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma normalize_repr (x : Fraction) : normalize x=repr (val x) := by
  by_cases hd : x.2=0
  · simp [normalize,repr,val,hd]
  · have he : val x=mkRat (x.1:Int) x.2 := by simp [val,Rat.mkRat_eq_div]
    simp only [normalize,hd,↓reduceIte,he,repr,Rat.num_mkRat,Rat.den_mkRat]
    simp [Nat.gcd_comm,←Int.natCast_ediv]

lemma val_nonneg (x : Fraction) : 0≤val x := by unfold val; positivity
lemma val_repr {q : ℚ} (h : 0≤q) : val (repr q)=q := by
  have hn : 0≤q.num := by exact Rat.num_nonneg.mpr h
  have he : (q.num.natAbs : ℤ)=q.num := Int.natAbs_of_nonneg hn
  change (q.num.natAbs:ℚ)/(q.den:ℚ)=q
  rw [←Int.cast_natCast q.num.natAbs,he]
  exact Rat.num_div_den q

lemma normalize_val (x : Fraction) : val (normalize x)=val x := by
  rw [normalize_repr]
  exact val_repr (val_nonneg x)

lemma mul_val (x y : Fraction) : val (mul (x,y))=val x*val y := by
  rw [mul,normalize_val]
  simp only [val,Nat.cast_mul]
  exact (div_mul_div_comm _ _ _ _).symm

lemma add_val (x y : Fraction) (hx : x.2≠0) (hy : y.2≠0) :
    val (add (x,y))=val x+val y := by
  rw [add,normalize_val]
  simp only [val,Nat.cast_add,Nat.cast_mul]
  rw [div_add_div (x.1:ℚ) (y.1:ℚ) (b:=(x.2:ℚ)) (d:=(y.2:ℚ))
    (by exact_mod_cast hx) (by exact_mod_cast hy)]
  ring

lemma div_val (x y : Fraction) : val (div (x,y))=val x/val y := by
  rw [div,normalize_val]
  simp only [val,Nat.cast_mul]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

lemma less_val (x y : Fraction) (hx : 0<x.2) (hy : 0<y.2) :
    less (x,y)=decide (val x<val y) := by
  unfold less
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [val,val,div_lt_div_iff₀ (by exact_mod_cast hx) (by exact_mod_cast hy)]
  norm_cast

end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeFunction Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

lemma polynomial_eval_monotone (p : Polynomial ℕ) : Monotone (fun n=>p.eval n) := by
  intro a b hab
  simp only [Polynomial.eval_eq_sum,Polynomial.sum_def]
  exact Finset.sum_le_sum (fun i _=>Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i))

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreePolynomialArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeFunction Polynomial

lemma weight_bits (bs : List Bool) : weight bs≤4*bs.length+1 := TreeData.bits_length bs
lemma weight_nat (n : ℕ) : weight n=weight n.bits := rfl
lemma weight_nat_le (n : ℕ) : weight n≤4*n.size+1 := by
  rw [weight_nat,←Nat.size_eq_bits_len]; exact weight_bits _
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreePolynomialLists
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]
omit [Codec A] in
lemma weight_map_bound {f : A → B} {as : List A} {N : ℕ}
    (h : ∀ a∈as,weight (f a)≤N) : weight (as.map f)≤as.length*(N+1)+1 := by
  induction as with
  | nil => simp
  | cons a as ih =>
    have ht:=ih (fun b hb=>h b (by simp [hb]))
    have ha:=h a (by simp)
    simp only [List.map_cons,weight_cons,List.length_cons]
    nlinarith
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_ExperimentSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream.Experiment
variable {α β : Type}
lemma all_bind (p : Experiment α) (q : α → Experiment β) (P : β → Prop) :
    All (p.bind q) P ↔ All p (fun a=>All (q a) P) := by
  induction p with
  | done a => rfl
  | read p ih => simp only [bind,All,ih]
  | delay n p ih => exact ih

variable {α : Type}
lemma worst_le (p : Experiment α) (f : α → ℕ) (N : ℕ) (h : All p (fun a=>f a≤N)) : p.worst f≤N := by
  induction p with
  | done a => exact h
  | read p ih => exact max_le (ih false h.1) (ih true h.2)
  | delay n p ih => exact ih h
end MatchingFPRAS.PhysicalStream.Experiment

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_OnlineUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream
open Finset

variable {A B C : Type} [Fintype A] [Fintype B]
omit [Fintype B] in
lemma qaverage_congr (f g : A → ℚ) (h : ∀ a,f a=g a) : qaverage f=qaverage g := by
  rw [show f=g from funext h]
end MatchingFPRAS.PhysicalStream

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreeCostMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

lemma weight_nat_numeric (n : ℕ) : weight n≤4*n+1 := by
  have h:=weight_nat_le n
  have hn : n.size≤n := Nat.size_le.mpr Nat.lt_two_pow_self
  omega

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeListMore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B X : Type} [Codec A] [Codec B] [Codec X]

lemma listMin_le_default (as : List ℕ) (d : ℕ) : listMin (as,d)≤d := by
  induction as generalizing d with
  | nil => rfl
  | cons a as ih => exact (ih (min d a)).trans (min_le_left _ _)

lemma listMin_le {as : List ℕ} {d a : ℕ} (ha : a∈as) : listMin (as,d)≤a := by
  induction as generalizing d with
  | nil => simp at ha
  | cons b bs ih =>
    simp only [List.mem_cons] at ha
    rcases ha with rfl|ha
    · exact (listMin_le_default bs (min d a)).trans (min_le_right _ _)
    · exact ih ha

lemma le_listMin {as : List ℕ} {d a : ℕ} (hd : a≤d) (ha : ∀ b∈as,a≤b) :
    a≤listMin (as,d) := by
  induction as generalizing d with
  | nil => exact hd
  | cons b bs ih =>
    apply ih (le_min hd (ha b (by simp)))
    intro c hc; exact ha c (by simp [hc])
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeCategorical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped

lemma bitDenominator_eq (bs : List Bool) : bitDenominator bs=2^bs.length := by
  have h : ∀ a,bs.foldl (fun a _=>2*a) a=a*2^bs.length := by
    induction bs with
    | nil => intro a; simp
    | cons _ _ ih => intro a; simp only [List.foldl_cons,ih,List.length_cons,pow_succ]; ring
  simpa [bitDenominator] using h 1

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeFractionExtra
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped Polynomial

lemma mul_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    mul (repr x,repr y)=repr (x*y) := by
  have h:=mul_val (repr x) (repr y)
  rw [val_repr hx,val_repr hy] at h
  unfold mul at h ⊢
  rw [normalize_val] at h
  rw [normalize_repr,h]
lemma div_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    div (repr x,repr y)=repr (x/y) := by
  have h:=div_val (repr x) (repr y)
  rw [val_repr hx,val_repr hy] at h
  unfold div at h ⊢
  rw [normalize_val] at h
  rw [normalize_repr,h]
end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped Polynomial Enlargement RealGeometry

variable {n m : ℕ}
lemma logicalRepr_injective : Function.Injective (logicalRepr (n:=n)) := by
  intro a b h
  apply Subtype.ext
  exact Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))
lemma vertexRepr_injective : Function.Injective (vertexRepr (n:=n) (m:=m)) := by
  intro a b h
  cases a with
  | inl a => cases b with
    | inl b => exact congrArg Sum.inl (Fin.ext (Sum.inl.inj h))
    | inr b => cases h
  | inr a => cases b with
    | inl b => cases h
    | inr b =>
      have h':(logicalRepr a.1,a.2.val)=(logicalRepr b.1,b.2.val):=Sum.inr.inj h
      exact congrArg Sum.inr (Prod.ext (logicalRepr_injective (congrArg Prod.fst h'))
        (Fin.ext (congrArg Prod.snd h')))
lemma at_repr (e : LogicalEdge (Fin n)) (i : Fin (m+2)) :
    position (m,(logicalRepr e,i.val))=vertexRepr (atVertex source target m e i) := by
  unfold position atVertex
  split_ifs <;> rfl

lemma mem_logicalEdges (vs : List ℕ) (e : RawLogical) :
    e∈logicalEdges vs ↔ e.1∈vs ∧ e.2∈vs ∧ e.1<e.2 := by
  rcases e with ⟨a,b⟩
  simp [logicalEdges,and_assoc]
lemma logicalRepr_mem (e : LogicalEdge (Fin n)) : logicalRepr e∈logicalEdges (List.range n) := by
  rw [mem_logicalEdges]
  exact ⟨List.mem_range.mpr e.val.1.isLt,List.mem_range.mpr e.val.2.isLt,e.property⟩
lemma logicalEdges_complete (e : RawLogical) (h : e∈logicalEdges (List.range n)) :
    ∃ a : LogicalEdge (Fin n),logicalRepr a=e := by
  rw [mem_logicalEdges] at h
  exact ⟨⟨(⟨e.1,List.mem_range.mp h.1⟩,⟨e.2,List.mem_range.mp h.2.1⟩),h.2.2⟩,rfl⟩
lemma vertexRepr_mem (fuel : List Bool) (v : Vertex (Fin n) (LogicalEdge (Fin n)) (4*fuel.length)) :
    vertexRepr v∈vertices (List.range n,fuel) := by
  cases v with
  | inl v => simp only [vertices,List.mem_append,List.mem_map]; exact Or.inl ⟨v.val,List.mem_range.mpr v.isLt,rfl⟩
  | inr q =>
    apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨(logicalRepr q.1,q.2.val),List.mem_product.mpr ⟨logicalRepr_mem q.1,List.mem_range.mpr q.2.isLt⟩,rfl⟩
lemma vertices_complete (fuel : List Bool) (v : RawVertex) (h : v∈vertices (List.range n,fuel)) :
    ∃ a : Vertex (Fin n) (LogicalEdge (Fin n)) (4*fuel.length),vertexRepr a=v := by
  simp only [vertices,List.mem_append,List.mem_map] at h
  rcases h with ⟨i,hi,rfl⟩|⟨⟨e,i⟩,hi,rfl⟩
  · exact ⟨.inl ⟨i,List.mem_range.mp hi⟩,rfl⟩
  · obtain ⟨he,hj⟩:=List.mem_product.mp hi
    obtain ⟨a,rfl⟩:=logicalEdges_complete e he
    exact ⟨.inr (a,⟨i,List.mem_range.mp hj⟩),rfl⟩
lemma realRepr_mem (fuel : List Bool) (e : LogicalEdge (Fin n)×Fin (4*fuel.length+1)) :
    realRepr e∈realEdges (List.range n,fuel) := by
  exact List.mem_product.mpr ⟨logicalRepr_mem e.1,List.mem_range.mpr e.2.isLt⟩
lemma realEdges_complete (fuel : List Bool) (e : RawReal) (h : e∈realEdges (List.range n,fuel)) :
    ∃ a : LogicalEdge (Fin n)×Fin (4*fuel.length+1),realRepr a=e := by
  obtain ⟨he,hi⟩:=List.mem_product.mp h
  obtain ⟨a,ha⟩:=logicalEdges_complete e.1 he
  exact ⟨(a,⟨e.2,List.mem_range.mp hi⟩),Prod.ext ha rfl⟩
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeDyadic
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction Polynomial

lemma findGreatest_lt_size (H s : ℕ) : Nat.findGreatest (fun k=>k < s) H=min H (s-1) := by
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨min_le_left _ _,?_,?_⟩
  · intro h
    have hle:=min_le_right H (s-1)
    omega
  · intro k hk hkH hks
    have hmin:=le_min hkH (show k ≤ s-1 by omega)
    omega
lemma level_val (H : ℕ) (x : Fraction) : level (H,x)=(NumberedHierarchy.level H (val x)).val := by
  have hp : (fun k=>(2:ℚ)^k≤val x)=(fun k=>k<(x.1/x.2).size) := by
    funext k
    apply propext
    rw [Nat.lt_size]
    rw [←Rat.natFloor_natCast_div_natCast]
    have h:=Nat.le_floor_iff' (R:=ℚ) (n:=2^k) (a:=val x) (by positivity)
    simpa only [val,Nat.cast_pow,Nat.cast_ofNat] using h.symm
  simp only [NumberedHierarchy.level,level,hp,findGreatest_lt_size]
lemma level_repr (H : ℕ) (q : ℚ) (hq : 0≤q) :
    level (H,TreeFraction.repr q)=(NumberedHierarchy.level H q).val := by
  rw [level_val,TreeFraction.val_repr hq]

lemma threshold_repr (xs : List Bool) (k : ℕ) (hk : k≤xs.length) :
    threshold (xs,k)=TreeFraction.repr ((2:ℚ)^k) := by
  simp only [threshold,bitDenominator_eq,List.length_take,min_eq_left hk]
  have h : val ((2^k,1):Fraction)=(2:ℚ)^k := by simp [val]
  rw [←h,←normalize_repr]
  simp [TreeFraction.normalize]
end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeBottleneck
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma maximum_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    maximum (repr x,repr y)=repr (max x y) := by
  unfold maximum
  rw [less_val _ _ x.pos y.pos,val_repr hx,val_repr hy]
  simp only [decide_eq_true_eq]
  split_ifs with h
  · rw [max_eq_right (le_of_lt h)]
  · rw [max_eq_left (le_of_not_gt h)]
lemma minimum_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    minimum (repr x,repr y)=repr (min x y) := by
  unfold minimum
  rw [less_val _ _ x.pos y.pos,val_repr hx,val_repr hy]
  simp only [decide_eq_true_eq]
  split_ifs with h
  · rw [min_eq_left (le_of_lt h)]
  · rw [min_eq_right (le_of_not_gt h)]
end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeBottleneckCorrect
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma maximum_fold_repr (xs : List ℚ) (z : ℚ) (hz : 0≤z) (hx : ∀ x∈xs,0≤x) :
    (xs.map TreeFraction.repr).foldl (fun z x=>maximum (x,z)) (TreeFraction.repr z)=
      TreeFraction.repr (xs.foldl (fun z x=>max x z) z) := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [maximum_repr (hx x (by simp)) hz]
    exact ih _ (hz.trans (le_max_right _ _)) (fun x h=>hx x (by simp [h]))
lemma le_fold_max (xs : List ℚ) (z : ℚ) : z≤xs.foldl (fun z x=>max x z) z := by
  induction xs generalizing z with
  | nil => exact le_rfl
  | cons x xs ih => exact (le_max_right x z).trans (ih _)
lemma mem_le_fold_max (xs : List ℚ) (z v : ℚ) (hv : v∈xs) : v≤xs.foldl (fun z x=>max x z) z := by
  induction xs generalizing z with
  | nil => simp at hv
  | cons x xs ih =>
    rcases List.mem_cons.mp hv with rfl|hv
    · exact (le_max_left _ _).trans (le_fold_max xs _)
    · exact ih _ hv
lemma fold_max_le (xs : List ℚ) (z B : ℚ) (hz : z≤B) (hx : ∀ x∈xs,x≤B) :
    xs.foldl (fun z x=>max x z) z≤B := by
  induction xs generalizing z with
  | nil => exact hz
  | cons x xs ih =>
    exact ih _ (max_le (hx x (by simp)) hz) (fun x h=>hx x (by simp [h]))
lemma fold_max_ofFn {n : ℕ} (w : Fin n→ℚ) (z : ℚ) (a : Fin n) :
    (List.ofFn w).foldl (fun z x=>max x z) z=max z (Finset.univ.sup' ⟨a,Finset.mem_univ a⟩ w) := by
  apply le_antisymm
  · apply fold_max_le _ _ _ (le_max_left _ _)
    intro x hx
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hx
    exact (Finset.le_sup' w (Finset.mem_univ i)).trans (le_max_right _ _)
  · apply max_le (le_fold_max _ _)
    apply Finset.sup'_le
    intro i _
    exact mem_le_fold_max _ _ _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.ExecutableBottleneck
open TreeTyped TreeFraction

lemma matrixRep_length {n : ℕ} (w : Fin n→Fin n→ℚ) : (matrixRep w).length=n := by
  simp [matrixRep]
lemma cell_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (a b : Fin n) :
    cell (matrixRep w,(a.val,b.val))=TreeFraction.repr (w a b) := by
  simp [cell,matrixRep,List.getD_eq_getElem?_getD,a.isLt,b.isLt]

lemma square_eq_ofFn {A B : Type} (n : ℕ) (x : A) (f : A×(ℕ×ℕ)→B) :
    square n x f=List.ofFn fun i : Fin n=>List.ofFn fun j : Fin n=>f (x,(i.val,j.val)) := by
  apply List.ext_getElem
  · simp [square]
  · intro i hi hi'
    simp only [square,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    apply List.ext_getElem
    · simp
    · intro j hj hj'
      simp
lemma one_repr : one=TreeFraction.repr (1:ℚ) := rfl
lemma seedEntry_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (a b : Fin n) :
    seedEntry (matrixRep w,(a.val,b.val))=TreeFraction.repr (BottleneckAlgorithm.seed w a b) := by
  unfold seedEntry BottleneckAlgorithm.seed BottleneckAlgorithm.edge
  dsimp only
  by_cases hab : a=b
  · subst b; simp only [↓reduceIte,one_repr]
  · have hv : a.val≠b.val := fun he=>hab (Fin.ext he)
    rw [ite_eq_right hv,ite_eq_right hab]
    by_cases hlt : a<b
    · rw [ite_eq_left hlt,min_eq_left (show a.val≤b.val from le_of_lt hlt),max_eq_right (show a.val≤b.val from le_of_lt hlt),cell_matrixRep,one_repr]
      exact maximum_repr (by norm_num) (hw a b)
    · rw [ite_eq_right hlt,min_eq_right (show b.val≤a.val from le_of_not_gt hlt),max_eq_left (show b.val≤a.val from le_of_not_gt hlt),cell_matrixRep,one_repr]
      exact maximum_repr (by norm_num) (hw b a)
lemma seed_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) :
    seed (matrixRep w)=matrixRep (BottleneckAlgorithm.seed w) := by
  rw [seed,matrixRep_length,square_eq_ofFn]
  unfold matrixRep
  congr 1
  funext a
  congr 1
  funext b
  exact seedEntry_matrixRep w hw a b

lemma via_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (a b c : Fin n) :
    via ((matrixRep w,(a.val,b.val)),c.val)=TreeFraction.repr (min (w a c) (w c b)) := by
  unfold via
  dsimp only
  rw [cell_matrixRep,cell_matrixRep]
  exact minimum_repr (hw a c) (hw c b)
lemma entry_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (a b : Fin n) :
    entry (matrixRep w,(a.val,b.val))=TreeFraction.repr (BottleneckAlgorithm.advance w a b) := by
  unfold entry BottleneckAlgorithm.advance
  dsimp only
  by_cases hab : a=b
  · subst b; simp only [↓reduceIte,one_repr]
  · have hv : a.val≠b.val := fun he=>hab (Fin.ext he)
    rw [ite_eq_right hv,ite_eq_right hab,cell_matrixRep,matrixRep_length]
    have he : (List.range n).map (fun c=>via ((matrixRep w,(a.val,b.val)),c))=
        (List.ofFn fun c : Fin n=>min (w a c) (w c b)).map TreeFraction.repr := by
      apply List.ext_getElem
      · simp
      · intro i hi hi'
        have hi0 : i<n := by simpa using hi
        simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
        exact via_matrixRep w hw a b ⟨i,hi0⟩
    rw [he,maximum_fold_repr _ _ (hw a b) (by
      intro x hx
      obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hx
      exact le_min (hw a i) (hw i b)),fold_max_ofFn _ _ a]
lemma advance_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) :
    advance (matrixRep w)=matrixRep (BottleneckAlgorithm.advance w) := by
  rw [advance,matrixRep_length,square_eq_ofFn]
  unfold matrixRep
  congr 1
  funext a
  congr 1
  funext b
  exact entry_matrixRep w hw a b
lemma fold_advance_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (_hw : ∀ a b,0≤w a b)
    (ls : List (List Fraction)) (k : ℕ) :
    ls.foldl (fun z _=>advance z) (matrixRep (BottleneckAlgorithm.close w k))=
      matrixRep (BottleneckAlgorithm.close w (k+ls.length)) := by
  induction ls generalizing k with
  | nil => simp
  | cons r ls ih =>
    rw [List.foldl_cons,advance_matrixRep _ (fun a b=>
      (show (0:ℚ)≤1 by norm_num).trans (BottleneckAlgorithm.close_one w k a b))]
    change ls.foldl (fun z _=>advance z) (matrixRep (BottleneckAlgorithm.close w (k+1)))=_
    rw [ih]
    congr 2
    simp only [List.length_cons]; omega

theorem close_matrixRep {n : ℕ} (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) :
    close (matrixRep w)=matrixRep (BottleneckAlgorithm.close w n) := by
  unfold close
  rw [seed_matrixRep w hw]
  change (matrixRep w).foldl (fun z _=>advance z) (matrixRep (BottleneckAlgorithm.close w 0))=_
  rw [fold_advance_matrixRep _ hw,matrixRep_length,Nat.zero_add]
end MatchingFPRAS.ExecutableBottleneck

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeHierarchyRoot
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck Polynomial

lemma related_matrixRep {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0≤B a b)
    (t : ℚ) (ht : 0≤t) (a b : Fin n) :
    related (((matrixRep B,TreeFraction.repr t),a.val),b.val)=decide (NumberedHierarchy.related B t a b) := by
  unfold related NumberedHierarchy.related
  rw [cell_matrixRep,TreeFraction.less_val _ _ (B a b).pos t.pos,
    TreeFraction.val_repr (hB a b),TreeFraction.val_repr ht]
  apply Bool.eq_iff_iff.mpr
  simp [Fin.ext_iff,not_lt]
lemma component_mem_matrixRep {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0≤B a b)
    (t : ℚ) (ht : 0≤t) (a b : Fin n) :
    b.val∈component ((matrixRep B,TreeFraction.repr t),a.val) ↔ b∈NumberedHierarchy.component B t a := by
  simp only [component,List.mem_filter,List.mem_range,matrixRep_length,
    related_matrixRep B hB t ht,decide_eq_true_eq,NumberedHierarchy.component,
    Finset.mem_filter,Finset.mem_univ,true_and]
  exact and_iff_right b.isLt
lemma root_matrixRep {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0≤B a b)
    (t : ℚ) (ht : 0≤t) (a : Fin n) :
    root ((matrixRep B,TreeFraction.repr t),a.val)=(NumberedHierarchy.root B t a).val := by
  apply le_antisymm
  · apply listMin_le
    exact (component_mem_matrixRep B hB t ht a _).mpr (NumberedHierarchy.root_mem B t a)
  · unfold root
    apply le_listMin (by rw [matrixRep_length]; exact Nat.le_of_lt (NumberedHierarchy.root B t a).isLt)
    intro v hv
    have hvlt : v<n := by
      have h:=List.mem_range.mp (List.mem_filter.mp hv).1
      simpa only [matrixRep_length] using h
    have hv' := (component_mem_matrixRep B hB t ht a ⟨v,hvlt⟩).mp hv
    exact Finset.min'_le _ _ hv'
end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeLabelTable
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck Polynomial

lemma mem_labels (x : HierarchyInput) (l : LabelKey) :
    l∈labels x ↔ l.1≤x.2.length ∧ l.2<x.1.length ∧ labelRoot (x,l)=l.2 := by
  simp only [labels,List.mem_filter,List.mem_flatMap,List.mem_map,List.mem_range,fixedRoot,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨k,hk,v,hv,he⟩,hr⟩
    cases he
    exact ⟨by omega,hv,hr⟩
  · rintro ⟨hk,hv,hr⟩
    exact ⟨⟨l.1,by omega,l.2,hv,rfl⟩,hr⟩

lemma labelRoot_matrixRep {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0≤B a b)
    (xs : List Bool) (k : Fin (xs.length+1)) (a : Fin n) :
    labelRoot ((matrixRep B,xs),(k.val,a.val))=(NumberedHierarchy.root B ((2:ℚ)^k.val) a).val := by
  unfold labelRoot
  dsimp only
  rw [threshold_repr xs k.val (by omega)]
  exact root_matrixRep B hB _ (by positivity) a

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeReweight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
lemma lookup_image {I E A : Type} [DecidableEq E] (d : A) (keys : List I)
    (f : I→E) (g : I→A) (hf : Function.Injective f) (i : I) (hi : i∈keys) :
    lookup d (keys.map (fun j=>(f j,g j)),f i)=g i := by
  induction keys with
  | nil=>simp at hi
  | cons j keys ih=>
    by_cases hji : j=i
    · subst j; simp [lookup]
    · have hne : f j≠f i:=fun h=>hji (hf h)
      have hi' : i∈keys:=(List.mem_cons.mp hi).resolve_left (Ne.symm hji)
      simpa [lookup,hne] using ih hi'
end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeClosureReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.BottleneckAlgorithm
open Finset

variable {V W α : Type} [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
    [LinearOrder α] [OfNat α 1]
omit [Fintype V] [Fintype W] in
lemma seed_reindex (e : V≃W) (he : ∀ a b,e a<e b ↔ a<b) (w : W→W→α) (a b : V) :
    seed (fun i j=>w (e i) (e j)) a b=seed w (e a) (e b) := by
  simp only [seed,edge,e.injective.eq_iff,he]
lemma advance_reindex (e : V≃W) (w : W→W→α) (a b : V) :
    advance (fun i j=>w (e i) (e j)) a b=advance w (e a) (e b) := by
  unfold advance
  simp only [e.injective.eq_iff]
  split_ifs
  · rfl
  · congr 1
    apply le_antisymm
    · apply Finset.sup'_le
      intro c _
      exact Finset.le_sup' (fun k=>min (w (e a) k) (w k (e b))) (Finset.mem_univ (e c))
    · apply Finset.sup'_le
      intro c _
      obtain ⟨d,rfl⟩:=e.surjective c
      exact Finset.le_sup' (fun k=>min (w (e a) (e k)) (w (e k) (e b))) (Finset.mem_univ d)
lemma close_reindex (e : V≃W) (he : ∀ a b,e a<e b ↔ a<b) (w : W→W→α) (k : ℕ) :
    close (fun i j=>w (e i) (e j)) k=fun i j=>close w k (e i) (e j) := by
  induction k with
  | zero=>funext a b; exact seed_reindex e he w a b
  | succ k ih=>
    simp only [close,ih]
    funext a b
    exact advance_reindex e _ a b
end MatchingFPRAS.BottleneckAlgorithm

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeNumberedCodec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.Numbered
variable {A : Type} [Fintype A] [LinearOrder A]

lemma index_orderedEnum (i : Fin (Fintype.card A)) :
    index (UnitRefresh.orderedEnum A i)=i.val := by simp [index]
end MatchingFPRAS.TreeTyped.Numbered

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeLabelCorrect
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh
lemma ofFn_orderedEnum (A : Type) [Fintype A] [LinearOrder A] :
    List.ofFn (orderedEnum A)=(Finset.univ : Finset A).sort (· ≤ ·) := by
  apply List.ext_getElem
  · simp
  · intro i _ _
    simp only [List.getElem_ofFn]
    rfl
end MatchingFPRAS.UnitRefresh

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck Finset

lemma key_injective {n H : ℕ} (B : Fin n→Fin n→ℚ) : Function.Injective (key (B:=B) (H:=H)) := by
  rintro ⟨k,a⟩ ⟨j,b⟩ he
  have he' : k=j := Fin.ext (congrArg Prod.fst he)
  cases he'
  exact congrArg (Sigma.mk k) (Subtype.ext (Fin.ext (congrArg Prod.snd he)))

lemma labels_pairwise (x : HierarchyInput) :
    (labels x).Pairwise (fun a b=>toLex a < toLex b) := by
  apply List.Pairwise.filter
  apply List.pairwise_flatMap.mpr
  constructor
  · intro k _
    apply List.pairwise_map.mpr
    exact (List.pairwise_lt_range (n:=x.1.length)).imp (fun h=>by exact Prod.Lex.right _ h)
  · apply (List.pairwise_lt_range (n:=x.2.length+1)).imp
    intro k j hkj a ha b hb
    obtain ⟨u,_,rfl⟩:=List.mem_map.mp ha
    obtain ⟨v,_,rfl⟩:=List.mem_map.mp hb
    exact Prod.Lex.left _ _ hkj

lemma mem_labels_iff_key {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (xs : List Bool) (l : LabelKey) :
    l∈labels (matrixRep B,xs) ↔ ∃ a : NumberedHierarchy.Label B xs.length,key a=l := by
  rw [mem_labels,matrixRep_length]
  dsimp only
  constructor
  · rintro ⟨hk,hv,hr⟩
    let k : Fin (xs.length+1):=⟨l.1,by omega⟩
    let v : Fin n:=⟨l.2,hv⟩
    have hr' : NumberedHierarchy.root B ((2:ℚ)^k.val) v=v := by
      apply Fin.ext
      exact (labelRoot_matrixRep B hB xs k v).symm.trans hr
    exact ⟨⟨k,⟨v,hr'⟩⟩,rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨Nat.le_of_lt_succ a.1.isLt,a.2.val.isLt,(labelRoot_matrixRep B hB xs a.1 a.2.val).trans (congrArg Fin.val a.2.property)⟩

attribute [local instance] OAI.MatchingFPRAS.ExecutableHierarchy.instLELabelFin
lemma key_le_iff {n H : ℕ} (B : Fin n→Fin n→ℚ) (a b : NumberedHierarchy.Label B H) :
    toLex (key a) ≤ toLex (key b) ↔ a ≤ b := by
  change _ ↔ toLex (a.1,a.2.val) ≤ toLex (b.1,b.2.val)
  simp only [Prod.Lex.le_iff,key,Fin.lt_def,Fin.le_def]
  exact or_congr Iff.rfl (and_congr Fin.val_inj Iff.rfl)
attribute [local instance] OAI.MatchingFPRAS.ExecutableHierarchy.instLinearOrderLabelFin
lemma labels_eq_sorted_keys {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (xs : List Bool) :
    labels (matrixRep B,xs)=((univ : Finset (NumberedHierarchy.Label B xs.length)).sort (· ≤ ·)).map key := by
  let R : LabelKey→LabelKey→Prop:=fun a b=>toLex a ≤ toLex b
  have ha : (labels (matrixRep B,xs)).Pairwise R := (labels_pairwise _).imp (fun h=>h.le)
  have hb : (((univ : Finset (NumberedHierarchy.Label B xs.length)).sort (· ≤ ·)).map key).Pairwise R := by
    apply List.pairwise_map.mpr
    exact (Finset.pairwise_sort _ _).imp (fun h=>(key_le_iff B _ _).mpr h)
  have hn : (labels (matrixRep B,xs)).Nodup :=
    (labels_pairwise _).imp (fun h he=>h.ne (congrArg toLex he))
  have hm : (((univ : Finset (NumberedHierarchy.Label B xs.length)).sort (· ≤ ·)).map key).Nodup :=
    (Finset.sort_nodup _ _).map (key_injective B)
  have hp : (labels (matrixRep B,xs)).Perm (((univ : Finset (NumberedHierarchy.Label B xs.length)).sort (· ≤ ·)).map key) := by
    apply List.perm_of_nodup_nodup_toFinset_eq hn hm
    ext l
    simp only [List.mem_toFinset,mem_labels_iff_key B hB,List.mem_map,Finset.mem_sort,Finset.mem_univ,true_and]
  exact hp.eq_of_pairwise (fun a b _ _ hab hba=>toLex.injective (le_antisymm hab hba)) ha hb
lemma labels_eq_ofFn {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (xs : List Bool) :
    labels (matrixRep B,xs)=List.ofFn (fun i=>key (UnitRefresh.orderedEnum (NumberedHierarchy.Label B xs.length) i)) := by
  change _=List.ofFn (key ∘ UnitRefresh.orderedEnum (NumberedHierarchy.Label B xs.length))
  rw [←List.map_ofFn,UnitRefresh.ofFn_orderedEnum,labels_eq_sorted_keys B hB]
end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Enlargement RealGeometry

attribute [local instance] Transport.prodOrder Transport.sumOrder

attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instLTProdOfLinearOrder_solutions
lemma pairwise_product {A B : Type} [LinearOrder A] [LinearOrder B]
    {as : List A} {bs : List B} (ha : as.Pairwise (· < ·)) (hb : bs.Pairwise (· < ·)) :
    (as.product bs).Pairwise (· < ·) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro a _
    apply List.pairwise_map.mpr
    exact hb.imp (fun h=>Prod.Lex.right _ h)
  · apply ha.imp
    intro a b hab x hx y hy
    obtain ⟨u,hu,rfl⟩:=List.mem_map.mp hx
    obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hy
    exact Prod.Lex.left _ _ hab

lemma logicalEdges_pairwise (n : ℕ) :
    (logicalEdges (List.range n)).Pairwise (· < ·) :=
  List.Pairwise.filter _ (pairwise_product (List.pairwise_lt_range) (List.pairwise_lt_range))
attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instLTSumOfLinearOrder_solutions
lemma vertices_pairwise (n : ℕ) (fuel : List Bool) :
    (vertices (List.range n,fuel)).Pairwise (· < ·) := by
  unfold vertices
  apply List.pairwise_append.mpr
  refine ⟨?_,?_,?_⟩
  · apply List.pairwise_map.mpr
    exact (List.pairwise_lt_range (n:=n)).imp (fun h=>Sum.Lex.inl h)
  · apply List.pairwise_map.mpr
    exact (pairwise_product (logicalEdges_pairwise n) List.pairwise_lt_range).imp
      (fun h=>Sum.Lex.inr h)
  · intro a ha b hb
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp ha
    obtain ⟨e,he,rfl⟩:=List.mem_map.mp hb
    exact Sum.Lex.sep _ _

attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instLEProdOfLinearOrder_solutions
lemma logicalRepr_le {n : ℕ} (a b : LogicalEdge (Fin n)) :
    logicalRepr a ≤ logicalRepr b ↔ a ≤ b := by
  change toLex (logicalRepr a) ≤ toLex (logicalRepr b) ↔ toLex a.val ≤ toLex b.val
  simp only [Prod.Lex.le_iff,logicalRepr,ofLex_toLex,Fin.lt_def,Fin.le_def,Fin.val_inj]
attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instLESumOfLinearOrder_solutions
lemma vertexRepr_le {n m : ℕ} (a b : Vertex (Fin n) (LogicalEdge (Fin n)) m) :
    vertexRepr a ≤ vertexRepr b ↔ a ≤ b := by
  cases a with
  | inl a => cases b with
    | inl b =>
      change toLex (Sum.inl a.val : ℕ⊕RawReal) ≤ toLex (Sum.inl b.val : ℕ⊕RawReal) ↔
        toLex (Sum.inl a : Fin n⊕LogicalEdge (Fin n)×Fin m) ≤ toLex (Sum.inl b : Fin n⊕LogicalEdge (Fin n)×Fin m)
      simp only [Sum.Lex.inl_le_inl_iff,Fin.le_def]
    | inr b =>
      change toLex (Sum.inl a.val : ℕ⊕RawReal) ≤ toLex (Sum.inr (logicalRepr b.1,b.2.val) : ℕ⊕RawReal) ↔
        toLex (Sum.inl a : Fin n⊕LogicalEdge (Fin n)×Fin m) ≤ toLex (Sum.inr b : Fin n⊕LogicalEdge (Fin n)×Fin m)
      simp
  | inr a => cases b with
    | inl b =>
      change toLex (Sum.inr (logicalRepr a.1,a.2.val) : ℕ⊕RawReal) ≤ toLex (Sum.inl b.val : ℕ⊕RawReal) ↔
        toLex (Sum.inr a : Fin n⊕LogicalEdge (Fin n)×Fin m) ≤ toLex (Sum.inl b : Fin n⊕LogicalEdge (Fin n)×Fin m)
      simp
    | inr b =>
      change toLex (Sum.inr (logicalRepr a.1,a.2.val) : ℕ⊕RawReal) ≤ toLex (Sum.inr (logicalRepr b.1,b.2.val) : ℕ⊕RawReal) ↔
        toLex (Sum.inr a : Fin n⊕LogicalEdge (Fin n)×Fin m) ≤ toLex (Sum.inr b : Fin n⊕LogicalEdge (Fin n)×Fin m)
      simp only [Sum.Lex.inr_le_inr_iff]
      change toLex (logicalRepr a.1,a.2.val) ≤ toLex (logicalRepr b.1,b.2.val) ↔ toLex a ≤ toLex b
      simp only [Prod.Lex.le_iff,ofLex_toLex,Fin.le_def,logicalRepr_injective.eq_iff]
      have hlt : logicalRepr a.1 < logicalRepr b.1 ↔ a.1 < b.1 := by
        rw [lt_iff_not_ge,lt_iff_not_ge,logicalRepr_le]
      rw [hlt]

attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instPreorderSumOfLinearOrder_solutions
lemma vertices_eq_ofFn (n : ℕ) (fuel : List Bool) :
    vertices (List.range n,fuel)=List.ofFn (fun i=>vertexRepr
      (UnitRefresh.orderedEnum (Vertex (Fin n) (LogicalEdge (Fin n)) (4*fuel.length)) i)) := by
  classical
  let V:=Vertex (Fin n) (LogicalEdge (Fin n)) (4*fuel.length)
  rw [show (fun i=>vertexRepr (UnitRefresh.orderedEnum V i))=vertexRepr ∘ UnitRefresh.orderedEnum V from rfl,
    ←List.map_ofFn,UnitRefresh.ofFn_orderedEnum]
  have ha : (vertices (List.range n,fuel)).Pairwise (· ≤ ·) :=
    (vertices_pairwise n fuel).imp (fun h=>le_of_lt h)
  have hb : (((Finset.univ : Finset V).sort (· ≤ ·)).map vertexRepr).Pairwise (· ≤ ·) := by
    apply List.pairwise_map.mpr
    exact (Finset.pairwise_sort _ _).imp (fun h=>(vertexRepr_le _ _).mpr h)
  have hn : (vertices (List.range n,fuel)).Nodup := (vertices_pairwise n fuel).imp (fun h=>h.ne)
  have hm := (Finset.sort_nodup (Finset.univ : Finset V) (· ≤ ·)).map vertexRepr_injective
  have hp : (vertices (List.range n,fuel)).Perm (((Finset.univ : Finset V).sort (· ≤ ·)).map vertexRepr) := by
    apply List.perm_of_nodup_nodup_toFinset_eq hn hm
    ext v
    simp only [List.mem_toFinset,List.mem_map,Finset.mem_sort,Finset.mem_univ,true_and]
    constructor
    · exact vertices_complete fuel v
    · rintro ⟨a,rfl⟩; exact vertexRepr_mem fuel a
  apply hp.eq_of_pairwise (fun _ _ _ _ h₁ h₂=>@le_antisymm _ Transport.sumOrder.toPartialOrder _ _ h₁ h₂) ha hb
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeDPCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped

lemma map_range_ofFn {A : Type} (f : ℕ → A) (n : ℕ) :
    (List.range n).map f=List.ofFn (fun i : Fin n=>f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'; simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]

end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeSamplerRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP
lemma rows_getD {a b : Bags} (h : List.Forall₂ List.Perm a b) (i : ℕ) :
    (a.getD i []).Perm (b.getD i []) := by
  induction h generalizing i with
  | nil=>exact List.Perm.refl []
  | @cons a b as bs hab _hs ih=>
    cases i with
    | zero=>exact hab
    | succ i=>exact ih i
end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRefreshIndexed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped TreeTyped.Numbered ExecutableDP ExecutableUnit Polynomial

section Source
open Transport UnitRefresh

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
variable {n m : ℕ} {bags : Fin n→Finset (Fin m)}
lemma key_injective : Function.Injective (key (bags:=bags)) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Sym2.sortEquiv.injective
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.ext (congrArg (fun z=>z.1.1) h)
    · exact Fin.ext (congrArg (fun z=>z.1.2) h)
  · exact Fin.ext (congrArg Prod.snd h)
end Source

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
end MatchingFPRAS.ExecutableRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRefreshCatalog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped ExecutableDP ExecutableSource Polynomial

open Transport UnitRefresh

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype Transport.prodOrder
variable {n m : ℕ} {bags : Fin n→Finset (Fin m)} {a : Bags}
local instance (priority := 2000) instLEProdOfLinearOrder_solutions_r4c82d9_1 {A B : Type} [LinearOrder A] [LinearOrder B] : LE (A×B) := Transport.prodOrder.toLE
attribute [local instance] OAI.MatchingFPRAS.ExecutableRefresh.instLTProdOfLinearOrder_solutions
attribute [local instance] OAI.MatchingFPRAS.ExecutableRefresh.instPreorderProdOfLinearOrder_solutions
attribute [local instance] OAI.MatchingFPRAS.ExecutableRefresh.instLTSym2OfLinearOrder_solutions
lemma key_le (e f : BagEdge bags) : @LE.le Key Transport.prodOrder.toLE (key e) (key f) ↔ @LE.le _ Transport.bagEdgeOrder.toLE e f := by
  change toLex (key e) ≤ toLex (key f) ↔ toLex e.val.val ≤ toLex f.val.val
  simp only [Prod.Lex.le_iff,key,ofLex_toLex,Fin.le_def]
  have hlt : (e.val.val.1.inf.val,e.val.val.1.sup.val)<(f.val.val.1.inf.val,f.val.val.1.sup.val) ↔ e.val.val.1<f.val.val.1 := by
    change toLex (e.val.val.1.inf.val,e.val.val.1.sup.val)<toLex (f.val.val.1.inf.val,f.val.val.1.sup.val) ↔
      toLex (Sym2.sortEquiv e.val.val.1).val<toLex (Sym2.sortEquiv f.val.val.1).val
    simp only [Prod.Lex.lt_iff,ofLex_toLex,Fin.lt_def,Fin.val_inj,Sym2.sortEquiv]
    rfl
  have heq : (e.val.val.1.inf.val,e.val.val.1.sup.val)=(f.val.val.1.inf.val,f.val.val.1.sup.val) ↔ e.val.val.1=f.val.val.1 := by
    constructor
    · intro h
      apply Sym2.sortEquiv.injective
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h
    · intro h; rw [h]
  rw [hlt,heq]
lemma row_mem (ha : List.Forall₂ List.Perm a (orderedRep bags)) (i : Fin n) (j : ℕ) :
    j∈a.getD i.val [] ↔ ∃ c∈bags i,c.val=j := by
  rw [(rows_getD ha i.val).mem_iff]
  simp only [orderedRep,List.getD,List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.getD_some,bagRep,List.mem_map,Finset.mem_toList]
lemma storedCatalog_mem (ha : List.Forall₂ List.Perm a (orderedRep bags)) (e : Key) :
    e∈storedCatalog (a,List.range m) ↔ ∃ b : BagEdge bags,key b=e := by
  have hn : a.length=n := by simpa only [orderedRep,List.length_ofFn] using ha.length_eq
  constructor
  · intro he
    obtain ⟨he,hs⟩:=List.mem_filter.mp he
    obtain ⟨he,hc⟩:=List.mem_product.mp he
    obtain ⟨he,huv⟩:=List.mem_filter.mp he
    obtain ⟨hu,hv⟩:=List.mem_product.mp he
    have hu : e.1.1<n := by simpa only [List.mem_range,hn] using hu
    have hv : e.1.2<n := by simpa only [List.mem_range,hn] using hv
    have hc : e.2 < m := List.mem_range.mp hc
    have huv : e.1.1<e.1.2 := of_decide_eq_true huv
    have hs : e.2∈a.getD e.1.1 [] ∧ e.2∈a.getD e.1.2 [] := of_decide_eq_true hs
    have hcu': (⟨e.2,hc⟩ : Fin m)∈bags ⟨e.1.1,hu⟩ := by
      obtain ⟨l,hl,he⟩:=(row_mem ha ⟨e.1.1,hu⟩ e.2).mp hs.1
      have he' : l=(⟨e.2,hc⟩ : Fin m) := Fin.ext he
      simpa only [he'] using hl
    have hcv': (⟨e.2,hc⟩ : Fin m)∈bags ⟨e.1.2,hv⟩ := by
      obtain ⟨l,hl,he⟩:=(row_mem ha ⟨e.1.2,hv⟩ e.2).mp hs.2
      have he' : l=(⟨e.2,hc⟩ : Fin m) := Fin.ext he
      simpa only [he'] using hl
    have huv' : (⟨e.1.1,hu⟩ : Fin n)<⟨e.1.2,hv⟩ := huv
    let b : BagEdge bags:=⟨⟨(s((⟨e.1.1,hu⟩ : Fin n),⟨e.1.2,hv⟩),(⟨e.2,hc⟩ : Fin m)),by
      simp only [Sym2.mk_isDiag_iff]; exact ne_of_lt huv'⟩,by
      intro i hi
      rcases Sym2.mem_iff.mp hi with rfl|rfl
      · exact hcu'
      · exact hcv'⟩
    refine ⟨b,?_⟩
    simp only [key,b,Sym2.inf_mk,Sym2.sup_mk,inf_eq_left.mpr huv'.le,sup_eq_right.mpr huv'.le]
  · rintro ⟨b,rfl⟩
    have hlt : b.val.val.1.inf<b.val.val.1.sup := lt_of_le_of_ne b.val.val.1.inf_le_sup (by
      intro h
      apply b.val.property
      rw [←sym_mk_inf_sup b.val.val.1,h]
      exact Sym2.mk_isDiag_iff.mpr rfl)
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_product.mpr
      constructor
      · apply List.mem_filter.mpr
        constructor
        · exact List.mem_product.mpr ⟨List.mem_range.mpr (by simpa only [hn] using b.val.val.1.inf.isLt),
            List.mem_range.mpr (by simpa only [hn] using b.val.val.1.sup.isLt)⟩
        · exact decide_eq_true hlt
      · exact List.mem_range.mpr b.val.val.2.isLt
    · apply decide_eq_true
      constructor
      · exact (row_mem ha _ _).mpr ⟨b.val.val.2,b.property _ (sym_inf_mem _),rfl⟩
      · exact (row_mem ha _ _).mpr ⟨b.val.val.2,b.property _ (sym_sup_mem _),rfl⟩
lemma storedCatalog_eq (ha : List.Forall₂ List.Perm a (orderedRep bags)) :
    storedCatalog (a,List.range m)=catalog bags := by
  have hpair : (storedCatalog (a,List.range m)).Pairwise (· < ·) := by
    apply List.Pairwise.filter
    exact pairwise_product (logicalEdges_pairwise a.length) List.pairwise_lt_range
  have hn := hpair.imp (fun h=>h.ne)
  have hc : (catalog bags).Nodup := List.nodup_ofFn.mpr
    ((key_injective (bags:=bags)).comp (orderedEnum (BagEdge bags)).injective)
  have hp : (storedCatalog (a,List.range m)).Perm (catalog bags) := by
    apply (List.perm_ext_iff_of_nodup hn hc).mpr
    intro e
    rw [storedCatalog_mem ha]
    simp only [catalog,List.mem_ofFn]
    constructor
    · rintro ⟨b,rfl⟩; exact ⟨(orderedEnum _).symm b,by simp⟩
    · rintro ⟨i,rfl⟩; exact ⟨(orderedEnum _ i),rfl⟩
  apply hp.eq_of_pairwise (fun _ _ _ _ h₁ h₂=>@le_antisymm _ Transport.prodOrder.toPartialOrder _ _ h₁ h₂)
    (hpair.imp (fun h=>le_of_lt h))
  rw [catalog,show (fun i=>key (orderedEnum (BagEdge bags) i))=key ∘ orderedEnum (BagEdge bags) from rfl,
    ←List.map_ofFn,ofFn_orderedEnum]
  apply List.pairwise_map.mpr
  exact (Finset.pairwise_sort _ _).imp (fun h=>(key_le _ _).mpr h)
end MatchingFPRAS.ExecutableRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRefreshNumbered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped TreeTyped.Numbered ExecutableDP ExecutableUnit Transport UnitRefresh

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype Transport.prodOrder
variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L}
lemma sourceKey_injective : Function.Injective (sourceKey (bags:=bags)) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Sym2.sortEquiv.injective
    apply Subtype.ext
    apply Prod.ext
    · exact Numbered.index_injective (congrArg (fun z=>z.1.1) h)
    · exact Numbered.index_injective (congrArg (fun z=>z.1.2) h)
  · exact Numbered.index_injective (congrArg Prod.snd h)
lemma index_lt (a b : V) : Numbered.index a < Numbered.index b ↔ a<b := by
  rw [lt_iff_not_ge,lt_iff_not_ge,Numbered.index_le]
attribute [local instance] OAI.MatchingFPRAS.ExecutableRefresh.instLEProdOfLinearOrder_solutions_1
attribute [local instance] OAI.MatchingFPRAS.ExecutableRefresh.instLTProdOfLinearOrder_solutions_1
local instance (priority := 2000) instPreorderProdOfLinearOrder_solutions_1_r4c82d9_1 {A B : Type} [LinearOrder A] [LinearOrder B] : Preorder (A×B) := Transport.prodOrder.toPreorder
attribute [local instance] OAI.MatchingFPRAS.ExecutableRefresh.instLTSym2OfLinearOrder_solutions_1
lemma sourceKey_le (e f : BagEdge bags) :
    @LE.le Key Transport.prodOrder.toLE (sourceKey e) (sourceKey f) ↔
      @LE.le _ Transport.bagEdgeOrder.toLE e f := by
  change toLex (sourceKey e)≤toLex (sourceKey f) ↔ toLex e.val.val≤toLex f.val.val
  simp only [Prod.Lex.le_iff,sourceKey,ofLex_toLex,Numbered.index_le]
  have hlt : (Numbered.index e.val.val.1.inf,Numbered.index e.val.val.1.sup)<
      (Numbered.index f.val.val.1.inf,Numbered.index f.val.val.1.sup) ↔ e.val.val.1<f.val.val.1 := by
    change toLex (Numbered.index e.val.val.1.inf,Numbered.index e.val.val.1.sup)<
      toLex (Numbered.index f.val.val.1.inf,Numbered.index f.val.val.1.sup) ↔
      toLex (Sym2.sortEquiv e.val.val.1).val<toLex (Sym2.sortEquiv f.val.val.1).val
    simp only [Prod.Lex.lt_iff,ofLex_toLex,index_lt,Numbered.index_injective.eq_iff]
    rfl
  have heq : (Numbered.index e.val.val.1.inf,Numbered.index e.val.val.1.sup)=
      (Numbered.index f.val.val.1.inf,Numbered.index f.val.val.1.sup) ↔ e.val.val.1=f.val.val.1 := by
    constructor
    · intro h
      apply Sym2.sortEquiv.injective
      apply Subtype.ext
      exact Prod.ext (Numbered.index_injective (congrArg Prod.fst h))
        (Numbered.index_injective (congrArg Prod.snd h))
    · intro h; rw [h]
  rw [hlt,heq]
lemma sourceCatalog_pairwise : (sourceCatalog bags).Pairwise (· ≤ ·) := by
  rw [sourceCatalog,show (fun i=>sourceKey (orderedEnum (BagEdge bags) i))=
    sourceKey ∘ orderedEnum (BagEdge bags) from rfl,←List.map_ofFn,ofFn_orderedEnum]
  apply List.pairwise_map.mpr
  exact (Finset.pairwise_sort _ _).imp (fun h=>(sourceKey_le _ _).mpr h)
lemma key_downEdge (e : BagEdge bags) : key (downEdge e)=sourceKey e := by
  have h : (orderedEnum V).symm e.val.val.1.inf≤(orderedEnum V).symm e.val.val.1.sup := by
    change Numbered.index e.val.val.1.inf≤Numbered.index e.val.val.1.sup
    exact (Numbered.index_le _ _).mpr e.val.val.1.inf_le_sup
  simp only [key,downEdge,Sym2.inf_mk,Sym2.sup_mk,inf_eq_left.mpr h,sup_eq_right.mpr h,sourceKey,Numbered.index]

lemma sourceKey_upEdge (e : BagEdge (numberedBags bags)) : sourceKey (upEdge e)=key e := by
  have h : orderedEnum V e.val.val.1.inf≤orderedEnum V e.val.val.1.sup := by
    exact ((Numbered.index_le _ _).mp (by simpa only [Numbered.index_orderedEnum,Fin.le_def] using e.val.val.1.inf_le_sup))
  simp only [sourceKey,upEdge,Sym2.inf_mk,Sym2.sup_mk,inf_eq_left.mpr h,sup_eq_right.mpr h,Numbered.index_orderedEnum,key]

lemma sourceCatalog_eq : sourceCatalog bags=catalog (numberedBags bags) := by
  have ha : (sourceCatalog bags).Nodup := List.nodup_ofFn.mpr
    ((sourceKey_injective (bags:=bags)).comp (orderedEnum (BagEdge bags)).injective)
  have hb : (catalog (numberedBags bags)).Nodup := List.nodup_ofFn.mpr
    ((key_injective (bags:=numberedBags bags)).comp (orderedEnum (BagEdge (numberedBags bags))).injective)
  have hp : (sourceCatalog bags).Perm (catalog (numberedBags bags)) := by
    apply (List.perm_ext_iff_of_nodup ha hb).mpr
    intro k
    simp only [sourceCatalog,catalog,List.mem_ofFn]
    constructor
    · rintro ⟨i,rfl⟩
      refine ⟨(orderedEnum _).symm (downEdge (orderedEnum _ i)),?_⟩
      rw [Equiv.apply_symm_apply,key_downEdge]
    · rintro ⟨i,rfl⟩
      refine ⟨(orderedEnum _).symm (upEdge (orderedEnum _ i)),?_⟩
      rw [Equiv.apply_symm_apply,sourceKey_upEdge]
  apply hp.eq_of_pairwise (fun _ _ _ _ h₁ h₂=>@le_antisymm _ Transport.prodOrder.toPartialOrder _ _ h₁ h₂) sourceCatalog_pairwise
  rw [catalog,show (fun i=>key (orderedEnum (BagEdge (numberedBags bags)) i))=
    key ∘ orderedEnum (BagEdge (numberedBags bags)) from rfl,←List.map_ofFn,ofFn_orderedEnum]
  apply List.pairwise_map.mpr
  exact (Finset.pairwise_sort _ _).imp (fun h=>(key_le _ _).mpr h)
end MatchingFPRAS.ExecutableRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRationalWeight
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
lemma fold_product_repr (xs : List ℚ) (hx : ∀ x∈xs,0≤x) (a : ℚ) (ha : 0≤a) :
    ((xs.map repr).foldl (fun a b=>mul (b,a)) (repr a))=repr (xs.prod*a) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    have h : 0≤x:=hx x (by simp)
    simp only [List.map_cons,List.foldl_cons,mul_repr h ha]
    rw [ih (fun y hy=>hx y (by simp [hy])) (x*a) (mul_nonneg h ha)]
    congr 1
    simp only [List.prod_cons]
    ring
lemma product_repr (xs : List ℚ) (hx : ∀ x∈xs,0≤x) : product (xs.map repr)=repr xs.prod := by
  unfold product
  have h:=fold_product_repr xs hx 1 (by decide)
  simpa only [mul_one,show repr (1:ℚ)=(1,1) from rfl] using h
end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeSlotWeight
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma add_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    add (repr x,repr y)=repr (x+y) := by
  have h:=add_val (repr x) (repr y) x.pos.ne' y.pos.ne'
  rw [val_repr hx,val_repr hy] at h
  unfold add at h ⊢
  rw [normalize_val] at h
  rw [normalize_repr,h]
lemma repr_nat (n : ℕ) : repr (n:ℚ)=(n,1) := by simp [repr]

lemma fuelPower_repr (q : ℚ) (hq : 0≤q) (fuel : List Bool) :
    fuelPower (repr q,fuel)=repr (q^fuel.length) := by
  unfold fuelPower
  have he : fuel.map (fun _=>repr q)=(fuel.map (fun _=>q)).map repr := by simp
  rw [he,product_repr _ (by intro t ht; obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ht; exact hq)]
  congr 1
  simp
end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeParentTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck

attribute [local instance] OAI.MatchingFPRAS.ExecutableHierarchy.instLinearOrderLabelFin_1
lemma index_key {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (xs : List Bool) (a : NumberedHierarchy.Label B xs.length) :
    (labels (matrixRep B,xs)).idxOf (key a)=((UnitRefresh.orderedEnum (NumberedHierarchy.Label B xs.length)).symm a).val := by
  rw [labels_eq_ofFn B hB]
  let e := UnitRefresh.orderedEnum (NumberedHierarchy.Label B xs.length)
  let i := e.symm a
  have hn := List.nodup_ofFn.mpr ((key_injective B).comp e.injective)
  have hi : i.val < (List.ofFn (fun j=>key (e j))).length := by simpa only [List.length_ofFn] using i.isLt
  have he := @List.Nodup.idxOf_getElem LabelKey (inferInstance : BEq LabelKey) inferInstance _ hn i.val hi
  simp only [List.getElem_ofFn,Fin.eta,i,Function.comp_apply,Equiv.apply_symm_apply] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma parentKey_eq {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (xs : List Bool) (a : NumberedHierarchy.Label B xs.length) (ha : 0<a.1.val) :
    parentKey ((matrixRep B,xs),key a)=key (NumberedHierarchy.labelAt B hsym htri (H:=xs.length) ⟨a.1.val-1,by omega⟩ a.2.val) := by
  apply Prod.ext
  · rfl
  exact labelRoot_matrixRep B hB xs ⟨a.1.val-1,by omega⟩ a.2.val

lemma parentEntry_eq {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (xs : List Bool) (a : NumberedHierarchy.Label B xs.length) :
    parentEntry (((matrixRep B,xs),labels (matrixRep B,xs)),key a)=
      ExecutableDP.parentTag ((NumberedHierarchy.parent B hsym htri a).map
        (UnitRefresh.orderedEnum (NumberedHierarchy.Label B xs.length)).symm) := by
  by_cases ha : 0<a.1.val
  · simp only [parentEntry,key,show ¬a.1.val=0 by omega,↓reduceIte,NumberedHierarchy.parent,ha,↓reduceDIte,Option.map_some,ExecutableDP.parentTag]
    rw [parentKey_eq B hB hsym htri xs a ha,index_key B hB]
  · have hz : a.1.val=0 := by omega
    simp [parentEntry,hz,NumberedHierarchy.parent,ExecutableDP.parentTag]

lemma parents_eq {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (xs : List Bool) :
    parents (matrixRep B,xs)=ExecutableDP.parentRep (UnitRefresh.numberedParent (NumberedHierarchy.parent B hsym htri (H:=xs.length))) := by
  unfold parents
  rw [labels_eq_ofFn B hB,List.map_ofFn]
  unfold ExecutableDP.parentRep
  congr 1
  funext i
  simpa only [Function.comp_apply,←labels_eq_ofFn B hB,UnitRefresh.numberedParent] using parentEntry_eq B hB hsym htri xs (UnitRefresh.orderedEnum _ i)
end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeBagTable
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck Polynomial

lemma edgeKey_eq {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (xs : List Bool) {E : Type} [Fintype E] (left right : E→Fin n) (e : E) :
    edgeKey ((matrixRep B,xs),((left e).val,(right e).val))=
      key (NumberedHierarchy.edgeLabel B hsym htri left right xs.length e) := by
  unfold edgeKey
  rw [cell_matrixRep,level_repr _ _ (hB _ _)]
  apply Prod.ext
  · rfl
  exact labelRoot_matrixRep B hB xs (NumberedHierarchy.level xs.length (B (left e) (right e))) (left e)
attribute [local instance] OAI.MatchingFPRAS.ExecutableHierarchy.instLinearOrderLabelFin_2
lemma edgeIndex_eq {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (xs : List Bool) {E : Type} [Fintype E] (left right : E→Fin n) (e : E) :
    edgeIndex (((matrixRep B,xs),labels (matrixRep B,xs)),((left e).val,(right e).val))=
      ((UnitRefresh.orderedEnum (NumberedHierarchy.Label B xs.length)).symm
        (NumberedHierarchy.edgeLabel B hsym htri left right xs.length e)).val := by
  unfold edgeIndex
  rw [edgeKey_eq B hB hsym htri xs left right e]
  exact index_key B hB xs (NumberedHierarchy.edgeLabel B hsym htri left right xs.length e)

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeBagCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck

variable {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (xs : List Bool) {E : Type} [Fintype E] [DecidableEq E] (left right : E→Fin n)
    (es : List (ℕ×ℕ))
    (hes : ∀ p,p∈es ↔ ∃ e,((left e).val,(right e).val)=p)

include hB hes
attribute [local instance] OAI.MatchingFPRAS.ExecutableHierarchy.instLinearOrderLabelFin_3
omit [DecidableEq E] in
lemma bag_members [DecidableEq E] (v : Fin n) (i : ℕ) :
    i∈bag (((matrixRep B,xs),es),v.val) ↔ ∃ e,(v=left e ∨ v=right e) ∧
      ((UnitRefresh.orderedEnum (NumberedHierarchy.Label B xs.length)).symm
        (NumberedHierarchy.edgeLabel B hsym htri left right xs.length e)).val=i := by
  simp only [bag,List.mem_dedup,List.mem_map,List.mem_filter]
  constructor
  · rintro ⟨p,⟨hp,hv⟩,hi⟩
    obtain ⟨e,rfl⟩ := (hes p).mp hp
    refine ⟨e,?_,?_⟩
    · simpa only [incident,decide_eq_true_eq,Fin.val_inj] using hv
    · rw [edgeIndex_eq B hB hsym htri xs left right e] at hi
      exact hi
  · rintro ⟨e,hv,hi⟩
    refine ⟨((left e).val,(right e).val),⟨(hes _).mpr ⟨e,rfl⟩,?_⟩,?_⟩
    · simpa only [incident,decide_eq_true_eq,Fin.val_inj] using hv
    · rw [edgeIndex_eq B hB hsym htri xs left right e]
      exact hi

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeHierarchyReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.Numbered
variable {A B : Type} [Fintype A] [Fintype B] [LinearOrder A] [LinearOrder B]
lemma index_orderIso (e : A≃o B) (a : A) : index (e a)=index a := by
  let h := Fintype.card_congr e.toEquiv
  have he : (orderedIso A).trans e=(Fin.castOrderIso h).trans (orderedIso B) := Subsingleton.elim _ _
  have hh:=congrArg (fun f : Fin (Fintype.card A)≃o B=>
    ((UnitRefresh.orderedEnum B).symm (f ((UnitRefresh.orderedEnum A).symm a))).val) he
  change ((UnitRefresh.orderedEnum B).symm
    (e (UnitRefresh.orderedEnum A ((UnitRefresh.orderedEnum A).symm a)))).val=
      ((UnitRefresh.orderedEnum B).symm
        (UnitRefresh.orderedEnum B (Fin.cast h ((UnitRefresh.orderedEnum A).symm a)))).val at hh
  simpa only [Equiv.apply_symm_apply,Equiv.symm_apply_apply,Fin.val_cast,index] using hh
end MatchingFPRAS.TreeTyped.Numbered

namespace MatchingFPRAS.NumberedHierarchy
open Finset

variable {V W : Type} [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
variable (B : W→W→ℚ) (e : V≃o W)

attribute [local instance] labelOrder

lemma labelReindex_index (H : ℕ) (l : Label (reindex B e) H) :
    TreeTyped.Numbered.index (labelReindex B e H l)=TreeTyped.Numbered.index l :=
  TreeTyped.Numbered.index_orderIso (labelOrderReindex B e H) l

open Finset

variable {V W : Type} [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
variable (B : W→W→ℚ) (e : V≃o W)
variable (hsym : ∀ a b,B a b=B b a)
variable (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
lemma labelAt_reindex {H : ℕ} (k : Fin (H+1)) (x : V) :
    labelReindex B e H (labelAt (reindex B e) (reindex_symm B e hsym)
      (reindex_tri B e htri) k x)=labelAt B hsym htri k (e x) := by
  apply congrArg (Sigma.mk k)
  apply Subtype.ext
  exact root_reindex B e _ x
lemma edgeLabel_reindex {E : Type} [Fintype E] [DecidableEq E]
    (left right : E→W) (H : ℕ) (a : E) :
    labelReindex B e H (edgeLabel (reindex B e) (reindex_symm B e hsym)
      (reindex_tri B e htri) (e.symm ∘ left) (e.symm ∘ right) H a)=
      edgeLabel B hsym htri left right H a := by
  unfold edgeLabel
  simp only [reindex,Function.comp_apply,OrderIso.apply_symm_apply]
  rw [labelAt_reindex,OrderIso.apply_symm_apply]
end MatchingFPRAS.NumberedHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeBags
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck NumberedHierarchy

variable {V : Type} [Fintype V] [LinearOrder V]
variable (B : V→V→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
attribute [local instance] NumberedHierarchy.labelOrder
variable (xs : List Bool) {E : Type} [Fintype E] [DecidableEq E] (left right : E→V)
    (es : List (ℕ×ℕ))
    (hes : ∀ p,p∈es ↔ ∃ e,(index (left e),index (right e))=p)

include hB hes in
lemma arbitrary_bag_members (v : V) (i : ℕ) :
    i∈bag (((matrixRep (reindex B (orderedIso V)),xs),es),index v) ↔
      ∃ e,(v=left e ∨ v=right e) ∧ index (edgeLabel B hsym htri left right xs.length e)=i := by
  let f:=orderedIso V
  have hh:=bag_members (reindex B f) (fun a b=>hB (f a) (f b))
    (reindex_symm B f hsym) (reindex_tri B f htri) xs (f.symm ∘ left) (f.symm ∘ right)
    es hes (f.symm v) i
  change i∈bag (((matrixRep (reindex B f),xs),es),index v) ↔ _ at hh
  rw [hh]
  apply exists_congr
  intro a
  have he:=labelReindex_index B f xs.length (edgeLabel (reindex B f)
    (reindex_symm B f hsym) (reindex_tri B f htri)
    (f.symm ∘ left) (f.symm ∘ right) xs.length a)
  rw [edgeLabel_reindex B f hsym htri] at he
  change (f.symm v=f.symm (left a) ∨ f.symm v=f.symm (right a)) ∧ _ ↔ _
  simp only [f.symm.injective.eq_iff]
  simpa only [index] using iff_of_eq (congrArg (fun j=>(v=left a ∨ v=right a) ∧ j=i) he.symm)

include hB hes in
lemma arbitrary_bag_perm (v : V) :
    (bag (((matrixRep (reindex B (orderedIso V)),xs),es),index v)).Perm
      (ExecutableDP.bagRep (arbitraryNumberedBags B hsym htri xs left right v)) := by
  apply (List.perm_ext_iff_of_nodup (List.nodup_dedup _) ((Finset.nodup_toList _).map Fin.val_injective)).mpr
  intro i
  change i∈bag (((matrixRep (reindex B (orderedIso V)),xs),es),index v) ↔ _
  rw [arbitrary_bag_members B hB hsym htri xs left right es hes]
  simp only [List.mem_map,Finset.mem_toList,arbitraryNumberedBags,
    Finset.mem_map,Equiv.toEmbedding_apply,NumberedHierarchy.mem_bags]
  constructor
  · rintro ⟨e,he,hi⟩
    exact ⟨_,⟨_,⟨e,he,rfl⟩,rfl⟩,hi⟩
  · rintro ⟨a,⟨l,⟨e,he,hel⟩,hla⟩,hai⟩
    subst l
    subst a
    exact ⟨e,he,hai⟩

include hB hes in
lemma arbitrary_bagTable :
    List.Forall₂ List.Perm (bagTable ((matrixRep (reindex B (orderedIso V)),xs),es))
      (List.ofFn (fun i=>ExecutableDP.bagRep
        (arbitraryNumberedBags B hsym htri xs left right (UnitRefresh.orderedEnum V i)))) := by
  unfold bagTable
  rw [matrixRep_length,ExecutableDP.map_range_ofFn]
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp,?_⟩
  intro i hi _right_bound
  have hh:=arbitrary_bag_perm B hB hsym htri xs left right es hes
    (UnitRefresh.orderedEnum V ⟨i,by simpa using hi⟩)
  simpa only [List.get_eq_getElem,List.getElem_ofFn,index,Equiv.symm_apply_apply] using hh
include hB hes in
lemma arbitrary_bagTable_length (H : ℕ) (h : xs.length=H) :
    List.Forall₂ List.Perm (bagTable ((matrixRep (reindex B (orderedIso V)),xs),es))
      (List.ofFn (fun i=>ExecutableDP.bagRep
        ((NumberedHierarchy.bags B hsym htri left right H (UnitRefresh.orderedEnum V i)).map
          (UnitRefresh.orderedEnum (Label B H)).symm.toEmbedding))) := by
  subst H
  exact arbitrary_bagTable B hB hsym htri xs left right es hes

include hB hes in
lemma arbitrary_bagTable_numbered (H : ℕ) (h : xs.length=H) :
    List.Forall₂ List.Perm (bagTable ((matrixRep (reindex B (orderedIso V)),xs),es))
      (ExecutableDP.orderedRep (UnitRefresh.numberedBags
        (NumberedHierarchy.bags B hsym htri left right H))) :=
  arbitrary_bagTable_length B hB hsym htri xs left right es hes H h

include hB hes in
lemma arbitrary_bagTable_enumerated (H : ℕ) (h : xs.length=H) :
    List.Forall₂ List.Perm
      (bagTable ((matrixRep (fun i j=>B (UnitRefresh.orderedEnum V i) (UnitRefresh.orderedEnum V j)),xs),es))
      (ExecutableDP.orderedRep (UnitRefresh.numberedBags
        (NumberedHierarchy.bags B hsym htri left right H))) :=
  arbitrary_bagTable_numbered B hB hsym htri xs left right es hes H h

include hB hes in
lemma arbitrary_bagTable_fintype (H : ℕ) (h : xs.length=H)
    (F : Fintype (Label B H)) :
    letI := F
    List.Forall₂ List.Perm
      (bagTable ((matrixRep (fun i j=>B (UnitRefresh.orderedEnum V i) (UnitRefresh.orderedEnum V j)),xs),es))
      (ExecutableDP.orderedRep (UnitRefresh.numberedBags
        (NumberedHierarchy.bags B hsym htri left right H))) := by
  have hf : F=ordinaryLabelFintype B H := Subsingleton.elim _ _
  subst F
  exact arbitrary_bagTable_enumerated B hB hsym htri xs left right es hes H h

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeOrderedTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped.Numbered
variable {A B C : Type} [Fintype A] [Fintype B] [LinearOrder A] [LinearOrder B]
lemma ordered_lists_transport (e : A≃o B) (f : A→C) (g : B→C)
    (h : ∀ a,f a=g (e a)) :
    List.ofFn (fun i=>f (UnitRefresh.orderedEnum A i))=
      List.ofFn (fun i=>g (UnitRefresh.orderedEnum B i)) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn]
    exact Fintype.card_congr e.toEquiv
  · intro i hi hj
    simp only [List.length_ofFn] at hi hj
    simp only [List.getElem_ofFn,h]
    congr 1
    apply index_injective
    rw [index_orderIso,index_orderedEnum,index_orderedEnum]
lemma parentTag_transport (e : A≃o B) (o : Option A) :
    ExecutableDP.parentTag (o.map (UnitRefresh.orderedEnum A).symm)=
      ExecutableDP.parentTag ((o.map e).map (UnitRefresh.orderedEnum B).symm) := by
  cases o with
  | none=>rfl
  | some a=>
    change (true,index a)=(true,index (e a))
    rw [index_orderIso]
end MatchingFPRAS.TreeTyped.Numbered

namespace MatchingFPRAS.NumberedHierarchy
variable {V W : Type} [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
variable (B : W→W→ℚ) (e : V≃o W)
variable (hsym : ∀ a b,B a b=B b a)
variable (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
lemma parent_reindex {H : ℕ} (l : Label (reindex B e) H) :
    (parent (reindex B e) (reindex_symm B e hsym) (reindex_tri B e htri) l).map
      (labelReindex B e H)=parent B hsym htri (labelReindex B e H l) := by
  unfold parent
  change (if h : 0<l.1.val then some (labelAt (reindex B e) (reindex_symm B e hsym)
    (reindex_tri B e htri) ⟨l.1.val-1,by omega⟩ l.2.val) else none).map (labelReindex B e H)=
    if h : 0<l.1.val then some (labelAt B hsym htri ⟨l.1.val-1,by omega⟩ (e l.2.val)) else none
  split_ifs with h
  · rw [Option.map_some]
    exact congrArg some (labelAt_reindex B e hsym htri _ _)
  · rfl
end MatchingFPRAS.NumberedHierarchy

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeTyped.Numbered ExecutableBottleneck NumberedHierarchy

variable {V : Type} [Fintype V] [LinearOrder V]
variable (B : V→V→ℚ) (hB : ∀ a b,0≤B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
attribute [local instance] NumberedHierarchy.labelOrder
local instance (priority := 2000) instLELabel_r4c82d9_1 {U : Type} [Fintype U] [LinearOrder U] {H : ℕ}
    (C : U→U→ℚ) : LE (Label C H) := (labelOrder C H).toLE
include hB in
lemma arbitrary_parents (xs : List Bool) :
    parents (matrixRep (reindex B (orderedIso V)),xs)=
      ExecutableDP.parentRep (UnitRefresh.numberedParent
        (NumberedHierarchy.parent B hsym htri (H:=xs.length))) := by
  let e:=orderedIso V
  rw [parents_eq _ (fun a b=>hB (e a) (e b)) (reindex_symm B e hsym) (reindex_tri B e htri)]
  unfold ExecutableDP.parentRep UnitRefresh.numberedParent
  exact ordered_lists_transport (labelOrderReindex B e xs.length)
    (fun a=>ExecutableDP.parentTag ((NumberedHierarchy.parent (reindex B e)
      (reindex_symm B e hsym) (reindex_tri B e htri) a).map
        (UnitRefresh.orderedEnum (Label (reindex B e) xs.length)).symm))
    (fun a=>ExecutableDP.parentTag ((NumberedHierarchy.parent B hsym htri a).map
      (UnitRefresh.orderedEnum (Label B xs.length)).symm)) (fun a=>by
    rw [parentTag_transport (labelOrderReindex B e xs.length)]
    change ExecutableDP.parentTag (Option.map (UnitRefresh.orderedEnum (Label B xs.length)).symm
      (Option.map (labelReindex B e xs.length)
        (NumberedHierarchy.parent (reindex B e) (reindex_symm B e hsym) (reindex_tri B e htri) a)))=_
    rw [parent_reindex B e hsym htri]
    rfl)
end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRefreshTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeTyped.Numbered ExecutableDP ExecutableRefresh NumberedHierarchy

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
variable {V : Type} [Fintype V] [LinearOrder V]
variable (B : V→V→ℚ) (hB : ∀ a b,0≤B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
include hB in
lemma arbitrary_labelIndices (xs : List Bool) :
    labelIndices (ExecutableBottleneck.matrixRep (reindex B (orderedIso V)),xs)=
      List.range (Fintype.card (Label B xs.length)) := by
  unfold labelIndices
  rw [labels_eq_ofFn _ (fun i j=>hB _ _),List.length_ofFn,
    Fintype.card_congr (labelReindex B (orderedIso V) xs.length)]

open TreePost Turing

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeColoredIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeTyped.Numbered ExecutableBottleneck NumberedHierarchy

attribute [local instance] NumberedHierarchy.labelOrder
variable {V : Type} [Fintype V] [LinearOrder V]
variable (B : V→V→ℚ) (hB : ∀ a b,0≤B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
variable (xs : List Bool) {E : Type} [Fintype E] [DecidableEq E] (left right : E→V)

omit [Fintype E] [DecidableEq E] in
include hB in
lemma arbitrary_labelIndices_fintype (H : ℕ) (hH : xs.length=H)
    (F : Fintype (Label B H)) :
    letI := F
    labelIndices (matrixRep (fun i j=>B (UnitRefresh.orderedEnum V i)
      (UnitRefresh.orderedEnum V j)),xs)=List.range (Fintype.card (Label B H)) := by
  subst H
  have hF : F=ordinaryLabelFintype B xs.length := Subsingleton.elim _ _
  subst F
  exact arbitrary_labelIndices B hB xs

end MatchingFPRAS.ExecutableHierarchy

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped TreeTyped.Numbered UnitRefresh Transport

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L}

lemma storedCatalog_source (a : ExecutableDP.Bags)
    (ha : List.Forall₂ List.Perm a (ExecutableDP.orderedRep (numberedBags bags))) :
    storedCatalog (a,List.range (Fintype.card L))=sourceCatalog bags := by
  rw [storedCatalog_eq ha,sourceCatalog_eq]
end MatchingFPRAS.ExecutableRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeEstimator
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
lemma fold_sum_repr (xs : List ℚ) (hx : ∀ x∈xs,0≤x) (a : ℚ) (ha : 0≤a) :
    ((xs.map repr).foldl (fun a b=>add (b,a)) (repr a))=repr (xs.sum+a) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    have h : 0≤x:=hx x (by simp)
    simp only [List.map_cons,List.foldl_cons,add_repr h ha]
    rw [ih (fun y hy=>hx y (by simp [hy])) (x+a) (add_nonneg h ha)]
    congr 1
    simp only [List.sum_cons]
    ring
lemma sum_repr (xs : List ℚ) (hx : ∀ x∈xs,0≤x) : sum (xs.map repr)=repr xs.sum := by
  unfold sum
  have h:=fold_sum_repr xs hx 0 (by decide)
  simpa only [add_zero,show repr (0:ℚ)=(0,1) from rfl] using h
end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeScalingCorrect
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableScaling
open TreeTyped TreeFraction ExecutableBottleneck ExecutableLadder

variable {n : ℕ}

lemma rowMax_rep (hn : 2≤n) (G : Fin n→Fin n→ℚ) (v : Fin n→ℚ)
    (hG : ∀ i j,i≠j→0≤G i j) (hv : ∀ j,0≤v j) (i : Fin n) :
    rowMax ((matrixRep G,vectorRep v),i.val)=TreeFraction.repr (Counting.rowMaximum hn G v i) := by
  let js := (List.finRange n).filter (fun j=>decide (j≠i))
  let qs := js.map (fun j=>G i j/v j)
  have hj : ∀ j,j∈js↔j≠i := by intro j; simp [js]
  have hq : ∀ q∈qs,0≤q := by
    intro q h
    obtain ⟨j,hj',rfl⟩:=List.mem_map.mp h
    exact div_nonneg (hG i j ((hj j).mp hj').symm) (hv j)
  have he : ((vectorRep v).filter (fun z=>decide (z.1≠i.val))).map
      (fun z=>ratio ((matrixRep G,i.val),z))=qs.map TreeFraction.repr := by
    unfold vectorRep qs
    rw [List.ofFn_eq_map,List.filter_map,List.map_map,List.map_map]
    have hp : (fun j : Fin n=>decide ((j.val,TreeFraction.repr (v j)).1≠i.val))=
        (fun j=>decide (j≠i)) := by
      funext j
      simp only [ne_eq,Fin.val_inj]
    change List.map _ (List.filter _ (List.finRange n))=_
    rw [show ((fun z : ℕ×Fraction=>decide (z.1≠i.val)) ∘ (fun j : Fin n=>(j.val,TreeFraction.repr (v j))))=
        (fun j=>decide (j≠i)) from hp]
    apply List.map_congr_left
    intro j hj'
    dsimp only [Function.comp_apply,ratio]
    rw [cell_matrixRep,div_repr (hG i j ((hj j).mp hj').symm) (hv j)]
  unfold rowMax
  dsimp only
  rw [he,show ((0,1) : Fraction)=TreeFraction.repr (0:ℚ) from rfl,maximum_fold_repr qs 0 (by decide) hq]
  congr 1
  apply le_antisymm
  · apply fold_max_le
    · obtain ⟨j,hjj⟩:=Counting.others_nonempty hn i
      have hnz:=div_nonneg (hG i j (Finset.mem_erase.mp hjj).1.symm) (hv j)
      exact hnz.trans (Counting.ratio_le_rowMaximum hn G v i j (Finset.mem_erase.mp hjj).1)
    · intro q h
      obtain ⟨j,hj',rfl⟩:=List.mem_map.mp h
      exact Counting.ratio_le_rowMaximum hn G v i j ((hj j).mp hj')
  · apply Finset.sup'_le
    intro j hj'
    exact mem_le_fold_max qs 0 _ (List.mem_map.mpr ⟨j,(hj j).mpr (Finset.mem_erase.mp hj').1,rfl⟩)

end MatchingFPRAS.ExecutableScaling

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeProfile
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck ExecutableHierarchy Polynomial

lemma profile_repr (fuel : List Bool) (B Hu Hv lam : ℚ)
    (hB : 0≤B) (hHu : 0≤Hu) (hHv : 0≤Hv) (_hlam : 0≤lam)
    (i : Fin (4*fuel.length+1)) :
    profile ((fuel,(TreeFraction.repr B,(TreeFraction.repr Hu,(TreeFraction.repr Hv,TreeFraction.repr lam)))),i.val)=
      TreeFraction.repr (RationalSource.profile fuel.length B Hu Hv lam i) := by
  unfold profile RationalSource.profile
  dsimp only
  split_ifs with h h'
  · have hi : i.val/2≤(fuel++fuel).length := by simp only [List.length_append]; omega
    rw [threshold_repr _ _ hi,div_repr hHu (by positivity),maximum_repr hB (by positivity)]
  · rfl
  · have hi : (4*fuel.length-i.val)/2≤(fuel++fuel).length := by simp only [List.length_append]; omega
    rw [threshold_repr _ _ hi,div_repr hHv (by positivity),maximum_repr hB (by positivity)]

lemma height_rep {n : ℕ} (hn : 2≤n) (B : Fin n→Fin n→ℚ) (hB : ∀ i j,0≤B i j) (i : Fin n) :
    height (matrixRep B,i.val)=TreeFraction.repr
      ((Finset.univ.erase i).sup' (Counting.others_nonempty hn i) (B i)) := by
  have he : (List.range (matrixRep B).length).map (fun i=>(i,((1,1) : Fraction)))=
      ExecutableScaling.vectorRep (fun _ : Fin n=>(1:ℚ)) := by
    rw [matrixRep_length]
    unfold ExecutableScaling.vectorRep
    rw [ExecutableDP.map_range_ofFn]
    rfl
  unfold height
  dsimp only
  rw [he,ExecutableScaling.rowMax_rep hn B (fun _=>1) (fun i j _=>hB i j) (by intro j; norm_num) i]
  simp only [Counting.rowMaximum,div_one]

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeWeights
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Polynomial Enlargement RealGeometry

lemma path_repr {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n) (w : Fin n→Fin n→ℚ)
    (hw : ∀ i j,0≤w i j) (K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2)
    (e : LogicalEdge (Fin n)) (i : Fin (4*fuel.length+1)) :
    path (((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),(logicalRepr e,i.val))=
      TreeFraction.repr (RationalSource.pathActivity w K e (Fin.cast (by rw [hf]) i)) := by
  have hB : ∀ a b,0≤RationalSource.logicalB w a b := by
    intro a b
    exact (by norm_num : (0:ℚ)≤1).trans (BottleneckAlgorithm.close_one w _ a b)
  have hHt : ∀ a,0≤RationalSource.height w a := by
    intro a
    obtain ⟨b,hb⟩:=Counting.others_nonempty hn a
    exact (hB a b).trans (Finset.le_sup' _ hb)
  have hheight (a : Fin n) : height (matrixRep (RationalSource.logicalB w),a.val)=
      TreeFraction.repr (RationalSource.height w a) := by
    exact height_rep hn _ hB a
  rw [path,logicalRepr,cell_matrixRep,cell_matrixRep,hheight,hheight]
  rw [profile_repr fuel _ _ _ _ (hB _ _) (hHt _) (hHt _) (hw _ _) i]
  congr 1
  have he : BottleneckAlgorithm.edge w (source e) (target e)=w (source e) (target e) := by
    have hp : source e<target e := e.property
    simp only [BottleneckAlgorithm.edge,ite_eq_left hp]
  rw [RationalSource.pathActivity,he]
  simp only [RationalSource.profile,Fin.val_cast,hf,source,target]

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeWeightsCorrect
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Enlargement RealGeometry

lemma logicalEdges_nodup {vs : List ℕ} (hv : vs.Nodup) : (logicalEdges vs).Nodup :=
  List.Nodup.filter _ (hv.product hv)
lemma realEdges_nodup {vs : List ℕ} (hv : vs.Nodup) (fuel : List Bool) :
    (realEdges (vs,fuel)).Nodup := (logicalEdges_nodup hv).product List.nodup_range
lemma realRepr_injective {n m : ℕ} : Function.Injective (realRepr (n:=n) (m:=m)) := by
  intro a b h
  exact Prod.ext (logicalRepr_injective (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))

lemma realEdges_finset (n K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2) :
    (realEdges (List.range n,fuel)).toFinset=
      Finset.univ.image (realRepr (n:=n) (m:=4*(2*K+2))) := by
  ext e
  simp only [List.mem_toFinset,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · intro he
    obtain ⟨⟨a,i⟩,hi⟩:=realEdges_complete fuel e he
    exact ⟨(a,Fin.cast (by rw [hf]) i),hi⟩
  · rintro ⟨⟨a,i⟩,rfl⟩
    exact realRepr_mem fuel (a,Fin.cast (by rw [hf]) i)

lemma sum_realEdges (n K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2) (f : RawReal→ℚ) :
    ((realEdges (List.range n,fuel)).map f).sum =
      ∑ e : SourceRealEdge (Fin n) K, f (realRepr e) := by
  rw [←List.sum_toFinset f (realEdges_nodup List.nodup_range fuel),realEdges_finset n K fuel hf]
  exact Finset.sum_image (fun a _ b _ h=>realRepr_injective h)

lemma path_source_repr {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n) (w : Fin n→Fin n→ℚ)
    (hw : ∀ i j,0≤w i j) (K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2)
    (e : SourceRealEdge (Fin n) K) :
    path (((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),realRepr e)=
      TreeFraction.repr (RationalSource.pathActivity w K e.1 e.2) := by
  have h:=path_repr hn w hw K fuel hf e.1 (Fin.cast (by rw [hf]) e.2)
  simpa only [Fin.cast_cast,Fin.cast_refl,Fin.val_cast,realRepr,id] using h

lemma ends_source_repr {n : ℕ} (K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2)
    (e : SourceRealEdge (Fin n) K) :
    (left ((List.range n,fuel),realRepr e),right ((List.range n,fuel),realRepr e))=
    (vertexRepr (atVertex source target (4*(2*K+2)) e.1 e.2.castSucc),
     vertexRepr (atVertex source target (4*(2*K+2)) e.1 e.2.succ)) := by
  apply Prod.ext
  · unfold left internalCount
    dsimp only
    rw [hf]
    exact at_repr e.1 e.2.castSucc
  · unfold right internalCount
    dsimp only
    rw [hf]
    exact at_repr e.1 e.2.succ

lemma sameEnds_source {n : ℕ} (K : ℕ) (a b x y : SourceVertex (Fin n) K) :
    sameEnds ((vertexRepr x,vertexRepr y),(vertexRepr a,vertexRepr b))=
      decide (s(a,b)=s(x,y)) := by
  simp only [sameEnds,vertexRepr_injective.eq_iff]
  congr 1
  rw [Sym2.eq_iff]
  apply propext
  constructor
  · rintro (⟨h₁,h₂⟩|⟨h₁,h₂⟩)
    · exact Or.inl ⟨h₁.symm,h₂.symm⟩
    · exact Or.inr ⟨h₂.symm,h₁.symm⟩
  · rintro (⟨h₁,h₂⟩|⟨h₁,h₂⟩)
    · exact Or.inl ⟨h₁.symm,h₂.symm⟩
    · exact Or.inr ⟨h₂.symm,h₁.symm⟩

lemma contribution_source_repr {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) (fuel : List Bool)
    (hf : fuel.length=2*K+2) (x y : SourceVertex (Fin n) K) (e : SourceRealEdge (Fin n) K) :
    contribution ((vertexRepr x,vertexRepr y),
      pathRow ((((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),List.range n),realRepr e))=
    TreeFraction.repr (if RealGeometry.edge source target (4*(2*K+2)) e.1 e.2=s(x,y)
      then RationalSource.pathActivity w K e.1 e.2 else 0) := by
  unfold contribution pathRow
  rw [path_source_repr hn w hw K fuel hf e,ends_source_repr K fuel hf e,
    sameEnds_source K]
  simp only [decide_eq_true_eq]
  change (if RealGeometry.edge source target (4*(2*K+2)) e.1 e.2=s(x,y)
       then TreeFraction.repr (RationalSource.pathActivity w K e.1 e.2) else TreeFraction.repr (0:ℚ))=_
  split_ifs <;> rfl

lemma pathActivity_nonneg {n : ℕ} [Nontrivial (Fin n)] (_hn : 2≤n) (w : Fin n→Fin n→ℚ)
    (hw : ∀ i j,0≤w i j) (K : ℕ) (e : LogicalEdge (Fin n)) (i : Fin (4*(2*K+2)+1)) :
    0≤RationalSource.pathActivity w K e i := by
  have hB : 0≤RationalSource.logicalB w (source e) (target e) :=
    (by norm_num : (0:ℚ)≤1).trans (BottleneckAlgorithm.close_one w _ _ _)
  unfold RationalSource.pathActivity RationalSource.profile
  split_ifs
  · exact hB.trans (le_max_left _ _)
  · unfold BottleneckAlgorithm.edge
    split_ifs <;> exact hw _ _
  · exact hB.trans (le_max_left _ _)

lemma activity_source_repr {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) (fuel : List Bool)
    (hf : fuel.length=2*K+2) (x y : SourceVertex (Fin n) K) :
    activity (pathTable (((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),List.range n),
      (vertexRepr x,vertexRepr y))=TreeFraction.repr (RationalSource.activity w K x y) := by
  let f : RawReal→ℚ := fun e=>
    if sameEnds ((vertexRepr x,vertexRepr y),
      (left ((List.range n,fuel),e),right ((List.range n,fuel),e))) then
        (path (((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),e)).1 /
          ((path (((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),e)).2 : ℚ)
      else 0
  let es:=realEdges (List.range n,fuel)
  let g : SourceRealEdge (Fin n) K→ℚ := fun e=>
    if RealGeometry.edge source target (4*(2*K+2)) e.1 e.2=s(x,y)
      then RationalSource.pathActivity w K e.1 e.2 else 0
  have hg (e) : 0≤g e := by
    dsimp only [g]
    split_ifs
    · exact pathActivity_nonneg hn w hw K _ _
    · exact le_rfl
  have hre (e : SourceRealEdge (Fin n) K) : f (realRepr e)=g e := by
    dsimp only [f,g]
    rw [ends_source_repr K fuel hf e,sameEnds_source K,path_source_repr hn w hw K fuel hf e]
    simp only [decide_eq_true_eq]
    change (if RealGeometry.edge source target (4*(2*K+2)) e.1 e.2=s(x,y)
       then val (TreeFraction.repr (RationalSource.pathActivity w K e.1 e.2)) else 0)=_
    split_ifs
    · exact val_repr (pathActivity_nonneg hn w hw K _ _)
    · rfl
  have hrow (e : RawReal) (he : e∈es) :
      contribution ((vertexRepr x,vertexRepr y),pathRow
        ((((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),List.range n),e))=
        TreeFraction.repr (f e) := by
    have hm : e∈(realEdges (List.range n,fuel)).toFinset:=List.mem_toFinset.mpr he
    rw [realEdges_finset n K fuel hf] at hm
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hm
    rw [hre]
    exact contribution_source_repr hn w hw K fuel hf x y a
  unfold activity pathTable
  rw [List.map_map]
  dsimp only [Function.comp,Prod.fst,Prod.snd]
  have hmap : (es.map fun e=>contribution ((vertexRepr x,vertexRepr y),pathRow
      ((((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),List.range n),e)))=
      (es.map f).map TreeFraction.repr := by
    rw [List.map_map]
    exact List.map_congr_left hrow
  change sum (es.map (fun e=>contribution ((vertexRepr x,vertexRepr y),pathRow
      ((((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),List.range n),e)))) = _
  rw [hmap,sum_repr]
  · congr 1
    rw [sum_realEdges n K fuel hf]
    exact Finset.sum_congr rfl (fun e _=>hre e)
  · intro q hq
    obtain ⟨e,he,rfl⟩:=List.mem_map.mp hq
    have hm : e∈(realEdges (List.range n,fuel)).toFinset:=List.mem_toFinset.mpr he
    rw [realEdges_finset n K fuel hf] at hm
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hm
    rw [hre]
    exact hg a
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeMatrix
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Enlargement RealGeometry

lemma activityMatrix_repr {N : ℕ} (vs : Fin N→RawVertex) (tab : List WeightedEdge)
    (w : Fin N→Fin N→ℚ) (hw : ∀ i j,activity (tab,(vs i,vs j))=TreeFraction.repr (w i j)) :
    activityMatrix (tab,List.ofFn vs)=matrixRep w := by
  unfold activityMatrix activityRow matrixRep
  simp only [List.map_ofFn,Function.comp_def]
  congr 1
  funext i
  congr 1
  funext j
  exact hw i j

lemma activityMatrix_source_repr {n N : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) (fuel : List Bool)
    (hf : fuel.length=2*K+2) (v : Fin N→SourceVertex (Fin n) K) :
    activityMatrix (pathTable (((matrixRep w,matrixRep (RationalSource.logicalB w)),fuel),List.range n),
      List.ofFn (fun i=>vertexRepr (v i)))=
    matrixRep (fun i j=>RationalSource.activity w K (v i) (v j)) := by
  apply activityMatrix_repr
  intro i j
  exact activity_source_repr hn w hw K fuel hf (v i) (v j)
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeBuild
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Enlargement RealGeometry

attribute [local instance] Transport.prodOrder Transport.sumOrder

lemma vertices_eq_ofFn_length (n : ℕ) (fuel : List Bool) (m : ℕ) (h : 4*fuel.length=m) :
    vertices (List.range n,fuel)=List.ofFn (fun i=>vertexRepr
      (UnitRefresh.orderedEnum (Vertex (Fin n) (LogicalEdge (Fin n)) m) i)) := by
  subst m
  exact vertices_eq_ofFn n fuel

lemma source_activity_nonneg {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n) (w : Fin n→Fin n→ℚ)
    (hw : ∀ i j,0≤w i j) (K : ℕ) (a b : SourceVertex (Fin n) K) :
    0≤RationalSource.activity w K a b := by
  unfold RationalSource.activity
  apply Finset.sum_nonneg
  intro q _
  split_ifs
  · exact pathActivity_nonneg hn w hw K q.1 q.2
  · exact le_rfl

lemma buildMatrix_repr {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) :
    buildMatrix ((matrixRep w,List.replicate (2*K+2) false),List.range n)=
      matrixRep (fun i j=>RationalSource.activity w K
        (UnitRefresh.orderedEnum (SourceVertex (Fin n) K) i)
        (UnitRefresh.orderedEnum (SourceVertex (Fin n) K) j)) := by
  unfold buildMatrix prepare materialize
  rw [close_matrixRep w hw]
  rw [show BottleneckAlgorithm.close w n=RationalSource.logicalB w by simp [RationalSource.logicalB]]
  change activityMatrix (pathTable (((matrixRep w,matrixRep (RationalSource.logicalB w)),
    List.replicate (2*K+2) false),List.range n),
    vertices (List.range n,List.replicate (2*K+2) false))=_
  have hv : vertices (List.range n,List.replicate (2*K+2) false)=
      List.ofFn (fun i=>vertexRepr (UnitRefresh.orderedEnum (SourceVertex (Fin n) K) i)) := by
    exact vertices_eq_ofFn_length n _ _ (by simp)
  rw [hv]
  exact activityMatrix_source_repr hn w hw K _ (List.length_replicate ..) _

lemma buildClosure_repr {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) :
    buildClosure ((matrixRep w,List.replicate (2*K+2) false),List.range n)=
      matrixRep (fun i j=>RationalSource.realB w K
        (UnitRefresh.orderedEnum (SourceVertex (Fin n) K) i)
        (UnitRefresh.orderedEnum (SourceVertex (Fin n) K) j)) := by
  unfold buildClosure
  rw [buildMatrix_repr hn w hw K,close_matrixRep _ (fun _ _=>source_activity_nonneg hn w hw K _ _)]
  rw [BottleneckAlgorithm.close_reindex (UnitRefresh.orderedEnum (SourceVertex (Fin n) K))
    UnitRefresh.orderedEnum_lt]
  rfl
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeBagBuild
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder

attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instBEqRawVertex
attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instLawfulBEqRawVertex
lemma index_vertices {n : ℕ} (K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2)
    (v : SourceVertex (Fin n) K) : (vertices (List.range n,fuel)).idxOf (vertexRepr v)=index v := by
  rw [vertices_eq_ofFn_length n fuel _ (by rw [hf])]
  let e:=UnitRefresh.orderedEnum (SourceVertex (Fin n) K)
  let i:=e.symm v
  have hn : (List.ofFn (fun j=>vertexRepr (e j))).Nodup :=
    List.nodup_ofFn.mpr (vertexRepr_injective.comp e.injective)
  have hi : i.val<(List.ofFn (fun j=>vertexRepr (e j))).length := by simpa only [List.length_ofFn] using i.isLt
  have he:=@List.Nodup.idxOf_getElem RawVertex _ _ _ hn i.val hi
  simpa only [List.getElem_ofFn,Fin.eta,i,Equiv.apply_symm_apply,e,index] using he

lemma endpointEntry_source {n : ℕ} (K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2)
    (e : SourceRealEdge (Fin n) K) :
    endpointEntry (((List.range n,fuel),vertices (List.range n,fuel)),realRepr e)=
      (index (realLeft K e),index (realRight K e)) := by
  have h:=ends_source_repr K fuel hf e
  have hl:=congrArg Prod.fst h
  have hr:=congrArg Prod.snd h
  unfold endpointEntry
  dsimp only at hl hr ⊢
  rw [hl,hr,index_vertices K fuel hf,index_vertices K fuel hf]
  rfl

lemma endpointList_members {n : ℕ} (K : ℕ) (fuel : List Bool) (hf : fuel.length=2*K+2)
    (p : ℕ×ℕ) : p∈endpointList (List.range n,fuel) ↔
      ∃ e : SourceRealEdge (Fin n) K,(index (realLeft K e),index (realRight K e))=p := by
  have hm (e : RawReal) : e∈realEdges (List.range n,fuel) ↔
      ∃ a : SourceRealEdge (Fin n) K,realRepr a=e := by
    rw [←List.mem_toFinset,realEdges_finset n K fuel hf]
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
  simp only [endpointList,List.mem_map,hm]
  constructor
  · rintro ⟨e,⟨a,rfl⟩,hp⟩
    exact ⟨a,(endpointEntry_source K fuel hf a).symm.trans hp⟩
  · rintro ⟨e,he⟩
    exact ⟨realRepr e,⟨e,rfl⟩,(endpointEntry_source K fuel hf e).trans he⟩

lemma source_bagTable {n : ℕ} [Nontrivial (Fin n)]
    (w : Fin n→Fin n→ℚ) (K : ℕ) :
    List.Forall₂ List.Perm
      (bagTable ((matrixRep (fun i j=>RationalSource.realB w K
        (UnitRefresh.orderedEnum (SourceVertex (Fin n) K) i)
        (UnitRefresh.orderedEnum (SourceVertex (Fin n) K) j)),
        List.replicate (RationalSource.levels w K) false),
        endpointList (List.range n,List.replicate (2*K+2) false)))
      (ExecutableDP.orderedRep (UnitRefresh.numberedBags (RationalSource.bags w K))) := by
  exact arbitrary_bagTable_fintype (RationalSource.realB w K)
    (fun a b=>(by norm_num : (0:ℚ)≤1).trans (RationalSource.realB_floor w K a b))
    (RationalSource.realB_symm w K) (RationalSource.realB_tri w K)
    (List.replicate (RationalSource.levels w K) false) (realLeft K) (realRight K)
    (endpointList (List.range n,List.replicate (2*K+2) false))
    (endpointList_members K _ (List.length_replicate ..))
    (RationalSource.levels w K) (List.length_replicate ..)
    (inferInstance : Fintype (RationalSource.Label w K))

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeHeight
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck ExecutableHierarchy Enlargement RealGeometry

lemma logicalB_nonneg {n : ℕ} (w : Fin n→Fin n→ℚ) (a b : Fin n) :
    0≤RationalSource.logicalB w a b :=
  (by norm_num : (0:ℚ)≤1).trans (BottleneckAlgorithm.close_one w _ a b)
lemma sourceHeight_nonneg {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (a : Fin n) : 0≤RationalSource.height w a := by
  obtain ⟨b,hb⟩:=Counting.others_nonempty hn a
  exact (logicalB_nonneg w a b).trans (Finset.le_sup' _ hb)
lemma sourceMaxHeight_nonneg {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) : 0≤RationalSource.maxHeight w := by
  exact (sourceHeight_nonneg hn w ⟨0,by omega⟩).trans (Finset.le_sup' _ (Finset.mem_univ _))

lemma maxHeight_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) :
    maxHeight (close (matrixRep w))=TreeFraction.repr (RationalSource.maxHeight w) := by
  rw [close_matrixRep w hw]
  have hc : BottleneckAlgorithm.close w n=RationalSource.logicalB w := by
    simp only [RationalSource.logicalB,Fintype.card_fin]
  rw [hc]
  unfold maxHeight
  have he : (List.range (matrixRep (RationalSource.logicalB w)).length).map
      (fun i=>height (matrixRep (RationalSource.logicalB w),i))=
      (List.ofFn (RationalSource.height w)).map TreeFraction.repr := by
    rw [matrixRep_length,ExecutableDP.map_range_ofFn,List.map_ofFn]
    congr 1
    funext i
    exact height_rep hn _ (logicalB_nonneg w) i
  rw [he]
  change ((List.ofFn (RationalSource.height w)).map TreeFraction.repr).foldl _ (TreeFraction.repr 0)=_
  rw [maximum_fold_repr _ 0 le_rfl (by
    intro x hx
    obtain ⟨a,rfl⟩:=List.mem_ofFn.mp hx
    exact sourceHeight_nonneg hn w a)]
  rw [fold_max_ofFn _ 0 ⟨0,by omega⟩]
  congr 1
  exact max_eq_right (sourceMaxHeight_nonneg hn w)

lemma hierarchyFuel_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K : ℕ) :
    hierarchyFuel (matrixRep w,List.replicate (2*K) false)=
      List.replicate (RationalSource.levels w K) false := by
  unfold hierarchyFuel
  dsimp only
  rw [maxHeight_source hn w hw,List.length_replicate,level_repr _ _ (sourceMaxHeight_nonneg hn w)]
  rw [List.take_replicate]
  congr 1
  exact min_eq_left (Nat.findGreatest_le _)

attribute [local instance] NumberedHierarchy.labelOrder
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeColor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

lemma sourceTables_catalog {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K : ℕ) :
    (sourceTables (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)).1=
      sourceCatalog (RationalSource.bags w K) := by
  rw [sourceTables,refreshTables,setupHierarchy,
    buildClosure_repr hn w hw K,hierarchyFuel_source hn w hw K]
  dsimp only
  rw [arbitrary_labelIndices_fintype (RationalSource.realB w K)
    (fun a b=>(by norm_num : (0:ℚ)≤1).trans (RationalSource.realB_floor w K a b))
    (List.replicate (RationalSource.levels w K) false) (RationalSource.levels w K)
    (List.length_replicate ..) (inferInstance : Fintype (RationalSource.Label w K))]
  have catalog := storedCatalog_source (bags:=RationalSource.bags w K) _ (source_bagTable w K)
  exact catalog

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeMetadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeTyped.Numbered ExecutableBottleneck NumberedHierarchy

attribute [local instance] NumberedHierarchy.labelOrder
variable {V : Type} [Fintype V] [LinearOrder V]
lemma arbitrary_parents_fintype (B : V→V→ℚ) (hB : ∀ a b,0≤B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (xs : List Bool) (H : ℕ) (hH : xs.length=H) (F : Fintype (Label B H)) :
    letI := F
    parents (matrixRep (fun i j=>B (UnitRefresh.orderedEnum V i) (UnitRefresh.orderedEnum V j)),xs)=
      ExecutableDP.parentRep (UnitRefresh.numberedParent (NumberedHierarchy.parent B hsym htri (H:=H))) := by
  subst H
  have hF : F=ordinaryLabelFintype B xs.length := Subsingleton.elim _ _
  subst F
  exact arbitrary_parents B hB hsym htri xs
end MatchingFPRAS.ExecutableHierarchy

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

lemma sourceParents_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K : ℕ) :
    sourceParents (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)=
      ExecutableDP.parentRep (UnitRefresh.numberedParent (RationalSource.parent w K)) := by
  unfold sourceParents setupHierarchy
  dsimp only
  rw [buildClosure_repr hn w hw K,hierarchyFuel_source hn w hw K]
  exact arbitrary_parents_fintype (RationalSource.realB w K)
    (fun a b=>(by norm_num : (0:ℚ)≤1).trans (RationalSource.realB_floor w K a b))
    (RationalSource.realB_symm w K) (RationalSource.realB_tri w K)
    (List.replicate (RationalSource.levels w K) false) (RationalSource.levels w K)
    (List.length_replicate ..) (inferInstance : Fintype (RationalSource.Label w K))

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeGeneratedPrepared
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

lemma sourceVertices_length {n : ℕ} (w : Fin n→Fin n→ℚ) (K : ℕ) :
    (sourceVertices (((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false)).length=
      Fintype.card (SourceVertex (Fin n) K) := by
  unfold sourceVertices
  dsimp only
  rw [vertices_eq_ofFn_length n _ (4*(2*K+2)) (by simp),List.length_ofFn]

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeStageActivity
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableScaling
open TreeTyped TreeFraction ExecutableLadder

lemma lookup_vectorRep {n : ℕ} (v : Fin n→ℚ) (i : Fin n) (d : Fraction) :
    lookup d (vectorRep v,i.val)=TreeFraction.repr (v i) := by
  unfold vectorRep
  rw [List.ofFn_eq_map]
  exact lookup_image d (List.finRange n) Fin.val (fun j=>TreeFraction.repr (v j))
    Fin.val_injective i (by simp)
end MatchingFPRAS.ExecutableScaling

namespace MatchingFPRAS.ExecutableAdaptive
open TreeTyped TreeFraction ExecutableBottleneck ExecutableScaling ExecutableLadder ExecutableSource

lemma cooling_rep (n : ℕ) : cooling n=TreeFraction.repr (FiniteTrial.cooling n) := by
  unfold cooling FiniteTrial.cooling
  rw [←repr_nat n,show ((1,1) : Fraction)=TreeFraction.repr (1:ℚ) from rfl,
    div_repr (by decide) (by positivity),add_repr (by decide) (by positivity),
    div_repr (by decide) (by positivity),one_div]

lemma orderedPair_minmax (a b : ℕ) : orderedPair (a,b)=(min a b,max a b) := by
  unfold orderedPair
  by_cases h : a<b
  · simp [h,min_eq_left h.le,max_eq_right h.le]
  · simp [h,min_eq_right (le_of_not_gt h),max_eq_left (le_of_not_gt h)]
lemma edge_mem_graphRep (G : GraphInput) (i j : Fin G.n) :
    orderedPair (i.val,j.val)∈(graphRep G).2 ↔ (min i j,max i j)∈G.edges := by
  rw [orderedPair_minmax]
  simp only [graphRep,List.mem_map,Finset.mem_toList]
  constructor
  · rintro ⟨⟨a,b⟩,hab,he⟩
    have ha : a=min i j := Fin.ext (congrArg Prod.fst he)
    have hb : b=max i j := Fin.ext (congrArg Prod.snd he)
    simpa [ha,hb] using hab
  · intro h
    exact ⟨(min i j,max i j),h,rfl⟩
lemma rawCell_rep (G : GraphInput) (fuel : List Bool) (a : Fin G.n→ℚ) (i j : Fin G.n) :
    rawCell (cellData ((graphRep G,fuel),vectorRep a),(i.val,j.val))=
      TreeFraction.repr (FiniteTrial.raw G fuel.length i j) := by
  unfold rawCell cellData
  dsimp only
  simp only [edge_mem_graphRep]
  unfold FiniteTrial.raw
  split_ifs
  · rfl
  · rw [show (graphRep G).1.length=G.n by simp [graphRep],cooling_rep,
      fuelPower_repr _ (by unfold FiniteTrial.cooling; positivity)]
lemma stageMatrix_rep (G : GraphInput) (fuel : List Bool) (a : Fin G.n→ℚ) (ha : ∀ i,0 ≤ a i) :
    stageMatrix ((graphRep G,fuel),vectorRep a)=
      matrixRep (fun i j=>FiniteTrial.raw G fuel.length i j*a i*a j) := by
  have hr (i j : Fin G.n) : 0 ≤ FiniteTrial.raw G fuel.length i j := by
    unfold FiniteTrial.raw FiniteTrial.cooling
    split_ifs <;> positivity
  unfold stageMatrix stageRow matrixRep
  change (List.range G.n).map _=(List.ofFn _)
  simp only [ExecutableDP.map_range_ofFn]
  congr 1
  funext i
  change (List.range G.n).map _=List.ofFn _
  rw [ExecutableDP.map_range_ofFn]
  congr 1
  funext j
  unfold stageCell
  rw [rawCell_rep,show (cellData ((graphRep G,fuel),vectorRep a)).2=vectorRep a from rfl,
    lookup_vectorRep a i,lookup_vectorRep a j,mul_repr (hr i j) (ha i),
    mul_repr (mul_nonneg (hr i j) (ha i)) (ha j)]
end MatchingFPRAS.ExecutableAdaptive

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeSparseStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics ExecutableScaling ExecutableAdaptive

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

lemma sparseUpdateData_source {G : GraphInput} {j : ℕ} (s : FiniteTrial.ScaleState G j)
    (K D : ℕ) (ft fq : List Bool) :
    sparseUpdateData (((graphRep G,List.replicate j false),
      (((List.replicate (2*K+2) false,List.replicate (2*K) false),D),(ft,fq))),vectorRep s.scale)=
      (((((((matrixRep s.activity,List.replicate (2*K+2) false),List.range G.n),List.replicate (2*K) false),D),(ft,fq)),
       matrixRep s.nextActivity),vectorRep s.scale) := by
  unfold sparseUpdateData sparseGeneratedInput sparseBagInput sparseCurrentMatrix sparseNextMatrix currentActivityArg nextActivityArg
  dsimp only
  rw [stageMatrix_rep G _ s.scale (fun i=>(s.positive i).le),stageMatrix_rep G _ s.scale (fun i=>(s.positive i).le)]
  simp only [List.length_replicate,List.length_cons]
  rfl

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineRequest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped TreeFraction Transport ExecutableSource NumericLadder ExecutableScaling
open TreeTyped.Numbered Enlargement UnitRefresh ExecutableAdaptive
open ExecutableBottleneck ExecutableHierarchy ExecutableRefresh

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

lemma sparseBagInput_source {G : GraphInput} {j : ℕ} (s : FiniteTrial.ScaleState G j)
    (K D : ℕ) (ft fq : List Bool) :
    sparseBagInput (OnlineStage.data s K D ft fq)=
      (((matrixRep s.activity,List.replicate (2*K+2) false),List.range G.n),List.replicate (2*K) false) := by
  have h:=sparseUpdateData_source s K D ft fq
  exact congrArg (fun x=>x.1.1.1.1) h

lemma sourcePrecision_source {G : GraphInput} [Nontrivial (Fin G.n)] (hn : 2≤G.n)
    {j : ℕ} (s : FiniteTrial.ScaleState G j) (K D S : ℕ) (ft fq : List Bool) :
    sourcePrecision (OnlineStage.data s K D ft fq,S)=
      (((((Fintype.card (SourceVertex (Fin G.n) K)),D),(K,ft.length)),1000*K*S),
        (Fintype.card (BagEdge (RationalSource.bags s.activity K)),Fintype.card (RationalSource.Label s.activity K))) := by
  unfold sourcePrecision
  rw [sparseBagInput_source]
  dsimp only [OnlineStage.data]
  rw [sourceVertices_length,sourceTables_catalog hn s.activity
    (fun i j=>(s.activity_pos i j).le) K,sourceParents_source hn s.activity
    (fun i j=>(s.activity_pos i j).le) K]
  simp only [List.length_replicate,Nat.mul_div_cancel_left _ (by decide : 0<2),sourceCatalog,List.length_ofFn,
    ExecutableDP.parentRep_length]

end MatchingFPRAS.OnlineSchedule

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OutputLengthBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Variation
open Transport

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
omit [Fintype C] in
lemma imageLaw_ignore_right [Nonempty B] (f : A → C) :
    imageLaw (fun x : A×B=>f x.1)=imageLaw f := by
  have hh:=imageLaw_comp_equiv (Equiv.prodComm A B) (fun x : B×A=>f x.2)
  exact hh.trans (imageLaw_ignore f)
omit [Fintype A] in
lemma padSampler_law {k B : ℕ} (h : k≤B) (f : (Fin k → Bool) → A) :
    imageLaw (padSampler h f)=imageLaw f :=
  (imageLaw_comp_equiv (paddedBits h) (fun x=>f x.1)).trans (imageLaw_ignore_right f)
end MatchingFPRAS.Variation
namespace MatchingFPRAS.RationalSource
open Transport Enlargement Variation

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelCastReal_4_r4c82d9_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instFintypeBagEdgeSourceVertexSourceLabelCastRealSourceBags_4
noncomputable local instance instDecidableEqBagPMSourceVertexLabelBags_5_r4c82d9_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (BagPM (bags w K)) := Classical.decEq _
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instFintypeMarked_2
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instFintypeSourceMarkedCastReal_2
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instFintypeProdForallFinBoolForallBagEdgeSourceVertexLabelBags_1
lemma bitSampler_law (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ)
    (hD : 0<D) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) :
    imageLaw (bitSampler w hw K D m hD hN h hq M η)=finiteSourceLaw w hw K D m hD hN h hq M η := by
  dsimp only [bitSampler,samplerBitCount]
  erw [←Function.comp_assoc,imageLaw_comp_equiv,imageLaw_output_equiv]
  rfl
lemma fixedSampler_law (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ)
    (hD : 0<D) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) :
    imageLaw (fixedSampler w hw K D m hD hN h hq M η)=finiteSourceLaw w hw K D m hD hN h hq M η := by
  rw [fixedSampler,padSampler_law,bitSampler_law]
end MatchingFPRAS.RationalSource

namespace MatchingFPRAS.FiniteTrial
open Transport Enlargement Variation Adaptive

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelFinNCastReal_4_r4c82d9_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
attribute [local instance] OAI.MatchingFPRAS.FiniteTrial.instFintypeSourceMarkedFinNCastReal_3
lemma ScaleState.drawOne_law (p : Trial.Parameters G) {j : ℕ} (hj : j≤p.K) (s : ScaleState G j) :
    imageLaw (s.drawOne p hj)=(s.runLaw p hj).mass := by
  exact RationalSource.fixedSampler_law _ _ _ _ _ _ _ _ _ _ _
lemma ScaleState.drawStage_law (p : Trial.Parameters G) {j : ℕ} (hj : j≤p.K) (s : ScaleState G j) :
    imageLaw (s.drawStage p hj)=(s.sampleLaw p hj).mass := by
  unfold ScaleState.drawStage
  erw [imageLaw_comp_equiv,imageLaw_componentwise]
  rw [ScaleState.drawOne_law]
  rfl

open Transport Enlargement Variation Adaptive

attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
end MatchingFPRAS.FiniteTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineFoldCost
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open TreeTyped PhysicalStream Polynomial

variable {A B : Type} [Codec A] [Codec B]

omit [Codec B] in
lemma fold_cost_bound (f : A×B→Experiment B) (t : A×B→ℕ)
    (as : List A) (b : B) (P : ℕ→B→Prop) (C M : ℕ)
    (hb : P as.length b) (hw : weight as≤M)
    (hs : ∀ a∈as,∀ k<as.length,∀ b,P (k+1) b→(f (a,b)).All (P k))
    (hc : ∀ a∈as,∀ k<as.length,∀ b,P (k+1) b→t (a,b)≤C) :
    Fold.cost f t as b≤as.length*(C+14*M+34)+10 ∧ (foldM f as b).All (P 0) := by
  induction as generalizing b with
  | nil => exact ⟨by simp [Fold.cost],hb⟩
  | cons a as ih =>
    have hwa : weight a≤M := by rw [weight_cons] at hw; omega
    have hwt : weight as≤M := by rw [weight_cons] at hw; omega
    have hb' : P (as.length+1) b := hb
    have hstep := hs a (by simp) as.length (by simp) b hb'
    have htime := hc a (by simp) as.length (by simp) b hb'
    have htt : (f (a,b)).All (fun v=>Fold.cost f t as v≤as.length*(C+14*M+34)+10 ∧
        (foldM f as v).All (P 0)) := hstep.mono (fun v hv=>ih v hv hwt
          (fun a ha k hk v hv=>hs a (by simp [ha]) k (by simp only [List.length_cons]; omega) v hv)
          (fun a ha k hk v hv=>hc a (by simp [ha]) k (by simp only [List.length_cons]; omega) v hv))
    constructor
    · have hworst := Experiment.worst_le _ _ _ (htt.mono (fun _ h=>h.1))
      change t (a,b)+6*weight a+8*weight as+34+_≤_
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · rw [foldM,Experiment.all_bind]
      exact htt.mono (fun _ h=>h.2)

end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineSampleCost
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSample
open TreeTyped PhysicalStream Polynomial

variable {A B : Type} [Codec A] [Codec B]
lemma weight_replicate (n : ℕ) (a : A) : weight (List.replicate n a)=n*(1+weight a)+1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ,weight_cons,ih,Nat.succ_mul];omega
end MatchingFPRAS.OnlineSample

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineStageCost
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTrial
open TreeTyped PhysicalStream Polynomial NumericBounds OnlineSchedule OnlineSample

lemma weight_le_stateSize (x : State) : weight x ≤ stateSize x := by unfold stateSize;omega
end MatchingFPRAS.OnlineTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineStage
open PhysicalStream TreeTyped ExecutableSource NumericLadder TreeFraction ExecutableScaling
open UnitRefresh Transport Enlargement TreeTyped.Numbered ExecutableAdaptive Variation

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

variable {n : ℕ} [Nontrivial (Fin n)]
variable (w : Fin n→Fin n→ℚ) (K D m : ℕ)
lemma raw_scan (η : ℚ) (bs : Raw w K D m η) :
    runBitsEquiv (SourceVertex (Fin n) K) (choiceWidth w K D m η) (scansCount (n:=n) K D m)
      ((rawEquiv w K D m η).symm bs).1=bs.1 :=
  congrArg Prod.fst ((rawEquiv w K D m η).apply_symm_apply bs)
lemma raw_marks (η : ℚ) (bs : Raw w K D m η) (e : BagEdge (RationalSource.bags w K)) :
    ((rawEquiv w K D m η).symm bs).2 e=bs.2 ((orderedEnum _).symm e) := rfl
lemma generated_eq_core (hw : ∀ a b,0<w a b) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K) (he : Even n)
    (ft fq : List Bool) (hq : 0<fq.length) {k r km : ℕ}
    (bits : Fin r→ScanBits (SourceVertex (Fin n) K) k)
    (mb : BagEdge (RationalSource.bags w K)→Fin km→Bool) :
    generatedSourceSample he w hw K D hD hu ft fq hq bits mb=
      core w K D hw hD hu he ft.length fq.length hq bits mb := rfl

lemma generated_eq_raw (hw : ∀ a b,0<w a b) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (hq : 0 < copies (n:=n) K D) (he : Even n) (η : ℚ) (bs : Raw w K D m η) :
    generatedSourceSample he w hw K D hD hu
      (List.replicate (tierCount (n:=n) K D) false) (List.replicate (copies (n:=n) K D) false)
      (by simpa only [List.length_replicate] using hq) bs.1
      (fun e=>bs.2 ((orderedEnum (BagEdge (RationalSource.bags w K))).symm e)) =
    rawDraw w K D m hw hD hu hq he η bs := by
  rw [generated_eq_core]
  simp only [List.length_replicate]
  unfold core rawDraw RationalSource.markedSampler TableMarking.draw RationalSource.topSampler
    RationalSource.sampler finiteLadder ladderBitRun
  simp only [Function.comp_apply,raw_scan,raw_marks]

lemma rawDraw_law (hw : ∀ a b,0<w a b) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (hq : 0 < copies (n:=n) K D) (he : Even n) (η : ℚ) :
    imageLaw (rawDraw w K D m hw hD hu hq he η)=
      RationalSource.markedSamplerLaw w hw K D m hD Fintype.card_pos hu hq
        (RationalSource.startMatching w K he) η := by
  unfold rawDraw RationalSource.markedSamplerLaw
  apply Eq.trans (imageLaw_comp_equiv (rawEquiv w K D m η).symm _)
  exact imageLaw_instances _ _ _
end MatchingFPRAS.OnlineStage

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_OnlineLawBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream
open Finset Variation

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
lemma qaverage_imageLaw (f : A→B) (h : B→ℚ) :
    ((qaverage (fun a=>h (f a)) : ℚ):ℝ)=∑ b,imageLaw f b*(h b:ℝ) := by
  classical
  unfold imageLaw push uniform
  simp only [sum_mul,ite_mul,zero_mul]
  rw [sum_comm]
  simp only [sum_ite_eq,mem_univ,ite_true,one_div,inv_mul_eq_div]
  unfold qaverage
  push_cast
  rw [sum_div]
lemma qaverage_eq_of_imageLaw_eq (f : A→C) (g : B→C)
    (he : imageLaw f=imageLaw g) (h : C→ℚ) :
    qaverage (fun a=>h (f a))=qaverage (fun b=>h (g b)) := by
  apply Rat.cast_injective (α:=ℝ)
  rw [qaverage_imageLaw,qaverage_imageLaw,he]
end MatchingFPRAS.PhysicalStream

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineTransitionLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineStage
open PhysicalStream TreeTyped ExecutableSource NumericLadder TreeFraction ExecutableScaling
open UnitRefresh Transport Enlargement TreeTyped.Numbered ExecutableAdaptive Variation

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
variable {n : ℕ} [Nontrivial (Fin n)]
variable (w : Fin n→Fin n→ℚ) (K D m : ℕ)
attribute [local instance] OAI.MatchingFPRAS.OnlineStage.instFintypeMarkedFin_1
attribute [local instance] OAI.MatchingFPRAS.OnlineStage.instFintypeSourceMarkedFinCastReal
lemma realRawDraw_law (hw : ∀ a b,0<w a b) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (hq : 0 < copies (n:=n) K D) (he : Even n) (η : ℚ) :
    imageLaw (realRawDraw w K D m hw hD hu hq he η)=
      RationalSource.finiteSourceLaw w hw K D m hD Fintype.card_pos hu hq
        (RationalSource.startMatching w K he) η := by
  unfold realRawDraw
  rw [imageLaw_output_equiv,rawDraw_law]
  rfl
lemma realRawDraw_inverse (hw : ∀ a b,0<w a b) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (hq : 0 < copies (n:=n) K D) (he : Even n) (η : ℚ) (b : Raw w K D m η) :
    RationalSource.sourceMarkedEquiv w K (realRawDraw w K D m hw hD hu hq he η b)=
      rawDraw w K D m hw hD hu hq he η b :=
  (RationalSource.sourceMarkedEquiv w K).apply_symm_apply _

lemma finiteLaw_parameters (hw : ∀ a b,0<w a b) (D' : ℕ) (hDD : D=D')
    (hD : 0<D) (hD' : 0<D')
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (hq : 0 < copies (n:=n) K D) (hq' : 0 < copies (n:=n) K D')
    (M : BagPM (RationalSource.bags w K)) (η η' : ℚ) (hη : η=η') :
    RationalSource.finiteSourceLaw w hw K D m hD Fintype.card_pos hu hq M η=
      RationalSource.finiteSourceLaw w hw K D' m hD' Fintype.card_pos hu hq' M η' := by
  subst D'; subst η'; rfl

variable {G : GraphInput} [Nontrivial (Fin G.n)]

lemma transition_mean {j : ℕ} (p : Trial.Parameters G) (hj : j≤p.K)
    (s : FiniteTrial.ScaleState G j) (h : Fraction×Vector→ℚ) :
    (transition p s).mean h=
      qaverage (fun bits : Fin (FiniteTrial.stageBits p)→Bool=>
        let x := RationalSource.sourceMarkedEquiv s.activity p.K ∘ s.drawStage p hj bits
        h (repr (s.ratioEstimate x),vectorRep (s.update p.hn x).scale)) := by
  have hD : 0<FiniteTrial.sourceD (G:=G) p.K := by
    rw [FiniteTrial.sourceD_eq]
    exact Enlargement.sourceD_one p.K
  have hq : 0 < copies (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K) := by
    simpa only [copies,vertexCount,FiniteTrial.sourceD_eq,Trial.Parameters.q,Trial.Parameters.N,Trial.Parameters.D] using p.q_pos
  unfold transition fixedData fixedRequest
  simp only [Trial.Parameters.N]
  rw [source_mean p.hn p.even s p.K hD (s.cap hj) _ _ (by simpa using hq)]
  let raw := realRawDraw s.activity p.K (FiniteTrial.sourceD (G:=G) p.K) (denominator p)
    s.activity_pos hD (s.cap hj) hq p.even (1/denominator p)
  have hr : imageLaw raw=(s.runLaw p hj).mass := by
    rw [realRawDraw_law]
    dsimp only [FiniteTrial.ScaleState.runLaw]
    apply finiteLaw_parameters
    · exact FiniteTrial.sourceD_eq p.K
    · simp only [denominator,Nat.cast_mul,Nat.cast_ofNat]
  have hp : imageLaw (fun bs : Fin p.S→Raw s.activity p.K (FiniteTrial.sourceD (G:=G) p.K)
      (denominator p) (1/denominator p)=>fun i=>raw (bs i)) = imageLaw (s.drawStage p hj) := by
    rw [imageLaw_componentwise,hr,FiniteTrial.ScaleState.drawStage_law]
    rfl
  have hmean := qaverage_eq_of_imageLaw_eq _ _ hp (fun y=>
    let x:=RationalSource.sourceMarkedEquiv s.activity p.K ∘ y
    h (repr (s.ratioEstimate x),vectorRep (s.update p.hn x).scale))
  apply Eq.trans _ hmean
  apply qaverage_congr
  intro bs
  have hx : (fun i=>generatedSourceSample p.even s.activity s.activity_pos p.K
      (FiniteTrial.sourceD (G:=G) p.K) hD (s.cap hj)
      (List.replicate (tierCount (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)) false)
      (List.replicate (copies (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)) false)
      (by simpa using hq) (bs i).1 (fun e=>(bs i).2 ((orderedEnum _).symm e))) =
      RationalSource.sourceMarkedEquiv s.activity p.K ∘ (fun i=>raw (bs i)) := by
    funext i
    rw [generated_eq_raw]
    exact (realRawDraw_inverse ..).symm
  rw [hx]
end MatchingFPRAS.OnlineStage

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineRequestLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open PhysicalStream TreeTyped TreeFraction ExecutableSource ExecutableScaling Transport
open UnitRefresh Enlargement TreeTyped.Numbered OnlineStage ExecutableRefresh

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

lemma bitPrecision_inverseNat (R m : ℕ) : bitPrecision R (1/(m:ℚ))=Nat.clog 2 (R*m) := by
  simp [bitPrecision]

variable {G : GraphInput} [Nontrivial (Fin G.n)]
lemma sourceRequest_source {j : ℕ} (p : Trial.Parameters G) (s : FiniteTrial.ScaleState G j) :
    sourceRequest (fixedData p s,p.S)=fixedRequest p s := by
  unfold sourceRequest
  rw [show sourcePrecision (fixedData p s,p.S)=
    (((((Fintype.card (SourceVertex (Fin G.n) p.K)),FiniteTrial.sourceD (G:=G) p.K),
      (p.K,tierCount (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K))),denominator p),
      (edgeCount s.activity p.K,labelCount s.activity p.K)) from by
    simpa only [fixedData,denominator,edgeCount,labelCount,List.length_replicate] using
      sourcePrecision_source p.hn s p.K (FiniteTrial.sourceD (G:=G) p.K) p.S
        (List.replicate (tierCount (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)) false)
        (List.replicate (copies (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)) false)]
  have hc : (sourceTables (sparseBagInput (fixedData p s))).1.length=edgeCount s.activity p.K := by
    unfold fixedData
    rw [sparseBagInput_source,sourceTables_catalog p.hn s.activity
      (fun i j=>(s.activity_pos i j).le) p.K]
    simp only [sourceCatalog,List.length_ofFn]
  simp only [hc,precisionPlan,fixedRequest,choiceWidth,markWidth,bitPrecision_inverseNat]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · simp only [index_orderedEnum]
      apply List.ext_getElem
      · simp
      · intro _ _ _
        simp
end MatchingFPRAS.OnlineSchedule

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_OnlineLayerLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream
lemma qaverage_const {A : Type} [Fintype A] [Nonempty A] (q : ℚ) :
    qaverage (fun _ : A=>q)=q := by
  simp only [qaverage,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have h : (Fintype.card A:ℚ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
end MatchingFPRAS.PhysicalStream

namespace MatchingFPRAS.OnlineTrial
open PhysicalStream TreeTyped TreeFraction ExecutableSource ExecutableScaling Transport UnitRefresh Enlargement

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
variable {G : GraphInput} [Nontrivial (Fin G.n)]

omit [Nontrivial (Fin G.n)] in
lemma product_nonneg [Nontrivial (Fin G.n)] {j : ℕ} (p : Trial.Parameters G) (L : FiniteTrial.Layer p j) (x : L.Ω) :
    0≤product p L x := mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _=>L.ratios_nonneg x i))
lemma product_append {j : ℕ} (p : Trial.Parameters G) (hj : j≤p.K) (L : FiniteTrial.Layer p j)
    (x : (L.append p hj).Ω) :
    product p (L.append p hj) x = product p L x.1 *
      (L.state x.1).ratioEstimate (RationalSource.sourceMarkedEquiv (L.state x.1).activity p.K ∘ x.2) := by
  unfold product FiniteTrial.Layer.append
  dsimp only
  rw [Fin.prod_snoc,mul_assoc]

end MatchingFPRAS.OnlineTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineTrialLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTrial
open PhysicalStream TreeTyped TreeFraction ExecutableSource ExecutableScaling OnlineSchedule OnlineStage
open Transport UnitRefresh Enlargement

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
variable {G : GraphInput} [Nontrivial (Fin G.n)]

lemma advance_source {j : ℕ} (p : Trial.Parameters G) (s : FiniteTrial.ScaleState G j)
    (xs : Fin p.S→RationalSource.Marked s.activity p.K) :
    advance (fixedData p s,vectorRep (s.update p.hn xs).scale)=fixedData p (s.update p.hn xs) := by
  unfold advance fixedData data
  simp only [List.replicate_succ]

lemma carry_represent {j : ℕ} (p : Trial.Parameters G) (hj : j≤p.K) (L : FiniteTrial.Layer p j)
    (x : (L.append p hj).Ω) :
    carry (represent p L x.1,
      (repr ((L.state x.1).ratioEstimate (RationalSource.sourceMarkedEquiv (L.state x.1).activity p.K ∘ x.2)),
        vectorRep ((L.state x.1).update p.hn (RationalSource.sourceMarkedEquiv (L.state x.1).activity p.K ∘ x.2)).scale))=
      represent p (L.append p hj) x := by
  unfold carry represent
  dsimp only
  rw [advance_source,mul_repr (product_nonneg p L _) ((L.state x.1).ratioEstimate_nonneg x.2),←product_append]
  rfl

lemma step_mean {j : ℕ} (p : Trial.Parameters G) (hj : j≤p.K) (L : FiniteTrial.Layer p j)
    (x : L.Ω) (h : State→ℚ) :
    (step (represent p L x)).mean h=
      qaverage (fun b=>h (represent p (L.append p hj) ⟨x,(L.state x).drawStage p hj b⟩)) := by
  unfold step
  rw [Experiment.mean_map]
  have hp : prepare (represent p L x).1 = (fixedData p (L.state x),(p.S,fixedRequest p (L.state x))) := by
    change (fixedData p (L.state x),(p.S,sourceRequest (fixedData p (L.state x),p.S)))=_
    rw [sourceRequest_source]
  rw [hp]
  change (transition p (L.state x)).mean (fun y=>h (carry (represent p L x,y)))=_
  rw [transition_mean p hj]
  apply qaverage_congr
  intro b
  have hc := carry_represent p hj L ⟨x,(L.state x).drawStage p hj b⟩
  dsimp only at hc ⊢
  exact congrArg h hc

end MatchingFPRAS.OnlineTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_OnlineGraphInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineGraph
open TreeTyped TreeFraction ExecutableAdaptive ExecutableScaling ExecutableSource
open PhysicalStream OnlineSchedule

variable (f : Edges→Edges) (hf : ∀ es e,e∈f es↔e∈es)
include hf
lemma stageCell (es : Edges) (q : Fraction) (v : Vector) (ij : (ℕ×ℕ)) :
    ExecutableAdaptive.stageCell (((f es,q),v),ij)=ExecutableAdaptive.stageCell (((es,q),v),ij) := by
  simp only [ExecutableAdaptive.stageCell,rawCell,hf]
lemma stageRow (es : Edges) (q : Fraction) (v : Vector) (vs : List ℕ) (i : ℕ) :
    ExecutableAdaptive.stageRow ((((f es,q),v),vs),i)=ExecutableAdaptive.stageRow ((((es,q),v),vs),i) := by
  unfold ExecutableAdaptive.stageRow
  simp only [stageCell f hf]
lemma stageMatrix (g : GraphData) (fuel : List Bool) (v : Vector) :
    ExecutableAdaptive.stageMatrix ((graph f g,fuel),v)=ExecutableAdaptive.stageMatrix ((g,fuel),v) := by
  unfold ExecutableAdaptive.stageMatrix cellData graph
  simp only [stageRow f hf]
lemma current (x : SparseStageData) : sparseCurrentMatrix (data f x)=sparseCurrentMatrix x := by
  exact stageMatrix f hf x.1.1.1 x.1.1.2 x.2
lemma next (x : SparseStageData) : sparseNextMatrix (data f x)=sparseNextMatrix x := by
  exact stageMatrix f hf x.1.1.1 (false::x.1.1.2) x.2
lemma bag (x : SparseStageData) : sparseBagInput (data f x)=sparseBagInput x := by
  unfold sparseBagInput
  rw [current f hf]
  rfl
lemma generated (x : SparseStageData) : sparseGeneratedInput (data f x)=sparseGeneratedInput x := by
  unfold sparseGeneratedInput
  rw [bag f hf]
  rfl
lemma update (x : SparseStageData) : sparseUpdateData (data f x)=sparseUpdateData x := by
  unfold sparseUpdateData
  rw [generated f hf,next f hf]
  rfl
lemma stage (x : SparseStageData) (bs : List NumericMarking.SampleBits) :
    sparseStage (data f x,bs)=sparseStage (x,bs) := by
  unfold sparseStage
  rw [update f hf]
lemma sourcePrecision (x : RequestInput) : OnlineSchedule.sourcePrecision (request f x)=OnlineSchedule.sourcePrecision x := by
  unfold OnlineSchedule.sourcePrecision request
  rw [bag f hf]
  rfl
lemma sourceRequest (x : RequestInput) : OnlineSchedule.sourceRequest (request f x)=OnlineSchedule.sourceRequest x := by
  unfold OnlineSchedule.sourceRequest
  rw [sourcePrecision f hf]
  change (_,(_,List.range ((sourceTables (sparseBagInput (data f x.1))).1.length)))=_
  rw [bag f hf]

omit hf in
lemma carry (_ : ∀ edges edge,edge∈f edges↔edge∈edges)
    (x : OnlineTrial.State) (y : Fraction×Vector) :
    OnlineTrial.carry (state f x,y)=state f (OnlineTrial.carry (x,y)) := rfl
lemma step_mean (x : OnlineTrial.State) (h : OnlineTrial.State→ℚ) :
    (OnlineTrial.step (state f x)).mean h=(OnlineTrial.step x).mean (h ∘ state f) := by
  unfold OnlineTrial.step OnlineTrial.prepare OnlineStage.execute
  simp only [Experiment.mean_map]
  change (OnlineSample.many (x.1.2,OnlineSchedule.sourceRequest (request f x.1))).mean
    (fun bs=>h (OnlineTrial.carry (state f x,sparseStage (data f x.1.1,bs))))=_
  rw [sourceRequest f hf]
  simp only [stage f hf,carry f hf,Function.comp_apply]
end MatchingFPRAS.OnlineGraph

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeHistorySize
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableScaling BitArithmetic

lemma fraction_weight_of_bound {B : ℕ} {q : ℚ} (h : FractionBound B (q:ℝ)) :
    TreeTyped.weight (TreeFraction.repr q)≤8*B.size+3 := by
  obtain ⟨hn,hd⟩:=h.num_den
  have hn':=Nat.size_le_size hn
  have hd':=Nat.size_le_size hd
  have h₁:=weight_nat_le q.num.natAbs
  have h₂:=weight_nat_le q.den
  simp only [TreeFraction.repr,weight_prod]
  omega

lemma vectorRep_weight_of_bound {n B : ℕ} (s : Fin n→ℚ)
    (h : ∀ i,FractionBound B (s i:ℝ)) :
    TreeTyped.weight (vectorRep s)≤n*(4*n.size+8*B.size+6)+1 := by
  have hb : ∀ i : Fin n,TreeTyped.weight (i.val,TreeFraction.repr (s i))≤4*n.size+8*B.size+5 := by
    intro i
    have h₁:=fraction_weight_of_bound (h i)
    have h₂:=weight_nat_le i.val
    have h₃:=Nat.size_le_size i.isLt.le
    simp only [weight_prod]
    omega
  unfold vectorRep
  rw [List.ofFn_eq_map]
  have hh:=weight_map_bound (as:=List.finRange n)
    (f:=fun i : Fin n=>(i.val,TreeFraction.repr (s i))) (N:=4*n.size+8*B.size+5)
    (fun i _=>hb i)
  simpa only [List.length_finRange] using hh

lemma history_vector_weight {G : GraphInput} [Nontrivial (Fin G.n)]
    (p : Trial.Parameters G) (j : ℕ) (hj : j≤p.K) (x : (FiniteTrial.layers p j hj).Ω) :
    TreeTyped.weight (vectorRep ((FiniteTrial.layers p j hj).state x).scale)≤
      G.n*(4*G.n.size+8*((G.n+1).size+j*(G.n+1)*
        (19+(p.D+1).size+2*(p.S.size+
          Fintype.card (Enlargement.SourceVertex (Fin G.n) p.K)*(G.n+1).size+1))+1)+6)+1 := by
  have h:=vectorRep_weight_of_bound ((FiniteTrial.layers p j hj).state x).scale
    (FiniteTrial.layers_scale_bits p j hj x)
  have h₁:=size_scaleBound p j
  have h₂:=size_matrixBound p
  have h₃:=size_empiricalBound p
  have hb : (p.scaleBound j).size≤
      (G.n+1).size+j*(G.n+1)*(19+(p.D+1).size+2*(p.S.size+
        Fintype.card (Enlargement.SourceVertex (Fin G.n) p.K)*(G.n+1).size+1))+1 := by
    calc
      _ ≤ (G.n+1).size+j*(G.n+1)*p.matrixBound.size+1 := h₁
      _ ≤ (G.n+1).size+j*(G.n+1)*(19+(p.D+1).size+2*p.empiricalBound.size)+1 := by gcongr
      _ ≤ _ := by gcongr
  exact h.trans (by gcongr)

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineHistorySize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTrial
open TreeTyped TreeFraction PhysicalStream ExecutableSource ExecutableScaling
open BitArithmetic Polynomial OnlineStage OnlineSchedule OnlineSample

variable {G : GraphInput} [Nontrivial (Fin G.n)]

lemma product_bits (p : Trial.Parameters G) (j : ℕ) (hj : j ≤ p.K)
    (x : (FiniteTrial.layers p j hj).Ω) :
    FractionBound ((Z (completeGraph G.n)+1)*(p.empiricalBound^2)^j)
      (product p (FiniteTrial.layers p j hj) x : ℝ) := by
  have h := FractionBound.prod Finset.univ (fun i=>((FiniteTrial.layers p j hj).ratios x i : ℝ)) (p.empiricalBound^2)
    (fun i _=>FiniteTrial.layers_ratio_bits p j hj x i)
  simpa only [product,Rat.cast_mul,Rat.cast_natCast,Rat.cast_prod,Finset.card_univ,Fintype.card_fin] using
    (FractionBound.nat (Z (completeGraph G.n))).mul h

omit [Nontrivial (Fin G.n)] in
lemma sizeNorm_fields (p : Trial.Parameters G) (g : ExecutableAdaptive.GraphData) :
    G.n ≤ sizeNorm p g ∧ p.K ≤ sizeNorm p g ∧ p.N ≤ sizeNorm p g ∧ p.D ≤ sizeNorm p g ∧
    p.S ≤ sizeNorm p g ∧ p.T ≤ sizeNorm p g ∧ p.q ≤ sizeNorm p g ∧ weight g ≤ sizeNorm p g ∧
    (Z (completeGraph G.n)+1).size ≤ sizeNorm p g := by
  unfold sizeNorm;omega

lemma vector_weight_bound (p : Trial.Parameters G) (g : ExecutableAdaptive.GraphData)
    (j : ℕ) (hj : j ≤ p.K) (x : (FiniteTrial.layers p j hj).Ω) :
    weight (vectorRep ((FiniteTrial.layers p j hj).state x).scale) ≤ vectorPolynomial.eval (sizeNorm p g) := by
  obtain ⟨hn,hk,hN,hd,hs,ht,hq,hg,hz⟩:=sizeNorm_fields p g
  have hn' := (Nat.size_le.mpr Nat.lt_two_pow_self : G.n.size ≤ G.n)
  have hn1 := (Nat.size_le.mpr Nat.lt_two_pow_self : (G.n+1).size ≤ G.n+1)
  have hd1 := (Nat.size_le.mpr Nat.lt_two_pow_self : (p.D+1).size ≤ p.D+1)
  have hs' := (Nat.size_le.mpr Nat.lt_two_pow_self : p.S.size ≤ p.S)
  have hv:=history_vector_weight p j hj x
  have hj' : j ≤ sizeNorm p g+1 := by omega
  simp only [vectorPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  change _ ≤ (sizeNorm p g+1)*(4*(sizeNorm p g+1)+8*((sizeNorm p g+1)+(sizeNorm p g+1)*(sizeNorm p g+1)*
    (19+(sizeNorm p g+1)+2*((sizeNorm p g+1)+(sizeNorm p g+1)*(sizeNorm p g+1)+1))+1)+6)+1
  apply hv.trans
  have hNN : Fintype.card (Enlargement.SourceVertex (Fin G.n) p.K) ≤ sizeNorm p g+1 := by
    change p.N ≤ _;omega
  gcongr <;> omega
lemma product_weight_bound (p : Trial.Parameters G) (g : ExecutableAdaptive.GraphData)
    (j : ℕ) (hj : j ≤ p.K) (x : (FiniteTrial.layers p j hj).Ω) :
    weight (TreeFraction.repr (product p (FiniteTrial.layers p j hj) x)) ≤ productPolynomial.eval (sizeNorm p g) := by
  obtain ⟨hn,hk,hN,hd,hs,ht,hq,hg,hz⟩:=sizeNorm_fields p g
  have he := size_empiricalBound p
  have hS:=(Nat.size_le.mpr Nat.lt_two_pow_self : p.S.size ≤ p.S)
  have hnn:=(Nat.size_le.mpr Nat.lt_two_pow_self : (G.n+1).size ≤ G.n+1)
  have he' : p.empiricalBound.size ≤ (sizeNorm p g+1)+(sizeNorm p g+1)*(sizeNorm p g+1)+1 := by
    apply he.trans
    change p.S.size+p.N*(G.n+1).size+1 ≤ _
    gcongr <;> omega
  have hp2:=size_pow_le p.empiricalBound 2
  have hpj:=size_pow_le (p.empiricalBound^2) j
  have hmul:=size_mul_le (Z (completeGraph G.n)+1) ((p.empiricalBound^2)^j)
  have hb : ((Z (completeGraph G.n)+1)*(p.empiricalBound^2)^j).size ≤
      (sizeNorm p g+1)+(sizeNorm p g+1)*(2*((sizeNorm p g+1)+(sizeNorm p g+1)*(sizeNorm p g+1)+1)+1)+1 := by
    calc
      _ ≤ (Z (completeGraph G.n)+1).size+j*(2*p.empiricalBound.size+1)+1 := by
        have h:=Nat.mul_le_mul_left j hp2;omega
      _ ≤ _ := by gcongr <;> omega
  have hw:=fraction_weight_of_bound (product_bits p j hj x)
  simp only [productPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  change _ ≤ 8*((sizeNorm p g+1)+(sizeNorm p g+1)*(2*((sizeNorm p g+1)+(sizeNorm p g+1)*(sizeNorm p g+1)+1)+1)+1)+3
  omega

lemma data_weight (g : ExecutableAdaptive.GraphData) (j K D T Q : ℕ) (v : Vector) :
    weight ((((g,List.replicate j false),(((List.replicate (2*K+2) false,List.replicate (2*K) false),D),
      (List.replicate T false,List.replicate Q false))),v))=
      weight g+2*j+8*K+weight D+2*T+2*Q+weight v+16 := by
  simp only [weight_prod,weight_replicate,show weight false=1 from rfl]
  omega
lemma stateSize_mk (d : SparseStageData) (S : ℕ) (q : Fraction) :
    stateSize ((d,S),q)=d.1.2.1.2+S+3+2*weight d+2*weight S+weight q := by
  unfold stateSize requestSize
  simp only [weight_prod]
  omega
lemma state_weight_bound (f : OnlineGraph.Edges→OnlineGraph.Edges) (p : Trial.Parameters G)
    (j : ℕ) (hj : j ≤ p.K) (x : (FiniteTrial.layers p j hj).Ω) :
    stateSize (OnlineGraph.state f (represent p (FiniteTrial.layers p j hj) x)) ≤
      statePolynomial.eval (sizeNorm p (OnlineGraph.graph f (ExecutableAdaptive.graphRep G))) := by
  let g:=OnlineGraph.graph f (ExecutableAdaptive.graphRep G)
  obtain ⟨hn,hk,hN,hd,hs,ht,hq,hg,hz⟩:=sizeNorm_fields p g
  have hv:=vector_weight_bound p g j hj x
  have hp:=product_weight_bound p g j hj x
  have hD : FiniteTrial.sourceD (G:=G) p.K=p.D := FiniteTrial.sourceD_eq p.K
  have hT : tierCount (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)=p.T := by
    rw [hD];exact Transport.endpoint_eq p.N p.D p.K _
  have hQ : copies (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)=p.q := by rw [hD];rfl
  have hwd:=weight_nat_numeric p.D
  have hws:=weight_nat_numeric p.S
  change stateSize ((OnlineGraph.data f (fixedData p ((FiniteTrial.layers p j hj).state x)),p.S),
    TreeFraction.repr (product p (FiniteTrial.layers p j hj) x)) ≤ _
  rw [stateSize_mk]
  have hw : weight (OnlineGraph.data f (fixedData p ((FiniteTrial.layers p j hj).state x)))=
      weight g+2*j+8*p.K+weight p.D+2*p.T+2*p.q+
      weight (vectorRep ((FiniteTrial.layers p j hj).state x).scale)+16 := by
    change weight ((((g,List.replicate j false),(((List.replicate (2*p.K+2) false,List.replicate (2*p.K) false),
      FiniteTrial.sourceD (G:=G) p.K),(List.replicate (tierCount (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)) false,
        List.replicate (copies (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)) false))),
      vectorRep ((FiniteTrial.layers p j hj).state x).scale))=_
    rw [data_weight,hT,hQ,hD]
  rw [hw]
  change FiniteTrial.sourceD (G:=G) p.K+p.S+3+2*(weight g+2*j+8*p.K+weight p.D+2*p.T+2*p.q+
    weight (vectorRep ((FiniteTrial.layers p j hj).state x).scale)+16)+2*weight p.S+
      weight (TreeFraction.repr (product p (FiniteTrial.layers p j hj) x)) ≤ statePolynomial.eval (sizeNorm p g)
  rw [hD]
  simp only [statePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  omega
end MatchingFPRAS.OnlineTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineHistoryCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream.Experiment
lemma all_of_qaverage {A B : Type} [Fintype B] [Nonempty B] (p : Experiment A) (f : B→A)
    (hm : ∀ h,p.mean h=qaverage (h ∘ f)) (P : A→Prop) (hf : ∀ b,P (f b)) : p.All P := by
  classical
  rw [all_indicator,hm]
  calc
    _=qaverage (fun _ : B=>(0:ℚ)) := by
      apply qaverage_congr
      intro b
      simp only [Function.comp_apply,ite_eq_left (hf b)]
    _=0 := qaverage_const 0
end MatchingFPRAS.PhysicalStream.Experiment

namespace MatchingFPRAS.OnlineTrial
open TreeTyped PhysicalStream Polynomial OnlineGraph OnlineSample

variable {G : GraphInput} [Nontrivial (Fin G.n)]
lemma history_initial (f : Edges→Edges) (p : Trial.Parameters G) : History f p p.K (initial f p).2 := by
  exact ⟨0,by omega,PUnit.unit,by omega,rfl⟩
lemma history_size (f : Edges→Edges) (p : Trial.Parameters G) (k : ℕ) (s : State)
    (hs : History f p k s) : stateSize s≤ statePolynomial.eval (sizeNorm p (graph f (ExecutableAdaptive.graphRep G))) := by
  obtain ⟨j,hj,x,_,rfl⟩:=hs
  exact state_weight_bound f p j hj x
lemma history_step (f : Edges→Edges) (hf : ∀ es e,e∈f es↔e∈es) (p : Trial.Parameters G)
    (k : ℕ) (s : State) (hs : History f p (k+1) s) : (step s).All (History f p k) := by
  classical
  obtain ⟨j,hj,x,hjk,rfl⟩:=hs
  apply Experiment.all_of_qaverage _
    (fun b=>state f (represent p ((FiniteTrial.layers p j hj).append p hj)
      ⟨x,((FiniteTrial.layers p j hj).state x).drawStage p hj b⟩))
  · intro h
    rw [OnlineGraph.step_mean f hf,step_mean p hj]
    rfl
  · intro b
    exact ⟨j+1,by omega,⟨x,((FiniteTrial.layers p j hj).state x).drawStage p hj b⟩,by omega,rfl⟩

open TreeTyped PhysicalStream Polynomial OnlineGraph OnlineSample

lemma sweep_bound_oai : ∃ q : Polynomial ℕ,∀ (G : GraphInput) [Nontrivial (Fin G.n)]
    (f : Edges→Edges) (_hf : ∀ es e,e∈f es↔e∈es) (p : Trial.Parameters G),
    sweepRealizer.cost (initial f p)+(sweep (initial f p)).worst weight≤
      q.eval (sizeNorm p (graph f (ExecutableAdaptive.graphRep G))) := by
  obtain ⟨q,hq⟩:=work_body
  let C := q.comp (2*statePolynomial+2)
  let M : Polynomial ℕ := 2*X+1
  refine ⟨X*(C+14*M+34)+10+statePolynomial,?_⟩
  intro G inst f hf p
  let n:=sizeNorm p (graph f (ExecutableAdaptive.graphRep G))
  have hk : p.K ≤ n := (sizeNorm_fields p _).2.1
  have hw : weight (initial f p).1≤M.eval n := by
    simp only [initial,weight_replicate,show weight false=1 from rfl,M,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
    omega
  have hc : ∀ a∈(initial f p).1,∀ k<(initial f p).1.length,∀ s,History f p (k+1) s→
      bodyRealizer.cost (a,s)≤C.eval n := by
    intro a ha k hk s hs
    have hsz : stateSize s ≤ statePolynomial.eval n := history_size f p (k+1) s hs
    have hw:=weight_le_stateSize s
    have hb:=hq (a,s)
    have ha' : weight a=1 := by
      have he : a=false := (List.mem_replicate.mp ha).2
      rw [he];rfl
    simp only [weight_prod,ha'] at hb
    have hm : stateSize s+(1+1+weight s)≤(2*statePolynomial+2).eval n := by
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
      omega
    exact (Nat.le_add_right _ _).trans (hb.trans (by simpa only [C,Polynomial.eval_comp] using polynomial_eval_monotone q hm))
  have hh:=OnlineTree.fold_cost_bound body bodyRealizer.cost (initial f p).1 (initial f p).2
    (History f p) (C.eval n) (M.eval n)
    (by simpa only [initial,List.length_replicate] using history_initial f p) hw
    (fun a ha k hk s hs=>history_step f hf p k s hs) hc
  have hout : (sweep (initial f p)).worst weight≤ statePolynomial.eval n := by
    apply Experiment.worst_le _ _ _
    exact hh.2.mono (fun s hs=>(weight_le_stateSize s).trans (history_size f p 0 s hs))
  have hmul:=Nat.mul_le_mul_right (C.eval n+14*M.eval n+34) hk
  change OnlineTree.Fold.cost body bodyRealizer.cost (initial f p).1 (initial f p).2+_≤_
  have hlen : (initial f p).1.length=p.K := List.length_replicate
  rw [hlen] at hh
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  change _ ≤ n*(C.eval n+14*M.eval n+34)+10+statePolynomial.eval n
  omega
end MatchingFPRAS.OnlineTrial

end OAI
end

theorem solution : type_of% @OAI.MatchingFPRAS.OnlineTrial.sweep_bound_oai := @OAI.MatchingFPRAS.OnlineTrial.sweep_bound_oai
