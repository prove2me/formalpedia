-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.sourceLevelIsHilbertSum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:36:17.534993+00:00
-- url     : https://prove2.me/submissions/4d139529-44da-42d4-b58a-144642cca25e

import Mathlib
import Definitions.Def_OAIQ039C056

section
-- module Solutions.OAIQ039_CM.Commutator_FreeCreation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology

namespace Kadison.FreeCreation

open FreeMoments FreeWordTensor

open scoped InnerProductSpace

open UniformSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap)

include hfree in
lemma headSpace_le_tailSpace_orthogonal (i : ι) :
    headSpace t S i ≤ (tailSpace t S i)ᗮ := by
  apply (headSpan t S i).topologicalClosure_minimal ?_ (Submodule.isClosed_orthogonal _)
  rw [tailSpace, Submodule.orthogonal_closure]
  apply Submodule.span_le.mpr
  rintro x ⟨z, hz, ⟨a, z, rfl, ha⟩, rfl⟩
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, hiw, rfl⟩ := hy
    rw [inner_wordVector]
    change t.functional.toLinearMap (star (word w) * word (a :: z)) = 0
    rw [gram_word (fun a => map_star t.functional a) t.normalized hfree _ _ hw hz]
    exact gram_zero_of_colors_ne _ _ (colors_ne_prepend t S hiw a ha)
  | zero => simp
  | add y z _ _ hy hz => simp [inner_add_left, hy, hz]
  | smul c y _ hy => simp [inner_smul_left, hy]

end Kadison.FreeCreation
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeBlockWords2
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeCreation UniformSpace

open scoped InnerProductSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap) {i j : ι} (hij : i ≠ j)

include hfree hij in
lemma blockVector_cons_nil (x : Letters t S i j)
    (xs : List (Letters t S i j)) {z v : A} (hz : z ∈ S j) (hv : v ∈ S j) :
    inner ℂ (blockVector t S (x::xs) z) (blockVector t S ([] : List (Letters t S i j)) v) = 0 := by
  rw [blockVector_cons, ← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ _ ((star (t.functional.gnsStarAlgHom (letterValue t S j x.1))) _) = 0
  rw [← map_star]
  have hm : t.functional.gnsStarAlgHom (star (letterValue t S j x.1))
      (blockVector t S ([] : List (Letters t S i j)) v) =
      (t.functional.toPreGNS (star (letterValue t S j x.1)*v) : t.functional.GNS) := by
    simp [blockVector_nil, PositiveLinearMap.gnsStarAlgHom]
  rw [hm]
  have ht := factor_vector_mem_tailSpace t S hij (mul_mem (star_mem x.1.property.1) hv)
  have hh := headSpace_le_tailSpace_orthogonal t S hfree i
    (creation_mem_headSpace t S i (a := letterValue t S i x.2) x.2.property.1 x.2.property.2
      (blockVector_mem_tail t S hij xs hz))
  exact inner_eq_zero_symm.mp (hh _ ht)

include hfree hij in
lemma blockVector_orthogonal (xs ys : List (Letters t S i j))
    (hlen : xs.length ≠ ys.length) {z v : A} (hz : z ∈ S j) (hv : v ∈ S j) :
    inner ℂ (blockVector t S xs z) (blockVector t S ys v) = 0 := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact (hlen rfl).elim
    | cons y ys => exact inner_eq_zero_symm.mp (blockVector_cons_nil t S hfree hij y ys hv hz)
  | cons x xs ih =>
    cases ys with
    | nil => exact blockVector_cons_nil t S hfree hij x xs hz hv
    | cons y ys =>
      rw [blockVector_cons_gram t S hfree hij x y xs ys hz hv,
        ih ys (by simpa using hlen), mul_zero]

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeBlockTensor2
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeCreation UniformSpace

open scoped InnerProductSpace TensorProduct

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap) {i j : ι} (hij : i≠j)

include hfree hij in
lemma inner_blockReadPre_ne {n m : ℕ} (hnm : n≠m)
    (x : blockTensor t S i j n) (y : blockTensor t S i j m) :
    inner ℂ (blockReadPre t S n x) (blockReadPre t S m y)=0 := by
  have hx : x ∈ Submodule.span ℂ (Set.range (blockPure t S (i := i) (j := j) n)) := by rw [span_blockPure]; trivial
  have hy : y ∈ Submodule.span ℂ (Set.range (blockPure t S (i := i) (j := j) m)) := by rw [span_blockPure]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w,rfl⟩ := hy
      rw [←Completion.inner_coe, blockReadPre_pure, blockReadPre_pure]
      exact blockVector_orthogonal t S hfree hij _ _
        (by simpa only [paramLetters_length] using hnm)
        (paramEnd t S n v).property (paramEnd t S m w).property
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, inner_add_right, hx, hy, add_zero]
    | smul c y _ hy => simp only [map_smul, inner_smul_right, hy, mul_zero]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, inner_add_left, hx, hy, add_zero]
  | smul c x _ hx => simp only [map_smul, inner_smul_left, hx, mul_zero]

include hfree hij in
lemma inner_endpointRead_ne {n m : ℕ} (hnm : n≠m)
    (x : endpointTensor t S i j n) (y : endpointTensor t S i j m) :
    inner ℂ (endpointRead t S n x) (endpointRead t S m y)=0 := by
  induction x using endpointTensor_induction_on t S n with
  | h0 => simp
  | ha x z hx hz => simp only [map_add, inner_add_left, hx, hz, add_zero]
  | ht a x =>
    induction y using endpointTensor_induction_on t S m with
    | h0 => simp
    | ha y z hy hz => simp only [map_add, inner_add_right, hy, hz, add_zero]
    | ht b y =>
      rw [←Completion.inner_coe, endpointRead_tmul, endpointRead_tmul,
        inner_mul_two_tailSpace t S hfree i (a := factorValue t S i a)
          (b := factorValue t S i b) a.property b.property
          (blockReadPre_mem_tail t S hij n x) (blockReadPre_mem_tail t S hij m y),
        Completion.inner_coe, inner_blockReadPre_ne t S hfree hij hnm, mul_zero]

lemma levelEmbedding_orthogonal {n m : ℕ} (hnm : n≠m)
    (x : Completion (endpointTensor t S i j n)) (y : Completion (endpointTensor t S i j m)) :
    inner ℂ (levelEmbedding t S hfree hij n x) (levelEmbedding t S hfree hij m y) = 0 := by
  induction x, y using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    rw [levelEmbedding_coe, levelEmbedding_coe, Completion.inner_coe]
    exact inner_endpointRead_ne t S hfree hij hnm x y

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeBlockTensor3
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeCreation UniformSpace

open scoped InnerProductSpace TensorProduct

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {i j : ι} (hcolors : ∀ c : ι, c=i ∨ c=j)

include hcolors in
lemma tail_word_as_block (w : List (Letter t S)) (hw : Reduced w)
    (hiw : CanPrepend t S i w) :
    ∃ (n : ℕ) (p : BlockParams t S i j n), word w = blockRead t S n (blockPure t S n p) := by
  induction w using List.twoStepInduction with
  | nil =>
    refine ⟨0, factorOf t S j 1 (one_mem _), ?_⟩
    exact (factorValue_factorOf t S j 1 (one_mem _)).symm
  | singleton a =>
    have hai : i≠a.color := by simpa [CanPrepend] using hiw
    have haj : a.color=j := (hcolors a.color).resolve_left (Ne.symm hai)
    refine ⟨0, factorOf t S j a.val (haj ▸ a.mem), ?_⟩
    simp only [word_cons, word_nil, mul_one, blockRead, blockPure, factorValue_factorOf]
  | cons_cons a b w ih =>
    have hai : i≠a.color := by simpa [CanPrepend] using hiw
    have haj : a.color=j := (hcolors a.color).resolve_left (Ne.symm hai)
    have hbi : b.color=i := (hcolors b.color).resolve_right (by
      intro hbj; exact hw.rel (haj.trans hbj.symm))
    have hiw' : CanPrepend t S i w := by
      cases w with
      | nil => simp [CanPrepend]
      | cons c w => simpa [CanPrepend, hbi] using hw.tail.rel
    obtain ⟨n,p,hp⟩ := ih hw.tail.tail hiw'
    let aa := letterOf t S j a.val (haj ▸ a.mem) a.centered
    let bb := letterOf t S i b.val (hbi ▸ b.mem) b.centered
    refine ⟨n+1, ((aa,bb),p), ?_⟩
    change a.val*(b.val*word w) = letterValue t S j aa *
      (letterValue t S i bb * blockRead t S n (blockPure t S n p))
    simp only [aa, bb, letterValue_letterOf, hp]

include hcolors in
lemma word_as_endpoint (w : List (Letter t S)) (hw : Reduced w) :
    ∃ (n : ℕ) (x : endpointTensor t S i j n),
      (t.functional.toPreGNS (word w))=endpointRead t S n x := by
  classical
  by_cases hiw : CanPrepend t S i w
  · obtain ⟨n,p,hp⟩ := tail_word_as_block t S hcolors w hw hiw
    refine ⟨n, factorOf t S i 1 (one_mem _) ⊗ₜ[ℂ] blockPure t S n p, ?_⟩
    change t.functional.toPreGNS (word w) = t.functional.toPreGNS
      (factorValue t S i (factorOf t S i 1 (one_mem _))*blockRead t S n (blockPure t S n p))
    rw [factorValue_factorOf, one_mul, hp]
  · cases w with
    | nil => exact False.elim (hiw (by simp [CanPrepend]))
    | cons a w =>
      have hai : a.color=i := by simpa [CanPrepend] using (show i=a.color by simpa [CanPrepend] using hiw).symm
      have hiw' : CanPrepend t S i w := by
        cases w with
        | nil => simp [CanPrepend]
        | cons b w => simpa [CanPrepend, hai] using hw.rel
      obtain ⟨n,p,hp⟩ := tail_word_as_block t S hcolors w hw.tail hiw'
      refine ⟨n, factorOf t S i a.val (hai ▸ a.mem) ⊗ₜ[ℂ] blockPure t S n p, ?_⟩
      change t.functional.toPreGNS (a.val*word w) = t.functional.toPreGNS
        (factorValue t S i (factorOf t S i a.val (hai ▸ a.mem))*blockRead t S n (blockPure t S n p))
      rw [factorValue_factorOf, hp]

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeBlockTensor4
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeCreation UniformSpace

open scoped InnerProductSpace TensorProduct

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap) {i j : ι} (hij : i≠j)

variable (hcolors : ∀ c : ι, c=i ∨ c=j)

include hcolors

lemma wordVector_mem_levels (w : List (Letter t S)) (hw : Reduced w) :
    wordVector t S w ∈ ⨆ n, LinearMap.range (levelEmbedding t S hfree hij n).toLinearMap := by
  obtain ⟨n,x,hx⟩ := word_as_endpoint t S hcolors w hw
  apply Submodule.mem_iSup_of_mem n
  refine ⟨(x : Completion (endpointTensor t S i j n)), ?_⟩
  rw [LinearIsometry.coe_toLinearMap, levelEmbedding_coe]
  exact congrArg (fun x : preSpace t => (x : t.functional.GNS)) hx.symm

lemma generated_mem_levels {a : A} (ha : a ∈ iSup S) :
    (t.functional.toPreGNS a : t.functional.GNS) ∈
      ⨆ n, LinearMap.range (levelEmbedding t S hfree hij n).toLinearMap := by
  have ha' : a ∈ FreeMoments.wordSpan S t.functional.toLinearMap := by
    change a ∈ (FreeMoments.reducedAlgebra S (fun a => map_star t.functional a) t.normalized)
    rw [FreeMoments.reducedAlgebra_eq_iSup]
    exact ha
  clear ha
  induction ha' using Submodule.span_induction with
  | mem a ha => obtain ⟨w,hw,rfl⟩ := ha; exact wordVector_mem_levels t S hfree hij hcolors w hw
  | zero => simp only [map_zero, Completion.coe_zero, Submodule.zero_mem]
  | add a b _ _ ha hb => simpa only [map_add, Completion.coe_add] using
      (⨆ n, LinearMap.range (levelEmbedding t S hfree hij n).toLinearMap).add_mem ha hb
  | smul c a _ ha => simpa only [map_smul, Completion.coe_smul] using
      (⨆ n, LinearMap.range (levelEmbedding t S hfree hij n).toLinearMap).smul_mem c ha

lemma total_levels
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _))) :
    (⨆ n, LinearMap.range (levelEmbedding t S hfree hij n).toLinearMap).topologicalClosure=⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  induction x using Completion.induction_on with
  | hp => exact (⨆ n, LinearMap.range
      (levelEmbedding t S hfree hij n).toLinearMap).isClosed_topologicalClosure
  | ih x =>
    let ξ : t.functional.GNS := (t.functional.toPreGNS 1 : t.functional.GNS)
    have h := Kadison.bicommutant_mem_cyclicSubspace (generatedOperators t S)
      (hgen (t.functional.ofPreGNS x)) ξ
    have heq : t.functional.gnsStarAlgHom (t.functional.ofPreGNS x) ξ =
        (x : t.functional.GNS) := by
      simp [ξ, PositiveLinearMap.gnsStarAlgHom]
    rw [heq] at h
    apply Submodule.topologicalClosure_mono ?_ h
    rintro y ⟨a,ha,rfl⟩
    obtain ⟨b,hb,rfl⟩ := ha
    simpa [ξ, PositiveLinearMap.gnsStarAlgHom] using generated_mem_levels t S hfree hij hcolors hb

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetry14
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace

namespace Kadison.FreeBlocks

open FreeWordTensor UniformSpace PreHilbert

open scoped ComplexOrder InnerProductSpace TensorProduct

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

variable (hfree : FreeMoments.Free S t.functional.toLinearMap) (hij : i≠j)

lemma sourceLevelEmbedding_shuffle (n : ℕ) (x : Completion (endpointTensor t S i j n)) :
    sourceLevelEmbedding t f hf S i j hS hfree hij n
      (sourceLevelShuffle t f hf S i j hS n x) = levelEmbedding t S hfree hij n x := by
  simp [sourceLevelEmbedding]

lemma sourceLevelEmbedding_range (n : ℕ) :
    LinearMap.range (sourceLevelEmbedding t f hf S i j hS hfree hij n).toLinearMap =
      LinearMap.range (levelEmbedding t S hfree hij n).toLinearMap := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨(sourceLevelShuffle t f hf S i j hS n).symm x,rfl⟩
  · rintro ⟨x,rfl⟩
    exact ⟨sourceLevelShuffle t f hf S i j hS n x,
      sourceLevelEmbedding_shuffle t f hf S i j hS hfree hij n x⟩

lemma sourceLevelEmbedding_orthogonal :
    OrthogonalFamily ℂ (fun n => sourceLevel t f hf S j n)
      (sourceLevelEmbedding t f hf S i j hS hfree hij) := by
  intro n m hnm x y
  exact levelEmbedding_orthogonal t S hfree hij hnm
    ((sourceLevelShuffle t f hf S i j hS n).symm x)
    ((sourceLevelShuffle t f hf S i j hS m).symm y)

variable (hcolors : ∀ c : ι, c=i ∨ c=j)

variable (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
  Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

include hcolors hgen in
lemma sourceLevelIsHilbertSum_oai : IsHilbertSum ℂ (sourceLevel t f hf S j)
    (sourceLevelEmbedding t f hf S i j hS hfree hij) := by
  apply IsHilbertSum.mk (sourceLevelEmbedding_orthogonal t f hf S i j hS hfree hij)
  have hr : (⨆ n, LinearMap.range (sourceLevelEmbedding t f hf S i j hS hfree hij n).toLinearMap) =
      ⨆ n, LinearMap.range (levelEmbedding t S hfree hij n).toLinearMap := by
    congr 1
    funext n
    exact sourceLevelEmbedding_range t f hf S i j hS hfree hij n
  rw [hr]
  exact le_of_eq (total_levels t S hfree hij hcolors hgen).symm

end Kadison.FreeBlocks
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.FreeBlocks.sourceLevelIsHilbertSum_oai.{u_1} := @OAI.Kadison.FreeBlocks.sourceLevelIsHilbertSum_oai.{u_1}
