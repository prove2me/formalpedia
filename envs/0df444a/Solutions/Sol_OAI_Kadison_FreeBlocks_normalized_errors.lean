-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.normalized_errors
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:56:17.588058+00:00
-- url     : https://prove2.me/submissions/e51cea9d-5356-438a-b1c0-53ef2e6c419f

import Mathlib
import Definitions.Def_OAIQ039C066

section
-- module Solutions.OAIQ039_CM.Commutator_FreeCreation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetry14
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

lemma sourceLevelEmbedding_orthogonal :
    OrthogonalFamily ℂ (fun n => sourceLevel t f hf S j n)
      (sourceLevelEmbedding t f hf S i j hS hfree hij) := by
  intro n m hnm x y
  exact levelEmbedding_orthogonal t S hfree hij hnm
    ((sourceLevelShuffle t f hf S i j hS n).symm x)
    ((sourceLevelShuffle t f hf S i j hS m).symm y)

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeNormalizedColumns
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace TensorProduct ComplexOrder

open UniformSpace

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {i j : ι} (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)
  (hS : S i=f.range) (hfree : Free S t.functional.toLinearMap) (hij : i≠j)

variable (d : D) (s : letterSpace t S j) (hs : ‖s‖=1)
  (x : letterSpace t S i) (hx : ‖x‖=1)

variable (hr : 0<‖TracialGNS.algebraVector (factorTrace t f hf) d‖)

lemma normalizedColumn_apply (n : ℕ) (v : multiplicityLevel t S j 0) :
    normalizedColumn t S f hf hS hfree hij d s hs x hx hr n v=
      ((‖TracialGNS.algebraVector (factorTrace t f hf) d‖⁻¹:ℝ):ℂ) •
        repeatedOutput t S f hf hS hfree hij d x n (repeatInsertion t S s hs n v) := rfl

lemma repeatedOutput_orthogonal {n m : ℕ} (hnm : n≠m)
    (v : multiplicityLevel t S j n) (z : multiplicityLevel t S j m) :
    inner ℂ (repeatedOutput t S f hf hS hfree hij d x n v)
      (repeatedOutput t S f hf hS hfree hij d x m z)=0 := by
  exact sourceLevelEmbedding_orthogonal t f hf S i j hS hfree hij hnm _ _

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)

variable (B : ∀ n, multiplicityLevel t S j n →L[ℂ] multiplicityLevel t S j n)

variable (hB : ∀ n d (x : letterSpace t S i) v,
  G (repeatedOutput t S f hf hS hfree hij d x n v)=
    repeatedOutput t S f hf hS hfree hij d x n (B n v))

include hB in
lemma normalizedColumn_error (n : ℕ) (v : multiplicityLevel t S j 0) :
    G (normalizedColumn t S f hf hS hfree hij d s hs x hx hr n v)-
      normalizedColumn t S f hf hS hfree hij d s hs x hx hr n (B 0 v)=
    ((‖TracialGNS.algebraVector (factorTrace t f hf) d‖⁻¹:ℝ):ℂ) •
      repeatedOutput t S f hf hS hfree hij d x n
        (B n (repeatInsertion t S s hs n v)-repeatInsertion t S s hs n (B 0 v)) := by
  simp only [normalizedColumn_apply t S f hf hS hfree hij d s hs x hx hr,map_smul,hB,map_sub,smul_sub]

include hB in
lemma normalizedColumn_error_norm (n : ℕ) (v : multiplicityLevel t S j 0) :
    ‖G (normalizedColumn t S f hf hS hfree hij d s hs x hx hr n v)-
      normalizedColumn t S f hf hS hfree hij d s hs x hx hr n (B 0 v)‖=
    ‖B n (repeatInsertion t S s hs n v)-repeatInsertion t S s hs n (B 0 v)‖ := by
  rw [normalizedColumn_error t S f hf hS hfree hij d s hs x hx hr G B hB,
    norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
    norm_repeatedOutput,hx,one_pow,mul_one,←mul_assoc,
    inv_mul_cancel₀ (ne_of_gt hr),one_mul]

include hB in
lemma normalizedColumn_error_orthogonal {n m : ℕ} (hnm : n≠m)
    (v z : multiplicityLevel t S j 0) :
    inner ℂ (G (normalizedColumn t S f hf hS hfree hij d s hs x hx hr n v)-
      normalizedColumn t S f hf hS hfree hij d s hs x hx hr n (B 0 v))
      (G (normalizedColumn t S f hf hS hfree hij d s hs x hx hr m z)-
      normalizedColumn t S f hf hS hfree hij d s hs x hx hr m (B 0 z))=0 := by
  simp only [normalizedColumn_error t S f hf hS hfree hij d s hs x hx hr G B hB,
    inner_smul_left,inner_smul_right,
    repeatedOutput_orthogonal t S f hf hS hfree hij d x hnm,mul_zero]

include hB in
lemma norm_normalizedColumn_error_le (δ : ℝ) (hδ : 0≤δ) (n : ℕ)
    (he : ∀ v, ‖B n (repeatInsertion t S s hs n v)-repeatInsertion t S s hs n (B 0 v)‖≤δ*‖v‖) :
    ‖G.comp (normalizedColumn t S f hf hS hfree hij d s hs x hx hr n).toContinuousLinearMap-
      (normalizedColumn t S f hf hS hfree hij d s hs x hx hr n).toContinuousLinearMap.comp (B 0)‖≤δ := by
  let T := G.comp (normalizedColumn t S f hf hS hfree hij d s hs x hx hr n).toContinuousLinearMap-
    (normalizedColumn t S f hf hS hfree hij d s hs x hx hr n).toContinuousLinearMap.comp (B 0)
  change sInf {r : ℝ | 0 ≤ r ∧ ∀ v, ‖T v‖ ≤ r*‖v‖}≤δ
  refine csInf_le ⟨0,fun r h => h.1⟩ ⟨hδ,?_⟩
  intro v
  change ‖G (normalizedColumn t S f hf hS hfree hij d s hs x hx hr n v)-
      normalizedColumn t S f hf hS hfree hij d s hs x hx hr n (B 0 v)‖≤_
  rw [normalizedColumn_error_norm t S f hf hS hfree hij d s hs x hx hr G B hB]
  exact he v

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeHankelBound
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open UniformSpace

open scoped ComplexOrder InnerProductSpace

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor DihedralCorner

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f) (hS : S false=f.range)

variable (htr : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (d s : unitary A) (hd : (d:A)∈S false) (hs : (s:A)∈S true)
  (hd0 : t.functional (d:A)=0) (hs0 : t.functional (s:A)=0)
  (hrot : MulAut.conj d (d*s)=(d*s)⁻¹)
  (hd2 : (d:A)*(d:A)=1) (hs2 : (s:A)*(s:A)=1)

variable {p : A} (hp : IsStarProjection p)
  (hpform : p=(1/2:ℂ) • (1+(d:A))) (hpd : p*(d:A)=p) (hdp : (d:A)*p=p)
  (hpD : p∈S false)
local notation "sl" => (letterOf t S true (s:A) hs hs0)
local notation "sn" => (norm_letterOf_unitary t S true s hs hs0)
local notation "dl" => (letterOf t S false (d:A) hd hd0)
local notation "dn" => (norm_letterOf_unitary t S false d hd hd0)

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)

variable (B : ∀ n, multiplicityLevel t S true n →L[ℂ] multiplicityLevel t S true n)

variable (hB : ∀ n a (x : letterSpace t S false) v,
  G (repeatedOutput t S f hf hS hfree Bool.false_ne_true a x n v)=
    repeatedOutput t S f hf hS hfree Bool.false_ne_true a x n (B n v))

variable (hB' : ∀ n a (x : letterSpace t S false) v,
  G.adjoint (repeatedOutput t S f hf hS hfree Bool.false_ne_true a x n v)=
    repeatedOutput t S f hf hS hfree Bool.false_ne_true a x n
      ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true n)
        (F:=multiplicityLevel t S true n) (B n)) v))

include hB hB' in
lemma normalized_errors_oai (e0 : D)
    (hr : 0<‖TracialGNS.algebraVector (factorTrace t f hf) e0‖)
    (N : ℕ) (δ : ℝ) (hδ : 0≤δ)
    (hprop : ∀ n v, ‖B n (repeatInsertion t S sl sn n v)-
      repeatInsertion t S sl sn n (B 0 v)‖≤δ*‖v‖)
    (hprop' : ∀ n v,
      ‖(ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true n)
        (F:=multiplicityLevel t S true n) (B n)) (repeatInsertion t S sl sn n v)-
      repeatInsertion t S sl sn n
        ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true 0)
          (F:=multiplicityLevel t S true 0) (B 0)) v)‖≤δ*‖v‖) :
    let E := Completion (factorSpace t S true)
    let U : Fin N → E →ₗᵢ[ℂ] t.functional.GNS := fun i =>
      normalizedColumn t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr i.val
    (∀ i : Fin N, ‖G.comp (U i).toContinuousLinearMap-
      (U i).toContinuousLinearMap.comp (B 0)‖≤δ) ∧
    (∀ i : Fin N, ‖G.adjoint.comp (U i).toContinuousLinearMap-
      (U i).toContinuousLinearMap.comp
        (ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=E) (F:=E) (B 0))‖≤δ) ∧
    (∀ i j : Fin N, i≠j → ∀ x : E,
      inner ℂ (G (U i x)-U i (B 0 x)) (G (U j x)-U j (B 0 x))=0) ∧
    (∀ i j : Fin N, i≠j → ∀ x : E,
      inner ℂ (G.adjoint (U i x)-U i ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=E) (F:=E) (B 0)) x))
        (G.adjoint (U j x)-U j ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=E) (F:=E) (B 0)) x))=0) := by
  dsimp only
  let E := Completion (factorSpace t S true)
  let U : Fin N → E →ₗᵢ[ℂ] t.functional.GNS := fun i =>
    normalizedColumn t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr i.val
  have hR : ∀ i : Fin N, ‖G.comp (U i).toContinuousLinearMap-
      (U i).toContinuousLinearMap.comp (B 0)‖≤δ := by
    intro i
    exact norm_normalizedColumn_error_le t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr
      G B hB _ hδ i.val (hprop i.val)
  have hR' : ∀ i : Fin N, ‖G.adjoint.comp (U i).toContinuousLinearMap-
      (U i).toContinuousLinearMap.comp
        (ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=E) (F:=E) (B 0))‖≤δ := by
    intro i
    exact norm_normalizedColumn_error_le t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr
      G.adjoint (fun n => ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true n)
        (F:=multiplicityLevel t S true n) (B n)) hB' _ hδ i.val (hprop' i.val)
  have hRorth : ∀ i j : Fin N, i≠j → ∀ x : E,
      inner ℂ (G (U i x)-U i (B 0 x)) (G (U j x)-U j (B 0 x))=0 := by
    intro i j hij x
    exact normalizedColumn_error_orthogonal t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr
      G B hB (mt Fin.ext hij) x x
  have hRorth' : ∀ i j : Fin N, i≠j → ∀ x : E,
      inner ℂ (G.adjoint (U i x)-U i ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=E) (F:=E) (B 0)) x))
        (G.adjoint (U j x)-U j ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=E) (F:=E) (B 0)) x))=0 := by
    intro i j hij x
    exact normalizedColumn_error_orthogonal t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr
      G.adjoint (fun n => ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true n)
        (F:=multiplicityLevel t S true n) (B n)) hB' (mt Fin.ext hij) x x
  exact ⟨hR,hR',hRorth,hRorth'⟩

end Kadison.FreeBlocks

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.FreeBlocks.normalized_errors_oai := @OAI.Kadison.FreeBlocks.normalized_errors_oai
