-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.base_intertwining
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:58:46.442984+00:00
-- url     : https://prove2.me/submissions/2dc653c1-6eba-4540-80b5-401b41aea332

import Mathlib
import Definitions.Def_OAIQ039C059

section
-- module Solutions.OAIQ039_CM.Commutator_TensorPowerCompletion
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

namespace Kadison.HilbertCompletion

open UniformSpace

open scoped TensorProduct

variable (E F : PreHilbert)

lemma powerEquiv_pure (U : Completion E ≃ₗᵢ[ℂ] Completion F)
    (n : ℕ) (v : Fin n → E) (w : Fin n → F)
    (h : ∀ i, U (v i : Completion E)=(w i : Completion F)) :
    powerEquiv E F U n (PreHilbert.pure E n v : Completion (PreHilbert.power E n)) =
      (PreHilbert.pure F n w : Completion (PreHilbert.power F n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (tensor (E := F) (F := PreHilbert.power F n)).symm
      (congr (TensorProduct.congrIsometry U (powerEquiv E F U n))
        (tensor (E := E) (F := PreHilbert.power E n)
          ((v 0 ⊗ₜ[ℂ] PreHilbert.pure E n (Fin.tail v)) :
            Completion (E ⊗[ℂ] PreHilbert.power E n)))) = _
    apply (tensor (E := F) (F := PreHilbert.power F n)).injective
    rw [LinearIsometryEquiv.apply_symm_apply, tensor_coe_tmul, congr_coe,
      TensorProduct.congrIsometry_apply, TensorProduct.congr_tmul]
    change ((U (v 0 : Completion E) ⊗ₜ[ℂ]
      powerEquiv E F U n (PreHilbert.pure E n (Fin.tail v) : Completion (PreHilbert.power E n))) :
      Completion (Completion F ⊗[ℂ] Completion (PreHilbert.power F n))) = _
    rw [h 0, ih (Fin.tail v) (Fin.tail w) (fun i => h i.succ)]
    exact (tensor_coe_tmul (w 0) (PreHilbert.pure F n (Fin.tail w))).symm

variable (E' F' : PreHilbert)

lemma wordEquiv_pure (U : Completion E ≃ₗᵢ[ℂ] Completion E')
    (V : Completion F ≃ₗᵢ[ℂ] Completion F') (n : ℕ)
    (a : E) (a' : E') (ha : U (a : Completion E)=(a' : Completion E'))
    (v : Fin n → F) (w : Fin n → F')
    (hv : ∀ i, V (v i : Completion F)=(w i : Completion F')) :
    wordEquiv E F E' F' U V n
      ((a ⊗ₜ[ℂ] PreHilbert.pure F n v) : Completion (E ⊗[ℂ] PreHilbert.power F n)) =
        ((a' ⊗ₜ[ℂ] PreHilbert.pure F' n w) : Completion (E' ⊗[ℂ] PreHilbert.power F' n)) := by
  change (tensor (E := E') (F := PreHilbert.power F' n)).symm
    (congr (TensorProduct.congrIsometry U (powerEquiv F F' V n))
      (tensor (E := E) (F := PreHilbert.power F n)
        ((a ⊗ₜ[ℂ] PreHilbert.pure F n v) : Completion (E ⊗[ℂ] PreHilbert.power F n)))) = _
  apply (tensor (E := E') (F := PreHilbert.power F' n)).injective
  rw [LinearIsometryEquiv.apply_symm_apply, tensor_coe_tmul, congr_coe,
    TensorProduct.congrIsometry_apply, TensorProduct.congr_tmul]
  change ((U (a : Completion E) ⊗ₜ[ℂ]
    powerEquiv F F' V n (PreHilbert.pure F n v : Completion (PreHilbert.power F n))) :
    Completion (Completion E' ⊗[ℂ] Completion (PreHilbert.power F' n))) = _
  rw [ha, powerEquiv_pure F F' V n v w hv]
  exact (tensor_coe_tmul a' (PreHilbert.pure F' n w)).symm

end Kadison.HilbertCompletion
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

lemma scalarGNSIso_pure (n : ℕ) (a : aLetters t S i) (x : Fin n → dLetters t S i) :
    scalarGNSIso t f hf S i hS n
      ((a ⊗ₜ[ℂ] PreHilbert.pure (dLetters t S i) n x) : scalarLevel t S i n) =
      PreHilbert.word (factorFull t f hf) (factorZero t f hf) n
        (factorGNSIso t f hf S i hS (HilbertCompletion.coeIsometry (aLetters t S i) a))
        (fun k => letterGNSIso t f hf S i hS (HilbertCompletion.coeIsometry (dLetters t S i) (x k))) := by
  have result := HilbertCompletion.wordEquiv_pure (aLetters t S i) (dLetters t S i)
    (factorFull t f hf) (factorZero t f hf)
    ((factorGNSIso t f hf S i hS).trans HilbertCompletion.completeEquiv)
    ((letterGNSIso t f hf S i hS).trans HilbertCompletion.completeEquiv)
    n a (factorGNSIso t f hf S i hS (HilbertCompletion.coeIsometry (aLetters t S i) a))
    rfl x (fun index => letterGNSIso t f hf S i hS
      (HilbertCompletion.coeIsometry (dLetters t S i) (x index))) (fun _ => rfl)
  dsimp only [scalarGNSIso, PreHilbert.word, factorFull, factorZero,
    TracialGNS.fullSpace, TracialGNS.zeroSpace, TracialGNS.vacuum, factorTrace,
    HilbertCompletion.centered, centeredSpace] at result ⊢
  exact result

lemma sourceLevelShuffle_word (n : ℕ) (a : aLetters t S i) (x : BlockParams t S i j n) :
    sourceLevelShuffle t f hf S i j hS n
      (HilbertCompletion.coeIsometry (endpointTensor t S i j n) (a ⊗ₜ[ℂ] blockPure t S n x)) =
      HilbertTensor.pair (E := sourceScalar t f hf n) (scalarGNSIso t f hf S i hS n
        ((a ⊗ₜ[ℂ] PreHilbert.pure (dLetters t S i) n (paramD t S n x)) : scalarLevel t S i n))
        (paramJ t S n x : multiplicityLevel t S j n) := by
  change HilbertCompletion.congr _ (levelShuffle t S n
    (HilbertCompletion.coeIsometry (endpointTensor t S i j n) (a ⊗ₜ[ℂ] blockPure t S n x))) = _
  rw [levelShuffle_pure t S n a x, HilbertCompletion.congr_coe]
  rfl

lemma sourceLevelShuffle_pure (n : ℕ) (a : aLetters t S i) (x : BlockParams t S i j n) :
    sourceLevelShuffle t f hf S i j hS n
      (HilbertCompletion.coeIsometry (endpointTensor t S i j n) (a ⊗ₜ[ℂ] blockPure t S n x)) =
      HilbertTensor.pair (E := sourceScalar t f hf n)
        (PreHilbert.word (factorFull t f hf) (factorZero t f hf) n
          (factorGNSIso t f hf S i hS (HilbertCompletion.coeIsometry (aLetters t S i) a))
          (fun k => letterGNSIso t f hf S i hS
            (HilbertCompletion.coeIsometry (dLetters t S i) (paramD t S n x k))))
        (paramJ t S n x : multiplicityLevel t S j n) := by
  rw [sourceLevelShuffle_word]
  exact congrArg (fun b : sourceScalar t f hf n =>
    HilbertTensor.pair b (paramJ t S n x : multiplicityLevel t S j n))
    (scalarGNSIso_pure t f hf S i hS n a (fun k => (paramD t S n x k : dLetters t S i)))

variable (hfree : FreeMoments.Free S t.functional.toLinearMap) (hij : i≠j)

lemma sourceLevelEmbedding_shuffle (n : ℕ) (x : Completion (endpointTensor t S i j n)) :
    sourceLevelEmbedding t f hf S i j hS hfree hij n
      (sourceLevelShuffle t f hf S i j hS n x) = levelEmbedding t S hfree hij n x := by
  simp [sourceLevelEmbedding]

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeCovariance
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
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap
open scoped InnerProductSpace ENNReal
open scoped ComplexOrder InnerProductSpace TensorProduct
open UniformSpace ContinuousLinearMap

namespace Kadison.FreeBlocks

open FreeWordTensor UniformSpace PreHilbert

open scoped ComplexOrder InnerProductSpace TensorProduct

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

lemma sourceLevelShuffle_bounded (d : D) (n : ℕ) (x : BlockParams t S i j n) :
    sourceLevelShuffle t f hf S i j hS n
      (HilbertCompletion.coeIsometry (endpointTensor t S i j n)
        (factorBounded t f hf S i hS d ⊗ₜ[ℂ] blockPure t S n x)) =
      levelWord t f hf S i j hS d n x := by
  have result := sourceLevelShuffle_pure t f hf S i j hS n (factorBounded t f hf S i hS d) x
  rw [factorBounded_GNS] at result
  dsimp only [levelWord, sourceScalar, factorFull, factorZero, TracialGNS.fullSpace,
    TracialGNS.zeroSpace, TracialGNS.vacuum, factorTrace, HilbertCompletion.centered,
    centeredSpace] at result ⊢
  exact result

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable (hfree : FreeMoments.Free S t.functional.toLinearMap) (hij : i≠j)

lemma sourceLevelEmbedding_word (d : D) (n : ℕ) (x : BlockParams t S i j n) :
    sourceLevelEmbedding t f hf S i j hS hfree hij n (levelWord t f hf S i j hS d n x) =
      t.functional.gnsStarAlgHom (f d)
        (blockReadPre t S n (blockPure t S n x) : t.functional.GNS) := by
  rw [←sourceLevelShuffle_bounded,sourceLevelEmbedding_shuffle]
  exact (levelEmbedding_coe t S hfree hij n
    (factorBounded t f hf S i hS d ⊗ₜ[ℂ] blockPure t S n x)).trans
      (endpointRead_tmul t S n (factorBounded t f hf S i hS d) (blockPure t S n x))

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeRepeatedWords
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

variable {i j : ι}

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap) (hij : i≠j)

lemma repeatedOutput_bounded (d : D) (s : letterSpace t S j) (hs : ‖s‖=1)
    (x : letterSpace t S i) (n : ℕ) (v : factorSpace t S j) :
    repeatedOutput t S f hf hS hfree hij d x n
      (repeatInsertion t S s hs n (v : multiplicityLevel t S j 0))=
      t.functional.gnsStarAlgHom (f d)
        (t.functional.gnsStarAlgHom ((letterValue t S j s*letterValue t S i x)^n)
          (blockEmbedding t S hfree hij 0 (v : multiplicityLevel t S j 0))) := by
  have hn : repeatedOutput t S f hf hS hfree hij d x n
      (repeatInsertion t S s hs n (v : multiplicityLevel t S j 0))=
      sourceLevelEmbedding t f hf S i j hS hfree hij n
        (levelWord t f hf S i j hS d n (repeatedParams t S s x v n)) := by
    rw [repeatInsertion_coe]
    simp only [repeatedOutput,tensorOutput,ContinuousLinearMap.comp_apply,HilbertTensor.insertLeft_apply,
      levelWord,repeatedParams_D,repeatedParams_J]
    rfl
  rw [hn,sourceLevelEmbedding_word]
  congr 1
  change (t.functional.toPreGNS
    (blockRead t S n (blockPure t S n (repeatedParams t S s x v n))) : t.functional.GNS)=_
  rw [blockRead_repeated]
  have hv : blockEmbedding t S hfree hij 0 (v : multiplicityLevel t S j 0)=
      (t.functional.toPreGNS (factorValue t S j v) : t.functional.GNS) := by
    simp [blockEmbedding,blockIsometry,blockReadPre,blockRead]
  rw [hv]
  simp [PositiveLinearMap.gnsStarAlgHom]

lemma repeatedOutput_inserted (d : D) (s : letterSpace t S j) (hs : ‖s‖=1)
    (x : letterSpace t S i) (n : ℕ) (v : multiplicityLevel t S j 0) :
    repeatedOutput t S f hf hS hfree hij d x n
      (repeatInsertion t S s hs n v)=t.functional.gnsStarAlgHom (f d)
        (t.functional.gnsStarAlgHom ((letterValue t S j s*letterValue t S i x)^n)
          (blockEmbedding t S hfree hij 0 v)) := by
  induction v using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih v => exact repeatedOutput_bounded t S f hf hS hfree hij d s hs x n v

lemma repeatedOutput_zero (s : letterSpace t S j) (hs : ‖s‖=1)
    (x : letterSpace t S i) (d : D) (v : multiplicityLevel t S j 0) :
    repeatedOutput t S f hf hS hfree hij d x 0 v=
      t.functional.gnsStarAlgHom (f d) (blockEmbedding t S hfree hij 0 v) := by
  have hr : repeatInsertion t S s hs 0 v=v := by
    induction v using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih v => rw [repeatInsertion_coe]; rfl
  simpa [hr] using
    repeatedOutput_inserted t S f hf hS hfree hij d s hs x 0 v

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)

variable (B : ∀ n, multiplicityLevel t S j n →L[ℂ] multiplicityLevel t S j n)

variable (hB : ∀ n d (x : letterSpace t S i) v,
  G (repeatedOutput t S f hf hS hfree hij d x n v)=
    repeatedOutput t S f hf hS hfree hij d x n (B n v))

include hB in
lemma base_intertwining_oai (s : letterSpace t S j) (hs : ‖s‖=1)
    (x : letterSpace t S i) (d : D) (v : multiplicityLevel t S j 0) :
    G (t.functional.gnsStarAlgHom (f d) (blockEmbedding t S hfree hij 0 v))=
      t.functional.gnsStarAlgHom (f d) (blockEmbedding t S hfree hij 0 (B 0 v)) := by
  simpa only [repeatedOutput_zero t S f hf hS hfree hij s hs x] using hB 0 d x v

end Kadison.FreeBlocks

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.FreeBlocks.base_intertwining_oai.{u_1} := @OAI.Kadison.FreeBlocks.base_intertwining_oai.{u_1}
