-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.free_word_structure
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:55:54.60909+00:00
-- url     : https://prove2.me/submissions/64f22328-3132-43f5-b33b-64864430ac55

import Mathlib
import Definitions.Def_OAIQ039C059
import Definitions.Def_OAIQ039C069
import Theorems.Thm_OAI_Kadison_FreeBlocks_innerRepresentation_word
import Theorems.Thm_OAI_Kadison_FreeBlocks_sourceLevelIsHilbertSum
import Theorems.Thm_OAI_Kadison_FreeBlocks_sumConjugation_levelWord
import Theorems.Thm_OAI_Kadison_TracialGNS_actual_word_structure

section
-- module Solutions.OAIQ039_CM.Commutator_TensorPowerCompletion
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.TracialGNS.sumLevelComplete _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.TracialGNS.sumLevelComplete _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.TracialGNS.sumLevelComplete _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

lemma factorBounded_surjective : Function.Surjective (factorBounded t f hf S i hS) := by
  intro a
  obtain ⟨v,hv⟩ := factorPreMap_surjective t f hf S i hS a
  refine ⟨(pullbackState t f hf).functional.ofPreGNS v,?_⟩
  simpa only [factorBounded,PositiveLinearMap.toPreGNS_ofPreGNS] using hv

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

lemma endpointCoordinate_pure (d : D) (n : ℕ) (x : BlockParams t S i j n) :
    endpointCoordinate t f hf S i j hS n
      (factorBounded t f hf S i hS d ⊗ₜ[ℂ] blockPure t S n x) =
      levelWord t f hf S i j hS d n x :=
  sourceLevelShuffle_bounded t f hf S i j hS d n x

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma sourceLevel_ext (n : ℕ) (F G : sourceLevel t f hf S j n →L[ℂ] E)
    (h : ∀ d x, F (levelWord t f hf S i j hS d n x)=G (levelWord t f hf S i j hS d n x)) :
    F=G := by
  ext v
  obtain ⟨v,rfl⟩ := (sourceLevelShuffle t f hf S i j hS n).surjective v
  change F (sourceLevelShuffle t f hf S i j hS n v)=G (sourceLevelShuffle t f hf S i j hS n v)
  induction v using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih v =>
    change F (endpointCoordinate t f hf S i j hS n v)=G (endpointCoordinate t f hf S i j hS n v)
    induction v using endpointTensor_induction_on t S n with
    | h0 => simp
    | ha v w hv hw => simpa only [map_add] using congrArg₂ (·+·) hv hw
    | ht a b =>
      obtain ⟨d,rfl⟩ := factorBounded_surjective t f hf S i hS a
      let Q : blockTensor t S i j n →ₗ[ℂ] endpointTensor t S i j n :=
        TensorProduct.mk ℂ (factorSpace t S i) (blockTensor t S i j n)
          (factorBounded t f hf S i hS d)
      let K : blockTensor t S i j n →ₗ[ℂ] E :=
        ((F.toLinearMap-G.toLinearMap).comp (endpointCoordinate t f hf S i j hS n)).comp Q
      have hker : Submodule.span ℂ (Set.range (blockPure t S (i:=i) (j:=j) n)) ≤ K.ker := by
        apply Submodule.span_le.mpr
        rintro _ ⟨x,rfl⟩
        change F (endpointCoordinate t f hf S i j hS n
          (factorBounded t f hf S i hS d ⊗ₜ[ℂ] blockPure t S n x)) -
          G (endpointCoordinate t f hf S i j hS n
            (factorBounded t f hf S i hS d ⊗ₜ[ℂ] blockPure t S n x))=0
        exact sub_eq_zero.mpr ((congrArg F (endpointCoordinate_pure t f hf S i j hS d n x)).trans
          ((h d x).trans (congrArg G (endpointCoordinate_pure t f hf S i j hS d n x)).symm))
      have hb : b∈Submodule.span ℂ (Set.range (blockPure t S (i:=i) (j:=j) n)) := by
        rw [span_blockPure]; trivial
      exact sub_eq_zero.mp (hker hb)

variable (hfree : FreeMoments.Free S t.functional.toLinearMap) (hij : i≠j)

lemma sourceLevelEmbedding_word (d : D) (n : ℕ) (x : BlockParams t S i j n) :
    sourceLevelEmbedding t f hf S i j hS hfree hij n (levelWord t f hf S i j hS d n x) =
      t.functional.gnsStarAlgHom (f d)
        (blockReadPre t S n (blockPure t S n x) : t.functional.GNS) := by
  rw [←sourceLevelShuffle_bounded,sourceLevelEmbedding_shuffle]
  exact (levelEmbedding_coe t S hfree hij n
    (factorBounded t f hf S i hS d ⊗ₜ[ℂ] blockPure t S n x)).trans
      (endpointRead_tmul t S n (factorBounded t f hf S i hS d) (blockPure t S n x))

lemma sourceLeft_word (a d : D) (n : ℕ) (x : BlockParams t S i j n) :
    sourceLeft t f hf S j a n (levelWord t f hf S i j hS d n x)=
      levelWord t f hf S i j hS (a*d) n x := by
  simp only [sourceLeft, levelWord, PreHilbert.word, HilbertTensor.map_pair,
    HilbertTensor.map_coe_tmul, one_apply_eq_self, TracialGNS.algebraVector_apply,
    TracialGNS.left_coe]

lemma sourceLevelEmbedding_left (a : D) (n : ℕ) :
    (sourceLevelEmbedding t f hf S i j hS hfree hij n).toContinuousLinearMap.comp
        (sourceLeft t f hf S j a n) =
      (t.functional.gnsStarAlgHom (f a)).comp
        (sourceLevelEmbedding t f hf S i j hS hfree hij n).toContinuousLinearMap := by
  apply sourceLevel_ext t f hf S i j hS
  intro d x
  simp only [ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,
    sourceLeft_word,sourceLevelEmbedding_word,map_mul]
  rfl

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeActualCovariance
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

variable (hij : i≠j)

lemma innerRepresentation_level (u : unitary D) (n : ℕ) :
    (innerRepresentation t ht f S i hS hfree hgen u).toLinearIsometry.toContinuousLinearMap.comp
      (sourceLevelEmbedding t f hf S i j hS hfree hij n).toContinuousLinearMap =
    (sourceLevelEmbedding t f hf S i j hS hfree hij n).toContinuousLinearMap.comp
      (sourceConjugation t ht f hf S j u n) := by
  apply sourceLevel_ext t f hf S i j hS
  intro d x
  change innerRepresentation t ht f S i hS hfree hgen u
      (sourceLevelEmbedding t f hf S i j hS hfree hij n
        (levelWord t f hf S i j hS d n x)) =
    sourceLevelEmbedding t f hf S i j hS hfree hij n
      (sourceConjugation t ht f hf S j u n (levelWord t f hf S i j hS d n x))
  exact (innerRepresentation_word t ht f hf S i j hS hfree hgen hij u d n x).trans
    (congrArg (sourceLevelEmbedding t f hf S i j hS hfree hij n)
      (sumConjugation_levelWord t ht f hf S i j hS u d n x).symm)

end Kadison.FreeBlocks

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeActualStructure
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

variable (hij : i≠j) (hcolors : ∀ c : ι, c=i ∨ c=j)

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]

variable (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)

variable (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)

variable (he : ∀ n m (h : n ≤ m) a, φ m (e h a)=φ n a)

variable (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))

variable (hDgen : ∀ a : D, (factorTrace t f hf).gnsStarAlgHom a ∈
  Set.centralizer (Set.centralizer
    (TracialGNS.stageAlgebra (factorTrace t f hf) I φ : Set _)))

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)

variable (hGL : ∀ a : D, G.comp (t.functional.gnsStarAlgHom (f a))=
  (t.functional.gnsStarAlgHom (f a)).comp G)

variable (hGW : ∀ n u, G.comp
  (innerRepresentation t ht f S i hS hfree hgen (TracialGNS.stageUnitary (φ n) u)).toLinearIsometry.toContinuousLinearMap =
  (innerRepresentation t ht f S i hS hfree hgen (TracialGNS.stageUnitary (φ n) u)).toLinearIsometry.toContinuousLinearMap.comp G)

private theorem faithfulWordActions_eq (state : FaithfulState D)
    (tracial : ∀ first second : D, state.functional (first * second) =
      state.functional (second * first)) :
    faithfulWordActions state tracial = tracialWordActions state.functional tracial := by
  rfl

include he hsize in
private theorem tracial_word_structure (functional : D →ₚ[ℂ] ℂ)
    (tracial : ∀ first second : D, functional (first * second) =
      functional (second * first)) (normalized : functional 1 = 1)
    (generation : ∀ element : D, functional.gnsStarAlgHom element ∈
      Set.centralizer (Set.centralizer (TracialGNS.stageAlgebra functional I φ : Set _)))
    (multiplicity : ℕ → Type*) [∀ level, NormedAddCommGroup (multiplicity level)]
    [∀ level, InnerProductSpace ℂ (multiplicity level)]
    [∀ level, CompleteSpace (multiplicity level)]
    (ambient : Type*) [NormedAddCommGroup ambient] [InnerProductSpace ℂ ambient] [CompleteSpace ambient] :
    wordStructureRule I φ (tracialWordActions functional tracial) multiplicity ambient := by
  intro embedding total left symmetries operator left_covariant symmetries_covariant
    commutes_left commutes_symmetries
  exact TracialGNS.actual_word_structure functional tracial normalized multiplicity embedding total
    I φ e he hsize generation left symmetries left_covariant symmetries_covariant operator
    commutes_left commutes_symmetries

include he hsize in
private theorem faithful_word_structure (state : FaithfulState D)
    (tracial : ∀ first second : D, state.functional (first * second) =
      state.functional (second * first))
    (generation : ∀ element : D, state.functional.gnsStarAlgHom element ∈
      Set.centralizer (Set.centralizer
        (TracialGNS.stageAlgebra state.functional I φ : Set _)))
    (multiplicity : ℕ → Type*) [∀ level, NormedAddCommGroup (multiplicity level)]
    [∀ level, InnerProductSpace ℂ (multiplicity level)]
    [∀ level, CompleteSpace (multiplicity level)]
    (ambient : Type*) [NormedAddCommGroup ambient] [InnerProductSpace ℂ ambient] [CompleteSpace ambient] :
    wordStructureRule I φ (faithfulWordActions state tracial) multiplicity ambient := by
  rw [faithfulWordActions_eq]
  exact tracial_word_structure I φ e he hsize state.functional tracial state.normalized generation
    multiplicity ambient

private lemma faithful_left_level (a : D) (n : ℕ) :
    (t.functional.gnsStarAlgHom (f a)).comp
      (sourceLevelEmbedding t f hf S i j hS hfree hij n).toContinuousLinearMap =
    (sourceLevelEmbedding t f hf S i j hS hfree hij n).toContinuousLinearMap.comp
      (wordLeftAction (faithfulWordActions (pullbackState t f hf)
        (factorTrace_tracial t f hf ht)) (multiplicityLevel t S j) a n) := by
  exact (sourceLevelEmbedding_left t f hf S i j hS hfree hij a n).symm

private lemma faithful_conjugation_level (u : unitary D) (n : ℕ) :
    (innerRepresentation t ht f S i hS hfree hgen u).toLinearIsometry.toContinuousLinearMap.comp
      (sourceLevelEmbedding t f hf S i j hS hfree hij n).toContinuousLinearMap =
    (sourceLevelEmbedding t f hf S i j hS hfree hij n).toContinuousLinearMap.comp
      (wordConjugationAction (faithfulWordActions (pullbackState t f hf)
        (factorTrace_tracial t f hf ht)) (multiplicityLevel t S j) u n) := by
  exact innerRepresentation_level t ht f hf S i j hS hfree hgen hij u n

include hgen hcolors he hsize hDgen hGL hGW in
theorem free_word_structure_oai : ∃ B : ∀ k, multiplicityLevel t S j k →L[ℂ] multiplicityLevel t S j k,
    (∀ k, ‖B k‖ ≤ ‖G‖) ∧
    (∀ k (d : factorFull t f hf)
      (x : factorZero t f hf) (a : multiplicityLevel t S j k),
      G (embeddedSourceWord t f hf S i j hS hfree hij k d x a) =
        embeddedSourceWord t f hf S i j hS hfree hij k d x (B k a)) ∧
    (∀ k (d : factorFull t f hf)
      (x : factorZero t f hf) (a : multiplicityLevel t S j k),
      G.adjoint (embeddedSourceWord t f hf S i j hS hfree hij k d x a) =
        embeddedSourceWord t f hf S i j hS hfree hij k d x ((B k).adjoint a)) := by
  have hcov (stage : ℕ) (u : unitary (Matrix (I stage) (I stage) ℂ)) (level : ℕ) :=
    faithful_conjugation_level t ht f hf S i j hS hfree hgen hij
      (by exact TracialGNS.stageUnitary (φ stage) u) level
  have rule := faithful_word_structure I φ e he hsize (pullbackState t f hf)
    (factorTrace_tracial t f hf ht) hDgen (multiplicityLevel t S j) t.functional.GNS
  have embedded := rule (sourceLevelEmbedding t f hf S i j hS hfree hij)
    (sourceLevelIsHilbertSum t f hf S i j hS hfree hij hcolors hgen)
  have h := embedded (fun a => t.functional.gnsStarAlgHom (f a))
    (fun n u => (innerRepresentation t ht f S i hS hfree hgen
      (TracialGNS.stageUnitary (φ n) u)).toLinearIsometry.toContinuousLinearMap)
    G (faithful_left_level t ht f hf S i j hS hfree hij) hcov hGL hGW
  exact h

end Kadison.FreeBlocks

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.FreeBlocks.free_word_structure_oai.{u_1, u_2} := @OAI.Kadison.FreeBlocks.free_word_structure_oai.{u_1, u_2}
