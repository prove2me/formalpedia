-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.normalized_fejer_entry
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:56:40.326983+00:00
-- url     : https://prove2.me/submissions/4d5c6f4e-ff7a-46cd-9b4f-927975caa8c8

import Mathlib
import Definitions.Def_OAIQ039C066
import Theorems.Thm_OAI_Kadison_FreeBlocks_finite_fejer_entry

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
-- module Solutions.OAIQ039_CM.Commutator_FreeHilbertEntries
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

open scoped InnerProductSpace ComplexOrder

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

lemma baseEmbedding_coe (v : factorSpace t S true) :
    baseEmbedding t S hfree (v : multiplicityLevel t S true 0)=
      (t.functional.toPreGNS (factorValue t S true v) : t.functional.GNS) := by
  simp [baseEmbedding,blockEmbedding,blockIsometry,blockReadPre,blockRead]

lemma dihedralColumn_coe (e : A) (w : unitary A) (c : ℝ) (n : ℕ)
    (v : factorSpace t S true) :
    dihedralColumn t S hfree e w c n (v : multiplicityLevel t S true 0)=
      (c:ℂ) • (t.functional.toPreGNS
        (e*DihedralCorner.wave w (-(n:ℤ))*factorValue t S true v) : t.functional.GNS) := by
  change (c:ℂ) • t.functional.gnsStarAlgHom _
    (baseEmbedding t S hfree (v : multiplicityLevel t S true 0))=_
  rw [baseEmbedding_coe,TracialGNS.left_coe]

end Kadison.FreeBlocks

end

end
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

end Kadison.FreeBlocks

end

end
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

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeDihedralColumns
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

open scoped InnerProductSpace ComplexOrder

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor DihedralCorner

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

omit [PartialOrder A] [StarOrderedRing A] in
lemma dihedral_negative_wave (d s : unitary A)
    (hd2 : (d:A)*(d:A)=1) (hs2 : (s:A)*(s:A)=1) (n : ℕ) :
    wave (d*s) (-(n:ℤ))=((s:A)*(d:A))^n := by
  have hd : d⁻¹=d := inv_eq_of_mul_eq_one_right (Subtype.ext hd2)
  have hs : s⁻¹=s := inv_eq_of_mul_eq_one_right (Subtype.ext hs2)
  rw [wave,zpow_neg,zpow_natCast,←inv_pow,mul_inv_rev,hd,hs]
  simp only [Submonoid.coe_mul,SubmonoidClass.coe_pow]

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f) (hS : S false=f.range)

variable (d s : unitary A) (hd : (d:A)∈S false) (hs : (s:A)∈S true)
  (hd0 : t.functional (d:A)=0) (hs0 : t.functional (s:A)=0)
  (hd2 : (d:A)*(d:A)=1) (hs2 : (s:A)*(s:A)=1)

variable (e : D) (hr : 0<‖TracialGNS.algebraVector (factorTrace t f hf) e‖)

include hd2 hs2 in
theorem normalizedColumn_eq_dihedral (n : ℕ) :
    (normalizedColumn t S f hf hS hfree Bool.false_ne_true e
      (letterOf t S true (s:A) hs hs0) (norm_letterOf_unitary t S true s hs hs0)
      (letterOf t S false (d:A) hd hd0) (norm_letterOf_unitary t S false d hd hd0) hr n
      ).toContinuousLinearMap=
    dihedralColumn t S hfree (f e) (d*s)
      ‖TracialGNS.algebraVector (factorTrace t f hf) e‖⁻¹ n := by
  apply ContinuousLinearMap.ext
  intro v
  induction v using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih v =>
    change normalizedColumn t S f hf hS hfree Bool.false_ne_true e
      (letterOf t S true (s:A) hs hs0) (norm_letterOf_unitary t S true s hs hs0)
      (letterOf t S false (d:A) hd hd0) (norm_letterOf_unitary t S false d hd hd0) hr n
        (v : multiplicityLevel t S true 0)=_
    rw [normalizedColumn_apply,repeatedOutput_bounded]
    rw [letterValue_letterOf,letterValue_letterOf]
    rw [dihedralColumn_coe,dihedral_negative_wave d s hd2 hs2]
    change (_:ℂ) • t.functional.gnsStarAlgHom (f e)
      (t.functional.gnsStarAlgHom (((s:A)*(d:A))^n)
        (baseEmbedding t S hfree (v : multiplicityLevel t S true 0)))=_
    rw [baseEmbedding_coe,TracialGNS.left_coe,TracialGNS.left_coe]
    apply congrArg (fun a : A =>
      ((‖TracialGNS.algebraVector (factorTrace t f hf) e‖⁻¹:ℝ):ℂ) •
        (t.functional.toPreGNS a : t.functional.GNS))
    exact (mul_assoc _ _ _).symm

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

include htr hd hs hd0 hs0 hrot hd2 hs2 hpform hpd hdp hpD in
lemma normalized_fejer_entry_oai (e0 : D) (e : Corner hp)
    (heq : f e0=(e:A)) (heproj : IsStarProjection e)
    (he : e∈cornerFactor hp (S false) hpD)
    (hr : 0<‖TracialGNS.algebraVector (factorTrace t f hf) e0‖)
    (N : ℕ) (hN : 0 < N) (i j : Fin N) :
    ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=Completion (factorSpace t S true)) (F:=t.functional.GNS)
      (normalizedColumn t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr i.val).toContinuousLinearMap).comp
      (t.functional.gnsStarAlgHom ((e:A)*((fejerCorner hp (d*s) (2*N):Corner hp):A)*(e:A)))).comp
      (normalizedColumn t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr j.val).toContinuousLinearMap =
    ((halfCornerTrace hp t.functional.toLinearMap e).re:ℂ) •
      ((2*t.functional (wave (d*s) ((i.val:ℤ)-j.val)*
        ((fejerCorner hp (d*s) (2*N):Corner hp):A))) •
          (1:Completion (factorSpace t S true) →L[ℂ] Completion (factorSpace t S true))+
       (Complex.ofReal (((2*N:ℝ)-i.val-j.val-1)/(2*N:ℝ)^2)) • baseAction t S hfree (s:A)) := by
  rw [normalizedColumn_eq_dihedral t S hfree f hf hS d s hd hs hd0 hs0 hd2 hs2 e0 hr,
    normalizedColumn_eq_dihedral t S hfree f hf hS d s hd hs hd0 hs0 hd2 hs2 e0 hr,heq]
  exact finite_fejer_entry t S hfree f hf hp htr d s hd hs hd0 hs0 hrot hd2 hs2 hpform hpd hdp hpD
    e0 e heq heproj he hr N hN i j

end Kadison.FreeBlocks

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.FreeBlocks.normalized_fejer_entry_oai := @OAI.Kadison.FreeBlocks.normalized_fejer_entry_oai
