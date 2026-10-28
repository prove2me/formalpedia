-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.innerRepresentation_word
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:04:20.92682+00:00
-- url     : https://prove2.me/submissions/cc4dfb39-a747-4f2d-9bbc-f7455e4b6270

import Mathlib
import Definitions.Def_OAIQ039C059

section
-- module Solutions.OAIQ039_CM.Commutator_FreeActionCovariance
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.FreeCreation.instIsClosedGNSFunctionalCoeSubmoduleComplexHeadSpace _root_.OAI.Kadison.FreeCreation.instIsClosedGNSFunctionalCoeSubmoduleComplexTailSpace _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeWordAction

open FreeWordTensor FreeMoments

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (α : ι → A ≃⋆ₐ[ℂ] A)
  (hmem : ∀ i a, a∈S i → α i a∈S i)
  (hτ : ∀ i a, t.functional (α i a)=t.functional a)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

lemma action_generator_word (i : ι) (a : A) (ha : a∈S i)
    (w : List (Letter S t.functional.toLinearMap)) (hw : Reduced w) :
    action t S α hmem hτ hfree hgen (TracialGNS.algebraVector t.functional (a*word w)) =
      TracialGNS.algebraVector t.functional
        (α i a*word (w.map (letter t S α hmem hτ))) := by
  let V := TracialGNS.algebraVector t.functional
  let W := action t S α hmem hτ hfree hgen
  have hword : ∀ w, Reduced w → W (V (word w))=V (word (w.map (letter t S α hmem hτ))) :=
    fun w hw => action_word t S α hmem hτ hfree hgen w hw
  have hone : W (V 1)=V 1 := hword [] reduced_nil
  let c : Letter S t.functional.toLinearMap :=
    ⟨i,a-t.functional a • (1:A),sub_mem ha (SMulMemClass.smul_mem _ (one_mem _)),
      by simp [map_sub,map_smul,t.normalized]⟩
  change W (V (a*word w))=V (α i a*word (w.map (letter t S α hmem hτ)))
  cases w with
  | nil =>
    have h := hword [c] (List.IsChain.singleton c)
    change W (V ((a-t.functional a • (1:A))*1)) =
      V (α i (a-t.functional a • (1:A))*1) at h
    simp only [mul_one,map_sub,map_smul,map_one,hone] at h
    simpa only [word_nil,List.map_nil,mul_one] using (sub_left_inj.mp h)
  | cons b w =>
    by_cases hib : i=b.color
    · let d : Letter S t.functional.toLinearMap :=
        ⟨i,a*b.val-t.functional (a*b.val) • (1:A),
          sub_mem (mul_mem ha (by simpa only [hib] using b.mem))
            (SMulMemClass.smul_mem _ (one_mem _)),
          by simp [map_sub,map_smul,t.normalized]⟩
      have hd : Reduced (d::w) := by
        exact hw.imp_head (by intro c hc; simpa only [d,hib] using hc)
      have ht := hword w hw.tail
      have h := hword (d::w) hd
      have hid : (a*b.val-t.functional (a*b.val) • (1:A))*word w =
          a*word (b::w)-t.functional (a*b.val) • word w := by
        simp only [word_cons,sub_mul,smul_mul_assoc,one_mul,mul_assoc]
      have hj : α i (a*b.val-t.functional (a*b.val) • (1:A))*
            word (w.map (letter t S α hmem hτ)) =
          α i a*word ((b::w).map (letter t S α hmem hτ)) -
            t.functional (a*b.val) • word (w.map (letter t S α hmem hτ)) := by
        simp only [map_sub,map_smul,map_mul,map_one,List.map_cons,word_cons,letter_val,
          sub_mul,smul_mul_assoc,one_mul,mul_assoc,hib]
      change W (V ((a*b.val-t.functional (a*b.val) • (1:A))*word w)) =
        V (α i (a*b.val-t.functional (a*b.val) • (1:A))*
          word (w.map (letter t S α hmem hτ))) at h
      rw [hid,hj] at h
      simp only [map_sub,map_smul,ht] at h
      exact sub_left_inj.mp h
    · have hc : Reduced (c::b::w) := by
        exact List.isChain_cons_cons.mpr ⟨hib,hw⟩
      have ht := hword (b::w) hw
      have h := hword (c::b::w) hc
      change W (V ((a-t.functional a • (1:A))*word (b::w))) =
        V (α i (a-t.functional a • (1:A))*word ((b::w).map (letter t S α hmem hτ))) at h
      simp only [sub_mul,smul_mul_assoc,one_mul,map_sub,map_smul,map_one,ht] at h
      exact sub_left_inj.mp h

lemma action_left (i : ι) (a : A) (ha : a∈S i) :
    (action t S α hmem hτ hfree hgen).toContinuousLinearMap.comp (t.functional.gnsStarAlgHom a) =
    (t.functional.gnsStarAlgHom (α i a)).comp (action t S α hmem hτ hfree hgen).toContinuousLinearMap := by
  apply ext_reduced t S hfree hgen
  intro w hw
  simp only [ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,
    TracialGNS.algebraVector_apply,TracialGNS.left_coe]
  rw [action_word t S α hmem hτ hfree hgen w hw]
  rw [TracialGNS.left_coe]
  exact action_generator_word t S α hmem hτ hfree hgen i a ha w hw

end Kadison.FreeWordAction

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeActionBlock
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι)

variable (α : ι → A ≃⋆ₐ[ℂ] A)
  (hmem : ∀ k a, a∈S k → α k a∈S k)
  (hτ : ∀ k a, t.functional (α k a)=t.functional a)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

lemma action_left_apply (k : ι) (a : A) (ha : a∈S k) (x : t.functional.GNS) :
    action t S α hmem hτ hfree hgen (t.functional.gnsStarAlgHom a x)=
      t.functional.gnsStarAlgHom (α k a) (action t S α hmem hτ hfree hgen x) :=
  congrArg (fun T : t.functional.GNS →L[ℂ] t.functional.GNS => T x)
    (action_left t S α hmem hτ hfree hgen k a ha)

lemma action_algebra_of_mem (k : ι) (a : A) (ha : a∈S k) :
    action t S α hmem hτ hfree hgen (TracialGNS.algebraVector t.functional a)=
      TracialGNS.algebraVector t.functional (α k a) := by
  simpa only [word_nil,List.map_nil,mul_one] using
    action_generator_word t S α hmem hτ hfree hgen k a ha [] reduced_nil

lemma action_vector_mul (k : ι) (a : A) (ha : a∈S k) (b : A) :
    action t S α hmem hτ hfree hgen (TracialGNS.algebraVector t.functional (a*b))=
      t.functional.gnsStarAlgHom (α k a)
        (action t S α hmem hτ hfree hgen (TracialGNS.algebraVector t.functional b)) := by
  simpa only [TracialGNS.algebraVector_apply,TracialGNS.left_coe] using (action_left_apply t S α hmem hτ hfree hgen k a ha
    (TracialGNS.algebraVector t.functional b))

include hfree hgen in
lemma action_blockRead_pure (hj : ∀ a∈S j, α j a=a) :
    ∀ n (x : BlockParams t S i j n),
      action t S α hmem hτ hfree hgen
        (TracialGNS.algebraVector t.functional (blockRead t S n (blockPure t S n x))) =
      TracialGNS.algebraVector t.functional
        (blockRead t S n (blockPure t S n
          (mapBlockD t S i j (letterIso t S α hmem hτ i) n x)))
  | 0,x => by
      change action t S α hmem hτ hfree hgen
        (TracialGNS.algebraVector t.functional (factorValue t S j x))=_
      rw [action_algebra_of_mem t S α hmem hτ hfree hgen j (factorValue t S j x) (show factorValue t S j x ∈ S j from x.property),
        hj (factorValue t S j x) (show factorValue t S j x ∈ S j from x.property)]
      rfl
  | n+1,x => by
      change action t S α hmem hτ hfree hgen
        (TracialGNS.algebraVector t.functional
          (letterValue t S j x.1.1 * (letterValue t S i x.1.2 *
            blockRead t S n (blockPure t S n x.2))))=_
      rw [action_vector_mul t S α hmem hτ hfree hgen j (letterValue t S j x.1.1) (show letterValue t S j x.1.1∈S j from x.1.1.property.1),
        action_vector_mul t S α hmem hτ hfree hgen i (letterValue t S i x.1.2) (show letterValue t S i x.1.2∈S i from x.1.2.property.1),
        action_blockRead_pure hj n x.2,hj (letterValue t S j x.1.1) (show letterValue t S j x.1.1∈S j from x.1.1.property.1)]
      simp only [TracialGNS.algebraVector_apply,TracialGNS.left_coe]
      rfl

end Kadison.FreeBlocks

end

end
end

end OAI
end

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

lemma innerRepresentation_word_oai (u : unitary D) (d : D) (n : ℕ)
    (x : BlockParams t S i j n) :
    innerRepresentation t ht f S i hS hfree hgen u
      (sourceLevelEmbedding t f hf S i j hS hfree hij n
        (levelWord t f hf S i j hS d n x)) =
    sourceLevelEmbedding t f hf S i j hS hfree hij n
      (levelWord t f hf S i j hS ((u:D)*d*star (u:D)) n
        (mapBlockD t S i j
          (letterIso t S (innerFamily f i u) (innerFamily_mem f S i hS u)
            (innerFamily_trace t ht f i u) i) n x)) := by
  rw [sourceLevelEmbedding_word,sourceLevelEmbedding_word]
  have hfd : f d∈S i := by rw [hS]; exact ⟨d,rfl⟩
  change action t S (innerFamily f i u) (innerFamily_mem f S i hS u)
      (innerFamily_trace t ht f i u) hfree hgen
      (t.functional.gnsStarAlgHom (f d)
        (TracialGNS.algebraVector t.functional (blockRead t S n (blockPure t S n x)))) = _
  rw [action_left_apply t S (innerFamily f i u) (innerFamily_mem f S i hS u)
    (innerFamily_trace t ht f i u) hfree hgen i (f d) hfd,
    action_blockRead_pure t S i j (innerFamily f i u) (innerFamily_mem f S i hS u)
      (innerFamily_trace t ht f i u) hfree hgen
      (fun a _ => innerFamily_other f i u hij.symm a) n x]
  congr 2
  simp only [innerFamily_self,map_mul]

end Kadison.FreeBlocks

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.FreeBlocks.innerRepresentation_word_oai.{u_1} := @OAI.Kadison.FreeBlocks.innerRepresentation_word_oai.{u_1}
