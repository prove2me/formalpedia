-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.innerRepresentation_commutes_other
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:02:29.303229+00:00
-- url     : https://prove2.me/submissions/fa3f1414-36b7-4924-a0be-668dd8007026

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

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeNormalizer
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

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

lemma innerRepresentation_conj_generator (u : unitary D) (k : ι) (a : A) (ha : a∈S k) :
    (innerRepresentation t ht f S i hS hfree hgen u).conjStarAlgEquiv
      (t.functional.gnsStarAlgHom a) =
    t.functional.gnsStarAlgHom (innerFamily f i u k a) := by
  ext x
  let W := innerRepresentation t ht f S i hS hfree hgen u
  change W (t.functional.gnsStarAlgHom a (W.symm x))=_
  have h := action_left_apply t S (innerFamily f i u) (innerFamily_mem f S i hS u)
    (innerFamily_trace t ht f i u) hfree hgen k a ha (W.symm x)
  change W (t.functional.gnsStarAlgHom a (W.symm x))=
    t.functional.gnsStarAlgHom (innerFamily f i u k a) (W (W.symm x)) at h
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetrization
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator

open MeasureTheory MeasureTheory.Measure

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

lemma innerRepresentation_commutes_other_oai (hji : j≠i) (u : unitary D) (a : A) (ha : a∈S j) :
    (innerRepresentation t ht f S i hS hfree hgen u : t.functional.GNS →L[ℂ] t.functional.GNS)*
      t.functional.gnsStarAlgHom a = t.functional.gnsStarAlgHom a*
    (innerRepresentation t ht f S i hS hfree hgen u : t.functional.GNS →L[ℂ] t.functional.GNS) := by
  let W := innerRepresentation t ht f S i hS hfree hgen u
  have h := innerRepresentation_conj_generator t ht f S i hS hfree hgen u j a ha
  rw [innerFamily_other f i u hji] at h
  ext x
  have hh := congrArg (fun T : t.functional.GNS →L[ℂ] t.functional.GNS => T (W x)) h
  change W (t.functional.gnsStarAlgHom a (W.symm (W x)))=t.functional.gnsStarAlgHom a (W x) at hh
  change W (t.functional.gnsStarAlgHom a x)=t.functional.gnsStarAlgHom a (W x)
  simpa only [LinearIsometryEquiv.symm_apply_apply] using hh

end Kadison.FreeBlocks

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.FreeBlocks.innerRepresentation_commutes_other_oai.{u_1} := @OAI.Kadison.FreeBlocks.innerRepresentation_commutes_other_oai.{u_1}
