-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.sumConjugation_levelWord
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:36:00.97381+00:00
-- url     : https://prove2.me/submissions/38873c9f-881a-4727-acaa-cf41ba3e7bcf

import Mathlib
import Definitions.Def_OAIQ039C048
import Definitions.Def_OAIQ039C065

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

lemma paramD_mapBlockD (T : letterSpace t S i → letterSpace t S i) :
    ∀ n (x : BlockParams t S i j n) (k : Fin n),
      paramD t S n (mapBlockD t S i j T n x) k=T (paramD t S n x k)
  | 0,_,k => Fin.elim0 k
  | n+1,x,k => by
      refine Fin.cases ?_ (fun k => ?_) k
      · rfl
      · exact paramD_mapBlockD T n x.2 k

lemma paramJ_mapBlockD (T : letterSpace t S i → letterSpace t S i) :
    ∀ n (x : BlockParams t S i j n),
      paramJ t S n (mapBlockD t S i j T n x)=paramJ t S n x
  | 0,_ => rfl
  | n+1,x => by
      change x.1.1 ⊗ₜ[ℂ] paramJ t S n (mapBlockD t S i j T n x.2)=_
      rw [paramJ_mapBlockD T n x.2]
      rfl

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetry13
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

open FreeWordTensor UniformSpace

open scoped ComplexOrder InnerProductSpace TensorProduct

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i : ι) (hS : S i=f.range)

lemma letterGNSIso_pre (x : HilbertCompletion.centered
    ((pullbackState t f hf).functional.toPreGNS 1)) :
    (letterGNSIso t f hf S i hS
      (letterPreMap t f hf S i hS x : Completion (letterSpace t S i)) :
        (pullbackState t f hf).functional.GNS) =
      ((x : preSpace (pullbackState t f hf)) : (pullbackState t f hf).functional.GNS) := by
  change (HilbertCompletion.centeredMap _
    ((HilbertCompletion.congr (letterPreIso t f hf S i hS)).symm
      (letterPreMap t f hf S i hS x : Completion (letterSpace t S i))) :
      (pullbackState t f hf).functional.GNS) = _
  have hx : (letterPreMap t f hf S i hS x : Completion (letterSpace t S i)) =
      HilbertCompletion.congr (letterPreIso t f hf S i hS)
        (x : Completion (HilbertCompletion.centered
          ((pullbackState t f hf).functional.toPreGNS 1))) :=
    (HilbertCompletion.congr_coe (letterPreIso t f hf S i hS) x).symm
  rw [hx, LinearIsometryEquiv.symm_apply_apply, HilbertCompletion.centeredMap_coe]

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeLetterIntertwine
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
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i : ι) (hS : S i=f.range)

lemma letterGNSIso_value (x : letterSpace t S i) (d : D) (hd : f d=letterValue t S i x) :
    (letterGNSIso t f hf S i hS (x : Completion (letterSpace t S i)) :
      (factorTrace t f hf).GNS)=TracialGNS.algebraVector (factorTrace t f hf) d := by
  let xp : HilbertCompletion.centered ((pullbackState t f hf).functional.toPreGNS 1) :=
    ⟨(pullbackState t f hf).functional.toPreGNS d,by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right,inner_pre_one]
      change t.functional (f d)=0
      rw [hd]
      exact x.property.2⟩
  have hx : letterPreMap t f hf S i hS xp=x := by
    apply Subtype.ext
    change t.functional.toPreGNS (f d)=(x : preSpace t)
    rw [hd]
    exact PositiveLinearMap.toPreGNS_ofPreGNS _ _
  have h := letterGNSIso_pre t f hf S i hS xp
  rw [hx] at h
  exact h

variable (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

lemma letterGNSIso_conjugation (u : unitary D) (x : letterSpace t S i) :
    letterGNSIso t f hf S i hS
      (letterIso t S (innerFamily f i u) (innerFamily_mem f S i hS u)
        (innerFamily_trace t ht f i u) i x : Completion (letterSpace t S i)) =
    centeredIsometry (TracialGNS.vacuum (factorTrace t f hf))
      (TracialGNS.conjugation (factorTrace t f hf) (factorTrace_tracial t f hf ht) u)
      (TracialGNS.conjugation_vacuum (factorTrace t f hf) (factorTrace_tracial t f hf ht) u)
      (letterGNSIso t f hf S i hS (x : Completion (letterSpace t S i))) := by
  have hxm : letterValue t S i x ∈ f.range := hS ▸ x.property.1
  obtain ⟨d,hd⟩ := hxm
  change f d=letterValue t S i x at hd
  have hd' : f ((u:D)*d*star (u:D)) = letterValue t S i
      (letterIso t S (innerFamily f i u) (innerFamily_mem f S i hS u)
        (innerFamily_trace t ht f i u) i x) := by
    change f ((u:D)*d*star (u:D))=innerFamily f i u i (letterValue t S i x)
    rw [innerFamily_self,map_mul,map_mul,hd]
  apply Subtype.ext
  change (letterGNSIso t f hf S i hS
      (letterIso t S (innerFamily f i u) (innerFamily_mem f S i hS u)
        (innerFamily_trace t ht f i u) i x : Completion (letterSpace t S i)) :
      (factorTrace t f hf).GNS) =
    TracialGNS.conjugation (factorTrace t f hf) (factorTrace_tracial t f hf ht) u
      (letterGNSIso t f hf S i hS (x : Completion (letterSpace t S i)) :
        (factorTrace t f hf).GNS)
  rw [letterGNSIso_value t f hf S i hS _ _ hd',
    letterGNSIso_value t f hf S i hS x d hd]
  exact (TracialGNS.conjugation_coe (factorTrace t f hf) (factorTrace_tracial t f hf ht) u d).symm

end Kadison.FreeBlocks

end

end
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

lemma sumConjugation_levelWord_oai (u : unitary D) (d : D) (n : ℕ)
    (x : BlockParams t S i j n) :
    sourceConjugation t ht f hf S j u n (levelWord t f hf S i j hS d n x) =
    levelWord t f hf S i j hS ((u:D)*d*star (u:D)) n
      (mapBlockD t S i j
        (letterIso t S (innerFamily f i u) (innerFamily_mem f S i hS u)
          (innerFamily_trace t ht f i u) i) n x) := by
  simp only [sourceConjugation, levelWord, HilbertTensor.map_pair,
    LinearIsometry.coe_toContinuousLinearMap, one_apply_eq_self,
    paramJ_mapBlockD,paramD_mapBlockD]
  apply congrArg (fun y : sourceScalar t f hf n =>
    HilbertTensor.pair y (paramJ t S n x : multiplicityLevel t S j n))
  have hw := PreHilbert.wordMap_word (factorFull t f hf) (factorZero t f hf)
    (TracialGNS.conjugation (factorTrace t f hf) (factorTrace_tracial t f hf ht) u)
    (centeredIsometry (TracialGNS.vacuum (factorTrace t f hf))
      (TracialGNS.conjugation (factorTrace t f hf) (factorTrace_tracial t f hf ht) u)
      (TracialGNS.conjugation_vacuum (factorTrace t f hf) (factorTrace_tracial t f hf ht) u))
    n (TracialGNS.algebraVector (factorTrace t f hf) d)
    (fun k => (letterGNSIso t f hf S i hS (paramD t S n x k : Completion (letterSpace t S i)) :
      TracialGNS.zeroSpace (factorTrace t f hf)))
  refine hw.trans ?_
  have hd := TracialGNS.conjugation_coe (factorTrace t f hf)
    (factorTrace_tracial t f hf ht) u d
  change TracialGNS.conjugation (factorTrace t f hf) (factorTrace_tracial t f hf ht) u
    (TracialGNS.algebraVector (factorTrace t f hf) d)=
      TracialGNS.algebraVector (factorTrace t f hf) ((u:D)*d*star (u:D)) at hd
  rw [hd]
  congr 1
  funext k
  exact (letterGNSIso_conjugation t f hf S i hS ht u (paramD t S n x k)).symm

end Kadison.FreeBlocks

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.FreeBlocks.sumConjugation_levelWord_oai.{u_1} := @OAI.Kadison.FreeBlocks.sumConjugation_levelWord_oai.{u_1}
