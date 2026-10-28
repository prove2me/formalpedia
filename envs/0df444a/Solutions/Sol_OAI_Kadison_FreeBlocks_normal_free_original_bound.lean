-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.normal_free_original_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:35:09.881532+00:00
-- url     : https://prove2.me/submissions/615ce209-677b-4eb9-b99a-4e81f36841d7

import Mathlib
import Definitions.Def_OAIQ039C018
import Definitions.Def_OAIQ039C041
import Definitions.Def_OAIQ039C054
import Definitions.Def_OAIQ039C055
import Definitions.Def_OAIQ039C056
import Theorems.Thm_OAI_Kadison_FreeBlocks_normal_free_corner_bound

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteHankel
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.FreeCorner

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma norm_compress_le (V : K →ₗᵢ[ℂ] H) (T : H →L[ℂ] H) :
    ‖compress V T‖ ≤ ‖T‖ := by
  have hv : ‖V.toContinuousLinearMap‖ ≤ 1 := V.norm_toContinuousLinearMap_le
  have hv' : ‖V.toContinuousLinearMap.adjoint‖ ≤ 1 := by rw [adjoint.norm_map]; exact hv
  calc
    ‖compress V T‖ ≤ ‖V.toContinuousLinearMap.adjoint‖ * ‖T‖ *
        ‖V.toContinuousLinearMap‖ := (opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖T‖ * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right hv' (norm_nonneg _)) hv (norm_nonneg _)
      (by positivity)
    _ = ‖T‖ := by ring

end Kadison.FreeCorner

end

end
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

lemma baseEmbedding_factorOf (a : A) (ha : a∈S true) :
    baseEmbedding t S hfree
      (factorOf t S true a ha : multiplicityLevel t S true 0)=
      (t.functional.toPreGNS a : t.functional.GNS) := by
  rw [baseEmbedding_coe,factorValue_factorOf]

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_GNSVectorEmbedding
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

open UniformSpace ContinuousLinearMap

namespace Kadison.VectorGNS

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (τ : A →ₚ[ℂ] ℂ) (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
  (hτ : ∀ a,τ a=inner ℂ ξ (φ a ξ))

lemma intertwines (a : A) :
    (embedding τ φ ξ hτ).toContinuousLinearMap.comp (τ.gnsStarAlgHom a)=
      (φ a).comp (embedding τ φ ξ hτ).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  refine (TracialGNS.algebraVector_dense τ).induction_on x
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  have hl : τ.gnsStarAlgHom a (TracialGNS.algebraVector τ b)=
      TracialGNS.algebraVector τ (a*b) := TracialGNS.left_coe τ a b
  simp only [comp_apply,LinearIsometry.coe_toContinuousLinearMap,hl,embedding_coe,
    map_mul,mul_apply_eq_comp]

lemma adjoint_intertwines (a : A) :
    (τ.gnsStarAlgHom a).comp (embedding τ φ ξ hτ).toContinuousLinearMap.adjoint=
      (embedding τ φ ξ hτ).toContinuousLinearMap.adjoint.comp (φ a) := by
  have he := congrArg (fun T : τ.GNS →L[ℂ] H => T.adjoint) (intertwines τ φ ξ hτ (star a))
  simpa only [adjoint_comp,map_star,star_eq_adjoint,adjoint_adjoint] using he

lemma compression_commutator (T : H →L[ℂ] H) (a : A) :
    compression τ φ ξ hτ T*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*compression τ φ ξ hτ T=
      compression τ φ ξ hτ (T*φ a-φ a*T) := by
  simp only [compression,FreeCorner.compress,mul_def,comp_sub,sub_comp]
  congr 1
  · simp only [comp_assoc]
    rw [intertwines τ φ ξ hτ a]
  · simp only [←comp_assoc]
    rw [adjoint_intertwines τ φ ξ hτ a]

lemma compression_on_preserved (T : H →L[ℂ] H) (x y : τ.GNS)
    (hxy : T (embedding τ φ ξ hτ x)=embedding τ φ ξ hτ y) :
    compression τ φ ξ hτ T x=y := by
  change (embedding τ φ ξ hτ).toContinuousLinearMap.adjoint
    (T (embedding τ φ ξ hτ x))=y
  rw [hxy]
  have he := congrArg (fun B : τ.GNS →L[ℂ] τ.GNS => B y)
    (LinearIsometry.adjoint_comp_self (embedding τ φ ξ hτ))
  exact he

end Kadison.VectorGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_IsometryCompression
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open ContinuousLinearMap

namespace Kadison.FreeCorner

variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

omit [CompleteSpace L] in
lemma factorIsometry_comp (E : L →ₗᵢ[ℂ] H) (F : K →ₗᵢ[ℂ] H)
    (hEF : Set.range E⊆Set.range F) :
    F.toContinuousLinearMap.comp (factorIsometry E F hEF).toContinuousLinearMap=
      E.toContinuousLinearMap := by
  ext x
  exact isometry_project_range E F hEF x

lemma compress_factorIsometry (E : L →ₗᵢ[ℂ] H) (F : K →ₗᵢ[ℂ] H)
    (hEF : Set.range E⊆Set.range F) (T : H →L[ℂ] H) :
    compress E T=compress (factorIsometry E F hEF) (compress F T) := by
  have he := factorIsometry_comp E F hEF
  conv_lhs => rw [compress,←he,adjoint_comp]
  simp only [compress,comp_assoc]

lemma norm_compress_le_of_range_subset (E : L →ₗᵢ[ℂ] H) (F : K →ₗᵢ[ℂ] H)
    (hEF : Set.range E⊆Set.range F) (T : H →L[ℂ] H) :
    ‖compress E T‖≤‖compress F T‖ := by
  rw [compress_factorIsometry E F hEF T]
  exact norm_compress_le _ _

end Kadison.FreeCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeBaseCompression
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments ContinuousLinearMap

variable {A B : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable (τ : B →ₚ[ℂ] ℂ) (t : FaithfulState A) (f : B →⋆ₐ[ℂ] A)
  (htrace : ∀ a,τ a=t.functional (f a))

variable (R : Bool → StarSubalgebra ℂ A) (hfree : Free R t.functional.toLinearMap)

lemma originalEmbedding_range (hf : ∀ a : B,f a∈R true) :
    Set.range (originalEmbedding τ t f htrace)⊆Set.range (baseEmbedding t R hfree) := by
  rintro _ ⟨x,rfl⟩
  refine (TracialGNS.algebraVector_dense τ).induction_on x
    ((baseEmbedding t R hfree).isometry.isClosedEmbedding.isClosed_range.preimage
      (originalEmbedding τ t f htrace).continuous) ?_
  intro a
  refine ⟨(factorOf t R true (f a) (hf a) : multiplicityLevel t R true 0),?_⟩
  rw [baseEmbedding_factorOf,originalEmbedding_coe]
  rfl

theorem original_commutator_le_base (hf : ∀ a : B,f a∈R true)
    (G : t.functional.GNS →L[ℂ] t.functional.GNS) (T : τ.GNS →L[ℂ] τ.GNS)
    (hGT : ∀ x,G (originalEmbedding τ t f htrace x)=originalEmbedding τ t f htrace (T x))
    (a : B) :
    ‖T*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*T‖≤
      ‖FreeCorner.compress (K:=multiplicityLevel t R true 0) (H:=t.functional.GNS) (baseEmbedding t R hfree)
        (G*t.functional.gnsStarAlgHom (f a)-t.functional.gnsStarAlgHom (f a)*G)‖ := by
  have hcomp : VectorGNS.compression τ (t.functional.gnsStarAlgHom.comp f)
      (TracialGNS.vacuum t.functional) (pullback_vector_trace τ t f htrace) G=T := by
    ext x
    exact VectorGNS.compression_on_preserved _ _ _ _ G x (T x) (hGT x)
  rw [←hcomp,VectorGNS.compression_commutator]
  exact @FreeCorner.norm_compress_le_of_range_subset
    t.functional.GNS (multiplicityLevel t R true 0) τ.GNS
    inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance
    (originalEmbedding τ t f htrace) (baseEmbedding t R hfree)
    (originalEmbedding_range τ t f htrace R hfree hf) _

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeOriginalBound
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeWordAction

variable {A B : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (D : VonNeumannAlgebra H)
  (t : FaithfulState A) (htr : ∀ a b : A,t.functional (a*b)=t.functional (b*a))
  (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)
  (R : Bool → StarSubalgebra ℂ A) (hR : R false=f.range)
  (hfree : Free R t.functional.toLinearMap)
  (hgen : ∀ a : A,t.functional.gnsStarAlgHom a∈
    Set.centralizer (Set.centralizer (generatedOperators t R : Set _)))
  (I : ℕ → Type*) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)] [∀ n,Nonempty (I n)]
  (φ : ∀ n,Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)
  (inc : ∀ {n m : ℕ},n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
  (hinc : ∀ n m (h : n ≤ m) a,φ m (inc h a)=φ n a)
  (hsize : ∀ n q : ℕ,∃ m,n ≤ m ∧ q ≤ Fintype.card (I m))
  (hDgen : ∀ a : D,(factorTrace t f hf).gnsStarAlgHom a∈
    Set.centralizer (Set.centralizer (TracialGNS.stageAlgebra (factorTrace t f hf) I φ : Set _)))

include htr hR hfree hgen hinc hsize hDgen in
theorem normal_free_original_bound_oai
    (hnormal : NormalGNS.BoundedWOTContinuous D (factorTrace t f hf))
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections D)
    (τ : B →ₚ[ℂ] ℂ) (j : B →⋆ₐ[ℂ] A) (htrace : ∀ a,τ a=t.functional (j a))
    (hj : ∀ a : B,j a∈R true)
    (G : t.functional.GNS →L[ℂ] t.functional.GNS) (T : τ.GNS →L[ℂ] τ.GNS)
    (hGT : ∀ x,G (originalEmbedding τ t j htrace x)=originalEmbedding τ t j htrace (T x))
    (hGD : ∀ a : D,G*t.functional.gnsStarAlgHom (f a)=t.functional.gnsStarAlgHom (f a)*G)
    (s : unitary B) (hs0 : τ (s:B)=0) (hs2 : (s:B)*(s:B)=1)
    (ε β : ℝ) (hε : 0≤ε) (hβ : 0<β) (hβ1 : β≤1)
    (hC : ∀ x,CornerSymmetrization.CornerElement (factorOperators t f) (ambientOperators t R)
      (TracialGNS.vacuum t.functional) (β:ℂ) x → ‖G*x-x*G‖≤ε*‖x‖) :
    ‖T*τ.gnsStarAlgHom (s:B)-τ.gnsStarAlgHom (s:B)*T‖≤1040*ε := by
  let u : unitary A := ⟨j (s:B),Unitary.map_mem j s.property⟩
  have hu0 : t.functional (u:A)=0 := (htrace (s:B)).symm.trans hs0
  have hu2 : (u:A)*(u:A)=1 := by change j (s:B)*j (s:B)=1; rw [←map_mul,hs2,map_one]
  exact (original_commutator_le_base τ t j htrace R hfree hj G T hGT (s:B)).trans
    (normal_free_corner_bound D t htr f hf R hR hfree hgen I φ inc hinc hsize hDgen
      hnormal hdiffuse G hGD u (hj (s:B)) hu0 hu2 ε β hε hβ hβ1 hC)

end Kadison.FreeBlocks

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.FreeBlocks.normal_free_original_bound_oai.{u_1} := @OAI.Kadison.FreeBlocks.normal_free_original_bound_oai.{u_1}
