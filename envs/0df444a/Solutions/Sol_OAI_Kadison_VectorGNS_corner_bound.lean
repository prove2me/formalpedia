-- Prove2me | solution 1 for OAI.Kadison.VectorGNS.corner_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:53:16.49032+00:00
-- url     : https://prove2.me/submissions/6279be6f-27da-48b1-911b-6e177046b216

import Mathlib
import Definitions.Def_OAIQ039C060
import Definitions.Def_OAIQ039C065
import Theorems.Thm_OAI_Kadison_VectorGNS_ambient_range

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
-- module Solutions.OAIQ039_CM.Commutator_StandardTrace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology ComplexOrder

namespace Kadison.NormalGNS

open TracialGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

lemma gns_norm (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (a : M) :
    ‖τ.gnsStarAlgHom a‖=‖a‖ :=
  NonUnitalStarAlgHom.norm_map _ (gns_injective M τ hfaith) a

end Kadison.NormalGNS

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

lemma norm_commutator_compression_le (T : H →L[ℂ] H) (a : A) :
    ‖compression τ φ ξ hτ T*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*compression τ φ ξ hτ T‖≤
      ‖T*φ a-φ a*T‖ := by
  rw [compression_commutator]
  exact FreeCorner.norm_compress_le _ _

end Kadison.VectorGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_GNSCornerTransport
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder

open ContinuousLinearMap

namespace Kadison.VectorGNS

open FreeWordTensor FreeMoments FreeWordAction FreeBlocks

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (ξ : H)

variable (htr : ∀ a b : M,subalgebraTrace M ξ (a*b)=subalgebraTrace M ξ (b*a))
  (hfaith : ∀ a : M,subalgebraTrace M ξ (star a*a)=0 → a=0)
  (hone : subalgebraTrace M ξ 1=1)

variable {D : Type} [CStarAlgebra D] (f : D →⋆ₐ[ℂ] M)
  (R : Bool → StarSubalgebra ℂ M)

private lemma corner_preimage (a : M) (β : ℂ)
    (hX : CornerSymmetrization.CornerElement
      (factorOperators (vectorState M ξ hfaith hone) f)
      (ambientOperators (vectorState M ξ hfaith hone) R)
      (TracialGNS.vacuum (subalgebraTrace M ξ)) β
      ((subalgebraTrace M ξ).gnsStarAlgHom a)) :
    ∃ q : D, IsStarProjection (f q) ∧ subalgebraTrace M ξ (f q)=β ∧
      f q*a=a ∧ a*f q=a := by
  obtain ⟨_,e,⟨q,hqe⟩,he,het,hel,her⟩ := hX
  change (subalgebraTrace M ξ).gnsStarAlgHom (f q)=e at hqe
  subst e
  have hq := (NormalGNS.gns_projection_iff M (subalgebraTrace M ξ) hfaith (f q)).mp he
  have hqt : subalgebraTrace M ξ (f q)=β := by
    change inner ℂ (TracialGNS.vacuum (subalgebraTrace M ξ))
      ((subalgebraTrace M ξ).gnsStarAlgHom (f q) (TracialGNS.vacuum (subalgebraTrace M ξ)))=β at het
    rw [TracialGNS.left_vacuum] at het
    exact (TracialGNS.inner_vacuum_algebraVector _ _).symm.trans het
  change (subalgebraTrace M ξ).gnsStarAlgHom (f q)*(subalgebraTrace M ξ).gnsStarAlgHom a=
    (subalgebraTrace M ξ).gnsStarAlgHom a at hel
  change (subalgebraTrace M ξ).gnsStarAlgHom a*(subalgebraTrace M ξ).gnsStarAlgHom (f q)=
    (subalgebraTrace M ξ).gnsStarAlgHom a at her
  have hl : f q*a=a := NormalGNS.gns_injective M (subalgebraTrace M ξ) hfaith
    ((map_mul (subalgebraTrace M ξ).gnsStarAlgHom (f q) a).trans hel)
  have hr : a*f q=a := NormalGNS.gns_injective M (subalgebraTrace M ξ) hfaith
    ((map_mul (subalgebraTrace M ξ).gnsStarAlgHom a (f q)).trans her)
  exact ⟨q,hq,hqt,hl,hr⟩

include htr in
theorem corner_bound_oai (T : H →L[ℂ] H) (ε : ℝ) (β : ℂ)
    (hbound : ∀ q : D,IsStarProjection (f q) → subalgebraTrace M ξ (f q)=β →
      ∀ a : M,f q*a=a → a*f q=a →
        ‖T*(a:H →L[ℂ] H)-(a:H →L[ℂ] H)*T‖≤ε*‖a‖)
    (X : (subalgebraTrace M ξ).GNS →L[ℂ] (subalgebraTrace M ξ).GNS)
    (hX : CornerSymmetrization.CornerElement
      (factorOperators (vectorState M ξ hfaith hone) f)
      (ambientOperators (vectorState M ξ hfaith hone) R)
      (TracialGNS.vacuum (subalgebraTrace M ξ)) β X) :
    ‖compression (subalgebraTrace M ξ) M.toStarSubalgebra.subtype ξ (subalgebraTrace_subtype M ξ) T*X-
      X*compression (subalgebraTrace M ξ) M.toStarSubalgebra.subtype ξ (subalgebraTrace_subtype M ξ) T‖≤ε*‖X‖ := by
  have hrange := ambient_range M ξ htr hfaith hone R hX.1
  obtain ⟨a,rfl⟩ := hrange
  have hpreimage := corner_preimage M ξ hfaith hone f R a β hX
  obtain ⟨q,hq,hqt,hl,hr⟩ := hpreimage
  calc
    _ ≤ ‖T*(a:H →L[ℂ] H)-(a:H →L[ℂ] H)*T‖ := norm_commutator_compression_le (subalgebraTrace M ξ)
      M.toStarSubalgebra.subtype ξ (subalgebraTrace_subtype M ξ) T a
    _ ≤ ε*‖a‖ := hbound q hq hqt a hl hr
    _ = _ := by rw [NormalGNS.gns_norm M (subalgebraTrace M ξ) hfaith]

end Kadison.VectorGNS

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.VectorGNS.corner_bound_oai := @OAI.Kadison.VectorGNS.corner_bound_oai
