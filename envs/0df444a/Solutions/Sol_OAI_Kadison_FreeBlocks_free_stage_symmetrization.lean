-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.free_stage_symmetrization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:01:44.669896+00:00
-- url     : https://prove2.me/submissions/52f44c5a-2bf3-4bf1-9387-7cb64a831e66

import Mathlib
import Definitions.Def_OAIQ039C059
import Theorems.Thm_OAI_Kadison_FreeBlocks_exists_free_symmetrization

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

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeStageAverage
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open UniformSpace MeasureTheory

open scoped ComplexOrder InnerProductSpace

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (htr : ∀ a b : A, t.functional (a*b)=t.functional (b*a))
  (S : Bool → StarSubalgebra ℂ A) (f : D →⋆ₐ[ℂ] A) (hS : S false=f.range)
  (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

lemma baseEmbedding_mem_baseSpace (v : multiplicityLevel t S true 0) :
    baseEmbedding t S hfree v∈baseSpace t S true := by
  induction v using Completion.induction_on with
  | hp =>
      exact (show IsClosed (baseSpace t S true : Set t.functional.GNS) from isClosed_closure).preimage (baseEmbedding t S hfree).continuous
  | ih v =>
      rw [baseEmbedding_coe]
      apply subset_closure
      refine ⟨t.functional.gnsStarAlgHom (factorValue t S true v),
        ⟨factorValue t S true v,v.property,rfl⟩,?_⟩
      simp only [TracialGNS.vacuum,TracialGNS.left_coe,mul_one]

lemma baseProjection_comp_embedding :
    (baseSpace t S true).starProjection.comp (baseEmbedding t S hfree).toContinuousLinearMap=
      (baseEmbedding t S hfree).toContinuousLinearMap := by
  ext x
  exact (baseSpace t S true).starProjection_eq_self_iff.mpr
    (baseEmbedding_mem_baseSpace t S hfree x)

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
  (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)
  (inc : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
  (hinc : ∀ n m (h : n ≤ m) a, φ m (inc h a)=φ n a)

omit [PartialOrder D] [StarOrderedRing D] [∀ n, Nonempty (I n)] in
include hinc in
theorem free_stage_symmetrization_oai (G : t.functional.GNS →L[ℂ] t.functional.GNS)
    (ε : ℝ) (hε : 0≤ε) (β : ℂ) (s : A) (hs : s∈S true)
    (hGD : ∀ a : D, G*t.functional.gnsStarAlgHom (f a)=t.functional.gnsStarAlgHom (f a)*G)
    (hC : ∀ x, CornerSymmetrization.CornerElement
      (factorOperators t f) (ambientOperators t S)
      (TracialGNS.vacuum t.functional) β x → ‖G*x-x*G‖≤ε*‖x‖) :
    ∃ V : t.functional.GNS →L[ℂ] t.functional.GNS,
      ‖V‖≤‖G‖ ∧
      (∀ n u, V*(innerRepresentation t htr f S false hS hfree hgen (TracialGNS.stageUnitary (φ n) u):
        t.functional.GNS →L[ℂ] t.functional.GNS)=
        (innerRepresentation t htr f S false hS hfree hgen (TracialGNS.stageUnitary (φ n) u):
          t.functional.GNS →L[ℂ] t.functional.GNS)*V) ∧
      (∀ a : D, V*t.functional.gnsStarAlgHom (f a)=t.functional.gnsStarAlgHom (f a)*V) ∧
      (∀ x, CornerSymmetrization.CornerElement
        (factorOperators t f) (ambientOperators t S)
        (TracialGNS.vacuum t.functional) β x → ‖V*x-x*V‖≤ε*‖x‖) ∧
      (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := multiplicityLevel t S true 0) (F := t.functional.GNS)
        (baseEmbedding t S hfree).toContinuousLinearMap).comp
        ((V*t.functional.gnsStarAlgHom s-t.functional.gnsStarAlgHom s*V).comp
          (baseEmbedding t S hfree).toContinuousLinearMap)=
      (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := multiplicityLevel t S true 0) (F := t.functional.GNS)
        (baseEmbedding t S hfree).toContinuousLinearMap).comp
        ((G*t.functional.gnsStarAlgHom s-t.functional.gnsStarAlgHom s*G).comp
          (baseEmbedding t S hfree).toContinuousLinearMap) := by
  obtain ⟨V,hV,hVU,hVD,hVC,_,hVe⟩ := exists_free_symmetrization t htr f S false true hS
    hfree hgen I φ inc hinc G hGD ε hε β hC s hs (by decide)
  refine ⟨V,hV,hVU,hVD,hVC,?_⟩
  let F := (baseEmbedding t S hfree).toContinuousLinearMap
  let F' := ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := multiplicityLevel t S true 0) (F := t.functional.GNS) F
  let Q := (baseSpace t S true).starProjection
  have hQF : Q.comp F=F := baseProjection_comp_embedding t S hfree
  have hFQ : F'.comp Q=F' := by
    have hh := congrArg (ContinuousLinearMap.adjoint (𝕜:=ℂ)
      (E := multiplicityLevel t S true 0) (F := t.functional.GNS)) hQF
    have hQa : Q.adjoint=Q := (isSelfAdjoint_starProjection (baseSpace t S true)).star_eq
    simpa only [ContinuousLinearMap.adjoint_comp,hQa] using hh
  have hh := congrArg (fun a : t.functional.GNS →L[ℂ] t.functional.GNS => F'.comp (a.comp F)) hVe
  change F'.comp ((Q.comp ((V*t.functional.gnsStarAlgHom s-t.functional.gnsStarAlgHom s*V).comp Q)).comp F)=
    F'.comp ((Q.comp ((G*t.functional.gnsStarAlgHom s-t.functional.gnsStarAlgHom s*G).comp Q)).comp F) at hh
  have hc (X : t.functional.GNS →L[ℂ] t.functional.GNS) :
      F'.comp ((Q.comp (X.comp Q)).comp F)=F'.comp (X.comp F) := by
    calc
      _ = (F'.comp Q).comp (X.comp (Q.comp F)) := by
        simp only [ContinuousLinearMap.comp_assoc]
      _ = _ := by rw [hFQ,hQF]
  rw [hc,hc] at hh
  exact hh

end Kadison.FreeBlocks

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.FreeBlocks.free_stage_symmetrization_oai.{u_1} := @OAI.Kadison.FreeBlocks.free_stage_symmetrization_oai.{u_1}
