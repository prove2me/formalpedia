-- Prove2me | solution 1 for OAI.Kadison.MatrixCornerImplementation.exists_matrix_corner_intertwiner
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T15:25:14.736612+00:00
-- url     : https://prove2.me/submissions/2101507a-b7db-48b4-9d6d-ff88599d79fa

import Mathlib
import Definitions.Def_OAIQ039C054
import Definitions.Def_OAIQ039C057
import Theorems.Thm_OAI_Kadison_CyclicSpatial_exists_embedded_cyclic_intertwiner
import Theorems.Thm_OAI_Kadison_MatrixCornerExtension_extend_intertwines
import Theorems.Thm_OAI_Kadison_MatrixCornerExtension_norm_sub_extend_le
import Theorems.Thm_OAI_Kadison_ReducingRepresentation_corner_dense

section
-- module Solutions.OAIQ039_CM.Commutator_ConcreteCornerVonNeumann
attribute [-instance] _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.ConcreteCorner

open MatrixCornerHilbert ReducingRepresentation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

variable {M} {p : Algebra M} (hp : IsStarProjection p)

lemma representation_project (a : Corner hp) (x : H) :
    (representation hp a (project hp x):H)=((a:Algebra M):H →L[ℂ] H) x := by
  change ((a:Algebra M):H →L[ℂ] H) ((p:H →L[ℂ] H) x)=((a:Algebra M):H →L[ℂ] H) x
  exact congrArg (fun b : Algebra M => (b:H →L[ℂ] H) x) a.property.2

lemma representation_injective : Function.Injective (representation hp) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  ext x
  have he := congrArg (fun T : Space hp →L[ℂ] Space hp => (T (project hp x):H)) h
  simpa only [representation_project] using he

variable (R : H →L[ℂ] H) (hR : R∈M.commutant)

lemma vonNeumann_range : Set.range (representation hp)=
    (vonNeumann hp : Set (Space hp →L[ℂ] Space hp)) := rfl

end Kadison.ConcreteCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CornerCyclicImplementation
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

namespace Kadison.MatrixCornerImplementation

open MatrixCornerHilbert ReducingRepresentation ConcreteCorner MatrixCornerExtension

variable {H K ι : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [Fintype ι] [DecidableEq ι]

variable (M : VonNeumannAlgebra H)
  (σ : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (j : K →ₗᵢ[ℂ] H)
  (hj : ∀ a x, j (σ a x)=inclusion M a (j x))

variable {p : Algebra M} (hp : IsStarProjection p)

lemma cornerEmbedding_intertwines (a : Corner hp) (x : fixedSpace (σ p)) :
    cornerEmbedding M σ j hj hp (corner σ hp a x)=
      representation hp a (cornerEmbedding M σ j hj hp x) := by
  apply Subtype.ext
  exact hj (a:Algebra M) (x:K)

variable (G : K →L[ℂ] H) (hGp : ∀ x, G (σ p x)=inclusion M p (G x))

omit [Fintype ι] [DecidableEq ι] in
lemma corner_derivation_bound {ε : ℝ} (hε : 0≤ε)
    (hδ : ∀ a : Corner hp, ‖G.comp (σ (a:Algebra M))-(inclusion M (a:Algebra M)).comp G‖≤ε*‖a‖)
    (a : Corner hp) :
    ‖(cornerMap σ (inclusion M) G hGp).comp (corner σ hp a)-
      (representation hp a).comp (cornerMap σ (inclusion M) G hGp)‖≤ε*‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hε (norm_nonneg _))
  intro x
  change ‖G (σ (a:Algebra M) (x:K))-inclusion M (a:Algebra M) (G (x:K))‖≤(ε*‖a‖)*‖x‖
  exact ((G.comp (σ (a:Algebra M))-(inclusion M (a:Algebra M)).comp G).le_opNorm (x:K)).trans
    (mul_le_mul_of_nonneg_right (hδ a) (norm_nonneg _))

include hj hGp in
theorem exists_matrix_corner_intertwiner_oai (v : ι → Algebra M)
    (hcol : ∀ i j, star (v i)*v j=if i=j then p else 0)
    (hinit : ∀ i, p*star (v i)=star (v i))
    (htotal : ∑ i, v i*star (v i)=1)
    (hGv : ∀ i x, G (σ (v i) x)=inclusion M (v i) (G x))
    (Ω : K) (hΩ : DenseRange (fun a : Algebra M => σ a Ω)) (hpΩ : σ p Ω=Ω)
    {ε : ℝ} (hε : 0≤ε)
    (hδ : ∀ a : Corner hp, ‖G.comp (σ (a:Algebra M))-(inclusion M (a:Algebra M)).comp G‖≤ε*‖a‖) :
    ∃ T : K →L[ℂ] H, (∀ a : Algebra M, T.comp (σ a)=(inclusion M a).comp T) ∧
      ‖G-T‖≤16*ε := by
  let Ωp : fixedSpace (σ p) := ⟨Ω,(mem_fixedSpace _ _).mpr hpΩ⟩
  obtain ⟨T,hT,hn⟩ := CyclicSpatial.exists_embedded_cyclic_intertwiner
    (corner σ hp) (representation hp) (cornerEmbedding M σ j hj hp)
    (cornerEmbedding_intertwines M σ j hj hp) (vonNeumann hp)
    (representation_injective hp) (vonNeumann_range hp)
    (cornerMap σ (inclusion M) G hGp) Ωp (corner_dense σ hp Ω hΩ hpΩ) hε
    (corner_derivation_bound M σ hp G hGp hε hδ)
  refine ⟨extend σ (inclusion M) v hcol hinit htotal T,?_,?_⟩
  · exact extend_intertwines σ (inclusion M) hp v hcol hinit htotal T hT
  · exact (norm_sub_extend_le σ (inclusion M) v hcol hinit htotal G hGp T hGv).trans hn

end Kadison.MatrixCornerImplementation

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.MatrixCornerImplementation.exists_matrix_corner_intertwiner_oai.{u_1, u_2, u_3} := @OAI.Kadison.MatrixCornerImplementation.exists_matrix_corner_intertwiner_oai.{u_1, u_2, u_3}
