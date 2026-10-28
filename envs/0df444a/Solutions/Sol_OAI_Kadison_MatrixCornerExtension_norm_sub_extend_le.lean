-- Prove2me | solution 1 for OAI.Kadison.MatrixCornerExtension.norm_sub_extend_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:45:37.353834+00:00
-- url     : https://prove2.me/submissions/909e663c-fb00-406d-8e85-48c17bf3cf9d

import Mathlib
import Definitions.Def_OAIQ039C038

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertModuleExtension
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ENNReal

open ContinuousLinearMap

namespace Kadison.HilbertModuleExtension

variable {ι E F K H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (V : ι → E →ₗᵢ[ℂ] K) (W : ι → F →ₗᵢ[ℂ] H)
  (hV : IsHilbertSum ℂ (fun _ : ι => E) V) (hW : IsHilbertSum ℂ (fun _ : ι => F) W)

omit [CompleteSpace E] [CompleteSpace F] in
lemma extend_norm_le (T : E →L[ℂ] F) : ‖extend V W hV hW T‖ ≤ ‖T‖ := by
  apply opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖hW.linearIsometryEquiv.symm
    (lp.mapCLM 2 (fun _ : ι => T) (norm_nonneg T) (fun _ => le_rfl)
      (hV.linearIsometryEquiv x))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact ((lp.mapCLM 2 (fun _ : ι => T) (norm_nonneg T) (fun _ => le_rfl)).le_of_opNorm_le
    (lp.norm_mapCLM_le 2 (fun _ : ι => T) (norm_nonneg T) (fun _ => le_rfl)) _).trans_eq
      (by rw [LinearIsometryEquiv.norm_map])

omit [CompleteSpace E] [CompleteSpace F] in
lemma extend_sub (T R : E →L[ℂ] F) :
    extend V W hV hW (T-R)=extend V W hV hW T-extend V W hV hW R := by
  apply ActualHilbertSum.map_ext (fun _ : ι => E) V hV
  intro i
  ext x
  simp only [comp_apply,ActualHilbertSum.insert,LinearIsometry.coe_toContinuousLinearMap,
    extend_insert,sub_apply,map_sub]

include hV hW in
omit [CompleteSpace E] [CompleteSpace F] in
lemma eq_extend (G : K →L[ℂ] H) (T : E →L[ℂ] F)
    (h : ∀ i x, G (V i x)=W i (T x)) : G=extend V W hV hW T := by
  apply ActualHilbertSum.map_ext (fun _ : ι => E) V hV
  intro i
  ext x
  exact (h i x).trans (extend_insert V W hV hW T i x).symm

include hV hW in
omit [CompleteSpace E] [CompleteSpace F] in
lemma norm_sub_extend_le (G : K →L[ℂ] H) (T R : E →L[ℂ] F)
    (h : ∀ i x, G (V i x)=W i (R x)) :
    ‖G-extend V W hV hW T‖ ≤ ‖R-T‖ := by
  rw [eq_extend V W hV hW G R h,←extend_sub]
  exact extend_norm_le V W hV hW (R-T)

end Kadison.HilbertModuleExtension

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixCornerExtension
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

namespace Kadison.MatrixCornerExtension

open MatrixCornerHilbert

variable {A K H ι : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [DecidableEq ι]

variable (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

variable {p : A} (hp : IsStarProjection p) (v : ι → A)
  (hcol : ∀ i j, star (v i)*v j=if i=j then p else 0)
  (hinit : ∀ i, p*star (v i)=star (v i))
  (htotal : ∑ i, v i*star (v i)=1)

variable (G : K →L[ℂ] H) (hGp : ∀ x, G (σ p x)=ρ p (G x))

lemma norm_sub_extend_le_oai (T : fixedSpace (σ p) →L[ℂ] fixedSpace (ρ p))
    (hGv : ∀ i x, G (σ (v i) x)=ρ (v i) (G x)) :
    ‖G-extend σ ρ v hcol hinit htotal T‖≤‖cornerMap σ ρ G hGp-T‖ := by
  apply HilbertModuleExtension.norm_sub_extend_le
  intro i x
  exact hGv i x

end Kadison.MatrixCornerExtension

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Kadison.MatrixCornerExtension.norm_sub_extend_le_oai.{u_1, u_2, u_3, u_4} := @OAI.Kadison.MatrixCornerExtension.norm_sub_extend_le_oai.{u_1, u_2, u_3, u_4}
