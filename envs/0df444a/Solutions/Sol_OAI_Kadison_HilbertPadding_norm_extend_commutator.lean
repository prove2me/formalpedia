-- Prove2me | solution 1 for OAI.Kadison.HilbertPadding.norm_extend_commutator
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:15:26.946082+00:00
-- url     : https://prove2.me/submissions/b6da4ac0-22f5-4156-b775-a47d62cb3930

import Mathlib
import Definitions.Def_OAIQ039C010
import Definitions.Def_OAIQ039C011
import Definitions.Def_OAIQ039C012

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteHankel
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
-- module Solutions.OAIQ039_CM.Commutator_HilbertPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

namespace Kadison.HilbertPadding

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma norm_extend_le (E : H →ₗᵢ[ℂ] K) (T : H →L[ℂ] H) : ‖extend E T‖ ≤ ‖T‖ := by
  have he : ‖E.toContinuousLinearMap‖ ≤ 1 := E.norm_toContinuousLinearMap_le
  have he' : ‖E.toContinuousLinearMap.adjoint‖ ≤ 1 := by rw [adjoint.norm_map]; exact he
  calc
    _ ≤ ‖E.toContinuousLinearMap‖*‖T‖*‖E.toContinuousLinearMap.adjoint‖ :=
      (opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1*‖T‖*1 := mul_le_mul (mul_le_mul_of_nonneg_right he (norm_nonneg _))
      he' (norm_nonneg _) (by positivity)
    _ = ‖T‖ := by ring

lemma compress_extend (E : H →ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    FreeCorner.compress E (extend E T)=T := by
  ext x
  change E.toContinuousLinearMap.adjoint (E (T (E.toContinuousLinearMap.adjoint (E x))))=T x
  simp only [FreeCorner.isometry_adjoint_apply]

lemma norm_extend (E : H →ₗᵢ[ℂ] K) (T : H →L[ℂ] H) : ‖extend E T‖=‖T‖ := by
  apply le_antisymm (norm_extend_le E T)
  simpa only [compress_extend] using FreeCorner.norm_compress_le E (extend E T)

lemma extend_commutator (E : H →ₗᵢ[ℂ] K) (T a : H →L[ℂ] H) (b : K →L[ℂ] K)
    (hl : b.comp E.toContinuousLinearMap=E.toContinuousLinearMap.comp a)
    (hr : E.toContinuousLinearMap.adjoint.comp b=a.comp E.toContinuousLinearMap.adjoint) :
    extend E T*b-b*extend E T=extend E (T*a-a*T) := by
  simp only [extend,mul_def,comp_sub,sub_comp,comp_assoc]
  rw [hr,←comp_assoc b,hl]
  simp only [comp_assoc]

lemma norm_extend_commutator_oai (E : H →ₗᵢ[ℂ] K) (T a : H →L[ℂ] H) (b : K →L[ℂ] K)
    (hl : b.comp E.toContinuousLinearMap=E.toContinuousLinearMap.comp a)
    (hr : E.toContinuousLinearMap.adjoint.comp b=a.comp E.toContinuousLinearMap.adjoint) :
    ‖extend E T*b-b*extend E T‖=‖T*a-a*T‖ := by
  rw [extend_commutator E T a b hl hr,norm_extend]

end Kadison.HilbertPadding

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.HilbertPadding.norm_extend_commutator_oai.{u_1, u_2} := @OAI.Kadison.HilbertPadding.norm_extend_commutator_oai.{u_1, u_2}
