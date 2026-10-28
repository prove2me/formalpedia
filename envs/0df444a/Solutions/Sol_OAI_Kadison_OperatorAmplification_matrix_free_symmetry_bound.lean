-- Prove2me | solution 1 for OAI.Kadison.OperatorAmplification.matrix_free_symmetry_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:07:53.918521+00:00
-- url     : https://prove2.me/submissions/2e1ffba8-16e7-462b-9913-91b6531f8217

import Mathlib
import Definitions.Def_OAIQ039C063
import Definitions.Def_OAIQ039C067
import Theorems.Thm_OAI_Kadison_MatrixGNS_trace_mul
import Theorems.Thm_OAI_Kadison_MatrixGNS_trace_one
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixGNSOperator_commutator_norm
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixGNSOperator_commutes
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixGNSOperator_small_real_corner
import Theorems.Thm_OAI_Kadison_TracialSequence_FreeCornerPosition_symmetry_bound

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixFreeSymmetry
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.OperatorAmplification

open TracialSequence FreeMoments

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] [Nonempty ι] (i₀ : ι) (M Q : VonNeumannAlgebra H) (hQM : Q≤M)

attribute [local instance] OAI.Kadison.OperatorAmplification.matrixFreeSymmetryDecidableEq
variable (τ : M →ₚ[ℂ] ℂ)

variable (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤atTop)

variable (F : FreeCornerPosition (MatrixGNS.trace (ι:=ι) τ) ω (matrixVonNeumann ι i₀ Q) (matrixInclusion ι i₀ M Q hQM))

include hω F in
theorem matrix_free_symmetry_bound_oai (hQ : FactorCorner.IsFactor Q)
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (T : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    (hTQ : ∀ q : Q,T*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom (NormalSubalgebra.inclusion M Q hQM q))=
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom (NormalSubalgebra.inclusion M Q hQM q))*T)
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ a : M,‖T*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*T‖ ≤ c*‖a‖)
    (s : unitary (CStarMatrix ι ι M)) (hs0 : (MatrixGNS.trace (ι:=ι) τ) (s:CStarMatrix ι ι M)=0)
    (hs2 : (s:CStarMatrix ι ι M)*(s:CStarMatrix ι ι M)=1) :
    ‖diagonal (H:=SumSpace (H:=τ.GNS) ι) ι T*MatrixGNS.representation τ (s:CStarMatrix ι ι M)-
      MatrixGNS.representation τ (s:CStarMatrix ι ι M)*diagonal (H:=SumSpace (H:=τ.GNS) ι) ι T‖≤1040*c := by
  let b : ℝ := (Fintype.card ι : ℝ)⁻¹
  have hn : (1:ℝ)≤Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hb : 0<b := inv_pos.mpr (lt_of_lt_of_le zero_lt_one hn)
  have hb1 : b≤1 := (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hn)).mpr hn
  have hg := FreeCornerPosition.symmetry_bound (MatrixGNS.trace (ι:=ι) τ) ω (matrixVonNeumann ι i₀ Q) (matrixInclusion ι i₀ M Q hQM) F
    (MatrixGNS.trace_mul τ hτ) hω (MatrixGNS.trace_one τ h1) (matrixGNSOperator ι M τ T)
    (matrixGNSOperator_commutes ι i₀ M Q hQM τ T hTQ)
    hb.le hc (show 0<b/2 by positivity) (show b/2≤1 by linarith)
    (show b/2<b by linarith)
    (matrixGNSOperator_small_real_corner ι i₀ M Q hQM τ hQ hτ hfaith h1 T hTQ hc hbound)
    s hs0 hs2
  exact (matrixGNSOperator_commutator_norm ι M τ T (s:CStarMatrix ι ι M)).ge.trans hg

end Kadison.OperatorAmplification

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.OperatorAmplification.matrix_free_symmetry_bound_oai := @OAI.Kadison.OperatorAmplification.matrix_free_symmetry_bound_oai
