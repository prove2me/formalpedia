-- Prove2me | solution 1 for GlobalTheory.T.hermitian_form_finite_zeros_on_line_cmExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:12:24.312797+00:00
-- url     : https://prove2.me/submissions/f5fb88c6-611e-4cac-ab00-a413debadc3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HermitianFormFiniteZerosOnLineCmExt
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HermitianFormFiniteZerosOnLineCmExtStatement
import Theorems.Thm_GlobalTheory_HermLineZeros_finite_zeros_on_line


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), 1 ≤ M → ∀ (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (K : Type) [Field K] [Algebra F K], ∃ y : Fin M → K ⊗[F] E, ∀ x : Fin M → K ⊗[F] E, {t : K | qR K σ J (x + t • y) = 0}.Finite := by
  first | exact @GlobalTheory.HermLineZeros.finite_zeros_on_line | exact GlobalTheory.HermLineZeros.finite_zeros_on_line | (intros; apply GlobalTheory.HermLineZeros.finite_zeros_on_line <;> assumption)
end _root_.GlobalTheory.T
