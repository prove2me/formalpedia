-- Prove2me | solution 1 for GlobalTheory.ResidueCharacterDense.psi_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:39:38.380249+00:00
-- url     : https://prove2.me/submissions/cba8c2a9-0510-497c-82a3-703f35d2c11a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
import Theorems.Thm_GlobalTheory_ResidueCharacterDense_trace_base_change

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResidueCharacterDense
open Formalism.MainNotions.S.Loc
namespace GlobalTheory.ResidueCharacterDense
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hE : Module.finrank F E = 2) {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
    (A : LocAt F E sig p) [Fact (resChar p).Prime] (x : E) :
    ∃ a : ℚ, (∃ n : ℕ, a.den = (resChar p) ^ n) ∧
      ‖Algebra.trace ℚ_[resChar p] A.Fp (A.ιF (Algebra.trace F E x)) - (a : ℚ_[resChar p])‖ ≤ 1 ∧
      A.psiE (A.ιE x) = Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) := by
  obtain ⟨a, h1, h2, h3⟩ := A.psiE_def (A.ιE x)
  refine ⟨a, h1, ?_, h3⟩
  have := A.free
  have := A.qlFin
  have : Module.Finite A.Fp A.Ep := Module.finite_of_finrank_pos (by rw [A.rank]; omega)
  letI := ((algebraMap A.Fp A.Ep).comp (algebraMap ℚ_[resChar p] A.Fp)).toAlgebra
  have : IsScalarTower ℚ_[resChar p] A.Fp A.Ep := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [← trace_base_change hE A.rank A.ιF A.ιE A.compat A.span x, Algebra.trace_trace]
  exact h2
end GlobalTheory.ResidueCharacterDense
