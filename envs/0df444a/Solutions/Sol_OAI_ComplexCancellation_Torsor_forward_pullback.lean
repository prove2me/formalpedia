-- Prove2me | solution 1 for OAI.ComplexCancellation.Torsor.forward_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:21:40.759576+00:00
-- url     : https://prove2.me/submissions/230c4aa9-166a-48a5-9d19-dbad9db9695c

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/TorsorFrame.lean:L121-L146
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.Torsor.forward_pullback. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
import Definitions.Def_OAI_Algebra_AffineCancellation_Quadric
import Definitions.Def_OAI_Algebra_AffineCancellation_Degeneration
import Definitions.Def_OAI_Algebra_AffineCancellation_Rees
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesReduction
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DegenerationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveInvariant
import Definitions.Def_OAI_Algebra_AffineCancellation_RelativeClearing
import Definitions.Def_OAI_Algebra_AffineCancellation_FractionDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DifferentialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_RationalSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_Modification
import Definitions.Def_OAI_Algebra_AffineCancellation_Bundle
import Definitions.Def_OAI_Algebra_AffineCancellation_ModificationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Extraction
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveObstruction
import Definitions.Def_OAI_Algebra_AffineCancellation_TorsorFrame

-- ---- from OAI.Algebra.AffineCancellation.TorsorFrame ----
namespace OAI

noncomputable section

namespace ComplexCancellation.Torsor
open LaurentPolynomial
open MvPolynomial (X aeval aeval_X eval₂Hom_C eval₂Hom_X)
variable {P : Type*} [CommRing P] [Algebra ℂ P]
variable (ρ : Degeneration.G →ₐ[ℂ] P)
variable (Q : Frame ρ)
lemma base_p_ne_zero (hρ : Function.Injective ρ) : base ρ Degeneration.p ≠ 0 := by
  have hp : Degeneration.p ≠ 0 := Degeneration.p_regular.ne_zero
  change C (ρ Degeneration.p) ≠ 0
  intro hz
  have hn : ρ Degeneration.p ≠ 0 := by simpa only [map_zero] using hρ.ne hp
  apply hn
  have he := congrArg (fun z : L (P := P) => z.coeff 0) hz
  simpa [LaurentPolynomial.C_apply] using he
variable [IsDomain P]
lemma forward_pullback (hρ : Function.Injective ρ) : (forward ρ Q).comp Bundle.pullback=base ρ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change forward ρ Q (Bundle.pullback (Degeneration.π (X i)))=base ρ (Degeneration.π (X i))
  rw [Bundle.pullback_π]
  simp only [Bundle.eval,MvPolynomial.aeval_X,Bundle.values]
  fin_cases i
  · change forward ρ Q Bundle.τ=base ρ Degeneration.p
    exact forward_τ ρ Q
  · change forward ρ Q (Bundle.j (Bundle.inclusion Quadric.s))=base ρ Degeneration.s
    rw [forward_j]
    simpa only [AlgHom.comp_apply,Degeneration.coefficientMap_s] using DFunLike.congr_fun (frameMap_inclusion ρ Q) Quadric.s
  · change forward ρ Q (Bundle.j Determinant.u)=base ρ Degeneration.u
    rw [forward_j,frameMap_u]
    rfl
  · change forward ρ Q (Bundle.j Bundle.C₁*Bundle.V)=base ρ Degeneration.F
    rw [map_mul,forward_j,forward_V]
    apply mul_left_cancel₀ (pow_ne_zero 2 (base_p_ne_zero ρ hρ))
    calc _ = frameMap ρ Q Bundle.C₁*(base ρ Degeneration.p^2*vb ρ Q) := by ring
      _ = _ := by rw [vb_equation,← frame_f]
  · change forward ρ Q (Bundle.j (Determinant.b^2)*Bundle.V)=base ρ Degeneration.J
    rw [map_mul,forward_j,forward_V]
    apply mul_left_cancel₀ (pow_ne_zero 2 (base_p_ne_zero ρ hρ))
    calc _ = frameMap ρ Q (Determinant.b^2)*(base ρ Degeneration.p^2*vb ρ Q) := by ring
      _ = _ := by rw [vb_equation,← frame_g]
end ComplexCancellation.Torsor

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.Torsor
open LaurentPolynomial
open MvPolynomial


theorem solution : type_of% @_root_.OAI.ComplexCancellation.Torsor.forward_pullback := @_root_.OAI.ComplexCancellation.Torsor.forward_pullback
