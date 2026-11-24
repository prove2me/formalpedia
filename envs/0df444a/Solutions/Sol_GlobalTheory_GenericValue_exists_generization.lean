-- Prove2me | solution 1 for GlobalTheory.GenericValue.exists_generization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:18:27.711845+00:00
-- url     : https://prove2.me/submissions/0d5fd330-d866-4aef-9701-2b6589712d85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsAlgHomOfIsTranscendenceBasis
import Theorems.Thm_GlobalTheory_GenericValue_isTranscendenceBasis_genX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GenericValue
open MvPolynomial
variable {K : Type} [Field K]
namespace GlobalTheory.GenericValue
theorem _root_.solution {F I : Type} [Field F] [Algebra K F] (T : I → F) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : Algebra K O)
      (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra K Ω) (r : O →ₐ[K] Ω) (e : F →ₐ[K] Ω) (S : I → O),
      RingHom.ker r = IsLocalRing.maximalIdeal O ∧ AlgebraicIndependent K S ∧ r ∘ S = e ∘ T := by
  let Ω := Gen F I
  let P : I → Polynomial Ω := fun i => Polynomial.C (algebraMap F Ω (T i)) +
    Polynomial.C (genX F I i - algebraMap F Ω (T i)) * Polynomial.X
  have hX : AlgebraicIndependent K (genX F I) :=
    (isTranscendenceBasis_genX F I).1.restrictScalars (algebraMap K F).injective
  have hP : AlgebraicIndependent K P := by
    refine AlgebraicIndependent.of_comp ((Polynomial.aeval (1 : Ω)).restrictScalars K) ?_
    convert hX using 1
    ext i
    simp [P]
  let c : Polynomial Ω →ₐ[K] PowerSeries Ω := (Polynomial.coeToPowerSeries.algHom Ω).restrictScalars K
  have hc : Function.Injective c := by
    intro p q h
    apply Polynomial.coe_injective Ω
    simpa [c] using h
  let r : PowerSeries Ω →ₐ[K] Ω :=
    { PowerSeries.constantCoeff (R := Ω) with commutes' := fun a => by simp [PowerSeries.algebraMap_apply] }
  refine ⟨PowerSeries Ω, inferInstance, inferInstance, inferInstance, inferInstance, Ω, inferInstance, inferInstance,
    inferInstance, r, IsScalarTower.toAlgHom K F Ω, c ∘ P, ?_, hP.map' hc, ?_⟩
  · exact PowerSeries.ker_coeff_eq_max_ideal
  · ext i
    simp [r, c, P]
end GlobalTheory.GenericValue
