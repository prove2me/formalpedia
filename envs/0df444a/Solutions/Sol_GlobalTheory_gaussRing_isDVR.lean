-- Prove2me | solution 1 for GlobalTheory.gaussRing_isDVR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:40:27.422408+00:00
-- url     : https://prove2.me/submissions/e4057853-0805-4f20-a507-30aabb5157de

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsMvPolynomialSubMapMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open IsLocalRing
namespace GlobalTheory
theorem _root_.solution {σ : Type} [Finite σ] (O₁ : Type) [CommRing O₁] [IsDomain O₁]
    [IsDiscreteValuationRing O₁] (P : Ideal (MvPolynomial σ O₁)) [P.IsPrime]
    (hP : P = Ideal.map MvPolynomial.C (maximalIdeal O₁))
    (O₂ : Type) [CommRing O₂] [IsLocalRing O₂] [Algebra (MvPolynomial σ O₁) O₂]
    [IsLocalization.AtPrime O₂ P] : ∃ _ : IsDomain O₂, IsDiscreteValuationRing O₂ := by
  have hd : IsDomain O₂ :=
    IsLocalization.isDomain_of_le_nonZeroDivisors O₂ P.primeCompl_le_nonZeroDivisors
  refine ⟨hd, ?_⟩
  have : IsNoetherianRing O₂ :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have hinj := IsLocalization.injective O₂ (M := P.primeCompl) P.primeCompl_le_nonZeroDivisors
  obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal (maximalIdeal O₁)
  have hg' : maximalIdeal O₁ = Ideal.span {g} := hg
  have hmax : maximalIdeal O₂ =
      Ideal.span {algebraMap (MvPolynomial σ O₁) O₂ (MvPolynomial.C g)} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P O₂]
    conv_lhs => rw [hP]
    rw [hg', Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  have hnf : ¬ IsField O₂ := by
    rw [isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
    intro h
    have h1 := hinj (h.trans (map_zero _).symm)
    have h2 : g = 0 := by simpa using h1
    apply IsDiscreteValuationRing.not_a_field O₁
    rw [hg', h2]; simp
  refine ((IsDiscreteValuationRing.TFAE O₂ hnf).out 0 4).mpr ?_
  rw [hmax]
  exact ⟨⟨_, rfl⟩⟩
end GlobalTheory
