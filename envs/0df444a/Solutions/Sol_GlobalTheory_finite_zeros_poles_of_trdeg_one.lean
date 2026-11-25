-- Prove2me | solution 1 for GlobalTheory.finite_zeros_poles_of_trdeg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:52:09.761946+00:00
-- url     : https://prove2.me/submissions/437bdc22-d7c0-4250-89ae-6f9615f52004

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FiniteNormDiscreteNeZeroOfIsDedekindDomain
import Theorems.Thm_GlobalTheory_finite_normDiscrete_ne_zero_of_isDedekindDomain

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
open scoped IntermediateField.algebraAdjoinAdjoin
namespace GlobalTheory
theorem _root_.solution :
    ∀ (F Ω : Type) [Field F] [CharZero F] [Field Ω] [Algebra F Ω] (t : Ω),
      (⊤ : IntermediateField F Ω).FG → Algebra.trdeg F Ω = 1 → Transcendental F t →
      ∀ g : Ω, g ≠ 0 → {v : AddValuation Ω (WithTop ℤ) |
        IsNormDiscrete v ∧ IsTrivOn F v ∧ 0 ≤ v t ∧ v g ≠ 0}.Finite := by
  intro F Ω _ _ _ _ t hfg htr ht g hg
  have hind : AlgebraicIndependent F (fun _ : Unit => t) :=
    algebraicIndependent_unique_type_iff.mpr ht
  have hbasis : IsTranscendenceBasis F (fun _ : Unit => t) :=
    hind.isTranscendenceBasis_of_lift_trdeg_le_of_finite (by rw [htr]; simp)
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin F ({t} : Set Ω)) Ω := by
    have h := hbasis.isAlgebraic_field
    rwa [Set.range_const] at h
  have : Algebra.EssFiniteType F Ω := IntermediateField.fg_top_iff.mp hfg
  have : Algebra.EssFiniteType (IntermediateField.adjoin F ({t} : Set Ω)) Ω := .of_comp F _ _
  have : FiniteDimensional (IntermediateField.adjoin F ({t} : Set Ω)) Ω :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  have : IsPrincipalIdealRing (Algebra.adjoin F ({t} : Set Ω)) :=
    IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental F t ht).toRingEquiv.toRingHom
      (Polynomial.algEquivOfTranscendental F t ht).surjective
  have : IsDedekindDomain (integralClosure (Algebra.adjoin F ({t} : Set Ω)) Ω) :=
    integralClosure.isDedekindDomain _ (IntermediateField.adjoin F ({t} : Set Ω)) Ω
  have : IsFractionRing (integralClosure (Algebra.adjoin F ({t} : Set Ω)) Ω) Ω :=
    integralClosure.isFractionRing_of_finite_extension (IntermediateField.adjoin F ({t} : Set Ω)) Ω
  refine (finite_normDiscrete_ne_zero_of_isDedekindDomain
    (S := integralClosure (Algebra.adjoin F ({t} : Set Ω)) Ω) g hg).subset ?_
  rintro w ⟨hw, hF, hwt, hwg⟩
  refine ⟨hw, fun b => ?_, hwg⟩
  have hA : ∀ x ∈ Algebra.adjoin F ({t} : Set Ω), x ∈ vRing w := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.mp hx]
      exact hwt
    | algebraMap r =>
      by_cases hr : r = 0
      · rw [hr, map_zero]; exact zero_mem _
      · exact (hF r hr).ge
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  have hb : IsIntegral (Algebra.adjoin F ({t} : Set Ω)) (b : Ω) := b.2
  let : Algebra (Algebra.adjoin F ({t} : Set Ω)) (vRing w) :=
    ((algebraMap (Algebra.adjoin F ({t} : Set Ω)) Ω).codRestrict (vRing w)
      (fun x => hA x x.2)).toAlgebra
  have : IsScalarTower (Algebra.adjoin F ({t} : Set Ω)) (vRing w) Ω :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hb' : IsIntegral (vRing w) (b : Ω) := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hb'
  change 0 ≤ w (b : Ω)
  rw [← hy]
  exact y.2
end GlobalTheory
