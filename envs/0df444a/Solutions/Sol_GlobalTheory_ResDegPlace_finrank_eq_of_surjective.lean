-- Prove2me | solution 1 for GlobalTheory.ResDegPlace.finrank_eq_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:12:38.190029+00:00
-- url     : https://prove2.me/submissions/26b8e770-a072-45a1-9190-e5139bc2f000

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAE
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FdegEqFinrankResidueField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResDegPlace
open IsLocalRing
namespace GlobalTheory.ResDegPlace
theorem _root_.solution {S₀ S k K k' K' : Type*} [CommRing S₀] [CommRing S] [Field k]
    [Field K] [Field k'] [Field K'] [Algebra k K] [Algebra k' K'] (j : S₀ →+* S)
    (p₀ : S₀ →+* k) (q₀ : S₀ →+* k') (p : S →+* K) (q : S →+* K')
    (hp₀ : Function.Surjective p₀) (hq₀ : Function.Surjective q₀)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hker : ∀ x, p x = 0 ↔ q x = 0)
    (h₁ : ∀ r, algebraMap k K (p₀ r) = p (j r)) (h₂ : ∀ r, algebraMap k' K' (q₀ r) = q (j r)) :
    Module.finrank k K = Module.finrank k' K' := by
  have hk : RingHom.ker p = RingHom.ker q := by
    ext x; simp only [RingHom.mem_ker]; exact hker x
  have hk₀ : RingHom.ker p₀ = RingHom.ker q₀ := by
    ext x
    simp only [RingHom.mem_ker]
    rw [← map_eq_zero_iff _ (algebraMap k K).injective, h₁, hker, ← h₂,
      map_eq_zero_iff _ (algebraMap k' K').injective]
  let e : K ≃+* K' := (RingHom.quotientKerEquivOfSurjective hp).symm.trans
    ((Ideal.quotEquivOfEq hk).trans (RingHom.quotientKerEquivOfSurjective hq))
  let e₀ : k ≃+* k' := (RingHom.quotientKerEquivOfSurjective hp₀).symm.trans
    ((Ideal.quotEquivOfEq hk₀).trans (RingHom.quotientKerEquivOfSurjective hq₀))
  have he : ∀ x, e (p x) = q x := fun x => by
    have : (RingHom.quotientKerEquivOfSurjective hp).symm (p x) = Ideal.Quotient.mk _ x := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp only [e, RingEquiv.trans_apply, this]; rfl
  have he₀ : ∀ x, e₀ (p₀ x) = q₀ x := fun x => by
    have : (RingHom.quotientKerEquivOfSurjective hp₀).symm (p₀ x) = Ideal.Quotient.mk _ x := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp only [e₀, RingEquiv.trans_apply, this]; rfl
  refine Algebra.finrank_eq_of_equiv_equiv e₀ e ?_
  ext y
  obtain ⟨r, rfl⟩ := hp₀ y
  change algebraMap k' K' (e₀ (p₀ r)) = e (algebraMap k K (p₀ r))
  rw [he₀, h₂, h₁, he]
end GlobalTheory.ResDegPlace
