-- Prove2me | solution 1 for GlobalTheory.addVal_eq_of_associated_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:25:58.377141+00:00
-- url     : https://prove2.me/submissions/a913b6c7-9db2-4b5f-80c2-46c182910dd9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAE
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsPtOrdEqAddValuation

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [Algebra O A] (ζ : Pts O A) (u : AddValuation A (WithTop ℤ))
    (hz : ∀ s : As O A, s ∉ ζ.asIdeal → u (s : A) = 0) (a b : As O A)
    (hab : Associated (algebraMap (As O A) (Loc ζ) a) (algebraMap (As O A) (Loc ζ) b)) :
    u (a : A) = u (b : A) := by
  obtain ⟨w, hw⟩ := hab
  obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.surj ζ.asIdeal.primeCompl (w : Loc ζ)
  have ht : IsUnit (algebraMap (As O A) (Loc ζ) t) := IsLocalization.map_units _ t
  have hs : s ∉ ζ.asIdeal := by
    have h1 : IsUnit (algebraMap (As O A) (Loc ζ) s) := by
      have := w.isUnit.mul ht
      simpa only [hst] using this
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal s).1 h1
  have h2 : algebraMap (As O A) (Loc ζ) (a * s) = algebraMap (As O A) (Loc ζ) (b * t) := by
    rw [map_mul, map_mul, ← hw, mul_assoc]
    exact congrArg _ hst.symm
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists ζ.asIdeal.primeCompl (Loc ζ)).1 h2
  have h3 := congrArg (fun x : As O A => u (x : A)) hc
  simp only [MulMemClass.coe_mul, AddValuation.map_mul] at h3
  rw [hz _ c.2, hz _ hs, hz _ t.2] at h3
  simpa using h3
end GlobalTheory
