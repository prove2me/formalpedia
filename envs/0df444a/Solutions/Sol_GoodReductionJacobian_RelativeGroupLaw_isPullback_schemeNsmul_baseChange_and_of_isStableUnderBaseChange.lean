-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/a356a3aa-b794-5c83-99ad-e53fd27f81b2

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_baseChange_schemeNsmul_comp_fst_and_eq_pullback_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian

theorem solution
    {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) (n : ℕ) :
    IsPullback (pullback.fst f ι) ((G.baseChange ι).schemeNsmul n) (G.schemeNsmul n) (pullback.fst f ι) ∧
    ∀ P : MorphismProperty Scheme.{u}, P.IsStableUnderBaseChange →
      P (G.schemeNsmul n) → P ((G.baseChange ι).schemeNsmul n) := by
  obtain ⟨hfst, hsnd, -⟩ := GoodReductionJacobian.RelativeGroupLaw.baseChange_schemeNsmul_comp_fst_and_eq_pullback_map ι G n
  have sq : IsPullback (pullback.snd f ι) (pullback.fst f ι) ι f := (IsPullback.of_hasPullback f ι).flip
  have big : IsPullback ((G.baseChange ι).schemeNsmul n ≫ pullback.snd f ι) (pullback.fst f ι) ι (G.schemeNsmul n ≫ f) := by
    rw [hsnd, G.schemeNsmul_over]
    exact sq
  have hP : IsPullback (pullback.fst f ι) ((G.baseChange ι).schemeNsmul n) (G.schemeNsmul n) (pullback.fst f ι) :=
    (IsPullback.of_right big hfst sq).flip
  refine ⟨hP, fun P hPst h => ?_⟩
  haveI := hPst
  exact P.of_isPullback hP h

end S_GoodReductionJacobian_RelativeGroupLaw_isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange (solution)
