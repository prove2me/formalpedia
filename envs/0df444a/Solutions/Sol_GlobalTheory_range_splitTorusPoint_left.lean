-- Prove2me | solution 1 for GlobalTheory.range_splitTorusPoint_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:00:24.985264+00:00
-- url     : https://prove2.me/submissions/42cb2cf9-1471-4753-84d9-20a26e4a8aee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteOfIsClosedSplitTorusOfPowEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open GlobalTheory
variable {k : Type} [Field k] {X : Type} [AddCommGroup X]
attribute [local instance] zuAlgebra
open scoped AlgebraMonoidAlgebra
namespace GlobalTheory
theorem _root_.solution (t : Multiplicative X →* kˣ) :
    Set.range (splitTorusPoint t).left = {(torusIso k X).hom (torusPrime t)} := by
  have h : ∀ p, (splitTorusPoint t).left p = (torusIso k X).hom (torusPrime t) := fun p => by
    have hp : p = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) :=
      Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [hp]
    rfl
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact h p
  · rintro rfl
    exact ⟨_, h (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)⟩
end GlobalTheory
