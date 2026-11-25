-- Prove2me | solution 1 for GlobalTheory.finite_of_isClosed_splitTorus_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:09:45.929213+00:00
-- url     : https://prove2.me/submissions/0da809a3-1b2d-4946-ac96-468076bba78e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteOfIsClosedSplitTorusOfPowEqOne
import Theorems.Thm_GlobalTheory_range_splitTorusPoint_left
import Theorems.Thm_GlobalTheory_finite_of_isClosed_torusZariski_of_pow_eq_one


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
theorem _root_.solution :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
      [Module.Finite ℤ X] (n : ℕ), n.Prime → (n : k) ≠ 0 →
      ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X))
        (Z : Set (splitTorus (Sp k) X).left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) →
        (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C := by
  intro k _ _ X _ _ _ n hp hn C Z hZ hC htors
  haveI : NeZero (n : k) := ⟨hn⟩
  let e := splitTorusPointEquiv k X
  have hcl : @IsClosed _ (torusZariski k X)
      (C.comap e.toMonoidHom : Set (Multiplicative X →* kˣ)) := by
    refine isClosed_induced_iff.2 ⟨(torusIso k X).hom ⁻¹' Z,
      hZ.preimage (torusIso k X).hom.continuous, ?_⟩
    ext t
    change _ ↔ splitTorusPoint t ∈ C
    rw [hC, range_splitTorusPoint_left, Set.singleton_subset_iff]
    rfl
  have h := finite_of_isClosed_torusZariski_of_pow_eq_one hp.two_le hcl fun s hs h1 =>
    e.injective (by rw [map_one]; exact htors _ hs (by rw [← map_pow, h1, map_one]))
  have e' : C.comap e.toMonoidHom ≃ C := e.toEquiv.subtypeEquiv fun _ => Iff.rfl
  exact e'.finite_iff.1 h.1
end GlobalTheory
