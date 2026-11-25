-- Prove2me | solution 1 for GlobalTheory.Published.AbMulNSt.dim_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:14:23.962458+00:00
-- url     : https://prove2.me/submissions/e563c68c-0ecf-44f5-b400-6a3225d83373

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__DimEqZero_40b4adf5f58b53e3

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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.AbMulNSt
variable {k : Type} [Field k] [IsAlgClosed k] {B : Over (Sp k)} [GrpObj B] {g n : ℕ}
namespace GlobalTheory.Published.AbMulNSt
theorem _root_.solution (h : AbMulNSt) (hB : IsAbelianScheme B) (hg : SmoothOfRelativeDimension g B.hom)
    (hn : (n : k) ≠ 0) (h2 : 2 ≤ n) (ht : ∀ x : 𝟙_ (Over (Sp k)) ⟶ B, x ^ n = 1 → x = 1) :
    g = 0 := by
  have : Unique {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} :=
    ⟨⟨⟨1, one_pow n⟩⟩, fun x => Subtype.ext (ht x.1 x.2)⟩
  have h1 := h k B g n hB hg hn
  rw [Nat.card_unique] at h1
  rcases Nat.pow_eq_one.1 h1.symm with h3 | h3 <;> omega
end GlobalTheory.Published.AbMulNSt
