-- Prove2me | solution 1 for GlobalTheory.FinOf.finOf_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:54:12.686589+00:00
-- url     : https://prove2.me/submissions/95b28ba1-8ecc-48b2-90dd-53ec764e9b1b

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinOfLocalAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FinOf
variable {R₀ : Type} [CommRing R₀]
namespace GlobalTheory.FinOf
theorem _root_.solution {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A]
    [Module.Free O A] [Module.Finite O A] {n : ℕ} (ε : Fin n → A)
    (hε : CompleteOrthogonalIdempotents ε) :
    (∀ i, Module.Free O (A ⧸ Ideal.span {1 - ε i})) ∧
      (∑ i, Module.finrank O (A ⧸ Ideal.span {1 - ε i})) = Module.finrank O A := by
  let Q : Fin n → Type := fun i => A ⧸ Ideal.span {1 - ε i}
  let E : A ≃ₗ[O] (∀ i, Q i) :=
    LinearEquiv.ofBijective (LinearMap.pi fun i => (Ideal.Quotient.mkₐ O _).toLinearMap)
      hε.bijective_pi
  haveI hfree : ∀ i, Module.Free O (Q i) := fun i => by
    haveI : Module.Projective O (Q i) :=
      Module.Projective.of_split (M := A)
        (E.symm.toLinearMap ∘ₗ LinearMap.single O Q i) (LinearMap.proj i ∘ₗ E.toLinearMap)
        (LinearMap.ext fun x => by simp)
    exact Module.free_of_flat_of_isLocalRing
  refine ⟨hfree, ?_⟩
  rw [E.finrank_eq, Module.finrank_pi_fintype]
end GlobalTheory.FinOf
