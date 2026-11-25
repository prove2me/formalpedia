-- Prove2me | solution 1 for GroundTheory.Arith.Toric.trdeg_semigroupAlgebra_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:54:57.963307+00:00
-- url     : https://prove2.me/submissions/640cbedd-7325-488f-a6f7-0d24a69b9ee6

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Normal
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Theorems.Thm_GroundTheory_Arith_Toric_trdeg_semigroupAlgebra_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
universe u
open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry Algebra
variable {k G : Type u} [CommRing k] [IsDomain k] [AddCommGroup G] [Module.Free ℤ G]
variable [Module.Finite ℤ G]
namespace GroundTheory.Arith.Toric
theorem _root_.solution :
    trdeg k (semigroupAlgebra k (⊤ : AddSubmonoid G)) = Module.finrank ℤ G := by
  classical
  let b := Module.finBasis ℤ G
  let P := AddMonoidHom.mrange (natCombination b)
  let one : Fin (Module.finrank ℤ G) →₀ ℕ := ∑ i, Finsupp.single i 1
  let u := natCombination b one
  have hu : u ∈ P := ⟨one, rfl⟩
  have hrepr_u : ∀ i, b.repr u i = 1 := by
    intro i
    rw [repr_natCombination]
    simp [one, Finsupp.finsetSum_apply, Finsupp.single_apply]
  have hT : ∀ m, ∃ j : ℕ, m + j • u ∈ P := by
    intro m
    let j : ℕ := ∑ i, (b.repr m i).natAbs
    refine ⟨j, ⟨Finsupp.equivFunOnFinite.symm fun i => (b.repr m i + j).toNat, ?_⟩⟩
    apply b.repr.injective
    ext i
    rw [repr_natCombination, map_add, map_nsmul, Finsupp.add_apply, Finsupp.smul_apply,
      hrepr_u, Finsupp.mapRange_apply, Finsupp.coe_equivFunOnFinite_symm]
    have hle : (b.repr m i).natAbs ≤ j :=
      Finset.single_le_sum (f := fun i => (b.repr m i).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    simp only [nsmul_eq_mul, mul_one]
    omega
  rw [← trdeg_semigroupAlgebra_eq_top hu hT, ← (mvPolynomialEquiv k b).trdeg_eq,
    MvPolynomial.trdeg_of_isDomain]
  simp
end GroundTheory.Arith.Toric
