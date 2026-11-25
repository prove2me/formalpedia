-- Prove2me | solution 1 for GroundTheory.Arith.Toric.trdeg_semigroupAlgebra_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:16:08.376773+00:00
-- url     : https://prove2.me/submissions/a0794378-1955-4543-a813-49f078cb76a7

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Normal
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Theorems.Thm_GroundTheory_Arith_Toric_isLocalization_away_semigroupAlgebra


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
namespace GroundTheory.Arith.Toric
theorem _root_.solution {S : AddSubmonoid G} {u : G} (hu : u ∈ S)
    (hT : ∀ m, ∃ j : ℕ, m + j • u ∈ S) :
    trdeg k (semigroupAlgebra k S) = trdeg k (semigroupAlgebra k (⊤ : AddSubmonoid G)) := by
  let := semigroupAlgebraAlgebra (k := k) (le_top : S ≤ ⊤)
  have hloc := isLocalization_away_semigroupAlgebra (k := k) (le_top : S ≤ ⊤) hu
    (AddSubmonoid.mem_top _) fun m _ => hT m
  have : IsScalarTower k (semigroupAlgebra k S) (semigroupAlgebra k (⊤ : AddSubmonoid G)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FaithfulSMul (semigroupAlgebra k S) (semigroupAlgebra k (⊤ : AddSubmonoid G)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 fun x y h =>
      Subtype.ext (congrArg (fun z : semigroupAlgebra k (⊤ : AddSubmonoid G) =>
        (z : AddMonoidAlgebra k G)) h)
  have : FaithfulSMul k (semigroupAlgebra k S) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 fun x y h => by
      have := congrArg (fun z : semigroupAlgebra k S => (z : AddMonoidAlgebra k G).coeff 0) h
      simpa [Algebra.algebraMap_eq_smul_one, AddMonoidAlgebra.one_def] using this
  have halg := IsLocalization.isAlgebraic (semigroupAlgebra k (⊤ : AddSubmonoid G))
    (Submonoid.powers (⟨single u 1, single_mem_semigroupAlgebra hu 1⟩ : semigroupAlgebra k S))
  have h0 : trdeg (semigroupAlgebra k S) (semigroupAlgebra k (⊤ : AddSubmonoid G)) = 0 :=
    trdeg_eq_zero
  rw [← trdeg_add_eq k (semigroupAlgebra k S) (A := semigroupAlgebra k (⊤ : AddSubmonoid G)),
    h0, add_zero]
end GroundTheory.Arith.Toric
