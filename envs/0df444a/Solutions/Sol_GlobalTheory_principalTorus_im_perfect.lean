-- Prove2me | solution 1 for GlobalTheory.principalTorus_im_perfect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:21:15.792097+00:00
-- url     : https://prove2.me/submissions/b94e7179-cb4b-429c-bffd-532051ccdfca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_PrincipalTorusEqZeroOfImLattice
import Theorems.Thm_GlobalTheory_principalTorus_eq_zero_of_im_lattice
import Theorems.Thm_GlobalTheory_principalTorus_mem_lattice_of_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
open scoped InnerProductSpace
open GlobalTheory
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory
theorem _root_.solution :
    (∀ (E : Type) [Field E] [NumberField E] (X : PT E) (a : Vsp X.dim),
      ((∀ y ∈ X.L, (Hf y a).im = 0) → a = 0) ∧
        ((∀ y ∈ X.L, ∃ k : ℤ, (Hf y a).im = k) → a ∈ X.L)) :=
  fun _ _ _ X _ => ⟨principalTorus_eq_zero_of_im_lattice X, principalTorus_mem_lattice_of_int X⟩
end GlobalTheory
