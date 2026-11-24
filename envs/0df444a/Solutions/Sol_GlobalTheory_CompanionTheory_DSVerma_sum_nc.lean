-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSVerma.sum_nc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:28:51.055777+00:00
-- url     : https://prove2.me/submissions/a8f43c68-b6dc-4102-9126-e3941cc8eb30

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_KummerLiftedCocycleImageEqPicardClass
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSVerma
open CompanionTheory.D.DSIC Formalism.REAL
variable {n : ℕ} {ε : Fin n → Bool}
namespace GlobalTheory.CompanionTheory.DSVerma
theorem _root_.solution {R : Type} [AddCommMonoid R] (d b : Fin n) (g : Fin n → Fin n → R) :
    (∑ j : NC ε, if d = j.1.1 ∧ b = j.1.2 then g j.1.1 j.1.2 else 0) =
      if ε d = true ∧ ε b = false then g d b else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨(d, b), h⟩ : NC ε)]
    · simp
    · intro j _ hj
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hj (Subtype.ext (Prod.ext h1.symm h2.symm))
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact h (by rw [h1, h2]; exact j.2)
end GlobalTheory.CompanionTheory.DSVerma
