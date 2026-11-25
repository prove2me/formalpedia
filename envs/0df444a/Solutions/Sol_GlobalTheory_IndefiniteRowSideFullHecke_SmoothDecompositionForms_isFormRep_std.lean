-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms.isFormRep_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:54:48.478404+00:00
-- url     : https://prove2.me/submissions/568d14a2-3aa4-4799-864d-64d812cb605c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_BesselMapUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SmoothDecompositionForms
import Theorems.Thm_PI_HwUniqW_Hpk_conjTranspose
import Theorems.Thm_PI_HwUniqW_Hpk_mul_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
open PI.UpqRep
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms
attribute [instance] HRep.instNorm HRep.instInner HRep.instComplete
variable {k r : ℕ}
variable {ι : Type} [Fintype ι]
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms
theorem _root_.solution (k r : ℕ) : IsFormRep k r (stdRep k r) (Hpk k r) 1 where
  map_one := rfl
  map_mul _ _ _ _ := rfl
  smooth c d g₀ _ := ⟨Set.univ, fun g => g c d, isOpen_univ, Set.mem_univ _,
    (contDiff_pi.1 (contDiff_pi.1 (contDiff_id (E := Ix k r → Ix k r → ℂ)) c) d).contDiffOn, fun _ _ _ => rfl⟩
  herm := PI.HwUniqW.Hpk_conjTranspose
  sq := PI.HwUniqW.Hpk_mul_self
  inv _ hg := hg
  unitK _ hg := hg.2
  growth := ⟨1, fun g _ c d => by
    rw [one_mul, pow_one]
    apply Real.le_sqrt_of_sq_le
    unfold hs stdRep
    calc ‖g c d‖ ^ 2 ≤ ∑ j, ‖g c j‖ ^ 2 :=
          Finset.single_le_sum (f := fun j => ‖g c j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ d)
      _ ≤ _ := Finset.single_le_sum (f := fun i => ∑ j, ‖g i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ c)⟩
end GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms
