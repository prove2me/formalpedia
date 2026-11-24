-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.density_factor_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:40:07.764398+00:00
-- url     : https://prove2.me/submissions/66422cdd-fd99-4b2c-ba61-232764238813

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualUnramifiedPlaces
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SelfDualUnramifiedPlaces_one_lt_resCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces
theorem _root_.solution (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (M : ℕ) (hM : 1 ≤ M) :
    0 < 1 - _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v ^ M *
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹ := by
  have hq := _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.one_lt_resCard F v
  have hqM : 1 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M := one_lt_pow₀ hq (by omega)
  have hpos : 0 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M := by linarith
  have hsign : |_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v| = 1 := by
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta
    split_ifs <;> norm_num
  have hle := le_abs_self (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v ^ M *
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹)
  rw [abs_mul, abs_pow, hsign, one_pow, one_mul, abs_inv, abs_of_pos hpos] at hle
  have hinv : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hqM
  linarith
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces
end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces
