-- Prove2me | solution 1 for GroundTheory.Global.Artin.mk_pow_smul_of_isArithFrobAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:45.495796+00:00
-- url     : https://prove2.me/submissions/d133f341-cfe7-43f8-8cf8-74bc0579d50d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Places
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesFrobenius
import Theorems.Thm_GroundTheory_Global_Artin_extendByZero_coe
import Theorems.Thm_GroundTheory_Global_Artin_subfieldPlaceEquiv_mk
import Theorems.Thm_GroundTheory_GroupCoh_doubleCosetMap_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Artin.extendByZero_coe
attribute [local simp] GroundTheory.Global.Artin.subfieldPlaceEquiv_mk
attribute [local simp] GroundTheory.GroupCoh.doubleCosetMap_mk



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K)) (v : HeightOneSpectrum (𝓞 K))
  (w : HeightOneSpectrum (𝓞 L))
namespace GroundTheory.Global.Artin
theorem _root_.solution {P : Ideal (𝓞 L)} {ψ : Gal(L/K)}
    (hψ : IsArithFrobAt (𝓞 K) ψ P) (n : ℕ) (y : 𝓞 L) :
    Ideal.Quotient.mk P ((ψ ^ n) • y) =
      Ideal.Quotient.mk P y ^ (Nat.card (𝓞 K ⧸ P.under (𝓞 K)) ^ n) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul]
    erw [hψ.mk_apply]
    rw [ih, ← pow_mul, ← pow_succ]
end GroundTheory.Global.Artin
