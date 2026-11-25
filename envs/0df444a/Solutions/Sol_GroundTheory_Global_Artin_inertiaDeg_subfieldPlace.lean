-- Prove2me | solution 1 for GroundTheory.Global.Artin.inertiaDeg_subfieldPlace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:12.411681+00:00
-- url     : https://prove2.me/submissions/8552cb55-09e7-4018-a486-fb97f3473ebe

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Places
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesFrobenius
import Theorems.Thm_GroundTheory_Global_Artin_card_mul_card_eq
import Theorems.Thm_GroundTheory_Global_Artin_inertia_smul_eq
import Theorems.Thm_GroundTheory_Global_Artin_stabilizer_smul_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
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
theorem _root_.solution (x : Gal(L/K)) :
    (subfieldPlace H w x).asIdeal.inertiaDeg (𝓞 K) =
      frobIndex H (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.asIdeal.inertia Gal(L/K)) x := by
  set D := MulAction.stabilizer Gal(L/K) w.asIdeal
  set I := w.asIdeal.inertia Gal(L/K)
  set u := subfieldPlace H w x
  have hID : I ≤ D := Ideal.inertia_le_stabilizer w.asIdeal

  have ha := Ideal.card_stabilizer_eq_card_inertia_mul_finrank (G := Gal(L/K)) (w.asIdeal.under (𝓞 K)) w.asIdeal
  have hb := Ideal.card_stabilizer_eq_card_inertia_mul_finrank (G := H) u.asIdeal (x • w.asIdeal)
  erw [stabilizer_smul_eq, inertia_smul_eq] at hb

  have hc := Ideal.inertiaDeg_tower (R := 𝓞 K) u.asIdeal (x • w.asIdeal)
  rw [Ideal.inertiaDeg_smul] at hc
  have hd := card_mul_card_eq (H := H) hID x
  rw [Nat.card_congr (conjSubgroupOfEquiv H D x)] at hd
  set r := frobIndex H D I x
  set fw := w.asIdeal.inertiaDeg (𝓞 K)
  set fu := u.asIdeal.inertiaDeg (𝓞 K)
  set fP := (x • w.asIdeal).inertiaDeg (𝓞 (fixedField H))
  have hI : 0 < Nat.card I := Nat.card_pos
  have hIx : 0 < Nat.card ((MulAut.conj x • I : Subgroup Gal(L/K)).subgroupOf H) := Nat.card_pos
  have hfP : 0 < fP := Ideal.inertiaDeg_pos (x • w.asIdeal) _
  rw [ha, hb] at hd
  have h1 : fw = r * fP := by
    have : Nat.card I * Nat.card ((MulAut.conj x • I : Subgroup Gal(L/K)).subgroupOf H) * fw =
        Nat.card I * Nat.card ((MulAut.conj x • I : Subgroup Gal(L/K)).subgroupOf H) * (r * fP) := by
      rw [← mul_assoc] at hd
      linarith [hd]
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hI hIx) this
  rw [hc] at h1
  exact (Nat.eq_of_mul_eq_mul_right hfP h1)
end GroundTheory.Global.Artin
