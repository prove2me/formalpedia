-- Prove2me | solution 1 for OAI.ShortDraftCRT.addChar_congr_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:31:30.239211+00:00
-- url     : https://prove2.me/submissions/b77a8c75-639d-4c5f-a792-600807e41609

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open OAI.ShortDraftCRT
open AddChar
variable {K : Type*} [Field K]
variable {R : Type*} [CommRing R]
namespace OAI.ShortDraftCRT
theorem _root_.solution
    (ι : R →+* K) (ψ : AddChar K ℂ) (lam d a b x : R)
    (hlam : ι lam ≠ 0) (hd : ι d ≠ 0)
    (hperiod : ∀ y : R, ψ (ι y / ι lam) = 1)
    (hcong : d ∣ a - b) :
    ψ (ι a * ι x / (ι lam * ι d)) =
      ψ (ι b * ι x / (ι lam * ι d)) := by
  obtain ⟨k, hk⟩ := hcong
  have ha : a = b + d * k := by
    calc
      a = b + (a - b) := by ring
      _ = b + d * k := by rw [hk]
  rw [ha, map_add, map_mul]
  have hsplit :
      (ι b + ι d * ι k) * ι x / (ι lam * ι d) =
        ι b * ι x / (ι lam * ι d) + ι (k * x) / ι lam := by
    simp only [map_mul]
    field_simp
  rw [hsplit, map_add_eq_mul, hperiod, mul_one]
end OAI.ShortDraftCRT
