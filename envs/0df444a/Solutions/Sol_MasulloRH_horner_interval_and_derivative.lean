-- Prove2me | solution 1 for MasulloRH.horner_interval_and_derivative
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T23:58:35.591839+00:00
-- url     : https://prove2.me/submissions/2ba87e38-5f06-48c4-9305-2f8ea900d620

import Definitions.Def_MasulloRH_ThetaDerivativeCertificates
import Theorems.Thm_MasulloRH_central_interval_arithmetic_sound

open MasulloRH.CentralInterval MasulloRH.ThetaDerivativeCertificate

theorem solution (p : List ℤ) :
    (∀ x : ℝ, HasDerivAt (hornerR p) (hornerSlope p x) x) ∧
    (∀ (z : Box) (x : ℝ), Covers z x → Covers (hornerB p z) (hornerR p x)) := by
  let ok := MasulloRH.central_interval_arithmetic_sound
  induction p with
  | nil =>
    exact ⟨fun x => hasDerivAt_const x 0,fun _ _ _ => by simpa [hornerB,hornerR] using ok.point_ok 0⟩
  | cons c p ih =>
    constructor
    · intro x
      simpa [hornerR,hornerSlope] using (((hasDerivAt_id x).mul (ih.1 x)).const_add (c:ℝ))
    · intro z x hx
      simpa [hornerB,hornerR] using ok.add_ok (ok.point_ok (c:ℚ)) (ok.mul_ok hx (ih.2 _ _ hx))
