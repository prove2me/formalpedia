-- Prove2me | solution 6 for Kyprianou.Ch04.chapterFourMainResultsV3
-- status  : ACCEPTED   (disprove)
-- author  : @daga2
-- created : 2026-11-26T02:59:19.721997+00:00
-- url     : https://prove2.me/submissions/684c9956-bb64-496b-b9cf-faa893b8b44f

import Mathlib
import Definitions.Def_Kyprianou_Ch04_CompensationCertificationV3
import Definitions.Def_Kyprianou_Ch04_Exercise4_1CertificationV2
import Definitions.Def_Kyprianou_Ch04_Exercise4_2Certification
import Definitions.Def_Kyprianou_Ch04_Exercise4_3Certification
import Definitions.Def_Kyprianou_Ch04_Exercise4_4Certification
import Definitions.Def_Kyprianou_Ch04_Exercise4_5Certification
import Definitions.Def_Kyprianou_Ch04_Exercise4_6Certification
import Definitions.Def_Kyprianou_Ch04_Exercise4_7Certification
import Definitions.Def_Kyprianou_Ch04_Exercise4_8CertificationV2
import Definitions.Def_Kyprianou_Ch04_Exercise4_9Certification
import Definitions.Def_Kyprianou_Ch04_DeterministicModel

open MeasureTheory ProbabilityTheory Filter Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
open Kyprianou.Ch04.DeterministicModel
open Kyprianou.Ch04
set_option autoImplicit false

/-- Unit drift cannot become a martingale under a divergent localisation. -/
private theorem noLocalDrift (M : NNReal → Unit → Real) (stops : Nat → Unit → NNReal)
    (hMt : ∀ t, M t () = (t : Real))
    (hlim : Tendsto (fun n => (stops n () : WithTop NNReal)) atTop (nhds ⊤))
    (hM : ∀ n, Martingale (fun t w => M (min t (stops n w)) w)
      (⊤ : Filtration NNReal _) (Measure.dirac ())) : False := by
  obtain ⟨n, hn⟩ := ((WithTop.tendsto_nhds_top_iff _).mp hlim 1).exists
  have he := (hM n).setIntegral_eq (i := 0) (j := 1) (by norm_num)
    (s := Set.univ) MeasurableSet.univ
  simp [hMt, min_eq_left (le_of_lt (WithTop.coe_lt_coe.mp hn))] at he

/-- In the zero-jump, zero-supplied-drift model, the grid integral vanishes. -/
private theorem driftContradiction (M I J : NNReal → Unit → Real)
    (stops : Nat → Unit → NNReal)
    (hJ : ∀ t : NNReal, Tendsto (fun _n : Nat => (0 : Real)) atTop (nhds (J t ())))
    (hIJ : ∀ t : NNReal, I t () = J t () + M t ())
    (hI : ∀ t : NNReal, (t : Real) = I t ())
    (hlim : Tendsto (fun n => (stops n () : WithTop NNReal)) atTop (nhds ⊤))
    (hM : ∀ n, Martingale (fun t w => M (min t (stops n w)) w)
      (⊤ : Filtration NNReal _) (Measure.dirac ())) : False := by
  apply noLocalDrift M stops _ hlim hM
  intro t
  have hz := tendsto_nhds_unique (hJ t) tendsto_const_nhds
  linarith [hI t, hIJ t]

/-- Disproof of the Chapter 4 capstone: its Exercise 4.5 conjunct is false.
    Transport (WORMHOLE donor: WillR's accepted disproofs 3ddf104a / 49f25072
    of `exercise_4_5_complete` / `exercise_4_5_iv_goalV2`): project the
    21-fold conjunction to its 17th conjunct `certificate_exercise_4_5`,
    then reuse the donor counterexample verbatim — singleton unit-speed
    Levy path, zero characteristic triplet, zero Poisson measure. The
    jump measure and X2 vanish, so the asserted (iv) decomposition forces
    the local martingale to be deterministic unit drift, contradicting
    equality of expectations at 0 and 1 after a divergent localisation. -/
theorem solution :
    ¬ (certificate_4_1_v2 ∧
    certificate_4_2_v2 ∧
    certificate_4_3_v2 ∧
    certificate_4_4_v3 ∧
    certificate_4_5_v3 ∧
    certificate_4_6_v3 ∧
    certificate_4_7_v2 ∧
    certificate_4_8_v2 ∧
    certificate_4_9_v2 ∧
    certificate_4_10_v2 ∧
    certificate_4_11_v2 ∧
    certificate_4_12_v2 ∧
    certificate_exercise_4_1_v2 ∧
    certificate_exercise_4_2 ∧
    certificate_exercise_4_3 ∧
    certificate_exercise_4_4 ∧
    certificate_exercise_4_5 ∧
    certificate_exercise_4_6 ∧
    certificate_exercise_4_7 ∧
    certificate_exercise_4_8_v2 ∧
    certificate_exercise_4_9) := by
  intro h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h45, _, _, _, _⟩ := h
  have hnot : ¬ Kyprianou.Ch04.certificate_exercise_4_5 := by
    intro hc
    let P : Measure Unit := Measure.dirac ()
    let T : LevyKhintchineTriple := ⟨0, 0, 0, by simp [IsLevyMeasure]⟩
    let : SigmaFinite T.levyMeasure := inferInstanceAs (SigmaFinite (0 : Measure Real))
    let X : NNReal → Unit → Real := fun t _ => (t : Real)
    let N : PoissonRandomMeasure.{0,0,0} P T.levyMeasure := zeroPRM
    obtain ⟨M, stops, I, J, hJ, hIJ, hI, hstop, hlim, hM, hIto⟩ :=
      hc.2.2.2 P (⊤ : Filtration NNReal _) X unitDrift.property T rfl N X
        (Eventually.of_forall fun _ _ _ => continuous_subtype_val.continuousWithinAt)
        (Eventually.of_forall fun _ => by simp [N, zeroPRM, Kyprianou.Ch04.pathJumpMeasure])
        (fun _ x => x) (fun _ _ => 0) (fun _ _ => 1) (fun _ _ => 0)
        (by simp) (by simp) (by simp)
        (fun _ => contDiff_const) (fun _ => contDiff_id)
        (fun _ _ => 0) (by simp [T, N, zeroPRM])
    simp only [P, ae_dirac_eq, Filter.eventually_pure] at hJ hIJ hlim hIto
    exact driftContradiction M I J stops
      (by simpa using hJ) hIJ (by simpa [X, N, zeroPRM] using hIto) hlim hM
  exact hnot h45
