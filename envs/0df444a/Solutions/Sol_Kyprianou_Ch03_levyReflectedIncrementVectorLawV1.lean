-- Prove2me | solution 1 for Kyprianou.Ch03.levyReflectedIncrementVectorLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:22:25.112931+00:00
-- url     : https://prove2.me/submissions/08676778-e8bf-4324-ad12-2837982e9f22

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) (n : Nat)
    (q : Fin (n + 1) → NNReal) (hq : Monotone q)
    (hqt : ∀ i, q i ≤ t) :
    P.map (fun ω : Omega => fun i : Fin n =>
      X (t - q i.castSucc) ω - X (t - q i.succ) ω) =
    P.map (fun ω : Omega => fun i : Fin n =>
      X (q i.succ) ω - X (q i.castSucc) ω) := by
  let r (i : Fin (n + 1)) := t - q i.rev
  have hr : Monotone r := by
    intro i j hij
    apply tsub_le_tsub_left
    apply hq
    change j.rev.val ≤ i.rev.val
    have hh : i.val ≤ j.val := hij
    simp [Fin.rev]
    omega
  let U (i : Fin n) := increment X (t - q i.succ) (t - q i.castSucc)
  let V (i : Fin n) := increment X (q i.castSucc) (q i.succ)
  have hI : iIndepFun (fun i : Fin n => increment X (r i.castSucc) (r i.succ)) P :=
    hX.indep_increments n r hr
  have he (i : Fin n) : i.rev.castSucc.rev = i.succ := by
    apply Fin.ext
    simp [Fin.rev]
    omega
  have hf (i : Fin n) : i.rev.succ.rev = i.castSucc := by
    apply Fin.ext
    simp [Fin.rev]
    omega
  have hU : iIndepFun U P := by
    have hh := hI.precomp (Fin.rev_injective : Function.Injective (Fin.rev : Fin n → Fin n))
    simpa only [U, r, he, hf] using hh
  have hV : iIndepFun V P := hX.indep_increments n q hq
  have hc := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX
  change P.map (fun ω i => U i ω) = P.map (fun ω i => V i ω)
  have hmU (i : Fin n) : AEMeasurable (U i) P := (hc _).sub (hc _)
  have hmV (i : Fin n) : AEMeasurable (V i) P := (hc _).sub (hc _)
  rw [iIndepFun.map_fun_eq_pi_map hmU hU, iIndepFun.map_fun_eq_pi_map hmV hV]
  congr 1
  funext i
  have hi : q i.castSucc ≤ q i.succ := hq (Fin.castSucc_le_succ i)
  have hj : t - q i.succ ≤ t - q i.castSucc := tsub_le_tsub_left hi t
  have hlag : (t - q i.castSucc) - (t - q i.succ) = q i.succ - q i.castSucc := by
    apply NNReal.eq
    simp only [NNReal.coe_sub hj, NNReal.coe_sub (hqt _), NNReal.coe_sub hi]
    ring
  have hmap (a b : NNReal) (hab : a ≤ b) :
      P.map (increment X a b) = P.map (increment X 0 (b - a)) := by
    have h := (hX.stationary_increments a (b - a)).map_eq
    rwa [add_comm a, tsub_add_cancel_of_le hab] at h
  exact (hmap _ _ hj).trans (by rw [hlag]; exact (hmap _ _ hi).symm)
