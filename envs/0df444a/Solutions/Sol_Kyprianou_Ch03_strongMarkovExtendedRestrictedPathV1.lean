-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovExtendedRestrictedPathV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:45:14.071892+00:00
-- url     : https://prove2.me/submissions/eabb7362-6238-4c02-ba9a-a284115ebdbf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_strongMarkovExtendedUpperGridV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovCountableGridRestrictedLawV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovPathLawOfCommonAELimitsV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovFiniteStoppedEventMeasV1
open MeasureTheory ProbabilityTheory Filter
open Kyprianou.Ch03
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (hDet : ∀ (s : NNReal) (B : Set Omega), MeasurableSet[F s] B →
      Measure.map (fun omega u => X (s + u) omega - X s omega) (P.restrict B) =
        P B • Measure.map (fun omega u => X u omega) P)
    (tau : Omega → WithTop NNReal)
    (hTau : IsStoppingTime F tau)
    (finiteTime : Omega → NNReal)
    (hFiniteTime : ∀ omega, tau omega ≠ ⊤ →
      tau omega = (finiteTime omega : WithTop NNReal)) :
    AEMeasurable (fun omega : Omega => fun u : NNReal =>
      X (finiteTime omega + u) omega - X (finiteTime omega) omega) (P.restrict {omega : Omega | tau omega ≠ ⊤}) ∧
    ∀ B : Set Omega, (∀ s : NNReal, MeasurableSet[F s]
      (B ∩ {omega : Omega | tau omega ≤ (s : WithTop NNReal)})) →
      Measure.map (fun omega : Omega => fun u : NNReal =>
      X (finiteTime omega + u) omega - X (finiteTime omega) omega)
        (P.restrict (B ∩ {omega : Omega | tau omega ≠ ⊤})) =
      P (B ∩ {omega : Omega | tau omega ≠ ⊤}) • Measure.map (fun omega u => X u omega) P := by
  classical
  have hAdapt : ∀ t : NNReal, Measurable[F t] (X t) := by
    intro t
    apply (comap_measurable (X t)).mono _ le_rfl
    rw [hNatural t]
    exact le_sup_of_le_left (le_iSup₂_of_le t le_rfl le_rfl)
  have hMeas : ∀ t : NNReal, Measurable (X t) :=
    fun t => (hAdapt t).mono (F.le t) le_rfl
  obtain ⟨T, hCount, hFib, hZero, hT⟩ :=
    strongMarkovExtendedUpperGridV1 F tau hTau finiteTime hFiniteTime
  let D : Set Omega := {w | tau w ≠ ⊤}
  let Y : ℕ → Omega → (NNReal → ℝ) :=
    fun n w u => X (T n w + u) w - X (T n w) w
  let Z : Omega → (NNReal → ℝ) :=
    fun w u => X (finiteTime w + u) w - X (finiteTime w) w
  let nu := Measure.map (fun w u => X u w) P
  have hGrid := fun n => strongMarkovCountableGridRestrictedLawV1 F tau hTau
    finiteTime hFiniteTime P X hMeas hDet (T n) (hCount n) (hFib n)
    (hZero n) (fun w hw => (hT w hw).1 n)
  have hConv : ∀ B : Set Omega, MeasurableSet (B ∩ D) →
      ∀ᵐ w ∂P.restrict (B ∩ D), ∀ u : NNReal,
        Tendsto (fun n => Y n w u) atTop (nhds (Z w u)) := by
    intro B hB
    filter_upwards [ae_restrict_mem hB,
      ae_mono Measure.restrict_le_self hX.cadlag_ae] with w hw hc u
    obtain ⟨hAbove, hlim⟩ := hT w hw.2
    have h1 := (hc (finiteTime w)).1.tendsto
    have h2 := (hc (finiteTime w + u)).1.tendsto
    have h3 : Tendsto (fun n => T n w + u) atTop (nhds (finiteTime w + u)) :=
      hlim.add tendsto_const_nhds
    have hm1 : Tendsto (fun n => T n w) atTop (nhdsWithin (finiteTime w) (Set.Ici (finiteTime w))) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hAbove⟩
    have hm2 : Tendsto (fun n => T n w + u) atTop
        (nhdsWithin (finiteTime w + u) (Set.Ici (finiteTime w + u))) :=
      tendsto_nhdsWithin_iff.mpr ⟨h3, Eventually.of_forall (fun n => by exact add_le_add (hAbove n) le_rfl)⟩
    exact (h2.comp hm2).sub (h1.comp hm1)
  have hAll : ∀ B : Set Omega, (∀ s : NNReal, MeasurableSet[F s]
      (B ∩ {w | tau w ≤ (s : WithTop NNReal)})) →
      AEMeasurable Z (P.restrict (B ∩ D)) ∧
      Measure.map Z (P.restrict (B ∩ D)) = P (B ∩ D) • nu := by
    intro B hB
    exact strongMarkovPathLawOfCommonAELimitsV1 (P.restrict (B ∩ D)) Y Z
      (P (B ∩ D) • nu) (fun n => (hGrid n).1)
      (fun n => (hGrid n).2 B hB)
      (hConv B (strongMarkovFiniteStoppedEventMeasV1 F tau hTau B hB))
  refine ⟨?_, fun B hB => (hAll B hB).2⟩
  simpa [D, Z] using (hAll Set.univ (fun s => by simpa using hTau s)).1
