-- Prove2me | solution 1 for Kyprianou.Ch04.totalIdleTraffic_nonSupercriticalInfiniteIdle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:10:51.525376+00:00
-- url     : https://prove2.me/submissions/8571d07b-8189-4dfd-83ca-0c4f67c1856d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_totalIdleStrictTailCrossingV1
import Theorems.Thm_Kyprianou_Ch04_totalIdleTrafficMaximalRootV1
import Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_maximalRootExistence
import Theorems.Thm_Kyprianou_Ch03_firstPassageZero_consequence1
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch03 Kyprianou.Ch04 Set

/-- Transfer the Chapter 3 finite first-passage probability to the idle strict tail. -/
private theorem idleTail
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P F) (w : Real) (hw : 0 ≤ w)
    (hd : 0 < L.drift) (T : Omega → ENNReal)
    (hc : ∀ᵐ omega ∂P, ∀ x : Real, 0 ≤ x →
      (ENNReal.ofReal x < T omega ↔
        ∃ t : NNReal, w + L.drift * x < L.X t omega))
    (hn : ¬ (∀ᵐ omega : Omega ∂P, Antitone (fun t : NNReal => L.X t omega)))
    (phi : Real)
    (hr : 0 ≤ phi ∧ L.ψ phi = 0 ∧
      (∀ theta : Real, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi))
    (x : Real) (hx : 0 ≤ x) :
    (P {omega | ENNReal.ofReal x < T omega}).toReal =
      Real.exp (-phi * (w + L.drift * x)) := by
  let a := w + L.drift * x
  have ha : 0 ≤ a := add_nonneg hw (mul_nonneg hd.le hx)
  let tau := firstHittingTime L.X (Set.Ioi a)
  have hhit : ∀ omega, tau omega ≠ ⊤ ↔ ∃ t : NNReal, a < L.X t omega := by
    intro omega
    change firstHittingTime L.X (Set.Ioi a) omega ≠ ⊤ ↔ _
    rw [← lt_top_iff_ne_top]
    simp only [firstHittingTime, sInf_lt_iff, mem_image, exists_exists_and_eq_and]
    constructor
    · rintro ⟨t, ⟨_, ht⟩, _⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      have ht0 : 0 < t := by
        by_contra! h
        have htzero : t = 0 := le_antisymm h zero_le
        rw [htzero, L.X_zero] at ht
        exact (not_lt_of_ge ha) ht
      exact ⟨t, ⟨ht0, ht⟩, WithTop.coe_lt_top _⟩
  have he : {omega | ENNReal.ofReal x < T omega} =ᵐ[P]
      {omega | tau omega ≠ ⊤} := by
    filter_upwards [hc] with omega ho
    exact propext ((ho x hx).trans (hhit omega).symm)
  let finiteTime : Omega → NNReal := fun omega => (tau omega).untopD 0
  have hfin (omega : Omega) (ho : tau omega ≠ ⊤) :
      tau omega = (finiteTime omega : WithTop NNReal) := by
    cases h : tau omega with
    | top => exact (ho h).elim
    | coe t => simp only [finiteTime, h, WithTop.untopD_coe]
  have hp := Kyprianou.Ch03.firstPassageZero_consequence1 P F L hn phi hr a ha
    finiteTime (fun omega ho => hfin omega (by simpa only [bne_iff_ne] using ho))
  rw [measure_congr he]
  simpa [tau, a, bne_iff_ne] using hp

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)
    (w : Real) (hw : 0 ≤ w) :
    let supX : NNReal → Omega → Real := fun t omega =>
      sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
    let W : NNReal → Omega → Real := fun t omega =>
      max w (supX t omega) - L.X t omega
    let totalIdle : Omega → ENNReal := fun omega =>
      ∫⁻ t in Set.Ici (0 : Real),
        (if W (Real.toNNReal t) omega = 0 then (1 : ENNReal) else 0) ∂volume
    let rho : ENNReal :=
      (∫⁻ y : Real, ENNReal.ofReal (-y) ∂L.ν) /
        ENNReal.ofReal L.drift
    (rho ≤ 1 →
      (P {omega : Omega | totalIdle omega = ⊤}).toReal = 1) := by
  intro supX W totalIdle rho htraffic
  letI : IsProbabilityMeasure P := L.isProbability
  have hpath := Kyprianou.Ch04.totalIdleStrictTailCrossingV1 P F L hBV hd w hw
  have hclass := Kyprianou.Ch04.totalIdleTrafficMaximalRootV1 P F L hBV hd
  rcases Kyprianou.Ch03.firstPassageTransform_maximalRootExistence P F L
    hclass.1 0 le_rfl with ⟨phi, hphi⟩
  have htail := idleTail P F L w hw hd totalIdle hpath.2 hclass.1 phi hphi
  have hz := (hclass.2 phi hphi.1 hphi.2.1 hphi.2.2).2 htraffic
  have hall : ∀ n : Nat, ∀ᵐ omega ∂P, (n : ENNReal) < totalIdle omega := by
    intro n
    let A : Set Omega := {omega | (n : ENNReal) < totalIdle omega}
    have hA : MeasurableSet A := hpath.1 measurableSet_Ioi
    have hp : (P A).toReal = 1 := by
      simpa [A, hz] using htail (n : Real) (Nat.cast_nonneg n)
    have hPA : P A = 1 := (ENNReal.toReal_eq_one_iff _).mp hp
    rw [ae_iff]
    change P Aᶜ = 0
    rw [measure_compl hA (measure_ne_top P A), measure_univ, hPA, tsub_self]
  have hAll : ∀ᵐ omega ∂P, ∀ n : Nat, (n : ENNReal) < totalIdle omega :=
    ae_all_iff.mpr hall
  have htop : ∀ᵐ omega ∂P, totalIdle omega = ⊤ := by
    filter_upwards [hAll] with omega ho
    by_contra hn
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hn
    exact (not_lt_of_ge (ho n).le) hn
  have he : {omega | totalIdle omega = ⊤} =ᵐ[P] (Set.univ : Set Omega) := by
    filter_upwards [htop] with omega ho
    change (totalIdle omega = ⊤) = True
    exact propext (iff_true_intro ho)
  rw [measure_congr he, measure_univ, ENNReal.toReal_one]
