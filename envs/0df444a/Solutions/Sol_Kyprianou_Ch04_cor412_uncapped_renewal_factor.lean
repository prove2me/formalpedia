-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_uncapped_renewal_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:29:07.540494+00:00
-- url     : https://prove2.me/submissions/2c7b56a7-3886-4044-bfd7-8fce74e3b843

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch04_cor412_lower_stop
import Theorems.Thm_Kyprianou_Ch04_cor412_finite_cap_selector
import Theorems.Thm_Kyprianou_Ch04_cor412_finite_cap_union
import Theorems.Thm_Kyprianou_Ch04_cor412_capped_renewal_factor
import Theorems.Thm_Kyprianou_Ch04_cor412_capped_renewal_path
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Exhaust the finite passage event by deterministic caps to obtain the defective renewal factor. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (hB : ∀ᵐ w ∂P, BddBelow (range (fun t : NNReal => L.X t w)))
    (β : ℝ) (hβ : 0 ≤ β)
    (finiteTime : Ω → NNReal)
    (hfin : ∀ w, Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤ →
      Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w = (finiteTime w : WithTop NNReal)) :
    let A : Set Ω := {w | Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤}
    let R : (NNReal → ℝ) → ℝ≥0∞ := fun f =>
      ⨅ q : ℕ × ℕ, ENNReal.ofReal (Real.exp (β * f ((q.1 : NNReal) / 2 ^ q.2)))
    (∫⁻ w in A, R (fun t => L.X t w) ∂P) =
      (∫⁻ w in A, ENNReal.ofReal (Real.exp (β * L.X (finiteTime w) w)) ∂P) *
        (∫⁻ w, R (fun t => L.X t w) ∂P) := by
  classical
  intro A R
  let τ : Ω → WithTop NNReal := fun w => Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w
  let C : ℕ → Set Ω := fun n => {w | τ w ≤ ((n : NNReal) : WithTop NNReal)}
  let H : Ω → ℝ≥0∞ := fun w => ENNReal.ofReal (Real.exp (β * L.X (finiteTime w) w))
  have hs := Kyprianou.Ch04.cor412_lower_stop P F L
  have hc (n : ℕ) : MeasurableSet (C n) :=
    (F.rightCont.le (n : NNReal)) _ (hs (n : NNReal))
  have hcap (n : ℕ) : (∫⁻ w in C n, R (fun t => L.X t w) ∂P) =
      (∫⁻ w in C n, H w ∂P) * (∫⁻ w, R (fun t => L.X t w) ∂P) := by
    let T : Ω → NNReal := fun w =>
      if τ w ≤ ((n : NNReal) : WithTop NNReal) then finiteTime w else n
    have ht := Kyprianou.Ch04.cor412_finite_cap_selector τ finiteTime hfin (n : NNReal)
    have h1 := Kyprianou.Ch04.cor412_capped_renewal_path L (n : NNReal) T ht hB β hβ
    have h2 := Kyprianou.Ch04.cor412_capped_renewal_factor L (n : NNReal) T ht β
    have he := h1.trans h2
    change (∫⁻ w, (C n).indicator (fun z => R (fun t => L.X t z)) w ∂P) =
      (∫⁻ w, (C n).indicator (fun z => ENNReal.ofReal (Real.exp (β * L.X (T z) z))) w ∂P) *
        (∫⁻ w, R (fun t => L.X t w) ∂P) at he
    rw [lintegral_indicator (hc n), lintegral_indicator (hc n)] at he
    rw [he]
    congr 1
    apply setLIntegral_congr_fun (hc n)
    intro w hw
    have hwc : τ w ≤ ((n : NNReal) : WithTop NNReal) := hw
    have heq : T w = finiteTime w := if_pos hwc
    simp only [H, heq]
  have hC : (⋃ n, C n) = A := Kyprianou.Ch04.cor412_finite_cap_union τ
  have hmono : Monotone C := by
    intro i j hij w hw
    change τ w ≤ ((i : NNReal) : WithTop NNReal) at hw
    change τ w ≤ ((j : NNReal) : WithTop NNReal)
    exact le_trans hw (WithTop.coe_le_coe.mpr (by exact_mod_cast hij))
  change (∫⁻ w in A, R (fun t => L.X t w) ∂P) =
    (∫⁻ w in A, H w ∂P) * (∫⁻ w, R (fun t => L.X t w) ∂P)
  rw [← hC, setLIntegral_iUnion_of_directed _ hmono.directed_le,
    setLIntegral_iUnion_of_directed _ hmono.directed_le, ENNReal.iSup_mul]
  exact congrArg iSup (funext hcap)
