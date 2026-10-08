-- Prove2me | solution 1 for OAI.PiExponent.asymptotic_determinant_bounds_inconsistent
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T19:02:39.215061+00:00
-- url     : https://prove2.me/submissions/30ea0166-f41f-4556-9aec-a415a9602bce

import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas

open Filter Topology

private theorem determinant_bounds_inconsistent
    (nu theta x b ear ean err collision d : ℝ)
    (hnu : 1 < nu) (hb0 : 0 ≤ b) (hb : b ≤ theta)
    (hgap : ear + ean + err < nu * (x - theta) - (1 - theta))
    (hcollision : 1 + ear + ean + err < collision)
    (hlower : -(1 - b) - ear ≤ d)
    (hupper : d ≤ ean + err + max (-collision) (-nu * (x - b))) : False := by
  have hfirst : ean + err - collision < -(1 - b) - ear := by linarith
  have hmono :
      nu * (x - theta) - (1 - theta) ≤ nu * (x - b) - (1 - b) := by
    nlinarith
  have hsecond : ean + err - nu * (x - b) < -(1 - b) - ear := by linarith
  rcases le_total (-collision) (-nu * (x - b)) with h | h
  · rw [max_eq_right h] at hupper
    linarith
  · rw [max_eq_left h] at hupper
    linarith

theorem solution
    (nu theta x ear ean collisionLimit : ℝ)
    (b d err collision : ℕ → ℝ)
    (hnu : 1 < nu)
    (hgap : ear + ean < nu * (x - theta) - (1 - theta))
    (hcollision : 1 + ear + ean < collisionLimit)
    (herr : Tendsto err atTop (𝓝 0))
    (hcol : Tendsto collision atTop (𝓝 collisionLimit))
    (hb0 : ∀ᶠ n in atTop, 0 ≤ b n)
    (hb : ∀ᶠ n in atTop, b n ≤ theta)
    (hlower : ∀ᶠ n in atTop, -(1 - b n) - ear ≤ d n)
    (hupper : ∀ᶠ n in atTop,
      d n ≤ ean + err n + max (-collision n) (-nu * (x - b n))) : False := by
  have hsum : Tendsto (fun n => ear + ean + err n) atTop (𝓝 (ear + ean + 0)) :=
    tendsto_const_nhds.add herr
  have hsmall : ∀ᶠ n in atTop,
      ear + ean + err n < nu * (x - theta) - (1 - theta) :=
    hsum.eventually (Iio_mem_nhds (by simpa using hgap))
  have hdiff : Tendsto (fun n => collision n - (1 + ear + ean + err n))
      atTop (𝓝 (collisionLimit - (1 + ear + ean + 0))) :=
    hcol.sub (tendsto_const_nhds.add herr)
  have hlarge : ∀ᶠ n in atTop, 0 < collision n - (1 + ear + ean + err n) :=
    hdiff.eventually (Ioi_mem_nhds (by linarith))
  have hfalse : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hsmall, hlarge, hb0, hb, hlower, hupper] with n hs hc h0 ht hl hu
    exact determinant_bounds_inconsistent nu theta x (b n) ear ean (err n)
      (collision n) (d n) hnu h0 ht hs (by linarith) hl hu
  exact hfalse.exists.elim fun _ h => h
