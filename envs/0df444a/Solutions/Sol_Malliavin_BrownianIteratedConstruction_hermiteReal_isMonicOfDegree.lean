-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.hermiteReal_isMonicOfDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:24:28.438057+00:00
-- url     : https://prove2.me/submissions/92be5029-575f-4fd2-8f0a-2f79909b4725

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Definitions.Def_Malliavin_BrownianHermite

set_option autoImplicit false
noncomputable section
open MeasureTheory
open Malliavin Malliavin.BrownianIteratedConstruction
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution (n : ℕ) :
    Polynomial.IsMonicOfDegree (hermiteReal n) n := by
  refine ⟨?_, (Polynomial.hermite_monic n).map (Int.castRingHom ℝ)⟩
  rw [hermiteReal,
    Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℝ) Int.cast_injective,
    Polynomial.natDegree_hermite]
end Malliavin.BrownianIteratedConstruction
