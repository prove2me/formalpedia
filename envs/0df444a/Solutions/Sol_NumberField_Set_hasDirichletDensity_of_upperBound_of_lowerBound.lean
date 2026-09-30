-- Prove2me | solution 1 for NumberField.Set.hasDirichletDensity_of_upperBound_of_lowerBound
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:16:28.890371+00:00
-- url     : https://prove2.me/submissions/20508c4f-0fb2-46a8-a643-95a0cdf3a5e6

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_DirichletDensityBounds
import Mathlib.NumberTheory.NumberField.DirichletDensity

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# One-sided bounds for Dirichlet density

For a set `S` of nonzero prime ideals of a number field, Mathlib's
`NumberField.Set.HasDirichletDensity S δ` says that the ratio

`S.primeIdealZetaSum s / Set.univ.primeIdealZetaSum s`

tends to `δ` as `s` approaches `1` from the right.  Squeeze arguments often produce the two
sides of this limit separately.  This file records those one-sided conclusions as
`NumberField.Set.IsLowerDirichletDensityBound S δ` and
`NumberField.Set.IsUpperDirichletDensityBound S δ`.

The predicates use eventual epsilon inequalities, rather than assigning junk-valued lower and
upper densities.  They are monotone in the proposed bound, and a common lower and upper bound
forces a Dirichlet density.  A lower bound is always at most an upper bound; this
comparison also gives the natural interval restrictions on one-sided bounds.

## Main results

* `NumberField.Set.hasDirichletDensity_iff`: Mathlib's `HasDirichletDensity`, unfolded to the
  convergence of the defining ratio.
* `NumberField.Set.HasDirichletDensity.isLowerDirichletDensityBound` and
  `NumberField.Set.HasDirichletDensity.isUpperDirichletDensityBound`: a Dirichlet density is
  both a lower and an upper bound.
* `NumberField.Set.isLowerDirichletDensityBound_of_forall_lt` and
  `NumberField.Set.isUpperDirichletDensityBound_of_forall_gt`: a value is a lower (upper) bound as
  soon as every smaller (larger) value is.
* `NumberField.Set.IsLowerDirichletDensityBound.le_of_isUpperDirichletDensityBound`:
  every lower bound is at most every upper bound.
* `NumberField.Set.hasDirichletDensity_of_upperBound_of_lowerBound`: matching one-sided bounds
  force a Dirichlet density.
* `NumberField.Set.hasDirichletDensity_iff_bounds`: the resulting characterization of
  Dirichlet density.

## References

* J.-P. Serre, *Corps locaux*, Chapter VI.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

 section

open _root_.Filter _root_.IsDedekindDomain _root_.NumberField
open scoped _root_.Topology

namespace NumberField.Set
end NumberField.Set
section NumberField.Set
open NumberField NumberField.Set

variable {K : Type*} [Field K] [NumberField K]

/-- Unfolds `HasDirichletDensity S δ` to the convergence, as `s → 1⁺`, of the ratio of the
partial prime sum over `S` to the sum over all primes. -/
theorem NumberField.Set.hasDirichletDensity_iff {S : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))} {δ : ℝ} :
    S.HasDirichletDensity δ ↔
      _root_.Filter.Tendsto (fun s : ℝ ↦ S.primeIdealZetaSum s /
        _root_.NumberField.Set.primeIdealZetaSum (_root_.Set.univ : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))) s)
        (𝓝[>] 1) (𝓝 δ) :=
  _root_.Iff.rfl











-- The proof below follows `NumberField.Set.HasDirichletDensity.le_one` from
-- `Mathlib.NumberTheory.NumberField.DirichletDensity`.
























/-- Matching lower and upper Dirichlet-density bounds force a Dirichlet density equal to their
common value. -/
theorem solution
    {S : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (hupper : _root_.NumberField.Set.IsUpperDirichletDensityBound S δ)
    (hlower : _root_.NumberField.Set.IsLowerDirichletDensityBound S δ) :
    S.HasDirichletDensity δ := by
  refine _root_.NumberField.Set.hasDirichletDensity_iff.2 <| _root_.tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    let ε := (δ - a) / 2
    have hε : 0 < ε := _root_.div_pos (sub_pos.mpr ha) _root_.zero_lt_two
    filter_upwards [hlower ε hε] with s hs
    have hlt : a < δ - ε := by
      dsimp [ε]
      linarith
    exact hlt.trans hs
  · intro b hb
    let ε := (b - δ) / 2
    have hε : 0 < ε := _root_.div_pos (sub_pos.mpr hb) _root_.zero_lt_two
    filter_upwards [hupper ε hε] with s hs
    have hlt : δ + ε < b := by
      dsimp [ε]
      linarith
    exact hs.trans hlt



end NumberField.Set

end
end
