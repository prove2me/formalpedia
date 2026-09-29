-- Prove2me | solution 1 for HlawkaSchatten.globalMinimumValue_two_sided_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-27T21:53:40.157551+00:00
-- url     : https://prove2.me/submissions/71b12c44-04e0-4293-b51a-82281345c3dd

import Definitions.Def_HlawkaSchatten_Variational
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Variational minima for the Bregman--Mazur argument

This file proves two reusable parts of the variational layer.  First, a
pointwise two-sided comparison transports to attained global minima, even
when the two objectives are indexed by different but equivalent spheres.
Second, the weighted squared-distance objective on a Hilbert unit sphere has
the exact minimum used in the Schatten argument.
-/


open scoped InnerProductSpace ComplexConjugate

open HlawkaSchatten

theorem solution
    {A B : Type*} (e : A ≃ B) (f : A → ℝ) (g : B → ℝ)
    (fmin gmin m M : ℝ) (hm : 0 ≤ m)
    (hf : IsGlobalMinimumValue f fmin)
    (hg : IsGlobalMinimumValue g gmin)
    (hcompare : ∀ x, m * g (e x) ≤ f x ∧ f x ≤ M * g (e x)) :
    m * gmin ≤ fmin ∧ fmin ≤ M * gmin := by
  constructor
  · obtain ⟨x, hx⟩ := hf.2
    calc
      m * gmin ≤ m * g (e x) := mul_le_mul_of_nonneg_left (hg.1 (e x)) hm
      _ ≤ f x := (hcompare x).1
      _ = fmin := hx
  · obtain ⟨y, hy⟩ := hg.2
    calc
      fmin ≤ f (e.symm y) := hf.1 (e.symm y)
      _ ≤ M * g (e (e.symm y)) := (hcompare (e.symm y)).2
      _ = M * gmin := by rw [e.apply_symm_apply, hy]
