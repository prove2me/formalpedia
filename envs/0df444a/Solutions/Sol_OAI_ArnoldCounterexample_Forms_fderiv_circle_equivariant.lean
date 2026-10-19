-- Prove2me | solution 1 for OAI.ArnoldCounterexample.Forms.fderiv_circle_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:56:50.310136+00:00
-- url     : https://prove2.me/submissions/f6889226-407e-4d06-b79b-63ba9864122a

import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension
import Definitions.Def_OAI_Geometry_Arnold_Deformation
import Definitions.Def_OAI_Geometry_Arnold_Exterior
import Definitions.Def_OAI_Geometry_Arnold_Homotopy
import Definitions.Def_OAI_Geometry_Arnold_Volume

open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.Forms
universe uE uF
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ContinuousAlternatingMap
open ContinuousAlternatingMap
theorem solution {m n : ℕ} (F : CSpace m → CSpace n)
    (hF : Differentiable ℝ F) (z : CSpace m)
    (hphase : ∀ a : ℂ, Complex.normSq a = 1 → F (a • z) = a • F z) :
    fderiv ℝ F z (Complex.I • z) = Complex.I • F z := by
  have hc : HasDerivAt (fun t : ℝ => Complex.exp (↑t * Complex.I)) Complex.I 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (↑t * Complex.I : ℂ)) Complex.I 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0:ℝ))).mul_const Complex.I
    have := h1.cexp
    simpa using this
  have hγ : HasDerivAt (fun t : ℝ => Complex.exp (↑t * Complex.I) • z) (Complex.I • z) 0 :=
    hc.smul_const z
  have h1 : HasDerivAt (fun t : ℝ => F (Complex.exp (↑t * Complex.I) • z))
      (fderiv ℝ F z (Complex.I • z)) 0 := by
    have h0 : Complex.exp (((0:ℝ) : ℂ) * Complex.I) • z = z := by simp
    have := (hF (Complex.exp (((0:ℝ) : ℂ) * Complex.I) • z)).hasFDerivAt.comp_hasDerivAt (0:ℝ) hγ
    rw [h0] at this
    exact this
  have h2 : HasDerivAt (fun t : ℝ => F (Complex.exp (↑t * Complex.I) • z))
      (Complex.I • F z) 0 := by
    have heq : (fun t : ℝ => F (Complex.exp (↑t * Complex.I) • z)) =
        fun t : ℝ => Complex.exp (↑t * Complex.I) • F z := by
      funext t
      apply hphase
      rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; norm_num
    rw [heq]
    exact hc.smul_const (F z)
  exact h1.unique h2
