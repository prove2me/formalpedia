-- Prove2me | solution 1 for OAI.TriangularHilbert.MatrixEnergy.energy_supported_path_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:21:26.610032+00:00
-- url     : https://prove2.me/submissions/5ca81423-4e3f-415b-8f11-ed52d0d7578e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/Support.lean:L190-L207
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.MatrixEnergy.energy_supported_path_hasDerivAt. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_energy_hasFDerivWithinAt

-- ---- from OAI.Analysis.TriangularHilbert.MatrixSupport ----
namespace OAI

universe uι uκ uX uμ

section
open scoped BigOperators
noncomputable section
namespace TriangularHilbert.MatrixEnergy

open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace InnerProductSpace

end TriangularHilbert.MatrixEnergy

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary
namespace TriangularHilbert.MatrixEnergy

variable {ι : Type uι} [Fintype ι]

variable [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary MeasureTheory Filter
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem energy_path_hasDerivAt {P : ℝ → Matrix ι ι ℂ} {U : Matrix ι ι ℂ} {x : ℝ}
    (hP : (P x).PosDef) (hn : ∀ᶠ t in 𝓝 x, 0 ≤ P t) (hd : HasDerivAt P U x) :
    HasDerivAt (fun t => energy (P t)) (energyGradient (P x) U) x := by
  exact (energy_hasFDerivWithinAt hP).comp_hasDerivAt x hd hn

end TriangularHilbert.MatrixEnergy

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace TriangularHilbert.MatrixEnergy
variable {ι : Type uι} {κ : Type uκ} {μ : Type uμ} [Fintype ι] [Fintype κ] [Fintype μ]

variable [DecidableEq κ]

end TriangularHilbert.MatrixEnergy
end
end
end
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.Support ----
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma sqrt_mul_eq_zero_of_mul_eq_zero {P Q : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hPQ : P * Q = 0) : CFC.sqrt P * Q = 0 := by
  apply (CStarRing.star_mul_self_eq_zero_iff _).mp
  have hs := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
  change (CFC.sqrt P * Q)ᴴ * (CFC.sqrt P * Q) = 0
  rw [Matrix.conjTranspose_mul, hs.eq, ← Matrix.mul_assoc,
    Matrix.mul_assoc Qᴴ, CFC.sqrt_mul_sqrt_self P hP.nonneg,
    Matrix.mul_assoc, hPQ, mul_zero]

lemma mul_sqrt_eq_zero_of_mul_eq_zero {P Q : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQP : Q * P = 0) : Q * CFC.sqrt P = 0 := by
  have ht : P * Qᴴ = 0 := by
    simpa only [Matrix.conjTranspose_mul, hP.isHermitian.eq,
      Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hQP
  have hz := sqrt_mul_eq_zero_of_mul_eq_zero hP ht
  have hs := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
  simpa only [Matrix.conjTranspose_mul, hs.eq, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hz

lemma sqrt_add_projection {P Q : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) :
    CFC.sqrt (P + Q) = CFC.sqrt P + Q := by
  apply CFC.sqrt_unique
  · have hsQ := sqrt_mul_eq_zero_of_mul_eq_zero hP hPQ
    have hQs := mul_sqrt_eq_zero_of_mul_eq_zero hP hQP
    simp only [add_mul, mul_add, hsQ, hQs, hQQ,
      CFC.sqrt_mul_sqrt_self P hP.nonneg, add_zero, zero_add]
  · exact add_nonneg (CFC.sqrt_nonneg P) hQ.nonneg

lemma energy_add_projection {P Q : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) :
    energy (P + Q) = energy P + traceReal Q := by
  rw [energy, sqrt_add_projection hP hQ hQQ hPQ hQP]
  simp only [add_mul, mul_add, hPQ, mul_sqrt_eq_zero_of_mul_eq_zero hP hQP,
    hQQ, add_zero, zero_add, traceReal_add, energy]

lemma energyGradient_add_projection {P Q K : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) (hQK : Q * K = 0) :
    energyGradient (P + Q) K = energyGradient P K := by
  simp only [energyGradient_apply, sqrt_add_projection hP hQ hQQ hPQ hQP,
    add_mul, hQK, add_zero]

lemma projection_mul_deriv_eq_zero {P : ℝ → Matrix ι ι ℂ} {U Q : Matrix ι ι ℂ}
    {x : ℝ} (hd : HasDerivAt P U x) (hz : ∀ᶠ t in 𝓝 x, Q * P t = 0) : Q * U = 0 := by
  have hh := hd.const_mul Q
  have he : HasDerivAt (fun _ : ℝ => (0 : Matrix ι ι ℂ)) (Q * U) x :=
    hh.congr_of_eventuallyEq (hz.mono fun _ ht => ht.symm)
  exact he.unique (hasDerivAt_const x 0)

omit [DecidableEq ι] in
lemma hermitian_mul_zero_flip {P Q : Matrix ι ι ℂ}
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (h : P * Q = 0) : Q * P = 0 := by
  simpa only [Matrix.conjTranspose_mul, hP.eq, hQ.eq, Matrix.conjTranspose_zero] using
    congrArg Matrix.conjTranspose h

theorem energy_supported_path_hasDerivAt {P : ℝ → Matrix ι ι ℂ}
    {Q U : Matrix ι ι ℂ} {x : ℝ}
    (hQ : Q.PosSemidef) (hQQ : Q * Q = Q) (hPD : (P x + Q).PosDef)
    (hn : ∀ᶠ t in 𝓝 x, (P t).PosSemidef) (hz : ∀ᶠ t in 𝓝 x, P t * Q = 0)
    (hd : HasDerivAt P U x) :
    HasDerivAt (fun t => energy (P t)) (energyGradient (P x) U) x := by
  have hzl : ∀ᶠ t in 𝓝 x, Q * P t = 0 := by
    filter_upwards [hn, hz] with t ht htz
    exact hermitian_mul_zero_flip ht.isHermitian hQ.isHermitian htz
  have hQU := projection_mul_deriv_eq_zero hd hzl
  have hnonneg : ∀ᶠ t in 𝓝 x, 0 ≤ P t + Q := hn.mono fun _ ht => (ht.add hQ).nonneg
  have hh := (energy_path_hasDerivAt hPD hnonneg (hd.add_const Q)).sub_const (traceReal Q)
  rw [energyGradient_add_projection hn.self_of_nhds hQ hQQ hz.self_of_nhds
    hzl.self_of_nhds hQU] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [hn, hz, hzl] with t ht hr hl
  rw [energy_add_projection ht hQ hQQ hr hl]
  ring

end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter Unitary


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.MatrixEnergy.energy_supported_path_hasDerivAt.{uι} := @_root_.OAI.TriangularHilbert.MatrixEnergy.energy_supported_path_hasDerivAt.{uι}
