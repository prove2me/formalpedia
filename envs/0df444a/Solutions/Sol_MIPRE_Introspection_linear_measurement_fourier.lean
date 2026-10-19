-- Prove2me | solution 1 for MIPRE.Introspection.linear_measurement_fourier
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:37:43.272982+00:00
-- url     : https://prove2.me/submissions/bb82b6bb-64a7-4662-8347-659a3232ff47

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/LinearMeasurement.lean (solution of MIPRE.Introspection.linear_measurement_fourier);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Theorems.Thm_MIPRE_Weyl_eq_sum_proj

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem mem_perp {S : Submodule F (Fin n → F)} {x : Fin n → F} :
    x ∈ perp S ↔ ∀ y ∈ S, ∑ i, y i * x i = 0 := by
  simp [perp, LinearMap.BilinForm.mem_orthogonal_iff]
end
end MIPRE.CL

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n : Type*} [Fintype n]
theorem trDot_comm (a b : n → F) : trDot a b = trDot b a := by
  rw [trDot, trDot, Finset.sum_congr rfl fun l _ => mul_comm (a l) (b l)]
end
end MIPRE.Weyl

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}
local instance instCharPOfNatNat_mIPRE : CharP F 2 := charP_of_injective_algebraMap' (ZMod 2) 2
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}
attribute [local instance] MIPRE.Introspection.instCharPOfNatNat_mIPRE
/-- On a fiber, every trace character perpendicular to the kernel is constant. -/
theorem trDot_eq_of_same_fiber (L : (Fin n → F) →ₗ[F] (Fin n → F))
    {v x y : Fin n → F} (hv : v ∈ CL.perp L.ker) (hxy : L x = L y) :
    trDot v x = trDot v y := by
  have hk : x - y ∈ L.ker := by simp [LinearMap.mem_ker, map_sub, hxy]
  have hdot := (CL.mem_perp.mp hv) (x - y) hk
  have ht : trDot (x - y) v = 0 := by rw [trDot, hdot, map_zero]
  have hchar : x - y = x + y := by
    ext i
    exact CharTwo.sub_eq_add _ _
  rw [hchar, trDot_add_left] at ht
  rw [trDot_comm v x, trDot_comm v y]
  exact CharTwo.add_eq_zero.mp ht
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}
attribute [local instance] MIPRE.Introspection.instCharPOfNatNat_mIPRE
theorem linearPreimage_image (L : (Fin n → F) →ₗ[F] (Fin n → F)) (x : Fin n → F) :
    L (linearPreimage L (L x)) = L x := by
  have hx : ∃ y, L y = L x := ⟨x, rfl⟩
  rw [linearPreimage, dif_pos hx]
  exact hx.choose_spec
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}
attribute [local instance] MIPRE.Introspection.instCharPOfNatNat_mIPRE
theorem _root_.solution
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (v : Fin n → F) (hv : v ∈ CL.perp L.ker) :
    w v = ∑ a : Fin n → F, sgn (trDot v (linearPreimage L a)) • synOf w L a := by
  rw [eq_sum_proj (w := w) v]
  have hc (e : Fin n → F) : trDot v e = trDot v (linearPreimage L (L e)) :=
    trDot_eq_of_same_fiber L hv (linearPreimage_image L e).symm
  simp_rw [synOf, Finset.smul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun e (_ : e ∈ (univ : Finset (Fin n → F))) => mem_univ (L e))
      (fun e => sgn (trDot v e) • proj w e)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro e he
  rw [hc, (Finset.mem_filter.mp he).2]
end MIPRE.Introspection
