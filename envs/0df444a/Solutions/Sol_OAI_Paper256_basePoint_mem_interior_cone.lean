-- Prove2me | solution 1 for OAI.Paper256.basePoint_mem_interior_cone
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:35:33.537389+00:00
-- url     : https://prove2.me/submissions/2e7be871-7ff6-4f80-b595-59b28b0598ca

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/ConeInterior.lean:L13-L43
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.basePoint_mem_interior_cone. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit
import Definitions.Def_OAI_Analysis_HyperbolicCones_Coordinates
import Definitions.Def_OAI_Analysis_HyperbolicCones_ConeMatrix
import Theorems.Thm_OAI_Paper256_cone_positive_slice_of_inverse_order
import Theorems.Thm_OAI_Paper256_isOpen_posDef

-- ---- from OAI.Analysis.HyperbolicCones.MatrixBasic ----
namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

universe u

namespace Paper256

theorem qMatrix_smul {R : Type u} [CommRing R] (y : Fin 3 → R) (s : R) :
    qMatrix (s • y) = s ^ 2 • qMatrix y := by
  ext i j
  by_cases h : i = j <;> simp [qMatrix, h, mul_pow] <;> ring

theorem phi_scaling_general {R : Type u} [CommRing R]
    (y : Fin 3 → R) (s : R) (X : Mat 4 R) :
    phi (s • y) X = s ^ 2 • phi y X := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [phi, qMatrix_smul, Matrix.trace, Matrix.mul_apply, Matrix.submatrix,
      ← Finset.mul_sum, mul_left_comm, mul_assoc]

theorem phi_zero_parameter {R : Type u} [CommRing R] (X : Mat 4 R) :
    phi (0 : Fin 3 → R) X = 0 := by
  simpa using phi_scaling_general (0 : Fin 3 → R) 0 X

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.ConeMatrix ----
namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

theorem continuousAt_symInverse {n : ℕ} (X : Sym n)
    (hX : IsUnit (X : Mat n ℝ)) : ContinuousAt symInverse X := by
  have hd : (X : Mat n ℝ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hX).ne_zero
  have hi : ContinuousAt Inv.inv (X : Mat n ℝ) :=
    continuousAt_matrix_inv _ (by
      simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hd))
  apply tendsto_subtype_rng.mpr
  exact hi.comp (f := fun H : Sym n => (H : Mat n ℝ)) (x := X)
    continuous_subtype_val.continuousAt

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.InverseOrder ----
namespace OAI

/-! Simultaneous spectral comparison of a positive matrix and its scalar shifts. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix
namespace Paper256

theorem matrix_cfc_affine {n : ℕ} (H : Sym n) (a b : ℝ) :
    cfc (fun x : ℝ => a + b * x) (H : Mat n ℝ) =
      a • (1 : Mat n ℝ) + b • (H : Mat n ℝ) := by
  calc
    _ = algebraMap ℝ (Mat n ℝ) a + cfc (fun x : ℝ => b * x) (H : Mat n ℝ) :=
      cfc_const_add a (fun x : ℝ => b * x) (H : Mat n ℝ)
        (H.val.finite_real_spectrum.continuousOn _) H.property
    _ = _ := by
      have hmul : cfc (fun x : ℝ => b * x) (H : Mat n ℝ) = b • (H : Mat n ℝ) :=
        cfc_const_mul_id b (H : Mat n ℝ) H.property
      rw [hmul, Algebra.algebraMap_eq_smul_one]

theorem posDef_inverse_eq_cfc {n : ℕ} (H : Sym n) (hH : (H : Mat n ℝ).PosDef) :
    (H : Mat n ℝ)⁻¹ = cfc (fun x : ℝ => x⁻¹) (H : Mat n ℝ) := by
  have hi := cfc_inv (fun x : ℝ => x) (H : Mat n ℝ)
    (fun x hx => (posDef_real_spectrum_positive hH hx).ne')
    (H.val.finite_real_spectrum.continuousOn _) H.property
  have hid : cfc (fun x : ℝ => x) (H : Mat n ℝ) = (H : Mat n ℝ) :=
    cfc_id' ℝ (H : Mat n ℝ) H.property
  rw [hid, ← Matrix.nonsing_inv_eq_ringInverse] at hi
  exact hi.symm

theorem posDef_shift_inverse_eq_cfc {n : ℕ} (H : Sym n)
    (hH : (H : Mat n ℝ).PosDef) (t : ℝ) (ht : 0 ≤ t) :
    ((H : Mat n ℝ) + t • 1)⁻¹ =
      cfc (fun x : ℝ => (x + t)⁻¹) (H : Mat n ℝ) := by
  have hi := cfc_inv (fun x : ℝ => x + t) (H : Mat n ℝ)
    (fun x hx => (add_pos_of_pos_of_nonneg (posDef_real_spectrum_positive hH hx) ht).ne')
    (H.val.finite_real_spectrum.continuousOn _) H.property
  have hshift : cfc (fun x : ℝ => x + t) (H : Mat n ℝ) =
      (H : Mat n ℝ) + t • 1 := by
    simpa only [add_comm, one_mul, one_smul] using matrix_cfc_affine H t 1
  rw [hshift, ← Matrix.nonsing_inv_eq_ringInverse] at hi
  exact hi.symm

theorem posDef_inverse_sub_shift_inverse_posSemidef {n : ℕ} (H : Sym n)
    (hH : (H : Mat n ℝ).PosDef) (t : ℝ) (ht : 0 ≤ t) :
    ((H : Mat n ℝ)⁻¹ - ((H : Mat n ℝ) + t • 1)⁻¹).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  rw [sub_nonneg, posDef_inverse_eq_cfc H hH, posDef_shift_inverse_eq_cfc H hH t ht]
  apply cfc_mono _ (H.val.finite_real_spectrum.continuousOn _)
    (H.val.finite_real_spectrum.continuousOn _)
  intro x hx
  exact inv_anti₀ (posDef_real_spectrum_positive hH hx) (le_add_of_nonneg_right ht)

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.ConePositive ----
namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

theorem cone_positive_slice (X Z : Sym 4) (y : Fin 3 → ℝ) (hX : (X : Mat 4 ℝ).PosDef) :
    ((X, Z), y) ∈ cone ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef := by
  have h := cone_positive_slice_of_inverse_order X Z y hX
    (fun t ht => posDef_inverse_sub_shift_inverse_posSemidef X hX t ht)
  simp only [coneResidual, zero_smul, add_zero] at h
  change ((X, Z), y) ∈ cone ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef at h
  exact h

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.ConeContinuity ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

theorem continuous_qMatrix : Continuous (qMatrix : (Fin 3 → ℝ) → Mat 3 ℝ) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases h : i = j
  · simp only [qMatrix, ite_eq_left h]
    fun_prop
  · simp only [qMatrix, ite_eq_right h]
    fun_prop

theorem continuous_phi :
    Continuous (fun z : (Fin 3 → ℝ) × Mat 4 ℝ => phi z.1 z.2) := by
  have hq : Continuous (fun z : (Fin 3 → ℝ) × Mat 4 ℝ => qMatrix z.1) :=
    continuous_qMatrix.comp continuous_fst
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [phi, Fin.cases_zero, Fin.cases_succ, Matrix.trace,
      Matrix.submatrix] <;> fun_prop

theorem continuous_phiSym_joint :
    Continuous (fun z : (Fin 3 → ℝ) × Sym 4 => phiSym z.1 z.2) := by
  let f : (Fin 3 → ℝ) × Sym 4 → (Fin 3 → ℝ) × Mat 4 ℝ :=
    fun z => (z.1, (z.2 : Mat 4 ℝ))
  have hf : Continuous f := continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)
  have hc : Continuous (fun z : (Fin 3 → ℝ) × Sym 4 => phi z.1 (z.2 : Mat 4 ℝ)) :=
    continuous_phi.comp (f := f) hf
  exact hc.subtype_mk (fun z => phi_isHermitian z.1 (z.2 : Mat 4 ℝ) z.2.property)

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.ConeInterior ----
namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator

namespace Paper256

theorem basePoint_mem_interior_cone : basePoint ∈ interior cone := by
  let R : Ambient → Sym 4 := fun x => x.1.2 - phiSym x.2 (symInverse x.1.1)
  have hX : Continuous (fun x : Ambient => x.1.1) := continuous_fst.fst
  have hZ : Continuous (fun x : Ambient => x.1.2) := continuous_fst.snd
  have hY : Continuous (fun x : Ambient => x.2) := continuous_snd
  have hInv : ContinuousAt (fun x : Ambient => symInverse x.1.1) basePoint :=
    (continuousAt_symInverse (1 : Sym 4) Matrix.PosDef.one.isUnit).comp
      (f := fun x : Ambient => x.1.1) (x := basePoint) hX.continuousAt
  have hPhi : ContinuousAt (fun x : Ambient => phiSym x.2 (symInverse x.1.1)) basePoint :=
    continuous_phiSym_joint.continuousAt.comp
      (f := fun x : Ambient => (x.2, symInverse x.1.1)) (x := basePoint)
      (hY.continuousAt.prodMk hInv)
  have hR : ContinuousAt R basePoint := hZ.continuousAt.sub hPhi
  have hRone : R basePoint = 1 := by
    apply Subtype.ext
    change (1 : Mat 4 ℝ) - phi (0 : Fin 3 → ℝ) (1 : Mat 4 ℝ)⁻¹ = 1
    rw [phi_zero_parameter, sub_zero]
  have hN : ∀ᶠ H : Sym 4 in 𝓝 (1 : Sym 4), (H : Mat 4 ℝ).PosDef :=
    (isOpen_posDef 4).mem_nhds Matrix.PosDef.one
  have heX : ∀ᶠ x : Ambient in 𝓝 basePoint, (x.1.1 : Mat 4 ℝ).PosDef := by
    have hxat : ContinuousAt (fun x : Ambient => x.1.1) basePoint := hX.continuousAt
    exact hxat.eventually hN
  have heR : ∀ᶠ x : Ambient in 𝓝 basePoint, (R x : Mat 4 ℝ).PosDef := by
    have hRN : ∀ᶠ H : Sym 4 in 𝓝 (R basePoint), (H : Mat 4 ℝ).PosDef := by
      rw [hRone]
      exact hN
    have h := hR.eventually hRN
    exact h
  rw [mem_interior_iff_mem_nhds]
  filter_upwards [heX, heR] with x hx hr
  exact (cone_positive_slice x.1.1 x.1.2 x.2 hx).mpr hr.posSemidef

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator


theorem solution : type_of% @_root_.OAI.Paper256.basePoint_mem_interior_cone := @_root_.OAI.Paper256.basePoint_mem_interior_cone
