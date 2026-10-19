-- Prove2me | solution 1 for OAI.KervaireMatrix.phase_weightedCycle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:33:04.941628+00:00
-- url     : https://prove2.me/submissions/9e277f52-7835-416d-bfd9-4c75528e80f8

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/WeightedCycles.lean:L344-L368
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireMatrix.phase_weightedCycle. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Theorems.Thm_OAI_KervaireMatrix_phase_weightedDiagonal
import Theorems.Thm_OAI_KervaireMatrix_phase_weightedShift_grid
import Theorems.Thm_OAI_KervaireRegular_groupPhase_conjugate

-- ---- from OAI.GroupTheory.Kervaire.MatrixShifts ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate

namespace KervaireMatrix

section
open KervaireRegular
open scoped Classical
variable {D A : Type*}

variable [Fintype D]

variable [Group A]

end

open KervaireRegular
open scoped Classical
variable {D A : Type*} [Group A]

variable [Fintype D]

/-- Multiplication proves the exact order of coefficient inverses on every boundary step. -/
theorem weightedShift_mul (σ τ : Equiv.Perm D) (u v : D → ℂ) (a b : D → A) :
    weightedShift σ u a * weightedShift τ v b =
      weightedShift (σ*τ) (fun d => u (τ d)*v d) (fun d => a (τ d)*b d) := by
  apply ext_delta
  rintro ⟨d,x⟩
  simp [mul_apply_eq_comp, smul_smul, mul_assoc, mul_comm (v d)]

end KervaireMatrix
namespace KervaireSpectral
end KervaireSpectral

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.WeightedCycles ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate

namespace KervaireMatrix
open KervaireRegular KervaireSpectral
variable {A : Type*} [Group A]

end KervaireMatrix
namespace KervaireSpectral
open KervaireTraceCalculus
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

end KervaireSpectral

namespace KervaireRegular
open KervaireSpectral
open scoped Classical
variable {A : Type*} [Group A]

end KervaireRegular

namespace KervaireMatrix
open KervaireRegular KervaireSpectral
variable {D A : Type*} [Fintype D] [Group A]

end KervaireMatrix
namespace KervaireCycle
open Fin.NatCast
variable {D B : Type*} [Monoid B]

/-- Cutting an oriented circuit respects the noncommutative order of labels. -/
theorem orbitWeight_add (σ : Equiv.Perm D) (b : D → B) (n m : ℕ) (i : D) :
    orbitWeight σ b (n+m) i =
      orbitWeight σ b n ((σ^m) i) * orbitWeight σ b m i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_add, orbitWeight_succ, ih, orbitWeight_succ, pow_add]
    simp only [Equiv.Perm.mul_apply, mul_assoc]

end KervaireCycle

namespace KervaireMatrix
open KervaireRegular KervaireCycle
variable {D A : Type*} [Fintype D] [Group A]

/-- Exact powers of the scalar/group-labelled shift. -/
theorem weightedShift_pow (σ : Equiv.Perm D) (u : D → ℂ) (a : D → A) (n : ℕ) :
    weightedShift σ u a ^ n = weightedShift (σ^n)
      (orbitWeight σ u n) (orbitWeight σ a n) := by
  induction n with
  | zero =>
    change 1 = labelledShift (Equiv.refl D) (fun _ => 1) * scalarDiagonal (fun _ => 1)
    rw [labelledShift_one, scalarDiagonal_one, mul_one]
  | succ n ih => rw [pow_succ', ih, weightedShift_mul, pow_succ']; rfl

/-- After one complete circuit the operator is diagonal, with the original circuit weights. -/
theorem weightedShift_cycle_pow (d : ℕ) [NeZero d] (u : Fin d → ℂ) (a : Fin d → A) :
    weightedShift (finRotate d) u a ^ d = weightedShift (Equiv.refl (Fin d))
      (orbitWeight (finRotate d) u d) (orbitWeight (finRotate d) a d) := by
  rw [weightedShift_pow, rotate_pow_self]
  rfl

end KervaireMatrix
namespace KervaireCycle
variable {D B : Type*} [Monoid B]

/-- Starting a full circuit after a partial traversal conjugates its weight. -/
theorem orbitWeight_start (σ : Equiv.Perm D) (b : D → B) (d j : ℕ)
    (hd : σ^d = 1) (i : D) :
    orbitWeight σ b d ((σ^j) i) * orbitWeight σ b j i =
      orbitWeight σ b j i * orbitWeight σ b d i := by
  rw [← orbitWeight_add, Nat.add_comm d j, orbitWeight_add, hd]
  rfl

end KervaireCycle

namespace KervaireMatrix
open KervaireRegular KervaireSpectral KervaireCycle
open Fin.NatCast
variable {A : Type*} [Group A]

/-- The scalar circuit weight is independent of its starting point, literally. -/
theorem scalar_orbitWeight_constant (d : ℕ) [NeZero d] (u : Fin d → ℂ)
    (hu : ∀ i, u i ∈ unitary ℂ) (i : Fin d) :
    orbitWeight (finRotate d) u d i = orbitWeight (finRotate d) u d 0 := by
  have h := orbitWeight_start (finRotate d) u d i.val (rotate_pow_self d) 0
  rw [rotate_pow_apply] at h
  simp only [zero_add, Fin.cast_val_eq_self] at h
  have hne : orbitWeight (finRotate d) u i.val 0 ≠ 0 :=
    (Unitary.isUnit_coe (U := ⟨_, orbitWeight_mem (unitary ℂ) _ u hu _ _⟩)).ne_zero
  apply mul_right_cancel₀ hne
  simpa only [mul_comm (orbitWeight (finRotate d) u i.val 0)] using h

/-- The group circuit weight is conjugated in the exact operator order. -/
theorem group_orbitWeight_conjugate (d : ℕ) [NeZero d] (a : Fin d → A) (i : Fin d) :
    orbitWeight (finRotate d) a d i =
      orbitWeight (finRotate d) a i.val 0 * orbitWeight (finRotate d) a d 0 *
        (orbitWeight (finRotate d) a i.val 0)⁻¹ := by
  have h := orbitWeight_start (finRotate d) a d i.val (rotate_pow_self d) 0
  rw [rotate_pow_apply] at h
  simp only [zero_add, Fin.cast_val_eq_self] at h
  exact (eq_mul_inv_iff_mul_eq).mpr h

/-- The diagonal full-circuit power has identical scalar regular phases on every slot. -/
theorem groupPhase_orbitWeight_constant (d : ℕ) [NeZero d] (u : Fin d → ℂ)
    (a : Fin d → A) (hu : ∀ i, u i ∈ unitary ℂ) (i : Fin d) :
    groupPhase (orbitWeight (finRotate d) u d i)
        (orbitWeight_mem (unitary ℂ) _ u hu _ _) (orbitWeight (finRotate d) a d i) =
      groupPhase (orbitWeight (finRotate d) u d 0)
        (orbitWeight_mem (unitary ℂ) _ u hu _ _) (orbitWeight (finRotate d) a d 0) := by
  simp only [scalar_orbitWeight_constant d u hu i, group_orbitWeight_conjugate d a i]
  exact groupPhase_conjugate _ _ _ _

/-- The literal weighted boundary-cycle formula, including the phase cut at 1.
No cyclic-word hypothesis, approximation, or finite-group restriction is used. -/
theorem phase_weightedCycle (n : ℕ) (u : Fin (n+1) → ℂ)
    (a : Fin (n+1) → A) (hu : ∀ i, u i ∈ unitary ℂ) :
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary (finRotate (n+1)) u a hu)
    phase (weightedShift (finRotate (n+1)) u a) = (n : ℝ)/2 +
      groupPhase (orbitWeight (finRotate (n+1)) u (n+1) 0)
        (orbitWeight_mem (unitary ℂ) _ u hu _ _) (orbitWeight (finRotate (n+1)) a (n+1) 0) := by
  let _ := isStarNormal_of_mem_unitary (weightedShift_unitary (finRotate (n+1)) u a hu)
  let _ := isStarNormal_of_mem_unitary (pow_mem (weightedShift_unitary (finRotate (n+1)) u a hu) (n+1))
  have h := phase_weightedShift_grid n u a hu
  have hp := phase_weightedDiagonal (orbitWeight (finRotate (n+1)) u (n+1))
    (orbitWeight (finRotate (n+1)) a (n+1))
    (orbitWeight_mem (unitary ℂ) _ u hu (n+1))
  simp_rw [groupPhase_orbitWeight_constant (n+1) u a hu] at hp
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] at hp
  have hpow : phase (weightedShift (finRotate (n+1)) u a ^ (n+1)) =
      (n+1 : ℝ) * groupPhase (orbitWeight (finRotate (n+1)) u (n+1) 0)
        (orbitWeight_mem (unitary ℂ) _ u hu _ _) (orbitWeight (finRotate (n+1)) a (n+1) 0) := by
    simpa only [weightedShift_cycle_pow] using hp
  dsimp only at h ⊢
  rw [hpow] at h
  have hn : (0 : ℝ) < n+1 := by positivity
  nlinarith
end KervaireMatrix

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireMatrix
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open KervaireRegular KervaireSpectral KervaireCycle
open Fin.NatCast


theorem solution : type_of% @_root_.OAI.KervaireMatrix.phase_weightedCycle := @_root_.OAI.KervaireMatrix.phase_weightedCycle
