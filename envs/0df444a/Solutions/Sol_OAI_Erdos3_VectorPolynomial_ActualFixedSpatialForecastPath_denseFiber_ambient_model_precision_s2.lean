-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.denseFiber_ambient_model_precision_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:10:50.991977+00:00
-- url     : https://prove2.me/submissions/43223ba7-930e-461b-b149-e03c734d5854

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B266
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialForecastPath_toDenseSliceMember_nativeMean_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_comparisonError_le_exp_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_native_ambient_model_comparison_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPathSlicedPerturbation_chosen_tail_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastModularCutoff
namespace OAI

section

namespace Erdos3

theorem forecastJointGridCutoff_lower (P E : ℝ) :
    Real.exp (P + E + 4) ≤ (forecastJointGridCutoff P E : ℝ) := Nat.le_ceil _

theorem forecastJointGridCutoff_pos_unconditional (P E : ℝ) : 0 < forecastJointGridCutoff P E := by
  exact_mod_cast (Real.exp_pos (P + E + 4)).trans_le (forecastJointGridCutoff_lower P E)

theorem forecastJointGridCutoff_pos {P E : ℝ} (_hP : 0 ≤ P) (_hE : 0 ≤ E) :
    0 < forecastJointGridCutoff P E := forecastJointGridCutoff_pos_unconditional P E

theorem forecastJointGridCutoff_le_exp {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) :
    (forecastJointGridCutoff P E : ℝ) ≤ Real.exp (P + E + 5) := by
  calc
    _ ≤ Real.exp (P + E + 4) + 1 := (Nat.ceil_lt_add_one (Real.exp_nonneg _)).le
    _ = 1 + Real.exp (P + E + 4) := add_comm _ _
    _ ≤ Real.exp ((P + E + 4) + 1) :=
      one_add_le_exp_succ (by linarith) le_rfl
    _ = _ := by congr 1; ring

end Erdos3

end

section

namespace Erdos3

theorem forecastJointGridMeshLog_nonneg (d : ℕ) {P E : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) : 0 ≤ forecastJointGridMeshLog d P E := by
  unfold forecastJointGridMeshLog
  positivity

theorem forecastJointGridMesh_bounds (d : ℕ) {P E : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) :
    0 < forecastJointGridMesh d P E ∧ forecastJointGridMesh d P E ≤ 1 :=
  ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr
    (forecastJointGridMeshLog_nonneg d hP hE))⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedPathSlicedGridMeshBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem fixedPathSlicedGrid_ratio_le {S H q : ℕ} {cost : ℝ}
    (hS : 0 < S) (hH : Real.exp (-cost) * S ≤ (H : ℝ)) :
    (q : ℝ) / H ≤ Real.exp cost * ((q : ℝ) / S) := by
  have hs : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  calc
    _ ≤ (q : ℝ) / (Real.exp (-cost) * S) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos (Real.exp_pos _) hs) hH
    _ = _ := by rw [Real.exp_neg]; field_simp

theorem fixedPathSlicedGrid_sum_ratio_le {Input : Type*} [Fintype Input]
    {D cost : ℝ} {S q : ℕ} (H : Input → ℕ)
    (hcard : (Fintype.card Input : ℝ) ≤ D) (hS : 0 < S)
    (hH : ∀ i, Real.exp (-cost) * S ≤ (H i : ℝ)) :
    (∑ i, (q : ℝ) / H i) ≤ D * Real.exp cost * ((q : ℝ) / S) := by
  calc
    _ ≤ ∑ _ : Input, Real.exp cost * ((q : ℝ) / S) :=
      Finset.sum_le_sum (fun i _ => fixedPathSlicedGrid_ratio_le hS (hH i))
    _ = (Fintype.card Input : ℝ) * (Real.exp cost * ((q : ℝ) / S)) := by simp
    _ ≤ D * (Real.exp cost * ((q : ℝ) / S)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

theorem fixedPathSlicedGridMeshFloor_lower (D C V cost E : ℝ) :
    Real.exp (fixedPathSlicedGridMeshLog D C V cost E) ≤
      (fixedPathSlicedGridMeshFloor D C V cost E : ℝ) := Nat.le_ceil _

theorem fixedPathSlicedGridMeshFloor_pos (D C V cost E : ℝ) :
    0 < fixedPathSlicedGridMeshFloor D C V cost E := by
  exact_mod_cast (Real.exp_pos _).trans_le (fixedPathSlicedGridMeshFloor_lower D C V cost E)

theorem fixedPathSlicedGridMesh_prefactor {D C V cost E : ℝ} {q S : ℕ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hq : (q : ℝ) ≤ Real.exp V)
    (hfloor : fixedPathSlicedGridMeshFloor D C V cost E ≤ S) :
    (D + C + 8) * (Real.exp cost * ((q : ℝ) / S)) ≤ Real.exp (-(E + 2)) := by
  have hp : (0 : ℝ) < D + C + 8 := by linarith
  have hS := (fixedPathSlicedGridMeshFloor_lower D C V cost E).trans
    (show (fixedPathSlicedGridMeshFloor D C V cost E : ℝ) ≤ S by exact_mod_cast hfloor)
  have hs : (0 : ℝ) < S := (Real.exp_pos _).trans_le hS
  have hnum : (D + C + 8) * Real.exp cost * (q : ℝ) ≤
      Real.exp (Real.log (D + C + 8) + V + cost) := by
    calc
      _ ≤ (D + C + 8) * Real.exp cost * Real.exp V :=
        mul_le_mul_of_nonneg_left hq (mul_nonneg hp.le (Real.exp_nonneg _))
      _ = _ := by rw [Real.exp_add, Real.exp_add, Real.exp_log hp]; ring
  rw [← mul_div_assoc, ← mul_div_assoc]
  apply (div_le_iff₀ hs).mpr
  calc
    _ ≤ Real.exp (Real.log (D + C + 8) + V + cost) := by simpa only [mul_assoc] using hnum
    _ = Real.exp (-(E + 2)) * Real.exp (fixedPathSlicedGridMeshLog D C V cost E) := by
      rw [← Real.exp_add]
      congr 1
      unfold fixedPathSlicedGridMeshLog
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hS (Real.exp_nonneg _)

theorem fixedPathSlicedGridMesh_of_floor {D C V cost E : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hE : 0 ≤ E)
    {Input : Type*} [Fintype Input] (H : Input → ℕ)
    (hcard : (Fintype.card Input : ℝ) ≤ D) {q S : ℕ}
    (hq0 : 0 < q) (hq : (q : ℝ) ≤ Real.exp V)
    (hfloor : fixedPathSlicedGridMeshFloor D C V cost E ≤ S)
    (hH : ∀ i, Real.exp (-cost) * S ≤ (H i : ℝ))
    (mesh : Input → ℝ) (hmesh : ∀ i, mesh i ≤ 2 * Real.exp cost / S) :
    (∑ i, (q : ℝ) / H i) ≤ Real.exp (-E) ∧
      (∀ i, C * ((q : ℝ) / H i) ≤ Real.exp (-E)) ∧
      (∀ i, mesh i ≤ Real.exp (-E)) ∧
      ∀ i, 2 ≤ H i ∧ q ≤ H i ∧
        scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H i) < 1 := by
  have hS := (fixedPathSlicedGridMeshFloor_pos D C V cost E).trans_le hfloor
  have hSr : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  let r := Real.exp cost * ((q : ℝ) / S)
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hbound := fixedPathSlicedGridMesh_prefactor hD hC hq hfloor
  have hsmall : Real.exp (-(E + 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have he : Real.exp (-(E + 2)) ≤ Real.exp (-E) := Real.exp_le_exp.mpr (by linarith)
  have hmajor {a : ℝ} (ha : a ≤ D + C + 8) : a * r ≤ Real.exp (-(E + 2)) :=
    (mul_le_mul_of_nonneg_right ha hr).trans hbound
  have hratio (i : Input) : (q : ℝ) / H i ≤ r := fixedPathSlicedGrid_ratio_le hS (hH i)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hsum := fixedPathSlicedGrid_sum_ratio_le (q := q) H hcard hS hH
    have hsummajor : D * Real.exp cost * ((q : ℝ) / S) ≤ Real.exp (-(E + 2)) := by
      simpa only [mul_assoc, r] using hmajor (show D ≤ D + C + 8 by linarith)
    exact hsum.trans (hsummajor.trans he)
  · intro i
    exact ((mul_le_mul_of_nonneg_left (hratio i) hC).trans
      (hmajor (show C ≤ D + C + 8 by linarith))).trans he
  · intro i
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq0
    have htwo : 2 * Real.exp cost / S ≤ 2 * r := by
      dsimp only [r]
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right
        (le_mul_of_one_le_right (Real.exp_nonneg _) hq1) hSr.le
    exact ((hmesh i).trans htwo).trans
      ((hmajor (show (2 : ℝ) ≤ D + C + 8 by linarith)).trans he)
  · intro i
    have hHi : (0 : ℝ) < H i := (mul_pos (Real.exp_pos _) hSr).trans_le (hH i)
    have hfour : 4 * ((q : ℝ) / H i) < 1 :=
      ((mul_le_mul_of_nonneg_left (hratio i) (by norm_num : (0 : ℝ) ≤ 4)).trans
        (hmajor (show (4 : ℝ) ≤ D + C + 8 by linarith))).trans_lt hsmall
    have hratio1 : (q : ℝ) / H i < 1 := by
      have hn : (0 : ℝ) ≤ (q : ℝ) / H i := by positivity
      linarith
    have hqH : q < H i := Nat.cast_lt.mp ((div_lt_one hHi).mp hratio1)
    refine ⟨by omega, hqH.le, ?_⟩
    have hconst : scalarCubeGridBoundaryConstant Empty = 4 := by
      norm_num [scalarCubeGridBoundaryConstant]
    rwa [hconst]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedPerturbativeSeedPowerBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : {a : LayerSamplerAxis I n // ¬short a},
  B (Subtype.val a) × Fin (degree (Subtype.val a)))

theorem allocatedOriginalSampleLiftInput_card_le_allAxis :
    Fintype.card Input ≤ Fintype.card (PrincipalTupleIndex B degree) := by
  simp only [PrincipalTupleIndex, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  apply Finset.sum_le_sum_of_injOn Subtype.val
    (fun _ _ _ _ h => Subtype.val_injective h) (Finset.subset_univ _)
  · intro a _
    exact le_rfl
  · intro a _ _
    exact Nat.zero_le _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastIntegerAxisSplit
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

theorem allocatedActiveIntegerGridScale_mesh {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    {L : ℕ} (hL : 0 < L) {H q : ℝ} (hq : 0 ≤ q) (hRinv : ∀ j, (R j)⁻¹ ≤ H)
    (a : AllocatedActiveIntegerAxis U basis L) :
    q / allocatedActiveIntegerGridScale U basis R L a ≤ q * H / L := by
  have hLR : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hpow : L ≤ L ^ (a.val.1.val + 1) :=
    Nat.le_self_pow (by omega) L
  have hscale : (L : ℝ) ≤ basisAxisScale (basis a.val.1) a.val.2 := by
    exact_mod_cast hpow.trans a.property.le
  have hqR : 0 ≤ q / R a.val.1 := div_nonneg hq (hR _).le
  calc
    q / allocatedActiveIntegerGridScale U basis R L a =
        (q / R a.val.1) / basisAxisScale (basis a.val.1) a.val.2 := by
      simp only [allocatedActiveIntegerGridScale, div_div]
    _ ≤ (q / R a.val.1) / L := div_le_div_of_nonneg_left hqR hLR hscale
    _ ≤ q * H / L := by
      apply div_le_div_of_nonneg_right _ hLR.le
      simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left (hRinv _) hq

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastJointScaleNormalization
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {X : Type*} [Fintype X]

omit [Fintype X] in
theorem forecastJointGridScale_mesh {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    {L : ℕ} (hL : 0 < L) (physicalN : X → ℕ) (hN : ∀ i, 0 < physicalN i)
    {τ H q cutoff δ : ℝ} (hτ : 0 < τ) (hq : 0 ≤ q) (hcutoff : 0 ≤ cutoff)
    (hRinv : ∀ j, (R j)⁻¹ ≤ H)
    (hspatial : ∀ i, q * cutoff * 8 * τ⁻¹ / physicalN i ≤ δ)
    (hactive : q * cutoff * H / L ≤ δ) :
    ∀ j, q * cutoff / forecastJointGridScale U basis R L physicalN τ j ≤ δ := by
  intro j
  cases j with
  | inl i =>
    have hi : (physicalN i : ℝ) ≠ 0 := by exact_mod_cast (hN i).ne'
    have he : q * cutoff / (τ * physicalN i / 8) =
        q * cutoff * 8 * τ⁻¹ / physicalN i := by
      field_simp [hτ.ne', hi]
    exact he.trans_le (hspatial i)
  | inr a =>
    exact (allocatedActiveIntegerGridScale_mesh U basis hR hL
      (mul_nonneg hq hcutoff) hRinv a).trans hactive

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem forecastJointGridSamplerFloor_lower (d : ℕ) (P E Q PR : ℝ) :
    Real.exp (forecastJointGridSamplerLog d P E Q PR) ≤
      (forecastJointGridSamplerFloor d P E Q PR : ℝ) := Nat.le_ceil _

private theorem forecastGrid_exp_div_le {a B H : ℝ} {N : ℕ}
    (ha : a ≤ Real.exp B) (hN : Real.exp (B + H) ≤ (N : ℝ)) :
    a / N ≤ Real.exp (-H) := by
  have hNpos : (0 : ℝ) < N := (Real.exp_pos _).trans_le hN
  apply (div_le_iff₀ hNpos).mpr
  calc
    a ≤ Real.exp B := ha
    _ = Real.exp (-H) * Real.exp (B + H) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hN (Real.exp_nonneg _)

namespace VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {X : Type*} [Fintype X]

omit [Fintype X] in
theorem forecastJointGridScale_mesh_of_exp_bounds
    (d : ℕ) {P E Q Pτ PR : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    {R : Fin m → ℝ} (hR : ∀ j, 0 < R j) {τ : ℝ} (hτ : 0 < τ)
    (q L : ℕ) (physicalN : X → ℕ)
    (hq : (q : ℝ) ≤ Real.exp Q) (hτinv : τ⁻¹ ≤ Real.exp Pτ)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp PR)
    (hL : Real.exp (forecastJointGridSamplerLog d P E Q PR) ≤ (L : ℝ))
    (hN : ∀ i, Real.exp (forecastJointGridAmbientLog d P E Q Pτ) ≤ (physicalN i : ℝ)) :
    ∀ j, (((q * forecastJointGridCutoff P E : ℕ) : ℝ) /
      forecastJointGridScale U basis R L physicalN τ j) ≤ forecastJointGridMesh d P E := by
  have hLpos : 0 < L := Nat.cast_pos.mp ((Real.exp_pos _).trans_le hL)
  have hNpos (i : X) : 0 < physicalN i :=
    Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hN i))
  have hT := forecastJointGridCutoff_le_exp hP hE
  have hqT : (q : ℝ) * forecastJointGridCutoff P E ≤ Real.exp (Q + (P + E + 5)) := by
    rw [Real.exp_add]
    exact mul_le_mul hq hT (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hactive : (q : ℝ) * forecastJointGridCutoff P E * Real.exp PR / L ≤
      forecastJointGridMesh d P E := by
    apply forecastGrid_exp_div_le (B := Q + (P + E + 5) + PR)
    · rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hqT (Real.exp_nonneg _)
    · exact hL
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    calc
      _ = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hspatial (i : X) : (q : ℝ) * forecastJointGridCutoff P E * 8 * τ⁻¹ / physicalN i ≤
      forecastJointGridMesh d P E := by
    apply forecastGrid_exp_div_le (B := Q + (P + E + 5) + 3 + Pτ)
    · have hnum := mul_le_mul
        (mul_le_mul hqT h8 (by norm_num) (Real.exp_nonneg _))
        hτinv (inv_nonneg.mpr hτ.le) (by positivity)
      exact hnum.trans_eq (by rw [← Real.exp_add, ← Real.exp_add])
    · convert hN i using 1
      congr 1
      unfold forecastJointGridAmbientLog
      ring
  have hm := forecastJointGridScale_mesh U basis hR hLpos physicalN hNpos hτ
    (Nat.cast_nonneg q) (Nat.cast_nonneg (forecastJointGridCutoff P E)) hRinv hspatial hactive
  intro j
  simpa only [Nat.cast_mul] using hm j

omit [Fintype X] in
theorem forecastJointGridScale_mesh_of_floor
    (d : ℕ) {P E Q Pτ PR : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    {R : Fin m → ℝ} (hR : ∀ j, 0 < R j) {τ : ℝ} (hτ : 0 < τ)
    (q L : ℕ) (physicalN : X → ℕ)
    (hq : (q : ℝ) ≤ Real.exp Q) (hτinv : τ⁻¹ ≤ Real.exp Pτ)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp PR)
    (hL : forecastJointGridSamplerFloor d P E Q PR ≤ L)
    (hN : ∀ i, Real.exp (forecastJointGridAmbientLog d P E Q Pτ) ≤ (physicalN i : ℝ)) :
    ∀ j, (((q * forecastJointGridCutoff P E : ℕ) : ℝ) /
      forecastJointGridScale U basis R L physicalN τ j) ≤ forecastJointGridMesh d P E := by
  apply forecastJointGridScale_mesh_of_exp_bounds U basis d hP hE hR hτ q L physicalN
    hq hτinv hRinv _ hN
  exact (forecastJointGridSamplerFloor_lower d P E Q PR).trans (by exact_mod_cast hL)

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedModelPrecision
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ (Real.exp (-cost) / 2) s.P s.Pbad s.Ppres)

namespace ActualFixedSpatialSlicedForecastPath

include hR in
omit [DecidableEq X] in
theorem comparisonPrecision_grid_mesh
    {Pu V E : ℝ} (hPu : 0 ≤ Pu) (hE : 0 ≤ E)
    (d q : ℕ) (hq : (q : ℝ) ≤ Real.exp V)
    (hfloor : comparisonPrecisionFloor s d Pu V E ≤ S.value)
    (hN : ∀ i, Real.exp (forecastJointGridAmbientLog d (comparisonGridLog s Pu)
      (E + 4) V s.Pτ) ≤ (physicalN i : ℝ)) :
    ∀ j, (((q * forecastJointGridCutoff (comparisonGridLog s Pu) (E + 4) : ℕ) : ℝ) /
      forecastJointGridScale U b R S.value physicalN τ j) ≤
      forecastJointGridMesh d (comparisonGridLog s Pu) (E + 4) := by
  apply forecastJointGridScale_mesh_of_floor U b d (hPu.trans (le_max_left _ _))
    (by linarith : 0 ≤ E + 4) hR s.hτ q S.value physicalN hq s.hτinv
    (fun j => (s.hK j).trans s.hKBound) _ hN
  exact (le_max_right _ _).trans hfloor

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ (Real.exp (-cost) / 2) s.P s.Pbad s.Ppres)

namespace ActualFixedSpatialSlicedForecastPath

omit [Fintype Tsp] in

theorem comparisonPrecision_geometry
    {Pu V E : ℝ} (hPu : 2 ≤ Pu) (hE : 0 ≤ E)
    (d q : ℕ) (hq0 : 0 < q) (hq : (q : ℝ) ≤ Real.exp V)
    (hfloor : comparisonPrecisionFloor s d Pu V E ≤ S.value)
    (hHP : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      ∀ p : B a.val × Fin (layerSamplerDegree I n a.val),
        Real.exp (-cost) * S.value ≤ (slice.principalLength ⟨a.val,p⟩ : ℝ))
    (hHG : ∀ g, Real.exp (-cost) * S.value ≤ (slice.kernelLength g : ℝ)) :
    (∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      ∀ p : B a.val × Fin (layerSamplerDegree I n a.val),
        2 ≤ slice.principalLength ⟨a.val,p⟩ ∧ q ≤ slice.principalLength ⟨a.val,p⟩ ∧
          scalarCubeGridBoundaryConstant Empty *
            ((q : ℝ) / slice.principalLength ⟨a.val,p⟩) < 1) ∧
    (∀ g, 2 ≤ slice.kernelLength g ∧ q ≤ slice.kernelLength g ∧
      scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / slice.kernelLength g) < 1) ∧
    (∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      ∀ p : B a.val × Fin (layerSamplerDegree I n a.val),
        Real.exp (-cost) * S.value ≤
          ((integerProgressionSupport (slice.principalStart ⟨a.val,p⟩) (slice.step : ℤ)
            (slice.principalLength ⟨a.val,p⟩)).card : ℝ)) := by
  let HP := fun j : PrincipalTupleIndex
    (fun a : {a // ¬allocatedShortAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) => slice.principalLength ⟨j.1.val,j.2⟩
  have hcard : (Fintype.card (PrincipalTupleIndex
      (fun a : {a // ¬allocatedShortAxis (I := I) U b S.value a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)) : ℝ) ≤ s.D :=
    (Nat.cast_le.mpr (allocatedOriginalSampleLiftInput_card_le_allAxis B U b S)).trans s.hD.tuples
  have hF : 0 ≤ 2 * Pu + (E + 4) + 14 := by linarith
  have hsource : fixedPathSlicedGridMeshFloor s.D 4 V cost (2 * Pu + (E + 4) + 14) ≤ S.value :=
    (le_max_left _ _).trans hfloor
  have hp := fixedPathSlicedGridMesh_of_floor s.hD.nonneg (by norm_num : (0 : ℝ) ≤ 4)
    hF HP hcard hq0 hq hsource (fun j => hHP j.1 j.2)
    (fun _ => (0 : ℝ)) (fun _ => by positivity)
  have hg := fixedPathSlicedGridMesh_of_floor s.hD.nonneg (by norm_num : (0 : ℝ) ≤ 4)
    hF slice.kernelLength s.hD.kernel_variables hq0 hq hsource hHG
    (fun _ => (0 : ℝ)) (fun _ => by positivity)
  refine ⟨fun a p => hp.2.2.2 ⟨a,p⟩, hg.2.2.2, ?_⟩
  intro a p
  rw [card_integerProgressionSupport _ _ _ slice.step_pos]
  exact hHP a p

omit [DecidableEq X] [Fintype Tsp] in

theorem comparisonPrecision_tail
    {Pu E : ℝ} (hcost : 0 ≤ cost) (hPu : 2 ≤ Pu) (hE : 0 ≤ E)
    (hAL : (s.L : ℝ) ≤ Real.exp Pu) :
    let F := 2 * Pu + (E + 4) + 14
    let η := Real.exp (-F)
    let t := Real.exp (-fixedPathSlicedPerturbationLog s.D (s.D + Pu + 4) (cost + 1) F m)
    0 < t ∧ t ≤ 1 ∧ 0 < η ∧ η ≤ 1 ∧
      |t| * polynomialMassC2Budget
        (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
          B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
      slicedPrincipalC2Tolerance
        (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
          B a.val × Fin (layerSamplerDegree I n a.val)))
        (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}) m 1
        (unitProfilePrincipalLowerBound B) (Real.exp (-cost) / 2) s.L η := by
  intro F η t
  have hF : 0 ≤ F := by dsimp only [F]; linarith
  have hη : 0 < η := Real.exp_pos _
  have ht := allocatedFixedPathSlicedPerturbation_chosen_tail_s2 (G := G) B U b
    s.hD.nonneg (by linarith : 0 ≤ Pu) hcost hF s.hD.tuples s.haxes s.L
    hη hAL (by dsimp only [η]; rw [Real.exp_neg, inv_inv])
  exact ⟨ht.1, ht.2.1, hη, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hF), ht.2.2 S⟩

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ (Real.exp (-cost) / 2) s.P s.Pbad s.Ppres)

namespace ActualFixedSpatialSlicedForecastPath

variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (originalpoly j))
variable (ξ : ℝ) (hξ : 0 < ξ)
variable (hbox : ∀ x, 0 < physicalN x)
variable (hframe : slice.path.noise ∈ rectangularWeightIndices 0
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1)
variable {Pu V E : ℝ}
variable (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
  s.D (s.D + Pu + 4) (cost + 1) (2 * Pu + (E + 4) + 14) m))
variable (q : ℕ) [NeZero q]
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (hqN : q ∣ slice.path.referenceModulus)
variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
variable (htrimbase : slice.path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))

variable {Pnative massLog capLog Edata Ptest : ℝ}
variable (data : ActualForecastData physicalN originalpoly Pnative massLog capLog Edata)
variable (hcenter : data.centerConstant = fun j => (slice.path.center j).val)
variable (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) τ)
variable (hUniversal : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
  ‖slice.targetAt (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb poly hm s.κ u -
    ∑ i, data.coefficient i * (data.twists i).eval physicalN
      (fun j => subtractConstant (data.centerConstant j) (poly j)) u‖ ≤ Real.exp (-Edata))
variable (hPtest : 0 ≤ Ptest) (hLw : (Lip : ℝ) ≤ Real.exp Ptest)
variable (hpw : periodCap ≤ Real.exp Ptest) (hcw : coverCap ≤ Real.exp Ptest)
variable {Rrank : ℝ} (hEprec : 0 ≤ massLog + E + 8)
variable (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * Pnative + 3) + 1)) (massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
variable (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * Pnative + 3) + 1)) (massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
  Rrank (U j) (originalpoly j))
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {sampleFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {readFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I Eout n B → ℤ}
variable (hglobal : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
  originalpoly hmem (allocatedShortAxis (I := I) U b S.value) spatial kernel block C
  center slice.path.center slice.path.base sampleFn readFn)
variable (hz : allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
  center slice.path.base slice.path.noise ≠ 0)
variable (hsampleAt : sampleFn slice.path.noise = slice.path.sample)
variable (hreadAt : readFn slice.path.noise = slice.path.read)

variable (hfinite : (integerBox physicalN).Nonempty)
variable (htarget : data.target = slice.target (allocatedShortIntegerSelection U b S.value)
  s.hBactive o bW hb originalpoly hmem s.κ)
variable (hcost : 0 ≤ cost) (hPu : 2 ≤ Pu) (hE : 0 ≤ E)
variable (hDsq : s.D * s.D ≤ Pu) (hAL : (s.L : ℝ) ≤ Real.exp Pu)
variable (hτ1 : τ ≤ 1) (hLip : (Lip : ℝ) ≤ Real.exp Pu)
variable (hq : (q : ℝ) ≤ Real.exp V)
variable (hfloor : comparisonPrecisionFloor s (Dmod + Fintype.card (Σ j, I j)) Pu V E ≤ S.value)
variable (hHP : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val),
    Real.exp (-cost) * S.value ≤ (slice.principalLength ⟨a.val,p⟩ : ℝ))
variable (hHG : ∀ g, Real.exp (-cost) * S.value ≤ (slice.kernelLength g : ℝ))
variable (hstep : (slice.step : ℝ) ≤ 2 * Real.exp cost)
variable (hξsmall : ξ ≤ Real.exp (-(2 * Pu + (E + 4) + 14)))
variable (hEdata : E + 8 ≤ Edata)
variable (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
  (Dmod + Fintype.card (Σ j, I j)) (comparisonGridLog s Pu)
  (E + 4) V s.Pτ) ≤ (physicalN i : ℝ))

include hR hσ hdegree hξ hbox hframe hσbound hperiod hcover hqN
  ν hlattice hcompact hmargin htrimbase hcenter hκ hUniversal hPtest hLw hpw hcw
  hEprec hlarge hRrank hrank hglobal hz hsampleAt hreadAt hfinite htarget
  hcost hPu hE hDsq hAL hτ1 hLip hq hfloor hHP hHG hstep hξsmall hEdata hNgrid in

theorem native_ambient_model_precision :
    ‖slice.nativeMean s W originalpoly -
      (FiniteProbabilityWeights.uniformFinset (integerBox physicalN) hfinite).complexMean
        (fun u => W.eval physicalN
          (fun j => subtractConstant (data.centerConstant j) (originalpoly j)) u.val *
            data.target u)‖ ≤ Real.exp (-E) := by
  have hPu0 : 0 ≤ Pu := by linarith
  have hE4 : 0 ≤ E + 4 := by linarith
  have hPg : 0 ≤ comparisonGridLog s Pu := hPu0.trans (le_max_left _ _)
  have hgeom := slice.comparisonPrecision_geometry s hPu hE
    (Dmod + Fintype.card (Σ j, I j)) q (NeZero.pos q) hq hfloor hHP hHG
  have htail := comparisonPrecision_tail s hcost hPu hE hAL
  have hgrid := comparisonPrecision_grid_mesh s (hR := hR) hPu0 hE
    (Dmod + Fintype.card (Σ j, I j)) q hq hfloor hNgrid
  have hgridbounds := forecastJointGridMesh_bounds
    (Dmod + Fintype.card (Σ j, I j)) hPg hE4
  have hcomp := slice.native_ambient_model_comparison_s2
    (s := s) (hb := hb) (o := o) (bW := bW) (W := W) (originalpoly := originalpoly)
    (hmem := hmem) (hdegree := hdegree) (ξ := ξ) (hξ := hξ) (hbox := hbox)
    (hframe := hframe) (ht := htail.1) (hσbound := hσbound)
    (hδ := Real.exp_pos (-cost))
    (hδone := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hcost))
    (hdense := hgeom.2.2) (q := q) (hperiod := hperiod) (hcover := hcover) (hqN := hqN)
    (hsizeG := fun g => (hgeom.2.1 g).2.1)
    (hsmallG := fun g => (hgeom.2.1 g).2.2)
    (hsize := fun a p => (hgeom.1 a p).2.1)
    (hsmall := fun a p => (hgeom.1 a p).2.2)
    (ε := 2 * Real.exp cost / S.value) (hε := by positivity)
    (hmesh := div_le_div_of_nonneg_right hstep (Nat.cast_nonneg S.value))
    (hη := htail.2.2.1) (htail := htail.2.2.2.2)
    (ν := ν) (hmargin := hmargin) (htrimbase := htrimbase)
    (data := data) (hcenter := hcenter) (hκ := hκ) (hUniversal := hUniversal)
    (hPtest := hPtest) (hLw := hLw) (hpw := hpw) (hcw := hcw)
    (hEprec := hEprec) (hlarge := hlarge) (hRrank := hRrank) (hrank := hrank)
    (cutoff := forecastJointGridCutoff (comparisonGridLog s Pu) (E + 4))
    (hcutoff := forecastJointGridCutoff_pos hPg hE4)
    (hδgrid := hgridbounds.1.le) (hδgrid1 := hgridbounds.2) (hgridmesh := hgrid)
    (C := C) (hglobal := hglobal) (hz := hz) (hsampleAt := hsampleAt)
    (hreadAt := hreadAt) (hfinite := hfinite) (htarget := htarget)
  exact hcomp.trans (slice.comparisonError_le_exp_s2 s o hcost hPu hE hDsq hAL
    hτ1 hLip q hq hfloor hHP hHG hξ.le hξsmall le_rfl hEdata)

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedSourceLog
namespace OAI

section

namespace Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X] {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} [Fintype A] {Dmod : ℕ} {selected : A → Σ j, Fin (n j)}
variable {τ δslice : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice)

omit [Fintype A] in
theorem transitionLip_le_Pcap : (s.L : ℝ) ≤ s.Pcap := by
  have h := s.hprimitiveCap
  have hpad : 0 ≤ paddedResidueDensityCap Empty 1 := by
    unfold paddedResidueDensityCap scalarCubeResidueDensityCap
    positivity
  norm_num [scalarCubePrimitiveEnvelope, scalarCubeCutoffDerivativeNumerator,
    scalarCubeGridBoundaryConstant] at h
  linarith [s.L.coe_nonneg]

omit [Fintype A] in
theorem transitionLip_le_exp : (s.L : ℝ) ≤ Real.exp s.pcap :=
  s.transitionLip_le_Pcap.trans s.hPcapp

end Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup

end

section

namespace Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X] {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} {Dmod : ℕ} {selected : A → Σ j, Fin (n j)}
variable {τ δslice : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice)

theorem slicedComparisonSourceLog_bounds (Ptest : ℝ) :
    2 ≤ s.slicedComparisonSourceLog Ptest ∧
    s.D * s.D ≤ s.slicedComparisonSourceLog Ptest ∧
    (s.L : ℝ) ≤ Real.exp (s.slicedComparisonSourceLog Ptest) ∧
    Ptest ≤ s.slicedComparisonSourceLog Ptest := by
  have hD := mul_self_nonneg s.D
  have hc := s.hpcap
  have hmax : 0 ≤ max 0 Ptest := le_max_left _ _
  have htest : Ptest ≤ max 0 Ptest := le_max_right _ _
  have hpc : s.pcap ≤ s.slicedComparisonSourceLog Ptest := by
    unfold slicedComparisonSourceLog
    linarith
  refine ⟨?_, ?_, s.transitionLip_le_exp.trans (Real.exp_le_exp.mpr hpc), ?_⟩ <;>
    unfold slicedComparisonSourceLog <;> linarith

end Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActualFiberSlicedBoundedTwistPrecision
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable {qnum : ActualFixedSpatialSlicedForecastNumerics s}
variable {δbase PpresBase : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ δbase s.P s.Pbad PpresBase)
variable (input : ActualFixedSpatialDenseSliceInput s qnum)
variable (hcost_match : input.cost = cost)

namespace ActualFixedSpatialForecastPath

variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (originalpoly j))
variable (ξ : ℝ) (hξ : 0 < ξ)
variable (hbox : ∀ x, 0 < physicalN x)
variable (hframe : path.noise ∈ rectangularWeightIndices 0
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1)
variable {V E Ptest : ℝ}
variable (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
  s.D (s.D + (s.slicedComparisonSourceLog Ptest) + 4) (cost + 1) (2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14) m))
variable (q : ℕ) [NeZero q]
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (hqN : q ∣ path.referenceModulus)
variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
variable (htrimbase : path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))

variable {Pnative massLog capLog Edata : ℝ}
variable (data : ActualForecastData physicalN originalpoly Pnative massLog capLog Edata)
variable (hcenter : data.centerConstant = fun j => (path.center j).val)
variable (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) τ)
variable (hUniversal : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
  ‖(path.toDenseSliceMember input).slice.targetAt (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb poly hm s.κ u -
    ∑ i, data.coefficient i * (data.twists i).eval physicalN
      (fun j => subtractConstant (data.centerConstant j) (poly j)) u‖ ≤ Real.exp (-Edata))
variable (hPtest : 0 ≤ Ptest) (hLw : (Lip : ℝ) ≤ Real.exp Ptest)
variable (hpw : periodCap ≤ Real.exp Ptest) (hcw : coverCap ≤ Real.exp Ptest)
variable {Rrank : ℝ} (hEprec : 0 ≤ massLog + E + 8)
variable (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * Pnative + 3) + 1)) (massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
variable (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * Pnative + 3) + 1)) (massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
  Rrank (U j) (originalpoly j))
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {sampleFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {readFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I Eout n B → ℤ}
variable (hglobal : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
  originalpoly hmem (allocatedShortAxis (I := I) U b S.value) spatial kernel block C
  center path.center path.base sampleFn readFn)
variable (hz : allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
  center path.base path.noise ≠ 0)
variable (hsampleAt : sampleFn path.noise = path.sample)
variable (hreadAt : readFn path.noise = path.read)

variable (hfinite : (integerBox physicalN).Nonempty)
variable (htarget : data.target = (path.toDenseSliceMember input).slice.target (allocatedShortIntegerSelection U b S.value)
  s.hBactive o bW hb originalpoly hmem s.κ)
variable (hcost : 0 ≤ cost) (hE : 0 ≤ E)
variable (hτ1 : τ ≤ 1)
variable (hq : (q : ℝ) ≤ Real.exp V)
variable (hfloor : ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest) V E ≤ S.value)
variable (hξsmall : ξ ≤ Real.exp (-(2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14)))
variable (hEdata : E + 8 ≤ Edata)
variable (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
  (Dmod + Fintype.card (Σ j, I j)) (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
  (E + 4) V s.Pτ) ≤ (physicalN i : ℝ))

include hR hσ hdegree hξ hbox hframe hσbound hperiod hcover hqN
  ν hlattice hcompact hmargin htrimbase hcenter hκ hUniversal hPtest hLw hpw hcw
  hEprec hlarge hRrank hrank hglobal hz hsampleAt hreadAt hfinite htarget
  hcost hE hτ1 hq hfloor hξsmall hEdata hNgrid hcost_match in

theorem denseFiber_ambient_model_precision_s2_oai :
    ‖(input.box.fiberSliceLaw input.length_pos input.fixed input.fixed_inside).complexMean
        (fun z => W.eval physicalN (path.physicalPolynomial originalpoly)
          (fun a => path.base a + integerPhysicalSite z.val path.noise a)) -
      (FiniteProbabilityWeights.uniformFinset (integerBox physicalN) hfinite).complexMean
        (fun u => W.eval physicalN
          (fun j => subtractConstant (data.centerConstant j) (originalpoly j)) u.val * data.target u)‖ ≤
      Real.exp (-E) := by
  obtain ⟨hPu, hDsq, hAL, htest⟩ := s.slicedComparisonSourceLog_bounds Ptest
  have hLip := hLw.trans (Real.exp_le_exp.mpr htest)
  have hHP : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      ∀ p : B a.val × Fin (layerSamplerDegree I n a.val),
        Real.exp (-cost) * S.value ≤
          ((path.toDenseSliceMember input).slice.principalLength ⟨a.val,p⟩ : ℝ) := by
    intro a p
    change Real.exp (-cost) * S.value ≤
      (input.box.fiberParameterLength (Sum.inr ⟨a.val,p⟩) : ℝ)
    rw [input.box.fiberParameterLength_of_keep _ (input.active_kept a p)]
    simpa only [Sum.elim_inr, allocatedPrincipalSides_not_short B U b S a p, hcost_match]
      using input.dense ⟨Sum.inr ⟨a.val,p⟩, input.active_kept a p⟩
  have hHG : ∀ g, Real.exp (-cost) * S.value ≤
      ((path.toDenseSliceMember input).slice.kernelLength g : ℝ) := by
    intro g
    change Real.exp (-cost) * S.value ≤ (input.box.length ⟨Sum.inl g,input.kernel_kept g⟩ : ℝ)
    simpa only [Sum.elim_inl, hcost_match] using input.dense ⟨Sum.inl g,input.kernel_kept g⟩
  have hstep : ((path.toDenseSliceMember input).slice.step : ℝ) ≤ 2 * Real.exp cost := by
    change (input.step : ℝ) ≤ 2 * Real.exp cost
    simpa only [hcost_match] using input.step_le
  have hcomp := (path.toDenseSliceMember input).slice.native_ambient_model_precision
    (s := s) (hb := hb) (o := o) (bW := bW) (W := W) (originalpoly := originalpoly)
    (hmem := hmem) (hdegree := hdegree) (ξ := ξ) (hξ := hξ) (hbox := hbox) (hframe := hframe)
    (hσbound := hσbound) (q := q) (hperiod := hperiod) (hcover := hcover) (hqN := hqN)
    (ν := ν) (hmargin := hmargin) (htrimbase := htrimbase)
    (data := data) (hcenter := hcenter) (hκ := hκ) (hUniversal := hUniversal)
    (hPtest := hPtest) (hLw := hLw) (hpw := hpw) (hcw := hcw)
    (hEprec := hEprec) (hlarge := hlarge) (hRrank := hRrank) (hrank := hrank)
    (C := C) (hglobal := hglobal) (hz := hz) (hsampleAt := hsampleAt) (hreadAt := hreadAt)
    (hfinite := hfinite) (htarget := htarget) (hcost := hcost) (hPu := hPu) (hE := hE)
    (hDsq := hDsq) (hAL := hAL) (hτ1 := hτ1) (hLip := hLip) (hq := hq) (hfloor := hfloor)
    (hHP := hHP) (hHG := hHG) (hstep := hstep) (hξsmall := hξsmall) (hEdata := hEdata)
    (hNgrid := hNgrid)
  rw [path.toDenseSliceMember_nativeMean_s2 input W originalpoly] at hcomp
  exact hcomp

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.denseFiber_ambient_model_precision_s2_oai := @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.denseFiber_ambient_model_precision_s2_oai
