-- Prove2me | solution 1 for M4aLocalCFT.decompositionSubgroup_exists_integralNormalBasis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/fc613080-0624-5cc0-b7aa-d052d2da012a

import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aLocalCFT_decompositionSubgroup_exists_integralNormalBasis

set_option autoImplicit false

open scoped Matrix

namespace M4aLocalCFT

namespace IntegralNormalBasis

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

local notation "G" => (ValuationSubring.decompositionSubgroup K A)

scoped instance instFaithfulSMul : FaithfulSMul (A.decompositionSubgroup K) L where
  eq_of_smul_eq_smul {s t} h := by
    apply Subtype.ext
    ext x
    exact h x

variable (K) in
private theorem _root_.M4aLocalCFT.IntegralNormalBasis.smul_mem {x : L} (s : G) (hx : x ∈ A) : s • x ∈ A :=
  (A.subMulAction K).smul_mem s hx

p2m_export "M4aLocalCFT.IntegralNormalBasis" "smul_mem"
variable (K) in
theorem smul_coe_fixed (s : G) (r : FixedPoints.subfield G L) : s • (r : L) = r :=
  r.2 s

section Fin

variable [Fintype (A.decompositionSubgroup K)]

variable (K) in

def fixedProd (y : L) : L := ∏ s : G, s • y

theorem smul_fixedProd (t : G) (y : L) : t • fixedProd K A y = fixedProd K A y := by
  unfold fixedProd
  rw [Finset.smul_prod']
  simp_rw [← mul_smul]
  exact Fintype.prod_bijective (t * ·) (Group.mulLeft_bijective t) _ _ (fun _ => rfl)

theorem fixedProd_mem {y : L} (hy : y ∈ A) : fixedProd K A y ∈ A := by
  unfold fixedProd
  exact prod_mem fun s _ => smul_mem K A s hy

theorem fixedProd_ne_zero {y : L} (hy : y ≠ 0) : fixedProd K A y ≠ 0 := by
  unfold fixedProd
  exact Finset.prod_ne_zero_iff.2 fun s _ => (smul_ne_zero_iff_ne s).2 hy

theorem fixedProd_mul_mem {y x : L} (hy : y ∈ A) (hyx : y * x ∈ A) : fixedProd K A y * x ∈ A := by
  classical
  unfold fixedProd
  rw [← Finset.mul_prod_erase Finset.univ (fun s : G => s • y) (Finset.mem_univ 1), one_smul,
    mul_right_comm]
  exact mul_mem hyx (prod_mem fun s _ => smul_mem K A s hy)

theorem fixedProd_mem_fixed (y : L) : fixedProd K A y ∈ FixedPoints.subfield G L :=
  fun t => smul_fixedProd A t y

theorem exists_normalElt : ∃ x : L,
    LinearIndependent (FixedPoints.subfield G L) (fun s : G => s • x) := by
  obtain ⟨x, hx⟩ := exists_linearIndependent_algEquiv_apply (FixedPoints.subfield G L) L
  exact ⟨x, hx.comp _ (FixedPoints.toAlgAutMulEquiv G L).injective⟩

theorem exists_integral_normalElt : ∃ α : L, α ∈ A ∧
    LinearIndependent (FixedPoints.subfield G L) (fun s : G => s • α) := by
  obtain ⟨x, hx⟩ := exists_normalElt (K := K) A

  obtain ⟨y, hyA, hy0, hyx⟩ : ∃ y : L, y ∈ A ∧ y ≠ 0 ∧ y * x ∈ A := by
    rcases A.mem_or_inv_mem x with h | h
    · exact ⟨1, one_mem A, one_ne_zero, by rwa [one_mul]⟩
    · by_cases hx0 : x = 0
      · exact ⟨1, one_mem A, one_ne_zero, by rw [hx0, mul_zero]; exact zero_mem A⟩
      · exact ⟨x⁻¹, h, inv_ne_zero hx0, by rw [inv_mul_cancel₀ hx0]; exact one_mem A⟩
  refine ⟨fixedProd K A y * x, fixedProd_mul_mem A hyA hyx, ?_⟩
  let u : (FixedPoints.subfield G L)ˣ :=
    Units.mk0 ⟨fixedProd K A y, fixedProd_mem_fixed A y⟩
      (fun h => fixedProd_ne_zero A hy0 (congrArg Subtype.val h))
  convert hx.units_smul (fun _ => u) using 1
  funext s
  simp only [Pi.smul_apply', smul_mul', smul_fixedProd]
  rfl

section Matrix

local notation "IsNB" A "," α =>
  LinearIndependent (FixedPoints.subfield (ValuationSubring.decompositionSubgroup K A) L)
    (fun s : ValuationSubring.decompositionSubgroup K A => s • α)

noncomputable def nbasis {α : L} (hα : IsNB A, α) : Module.Basis G (FixedPoints.subfield G L) L :=
  basisOfLinearIndependentOfCardEqFinrank hα (FixedPoints.finrank_eq_card G L).symm

theorem nbasis_apply {α : L} (hα : IsNB A, α) (s : G) : nbasis A hα s = s • α := by
  simp [nbasis]

variable [DecidableEq (A.decompositionSubgroup K)]

variable (K) in

noncomputable def conjMatrix (α : L) : Matrix G G L := Matrix.of fun ρ σ => (ρ * σ) • α

variable (K) in

noncomputable def conjMatrixInt {α : L} (hαA : α ∈ A) : Matrix G G A :=
  Matrix.of fun ρ σ => ⟨(ρ * σ) • α, smul_mem K A _ hαA⟩

theorem conjMatrix_eq_map {α : L} (hαA : α ∈ A) :
    conjMatrix K A α = A.subtype.mapMatrix (conjMatrixInt K A hαA) := by
  ext ρ σ
  rfl

theorem det_conjMatrix_mem {α : L} (hαA : α ∈ A) : (conjMatrix K A α).det ∈ A := by
  rw [conjMatrix_eq_map A hαA, ← RingHom.map_det]
  exact SetLike.coe_mem _

theorem adjugate_conjMatrix_mem {α : L} (hαA : α ∈ A) (ρ σ : G) :
    (conjMatrix K A α).adjugate ρ σ ∈ A := by
  rw [conjMatrix_eq_map A hαA, ← RingHom.map_adjugate, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact SetLike.coe_mem _

theorem det_conjMatrix_ne_zero {α : L} (hα : IsNB A, α) : (conjMatrix K A α).det ≠ 0 := by
  suffices h : IsUnit (conjMatrix K A α) by
    exact ((Matrix.isUnit_iff_isUnit_det _).1 h).ne_zero
  rw [← Matrix.linearIndependent_rows_iff_isUnit, Fintype.linearIndependent_iff]
  intro g hg ρ₀

  have hind : LinearIndependent L
      (fun ρ : G => (MulSemiringAction.toAlgHom (FixedPoints.subfield G L) L ρ).toLinearMap) :=
    (linearIndependent_algHom_toLinearMap (FixedPoints.subfield G L) L L).comp _
      (FixedPoints.toAlgHom_bijective G L).1
  rw [Fintype.linearIndependent_iff] at hind
  refine hind g ?_ ρ₀

  apply (nbasis A hα).ext
  intro σ
  have := congr_fun hg σ
  simp only [Finset.sum_apply, Pi.smul_apply, Matrix.row, conjMatrix, Matrix.of_apply,
    smul_eq_mul, Pi.zero_apply] at this
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
    LinearMap.zero_apply, nbasis_apply, smul_eq_mul, mul_smul] at this ⊢
  exact this

theorem smul_det_conjMatrix (α : L) (t : G) :
    t • (conjMatrix K A α).det =
      ((Equiv.Perm.sign (Equiv.mulLeft t) : ℤ) : L) * (conjMatrix K A α).det := by
  have h1 : t • (conjMatrix K A α).det =
      (MulSemiringAction.toRingHom G L t) (conjMatrix K A α).det := rfl
  rw [h1, RingHom.map_det, ← Matrix.det_permute]
  congr 1

theorem smul_det_conjMatrix_sq (α : L) (t : G) :
    t • ((conjMatrix K A α).det ^ 2) = (conjMatrix K A α).det ^ 2 := by
  rw [smul_pow', smul_det_conjMatrix, mul_pow, ← Int.cast_pow, ← Units.val_pow_eq_pow_val,
    Int.units_sq, Units.val_one, Int.cast_one, one_mul]

theorem det_mul_repr_mem {α : L} (hαA : α ∈ A) (hα : IsNB A, α) {a : L} (ha : a ∈ A) (σ : G) :
    (conjMatrix K A α).det * ((nbasis A hα).repr a σ : L) ∈ A := by
  set W := conjMatrix K A α with hW
  set cv : G → L := fun σ => ((nbasis A hα).repr a σ : L) with hcv
  set v : G → L := fun ρ => ρ • a with hv

  have hsum : ∑ σ, ((nbasis A hα).repr a σ : L) * σ • α = a := by
    conv_rhs => rw [← (nbasis A hα).sum_repr a]
    simp only [nbasis_apply]
    rfl
  have hWc : W *ᵥ cv = v := by
    funext ρ
    simp only [hv, Matrix.mulVec, dotProduct, hW, conjMatrix, Matrix.of_apply, hcv]
    conv_rhs => rw [← hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_mul', smul_coe_fixed, mul_smul, mul_comm]
  have hadj : W.adjugate *ᵥ v = W.det • cv := by
    rw [← hWc, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hσ := congr_fun hadj σ
  simp only [Pi.smul_apply, smul_eq_mul] at hσ
  rw [← hσ]
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun ρ _ => mul_mem (adjugate_conjMatrix_mem A hαA σ ρ) (smul_mem K A ρ ha)

theorem main {α : L} (hαA : α ∈ A) (hα : IsNB A, α) :
    ∃ d : L, d ∈ A ∧ d ≠ 0 ∧ (∀ s : G, s • d = d) ∧
      ∀ a : L, a ∈ A → ∃ c : G → L,
        (∀ s, c s ∈ A) ∧ (∀ s t : G, t • c s = c s) ∧ d * a = ∑ s, c s * s • α := by
  refine ⟨(conjMatrix K A α).det ^ 2, pow_mem (det_conjMatrix_mem A hαA) 2,
    pow_ne_zero 2 (det_conjMatrix_ne_zero A hα), smul_det_conjMatrix_sq A α, fun a ha => ?_⟩
  refine ⟨fun σ => (conjMatrix K A α).det ^ 2 * ((nbasis A hα).repr a σ : L), fun σ => ?_,
    fun σ t => ?_, ?_⟩
  · show (conjMatrix K A α).det ^ 2 * ((nbasis A hα).repr a σ : L) ∈ A
    rw [pow_two, mul_assoc]
    exact mul_mem (det_conjMatrix_mem A hαA) (det_mul_repr_mem A hαA hα ha σ)
  · rw [smul_mul', smul_det_conjMatrix_sq, smul_coe_fixed]
  · conv_lhs => rw [← (nbasis A hα).sum_repr a]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [nbasis_apply, mul_assoc]
    rfl

end Matrix

end Fin

end IntegralNormalBasis
p2m_reactivate "P2MW.S_M4aLocalCFT_decompositionSubgroup_exists_integralNormalBasis.M4aLocalCFT.IntegralNormalBasis"

end M4aLocalCFT
p2m_reactivate "P2MW.S_M4aLocalCFT_decompositionSubgroup_exists_integralNormalBasis.M4aLocalCFT.IntegralNormalBasis P2MW.S_M4aLocalCFT_decompositionSubgroup_exists_integralNormalBasis.M4aLocalCFT"

open M4aLocalCFT.IntegralNormalBasis in
theorem solution
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    [Finite (A.decompositionSubgroup K)] :
    letI := Fintype.ofFinite (A.decompositionSubgroup K)
    ∃ α : L, α ∈ A ∧
      LinearIndependent (FixedPoints.subfield (A.decompositionSubgroup K) L)
        (fun s : A.decompositionSubgroup K => s • α) ∧
      ∃ d : L, d ∈ A ∧ d ≠ 0 ∧ (∀ s : A.decompositionSubgroup K, s • d = d) ∧
        ∀ a : L, a ∈ A → ∃ c : A.decompositionSubgroup K → L,
          (∀ s, c s ∈ A) ∧ (∀ s t : A.decompositionSubgroup K, t • c s = c s) ∧
          d * a = ∑ s, c s * s • α := by
  classical
  letI := Fintype.ofFinite (A.decompositionSubgroup K)
  obtain ⟨α, hαA, hα⟩ := exists_integral_normalElt (K := K) A
  exact ⟨α, hαA, hα, main A hαA hα⟩

end S_M4aLocalCFT_decompositionSubgroup_exists_integralNormalBasis
end P2MW
export P2MW.S_M4aLocalCFT_decompositionSubgroup_exists_integralNormalBasis (solution)
