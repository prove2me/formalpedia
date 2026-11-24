-- Prove2me | solution 1 for GlobalTheory.FinTypCount.cong_of_code
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:28:19.129296+00:00
-- url     : https://prove2.me/submissions/f5cf8fc8-9940-421f-af4d-f088d4969820

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsFinTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankLeAleph0SmoothIrreducibleUnitaryAdelic
import Theorems.Thm_GlobalTheory_FinTypCount_inv_val
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Idele_smul_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2.NG
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.FinTypCount
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => NumberField.maximalRealSubfield L
variable {n : ℕ}
namespace GlobalTheory.FinTypCount
theorem _root_.solution {N m : ℕ} {c : Fin n → Fin n → L} {g g' : GAf L n}
    (hg : ∀ i j, (m : AL L) * (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L)
    (e : ∀ i j, ∃ y ∈ ALint L, (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j =
      c i j ⊗ₜ[L⁺] (1 : AFplus L) + (m * N) • y)
    (e' : ∀ i j, ∃ y ∈ ALint L, (g'.1 : Matrix (Fin n) (Fin n) (AL L)) i j =
      c i j ⊗ₜ[L⁺] (1 : AFplus L) + (m * N) • y) :
    Cong L n N (g⁻¹ * g') := by
  choose y hy ey using e
  choose y' hy' ey' using e'
  set A : Matrix (Fin n) (Fin n) (AL L) := (((g⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hAdef
  have hAint : ∀ i j, (m : AL L) * A i j ∈ ALint L := by
    intro i j
    rw [hAdef, inv_val]
    simp only [conjT, Matrix.transpose_apply, Matrix.map_apply]
    have := conjAL_mem_ALint L (hg j i)
    rwa [map_mul, map_natCast] at this
  have hAG : A * (g.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := Units.inv_mul g.1
  set Y : Matrix (Fin n) (Fin n) (AL L) := Matrix.of fun i j => y' i j - y i j
  have hG' : (g'.1 : Matrix (Fin n) (Fin n) (AL L)) =
      (g.1 : Matrix (Fin n) (Fin n) (AL L)) + (N : AL L) • ((m : AL L) • Y) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Y, Matrix.of_apply, smul_eq_mul, ey, ey',
      nsmul_eq_mul]
    push_cast
    ring
  have hk : (((g⁻¹ * g' : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      1 + (N : AL L) • (((m : AL L) • A) * Y) := by
    change A * (g'.1 : Matrix (Fin n) (Fin n) (AL L)) = _
    rw [hG', Matrix.mul_add, hAG, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hz : ∀ i j, (((m : AL L) • A) * Y) i j ∈ ALint L := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, Y, Matrix.of_apply, smul_eq_mul]
    exact Subring.sum_mem _ fun k _ =>
      Subring.mul_mem _ (hAint i k) (Subring.sub_mem _ (hy' k j) (hy k j))
  refine ⟨fun i j => ?_, fun i j => ⟨_, hz i j, ?_⟩⟩
  · show (((g⁻¹ * g' : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L
    rw [hk, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine Subring.add_mem _ ?_ (Subring.mul_mem _ (natCast_mem _ _) (hz i j))
    rw [Matrix.one_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · rw [hk, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
end GlobalTheory.FinTypCount
