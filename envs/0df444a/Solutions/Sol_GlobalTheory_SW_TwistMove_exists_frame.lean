-- Prove2me | solution 1 for GlobalTheory.SW.TwistMove.exists_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:27:41.758976+00:00
-- url     : https://prove2.me/submissions/eb2c3052-8b58-4041-8df9-e6cf8aff9dc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalMatrixMoveAdmissibleUniformLevel
import Theorems.Thm_GlobalTheory_SW_Base_mem_stdL
import Theorems.Thm_GlobalTheory_SW_NearPrim_exists_approx
import Theorems.Thm_GlobalTheory_SW_NearPrim_exists_reduce
import Theorems.Thm_GlobalTheory_SW_NearPrim_exists_rows
import Theorems.Thm_GlobalTheory_SW_NearPrim_integral_coord
import Theorems.Thm_GlobalTheory_SW_TwistAdm_colsIn_mulVec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TwistMove
open GlobalTheory.SW.TwistAdm
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
namespace GlobalTheory.SW.TwistMove
theorem _root_.solution (E : Type) [Field E] [NumberField E] (N : ℕ) : ∃ c : ℕ, 0 < c ∧
    ∀ (𝔛 : Lt E N) (t : ℕ), 0 < t → (∀ v ∈ 𝔛, (t : E) • v ∈ stdL E N) →
      (∀ v ∈ stdL E N, (t : E) • v ∈ 𝔛) → ∃ b : Matrix (Fin N) (Fin N) E, b.det ≠ 0 ∧
        (∀ v ∈ stdL E N, b *ᵥ v ∈ 𝔛) ∧ ∀ u, b *ᵥ u ∈ 𝔛 → (c : E) • u ∈ stdL E N := by
  obtain ⟨C, hC⟩ := NearPrim.exists_reduce E
  obtain ⟨M, hM⟩ := NearPrim.exists_approx E
  refine ⟨M.factorial ^ N, pow_pos M.factorial_pos _, fun 𝔛 t ht h1 h2 => ?_⟩
  have ht0 : (t : E) ≠ 0 := Nat.cast_ne_zero.2 ht.ne'
  let L : AddSubgroup (Fin N → E) :=
    { carrier := {s | (t : E) • s ∈ 𝔛}
      add_mem' := fun {s t} hs ht => by
        rw [Set.mem_setOf_eq, smul_add]; exact add_mem hs ht
      zero_mem' := by simp
      neg_mem' := fun {s} hs => by rw [Set.mem_setOf_eq, smul_neg]; exact neg_mem hs }
  have hO : ∀ s : Fin N → E, (∀ i, IsIntegral ℤ (s i)) → s ∈ L := fun s hs =>
    h2 s ((Base.mem_stdL s).2 hs)
  have hsm : ∀ y : E, IsIntegral ℤ y → ∀ s ∈ L, y • s ∈ L := fun y hy s hs => by
    change (t : E) • y • s ∈ 𝔛
    rw [smul_comm]
    exact 𝔛.smul_mem (⟨y, hy⟩ : 𝓞 E) hs
  have hden : ∀ s ∈ L, ∀ i, IsIntegral ℤ (((t * t : ℤ) : E) * s i) := fun s hs i => by
    have := (Base.mem_stdL _).1 (h1 _ hs) i
    simpa [mul_assoc] using this
  choose a haL ha0 hai haC hmin using NearPrim.exists_rows L hO (t * t)
    (by positivity) hden C hC
  refine ⟨(t : E) • (Matrix.of a)ᵀ, ?_, fun v hv => ?_, fun u hu => ?_⟩
  · rw [Matrix.det_smul, Matrix.det_transpose,
      Matrix.det_of_lowerTriangular (Matrix.of a) (fun i j h => ha0 i j h)]
    exact mul_ne_zero (pow_ne_zero _ ht0) (Finset.prod_ne_zero_iff.2 fun i _ => hai i)
  · exact colsIn_mulVec (fun j => haL j) hv
  · rw [Matrix.smul_mulVec, Matrix.mulVec_transpose] at hu
    exact (Base.mem_stdL _).2 (NearPrim.integral_coord L hsm M hM (Matrix.of a) haL ha0 hai hmin N
      le_rfl u (fun j hj => absurd j.2 (not_lt.2 hj)) hu)
end GlobalTheory.SW.TwistMove
