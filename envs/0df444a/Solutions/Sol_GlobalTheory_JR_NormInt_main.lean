-- Prove2me | solution 1 for GlobalTheory.JR.NormInt.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:21:07.441875+00:00
-- url     : https://prove2.me/submissions/6e0932ee-ba44-4195-8c21-5eae118c95c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PsiKMulNLEqOneOnIntegralLattice
import Theorems.Thm_GlobalTheory_JR_NormInt_traceE
import Theorems.Thm_GlobalTheory_JR_Et_quadratic_structure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NormInt
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.NormInt
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.K) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ y : A.L, (∀ i, ‖j y i‖ ≤ 1) → A.psiK ψ (x * A.NL y) = 1 := by
  intro F E _ _ _ _ U A ψ hψ x r j hj y hy
  have := U.charZero
  have := U.ultraE
  have hE2 : Module.Finite F E := Module.finite_of_finrank_pos (by rw [U.finrank_eq]; norm_num)
  obtain ⟨⟨c⟩, hinj, hN, htr, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have : Module.Free A.K A.L := Module.Free.of_basis c
  have : Module.Finite A.K A.L := Module.Finite.of_basis c
  have : Module.Free E A.L := Module.Free.of_basis (A.push.out.basis (Module.Free.chooseBasis F A.K))
  have : Module.Finite E A.L := Module.Finite.of_basis (A.push.out.basis (Module.Free.chooseBasis F A.K))
  set s : E := star (j y) ⬝ᵥ j y with hs_def

  have hs1 : ‖s‖ ≤ 1 := by
    rw [hs_def, dotProduct]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [Pi.star_apply, norm_mul, U.norm_star]
    exact mul_le_one₀ (hy i) (norm_nonneg _) (hy i)

  have hss : star s = s := by
    rw [hs_def, dotProduct, star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.star_apply, star_mul', star_star, mul_comm]
  have hsL : s = Algebra.trace E A.L (algebraMap A.K A.L x * star y * y) := hj y y
  set T : F := Algebra.trace F A.K (x * A.NL y) with hT
  have hz : algebraMap A.K A.L (x * A.NL y) = algebraMap A.K A.L x * star y * y := by
    rw [map_mul, hN, mul_assoc, mul_comm y]
  have htK : ∀ k : A.K, Algebra.trace A.K A.L (algebraMap A.K A.L k) = 2 • k := by
    intro k
    apply hinj
    rw [htr, A.star_K, map_nsmul, two_nsmul]
  have h1 : Algebra.trace F A.L (algebraMap A.K A.L (x * A.NL y)) = 2 • T := by
    rw [← Algebra.trace_trace (S := A.K), htK, map_nsmul]
  have h2 : Algebra.trace F A.L (algebraMap A.K A.L (x * A.NL y)) = Algebra.trace F E s := by
    rw [← Algebra.trace_trace (S := E), hz, hsL]
  have h3 : algebraMap F E T = s := by
    have e := congrArg (algebraMap F E) (h1.symm.trans h2)
    rw [traceE, hss, map_nsmul, two_nsmul, ← two_mul, ← two_mul] at e
    have : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
    have h20 : (2 : E) ≠ 0 := two_ne_zero
    exact mul_left_cancel₀ h20 e
  have hT1 : ‖T‖ ≤ 1 := by rw [← norm_algebraMap' E T, h3]; exact hs1
  exact hψ.1 T hT1
end GlobalTheory.JR.NormInt
