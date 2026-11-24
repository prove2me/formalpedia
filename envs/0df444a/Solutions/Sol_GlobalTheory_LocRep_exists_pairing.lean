-- Prove2me | solution 1 for GlobalTheory.LocRep.exists_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:36.007654+00:00
-- url     : https://prove2.me/submissions/520088f0-c113-4d85-afd8-4ea246f391a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
import Theorems.Thm_GlobalTheory_LocRep_rep_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.LocRep
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ}
open MeasureTheory
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ}
namespace GlobalTheory.LocRep
namespace _root_.GlobalTheory.LocRep
theorem _root_.solution
    (hloc : ∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖)
    (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) {C : Set G} (hC : IsCompact C) :
    ∃ Λ : K →L[ℂ] ℂ, ∀ v, Λ v = ∫ x in C, ι v x ∂μ := by
  obtain ⟨M, hM⟩ := hloc C hC
  have hint : ∀ (a : ℂ) v w, ∫ x in C, ι (a • v + w) x ∂μ =
      a * ∫ x in C, ι v x ∂μ + ∫ x in C, ι w x ∂μ := by
    intro a v w
    rw [integral_congr_ae (ae_restrict_of_ae (hlin a v w)),
      integral_add ((hM v).1.const_mul a) (hM w).1, integral_const_mul]
  have hz : ∫ x in C, ι 0 x ∂μ = 0 := by
    rw [integral_congr_ae (ae_restrict_of_ae (_root_.GlobalTheory.LocRep.rep_zero hlin))]
    simp
  let L : K →ₗ[ℂ] ℂ :=
    { toFun := fun v => ∫ x in C, ι v x ∂μ
      map_add' := fun v w => by simpa using hint 1 v w
      map_smul' := fun a v => by
        simp only [RingHom.id_apply, smul_eq_mul]
        simpa [hz] using hint a v 0 }
  refine ⟨L.mkContinuous M fun v => ?_, fun v => rfl⟩
  exact (norm_integral_le_integral_norm _).trans (hM v).2
end _root_.GlobalTheory.LocRep
end GlobalTheory.LocRep
