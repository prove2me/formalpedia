-- Prove2me | solution 1 for GlobalTheory.KeyKa.discr_jacobian_of_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:43:37.092404+00:00
-- url     : https://prove2.me/submissions/4023e097-8d8f-4315-9da2-3bae40232626

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsUnitDetOfProductMapNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PointMatrixMulLeftMulMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrEqJacobianOfIntegralPoints
import Theorems.Thm_GlobalTheory_KeyKa_exists_basis_det_ne_zero_of_points
import Theorems.Thm_GlobalTheory_DiscrJacobian_associated_discr_norm_jacobian
import Theorems.Thm_GlobalTheory_DiscrJacobian_der_tmul
import Theorems.Thm_GlobalTheory_DiscrJacobian_exists_eq_C_add_sum
import Theorems.Thm_GlobalTheory_DiscrJacobian_mu_tmul
import Theorems.Thm_GlobalTheory_DiscrJacobian_pairing_tmul
import Theorems.Thm_GlobalTheory_KeyKa_discr_norm_eq_of_points
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DiscrJacobian.der_tmul
attribute [local simp] GlobalTheory.DiscrJacobian.mu_tmul
attribute [local simp] GlobalTheory.DiscrJacobian.pairing_tmul



set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa
namespace GlobalTheory.KeyKa
theorem _root_.solution :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (g : ℕ) (Ix : Type) [Fintype Ix]
      [DecidableEq Ix] (F : Fin g → (MvPowerSeries (Fin g) O))
      (e : Ix → ((MvPowerSeries (Fin g) O) →ₐ[O] O)), (∀ a i, e a (F i) = 0) →
      (∀ a i, e a (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal O) →
      (∀ G, (∀ a, e a G = 0) → G ∈ Ideal.span (Set.range F)) →
      (∃ c : O, c ≠ 0 ∧ ∀ t : Ix → O, ∃ G, ∀ a, e a G = c * t a) →
      ∃ β : Ix → (MvPowerSeries (Fin g) O),
        (∀ G, ∃! r : Ix → O, G - ∑ a, r a • β a ∈ Ideal.span (Set.range F)) ∧
        (Matrix.of fun a a' => e a (β a')).det ≠ 0 ∧
        Associated ((Matrix.of fun a a' => e a (β a')).det ^ 2)
          (∏ a, e a (Matrix.of fun i j => MvPowerSeries.pderiv O j (F i)).det) := by
  intro O _ _ _ _ g Ix _ _ F e hF hX hker ⟨c, hc, hs⟩
  let S := MvPowerSeries (Fin g) O
  let I : Ideal S := Ideal.span (Set.range F)
  let eb : Ix → ((S ⧸ I) →ₐ[O] O) := fun a => Ideal.Quotient.liftₐ I (e a) (fun s hs => by
    have : I ≤ RingHom.ker (e a) := Ideal.span_le.2 (by
      rintro _ ⟨i, rfl⟩
      exact hF a i)
    exact this hs)
  have heb : ∀ a s, eb a (Ideal.Quotient.mk I s) = e a s := fun a s => rfl
  let φ : (S ⧸ I) →ₗ[O] (Ix → O) := LinearMap.pi fun a => (eb a).toLinearMap
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hker s fun a => congrFun hy a)
  obtain ⟨b, hb⟩ := exists_basis_det_ne_zero_of_points φ hφ c hc fun t => by
    obtain ⟨G, hG⟩ := hs t
    exact ⟨Ideal.Quotient.mk I G, funext hG⟩
  choose β hβ using fun a => Ideal.Quotient.mk_surjective (b a)
  have hM : (Matrix.of fun a a' => e a (β a')) = Matrix.of fun a a' => eb a (b a') := by
    ext a a'
    rw [Matrix.of_apply, Matrix.of_apply, ← hβ, heb]
  have hb' : (Matrix.of fun a a' => eb a (b a')).det ≠ 0 := hb
  have hq : ∀ (G : S) (r : Ix → O), G - ∑ a, r a • β a ∈ I ↔
      Ideal.Quotient.mk I G = ∑ a, r a • b a := by
    intro G r
    rw [← Ideal.Quotient.eq, ← Ideal.Quotient.mkₐ_eq_mk O, map_sum]
    simp only [map_smul, Ideal.Quotient.mkₐ_eq_mk, hβ]
  refine ⟨β, fun G => ⟨b.equivFun (Ideal.Quotient.mk I G), ?_, fun r hr => ?_⟩, ?_, ?_⟩
  · exact (hq G _).2 (b.sum_equivFun _).symm
  · rw [(hq G r).1 hr, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
  · rw [hM]; exact hb'
  · rcases isEmpty_or_nonempty Ix with h | ⟨⟨a⟩⟩
    · simp
    · have hf : ∀ i, MvPowerSeries.constantCoeff (F i) ∈ IsLocalRing.maximalIdeal O := by
        intro i
        obtain ⟨u, hu⟩ := GlobalTheory.DiscrJacobian.exists_eq_C_add_sum (F i)
        have h1 := congrArg (e a) hu
        have h2 : e a (MvPowerSeries.C (MvPowerSeries.constantCoeff (F i)))
            = MvPowerSeries.constantCoeff (F i) := (e a).commutes _
        rw [hF, map_add, h2, map_sum] at h1
        rw [eq_neg_of_add_eq_zero_left h1.symm]
        refine neg_mem (Ideal.sum_mem _ fun j _ => ?_)
        rw [map_mul]
        exact Ideal.mul_mem_right _ _ (hX a j)
      have h1 := GlobalTheory.DiscrJacobian.associated_discr_norm_jacobian O g _ F
        (b.reindex (Fintype.equivFin Ix)) hf
      obtain ⟨h2, h3⟩ := discr_norm_eq_of_points O (S ⧸ I) Ix b eb hb'
      rw [Module.Basis.coe_reindex, Algebra.discr_reindex, h2, h3] at h1
      rw [hM]
      exact h1
end GlobalTheory.KeyKa
