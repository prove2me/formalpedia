-- Prove2me | solution 1 for GlobalTheory.AdelicMatLat.inv_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:04:44.745668+00:00
-- url     : https://prove2.me/submissions/5f3bb200-30c7-4684-b901-2ffbcddaebf2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsLatticeAdelicMatrixIntegralTranslate
import Theorems.Thm_GlobalTheory_AdelicMatLat_exists_nat_mul_mem_family
import Theorems.Thm_GlobalTheory_AdLat_exists_eq_algebraMap_add_nsmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.AdelicMatLat
variable (E : Type) [Field E] [NumberField E]
variable {E} {n : ℕ}
namespace GlobalTheory.AdelicMatLat
theorem _root_.solution (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (M : ℕ) (δ : GL (Fin n) E)
    (hδ : ∀ x ∈ lat β.1, ∃ y : Fin n → 𝓞 E, (M : E) • x = (fun i => (y i : E)) ᵥ* δ.1)
    (i j : Fin n) :
    (M : FiniteAdeleRing (𝓞 E) E) *
      (β⁻¹.1 * δ⁻¹.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E))) i j ∈ intAdeles E := by
  classical
  obtain ⟨d₁, hd₁, h₁⟩ := exists_nat_mul_mem_family E (fun p : Fin n × Fin n => β.1 p.1 p.2)
  obtain ⟨d₂, hd₂, h₂⟩ := exists_nat_mul_mem_family E
    (fun p : Fin n × Fin n => algebraMap E (FiniteAdeleRing (𝓞 E) E) (δ⁻¹.1 p.1 p.2))
  choose x b hb hx using fun k => GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul E (d₁ * d₂)
    (Nat.mul_pos hd₁ hd₂) (β⁻¹.1 i k)
  have hxl : x ∈ lat β.1 := by
    intro l
    have h3 : ∑ k, algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k) * β.1 k l =
        (β⁻¹.1 * β.1) i l - ∑ k, ((d₂ : FiniteAdeleRing (𝓞 E) E) * b k) *
          ((d₁ : FiniteAdeleRing (𝓞 E) E) * β.1 k l) := by
      rw [Matrix.mul_apply, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hx k, nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [h3, Units.inv_mul]
    refine sub_mem ?_ (sum_mem fun k _ => mul_mem (mul_mem (natCast_mem _ _) (hb k)) (h₁ (k, l)))
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨y, hy⟩ := hδ x hxl
  have h4 : (y j : E) = ∑ k, (M : E) * x k * δ⁻¹.1 k j := by
    have h5 : ((M : E) • x) ᵥ* δ⁻¹.1 = fun i => (y i : E) := by
      rw [hy, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
    rw [← congrFun h5 j]
    rfl
  have h6 : (M : FiniteAdeleRing (𝓞 E) E) *
      (β⁻¹.1 * δ⁻¹.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E))) i j =
      algebraMap E (FiniteAdeleRing (𝓞 E) E) (y j : E) +
        ∑ k, ((M : FiniteAdeleRing (𝓞 E) E) * ((d₁ : FiniteAdeleRing (𝓞 E) E) * b k)) *
          ((d₂ : FiniteAdeleRing (𝓞 E) E) *
            algebraMap E (FiniteAdeleRing (𝓞 E) E) (δ⁻¹.1 k j)) := by
    rw [h4, map_sum, Matrix.mul_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hx k, nsmul_eq_mul, Nat.cast_mul, Matrix.map_apply, map_mul, map_mul, map_natCast]
    ring
  rw [h6]
  exact add_mem ((algebraMap_mem_iff E _).2 ⟨y j, rfl⟩) (sum_mem fun k _ =>
    mul_mem (mul_mem (natCast_mem _ _) (mul_mem (natCast_mem _ _) (hb k))) (h₂ (k, j)))
end GlobalTheory.AdelicMatLat
