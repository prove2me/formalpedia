-- Prove2me | solution 1 for GlobalTheory.Hk.LamRay.lamRay_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:13:31.087249+00:00
-- url     : https://prove2.me/submissions/b6cd9e9b-f954-459f-a030-63359b7aa827

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsImagQuadIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PrimeIdealsCountingBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumLamIdealLe
import Theorems.Thm_GlobalTheory_Hk_LamRay_lamIdeal_nonneg
import Theorems.Thm_GlobalTheory_Hk_LamRay_sum_lamIdeal_le
import Theorems.Thm_GlobalTheory_Hk_LamRay_exists_gen
import Theorems.Thm_GlobalTheory_Hk_LamRay_normOne_span
import Theorems.Thm_GlobalTheory_Hk_LamRay_finite_idealsIn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LamRay
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Hk.LamRay
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (d M : ℕ) (x : K), d.Prime → d % 4 = 3 → 100 ≤ d → x ^ 2 = -(d : K) → Module.finrank ℚ K = 2 → 3 ≤ M → ∀ D : RayData K M, (∀ g n, 0 ≤ lamRay D g n) ∧ (∀ n : ℕ, ∑ g : D.G, lamRay D g n ≤ 2 * Λ n) ∧ ∀ p : ℕ, p.Prime → lamRay D 1 p ≠ 0 → GlobalTheory.Mem.An.NormOne d M p := by
  intro K _ _ d M x hp hd _ hx hK _ D
  refine ⟨fun g n => ?_, fun n => ?_, fun p _ h => ?_⟩
  · exact finsum_nonneg fun I => finsum_nonneg fun _ => lamIdeal_nonneg I
  · have e : ∀ g, lamRay D g n = ∑ I ∈ (finite_idealsIn D g n).toFinset, lamIdeal I := fun g =>
      finsum_mem_eq_finite_toFinset_sum _ _
    simp only [e]
    rw [← Finset.sum_biUnion]
    · refine sum_lamIdeal_le hK n _ fun I hI => ?_
      obtain ⟨g, -, hg⟩ := Finset.mem_biUnion.1 hI
      exact ((Set.Finite.mem_toFinset _).1 hg).2.2.1
    · intro g _ g' _ hgg
      refine Finset.disjoint_left.2 fun I h1 h2 => hgg ?_
      exact ((Set.Finite.mem_toFinset _).1 h1).2.2.2.symm.trans ((Set.Finite.mem_toFinset _).1 h2).2.2.2
  · have hne : (idealsIn D 1 p).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h0
      apply h
      unfold lamRay
      rw [h0, finsum_mem_empty]
    obtain ⟨I, h0, hc, hN, hcl⟩ := hne
    obtain ⟨a, b, ha, -, ha1, hb1, hab⟩ := (D.cls_eq_one_iff hc h0).1 hcl
    have hb : b ∈ Ideal.span {a} := by
      have : Ideal.span {b} ≤ Ideal.span {a} := hab ▸ Ideal.mul_le_left
      exact this (Ideal.mem_span_singleton_self b)
    obtain ⟨π, rfl⟩ := Ideal.mem_span_singleton.1 hb
    rw [← Ideal.span_singleton_mul_span_singleton] at hab
    have hI : I = Ideal.span {π} :=
      mul_left_cancel₀ (by simpa [Ideal.span_singleton_eq_bot] using ha) hab
    have hπ : π - 1 ∈ Ideal.span {(M : 𝓞 K)} := by
      have : π - 1 = (a * π - 1) - π * (a - 1) := by ring
      rw [this]
      exact Ideal.sub_mem _ hb1 (Ideal.mul_mem_left _ _ ha1)
    obtain ⟨ω, hgen, hnorm⟩ := exists_gen hp hd hx hK
    rw [← hN, hI]
    exact normOne_span hgen hnorm hπ
end GlobalTheory.Hk.LamRay
