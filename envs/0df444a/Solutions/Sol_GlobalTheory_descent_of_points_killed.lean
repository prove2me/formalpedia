-- Prove2me | solution 1 for GlobalTheory.descent_of_points_killed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:47:50.7343+00:00
-- url     : https://prove2.me/submissions/b4d3648c-c0c6-482f-85af-20655a5ebdfc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdAllPowOfFrobeniusEqKilledByPerfectPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DescentOfPointsKilled
import Theorems.Thm_GlobalTheory_T_dvd_all_pow_of_frobenius_eq_killed_by_perfect_points


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] (u : A) (pr : B →ₗ[A] A), ((l : ℕ) : B) = 0 → algebraMap A B u ∈ nonZeroDivisors B → IsHausdorff (Ideal.span {algebraMap A B u}) B → ∀ (κ : Type) [Fintype κ] (x : κ → B), (∀ (T : Type) [CommRing T] (i₁ i₂ : B →+* T), (∀ a, i₁ (algebraMap A B a) = i₂ (algebraMap A B a)) → IsUnit (i₁ (algebraMap A B u)) → ∃ c : κ → κ → T, ∀ j, i₁ (x j) - i₂ (x j) = ∑ i, (i₁ (x i) - i₂ (x i)) ^ l * c i j) → (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ ψ' : B →+* O), ψ (algebraMap A B u) ≠ 0 → ¬ IsUnit (ψ (algebraMap A B u)) → IsAdicComplete (Ideal.span {ψ (algebraMap A B u)}) O → (∀ a, ψ (algebraMap A B a) = ψ' (algebraMap A B a)) → ∀ j, ψ (x j) = ψ' (x j)) → pr 1 = 1 → ∀ j, x j = algebraMap A B (pr (x j)) := by
  intro l _ A B _ _ _ _ u pr hl hu hH κ _ x hEq hPt hpr
  let iL : B →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeLeft
  let iR : B →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeRight
  let U : B ⊗[A] B := algebraMap A (B ⊗[A] B) u
  let D : κ → B ⊗[A] B := fun j => iL (x j) - iR (x j)
  have hiL : ∀ a, iL (algebraMap A B a) = algebraMap A (B ⊗[A] B) a := fun a => iL.commutes a
  have hiR : ∀ a, iR (algebraMap A B a) = algebraMap A (B ⊗[A] B) a := fun a => iR.commutes a

  have hlR : ((l : ℕ) : B ⊗[A] B) = 0 := by
    rw [← map_natCast iL, hl, map_zero]

  have hUreg : U ∈ nonZeroDivisors (B ⊗[A] B) := by
    have hinj : Function.Injective (LinearMap.mulLeft A (algebraMap A B u)) := by
      intro b b' hbb
      have h0 : (b - b') * algebraMap A B u = 0 := by
        simp only [LinearMap.mulLeft_apply] at hbb
        rw [sub_mul, mul_comm b, mul_comm b', hbb, sub_self]
      exact sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff hu).mp h0)
    have hinj' := Module.Flat.rTensor_preserves_injective_linearMap (M := B) _ hinj
    have hmul : ∀ y : B ⊗[A] B, y * U = LinearMap.rTensor B (LinearMap.mulLeft A (algebraMap A B u)) y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b b' =>
        simp [U, Algebra.TensorProduct.algebraMap_apply, mul_comm]
      | add y z hy hz => rw [add_mul, hy, hz, map_add]
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    rw [hmul] at hy
    exact hinj' (by rw [hy, map_zero])

  obtain ⟨h, c', hc'⟩ : ∃ (h : ℕ) (c' : κ → κ → B ⊗[A] B), ∀ j, U ^ h * D j = ∑ i, D i ^ l * c' i j := by
    let T := Localization.Away U
    let i₁ : B →+* T := (algebraMap (B ⊗[A] B) T).comp iL.toRingHom
    let i₂ : B →+* T := (algebraMap (B ⊗[A] B) T).comp iR.toRingHom
    have hA : ∀ a, i₁ (algebraMap A B a) = i₂ (algebraMap A B a) := by
      intro a
      simp only [i₁, i₂, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hiL, hiR]
    have hunit : IsUnit (i₁ (algebraMap A B u)) := by
      simp only [i₁, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hiL]
      exact IsLocalization.Away.algebraMap_isUnit U
    obtain ⟨c, hc⟩ := hEq T i₁ i₂ hA hunit
    obtain ⟨⟨b, hb⟩, hb'⟩ := IsLocalization.exist_integer_multiples (Submonoid.powers U) (S := T)
      (Finset.univ : Finset (κ × κ)) (fun p => c p.1 p.2)
    obtain ⟨h, rfl⟩ := hb
    choose c' hc'' using fun (p : κ × κ) => hb' p (Finset.mem_univ p)
    refine ⟨h, fun i j => c' (i, j), fun j => ?_⟩
    have hD : ∀ i, algebraMap (B ⊗[A] B) T (D i) = i₁ (x i) - i₂ (x i) := by
      intro i; simp [D, i₁, i₂]
    apply IsLocalization.injective T (M := Submonoid.powers U) (Submonoid.powers_le.mpr hUreg)
    rw [map_mul, map_sum, hD, hc j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul, map_pow, hD]
    rw [hc'' (i, j)]
    change _ = _ * ((U ^ h) • c i j)
    rw [Algebra.smul_def, map_pow]
    ring

  have hkey : ∀ (m : ℕ) j, U ^ m ∣ D j := by
    refine GlobalTheory.T.dvd_all_pow_of_frobenius_eq_killed_by_perfect_points l (B ⊗[A] B) U hlR hUreg κ D c' h hc' ?_
    intro O _ _ _ _ _ f hf0 hfnu hcomp j
    let ψ : B →+* O := f.comp iL.toRingHom
    let ψ' : B →+* O := f.comp iR.toRingHom
    have hψ : ψ (algebraMap A B u) = f U := by
      simp only [ψ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hiL, U]
    have hagree : ∀ a, ψ (algebraMap A B a) = ψ' (algebraMap A B a) := by
      intro a
      simp only [ψ, ψ', RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hiL, hiR]
    have := hPt O ψ ψ' (by rw [hψ]; exact hf0) (by rw [hψ]; exact hfnu) (by rw [hψ]; exact hcomp) hagree j
    simp only [ψ, ψ', RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
    simp only [D, map_sub, this, sub_self]

  let φ : B ⊗[A] B →ₗ[A] B := TensorProduct.lift ((LinearMap.lsmul A B).comp pr)
  have hφ : ∀ b b' : B, φ (b ⊗ₜ b') = pr b • b' := fun b b' => by simp [φ]
  intro j
  have hφD : φ (D j) = algebraMap A B (pr (x j)) - x j := by
    simp only [D, map_sub]
    change φ (x j ⊗ₜ 1) - φ (1 ⊗ₜ x j) = _
    rw [hφ, hφ, hpr, one_smul, Algebra.smul_def, mul_one]
  have hmem : ∀ n : ℕ, algebraMap A B (pr (x j)) - x j ∈ Ideal.span {algebraMap A B u ^ n} := by
    intro n
    obtain ⟨r, hr⟩ := hkey n j
    rw [← hφD, hr]
    have : U ^ n * r = u ^ n • r := by simp [U, Algebra.smul_def, map_pow]
    rw [this, LinearMap.map_smul, Algebra.smul_def, map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hz := hH.haus (algebraMap A B (pr (x j)) - x j) (fun n => by
    rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
    exact hmem n)
  exact (sub_eq_zero.mp hz).symm
end GlobalTheory
