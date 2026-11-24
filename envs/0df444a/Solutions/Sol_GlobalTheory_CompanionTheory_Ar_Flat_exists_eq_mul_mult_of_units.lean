-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Flat.exists_eq_mul_mult_of_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:18:37.782905+00:00
-- url     : https://prove2.me/submissions/01fcbce1-25d0-4645-9c42-94143f70e85d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_ExistsEqMulMultOfUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem
namespace GlobalTheory.CompanionTheory.Ar.Flat
theorem _root_.solution (F : Type) [Field F] [NumberField F]
    (D : InfinitePlace F → ℝ)
    (h : ∀ u : (𝓞 F)ˣ, ∑ w : InfinitePlace F, Real.log (w ((u : 𝓞 F) : F)) * D w = 0) :
    ∃ c : ℝ, ∀ w, D w = c * (mult w : ℝ) := by
  classical
  have hsplit : ∀ f : InfinitePlace F → ℝ,
      ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)}, f v.1 = ∑ w, f w - f (w₀ : InfinitePlace F) := by
    intro f
    rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ (w₀ : InfinitePlace F)), add_sub_cancel_right]
    exact (Finset.sum_subtype _ (fun w => by simp) f).symm
  let a : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ :=
    fun v => D v.1 / (mult v.1 : ℝ) - D (w₀ : InfinitePlace F) / (mult (w₀ : InfinitePlace F) : ℝ)
  let φ : ({w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ v, x v * a v
      map_add' := fun x y => by simp [Finset.sum_add_distrib, add_mul]
      map_smul' := fun r x => by simp [Finset.mul_sum, mul_assoc] }
  have hφ : ∀ u : (𝓞 F)ˣ, φ (logEmbedding F (Additive.ofMul u)) = 0 := by
    intro u
    have e1 : ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)},
        Real.log (v.1 (algebraMap (𝓞 F) F u)) * D v.1
          = 0 - Real.log ((w₀ : InfinitePlace F) (algebraMap (𝓞 F) F u)) * D (w₀ : InfinitePlace F) := by
      rw [← h u]
      exact hsplit (fun w => Real.log (w (algebraMap (𝓞 F) F u)) * D w)
    have e2 : ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)},
        (mult v.1 : ℝ) * Real.log (v.1 (algebraMap (𝓞 F) F u))
          = 0 - (mult (w₀ : InfinitePlace F) : ℝ) * Real.log ((w₀ : InfinitePlace F) (algebraMap (𝓞 F) F u)) := by
      rw [← sum_mult_mul_log u]
      exact hsplit (fun w => (mult w : ℝ) * Real.log (w (algebraMap (𝓞 F) F u)))
    have hm0 : (mult (w₀ : InfinitePlace F) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr mult_ne_zero
    show ∑ v, logEmbedding F (Additive.ofMul u) v * a v = 0
    simp only [logEmbedding_component]
    calc ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)},
          (mult v.1 : ℝ) * Real.log (v.1 (algebraMap (𝓞 F) F u)) * a v
        = ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)},
          (Real.log (v.1 (algebraMap (𝓞 F) F u)) * D v.1
            - D (w₀ : InfinitePlace F) / (mult (w₀ : InfinitePlace F) : ℝ) * ((mult v.1 : ℝ) * Real.log (v.1 (algebraMap (𝓞 F) F u)))) := by
          apply Finset.sum_congr rfl
          intro v _
          have hm : (mult v.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr mult_ne_zero
          simp only [a]
          field_simp
          try ring
      _ = 0 := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, e1, e2]
          field_simp
          try ring
  have hle : Submodule.span ℝ (unitLattice F : Set (logSpace F)) ≤ LinearMap.ker φ := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨y, -, rfl⟩ := hx
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact hφ (Additive.toMul y)
  rw [unitLattice_span_eq_top F] at hle
  have ha : ∀ v, a v = 0 := by
    intro v
    have hv : (Pi.single v (1 : ℝ) : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ) ∈ LinearMap.ker φ :=
      hle Submodule.mem_top
    rw [LinearMap.mem_ker] at hv
    have hφv : φ (Pi.single v (1 : ℝ)) = a v := by
      show ∑ v', (Pi.single v (1 : ℝ) : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ) v' * a v' = a v
      simp [Pi.single_apply]
    rw [← hφv]
    exact hv
  refine ⟨D (w₀ : InfinitePlace F) / (mult (w₀ : InfinitePlace F) : ℝ), fun w => ?_⟩
  have hm : (mult w : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr mult_ne_zero
  by_cases hw : w = (w₀ : InfinitePlace F)
  · subst hw
    field_simp
  · have hv := ha ⟨w, hw⟩
    simp only [a, sub_eq_zero] at hv
    rw [← hv]
    field_simp
end GlobalTheory.CompanionTheory.Ar.Flat
