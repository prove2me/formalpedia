-- Prove2me | solution 1 for GlobalTheory.NormCompat.RatioClose.norm_div_close_to_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:43:47.550357+00:00
-- url     : https://prove2.me/submissions/2e2ce7a1-d0ae-47cb-a6d6-16faea3bf1d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormCloseToOneOfCloseAbovePlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTensorIdempotentOfAlgHomToBaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqMulNormIdempotentCornerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationLeOneOfSqSubSelfIntegralBasisStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGlobalElementNearIdempotentAdicCompletionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormDivLocalEmbeddingCloseToOne
import Theorems.Thm_P2M_GlobalTheory_NormCompat_RatioClose_norm_one_tmul__0e587e6c05b4
import Theorems.Thm_GlobalTheory_NormCompat_NormCont_norm_close_to_one
import Theorems.Thm_GlobalTheory_T_exists_global_element_near_idempotent_adicCompletion
import Theorems.Thm_GlobalTheory_T_exists_tensor_idempotent_of_algHom_to_base
import Theorems.Thm_GlobalTheory_T_norm_eq_mul_norm_idempotent_corner
import Theorems.Thm_GlobalTheory_T_valuation_le_one_of_sq_sub_self_integral_basis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct
open GlobalTheory GlobalTheory.NormCompat GlobalTheory.NormCompat.RatioClose
namespace GlobalTheory.NormCompat.RatioClose
theorem _root_.solution : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')) (σ : E' →+* w.adicCompletion E), (∀ x : E, σ (algebraMap E E' x) = algebraMap E _ x) → (∀ x : E', Valued.v (σ x) = w'.valuation E' x) → ∀ M : ℕ, ∃ M' : ℕ, ∀ z : E', z ≠ 0 → (∀ w'' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'), w''.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = w.asIdeal → w'' ≠ w' → w''.valuation E' (z - 1) ≤ WithZero.exp (-(M' : ℤ))) → Valued.v (algebraMap E (w.adicCompletion E) (Algebra.norm E z) / σ z - 1) ≤ WithZero.exp (-(M : ℤ)) := by
  intro E E' _ _ _ _ _ w w' σ hσ hv M
  classical
  obtain ⟨M₁, hM₁⟩ := GlobalTheory.NormCompat.NormCont.norm_close_to_one E E' w M
  refine ⟨M₁, fun z hz0 hz => ?_⟩
  set K := w.adicCompletion E
  let σA : E' →ₐ[E] K := { σ with commutes' := hσ }
  let ψ : K ⊗[E] E' →ₐ[K] K := Algebra.TensorProduct.lift (Algebra.ofId K K) σA (fun _ _ => Commute.all _ _)
  have hψ : ∀ x : E', ψ ((1 : K) ⊗ₜ x) = σ x := fun x => by
    simp [ψ, σA, Algebra.TensorProduct.lift_tmul]
  obtain ⟨e, he1, he⟩ := GlobalTheory.T.exists_tensor_idempotent_of_algHom_to_base E K E' ψ
  have hee : e * e = e := by rw [he, he1, map_one, one_mul]
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral (𝓞 E) E E'
  have hb' : ∀ i, IsIntegral ℤ (b i) := fun i => isIntegral_trans _ (hb i)
  have hvK : ∀ x : E, Valued.v (algebraMap E K x) = w.valuation E x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  have hβ : ∀ x : E', x ≠ 0 → algebraMap E K (Algebra.norm E x) / σ x =
      Algebra.norm K (e + (1 - e) * ((1 : K) ⊗ₜ x)) := by
    intro x hx
    have h2 := GlobalTheory.T.norm_eq_mul_norm_idempotent_corner K (K ⊗[E] E') ψ e he1 he ((1 : K) ⊗ₜ x)
    rw [norm_one_tmul', hψ] at h2
    rw [h2, mul_div_cancel_left₀ _ ((map_ne_zero σ).2 hx)]
  let Z : K ⊗[E] E' := (1 : K) ⊗ₜ z
  set p : K ⊗[E] E' := e + (1 - e) * Z with hp
  set q : K ⊗[E] E' := (1 - e) * (1 - Z) with hq
  obtain ⟨K₀, hK₂, hK₁, hK₃⟩ : ∃ K₀ : ℕ, M ≤ K₀ ∧ M₁ ≤ K₀ ∧ 1 ≤ K₀ := ⟨M + M₁ + 1, by omega, by omega, by omega⟩
  set m : ℤ := (w'.valuation E' (z - 1)).log with hm
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, M ≤ n ∧ (K₀ : ℤ) + m ≤ n := ⟨M + K₀ + m.toNat, by omega, by omega⟩
  obtain ⟨ε, hε1, hε2, hε3⟩ := GlobalTheory.T.exists_global_element_near_idempotent_adicCompletion E E' w b ψ e hee he1 p q n
  set y : E' := ε + (1 - ε) * z with hy
  have hy1 : y - 1 = (1 - ε) * (z - 1) := by rw [hy]; ring
  have hw'ε : w'.valuation E' (ε - 1) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [← hv, map_sub, map_one, ← hψ]; exact hε2
  have hw'y : w'.valuation E' (y - 1) ≤ WithZero.exp (-(K₀ : ℤ)) := by
    rw [hy1, map_mul, Valuation.map_sub_swap]
    by_cases hz1 : w'.valuation E' (z - 1) = 0
    · rw [hz1, mul_zero]; exact zero_le'
    calc w'.valuation E' (ε - 1) * w'.valuation E' (z - 1)
        ≤ WithZero.exp (-(n : ℤ)) * WithZero.exp m := by
          rw [hm, WithZero.exp_log hz1]; exact mul_le_mul' hw'ε le_rfl
      _ = WithZero.exp (-(n : ℤ) + m) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp (-(K₀ : ℤ)) := by
          rw [WithZero.exp_le_exp]; omega
  have hall : ∀ w'' : HeightOneSpectrum (𝓞 E'), w''.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = w.asIdeal →
      w''.valuation E' (y - 1) ≤ WithZero.exp (-(M₁ : ℤ)) := by
    intro w'' h1
    by_cases h2 : w'' = w'
    · subst h2
      exact hw'y.trans (WithZero.exp_le_exp.2 (by omega))
    rw [hy1, map_mul]
    have hi := GlobalTheory.T.valuation_le_one_of_sq_sub_self_integral_basis E E' b hb' w w'' h1 ε hε1
    have h1e : w''.valuation E' (1 - ε) ≤ 1 :=
      (Valuation.map_sub _ _ _).trans (max_le (by simp) hi)
    calc w''.valuation E' (1 - ε) * w''.valuation E' (z - 1) ≤ 1 * WithZero.exp (-(M₁ : ℤ)) :=
          mul_le_mul' h1e (hz w'' h1 h2)
      _ = _ := one_mul _
  have hN := hM₁ y hall
  have hσy : Valued.v (σ y - 1) ≤ WithZero.exp (-(K₀ : ℤ)) := by
    rw [← map_one σ, ← map_sub, hv]; exact hw'y
  have hσy1 : Valued.v (σ y) = 1 := by
    have hlt : Valued.v (σ y - 1) < Valued.v (1 : K) := by
      rw [map_one]
      refine hσy.trans_lt ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    rw [Valuation.map_eq_of_sub_lt _ hlt, map_one]
  have hσy0 : σ y ≠ 0 := fun h => by rw [h, map_zero] at hσy1; exact zero_ne_one hσy1
  have hy0 : y ≠ 0 := fun h => hσy0 (by rw [h, map_zero])
  have hry : Valued.v (algebraMap E K (Algebra.norm E y) / σ y - 1) ≤ WithZero.exp (-(M : ℤ)) := by
    rw [div_sub_one hσy0, map_div₀, hσy1, div_one]
    have : algebraMap E K (Algebra.norm E y) - σ y =
        (algebraMap E K (Algebra.norm E y) - 1) - (σ y - 1) := by ring
    rw [this]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ (hσy.trans (WithZero.exp_le_exp.2 (by omega))))
    rw [← map_one (algebraMap E K), ← map_sub, hvK]; exact hN
  have hid : e + (1 - e) * ((1 : K) ⊗ₜ y) = p + q * ((1 : K) ⊗ₜ ε - e) := by
    have h1 : (1 : K) ⊗ₜ[E] y = (1 : K) ⊗ₜ ε + (1 - (1 : K) ⊗ₜ ε) * Z := by
      have := map_add (Algebra.TensorProduct.includeRight (R := E) (A := K) (B := E')) ε ((1 - ε) * z)
      simp only [Algebra.TensorProduct.includeRight_apply, map_mul, map_sub, map_one] at this
      rw [hy, this]
    rw [h1, hp, hq]
    linear_combination (Z - 1) * hee
  have hbz := hβ z hz0
  have hby : algebraMap E K (Algebra.norm E y) / σ y = Algebra.norm K (p + q * ((1 : K) ⊗ₜ ε - e)) := by
    rw [hβ y hy0, hid]
  rw [hbz]
  have : Algebra.norm K p - 1 = (Algebra.norm K (p + q * ((1 : K) ⊗ₜ ε - e)) - 1) -
      (Algebra.norm K (p + q * ((1 : K) ⊗ₜ ε - e)) - Algebra.norm K p) := by ring
  rw [this]
  refine (Valuation.map_sub _ _ _).trans (max_le (hby ▸ hry) (hε3.trans (WithZero.exp_le_exp.2 ?_)))
  omega
end GlobalTheory.NormCompat.RatioClose
