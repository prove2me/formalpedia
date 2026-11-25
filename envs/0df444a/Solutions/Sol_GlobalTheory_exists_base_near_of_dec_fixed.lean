-- Prove2me | solution 1 for GlobalTheory.exists_base_near_of_dec_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:29:39.470516+00:00
-- url     : https://prove2.me/submissions/aa1b298f-4950-4423-b6ce-8f9b5743e836

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAlgebraMapSubEqSumConjugatesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjPlacesOfSamePrimeBelowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CrtApproxIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBaseNearOfDecompositionFixed
import Theorems.Thm_GlobalTheory_T_exists_conj_valuationSubring_of_same_below
import Theorems.Thm_GlobalTheory_T_exists_integral_near_one_small_off_decomposition
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
import Theorems.Thm_P2M_GlobalTheory_T_exists_algebraMap_sub_eq_sum_conjugates__8f225b3c9a0f
import Theorems.Thm_ReciprocityTheory_Gal_smul_valuation_lt_one_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open scoped Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (z : Ω), (∀ d ∈ Dec (F := E) A, d z = z) → ∀ r : Ω, r ≠ 0 → ∃ e : E, A.valuation (algebraMap E Ω e - z) < A.valuation r := by
  intro E Ω _ _ _ _ _ A w h z hz r hr
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hint : ∀ x : Ω, IsIntegral ℤ x → A.valuation x ≤ 1 := fun x hx =>
    (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A hx)
  have halg : ∀ x : Ω, IsAlgebraic ℤ x := fun x => by
    have : IsIntegral ℚ x := isIntegral_trans (R := ℚ) (A := E) x (Algebra.IsIntegral.isIntegral x)
    exact (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).mpr this.isAlgebraic

  obtain ⟨b, hb0, hbz⟩ := (halg z).exists_integral_multiple

  obtain ⟨b', hb'0, hb'r⟩ := (halg r⁻¹).exists_integral_multiple

  set m : ℕ := Ideal.absNorm w.asIdeal with hm
  have hm0 : m ≠ 0 := by
    rw [hm, Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  have hmA : A.valuation (m : Ω) < 1 := by
    have h1 := (h ((m : ℕ) : 𝓞 E)).mpr (Ideal.absNorm_mem w.asIdeal)
    simpa using h1
  have hbv : A.valuation (b : Ω) ≠ 0 := by simpa using hb0
  have hrv : A.valuation r ≠ 0 := by simpa using hr
  have hb'v : A.valuation (b' : Ω) ≤ A.valuation r := by
    have h1 := hint _ hb'r
    rw [zsmul_eq_mul, Valuation.map_mul, map_inv₀] at h1
    have := mul_le_mul_left h1 (A.valuation r)
    rwa [mul_assoc, inv_mul_cancel₀ hrv, mul_one, one_mul] at this
  set c : ℕ := b'.natAbs * b.natAbs * m with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact mul_ne_zero (mul_ne_zero (Int.natAbs_ne_zero.mpr hb'0) (Int.natAbs_ne_zero.mpr hb0)) hm0
  have hnat : ∀ n : ℤ, A.valuation ((n.natAbs : ℕ) : Ω) = A.valuation (n : Ω) := by
    intro n
    rcases Int.natAbs_eq n with e | e
    · conv_rhs => rw [e]
      simp
    · conv_rhs => rw [e]
      simp

  have hcv : A.valuation (c : Ω) < A.valuation r * A.valuation (b : Ω) := by
    rw [hc, Nat.cast_mul, Nat.cast_mul, Valuation.map_mul, Valuation.map_mul, hnat, hnat]
    have h1 : A.valuation (b' : Ω) * A.valuation (b : Ω) ≤ A.valuation r * A.valuation (b : Ω) :=
      mul_le_mul_left hb'v _
    have hpos : 0 < A.valuation (b' : Ω) * A.valuation (b : Ω) := by
      rw [zero_lt_iff, ← Valuation.map_mul]; simpa using ⟨hb'0, hb0⟩
    calc A.valuation (b' : Ω) * A.valuation (b : Ω) * A.valuation (m : Ω)
        < A.valuation (b' : Ω) * A.valuation (b : Ω) * 1 := mul_lt_mul_of_pos_left hmA hpos
      _ ≤ A.valuation r * A.valuation (b : Ω) := by rw [mul_one]; exact h1
  have hbz' : IsIntegral ℤ ((b : Ω) * z) := by rwa [zsmul_eq_mul] at hbz
  have key : ∀ x u : Ω, A.valuation x ≤ A.valuation (c : Ω) → IsIntegral ℤ ((b : Ω) * u) →
      A.valuation (x * u) < A.valuation r := by
    intro x u hx hu
    refine lt_of_mul_lt_mul_right' (a := A.valuation (b : Ω)) ?_
    calc A.valuation (x * u) * A.valuation (b : Ω) = A.valuation x * A.valuation ((b : Ω) * u) := by
          rw [Valuation.map_mul, Valuation.map_mul, mul_assoc, mul_comm (A.valuation u)]
      _ ≤ A.valuation (c : Ω) * 1 := mul_le_mul' hx (hint _ hu)
      _ < A.valuation r * A.valuation (b : Ω) := by rw [mul_one]; exact hcv
  set K := IntermediateField.adjoin E ({z} : Set Ω) with hK
  haveI : FiniteDimensional E K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
  have hzK : z ∈ K := IntermediateField.mem_adjoin_simple_self E z
  have hfix : ∀ σ : G E Ω, σ z = z → ∀ x ∈ K, σ x = x := by
    intro σ hσ x hx
    have e1 : ((σ : Ω →ₐ[E] Ω).comp K.val) = K.val :=
      IntermediateField.adjoin_algHom_ext E (fun y hy => by
        rw [Set.mem_singleton_iff] at hy; subst hy; simpa using hσ)
    simpa using congrArg (fun φ : K →ₐ[E] Ω => φ ⟨x, hx⟩) e1
  have hsame : ∀ σ : G E Ω, (∀ x ∈ K, IsIntegral ℤ x → (A.valuation (σ x) < 1 ↔ A.valuation x < 1)) →
      σ z = z := by
    intro σ hall
    obtain ⟨ρ, hρK, hρ⟩ := GlobalTheory.T.exists_conj_valuationSubring_of_same_below E Ω K A (σ⁻¹ • A) (fun x hx hxi => by
      rw [smul_valuation_lt_one_iff, inv_inv]; exact (hall x hx hxi).symm)
    have hD : σ * ρ ∈ Dec (F := E) A := by
      rw [mem_Dec, mul_smul, hρ, smul_inv_smul]
    have := hz _ hD
    rw [AlgEquiv.mul_apply, hρK z hzK] at this
    exact this
  obtain ⟨t, htK, htint, ht1, htσ⟩ := GlobalTheory.T.exists_integral_near_one_small_off_decomposition E Ω K A c hc0
  obtain ⟨e, s, hs, he⟩ := GlobalTheory.T.exists_algebraMap_sub_eq_sum_conjugates' E Ω (t * z)
  refine ⟨e, ?_⟩
  have hyz : A.valuation (t * z - z) < A.valuation r := by
    have : t * z - z = (t - 1) * z := by ring
    rw [this]; exact key _ _ ht1 hbz'
  have hsum : ∀ x ∈ s, A.valuation x < A.valuation r := by
    intro x hx
    obtain ⟨hxy, σ, rfl⟩ := hs x hx
    have hσz : σ z ≠ z := by
      intro hσz
      apply hxy
      rw [map_mul, hfix σ hσz t htK, hσz]
    have hex : ∃ x ∈ K, IsIntegral ℤ x ∧ ¬(A.valuation (σ x) < 1 ↔ A.valuation x < 1) := by
      by_contra hne
      exact hσz (hsame σ (fun x hx hxi => by
        by_contra hn
        exact hne ⟨x, hx, hxi, hn⟩))
    rw [map_mul]
    refine key _ _ (htσ σ hex) ?_
    have : (b : Ω) * σ z = σ ((b : Ω) * z) := by simp
    rw [this]
    exact hbz'.map ((σ : Ω ≃ₐ[E] Ω).toAlgHom.restrictScalars ℤ)
  have e2 : algebraMap E Ω e - z = (∑ x ∈ s, x) + (t * z - z) := by rw [← he]; ring
  rw [e2]
  exact Valuation.map_add_lt _ (Valuation.map_sum_lt _ hrv hsum) hyz
end GlobalTheory
