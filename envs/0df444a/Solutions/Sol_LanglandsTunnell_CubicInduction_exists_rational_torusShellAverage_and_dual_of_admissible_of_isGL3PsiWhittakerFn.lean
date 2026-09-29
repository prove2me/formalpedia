-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_rational_torusShellAverage_and_dual_of_admissible_of_isGL3PsiWhittakerFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/4c904453-d44f-5a8f-a092-252de536e697

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_torusShellAverage_and_dual_eq_zero_of_lt_of_isGL3PsiWhittakerFn
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_forall_torusShellAverage_eq_apply
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_polynomial_sum_coeff_smul_rightTranslate_pow_mem_span_radical_of_admissible
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_torus_eq_zero_of_mem_span_radical_of_isGL3PsiWhittakerFn
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Theorems.Thm_LanglandsTunnell_CubicInduction_admissible_gl3CyclicSubspace_dualWhittakerFn3_rightTranslate
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_rational_torusShellAverage_and_dual_of_admissible_of_isGL3PsiWhittakerFn
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

namespace Ws46
namespace TA

open Finset Polynomial

theorem sum_reverse_coeff_mul_eq_zero (A : ℤ → ℂ) (C : Polynomial ℂ) (N₀ : ℤ)
    (hrec : ∀ n₁ : ℤ, N₀ ≤ n₁ → ∑ i ∈ range (C.natDegree + 1), C.coeff i * A (n₁ + i) = 0)
    (x : ℤ) (hx : N₀ ≤ x - C.natDegree) :
    ∑ j ∈ range (C.reverse.natDegree + 1), C.reverse.coeff j * A (x - j) = 0 := by
  set d := C.natDegree with hd

  have hsub : range (C.reverse.natDegree + 1) ⊆ range (d + 1) := by
    apply range_subset_range.mpr
    have := reverse_natDegree_le C
    omega
  rw [sum_subset hsub (fun j _ hj => by
    have hj' : C.reverse.natDegree < j := by
      simp only [mem_range, not_lt] at hj; omega
    rw [coeff_eq_zero_of_natDegree_lt hj', zero_mul])]

  have hterm : ∀ j ∈ range (d + 1), C.reverse.coeff j * A (x - j) = C.coeff (d - j) * A (x - j) := by
    intro j hj
    rw [coeff_reverse, revAt_le (by simp only [mem_range] at hj; omega)]
  rw [sum_congr rfl hterm]

  have hrefl := sum_range_reflect (fun i => C.coeff i * A (x - d + i)) (d + 1)
  have hterm2 : ∀ j ∈ range (d + 1), C.coeff (d + 1 - 1 - j) * A (x - d + ((d + 1 - 1 - j : ℕ) : ℤ)) =
      C.coeff (d - j) * A (x - j) := by
    intro j hj
    simp only [mem_range] at hj
    have hjd : j ≤ d := by omega
    rw [show d + 1 - 1 - j = d - j by omega]
    congr 1
    rw [Nat.cast_sub hjd]; ring_nf
  rw [← sum_congr rfl hterm2, hrefl]
  exact hrec (x - d) hx

theorem rational_of_recurrences (A : ℤ × ℤ → ℂ) (N₁ : ℤ)
    (hsupp : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0)
    (C₁ : Polynomial ℂ) (hC₁ : C₁ ≠ 0) (N₀ : ℤ)
    (hrec₁ : ∀ n₁ n₂ : ℤ, N₀ ≤ n₁ → ∑ i ∈ range (C₁.natDegree + 1), C₁.coeff i * A (n₁ + i, n₂) = 0)
    (C₂ : Polynomial ℂ) (hC₂ : C₂ ≠ 0) (N₀' : ℤ)
    (hrec₂ : ∀ n₁ n₂ : ℤ, N₀' ≤ n₂ → ∑ i ∈ range (C₂.natDegree + 1), C₂.coeff i * A (n₁, n₂ + i) = 0) :
    ∃ (N : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
      (∀ n : ℤ × ℤ, (n.1 < N ∨ n.2 < N) → A n = 0) ∧
      (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
        ∑ i ∈ range (D₁.natDegree + 1), ∑ l ∈ range (D₂.natDegree + 1),
          D₁.coeff i * D₂.coeff l * A (N + (m₁ : ℤ) - (i : ℤ), N + (m₂ : ℤ) - (l : ℤ)) = 0) := by
  refine ⟨N₁, C₁.reverse, C₂.reverse, C₁.natDegree + C₂.natDegree + (N₀ - N₁).toNat + (N₀' - N₁).toNat,
    ?_, ?_, hsupp, ?_⟩
  · rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse]; exact leadingCoeff_ne_zero.mpr hC₁
  · rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse]; exact leadingCoeff_ne_zero.mpr hC₂
  intro m₁ m₂ hm
  rcases hm with h1 | h2
  ·
    have hinner : ∀ l : ℕ, ∑ i ∈ range (C₁.reverse.natDegree + 1),
        C₁.reverse.coeff i * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0 := by
      intro l
      have := sum_reverse_coeff_mul_eq_zero (fun z => A (z, N₁ + (m₂ : ℤ) - (l : ℤ))) C₁ N₀
        (fun n₁ hn₁ => hrec₁ n₁ _ hn₁) (N₁ + m₁) (by
          have : ((N₀ - N₁).toNat : ℤ) ≥ N₀ - N₁ := Int.self_le_toNat _
          push_cast at h1 ⊢; omega)
      simpa using this
    calc ∑ i ∈ range (C₁.reverse.natDegree + 1), ∑ l ∈ range (C₂.reverse.natDegree + 1),
          C₁.reverse.coeff i * C₂.reverse.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ))
        = ∑ l ∈ range (C₂.reverse.natDegree + 1), C₂.reverse.coeff l *
            ∑ i ∈ range (C₁.reverse.natDegree + 1),
              C₁.reverse.coeff i * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) := by
          rw [sum_comm]; refine sum_congr rfl fun l _ => ?_; rw [mul_sum]; refine sum_congr rfl fun i _ => ?_; ring
      _ = 0 := by simp [hinner]
  · have hinner : ∀ i : ℕ, ∑ l ∈ range (C₂.reverse.natDegree + 1),
        C₂.reverse.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0 := by
      intro i
      have := sum_reverse_coeff_mul_eq_zero (fun z => A (N₁ + (m₁ : ℤ) - (i : ℤ), z)) C₂ N₀'
        (fun n₂ hn₂ => hrec₂ _ n₂ hn₂) (N₁ + m₂) (by
          have : ((N₀' - N₁).toNat : ℤ) ≥ N₀' - N₁ := Int.self_le_toNat _
          push_cast at h2 ⊢; omega)
      simpa using this
    calc ∑ i ∈ range (C₁.reverse.natDegree + 1), ∑ l ∈ range (C₂.reverse.natDegree + 1),
          C₁.reverse.coeff i * C₂.reverse.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ))
        = ∑ i ∈ range (C₁.reverse.natDegree + 1), C₁.reverse.coeff i *
            ∑ l ∈ range (C₂.reverse.natDegree + 1),
              C₂.reverse.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) := by
          refine sum_congr rfl fun i _ => ?_; rw [mul_sum]; refine sum_congr rfl fun l _ => ?_; ring
      _ = 0 := by simp [hinner]

section Shift
variable {K : Type*} [Field K]

theorem diagUnitGL2_zpow_mul_pow (u : Kˣ) (n : ℤ) (i : ℕ) :
    diagUnitGL2 (u ^ n) * diagUnitGL2 u ^ i = diagUnitGL2 (u ^ (n + (i : ℤ))) := by
  rw [← diagHom_apply, ← diagHom_apply, ← diagHom_apply, ← map_pow, ← map_mul, ← zpow_natCast, ← zpow_add]

theorem scalarPi_commute_diagUnitGL2 (π : K) (hπ : π ≠ 0) (w : Kˣ) :
    Commute (UnramifiedWhittaker.scalarPi π hπ) (diagUnitGL2 w) := by
  unfold Commute SemiconjBy
  apply Units.ext
  simp only [Units.val_mul, coe_diagUnitGL2, UnramifiedWhittaker.scalarPi, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem torus_mul_T₁ (π : K) (hπ : π ≠ 0) (n₁ n₂ : ℤ) (i : ℕ) :
    iotaGL (UnramifiedWhittaker.scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁)) *
        iotaGL (diagUnitGL2 (Units.mk0 π hπ)) ^ i =
      iotaGL (UnramifiedWhittaker.scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ (n₁ + (i : ℤ)))) := by
  rw [← map_pow, ← map_mul, mul_assoc, diagUnitGL2_zpow_mul_pow]

theorem torus_mul_T₂ (π : K) (hπ : π ≠ 0) (n₁ n₂ : ℤ) (i : ℕ) :
    iotaGL (UnramifiedWhittaker.scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁)) *
        iotaGL (UnramifiedWhittaker.scalarPi π hπ) ^ i =
      iotaGL (UnramifiedWhittaker.scalarPi π hπ ^ (n₂ + (i : ℤ)) * diagUnitGL2 (Units.mk0 π hπ ^ n₁)) := by
  rw [← map_pow, ← map_mul, mul_assoc, ((scalarPi_commute_diagUnitGL2 π hπ _).symm.pow_right i).eq,
    ← mul_assoc, ← zpow_natCast, ← zpow_add]

end Shift

end Ws46.TA

open Ws46.TA LanglandsTunnell LanglandsTunnell.CubicInduction in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (hψ : ψv ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (b : ℕ) :
    ∀ (g₃ : LocalGL3 v) (k₀ : GL (Fin 2) (v.adicCompletion ℚ)) (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ),
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v η c → c ≤ b →
      letI := localBorel ℚ v
      letI := localGLBorel ℚ v
      haveI := borelSpace_localGLBorel ℚ v
      ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        let A : ℤ × ℤ → ℂ := fun n =>
          ∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
            (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) :
                  Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                W (iotaGL (UnramifiedWhittaker.scalarPi
                      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
                      ^ n.1 * u) * (k₀ * k)) * g₃) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        let Ad : ℤ × ℤ → ℂ := fun n =>
          ∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
            (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) :
                  Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                dualWhittakerFn3 (fun x => W (x * g₃)) (iotaGL (UnramifiedWhittaker.scalarPi
                      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
                      ^ n.1 * u) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        (∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
          (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0) ∧
          (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
            ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
              D₁.coeff i * D₂.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0)) ∧
        (∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
          (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → Ad n = 0) ∧
          (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
            ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
              D₁.coeff i * D₂.coeff l * Ad (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0)) := by
  intro g₃ k₀ η c hηc hcb μ₂ _
  intro A Ad

  obtain ⟨N₁, hsupp⟩ := LanglandsTunnell.CubicInduction.exists_forall_torusShellAverage_and_dual_eq_zero_of_lt_of_isGL3PsiWhittakerFn
    v ψv hψ W hW hsm hπ hϖ b g₃ k₀ η c hηc hcb μ₂
  obtain ⟨⟨Φ, hΦV, -, hAΦ⟩, ⟨Φd, hΦdV, -, hAdΦ⟩⟩ :=
    LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_forall_torusShellAverage_eq_apply
      v W hsm hπ hϖ b g₃ k₀ η c hηc hcb μ₂
  obtain ⟨hdsm, hdadm, hdW⟩ := LanglandsTunnell.CubicInduction.admissible_gl3CyclicSubspace_dualWhittakerFn3_rightTranslate v W hsm hadm g₃

  by_cases hW0 : ∀ g : LocalGL3 v, W g = 0
  · have hbot : ∀ (W' : LocalGL3 v → ℂ), (∀ g, W' g = 0) → ∀ Ψ ∈ gl3CyclicSubspace W', Ψ = 0 := by
      intro W' hW' Ψ hΨ
      have hW'0 : W' = 0 := funext hW'
      have : gl3CyclicSubspace W' = ⊥ := by
        unfold gl3CyclicSubspace
        rw [Submodule.span_eq_bot]
        rintro _ ⟨h, rfl⟩
        simp only [hW'0, map_zero]
      rw [this] at hΨ
      exact (Submodule.mem_bot ℂ).mp hΨ
    have hΦ0 : Φ = 0 := hbot W hW0 Φ hΦV
    have hΦd0 : Φd = 0 := hbot _ (fun y => by simp only [dualWhittakerFn3, hW0]) Φd hΦdV
    have hA0 : ∀ n, A n = 0 := fun n => (hAΦ n).trans (by rw [hΦ0]; rfl)
    have hAd0 : ∀ n, Ad n = 0 := fun n => (hAdΦ n).trans (by rw [hΦd0]; rfl)
    refine ⟨?_, ?_⟩
    · exact rational_of_recurrences A 0 (fun n _ => hA0 n) 1 one_ne_zero 0 (fun n₁ n₂ _ => by simp [hA0])
        1 one_ne_zero 0 (fun n₁ n₂ _ => by simp [hA0])
    · exact rational_of_recurrences Ad 0 (fun n _ => hAd0 n) 1 one_ne_zero 0 (fun n₁ n₂ _ => by simp [hAd0])
        1 one_ne_zero 0 (fun n₁ n₂ _ => by simp [hAd0])

  push_neg at hW0
  obtain ⟨g, hg⟩ := hW0
  have hψball : ∃ m : ℤ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp m → ψv x = 1 := by
    obtain ⟨Uv, hUo, hUinv⟩ := hsm
    have hW' : ∀ (x y z : v.adicCompletion ℚ) (h : LocalGL3 v), W (upperUnipotent3 x y z * h) = ψv (x + y) * W h := hW

    have hcu : Continuous fun x : v.adicCompletion ℚ => (upperUnipotent3 x 0 0 : LocalGL3 v) := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · show Continuous fun x : v.adicCompletion ℚ => ((upperUnipotent3 x 0 0 : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
        simp only [upperUnipotent3_coe]
        refine continuous_matrix fun i j => ?_
        fin_cases i <;> fin_cases j <;> simp <;> fun_prop
      · show Continuous fun x : v.adicCompletion ℚ => (((upperUnipotent3 x 0 0 : LocalGL3 v))⁻¹ : LocalGL3 v).val
        have : ∀ x : v.adicCompletion ℚ, (((upperUnipotent3 x 0 0 : LocalGL3 v))⁻¹ : LocalGL3 v).val =
            !![1, -x, x * 0 - 0; 0, 1, -0; 0, 0, 1] := fun x => rfl
        simp only [this]
        refine continuous_matrix fun i j => ?_
        fin_cases i <;> fin_cases j <;> simp <;> fun_prop
    have hc : Continuous fun x : v.adicCompletion ℚ => g⁻¹ * (upperUnipotent3 x 0 0 : LocalGL3 v) * g :=
      (continuous_const.mul hcu).mul continuous_const
    have h0 : g⁻¹ * (upperUnipotent3 (0 : v.adicCompletion ℚ) 0 0 : LocalGL3 v) * g = 1 := by
      rw [upperUnipotent3_zero, mul_one, inv_mul_cancel]
    have hmem : {x : v.adicCompletion ℚ | g⁻¹ * (upperUnipotent3 x 0 0 : LocalGL3 v) * g ∈ (Uv : Set (LocalGL3 v))} ∈
        nhds (0 : v.adicCompletion ℚ) :=
      hc.continuousAt.preimage_mem_nhds (by rw [h0]; exact hUo.mem_nhds Uv.one_mem)
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hmem
    have hγ0 : (MonoidWithZeroHom.ValueGroup₀.embedding γ.1 : WithZero (Multiplicative ℤ)) ≠ 0 :=
      (map_ne_zero MonoidWithZeroHom.ValueGroup₀.embedding).mpr γ.ne_zero
    refine ⟨WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) - 1, fun x hx => ?_⟩
    have hxγ : Valued.v.restrict x < γ.1 := by
      rw [Valuation.restrict_lt_iff_lt_embedding]
      refine lt_of_le_of_lt hx ?_
      conv_rhs => rw [← WithZero.exp_log hγ0]
      exact WithZero.exp_lt_exp.mpr (by omega)
    have hk : g⁻¹ * (upperUnipotent3 x 0 0 : LocalGL3 v) * g ∈ Uv := hγ hxγ
    have h1 := hUinv _ hk g
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, hW' x 0 0 g, add_zero] at h1
    exact (mul_eq_right₀ hg).mp h1
  have hψball' : ∃ m : ℤ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp m → ψv⁻¹ x = 1 := by
    obtain ⟨m, hm⟩ := hψball
    exact ⟨m, fun x hx => by rw [AddChar.inv_apply, hm (-x) (by rwa [Valuation.map_neg])]⟩
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨⟨C₁, hC₁, hF₁⟩, ⟨C₂, hC₂, hF₂⟩⟩ :=
      LanglandsTunnell.CubicInduction.exists_polynomial_sum_coeff_smul_rightTranslate_pow_mem_span_radical_of_admissible
        v W hsm hadm hπ hϖ Φ hΦV
    obtain ⟨hV12, hV21⟩ :=
      LanglandsTunnell.CubicInduction.exists_forall_apply_iotaGL_torus_eq_zero_of_mem_span_radical_of_isGL3PsiWhittakerFn
        v ψv hψball W hW hπ hϖ
    obtain ⟨N₀, hN₀⟩ := hV12 _ hF₁
    obtain ⟨N₀', hN₀'⟩ := hV21 _ hF₂
    have hrec₁ : ∀ n₁ n₂ : ℤ, N₀ ≤ n₁ →
        ∑ i ∈ Finset.range (C₁.natDegree + 1), C₁.coeff i * A (n₁ + i, n₂) = 0 := by
      intro n₁ n₂ hn₁
      have h := hN₀ n₁ n₂ hn₁
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [torus_mul_T₁]
      congr 1
      exact hAΦ (n₁ + i, n₂)
    have hrec₂ : ∀ n₁ n₂ : ℤ, N₀' ≤ n₂ →
        ∑ i ∈ Finset.range (C₂.natDegree + 1), C₂.coeff i * A (n₁, n₂ + i) = 0 := by
      intro n₁ n₂ hn₂
      have h := hN₀' n₁ n₂ hn₂
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [torus_mul_T₂]
      congr 1
      exact hAΦ (n₁, n₂ + i)
    exact rational_of_recurrences A N₁ (fun n hn => (hsupp n hn).1) C₁ hC₁ N₀ hrec₁ C₂ hC₂ N₀' hrec₂
  ·
    obtain ⟨⟨C₁, hC₁, hF₁⟩, ⟨C₂, hC₂, hF₂⟩⟩ :=
      LanglandsTunnell.CubicInduction.exists_polynomial_sum_coeff_smul_rightTranslate_pow_mem_span_radical_of_admissible
        v (dualWhittakerFn3 (fun x => W (x * g₃))) hdsm hdadm hπ hϖ Φd hΦdV
    obtain ⟨hV12, hV21⟩ :=
      LanglandsTunnell.CubicInduction.exists_forall_apply_iotaGL_torus_eq_zero_of_mem_span_radical_of_isGL3PsiWhittakerFn
        v ψv⁻¹ hψball' (dualWhittakerFn3 (fun x => W (x * g₃))) (hdW ψv hW) hπ hϖ
    obtain ⟨N₀, hN₀⟩ := hV12 _ hF₁
    obtain ⟨N₀', hN₀'⟩ := hV21 _ hF₂
    have hrec₁ : ∀ n₁ n₂ : ℤ, N₀ ≤ n₁ →
        ∑ i ∈ Finset.range (C₁.natDegree + 1), C₁.coeff i * Ad (n₁ + i, n₂) = 0 := by
      intro n₁ n₂ hn₁
      have h := hN₀ n₁ n₂ hn₁
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [torus_mul_T₁]
      congr 1
      exact hAdΦ (n₁ + i, n₂)
    have hrec₂ : ∀ n₁ n₂ : ℤ, N₀' ≤ n₂ →
        ∑ i ∈ Finset.range (C₂.natDegree + 1), C₂.coeff i * Ad (n₁, n₂ + i) = 0 := by
      intro n₁ n₂ hn₂
      have h := hN₀' n₁ n₂ hn₂
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [torus_mul_T₂]
      congr 1
      exact hAdΦ (n₁, n₂ + i)
    exact rational_of_recurrences Ad N₁ (fun n hn => (hsupp n hn).2) C₁ hC₁ N₀ hrec₁ C₂ hC₂ N₀' hrec₂

end S_LanglandsTunnell_CubicInduction_exists_rational_torusShellAverage_and_dual_of_admissible_of_isGL3PsiWhittakerFn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_rational_torusShellAverage_and_dual_of_admissible_of_isGL3PsiWhittakerFn (solution)
