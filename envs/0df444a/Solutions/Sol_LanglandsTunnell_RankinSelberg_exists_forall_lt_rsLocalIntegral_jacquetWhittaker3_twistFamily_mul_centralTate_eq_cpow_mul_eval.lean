-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_lt_rsLocalIntegral_jacquetWhittaker3_twistFamily_mul_centralTate_eq_cpow_mul_eval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/465d34d9-8c0a-519e-a24e-fb0b7b0713d8

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Theorems.Thm_LanglandsTunnell_forall_cpow_mul_eval_eq_of_forall_lt_re
import Theorems.Thm_LanglandsTunnell_clearedFE_of_clearedFE_of_forall_eval_mul_eval_mul_cpow_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_unitary_mul_modulus_cpow_of_hasConductorExponentAt
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_jacquetWhittaker3_mul_centralTate_eq_cpow_mul_eval_and_dual_of_chamber
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_lt_rsLocalIntegral_jacquetWhittaker3_twistFamily_mul_centralTate_eq_cpow_mul_eval
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical Topology

namespace M2PGlue

theorem exists_real_forall_norm_apply_eq_norm_rpow (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ∃ c : ℝ, ∀ a : (p.adicCompletion ℚ)ˣ, ‖((χ a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ c := by
  obtain ⟨n, hn⟩ :=
    LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous ℚ p χ hχ.continuous
  obtain ⟨η, σ, hη, -, hχη⟩ :=
    LanglandsTunnell.TateLocal.exists_unitary_mul_modulus_cpow_of_hasConductorExponentAt ℚ p χ n hn
  refine ⟨σ, fun a => ?_⟩
  have hmod : ((modulus (a : p.adicCompletion ℚ) : ℝ)) = ‖(a : p.adicCompletion ℚ)‖ := by
    rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm]; rfl
  have hpos : 0 < ‖(a : p.adicCompletion ℚ)‖ := norm_pos_iff.mpr a.ne_zero
  rw [hχη a, norm_mul, hη a, one_mul, hmod, Complex.norm_cpow_eq_rpow_re_of_pos hpos,
    Complex.ofReal_re]

noncomputable def normPow (p : HeightOneSpectrum (𝓞 ℚ)) (u : ℂ) : (p.adicCompletion ℚ)ˣ →* ℂˣ where
  toFun a := Units.mk0 (((‖(a : p.adicCompletion ℚ)‖ : ℂ)) ^ u) (by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (by exact_mod_cast (norm_ne_zero_iff.mpr a.ne_zero)))
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    simp only [Units.val_mul, norm_mul, Complex.ofReal_mul, Units.val_mk0]
    exact Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _) u

@[scoped simp] theorem normPow_apply (p : HeightOneSpectrum (𝓞 ℚ)) (u : ℂ) (a : (p.adicCompletion ℚ)ˣ) :
    ((normPow p u a : ℂˣ) : ℂ) = ((‖(a : p.adicCompletion ℚ)‖ : ℂ)) ^ u := rfl

theorem normPow_zero (p : HeightOneSpectrum (𝓞 ℚ)) : normPow p 0 = 1 := by
  ext a; simp

private theorem _root_.M2PGlue.eventually_norm_eq (p : HeightOneSpectrum (𝓞 ℚ)) (x : (p.adicCompletion ℚ)ˣ) :
    ∀ᶠ y : (p.adicCompletion ℚ)ˣ in 𝓝 x, ‖(y : p.adicCompletion ℚ)‖ = ‖(x : p.adicCompletion ℚ)‖ := by
  have h0 : (Valued.v (x : p.adicCompletion ℚ)) ≠ 0 := by simp
  have h1 : ∀ᶠ z in 𝓝 (x : p.adicCompletion ℚ), ‖z‖ = ‖(x : p.adicCompletion ℚ)‖ :=
    Filter.mem_of_superset (Valued.locally_const h0) (fun z hz => by
      simp only [Set.mem_setOf_eq] at hz
      show ‖z‖ = ‖(x : p.adicCompletion ℚ)‖
      rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, hz])
  exact (Units.continuous_val.tendsto x).eventually h1

p2m_export "M2PGlue" "eventually_norm_eq"
theorem isLocallyConstant_normPow (p : HeightOneSpectrum (𝓞 ℚ)) (u : ℂ) :
    IsLocallyConstant (normPow p u) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  exact (eventually_norm_eq p x).mono (fun y hy => Units.ext (by simp [hy]))

theorem exists_twistFamily (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i)) :
    ∃ lamU : ℂ → Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ),
      lamU 0 = lam ∧
      (∀ (u : ℂ) (a : (p.adicCompletion ℚ)ˣ),
        ((lamU u 0 a : ℂˣ) : ℂ) = ((lam 0 a : ℂˣ) : ℂ) * ((‖(a : p.adicCompletion ℚ)‖ : ℂ)) ^ u ∧
          ((lamU u 1 a : ℂˣ) : ℂ) = ((lam 1 a : ℂˣ) : ℂ) ∧
            ((lamU u 2 a : ℂˣ) : ℂ) = ((lam 2 a : ℂˣ) : ℂ) * ((‖(a : p.adicCompletion ℚ)‖ : ℂ)) ^ (-u)) ∧
      (∀ (u : ℂ) (i : Fin 3), IsLocallyConstant (lamU u i)) := by
  refine ⟨fun u => ![lam 0 * normPow p u, lam 1, lam 2 * normPow p (-u)], ?_, ?_, ?_⟩
  · funext i
    fin_cases i <;> ext a <;> simp
  · intro u a
    simp
  · intro u i
    have hmul : ∀ (f g : (p.adicCompletion ℚ)ˣ →* ℂˣ), IsLocallyConstant f → IsLocallyConstant g →
        IsLocallyConstant (f * g) := fun f g hf hg => by
      have : ⇑(f * g) = ⇑f * ⇑g := rfl
      rw [this]; exact hf.mul hg
    fin_cases i
    · simpa using hmul _ _ (hlam 0) (isLocallyConstant_normPow p u)
    · simpa using hlam 1
    · simpa using hmul _ _ (hlam 2) (isLocallyConstant_normPow p (-u))

theorem exists_forall_chamber_of_twistFamily (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (lamU : ℂ → Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hlamU : ∀ (u : ℂ) (a : (p.adicCompletion ℚ)ˣ),
      ((lamU u 0 a : ℂˣ) : ℂ) = ((lam 0 a : ℂˣ) : ℂ) * ((‖(a : p.adicCompletion ℚ)‖ : ℂ)) ^ u ∧
        ((lamU u 1 a : ℂˣ) : ℂ) = ((lam 1 a : ℂˣ) : ℂ) ∧
          ((lamU u 2 a : ℂˣ) : ℂ) = ((lam 2 a : ℂˣ) : ℂ) * ((‖(a : p.adicCompletion ℚ)‖ : ℂ)) ^ (-u)) :
    ∃ u₀ : ℝ, ∀ u : ℂ, u₀ < u.re →
      ∃ σ : Fin 3 → ℝ,
        (∀ (i : Fin 3) (a : (p.adicCompletion ℚ)ˣ),
          ‖((lamU u i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i)) ∧
        σ 1 < σ 0 ∧ σ 2 < σ 1 := by
  choose c hc using fun i => exists_real_forall_norm_apply_eq_norm_rpow p (lam i) (hlam i)
  refine ⟨max (c 1 - c 0) (c 2 - c 1), fun u hu => ⟨![c 0 + u.re, c 1, c 2 - u.re], ?_, ?_, ?_⟩⟩
  · intro i a
    have hpos : 0 < ‖(a : p.adicCompletion ℚ)‖ := norm_pos_iff.mpr a.ne_zero
    obtain ⟨h0, h1, h2⟩ := hlamU u a
    fin_cases i
    · show ‖((lamU u 0 a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (c 0 + u.re)
      rw [h0, norm_mul, hc 0 a, Complex.norm_cpow_eq_rpow_re_of_pos hpos, ← Real.rpow_add hpos]
    · show ‖((lamU u 1 a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (c 1)
      rw [h1, hc 1 a]
    · show ‖((lamU u 2 a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (c 2 - u.re)
      rw [h2, norm_mul, hc 2 a, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.neg_re,
        ← Real.rpow_add hpos, sub_eq_add_neg]
  · have := (le_max_left (c 1 - c 0) (c 2 - c 1)).trans_lt hu
    show c 1 < c 0 + u.re
    linarith
  · have := (le_max_right (c 1 - c 0) (c 2 - c 1)).trans_lt hu
    show c 2 - u.re < c 1
    linarith

theorem shift_eval (N : ℂ) (hN : N ≠ 0) (Q : Polynomial ℂ) (k : ℤ) (s u : ℂ) :
    N ^ ((k : ℂ) * s) * (Polynomial.C (N ^ ((k : ℂ) * u)) * Q.comp (Polynomial.C (N ^ (-u)) * Polynomial.X)).eval
        (N ^ (-s)) = N ^ ((k : ℂ) * (s + u)) * Q.eval (N ^ (-(s + u))) := by
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_X]
  rw [mul_add, Complex.cpow_add _ _ hN, show -(s + u) = -u + -s by ring, Complex.cpow_add _ _ hN]
  ring

theorem hfe_shift (p : HeightOneSpectrum (𝓞 ℚ))
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (wJ : GL (Fin 2) (p.adicCompletion ℚ))
    (χ χ' : (p.adicCompletion ℚ)ˣ →* ℂˣ) (u : ℂ)
    (hχ' : ∀ y : (p.adicCompletion ℚ)ˣ, ((χ' y : ℂˣ) : ℂ) = ((χ y : ℂˣ) : ℂ) * ((‖(y : p.adicCompletion ℚ)‖ : ℂ)) ^ u)
    (E₀ : ℂ) (e₀ : ℤ)
    (h : letI := localBorel ℚ p
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e₀ : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))))) :
    letI := localBorel ℚ p
    ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((χ' y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((χ' y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((χ' y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((χ' y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e₀ : ℂ) * u) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e₀ : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))) := by
  obtain ⟨P, Pd, m, md, σ₀, σ₁, h1, h2, h3, h4, h5⟩ := h
  have hN : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (fun h => p.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  have hmod : ∀ y : (p.adicCompletion ℚ)ˣ, ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) = ((‖(y : p.adicCompletion ℚ)‖ : ℂ)) := by
    intro y
    rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm]; rfl
  have hn : ∀ y : (p.adicCompletion ℚ)ˣ, ((‖(y : p.adicCompletion ℚ)‖ : ℂ)) ≠ 0 := fun y => by
    exact_mod_cast (norm_ne_zero_iff.mpr y.ne_zero)
  have hint1 : ∀ (s : ℂ) (y : (p.adicCompletion ℚ)ˣ),
      w (diagOne y) * ((χ' y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2) =
        w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ ((s + u) - 1 / 2) := by
    intro s y
    rw [hχ', hmod, show s + u - 1 / 2 = u + (s - 1 / 2) by ring, Complex.cpow_add _ _ (hn y)]
    ring
  have hint2 : ∀ (s : ℂ) (y : (p.adicCompletion ℚ)ˣ),
      w (diagOne y * wJ) * (((χ' y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
          ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s) =
        w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
          ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - (s + u)) := by
    intro s y
    rw [hχ', hmod, mul_inv, show 1 / 2 - (s + u) = -u + (1 / 2 - s) by ring, Complex.cpow_add _ _ (hn y),
      Complex.cpow_neg]
    ring
  have hre : ∀ s : ℂ, (s + u).re = s.re + u.re := fun s => by simp
  refine ⟨Polynomial.C ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * u)) *
      P.comp (Polynomial.C ((Ideal.absNorm p.asIdeal : ℂ) ^ (-u)) * Polynomial.X),
    Polynomial.C ((Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * u)) *
      Pd.comp (Polynomial.C ((Ideal.absNorm p.asIdeal : ℂ) ^ (-u)) * Polynomial.X),
    m, md, σ₀ - u.re, σ₁ - u.re, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    simp_rw [hint1 s]
    exact h1 (s + u) (by rw [hre]; linarith)
  · intro s hs
    simp_rw [hint1 s]
    rw [h2 (s + u) (by rw [hre]; linarith), shift_eval _ hN]
  · intro s hs
    simp_rw [hint2 s]
    exact h3 (s + u) (by rw [hre]; linarith)
  · intro s hs
    simp_rw [hint2 s]
    rw [h4 (s + u) (by rw [hre]; linarith), shift_eval _ hN]
  · intro s
    rw [shift_eval _ hN, mul_assoc (E₀ * _), shift_eval _ hN, h5 (s + u), mul_add,
      Complex.cpow_add _ _ hN]
    ring

theorem evev (P : Polynomial (Polynomial ℂ)) (x y : ℂ) :
    (P.eval (Polynomial.C y)).eval x = (P.map (Polynomial.evalRingHom x)).eval y := by
  have h := Polynomial.eval₂_at_apply (p := P) (Polynomial.evalRingHom x) (Polynomial.C y)
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_C] at h
  rw [Polynomial.eval_map, h]

theorem s_continuation (N : ℕ) (hN : 1 < N) (P Q' P' Q : Polynomial ℂ) (m m' : ℤ) (c : ℝ)
    (h : ∀ s : ℂ, c < s.re →
      (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s)) * Q'.eval ((N : ℂ) ^ (-s)) =
        (N : ℂ) ^ ((m' : ℂ) * s) * P'.eval ((N : ℂ) ^ (-s)) * Q.eval ((N : ℂ) ^ (-s))) :
    ∀ s : ℂ, (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s)) * Q'.eval ((N : ℂ) ^ (-s)) =
        (N : ℂ) ^ ((m' : ℂ) * s) * P'.eval ((N : ℂ) ^ (-s)) * Q.eval ((N : ℂ) ^ (-s)) := by
  have key := LanglandsTunnell.forall_cpow_mul_eval_eq_of_forall_lt_re N hN (P * Q') (P' * Q) m m' c
    (fun u hu => by simpa only [Polynomial.eval_mul, mul_assoc] using h u hu)
  intro s
  simpa only [Polynomial.eval_mul, mul_assoc] using key s

theorem u_continuation (N : ℕ) (hN : 1 < N) (K E₀ E₁ E₂ : ℂ) (e₀ e₁ e₂ r : ℤ)
    (P₂ Pd₂ Q₂ Qd₂ : Polynomial (Polynomial ℂ)) (m₂ md₂ j jd : ℤ) (c : ℝ)
    (h : ∀ u : ℂ, c < u.re → ∀ s : ℂ,
        (1 : Polynomial ℂ).eval ((N : ℂ) ^ s) *
          ((N : ℂ) ^ ((md₂ : ℂ) * s) * (Polynomial.C ((N : ℂ) ^ ((jd : ℂ) * u)) * Pd₂.eval (Polynomial.C ((N : ℂ) ^ (-u)))).eval ((N : ℂ) ^ (-s))) *
          (Q₂.eval (Polynomial.C ((N : ℂ) ^ (-u)))).eval ((N : ℂ) ^ s) =
        ((Polynomial.C (K * (E₀ * (N : ℂ) ^ ((e₀ : ℂ) * u) * (E₁ * (N : ℂ) ^ ((e₁ : ℂ) * 0)) * (E₂ * (N : ℂ) ^ ((e₂ : ℂ) * (-u)))))).eval ((N : ℂ) ^ s) *
            (N : ℂ) ^ ((r : ℂ) * s)) *
          ((N : ℂ) ^ ((m₂ : ℂ) * (-s)) * (Polynomial.C ((N : ℂ) ^ ((j : ℂ) * u)) * P₂.eval (Polynomial.C ((N : ℂ) ^ (-u)))).eval ((N : ℂ) ^ s)) *
          (Qd₂.eval (Polynomial.C ((N : ℂ) ^ (-u)))).eval ((N : ℂ) ^ (-s))) :
    ∀ s : ℂ, (1 : Polynomial ℂ).eval ((N : ℂ) ^ s) * ((N : ℂ) ^ ((md₂ : ℂ) * s) * (Pd₂.eval 1).eval ((N : ℂ) ^ (-s))) *
          (Q₂.eval 1).eval ((N : ℂ) ^ s) =
        ((Polynomial.C (K * (E₀ * E₁ * E₂))).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((r : ℂ) * s)) *
          ((N : ℂ) ^ ((m₂ : ℂ) * (-s)) * (P₂.eval 1).eval ((N : ℂ) ^ s)) * (Qd₂.eval 1).eval ((N : ℂ) ^ (-s)) := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  intro s

  have keyL : ∀ u : ℂ,
      (1 : Polynomial ℂ).eval ((N : ℂ) ^ s) *
          ((N : ℂ) ^ ((md₂ : ℂ) * s) * (Polynomial.C ((N : ℂ) ^ ((jd : ℂ) * u)) * Pd₂.eval (Polynomial.C ((N : ℂ) ^ (-u)))).eval ((N : ℂ) ^ (-s))) *
          (Q₂.eval (Polynomial.C ((N : ℂ) ^ (-u)))).eval ((N : ℂ) ^ s) =
        (N : ℂ) ^ ((jd : ℂ) * u) *
          (Polynomial.C ((N : ℂ) ^ ((md₂ : ℂ) * s)) * Pd₂.map (Polynomial.evalRingHom ((N : ℂ) ^ (-s))) *
            Q₂.map (Polynomial.evalRingHom ((N : ℂ) ^ s))).eval ((N : ℂ) ^ (-u)) := by
    intro u
    simp only [Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, evev]
    ring
  have keyR : ∀ u : ℂ,
      ((Polynomial.C (K * (E₀ * (N : ℂ) ^ ((e₀ : ℂ) * u) * (E₁ * (N : ℂ) ^ ((e₁ : ℂ) * 0)) * (E₂ * (N : ℂ) ^ ((e₂ : ℂ) * (-u)))))).eval ((N : ℂ) ^ s) *
            (N : ℂ) ^ ((r : ℂ) * s)) *
          ((N : ℂ) ^ ((m₂ : ℂ) * (-s)) * (Polynomial.C ((N : ℂ) ^ ((j : ℂ) * u)) * P₂.eval (Polynomial.C ((N : ℂ) ^ (-u)))).eval ((N : ℂ) ^ s)) *
          (Qd₂.eval (Polynomial.C ((N : ℂ) ^ (-u)))).eval ((N : ℂ) ^ (-s)) =
        (N : ℂ) ^ (((j + e₀ - e₂ : ℤ) : ℂ) * u) *
          (Polynomial.C (K * (E₀ * E₁ * E₂) * (N : ℂ) ^ ((r : ℂ) * s) * (N : ℂ) ^ ((m₂ : ℂ) * (-s))) *
            P₂.map (Polynomial.evalRingHom ((N : ℂ) ^ s)) * Qd₂.map (Polynomial.evalRingHom ((N : ℂ) ^ (-s)))).eval ((N : ℂ) ^ (-u)) := by
    intro u
    simp only [Polynomial.eval_mul, Polynomial.eval_C, evev, mul_zero, Complex.cpow_zero, mul_one]
    rw [show (((j + e₀ - e₂ : ℤ)) : ℂ) * u = (j : ℂ) * u + ((e₀ : ℂ) * u + (e₂ : ℂ) * (-u)) by push_cast; ring,
      Complex.cpow_add _ _ hNc, Complex.cpow_add _ _ hNc]
    ring
  have key := LanglandsTunnell.forall_cpow_mul_eval_eq_of_forall_lt_re N hN _ _ jd (j + e₀ - e₂) c
    (fun u hu => by rw [← keyL u, ← keyR u]; exact h u hu s) 0
  rw [← keyL 0, ← keyR 0] at key
  simpa only [neg_zero, mul_zero, Complex.cpow_zero, Polynomial.C_1, one_mul, mul_one] using key

open Polynomial in

theorem transfer (N : ℕ) (hN : 1 < N) (K : ℂ) (r : ℤ)
    (P Pd Q Qd : Polynomial ℂ) (m md : ℤ)
    (P₀ Pd₀ Q₀ Qd₀ : Polynomial ℂ) (m₀ md₀ : ℤ)
    (hQ₀ : Q₀ ≠ 0) (hQd₀ : Qd₀ ≠ 0)
    (ha : ∀ s : ℂ, (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s)) * Q₀.eval ((N : ℂ) ^ (-s)) =
      (N : ℂ) ^ ((m₀ : ℂ) * s) * P₀.eval ((N : ℂ) ^ (-s)) * Q.eval ((N : ℂ) ^ (-s)))
    (hb : ∀ s : ℂ, (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s)) * Qd₀.eval ((N : ℂ) ^ (-s)) =
      (N : ℂ) ^ ((md₀ : ℂ) * s) * Pd₀.eval ((N : ℂ) ^ (-s)) * Qd.eval ((N : ℂ) ^ (-s)))
    (hc : ∀ s : ℂ, (1 : Polynomial ℂ).eval ((N : ℂ) ^ s) * ((N : ℂ) ^ ((md₀ : ℂ) * s) * Pd₀.eval ((N : ℂ) ^ (-s))) * Q₀.eval ((N : ℂ) ^ s) =
      ((Polynomial.C K).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((r : ℂ) * s)) * ((N : ℂ) ^ ((m₀ : ℂ) * (-s)) * P₀.eval ((N : ℂ) ^ s)) * Qd₀.eval ((N : ℂ) ^ (-s))) :
    ∀ s : ℂ, (1 : Polynomial ℂ).eval ((N : ℂ) ^ s) * ((N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s))) * Q.eval ((N : ℂ) ^ s) =
      ((Polynomial.C K).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((r : ℂ) * s)) * ((N : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((N : ℂ) ^ s)) * Qd.eval ((N : ℂ) ^ (-s)) := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)

  have hsplit : ∀ a b c : ℂ, c = a + b → (N : ℂ) ^ c = (N : ℂ) ^ a * (N : ℂ) ^ b := by
    intro a b c h; rw [h, Complex.cpow_add _ _ hNc]
  have e1 : ∀ s : ℂ, (N : ℂ) ^ (((r - m₀ : ℤ) : ℂ) * s) = (N : ℂ) ^ ((r : ℂ) * s) * (N : ℂ) ^ ((m₀ : ℂ) * (-s)) :=
    fun s => hsplit _ _ _ (by push_cast; ring)
  have e2 : ∀ s : ℂ, (N : ℂ) ^ (((r - m : ℤ) : ℂ) * s) = (N : ℂ) ^ ((r : ℂ) * s) * (N : ℂ) ^ ((m : ℂ) * (-s)) :=
    fun s => hsplit _ _ _ (by push_cast; ring)
  have e0 : ∀ s : ℂ, (N : ℂ) ^ (((0 : ℤ) : ℂ) * s) = 1 := fun s => by simp

  have stepA := LanglandsTunnell.clearedFE_of_clearedFE_of_forall_eval_mul_eval_mul_cpow_eq N hN
    (Polynomial.C K * P₀) Q₀ (Polynomial.C K * P) Q (r - m₀) (r - m) hQ₀
    (by
      intro s
      have h := ha (-s)
      simp only [neg_neg] at h
      simp only [Polynomial.eval_mul, Polynomial.eval_C, e1, e2]

      linear_combination (K * (N : ℂ) ^ ((r : ℂ) * s)) * h.symm)
    1 Pd₀ 1 Qd₀ 0 md₀
    (by
      intro s
      have h := hc s
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one, one_mul, mul_one] at h
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one, one_mul, mul_one, e1, e0]
      linear_combination h)

  have stepB := LanglandsTunnell.clearedFE_of_clearedFE_of_forall_eval_mul_eval_mul_cpow_eq N hN
    Pd₀ Qd₀ Pd Qd (-md₀) (-md) hQd₀
    (by
      intro t
      have h := hb (-t)
      simp only [neg_neg] at h
      have f1 : (N : ℂ) ^ (((-md₀ : ℤ) : ℂ) * t) = (N : ℂ) ^ ((md₀ : ℂ) * (-t)) := by congr 1; push_cast; ring
      have f2 : (N : ℂ) ^ (((-md : ℤ) : ℂ) * t) = (N : ℂ) ^ ((md : ℂ) * (-t)) := by congr 1; push_cast; ring
      rw [f1, f2]
      linear_combination h.symm)
    1 (Polynomial.C K * P) 1 Q 0 (m - r)
    (by
      intro t
      have h := stepA (-t)
      simp only [neg_neg, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one, mul_one, one_mul] at h
      have f1 : (N : ℂ) ^ (((-md₀ : ℤ) : ℂ) * t) = (N : ℂ) ^ ((md₀ : ℂ) * (-t)) := by congr 1; push_cast; ring
      have f3 : (N : ℂ) ^ (((m - r : ℤ) : ℂ) * t) = (N : ℂ) ^ (((r - m : ℤ) : ℂ) * (-t)) := by congr 1; push_cast; ring
      simp only [e0, mul_one, one_mul] at h
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one, mul_one, one_mul, f1, f3, e0]
      linear_combination h.symm)

  intro s
  have h := stepB (-s)
  simp only [neg_neg, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one, mul_one, one_mul] at h
  have f2 : (N : ℂ) ^ (((m - r : ℤ) : ℂ) * (-s)) = (N : ℂ) ^ ((r : ℂ) * s) * (N : ℂ) ^ ((m : ℂ) * (-s)) :=
    hsplit _ _ _ (by push_cast; ring)
  have f4 : (N : ℂ) ^ (((-md : ℤ) : ℂ) * (-s)) = (N : ℂ) ^ ((md : ℂ) * s) := by congr 1; push_cast; ring
  simp only [f2, f4, e0, mul_one, one_mul] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one, one_mul]
  linear_combination h.symm

end M2PGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_lt_rsLocalIntegral_jacquetWhittaker3_twistFamily_mul_centralTate_eq_cpow_mul_eval.M2PGlue"

namespace BridgeGlue

open Filter Topology

theorem isLocallyConstant_family (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (lamU : ℂ → Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hlamU : ∀ (u : ℂ) (a : (p.adicCompletion ℚ)ˣ),
      ((lamU u 0 a : ℂˣ) : ℂ) = ((lam 0 a : ℂˣ) : ℂ) * ((‖(a : (p.adicCompletion ℚ))‖ : ℂ)) ^ u ∧
        ((lamU u 1 a : ℂˣ) : ℂ) = ((lam 1 a : ℂˣ) : ℂ) ∧
          ((lamU u 2 a : ℂˣ) : ℂ) = ((lam 2 a : ℂˣ) : ℂ) * ((‖(a : (p.adicCompletion ℚ))‖ : ℂ)) ^ (-u))
    (u : ℂ) (i : Fin 3) : IsLocallyConstant (lamU u i) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h1 : ∀ᶠ y : (p.adicCompletion ℚ)ˣ in 𝓝 x, ‖(y : (p.adicCompletion ℚ))‖ = ‖(x : (p.adicCompletion ℚ))‖ :=
    (Units.continuous_val.tendsto x).eventually (LanglandsTunnell.CubicInduction.eventually_norm_eq p x.ne_zero)
  fin_cases i
  · have h2 : ∀ᶠ y : (p.adicCompletion ℚ)ˣ in 𝓝 x, lam 0 y = lam 0 x := (hlam 0).eventually_eq x
    filter_upwards [h1, h2] with y hy1 hy2
    apply Units.ext
    show ((lamU u 0 y : ℂˣ) : ℂ) = ((lamU u 0 x : ℂˣ) : ℂ)
    rw [(hlamU u y).1, (hlamU u x).1, hy1, hy2]
  · have h2 : ∀ᶠ y : (p.adicCompletion ℚ)ˣ in 𝓝 x, lam 1 y = lam 1 x := (hlam 1).eventually_eq x
    filter_upwards [h1, h2] with y hy1 hy2
    apply Units.ext
    show ((lamU u 1 y : ℂˣ) : ℂ) = ((lamU u 1 x : ℂˣ) : ℂ)
    rw [(hlamU u y).2.1, (hlamU u x).2.1, hy2]
  · have h2 : ∀ᶠ y : (p.adicCompletion ℚ)ˣ in 𝓝 x, lam 2 y = lam 2 x := (hlam 2).eventually_eq x
    filter_upwards [h1, h2] with y hy1 hy2
    apply Units.ext
    show ((lamU u 2 y : ℂˣ) : ℂ) = ((lamU u 2 x : ℂˣ) : ℂ)
    rw [(hlamU u y).2.2, (hlamU u x).2.2, hy1, hy2]

theorem norm_uniformiser (p : HeightOneSpectrum (𝓞 ℚ)) (ϖ : (p.adicCompletion ℚ)ˣ)
    (hϖ : Valued.v (ϖ : (p.adicCompletion ℚ)) = WithZero.exp (-1 : ℤ)) :
    ‖(ϖ : (p.adicCompletion ℚ))‖ = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [NumberField.FinitePlace.norm_def, hϖ, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero,
    show Multiplicative.toAdd (WithZero.unzero (WithZero.exp_ne_zero (a := (-1 : ℤ)))) = -1 from rfl]
  simp

theorem norm_uniformiser_cpow_neg (p : HeightOneSpectrum (𝓞 ℚ)) (ϖ : (p.adicCompletion ℚ)ˣ)
    (hϖ : Valued.v (ϖ : (p.adicCompletion ℚ)) = WithZero.exp (-1 : ℤ)) (u : ℂ) :
    ((‖(ϖ : (p.adicCompletion ℚ))‖ : ℂ)) ^ (-u) = (Ideal.absNorm p.asIdeal : ℂ) ^ u := by
  rw [norm_uniformiser p ϖ hϖ]
  push_cast
  rw [Complex.inv_cpow _ _ (by
      rw [show ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) = (((Ideal.absNorm p.asIdeal : ℕ) : ℝ) : ℂ) by push_cast; rfl,
        Complex.arg_ofReal_of_nonneg (by positivity)]
      exact Real.pi_ne_zero.symm),
    Complex.cpow_neg, inv_inv]

theorem sum_primal (N c s u : ℂ) :
    (∑ ab ∈ ({((0 : ℤ), (0 : ℤ)), (2, -1)} : Finset (ℤ × ℤ)),
        (fun ab : ℤ × ℤ => if ab = (0, 0) then (1 : ℂ) else -c) ab * N ^ (-(ab.1 : ℂ) * s) * N ^ (-(ab.2 : ℂ) * u)) =
      1 - c * N ^ u * N ^ (-(2 : ℂ) * s) := by
  rw [Finset.sum_pair (by simp)]
  simp only [if_true, Prod.mk.injEq, Int.cast_zero, neg_zero, zero_mul, Complex.cpow_zero, mul_one, Int.cast_ofNat,
    Int.cast_neg, Int.cast_one, neg_neg, one_mul]
  rw [if_neg (by omega)]
  ring

theorem sum_dual (N cd s u : ℂ) :
    (∑ ab ∈ ({((0 : ℤ), (0 : ℤ)), (2, 1)} : Finset (ℤ × ℤ)),
        (fun ab : ℤ × ℤ => if ab = (0, 0) then (1 : ℂ) else -cd) ab * N ^ (-(ab.1 : ℂ) * s) * N ^ (-(ab.2 : ℂ) * u)) =
      1 - cd * N ^ (-u) * N ^ (-(2 : ℂ) * s) := by
  rw [Finset.sum_pair (by simp)]
  simp only [if_true, Prod.mk.injEq, Int.cast_zero, neg_zero, zero_mul, Complex.cpow_zero, mul_one, Int.cast_ofNat,
    Int.cast_one, one_mul, neg_mul]
  rw [if_neg (by omega)]
  ring

end BridgeGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_lt_rsLocalIntegral_jacquetWhittaker3_twistFamily_mul_centralTate_eq_cpow_mul_eval.M2PGlue"

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (x y z : p.adicCompletion ℚ)

    (lamU : ℂ → Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hlamU0 : lamU 0 = lam)
    (hlamU : ∀ (u : ℂ) (a : (p.adicCompletion ℚ)ˣ),
      ((lamU u 0 a : ℂˣ) : ℂ) = ((lam 0 a : ℂˣ) : ℂ) * ((‖(a : p.adicCompletion ℚ)‖ : ℂ)) ^ u ∧
        ((lamU u 1 a : ℂˣ) : ℂ) = ((lam 1 a : ℂˣ) : ℂ) ∧
          ((lamU u 2 a : ℂˣ) : ℂ) = ((lam 2 a : ℂˣ) : ℂ) * ((‖(a : p.adicCompletion ℚ)‖ : ℂ)) ^ (-u))

    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])

    (E : Fin 3 → ℂ) (e : Fin 3 → ℤ)
    (hfe0 : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((lam 0 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((lam 0 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((lam 0 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((lam 0 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E 0 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 0 : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))
    (hfe1 : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((lam 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((lam 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((lam 1 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((lam 1 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E 1 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 1 : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))
    (hfe2 : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((lam 2 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((lam 2 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((lam 2 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((lam 2 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E 2 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 2 : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))
    :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          ∃ (c cd : ℂ) (u₁ : ℝ), ∀ u : ℝ, u₁ < u → ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),
            (∀ s : ℂ, σ₂ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (jacquetWhittaker3 p (lamU u) Φ (diagonal3 p ![1, -1, 1] * iotaGL g * (upperUnipotent3 x y z * antidiagonal3 p)) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂))) ∧
            (∀ s : ℂ, σ₃ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (dualWhittakerFn3 (fun h => jacquetWhittaker3 p (lamU u) Φ (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p))) (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂))) ∧
            (∀ s : ℂ, σ₂ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
                  s (fun g => jacquetWhittaker3 p (lamU u) Φ (diagonal3 p ![1, -1, 1] * iotaGL g * (upperUnipotent3 x y z * antidiagonal3 p))) w₂ *
                (∑ ab ∈ ({((0 : ℤ), (0 : ℤ)), (2, -1)} : Finset (ℤ × ℤ)),
                  (fun ab : ℤ × ℤ => if ab = (0, 0) then (1 : ℂ) else -c) ab *
                    (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.2 : ℂ) * (u : ℂ))) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
            (∀ s : ℂ, σ₃ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
                  s (fun g => dualWhittakerFn3 (fun h => jacquetWhittaker3 p (lamU u) Φ (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p))) (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) *
                (∑ ab ∈ ({((0 : ℤ), (0 : ℤ)), (2, 1)} : Finset (ℤ × ℤ)),
                  (fun ab : ℤ × ℤ => if ab = (0, 0) then (1 : ℂ) else -cd) ab *
                    (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.2 : ℂ) * (u : ℂ))) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by
  intro μ₂ hμ₂ μN₂ hμN₂ w₂ hw₂
  have hlc := BridgeGlue.isLocallyConstant_family p lam hlam lamU hlamU
  obtain ⟨u₀, hu₀⟩ := M2PGlue.exists_forall_chamber_of_twistFamily p lam hlam lamU hlamU
  have h1N : 1 < Ideal.absNorm p.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm p
  have hNc : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)

  set ϖ : (p.adicCompletion ℚ)ˣ := NumberField.AdelicLevel.uniformizerUnit ℚ p with hϖdef
  have hϖ : Valued.v (ϖ : (p.adicCompletion ℚ)) = WithZero.exp (-1 : ℤ) := NumberField.AdelicLevel.valued_uniformizerUnit ℚ p
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ((θ₀ ϖ : ℂˣ) : ℂ) * ((lam 1 ϖ : ℂˣ) : ℂ) * ((lam 2 ϖ : ℂˣ) : ℂ) := ⟨_, rfl⟩
  refine ⟨c, c⁻¹ * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ)), u₀, fun u hu => ?_⟩
  obtain ⟨σ, hσ, h01, h12⟩ := hu₀ (u : ℂ) (by rw [Complex.ofReal_re]; exact hu)
  have hfe0u := fun w hw => M2PGlue.hfe_shift p w θ₀ wJ (lam 0) (lamU u 0) (u : ℂ) (fun y => (hlamU u y).1)
    (E 0) (e 0) (hfe0 w hw)
  have hfe1u := fun w hw => M2PGlue.hfe_shift p w θ₀ wJ (lam 1) (lamU u 1) 0
    (fun y => by rw [Complex.cpow_zero, mul_one]; exact (hlamU u y).2.1) (E 1) (e 1) (hfe1 w hw)
  have hfe2u := fun w hw => M2PGlue.hfe_shift p w θ₀ wJ (lam 2) (lamU u 2) (-(u : ℂ)) (fun y => (hlamU u y).2.2)
    (E 2) (e 2) (hfe2 w hw)
  obtain ⟨⟨m, P, σ₂, hP⟩, ⟨md, Pd, σ₃, hPd⟩⟩ :=
    LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_jacquetWhittaker3_mul_centralTate_eq_cpow_mul_eval_and_dual_of_chamber
      p ϖ hϖ (lamU u) (hlc u) σ hσ h01 h12 Φ hΦ x y z
      (fun h => jacquetWhittaker3 p (lamU u) Φ (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p))) rfl
      θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral w₀p hw₀p wJ hwJ
      ![E 0 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 0 : ℂ) * (u : ℂ)), E 1 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 1 : ℂ) * 0), E 2 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 2 : ℂ) * (-(u : ℂ)))] e
      hfe0u hfe1u hfe2u μ₂ μN₂ w₂ hw₂

  have hcu : (((θ₀ ϖ : ℂˣ) : ℂ) * ((lamU u 1 ϖ : ℂˣ) : ℂ) * ((lamU u 2 ϖ : ℂˣ) : ℂ)) = c * (Ideal.absNorm p.asIdeal : ℂ) ^ (u : ℂ) := by
    rw [(hlamU u ϖ).2.1, (hlamU u ϖ).2.2, BridgeGlue.norm_uniformiser_cpow_neg p ϖ hϖ, hc]
    ring
  have hNu : ((Ideal.absNorm p.asIdeal : ℂ) ^ (u : ℂ))⁻¹ = (Ideal.absNorm p.asIdeal : ℂ) ^ (-(u : ℂ)) := by rw [Complex.cpow_neg]
  refine ⟨P, Pd, m, md, σ₂, σ₃, fun s hs => (hP s hs).1, fun s hs => (hPd s hs).1, fun s hs => ?_, fun s hs => ?_⟩
  · rw [BridgeGlue.sum_primal, ← (hP s hs).2, hcu]
  · rw [BridgeGlue.sum_dual, ← (hPd s hs).2, hcu, mul_inv, hNu]
    ring

end S_LanglandsTunnell_RankinSelberg_exists_forall_lt_rsLocalIntegral_jacquetWhittaker3_twistFamily_mul_centralTate_eq_cpow_mul_eval
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_lt_rsLocalIntegral_jacquetWhittaker3_twistFamily_mul_centralTate_eq_cpow_mul_eval (solution)
