-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/572d3ba4-d84b-5cd7-8214-2f6bb6d1c882

import Theorems.Thm_AutomorphicForm_WhittakerModel_setIntegral_unitShell_diagOne_weyl_eq_stdRootNumberAt_mul_setIntegral_shell_of_admissible_of_le_of_norm_eq_one
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_mem_localLevelOne_pow_mul_eq_of_forall_mem_localLevelOne_mul_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_ne_zero_of_hasConductorExponentAt
import Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_tateFourier_psiLocal_selfDualHaarAt_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_isSchwartzBruhat_tateFourier
import Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_comp_mul_left
import Theorems.Thm_LanglandsTunnell_TateLocal_hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_MeasureTheory_Measure_isInvInvariant_of_isMulRightInvariant
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_NumberField_AdelicLevel

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
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

noncomputable section

namespace PSKernelsBody

open NumberField.StandardAddChar

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem level_zero :
    (∀ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (0 : ℤ) → psiLocal ℚ p x = 1) ∧
      ∃ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ psiLocal ℚ p x ≠ 1 := by
  have hk : ∃ k : ℤ, ∀ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp k → psiLocal ℚ p x = 1 := by
    refine ⟨0, fun x hx => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ p x ?_⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simpa using hx
  have h := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ p (psiLocal ℚ p) hk
    (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p)
  rwa [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p] at h

theorem selfDualHaarAt_eq :
    selfDualHaarAt ℚ p = @Measure.addHaarMeasure (p.adicCompletion ℚ) _ _ _ (localBorel ℚ p)
      (borelSpace_localBorel ℚ p) (integersPositiveCompacts ℚ p) := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  unfold selfDualHaarAt
  rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p]
  simp

theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel ℚ p
    Measure.IsAddHaarMeasure (selfDualHaarAt ℚ p) := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  rw [selfDualHaarAt_eq p]
  infer_instance

theorem regular_selfDualHaarAt :
    letI := localBorel ℚ p
    Measure.Regular (selfDualHaarAt ℚ p) := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  rw [selfDualHaarAt_eq p]
  infer_instance

section Generic
variable {K : Type*} [Field K] [MeasurableSpace K]

theorem tateFourier_inv_apply (ψ : AddChar K ℂ) (μ : Measure K) (f : K → ℂ) (y : K) :
    tateFourier ψ⁻¹ μ f y = tateFourier ψ μ f (-y) := by
  unfold tateFourier
  congr 1
  funext x
  rw [AddChar.inv_apply, mul_neg]

theorem tateFourier_const_mul (ψ : AddChar K ℂ) (μ : Measure K) (c : ℂ) (f : K → ℂ) (y : K) :
    tateFourier ψ μ (fun x => c * f x) y = c * tateFourier ψ μ f y := by
  unfold tateFourier
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

end Generic

theorem exp_add_one_le_of_not_le {y : p.adicCompletion ℚ} {r : ℤ} (hy : ¬ Valued.v y ≤ WithZero.exp r) :
    y ≠ 0 ∧ WithZero.exp (r + 1) ≤ Valued.v y := by
  have hy0 : y ≠ 0 := by
    intro h; apply hy; rw [h, map_zero]; exact zero_le'
  refine ⟨hy0, ?_⟩
  have hv0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
  rw [← WithZero.exp_log hv0] at hy ⊢
  rw [WithZero.exp_le_exp]
  rw [WithZero.exp_le_exp, not_le] at hy
  omega

theorem tateFourier_eq_zero_of_forall_translate (g : p.adicCompletion ℚ → ℂ) (r : ℤ)
    (hg : ∀ a : p.adicCompletion ℚ, Valued.v a ≤ WithZero.exp r → ∀ x, g (x + a) = g x)
    (y : p.adicCompletion ℚ) (hy : ¬ Valued.v y ≤ WithZero.exp (-r)) :
    letI := localBorel ℚ p
    tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) g y = 0 := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI := isAddHaarMeasure_selfDualHaarAt p
  obtain ⟨hy0, hyr⟩ := exp_add_one_le_of_not_le p hy
  obtain ⟨x₁, hx₁, hψx₁⟩ := (level_zero p).2
  have hvy : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
  have hva : Valued.v (x₁ * y⁻¹) ≤ WithZero.exp r := by
    rw [map_mul, map_inv₀]
    have h1 : (Valued.v y)⁻¹ ≤ (WithZero.exp (-r + 1))⁻¹ := inv_anti₀ WithZero.exp_pos hyr
    calc Valued.v x₁ * (Valued.v y)⁻¹ ≤ WithZero.exp (0 + 1) * (WithZero.exp (-r + 1))⁻¹ :=
          mul_le_mul' hx₁ h1
      _ = WithZero.exp r := by
          rw [← WithZero.exp_neg, ← WithZero.exp_add]
          congr 1; ring
  have hay : x₁ * y⁻¹ * y = x₁ := by rw [mul_assoc, inv_mul_cancel₀ hy0, mul_one]
  have key : tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) g y =
      psiLocal ℚ p x₁ * tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) g y := by
    unfold tateFourier
    rw [← integral_const_mul]
    rw [← integral_add_right_eq_self (μ := selfDualHaarAt ℚ p) (fun x => g x * (psiLocal ℚ p) (x * y)) (x₁ * y⁻¹)]
    congr 1
    funext x
    rw [hg (x₁ * y⁻¹) hva x, add_mul, hay, AddChar.map_add_eq_mul]
    ring
  have h1 : (1 - psiLocal ℚ p x₁) * tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) g y = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hψx₁
  · exact h

section Shell

variable {p}

theorem mem_higherUnitsAt_of_valued_sub_one_le {m : ℕ} (hm : 1 ≤ m) {u : (p.adicCompletion ℚ)ˣ}
    (hu : Valued.v ((u : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(m : ℤ))) :
    u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p m := by
  refine ⟨?_, Or.inr hu⟩
  have hlt : Valued.v ((u : p.adicCompletion ℚ) - 1) < 1 := by
    refine lt_of_le_of_lt hu ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have := Valuation.map_add_eq_of_lt_left (Valued.v) (x := (1 : p.adicCompletion ℚ)) (y := (u : p.adicCompletion ℚ) - 1)
    (by rwa [map_one])
  rw [map_one, add_sub_cancel] at this
  exact this

theorem valued_div_sub_one_le {x a : p.adicCompletion ℚ} (hx : x ≠ 0) {n : ℤ} (hxn : Valued.v x = WithZero.exp n)
    {m : ℕ} (ha : Valued.v a ≤ WithZero.exp (n - (m : ℤ))) :
    Valued.v ((x + a) * x⁻¹ - 1) ≤ WithZero.exp (-(m : ℤ)) := by
  have : (x + a) * x⁻¹ - 1 = a * x⁻¹ := by field_simp; ring
  rw [this, map_mul, map_inv₀, hxn, ← WithZero.exp_neg]
  calc Valued.v a * WithZero.exp (-n) ≤ WithZero.exp (n - (m : ℤ)) * WithZero.exp (-n) := mul_le_mul_left ha _
    _ = WithZero.exp (-(m : ℤ)) := by rw [← WithZero.exp_add]; congr 1; ring

theorem valued_add_eq_of_le {x a : p.adicCompletion ℚ} {n : ℤ} (hxn : Valued.v x = WithZero.exp n)
    {m : ℕ} (hm : 1 ≤ m) (ha : Valued.v a ≤ WithZero.exp (n - (m : ℤ))) : Valued.v (x + a) = Valued.v x := by
  apply Valuation.map_add_eq_of_lt_left
  rw [hxn]
  refine lt_of_le_of_lt ha ?_
  rw [WithZero.exp_lt_exp]; omega

theorem valued_add_ne_of_ne {x a : p.adicCompletion ℚ} {n : ℤ} (hxn : Valued.v x ≠ WithZero.exp n)
    {m : ℕ} (hm : 1 ≤ m) (ha : Valued.v a ≤ WithZero.exp (n - (m : ℤ))) : Valued.v (x + a) ≠ WithZero.exp n := by
  have halt : Valued.v a < WithZero.exp n := by
    refine lt_of_le_of_lt ha ?_
    rw [WithZero.exp_lt_exp]; omega
  rcases lt_or_gt_of_ne hxn with hlt | hgt
  · exact (lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hlt halt)).ne
  · rw [Valuation.map_add_eq_of_lt_left _ (lt_trans halt hgt)]
    exact hxn

variable (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (c : (p.adicCompletion ℚ)ˣ) (n : ℤ)

def shellFn (x : p.adicCompletion ℚ) : ℂ :=
  if Valued.v x = WithZero.exp n then charExt χ (x * (c : p.adicCompletion ℚ)) else 0

theorem shellFn_of_ne {x : p.adicCompletion ℚ} (hx : Valued.v x ≠ WithZero.exp n) : shellFn χ c n x = 0 := by
  simp [shellFn, hx]

theorem shellFn_of_eq {x : p.adicCompletion ℚ} (hx : Valued.v x = WithZero.exp n) :
    shellFn χ c n x = charExt χ (x * (c : p.adicCompletion ℚ)) := by
  simp [shellFn, hx]

theorem ne_zero_of_valued_eq_exp {x : p.adicCompletion ℚ} {k : ℤ} (hx : Valued.v x = WithZero.exp k) : x ≠ 0 := by
  intro h; rw [h, map_zero] at hx; exact WithZero.exp_ne_zero hx.symm

theorem shellFn_add {m : ℕ} (hm : 1 ≤ m) (hχ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p m, χ u = 1)
    (a : p.adicCompletion ℚ) (ha : Valued.v a ≤ WithZero.exp (n - (m : ℤ))) (x : p.adicCompletion ℚ) :
    shellFn χ c n (x + a) = shellFn χ c n x := by
  by_cases hx : Valued.v x = WithZero.exp n
  · have hxa : Valued.v (x + a) = WithZero.exp n := (valued_add_eq_of_le hx hm ha).trans hx
    rw [shellFn_of_eq χ c n hxa, shellFn_of_eq χ c n hx]
    have hx0 : x ≠ 0 := ne_zero_of_valued_eq_exp hx
    have hxa0 : x + a ≠ 0 := ne_zero_of_valued_eq_exp hxa
    rw [charExt_of_ne_zero χ (mul_ne_zero hxa0 c.ne_zero), charExt_of_ne_zero χ (mul_ne_zero hx0 c.ne_zero)]

    set u : (p.adicCompletion ℚ)ˣ := Units.mk0 ((x + a) * x⁻¹) (mul_ne_zero hxa0 (inv_ne_zero hx0)) with hu
    have hmem : u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p m :=
      mem_higherUnitsAt_of_valued_sub_one_le hm (by rw [hu, Units.val_mk0]; exact valued_div_sub_one_le hx0 hx ha)
    have hfac : Units.mk0 ((x + a) * (c : p.adicCompletion ℚ)) (mul_ne_zero hxa0 c.ne_zero) =
        u * Units.mk0 (x * (c : p.adicCompletion ℚ)) (mul_ne_zero hx0 c.ne_zero) := by
      ext
      simp only [Units.val_mul, Units.val_mk0, hu]
      field_simp
    rw [hfac, map_mul, hχ u hmem, one_mul]
  · rw [shellFn_of_ne χ c n hx, shellFn_of_ne χ c n (valued_add_ne_of_ne hx hm ha)]

theorem shellFn_unit_mul (t : (p.adicCompletion ℚ)ˣ) (ht : Valued.v (t : p.adicCompletion ℚ) = 1)
    (x : p.adicCompletion ℚ) :
    shellFn χ c n (((t⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * x) = ((χ t⁻¹ : ℂˣ) : ℂ) * shellFn χ c n x := by
  have hti : Valued.v (((t⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, ht, inv_one]
  have hv : Valued.v (((t⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * x) = Valued.v x := by
    rw [map_mul, hti, one_mul]
  by_cases hx : Valued.v x = WithZero.exp n
  · rw [shellFn_of_eq χ c n (hv.trans hx), shellFn_of_eq χ c n hx]
    have hx0 : x ≠ 0 := ne_zero_of_valued_eq_exp hx
    rw [charExt_of_ne_zero χ (mul_ne_zero hx0 c.ne_zero),
      charExt_of_ne_zero χ (mul_ne_zero (mul_ne_zero (t⁻¹).ne_zero hx0) c.ne_zero)]
    have hfac : Units.mk0 (((t⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * x * (c : p.adicCompletion ℚ))
        (mul_ne_zero (mul_ne_zero (t⁻¹).ne_zero hx0) c.ne_zero) =
        t⁻¹ * Units.mk0 (x * (c : p.adicCompletion ℚ)) (mul_ne_zero hx0 c.ne_zero) := by
      ext; simp only [Units.val_mul, Units.val_mk0, mul_assoc]
    rw [hfac, map_mul, Units.val_mul]
  · rw [shellFn_of_ne χ c n hx, shellFn_of_ne χ c n (fun h => hx (hv.symm.trans h)), mul_zero]

theorem valued_uniformizer_zpow (j : ℤ) :
    Valued.v (((NumberField.AdelicLevel.uniformizerUnit ℚ p ^ j : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) =
      WithZero.exp (-j) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, NumberField.AdelicLevel.valued_uniformizerUnit ℚ p, ← WithZero.exp_zsmul]
  congr 1; ring

theorem isOpen_valued_sub_le (x a₀ : p.adicCompletion ℚ) (ha₀ : a₀ ≠ 0) :
    IsOpen {y : p.adicCompletion ℚ | Valued.v (y - x) ≤ Valued.v a₀} := by
  have h : {y : p.adicCompletion ℚ | Valued.v (y - x) ≤ Valued.v a₀} =
      (fun y => y - x) ⁻¹' {z : p.adicCompletion ℚ | Valued.v.restrict z ≤ Valued.v.restrict a₀} := by
    ext y; simp [Valuation.restrict_le_iff]
  rw [h]
  refine IsOpen.preimage (continuous_sub_right x) (Valued.isOpen_closedBall _ ?_)
  have hpos : 0 < Valued.v.restrict a₀ :=
    (Valuation.restrict_pos_iff _ _).mpr (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr ha₀))
  exact ne_of_gt hpos

theorem isCompact_valued_le (k : ℤ) : IsCompact {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp k} := by

  set ϖ : (p.adicCompletion ℚ)ˣ := NumberField.AdelicLevel.uniformizerUnit ℚ p with hϖ
  have hvϖ : Valued.v ((ϖ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) :=
    NumberField.AdelicLevel.valued_uniformizerUnit ℚ p
  have hvpow : ∀ j : ℤ, Valued.v (((ϖ ^ j : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) = WithZero.exp (-j) :=
    fun j => by rw [hϖ]; exact valued_uniformizer_zpow j
  have hO : IsCompact ((p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ))) := by
    rw [← LanglandsTunnell.TateLocal.coe_integersPositiveCompacts]
    exact (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ p).isCompact
  have heq : {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp k} =
      (fun x => (((ϖ ^ (-k) : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) * x) ''
        (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
    constructor
    · intro hx
      refine ⟨(((ϖ ^ k : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) * x, ?_, ?_⟩
      · rw [map_mul, hvpow]
        calc WithZero.exp (-k) * Valued.v x ≤ WithZero.exp (-k) * WithZero.exp k := mul_le_mul_right hx _
          _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
      · rw [← mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, one_mul]
    · rintro ⟨z, hz, rfl⟩
      rw [map_mul, hvpow, neg_neg]
      calc WithZero.exp k * Valued.v z ≤ WithZero.exp k * 1 := mul_le_mul_right hz _
        _ = WithZero.exp k := mul_one _
  rw [heq]
  exact hO.image (continuous_const_mul _)

theorem isSchwartzBruhat_shellFn {m : ℕ} (hm : 1 ≤ m)
    (hχ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p m, χ u = 1) : IsSchwartzBruhat (shellFn χ c n) := by
  constructor
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    set a₀ : p.adicCompletion ℚ :=
      ((NumberField.AdelicLevel.uniformizerUnit ℚ p ^ ((m : ℤ) - n) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) with ha₀
    have hva₀ : Valued.v a₀ = WithZero.exp (n - (m : ℤ)) := by
      rw [ha₀, valued_uniformizer_zpow]; congr 1; ring
    have ha₀0 : a₀ ≠ 0 := ne_zero_of_valued_eq_exp hva₀
    refine ⟨{y | Valued.v (y - x) ≤ Valued.v a₀}, isOpen_valued_sub_le x a₀ ha₀0, ?_, ?_⟩
    · show Valued.v (x - x) ≤ Valued.v a₀
      rw [sub_self, map_zero]; exact zero_le'
    · intro y hy
      have hy' : Valued.v (y - x) ≤ WithZero.exp (n - (m : ℤ)) := by rw [← hva₀]; exact hy
      have := shellFn_add χ c n hm hχ (y - x) hy' x
      rwa [add_sub_cancel] at this
  · refine HasCompactSupport.intro (isCompact_valued_le n) fun x hx => ?_
    apply shellFn_of_ne
    intro h; exact hx (by rw [Set.mem_setOf_eq, h])

end Shell

section Fourier
variable {p}

theorem modulus_eq_one_of_valued_eq_one (t : (p.adicCompletion ℚ)ˣ) (ht : Valued.v (t : p.adicCompletion ℚ) = 1) :
    modulus (t : p.adicCompletion ℚ) = 1 := by
  have h := (LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p).2.2.2.1
    0 t (by simpa using ht)
  simp only [neg_zero, zpow_zero] at h
  exact_mod_cast h

theorem tateFourier_shellFn_unit_mul (ψ : AddChar (p.adicCompletion ℚ) ℂ) (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (c : (p.adicCompletion ℚ)ˣ) (n : ℤ) (t : (p.adicCompletion ℚ)ˣ) (ht : Valued.v (t : p.adicCompletion ℚ) = 1)
    (y : p.adicCompletion ℚ) :
    letI := localBorel ℚ p
    tateFourier ψ (selfDualHaarAt ℚ p) (shellFn χ c n) ((t : p.adicCompletion ℚ) * y) =
      ((χ t⁻¹ : ℂˣ) : ℂ) * tateFourier ψ (selfDualHaarAt ℚ p) (shellFn χ c n) y := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI := isAddHaarMeasure_selfDualHaarAt p
  haveI := regular_selfDualHaarAt p
  have hcomp := LanglandsTunnell.TateLocal.tateFourier_comp_mul_left (p.adicCompletion ℚ) ψ (selfDualHaarAt ℚ p)
    (shellFn χ c n) (((t⁻¹ : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) (t⁻¹).ne_zero y
  have hfun : (fun x => shellFn χ c n ((((t⁻¹ : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) * x)) =
      fun x => ((χ t⁻¹ : ℂˣ) : ℂ) * shellFn χ c n x := by
    funext x; exact shellFn_unit_mul χ c n t ht x
  rw [hfun, tateFourier_const_mul] at hcomp
  have hmod : modulus (((t⁻¹ : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) = 1 :=
    modulus_eq_one_of_valued_eq_one t⁻¹ (by rw [Units.val_inv_eq_inv_val, map_inv₀, ht, inv_one])
  rw [hmod, Units.val_inv_eq_inv_val, inv_inv] at hcomp
  rw [hcomp]
  push_cast
  ring

theorem tateFourier_inv_shellFn_eq_zero (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (c : (p.adicCompletion ℚ)ˣ) (n : ℤ)
    {m : ℕ} (hm : 1 ≤ m) (hχ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p m, χ u = 1)
    (y : p.adicCompletion ℚ) (hy : ¬ Valued.v y ≤ WithZero.exp ((m : ℤ) - n)) :
    letI := localBorel ℚ p
    tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) (shellFn χ c n) y = 0 := by
  letI := localBorel ℚ p
  rw [tateFourier_inv_apply]
  refine tateFourier_eq_zero_of_forall_translate p (shellFn χ c n) (n - (m : ℤ)) (shellFn_add χ c n hm hχ) (-y) ?_
  rw [Valuation.map_neg]
  intro h; apply hy
  refine h.trans (le_of_eq ?_)
  congr 1; ring

theorem tateFourier_shellFn_eq_zero (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (c : (p.adicCompletion ℚ)ˣ) (n : ℤ)
    {m : ℕ} (hm : 1 ≤ m) (hχ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p m, χ u = 1)
    (y : p.adicCompletion ℚ) (hy : ¬ Valued.v y ≤ WithZero.exp ((m : ℤ) - n)) :
    letI := localBorel ℚ p
    tateFourier (NumberField.StandardAddChar.psiLocal ℚ p) (selfDualHaarAt ℚ p) (shellFn χ c n) y = 0 := by
  letI := localBorel ℚ p
  refine tateFourier_eq_zero_of_forall_translate p (shellFn χ c n) (n - (m : ℤ)) (shellFn_add χ c n hm hχ) y ?_
  intro h; apply hy
  refine h.trans (le_of_eq ?_)
  congr 1; ring

end Fourier

end PSKernelsBody
end

noncomputable section

section SupplyWA
open NumberField.AdelicLevel
open scoped NNReal ENNReal

namespace Ws31
namespace E4S

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem valued_ne_zero (y : (p.adicCompletion ℚ)ˣ) : Valued.v (y : p.adicCompletion ℚ) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr y.ne_zero

theorem valued_varpi_zpow (m : ℤ) :
    Valued.v ((uniformizerUnit ℚ p ^ m : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem isOpen_shellK (n : ℤ) : IsOpen {x : p.adicCompletion ℚ | Valued.v x = WithZero.exp (-n)} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [Set.mem_setOf_eq] at hx
  have h := Valued.locally_const (x := x) (by rw [hx]; exact WithZero.coe_ne_zero)
  rw [hx] at h
  exact h

theorem shell_eq_preimage (n : ℤ) :
    {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))} = Units.val ⁻¹' {x : p.adicCompletion ℚ | Valued.v x = WithZero.exp (-n)} := rfl

theorem isOpen_shell (n : ℤ) : IsOpen {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))} := by
  rw [shell_eq_preimage]
  exact (isOpen_shellK p n).preimage Units.continuous_val

theorem varpi_zpow_mem_shell (n : ℤ) : uniformizerUnit ℚ p ^ n ∈ {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))} :=
  valued_varpi_zpow p n

theorem shell_eq_preimage_mul (n : ℤ) :
    {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))} = (fun h => uniformizerUnit ℚ p ^ (-n) * h) ⁻¹' {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-((0 : ℤ)))} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.val_mul, map_mul, valued_varpi_zpow, neg_neg, neg_zero,
    WithZero.exp_zero]
  constructor
  · intro h
    rw [h, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  · intro h
    calc Valued.v (y : p.adicCompletion ℚ)
        = WithZero.exp (-n) * (WithZero.exp n * Valued.v (y : p.adicCompletion ℚ)) := by
          rw [← mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, one_mul]
      _ = WithZero.exp (-n) := by rw [h, mul_one]

theorem shellK_zero_eq_sphere :
    {x : p.adicCompletion ℚ | Valued.v x = WithZero.exp (-((0 : ℤ)))} = Metric.sphere (0 : p.adicCompletion ℚ) 1 := by
  ext x
  simp only [Set.mem_setOf_eq, Metric.mem_sphere, dist_zero_right, neg_zero, WithZero.exp_zero]
  constructor
  · intro h
    exact le_antisymm (Valued.toNormedField.norm_le_one_iff.mpr h.le) (Valued.toNormedField.one_le_norm_iff.mpr h.ge)
  · intro h
    exact le_antisymm (Valued.toNormedField.norm_le_one_iff.mp h.le) (Valued.toNormedField.one_le_norm_iff.mp h.ge)

theorem isCompact_shell_zero : IsCompact {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-((0 : ℤ)))} := by
  refine Units.isEmbedding_val₀.isCompact_iff.mpr ?_
  have himg : Units.val '' {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-((0 : ℤ)))}
      = {x : p.adicCompletion ℚ | Valued.v x = WithZero.exp (-((0 : ℤ)))} := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hx
      have hx0 : x ≠ 0 := by
        intro h0
        rw [h0, Set.mem_setOf_eq, map_zero] at hx
        exact WithZero.coe_ne_zero hx.symm
      exact ⟨Units.mk0 x hx0, hx, Units.val_mk0 hx0⟩
  rw [himg, shellK_zero_eq_sphere]
  exact isCompact_sphere _ _

theorem modulus_eq_of_mem_shell (n : ℤ) (y : (p.adicCompletion ℚ)ˣ) (hy : y ∈ {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))}) :
    (modulus (y : p.adicCompletion ℚ) : ℝ) = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-n) := by
  rw [Set.mem_setOf_eq] at hy
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p, coe_nnnorm, NumberField.FinitePlace.norm_def,
    hy, show WithZero.exp (-n) = ((Multiplicative.ofAdd (-n) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd, NNReal.coe_zpow,
    NNReal.coe_natCast]

section Meas

variable [MeasurableSpace (p.adicCompletion ℚ)]

theorem measurable_val : Measurable (Units.val : (p.adicCompletion ℚ)ˣ → p.adicCompletion ℚ) :=
  comap_measurable Units.val

variable [BorelSpace (p.adicCompletion ℚ)]

private theorem _root_.Ws31.E4S.measurableSet_shell (n : ℤ) : MeasurableSet {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))} := by
  rw [shell_eq_preimage]
  exact (isOpen_shellK p n).measurableSet.preimage (measurable_val p)

p2m_export "Ws31.E4S" "measurableSet_shell"

scoped instance borelSpace_units : BorelSpace (p.adicCompletion ℚ)ˣ :=
  ⟨by
    rw [(Units.isEmbedding_val₀ (G₀ := p.adicCompletion ℚ)).isInducing.eq_induced, borel_comap,
      ← BorelSpace.measurable_eq (α := p.adicCompletion ℚ)]
    rfl⟩

variable (μ : Measure (p.adicCompletion ℚ)) [μ.IsAddHaarMeasure]

scoped instance isHaarMeasure_units : (Measure.comap Units.val (mulMeasure μ)).IsHaarMeasure :=
  LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ p μ

theorem measure_shell_eq (n : ℤ) :
    (Measure.comap Units.val (mulMeasure μ)) {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))}
      = (Measure.comap Units.val (mulMeasure μ)) {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-((0 : ℤ)))} := by
  rw [shell_eq_preimage_mul p n]
  exact measure_preimage_mul _ _ _

theorem measure_shell_pos (n : ℤ) : 0 < (Measure.comap Units.val (mulMeasure μ)) {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))} :=
  (isOpen_shell p n).measure_pos _ ⟨_, varpi_zpow_mem_shell p n⟩

theorem measure_shell_lt_top (n : ℤ) : (Measure.comap Units.val (mulMeasure μ)) {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))} < ⊤ := by
  rw [measure_shell_eq p μ n]
  exact (isCompact_shell_zero p).measure_lt_top

omit [μ.IsAddHaarMeasure] in
theorem hasSum_setIntegral_shell (f : (p.adicCompletion ℚ)ˣ → ℂ) (hf : Integrable f (Measure.comap Units.val (mulMeasure μ))) :
    HasSum (fun n : ℤ => ∫ y in {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))}, f y ∂(Measure.comap Units.val (mulMeasure μ)))
      (∫ y, f y ∂(Measure.comap Units.val (mulMeasure μ))) := by
  have hunion : (⋃ n : ℤ, {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))}) = Set.univ := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨-WithZero.log (Valued.v (y : p.adicCompletion ℚ)), by rw [neg_neg, WithZero.exp_log (valued_ne_zero p y)]⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun n : ℤ => {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))}) := by
    intro m n hmn
    dsimp only [Function.onFun]
    rw [Set.disjoint_left]
    intro y hym hyn
    rw [Set.mem_setOf_eq] at hym hyn
    exact hmn (neg_inj.mp (WithZero.exp_injective (hym.symm.trans hyn)))
  have h := hasSum_integral_iUnion (μ := Measure.comap Units.val (mulMeasure μ)) (f := f)
    (fun n => measurableSet_shell p n) hdisj (by rw [hunion]; exact hf.integrableOn)
  rwa [hunion, Measure.restrict_univ] at h

end Meas

end Ws31.E4S
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31.E4S"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31"

namespace Ws31
namespace E4A

open NumberField.StandardAddChar NumberField.AdelicLevel

variable {p : HeightOneSpectrum (𝓞 ℚ)}

theorem isCompact_shell (p : HeightOneSpectrum (𝓞 ℚ)) (n : ℤ) :
    IsCompact {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))} := by
  rw [Ws31.E4S.shell_eq_preimage_mul p n]
  exact (Homeomorph.mulLeft (uniformizerUnit ℚ p ^ (-n))).isCompact_preimage.2 (Ws31.E4S.isCompact_shell_zero p)

theorem shell_eq_neg (T : Set (p.adicCompletion ℚ)ˣ) (n : ℤ)
    (hT : T = {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp n}) :
    T = {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp (-(-n))} := by
  rw [neg_neg]; exact hT

theorem shell_facts (k : ℤ) :
    letI := localBorel ℚ p
    MeasurableSet {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp k} ∧
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp k} < ⊤ ∧
      0 < (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp k} := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI : (selfDualHaarAt ℚ p).IsAddHaarMeasure := PSKernelsBody.isAddHaarMeasure_selfDualHaarAt p
  have hS : {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp k} =
      {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp (-(-k))} := by rw [neg_neg]
  rw [hS]
  exact ⟨Ws31.E4S.measurableSet_shell p (-k), Ws31.E4S.measure_shell_lt_top p _ (-k),
    Ws31.E4S.measure_shell_pos p _ (-k)⟩

theorem setIntegral_shell_const (k : ℤ) (c : ℂ) :
    letI := localBorel ℚ p
    (∫ t in {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp k}, c
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
      c * (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
        {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp k}).toReal : ℂ) ∧
    ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
        {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp k}).toReal ≠ 0 := by
  letI := localBorel ℚ p
  obtain ⟨-, hfin, hpos⟩ := shell_facts (p := p) k
  refine ⟨?_, (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'⟩
  rw [setIntegral_const, Complex.real_smul, mul_comm]
  first
    | rfl
    | (left; rfl)
    | simp [Measure.real]
    | simp [measureReal_def]

theorem setIntegral_integral_swap (T : Set (p.adicCompletion ℚ)ˣ) (n : ℤ)
    (hT : T = {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp n})
    (F : (p.adicCompletion ℚ)ˣ → p.adicCompletion ℚ → ℂ)
    (hF : Continuous fun q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ => F q.1 q.2)
    (Kc : Set (p.adicCompletion ℚ)) (hKc : IsCompact Kc) (hsupp : ∀ t x, x ∉ Kc → F t x = 0) :
    letI := localBorel ℚ p
    (∫ t in T, (∫ x, F t x ∂(selfDualHaarAt ℚ p)) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
      ∫ x, (∫ t in T, F t x ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∂(selfDualHaarAt ℚ p) := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI : (selfDualHaarAt ℚ p).IsAddHaarMeasure := PSKernelsBody.isAddHaarMeasure_selfDualHaarAt p
  obtain ⟨hTm, hTfin, -⟩ := shell_facts (p := p) n
  rw [← hT] at hTm hTfin
  have hTc : IsCompact T := by rw [shell_eq_neg T n hT]; exact isCompact_shell p (-n)
  haveI hfinT : IsFiniteMeasure ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).restrict T) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hTfin⟩

  have hF' : Continuous (Function.uncurry F) := hF
  have h1 : IntegrableOn (Function.uncurry F) (T ×ˢ Kc)
      (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).restrict T).prod (selfDualHaarAt ℚ p)) :=
    hF'.continuousOn.integrableOn_compact (hTc.prod hKc)
  have h2 : IntegrableOn (Function.uncurry F) (T ×ˢ (Set.univ : Set (p.adicCompletion ℚ)))
      (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).restrict T).prod (selfDualHaarAt ℚ p)) := by
    refine h1.of_forall_diff_eq_zero (hTm.prod MeasurableSet.univ) ?_
    rintro ⟨t, x⟩ ⟨⟨ht, -⟩, hq⟩
    exact hsupp t x fun hx => hq ⟨ht, hx⟩
  have h3 : Integrable (Function.uncurry F)
      (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).restrict T).prod (selfDualHaarAt ℚ p)) := by
    have hre : ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).restrict T).restrict T =
        (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).restrict T := by
      rw [Measure.restrict_restrict hTm, Set.inter_self]
    rw [IntegrableOn, ← Measure.restrict_prod_eq_prod_univ, hre] at h2
    exact h2
  exact MeasureTheory.integral_integral_swap h3

end Ws31.E4A
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31.E4S"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31.E4S"

end SupplyWA
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31.E4S"

section SupplyWB

namespace WBPairing

open NumberField.StandardAddChar

variable {p : HeightOneSpectrum (𝓞 ℚ)}

def wJ (p : HeightOneSpectrum (𝓞 ℚ)) : GL (Fin 2) (p.adicCompletion ℚ) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two_of])

theorem wJ_coe (p : HeightOneSpectrum (𝓞 ℚ)) : ((wJ p : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0] := rfl

theorem unipotent_coe' (x : p.adicCompletion ℚ) :
    ((unipotent x : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![1, x; 0, 1] := rfl

theorem diagUnitGL2_coe' (t : (p.adicCompletion ℚ)ˣ) :
    ((diagUnitGL2 t : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![(t : p.adicCompletion ℚ), 0; 0, 1] := rfl

theorem scalar2_coe (u : (p.adicCompletion ℚ)ˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
      !![(u : p.adicCompletion ℚ), 0; 0, (u : p.adicCompletion ℚ)] := by
  show Matrix.scalar (Fin 2) (u : p.adicCompletion ℚ) = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar]

theorem cell_identity (w₀p : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (t : (p.adicCompletion ℚ)ˣ) (x : p.adicCompletion ℚ) :
    w₀p * diagUnitGL2 t * unipotent x =
      Matrix.GeneralLinearGroup.scalar (Fin 2) t * (diagUnitGL2 t⁻¹ * wJ p * (diagUnitGL2 (-1) * unipotent x)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, hw₀p,
    diagUnitGL2_coe', diagUnitGL2_coe', diagUnitGL2_coe', unipotent_coe', wJ_coe, scalar2_coe,
    Units.val_inv_eq_inv_val, Units.val_neg, Units.val_one]
  have ht : (t : p.adicCompletion ℚ) ≠ 0 := t.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem det_diagUnitGL2 (t : (p.adicCompletion ℚ)ˣ) : Matrix.GeneralLinearGroup.det (diagUnitGL2 t) = t := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, diagUnitGL2_coe', Matrix.det_fin_two_of]
  simp

theorem det_unipotent' (z : p.adicCompletion ℚ) :
    Matrix.GeneralLinearGroup.det (unipotent z : GL (Fin 2) (p.adicCompletion ℚ)) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotent_coe', Matrix.det_fin_two_of]
  simp

theorem det_wJ : Matrix.GeneralLinearGroup.det (wJ p) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, wJ_coe, Matrix.det_fin_two_of]
  simp

theorem det_unipotent_mul (z : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    Matrix.GeneralLinearGroup.det (unipotent z * g) = Matrix.GeneralLinearGroup.det g := by
  rw [map_mul, det_unipotent', one_mul]

theorem det_cell (t : (p.adicCompletion ℚ)ˣ) (x : p.adicCompletion ℚ) :
    Matrix.GeneralLinearGroup.det (diagUnitGL2 t⁻¹ * wJ p * (diagUnitGL2 (-1) * unipotent x)) = -t⁻¹ := by
  rw [map_mul, map_mul, map_mul, det_diagUnitGL2, det_wJ, det_diagUnitGL2, det_unipotent', mul_one, mul_one,
    mul_neg_one]

theorem diagOne_eq_diagUnitGL2 (y : (p.adicCompletion ℚ)ˣ) : NumberField.AdelicLevel.diagOne y = diagUnitGL2 y := by
  apply Units.ext
  rw [diagUnitGL2_coe']
  ext i j
  rw [NumberField.AdelicLevel.diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem diagUnitGL2_mul_negOne_mul_unipotent (y : (p.adicCompletion ℚ)ˣ) (x : p.adicCompletion ℚ) :
    diagUnitGL2 y * (diagUnitGL2 (-1) * unipotent x) = unipotent (-((y : p.adicCompletion ℚ) * x)) * diagUnitGL2 (-y) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, diagUnitGL2_coe', diagUnitGL2_coe', diagUnitGL2_coe', unipotent_coe',
    unipotent_coe', Units.val_neg, Units.val_neg, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem continuous_of_open_stabilizer (W : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hW : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) :
    Continuous W := by
  obtain ⟨U, hU, hinv⟩ := hW
  refine continuous_def.2 fun s _ => ?_
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun k => g * k) '' (U : Set (GL (Fin 2) (p.adicCompletion ℚ))), ?_, ?_, ⟨1, U.one_mem, mul_one g⟩⟩
  · rintro _ ⟨k, hk, rfl⟩
    show W (g * k) ∈ s
    rw [hinv k hk g]; exact hg
  · exact (Homeomorph.mulLeft g).isOpenMap _ hU

theorem continuous_of_open_stabilizer' {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (F : G → ℂ) (hF : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, F (g * k) = F g) :
    Continuous F := by
  obtain ⟨U, hU, hinv⟩ := hF
  refine continuous_def.2 fun s _ => ?_
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun k => g * k) '' (U : Set G), ?_, ?_, ⟨1, U.one_mem, mul_one g⟩⟩
  · rintro _ ⟨k, hk, rfl⟩
    show F (g * k) ∈ s
    rw [hinv k hk g]; exact hg
  · exact (Homeomorph.mulLeft g).isOpenMap _ hU

theorem unipotent_inv' (x : p.adicCompletion ℚ) : (unipotent x : GL (Fin 2) (p.adicCompletion ℚ))⁻¹ = unipotent (-x) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv]
  apply Units.ext
  rw [Units.val_mul, unipotent_coe', unipotent_coe', Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem continuous_unipotent : Continuous (fun x : p.adicCompletion ℚ => (unipotent x : GL (Fin 2) (p.adicCompletion ℚ))) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun x : p.adicCompletion ℚ => ((unipotent x : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
    simp only [unipotent_coe']
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_id
  · show Continuous fun x : p.adicCompletion ℚ => (((unipotent x : GL (Fin 2) (p.adicCompletion ℚ))⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
    simp only [unipotent_inv', unipotent_coe']
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_neg

theorem continuous_diagUnitGL2 : Continuous (fun t : (p.adicCompletion ℚ)ˣ => (diagUnitGL2 t : GL (Fin 2) (p.adicCompletion ℚ))) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun t : (p.adicCompletion ℚ)ˣ => ((diagUnitGL2 t : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
    simp only [diagUnitGL2_coe']
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact Units.continuous_val
  · show Continuous fun t : (p.adicCompletion ℚ)ˣ => (((diagUnitGL2 t : GL (Fin 2) (p.adicCompletion ℚ))⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
    have h : ∀ t : (p.adicCompletion ℚ)ˣ, (((diagUnitGL2 t : GL (Fin 2) (p.adicCompletion ℚ))⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
        !![((t⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ), 0; 0, 1] := fun t => rfl
    simp only [h]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | (simp_rw [← Units.val_inv_eq_inv_val]; exact @Units.continuous_coe_inv (p.adicCompletion ℚ) _ _) | exact @Units.continuous_coe_inv (p.adicCompletion ℚ) _ _

theorem continuous_cell (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) :
    Continuous fun q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ => w₀p * diagUnitGL2 q.1 * unipotent q.2 :=
  (continuous_const.mul (continuous_diagUnitGL2.comp continuous_fst)).mul (continuous_unipotent.comp continuous_snd)

theorem continuous_psiLocal_units_mul :
    Continuous fun q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ =>
      (psiLocal ℚ p (-((q.1 : p.adicCompletion ℚ) * q.2)) : ℂ) :=
  (continuous_psiLocal ℚ p).comp ((Units.continuous_val.comp continuous_fst).mul continuous_snd).neg

theorem isOpen_ball' (m : ℤ) : IsOpen {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp m} := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer ℚ p
  set ϖ : p.adicCompletion ℚ := ((WithVal.equiv (HeightOneSpectrum.valuation ℚ p)).symm π : p.adicCompletion ℚ) with hϖdef
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
    rw [hϖdef, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ
  have hϖ0 : ϖ ≠ 0 := by intro h; rw [h, Valuation.map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hzpow : ∀ j : ℤ, Valued.v (ϖ ^ j) = WithZero.exp (-j) := by
    intro j; rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]
  have hset : {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp m} =
      (fun x => ϖ ^ m * x) ⁻¹' (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, hzpow, WithZero.exp_neg]
    constructor
    · intro h
      calc (WithZero.exp m)⁻¹ * Valued.v x ≤ (WithZero.exp m)⁻¹ * WithZero.exp m :=
            mul_le_mul_right h _
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
    · intro h
      calc Valued.v x = WithZero.exp m * ((WithZero.exp m)⁻¹ * Valued.v x) := by
            rw [← mul_assoc, mul_inv_cancel₀ WithZero.exp_ne_zero, one_mul]
        _ ≤ WithZero.exp m * 1 := mul_le_mul_right h _
        _ = WithZero.exp m := mul_one _
  rw [hset]
  exact (Valued.isOpen_valuationSubring _).preimage (continuous_const_mul _)

def higherUnitsSubgroup (p : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (hn : 1 ≤ n) : Subgroup (p.adicCompletion ℚ)ˣ where
  carrier := {u | Valued.v ((u : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(n : ℤ))}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have hlt : WithZero.exp (-(n : ℤ)) < 1 := by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have hva : Valued.v (a : p.adicCompletion ℚ) = 1 := by
      have : (a : p.adicCompletion ℚ) = 1 + ((a : p.adicCompletion ℚ) - 1) := by ring
      rw [this]; exact Valuation.map_one_add_of_lt _ (ha.trans_lt hlt)
    have e : ((a * b : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) - 1 =
        (a : p.adicCompletion ℚ) * ((b : p.adicCompletion ℚ) - 1) + ((a : p.adicCompletion ℚ) - 1) := by
      rw [Units.val_mul]; ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ha)
    rw [Valuation.map_mul, hva, one_mul]; exact hb
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have hlt : WithZero.exp (-(n : ℤ)) < 1 := by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have hva : Valued.v (a : p.adicCompletion ℚ) = 1 := by
      have : (a : p.adicCompletion ℚ) = 1 + ((a : p.adicCompletion ℚ) - 1) := by ring
      rw [this]; exact Valuation.map_one_add_of_lt _ (ha.trans_lt hlt)
    have e : ((a⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) - 1 =
        ((a⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * (-((a : p.adicCompletion ℚ) - 1)) := by
      rw [Units.val_inv_eq_inv_val]; field_simp; ring
    rw [e, Valuation.map_mul, Valuation.map_neg, Units.val_inv_eq_inv_val, map_inv₀, hva, inv_one, one_mul]
    exact ha

theorem mem_higherUnitsSubgroup_iff (n : ℕ) (hn : 1 ≤ n) (u : (p.adicCompletion ℚ)ˣ) :
    u ∈ higherUnitsSubgroup p n hn ↔ Valued.v ((u : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(n : ℤ)) := Iff.rfl

theorem isOpen_higherUnitsSubgroup (n : ℕ) (hn : 1 ≤ n) :
    IsOpen (higherUnitsSubgroup p n hn : Set (p.adicCompletion ℚ)ˣ) := by
  have hset : (higherUnitsSubgroup p n hn : Set (p.adicCompletion ℚ)ˣ) =
      (fun u : (p.adicCompletion ℚ)ˣ => (u : p.adicCompletion ℚ) - 1) ⁻¹' {x | Valued.v x ≤ WithZero.exp (-(n : ℤ))} := rfl
  rw [hset]
  exact (isOpen_ball' (-(n : ℤ))).preimage (Units.continuous_val.sub continuous_const)

theorem mem_higherUnitsAt_of_mem_higherUnitsSubgroup {n m : ℕ} (hn : 1 ≤ n) (hmn : m ≤ n) {u : (p.adicCompletion ℚ)ˣ}
    (hu : u ∈ higherUnitsSubgroup p n hn) : u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p m := by
  have hu' : Valued.v ((u : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(n : ℤ)) := hu
  have hlt : WithZero.exp (-(n : ℤ)) < 1 := by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hva : Valued.v (u : p.adicCompletion ℚ) = 1 := by
    have : (u : p.adicCompletion ℚ) = 1 + ((u : p.adicCompletion ℚ) - 1) := by ring
    rw [this]; exact Valuation.map_one_add_of_lt _ (hu'.trans_lt hlt)
  refine ⟨hva, Or.inr (hu'.trans ?_)⟩
  rw [WithZero.exp_le_exp]; omega

theorem continuous_charExt_units (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (m : ℕ)
    (hχ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p m, χ u = 1) :
    Continuous fun t : (p.adicCompletion ℚ)ˣ => ((χ t : ℂˣ) : ℂ) := by
  have h1 : 1 ≤ max m 1 := le_max_right _ _
  refine continuous_of_open_stabilizer' (G := (p.adicCompletion ℚ)ˣ) _
    ⟨higherUnitsSubgroup p (max m 1) h1, isOpen_higherUnitsSubgroup _ h1, fun k hk g => ?_⟩
  rw [map_mul, hχ k (mem_higherUnitsAt_of_mem_higherUnitsSubgroup h1 (le_max_left _ _) hk), mul_one]

end WBPairing
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31.E4S"

namespace WBPairingInv

open NumberField.StandardAddChar

variable {p : HeightOneSpectrum (𝓞 ℚ)}

theorem selfDualHaarAt_eq (p : HeightOneSpectrum (𝓞 ℚ)) :
    selfDualHaarAt ℚ p = @Measure.addHaarMeasure (p.adicCompletion ℚ) _ _ _ (localBorel ℚ p)
      (borelSpace_localBorel ℚ p) (integersPositiveCompacts ℚ p) := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  unfold selfDualHaarAt
  rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p]
  simp

private theorem _root_.WBPairingInv.isAddHaarMeasure_selfDualHaarAt (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localBorel ℚ p
    (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  rw [selfDualHaarAt_eq p]
  infer_instance

p2m_export "WBPairingInv" "isAddHaarMeasure_selfDualHaarAt"

theorem borelSpace_units (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localBorel ℚ p
    BorelSpace (p.adicCompletion ℚ)ˣ := by
  letI := localBorel ℚ p
  refine ⟨?_⟩
  show MeasurableSpace.comap Units.val (borel (p.adicCompletion ℚ)) = borel (p.adicCompletion ℚ)ˣ
  rw [← borel_comap]
  congr 1
  exact (Units.isEmbedding_val₀ (G₀ := p.adicCompletion ℚ)).eq_induced.symm

theorem secondCountableTopology_units (p : HeightOneSpectrum (𝓞 ℚ)) :
    SecondCountableTopology (p.adicCompletion ℚ)ˣ :=
  (Units.isEmbedding_val₀ (G₀ := p.adicCompletion ℚ)).isInducing.secondCountableTopology

theorem isOpenEmbedding_units_val (p : HeightOneSpectrum (𝓞 ℚ)) :
    Topology.IsOpenEmbedding (Units.val : (p.adicCompletion ℚ)ˣ → p.adicCompletion ℚ) := by
  refine ⟨Units.isEmbedding_val₀, ?_⟩
  have : Set.range (Units.val : (p.adicCompletion ℚ)ˣ → p.adicCompletion ℚ) = {x | x ≠ 0} := by
    ext x
    simp only [Set.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, rfl⟩; exact u.ne_zero
    · intro hx; exact ⟨Units.mk0 x hx, rfl⟩
  rw [this]
  exact isOpen_ne

theorem locallyCompactSpace_units (p : HeightOneSpectrum (𝓞 ℚ)) :
    LocallyCompactSpace (p.adicCompletion ℚ)ˣ :=
  (isOpenEmbedding_units_val p).locallyCompactSpace

theorem isInvInvariant_tau (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localBorel ℚ p
    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (p.adicCompletion ℚ)ˣ).IsHaarMeasure ∧
    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (p.adicCompletion ℚ)ˣ).IsInvInvariant := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI := isAddHaarMeasure_selfDualHaarAt p
  haveI := borelSpace_units p
  haveI := secondCountableTopology_units p
  haveI := locallyCompactSpace_units p
  haveI hH : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (p.adicCompletion ℚ)ˣ).IsHaarMeasure :=
    LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ p (selfDualHaarAt ℚ p)
  exact ⟨hH, MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant _⟩

theorem setIntegral_unitShell_comp_inv (f : (p.adicCompletion ℚ)ˣ → ℂ) :
    letI := localBorel ℚ p
    (∫ t in {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = 1}, f t⁻¹
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
      ∫ t in {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = 1}, f t
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by
  letI := localBorel ℚ p
  haveI := borelSpace_units p
  haveI := (isInvInvariant_tau p).2
  have hmp := Measure.measurePreserving_inv
    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (p.adicCompletion ℚ)ˣ)
  have hemb : MeasurableEmbedding (Inv.inv : (p.adicCompletion ℚ)ˣ → (p.adicCompletion ℚ)ˣ) :=
    (MeasurableEquiv.inv (p.adicCompletion ℚ)ˣ).measurableEmbedding
  have h := hmp.setIntegral_preimage_emb hemb f {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = 1}
  have hS : (Inv.inv : (p.adicCompletion ℚ)ˣ → (p.adicCompletion ℚ)ˣ) ⁻¹'
      {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = 1} =
      {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = 1} := by
    ext t
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Units.val_inv_eq_inv_val, map_inv₀, inv_eq_one]
  rw [hS] at h
  exact h

end WBPairingInv
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31.E4S"

end SupplyWB
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31.E4S"

section SupplyE3

namespace E3SupplyForPS

open NumberField.StandardAddChar

private theorem _root_.E3SupplyForPS.measurableSet_shell {p : HeightOneSpectrum (𝓞 ℚ)} (k : ℤ) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ p
    MeasurableSet {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp k} := by
  have h := (LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p).1 (-k)
  rwa [neg_neg] at h

p2m_export "E3SupplyForPS" "measurableSet_shell"

theorem shell_pos_lt_top {p : HeightOneSpectrum (𝓞 ℚ)} (k : ℤ) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ p
    0 < (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
        {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp k} ∧
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
        {t | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp k} < ⊤ := by
  have h := ((LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p).2.2.1 (-k)).2
  rwa [neg_neg] at h

theorem integral_char_mul_psiLocal_neg_mul_tateFourier_eq {p : HeightOneSpectrum (𝓞 ℚ)}
    (φ₁ : p.adicCompletion ℚ → ℂ) (hφ₁ : IsSchwartzBruhat φ₁)
    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ) (y : (p.adicCompletion ℚ)ˣ) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ p
    (∫ x, ((ω y : ℂˣ) : ℂ) * (psiLocal ℚ p (-((y : p.adicCompletion ℚ) * x)) : ℂ) *
        tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) φ₁ x ∂(selfDualHaarAt ℚ p)) =
      ((ω y : ℂˣ) : ℂ) * φ₁ (y : p.adicCompletion ℚ) := by
  letI := LanglandsTunnell.TateLocal.localBorel ℚ p
  have hFF := LanglandsTunnell.TateLocal.tateFourier_tateFourier_psiLocal_selfDualHaarAt_rat p φ₁ hφ₁
    (-(y : p.adicCompletion ℚ))
  rw [neg_neg] at hFF
  rw [← hFF, tateFourier]
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [show -((y : p.adicCompletion ℚ) * x) = x * (-(y : p.adicCompletion ℚ)) by ring]
  ring

end E3SupplyForPS
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31.E4S"

end SupplyE3
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31.E4S"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31.E4S"

noncomputable section

namespace PSPairing

open NumberField.StandardAddChar

variable {p : HeightOneSpectrum (𝓞 ℚ)}

def wJ (p : HeightOneSpectrum (𝓞 ℚ)) : GL (Fin 2) (p.adicCompletion ℚ) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two_of])

theorem wJ_coe (p : HeightOneSpectrum (𝓞 ℚ)) : ((wJ p : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0] := rfl

private theorem _root_.PSPairing.cell_identity (w₀p : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (t : (p.adicCompletion ℚ)ˣ) (x : p.adicCompletion ℚ) :
    w₀p * diagUnitGL2 t * unipotent x =
      Matrix.GeneralLinearGroup.scalar (Fin 2) t * (diagUnitGL2 t⁻¹ * wJ p * (diagUnitGL2 (-1) * unipotent x)) := by
  exact WBPairing.cell_identity w₀p hw₀p t x

p2m_export "PSPairing" "cell_identity"
private theorem _root_.PSPairing.det_cell (t : (p.adicCompletion ℚ)ˣ) (x : p.adicCompletion ℚ) :
    Matrix.GeneralLinearGroup.det (diagUnitGL2 t⁻¹ * wJ p * (diagUnitGL2 (-1) * unipotent x)) = -t⁻¹ :=
  WBPairing.det_cell t x

p2m_export "PSPairing" "det_cell"
private theorem _root_.PSPairing.det_diagUnitGL2 (t : (p.adicCompletion ℚ)ˣ) : Matrix.GeneralLinearGroup.det (diagUnitGL2 t) = t :=
  WBPairing.det_diagUnitGL2 t

p2m_export "PSPairing" "det_diagUnitGL2"
private theorem _root_.PSPairing.det_unipotent_mul (z : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    Matrix.GeneralLinearGroup.det (unipotent z * g) = Matrix.GeneralLinearGroup.det g :=
  WBPairing.det_unipotent_mul z g

p2m_export "PSPairing" "det_unipotent_mul"
private theorem _root_.PSPairing.diagOne_eq_diagUnitGL2 (y : (p.adicCompletion ℚ)ˣ) : NumberField.AdelicLevel.diagOne y = diagUnitGL2 y :=
  WBPairing.diagOne_eq_diagUnitGL2 y

p2m_export "PSPairing" "diagOne_eq_diagUnitGL2"
private theorem _root_.PSPairing.diagUnitGL2_mul_negOne_mul_unipotent (y : (p.adicCompletion ℚ)ˣ) (x : p.adicCompletion ℚ) :
    diagUnitGL2 y * (diagUnitGL2 (-1) * unipotent x) = unipotent (-((y : p.adicCompletion ℚ) * x)) * diagUnitGL2 (-y) :=
  WBPairing.diagUnitGL2_mul_negOne_mul_unipotent y x

p2m_export "PSPairing" "diagUnitGL2_mul_negOne_mul_unipotent"

private theorem _root_.PSPairing.setIntegral_unitShell_comp_inv (f : (p.adicCompletion ℚ)ˣ → ℂ) :
    letI := localBorel ℚ p
    (∫ t in {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = 1}, f t⁻¹
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
      ∫ t in {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = 1}, f t
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) :=
  WBPairingInv.setIntegral_unitShell_comp_inv f

p2m_export "PSPairing" "setIntegral_unitShell_comp_inv"

private theorem _root_.PSPairing.setIntegral_integral_swap (T : Set (p.adicCompletion ℚ)ˣ) (n : ℤ)
    (hT : T = {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp n})
    (F : (p.adicCompletion ℚ)ˣ → p.adicCompletion ℚ → ℂ)
    (hF : Continuous fun q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ => F q.1 q.2)
    (Kc : Set (p.adicCompletion ℚ)) (hKc : IsCompact Kc) (hsupp : ∀ t x, x ∉ Kc → F t x = 0) :
    letI := localBorel ℚ p
    (∫ t in T, (∫ x, F t x ∂(selfDualHaarAt ℚ p)) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
      ∫ x, (∫ t in T, F t x ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∂(selfDualHaarAt ℚ p) :=
  Ws31.E4A.setIntegral_integral_swap T n hT F hF Kc hKc hsupp

p2m_export "PSPairing" "setIntegral_integral_swap"

private theorem _root_.PSPairing.continuous_of_open_stabilizer (W : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hW : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) :
    Continuous W :=
  WBPairing.continuous_of_open_stabilizer W hW

p2m_export "PSPairing" "continuous_of_open_stabilizer"
private theorem _root_.PSPairing.continuous_charExt_units (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (m : ℕ)
    (hχ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p m, χ u = 1) :
    Continuous fun t : (p.adicCompletion ℚ)ˣ => ((χ t : ℂˣ) : ℂ) :=
  WBPairing.continuous_charExt_units χ m hχ

p2m_export "PSPairing" "continuous_charExt_units"
private theorem _root_.PSPairing.continuous_cell (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) :
    Continuous fun q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ => w₀p * diagUnitGL2 q.1 * unipotent q.2 :=
  WBPairing.continuous_cell w₀p

p2m_export "PSPairing" "continuous_cell"
private theorem _root_.PSPairing.continuous_psiLocal_units_mul :
    Continuous fun q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ =>
      (psiLocal ℚ p (-((q.1 : p.adicCompletion ℚ) * q.2)) : ℂ) :=
  WBPairing.continuous_psiLocal_units_mul

p2m_export "PSPairing" "continuous_psiLocal_units_mul"
end PSPairing
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31.E4S"

namespace PSPairing
open NumberField.StandardAddChar

variable {p : HeightOneSpectrum (𝓞 ℚ)}

theorem translate_mem_span (w₂base w' : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (m : GL (Fin 2) (p.adicCompletion ℚ))
    (hw' : w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h))) :
    (fun g => w' (g * m)) ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) := by
  refine Submodule.span_induction (p := fun w _ => (fun g => w (g * m)) ∈ Submodule.span ℂ
    (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h))) ?_ ?_ ?_ ?_ hw'
  · rintro _ ⟨h, rfl⟩
    refine Submodule.subset_span ⟨m * h, ?_⟩
    funext g; simp only [mul_assoc]
  · show (fun g => (0 : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (g * m)) ∈ _
    have h0 : (fun g => (0 : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (g * m)) = 0 := rfl
    rw [h0]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    have : (fun g => (a + b) (g * m)) = (fun g => a (g * m)) + (fun g => b (g * m)) := by funext g; rfl
    rw [this]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    have : (fun g => (c • a) (g * m)) = c • (fun g => a (g * m)) := by funext g; rfl
    rw [this]; exact Submodule.smul_mem _ c ha

theorem law_of_twisted_law (χ ξ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (w' : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
          ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (unipotent x * g) =
        psiLocal ℚ p x *
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) g)
    (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    w' (unipotent x * g) = psiLocal ℚ p x * w' g := by
  have h := hlaw x g
  simp only [det_unipotent_mul] at h
  have hne : ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (inv_ne_zero (Units.ne_zero _))
  have h' : (((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹) *
      w' (unipotent x * g) =
      (((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹) *
      (psiLocal ℚ p x * w' g) := by
    rw [h]; ring
  exact mul_left_cancel₀ hne h'

theorem integrand_eq (χ ξ ω θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (w' : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hcen : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
          ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) =
        (((θ₀ * (χ * ξ⁻¹) ^ 2) z : ℂˣ) : ℂ) *
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) g)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (t : (p.adicCompletion ℚ)ˣ) (x : p.adicCompletion ℚ) :
    ((ω t : ℂˣ) : ℂ) *
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
          ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (w₀p * diagUnitGL2 t * unipotent x) =
    (((χ * ξ⁻¹) (-1) : ℂˣ) : ℂ) *
      ((fun g => w' (g * (diagUnitGL2 (-1) * unipotent x))) (diagUnitGL2 t⁻¹ * wJ p) *
        ((((ω * (χ * ξ⁻¹)) t⁻¹ : ℂˣ) : ℂ))⁻¹ * (((θ₀ t⁻¹ : ℂˣ) : ℂ))⁻¹) := by
  rw [cell_identity w₀p hw₀p t x, hcen]
  beta_reduce
  rw [det_cell t x]
  have e1 : (-t⁻¹ : (p.adicCompletion ℚ)ˣ) = -1 * t⁻¹ := by rw [neg_one_mul]
  rw [e1]
  simp only [map_mul, map_inv, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_mul,
    Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, mul_inv, inv_inv]
  field_simp

theorem shell_integrand_eq (χ ξ ω : (p.adicCompletion ℚ)ˣ →* ℂˣ) (w' : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (kp : ℕ) (c₀ : ℂ)
    (hlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
          ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (unipotent x * g) =
        psiLocal ℚ p x *
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) g)
    (hK : ∀ y : (p.adicCompletion ℚ)ˣ,
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (diagUnitGL2 y) =
          if Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (((2 * kp : ℕ)) : ℤ) then c₀ else 0)
    (x : p.adicCompletion ℚ) (y : (p.adicCompletion ℚ)ˣ)
    (hy : Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (((2 * kp : ℕ)) : ℤ)) :
    (fun g => w' (g * (diagUnitGL2 (-1) * unipotent x))) (NumberField.AdelicLevel.diagOne y) * (((ω * (χ * ξ⁻¹)) y : ℂˣ) : ℂ) =
      c₀ * ((((χ * ξ⁻¹) (-1) : ℂˣ) : ℂ))⁻¹ * ((psiLocal ℚ p (-((y : p.adicCompletion ℚ) * x)) : ℂ) * ((ω y : ℂˣ) : ℂ)) := by
  have hKy := hK (-y)
  simp only [det_diagUnitGL2, Units.val_neg, Valuation.map_neg, hy, if_true] at hKy

  have hne : ((χ (-y) : ℂˣ) : ℂ) * ((ξ (-y) : ℂˣ) : ℂ)⁻¹ ≠ 0 := mul_ne_zero (Units.ne_zero _) (inv_ne_zero (Units.ne_zero _))
  have hw : w' (diagUnitGL2 (-y)) = (((χ (-y) : ℂˣ) : ℂ) * ((ξ (-y) : ℂˣ) : ℂ)⁻¹)⁻¹ * c₀ := by
    rw [← hKy]; field_simp
  show w' (NumberField.AdelicLevel.diagOne y * (diagUnitGL2 (-1) * unipotent x)) * _ = _
  rw [diagOne_eq_diagUnitGL2, diagUnitGL2_mul_negOne_mul_unipotent, law_of_twisted_law χ ξ w' hlaw, hw]
  have e1 : (-y : (p.adicCompletion ℚ)ˣ) = -1 * y := by rw [neg_one_mul]
  simp only [e1, map_mul, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, mul_inv, inv_inv]
  field_simp

end PSPairing
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31.E4S"

namespace PSPairing
open NumberField.StandardAddChar
variable {p : HeightOneSpectrum (𝓞 ℚ)}

private theorem _root_.PSPairing.setIntegral_shell_const (k : ℤ) (c : ℂ) :
    letI := localBorel ℚ p
    (∫ t in {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp k}, c
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
      c * ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
        {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp k}).toReal ∧
    ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
        {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp k}).toReal ≠ 0 :=
  Ws31.E4A.setIntegral_shell_const k c

p2m_export "PSPairing" "setIntegral_shell_const"
private theorem _root_.PSPairing.integral_char_mul_psiLocal_neg_mul_tateFourier_eq (φ₁ : p.adicCompletion ℚ → ℂ) (hφ₁ : IsSchwartzBruhat φ₁)
    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ) (y : (p.adicCompletion ℚ)ˣ) :
    letI := localBorel ℚ p
    (∫ x, ((ω y : ℂˣ) : ℂ) * (psiLocal ℚ p (-((y : p.adicCompletion ℚ) * x)) : ℂ) *
        tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) φ₁ x ∂(selfDualHaarAt ℚ p)) =
      ((ω y : ℂˣ) : ℂ) * φ₁ (y : p.adicCompletion ℚ) :=
  E3SupplyForPS.integral_char_mul_psiLocal_neg_mul_tateFourier_eq φ₁ hφ₁ ω y

p2m_export "PSPairing" "integral_char_mul_psiLocal_neg_mul_tateFourier_eq"
end PSPairing
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31.E4S"

namespace PSPairing
open NumberField.StandardAddChar

variable {p : HeightOneSpectrum (𝓞 ℚ)}

theorem hasConductorExponentAt_mul_of_trivial (χ₁ ν₁ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (a b : ℕ)
    (h₁ : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p χ₁ a)
    (hν : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p b, ν₁ u = 1) (hb : b < a) :
    LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (χ₁ * ν₁) a := by
  constructor
  · intro u hu
    have huB := LanglandsTunnell.TateLocal.higherUnitsAt_antitone ℚ p hb.le hu
    simp [MonoidHom.mul_apply, h₁.1 u hu, hν u huB]
  · intro m hm
    obtain ⟨u, hu, hne⟩ := h₁.2 (max m b) (max_lt hm hb)
    have huB := LanglandsTunnell.TateLocal.higherUnitsAt_antitone ℚ p (le_max_right m b) hu
    refine ⟨u, LanglandsTunnell.TateLocal.higherUnitsAt_antitone ℚ p (le_max_left m b) hu, ?_⟩
    simpa [MonoidHom.mul_apply, hν u huB] using hne

private theorem _root_.PSPairing.measurableSet_shell (k : ℤ) :
    letI := localBorel ℚ p
    MeasurableSet {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp k} :=
  E3SupplyForPS.measurableSet_shell k

p2m_export "PSPairing" "measurableSet_shell"
private theorem _root_.PSPairing.shell_pos_lt_top (k : ℤ) :
    letI := localBorel ℚ p
    0 < (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
        {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp k} ∧
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
        {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp k} < ⊤ :=
  E3SupplyForPS.shell_pos_lt_top k

p2m_export "PSPairing" "shell_pos_lt_top"
end PSPairing
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31.E4S"

open PSPairing PSKernelsBody NumberField.StandardAddChar in
set_option maxHeartbeats 3200000 in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1)
    (kp : ℕ) (hkp : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p χ kp)
    (ξ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hξu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((ξ x : ℂˣ) : ℂ)‖ = 1)
    (B : ℕ) (hξB : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p ξ B)
    (f : ℕ)
    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hωu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((ω x : ℂˣ) : ℂ)‖ = 1)
    (hωf : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p f, ω u = 1)
    (hωB : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p B, ω u = 1)
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hθu : ∀ z : (p.adicCompletion ℚ)ˣ, ‖((θ₀ z : ℂˣ) : ℂ)‖ = 1)
    (b : ℕ) (hcθ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p b, θ₀ u = 1)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (hNb : p.asIdeal ^ b ∣ N ∧ ¬ p.asIdeal ^ (b + 1) ∣ N)
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
    (hBk : B < kp) (hfk : f ≤ kp) (hbk : 2 * b + 1 ≤ kp)

    (w' : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw'V : w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)))
    (c₀ : ℂ) (hc₀ : c₀ ≠ 0)
    (hK : ∀ y : (p.adicCompletion ℚ)ˣ,
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (diagUnitGL2 y) =
          if Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (((2 * kp : ℕ)) : ℤ) then c₀ else 0)
    (hreg :

      (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (unipotent x * g) =
          NumberField.StandardAddChar.psiLocal ℚ p x *
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
              ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) g) ∧
      (∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) =
          (((θ₀ * (χ * ξ⁻¹) ^ 2) z : ℂˣ) : ℂ) *
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
              ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) g) ∧
      (∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
        ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (g * k) =
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) g) )

    (φ₁ : p.adicCompletion ℚ → ℂ)
    (hφ₁def : φ₁ = (fun y : p.adicCompletion ℚ =>
        if Valued.v y = WithZero.exp (((2 * kp : ℕ)) : ℤ) then
          charExt ω⁻¹ (y * ((NumberField.AdelicLevel.uniformizerUnit ℚ p ^ (2 * kp) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ))
        else 0)) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ p;
      (∫ t in {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = 1},
          ((ω t : ℂˣ) : ℂ) *
            (∫ x : p.adicCompletion ℚ,
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
                    ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (w₀p * diagUnitGL2 t * unipotent x) *
                  tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ (-x) ∂(selfDualHaarAt ℚ p))
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ≠ 0 := by
  classical
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI := isAddHaarMeasure_selfDualHaarAt p
  obtain ⟨hlaw, hcen, hsm⟩ := hreg
  subst hφ₁def

  set Wsh : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun g => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
      ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g with hWsh
  set ϖ : (p.adicCompletion ℚ)ˣ := NumberField.AdelicLevel.uniformizerUnit ℚ p with hϖ
  have hφ₁eq : (fun y : p.adicCompletion ℚ =>
        if Valued.v y = WithZero.exp (((2 * kp : ℕ)) : ℤ) then
          charExt ω⁻¹ (y * ((NumberField.AdelicLevel.uniformizerUnit ℚ p ^ (2 * kp) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ))
        else 0) = shellFn ω⁻¹ (ϖ ^ (2 * kp)) (((2 * kp : ℕ)) : ℤ) := by
    funext y; simp only [shellFn, hϖ]
  rw [hφ₁eq]
  set φ₁ : p.adicCompletion ℚ → ℂ := shellFn ω⁻¹ (ϖ ^ (2 * kp)) (((2 * kp : ℕ)) : ℤ) with hφ₁
  set G : p.adicCompletion ℚ → ℂ := tateFourier (psiLocal ℚ p) (selfDualHaarAt ℚ p) φ₁ with hG

  have hkp1 : 1 ≤ kp := by omega
  set m : ℕ := max f 1 with hmdef
  have hm1 : 1 ≤ m := le_max_right _ _
  have hωm : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p m, ω u = 1 :=
    fun u hu => hωf u (LanglandsTunnell.TateLocal.higherUnitsAt_antitone ℚ p (le_max_left f 1) hu)
  have hωm' : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p m, ω⁻¹ u = 1 := by
    intro u hu; rw [MonoidHom.inv_apply, hωm u hu, inv_one]
  have hφ₁SB : IsSchwartzBruhat φ₁ := isSchwartzBruhat_shellFn ω⁻¹ _ _ hm1 hωm'
  obtain ⟨hψ0, hψ1⟩ := level_zero p
  have hGSB : IsSchwartzBruhat G :=
    LanglandsTunnell.TateLocal.isSchwartzBruhat_tateFourier ℚ p (selfDualHaarAt ℚ p) (psiLocal ℚ p) 0 hψ0 hψ1 φ₁ hφ₁SB
  have hgG : ∀ x : p.adicCompletion ℚ,
      tateFourier (psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ (-x) = G x := by
    intro x; rw [tateFourier_inv_apply, neg_neg]

  have hχ' : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (ω * (χ * ξ⁻¹)) kp := by
    have hcomm : ω * (χ * ξ⁻¹) = χ * (ω * ξ⁻¹) := mul_left_comm ω χ ξ⁻¹
    rw [hcomm]
    refine hasConductorExponentAt_mul_of_trivial χ (ω * ξ⁻¹) kp B hkp (fun u hu => ?_) hBk
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hωB u hu, hξB.1 u hu, inv_one, mul_one]
  have hχ'θ : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (ω * (χ * ξ⁻¹) * θ₀) kp :=
    hasConductorExponentAt_mul_of_trivial _ θ₀ kp b hχ' hcθ (by omega)
  have hnorm1 : ∀ z : (p.adicCompletion ℚ)ˣ, ‖(((ω * (χ * ξ⁻¹)) z : ℂˣ) : ℂ)‖ = 1 := by
    intro z
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv,
      hωu z, hχu z, hξu z]
    norm_num
  have hnorm2 : ∀ z : (p.adicCompletion ℚ)ˣ, ‖(((ω * (χ * ξ⁻¹) * θ₀) z : ℂˣ) : ℂ)‖ = 1 := by
    intro z
    rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hnorm1 z, hθu z, one_mul]
  have hε₁ : LanglandsTunnell.TateLocal.stdRootNumberAt ℚ p (ω * (χ * ξ⁻¹)) ≠ 0 :=
    LanglandsTunnell.TateLocal.stdRootNumberAt_ne_zero_of_hasConductorExponentAt ℚ p _ kp hkp1 hχ' (hnorm1 _)
  have hε₂ : LanglandsTunnell.TateLocal.stdRootNumberAt ℚ p (ω * (χ * ξ⁻¹) * θ₀) ≠ 0 :=
    LanglandsTunnell.TateLocal.stdRootNumberAt_ne_zero_of_hasConductorExponentAt ℚ p _ kp hkp1 hχ'θ (hnorm2 _)

  have hWcont : Continuous Wsh := continuous_of_open_stabilizer Wsh hsm
  have hωcont : Continuous fun t : (p.adicCompletion ℚ)ˣ => ((ω t : ℂˣ) : ℂ) := continuous_charExt_units ω m hωm
  have hGcont : Continuous G := hGSB.1.continuous
  have hKc : IsCompact (tsupport G) := hGSB.2
  have hGsupp : ∀ x, x ∉ tsupport G → G x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx

  set F₁ : (p.adicCompletion ℚ)ˣ → p.adicCompletion ℚ → ℂ := fun t x =>
    ((ω t : ℂˣ) : ℂ) * Wsh (w₀p * diagUnitGL2 t * unipotent x) * G x with hF₁
  have hF₁cont : Continuous fun q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ => F₁ q.1 q.2 := by
    simp only [hF₁]
    exact ((hωcont.comp continuous_fst).mul (hWcont.comp (continuous_cell w₀p))).mul (hGcont.comp continuous_snd)
  have hstep1 : (fun t : (p.adicCompletion ℚ)ˣ => ((ω t : ℂˣ) : ℂ) *
        ∫ x : p.adicCompletion ℚ, Wsh (w₀p * diagUnitGL2 t * unipotent x) *
          tateFourier (psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ (-x) ∂(selfDualHaarAt ℚ p)) =
      fun t => ∫ x, F₁ t x ∂(selfDualHaarAt ℚ p) := by
    funext t
    rw [← integral_const_mul]
    congr 1; funext x
    simp only [hF₁, hgG x]; ring

  have hUdef : ({t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = 1} : Set (p.adicCompletion ℚ)ˣ) =
      {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp (0 : ℤ)} := by
    rw [WithZero.exp_zero]
  have hUmeas : MeasurableSet ({t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = 1} : Set (p.adicCompletion ℚ)ˣ) := by
    rw [hUdef]; exact measurableSet_shell 0
  have hSmeas : MeasurableSet ({t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp (((2 * kp : ℕ)) : ℤ)} :
      Set (p.adicCompletion ℚ)ˣ) := measurableSet_shell _

  set wx : p.adicCompletion ℚ → GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun x g => w' (g * (diagUnitGL2 (-1) * unipotent x)) with hwx
  have hwxV : ∀ x, wx x ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) := fun x => translate_mem_span w₂base w' _ hw'V
  have hw₂Kb := LanglandsTunnell.RankinSelberg.forall_mem_localLevelOne_pow_mul_eq_of_forall_mem_localLevelOne_mul_eq p N w₂base hw₂K b hNb
  have hE4c1 := fun x =>
    AutomorphicForm.WhittakerModel.setIntegral_unitShell_diagOne_weyl_eq_stdRootNumberAt_mul_setIntegral_shell_of_admissible_of_le_of_norm_eq_one
      p w₂base hw₂law b (fun k hk g => hw₂Kb k g hk) hw₂ne hw₂irr hw₂adm θ₀ hcentral (hθu _) (ω * (χ * ξ⁻¹)) kp hχ'
      (hnorm1 _) hbk (wJ p) (wJ_coe p) (wx x) (hwxV x)
  have hinner : ∀ x : p.adicCompletion ℚ,
      (∫ t in {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = 1},
          ((ω t : ℂˣ) : ℂ) * Wsh (w₀p * diagUnitGL2 t * unipotent x) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
        LanglandsTunnell.TateLocal.stdRootNumberAt ℚ p (ω * (χ * ξ⁻¹) * θ₀) * LanglandsTunnell.TateLocal.stdRootNumberAt ℚ p (ω * (χ * ξ⁻¹)) *
          c₀ * ∫ y in {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp (((2 * kp : ℕ)) : ℤ)},
            ((psiLocal ℚ p (-((y : p.adicCompletion ℚ) * x)) : ℂ) * ((ω y : ℂˣ) : ℂ))
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by
    intro x

    have hpt : ∀ t : (p.adicCompletion ℚ)ˣ, ((ω t : ℂˣ) : ℂ) * Wsh (w₀p * diagUnitGL2 t * unipotent x) =
        (((χ * ξ⁻¹) (-1) : ℂˣ) : ℂ) * ((fun u : (p.adicCompletion ℚ)ˣ => wx x (diagUnitGL2 u * wJ p) *
          ((((ω * (χ * ξ⁻¹)) u : ℂˣ) : ℂ))⁻¹ * (((θ₀ u : ℂˣ) : ℂ))⁻¹) t⁻¹) := by
      intro t; simp only [hWsh, hwx]; exact integrand_eq χ ξ ω θ₀ w' hcen w₀p hw₀p t x
    simp_rw [hpt]
    have hinvU := setIntegral_unitShell_comp_inv (p := p) (fun u : (p.adicCompletion ℚ)ˣ => wx x (diagUnitGL2 u * wJ p) *
          ((((ω * (χ * ξ⁻¹)) u : ℂˣ) : ℂ))⁻¹ * (((θ₀ u : ℂˣ) : ℂ))⁻¹)
    beta_reduce at hinvU
    rw [integral_const_mul, hinvU]
    have hc1 := hE4c1 x
    simp_rw [diagOne_eq_diagUnitGL2] at hc1
    rw [hc1]

    have hshell : ∀ y ∈ {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp (((2 * kp : ℕ)) : ℤ)},
        wx x (diagUnitGL2 y) * (((ω * (χ * ξ⁻¹)) y : ℂˣ) : ℂ) =
          c₀ * ((((χ * ξ⁻¹) (-1) : ℂˣ) : ℂ))⁻¹ * ((psiLocal ℚ p (-((y : p.adicCompletion ℚ) * x)) : ℂ) * ((ω y : ℂˣ) : ℂ)) := by
      intro y hy
      have := shell_integrand_eq χ ξ ω w' kp c₀ hlaw hK x y hy
      rw [diagOne_eq_diagUnitGL2] at this
      simpa only [hwx] using this
    rw [setIntegral_congr_fun hSmeas hshell, integral_const_mul]
    set I := ∫ y in {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp (((2 * kp : ℕ)) : ℤ)},
            ((psiLocal ℚ p (-((y : p.adicCompletion ℚ) * x)) : ℂ) * ((ω y : ℂˣ) : ℂ))
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) with hI
    have hu : ((((χ * ξ⁻¹) (-1) : ℂˣ) : ℂ)) ≠ 0 := Units.ne_zero _
    field_simp

  set C : ℂ := LanglandsTunnell.TateLocal.stdRootNumberAt ℚ p (ω * (χ * ξ⁻¹) * θ₀) *
      LanglandsTunnell.TateLocal.stdRootNumberAt ℚ p (ω * (χ * ξ⁻¹)) * c₀ with hC
  set F₂ : (p.adicCompletion ℚ)ˣ → p.adicCompletion ℚ → ℂ := fun y x =>
    ((ω y : ℂˣ) : ℂ) * ((psiLocal ℚ p (-((y : p.adicCompletion ℚ) * x))) : ℂ) * G x with hF₂
  have hF₂cont : Continuous fun q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ => F₂ q.1 q.2 := by
    simp only [hF₂]
    exact ((hωcont.comp continuous_fst).mul continuous_psiLocal_units_mul).mul (hGcont.comp continuous_snd)
  have hF₁supp : ∀ t x, x ∉ tsupport G → F₁ t x = 0 := by
    intro t x hx; simp only [hF₁, hGsupp x hx, mul_zero]
  have hF₂supp : ∀ t x, x ∉ tsupport G → F₂ t x = 0 := by
    intro t x hx; simp only [hF₂, hGsupp x hx, mul_zero]
  have hmid : ∀ x : p.adicCompletion ℚ,
      (∫ t in {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = 1}, F₁ t x
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
      C * ∫ y in {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp (((2 * kp : ℕ)) : ℤ)}, F₂ y x
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by
    intro x
    simp only [hF₁, hF₂]
    rw [integral_mul_const, hinner x, hC, mul_assoc (_ * _ * c₀), ← integral_mul_const]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)

  have hfin : ∀ y : (p.adicCompletion ℚ)ˣ, (∫ x, F₂ y x ∂(selfDualHaarAt ℚ p)) = ((ω y : ℂˣ) : ℂ) * φ₁ (y : p.adicCompletion ℚ) := by
    intro y
    simp only [hF₂, hG]
    exact integral_char_mul_psiLocal_neg_mul_tateFourier_eq φ₁ hφ₁SB ω y
  have hshellval : ∀ y ∈ {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp (((2 * kp : ℕ)) : ℤ)},
      ((ω y : ℂˣ) : ℂ) * φ₁ (y : p.adicCompletion ℚ) = ((((ω (ϖ ^ (2 * kp)) : ℂˣ) : ℂ)))⁻¹ := by
    intro y hy
    rw [hφ₁, shellFn_of_eq ω⁻¹ (ϖ ^ (2 * kp)) _ hy, ← Units.val_mul, charExt_coe_units, MonoidHom.inv_apply, map_mul,
      mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, ← mul_assoc,
      mul_inv_cancel₀ (Units.ne_zero _), one_mul]
  obtain ⟨hSconst, hSne⟩ := setIntegral_shell_const (p := p) (((2 * kp : ℕ)) : ℤ) (((((ω (ϖ ^ (2 * kp)) : ℂˣ) : ℂ)))⁻¹)

  have hfub₁ := setIntegral_integral_swap {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = 1} 0 hUdef F₁
    hF₁cont (tsupport G) hKc hF₁supp
  have hfub₂ := setIntegral_integral_swap
    {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp (((2 * kp : ℕ)) : ℤ)} _ rfl F₂
    hF₂cont (tsupport G) hKc hF₂supp
  have hval : (∫ t in {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = 1},
      (∫ x, F₁ t x ∂(selfDualHaarAt ℚ p)) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
      C * (((((ω (ϖ ^ (2 * kp)) : ℂˣ) : ℂ)))⁻¹ *
        ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = WithZero.exp (((2 * kp : ℕ)) : ℤ)}).toReal) := by
    rw [hfub₁]
    simp_rw [hmid]
    rw [integral_const_mul, ← hfub₂]
    simp_rw [hfin]
    rw [setIntegral_congr_fun hSmeas hshellval, hSconst]

  have hgoal : (fun t : (p.adicCompletion ℚ)ˣ => ((ω t : ℂˣ) : ℂ) *
        ∫ x : p.adicCompletion ℚ, Wsh (w₀p * diagUnitGL2 t * unipotent x) *
          tateFourier (psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ (-x) ∂(selfDualHaarAt ℚ p)) =
      fun t => ∫ x, F₁ t x ∂(selfDualHaarAt ℚ p) := hstep1
  show (∫ t in {t : (p.adicCompletion ℚ)ˣ | Valued.v (t : p.adicCompletion ℚ) = 1},
      ((ω t : ℂˣ) : ℂ) * ∫ x : p.adicCompletion ℚ, Wsh (w₀p * diagUnitGL2 t * unipotent x) *
          tateFourier (psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ (-x) ∂(selfDualHaarAt ℚ p)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ≠ 0
  rw [show (fun t : (p.adicCompletion ℚ)ˣ => ((ω t : ℂˣ) : ℂ) *
        ∫ x : p.adicCompletion ℚ, Wsh (w₀p * diagUnitGL2 t * unipotent x) *
          tateFourier (psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ (-x) ∂(selfDualHaarAt ℚ p)) =
      fun t => ∫ x, F₁ t x ∂(selfDualHaarAt ℚ p) from hstep1, hval]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero hε₂ hε₁) hc₀) (mul_ne_zero (inv_ne_zero (Units.ne_zero _)) ?_)
  exact_mod_cast hSne

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31 P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le.Ws31.E4S"

end S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_unitShell_pairing_ne_zero_of_kirillov_shell_of_deepTwist_of_conductor_le (solution)
