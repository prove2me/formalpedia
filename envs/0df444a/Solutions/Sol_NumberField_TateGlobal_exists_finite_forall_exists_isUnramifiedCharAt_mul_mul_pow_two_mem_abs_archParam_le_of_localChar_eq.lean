-- Prove2me | solution 1 for NumberField.TateGlobal.exists_finite_forall_exists_isUnramifiedCharAt_mul_mul_pow_two_mem_abs_archParam_le_of_localChar_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/26bff47c-fedd-51be-a914-60bcbef22474

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_NormPowChar
import Theorems.Thm_NumberField_TateGlobal_exists_forall_exists_isIdeleClassChar_isUnramifiedCharAt_archLocalChar_eq_abs_sub_le
import Theorems.Thm_AutomorphicForm_exists_forall_finite_and_ncard_archParam_spread_le_of_isUnitaryChar_of_pairwise_ne_normOneIdeles
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_finite_forall_exists_isUnramifiedCharAt_mul_mul_pow_two_mem_abs_archParam_le_of_localChar_eq
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open IsDedekindDomain NumberField
open NumberField.AdelicLevel NumberField.AdelicVolume AutomorphicForm NumberField.TateGlobal
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open scoped Classical

namespace R4TwistNorm

variable {K : Type} [Field K] [NumberField K]

section Elementary

theorem continuous_units_of_isUnitaryChar {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hu : IsUnitaryChar (𝓞 K) K χ)
    (hc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) : Continuous χ := by
  refine Units.continuous_iff.mpr ⟨hc, ?_⟩
  have e : (fun z : (AdeleRing (𝓞 K) K)ˣ => (((χ z)⁻¹ : ℂˣ) : ℂ)) =
      fun z => (starRingEnd ℂ) ((χ z : ℂˣ) : ℂ) := by
    funext z
    have h1 : ((χ z : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    rw [Units.val_inv_eq_inv_val, Complex.inv_def, Complex.normSq_eq_norm_sq, hu z, one_pow, inv_one,
      Complex.ofReal_one, mul_one]
  rw [e]
  exact Complex.continuous_conj.comp hc

theorem eq_of_forall_cpow_mul_I_eq {a b : ℝ}
    (h : ∀ r : ℝ, 0 < r → ((r : ℂ)) ^ (((a : ℝ) : ℂ) * Complex.I) = ((r : ℂ)) ^ (((b : ℝ) : ℂ) * Complex.I)) : a = b := by
  by_contra hab
  have hd : a - b ≠ 0 := sub_ne_zero.2 hab
  set s : ℝ := Real.pi / (a - b) with hs
  have hr : 0 < Real.exp s := Real.exp_pos s
  have h1 := h _ hr
  have hlog : Complex.log ((Real.exp s : ℝ) : ℂ) = (s : ℂ) := by rw [← Complex.ofReal_log hr.le, Real.log_exp]
  have hne : ((Real.exp s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  rw [Complex.cpow_def_of_ne_zero hne, Complex.cpow_def_of_ne_zero hne, hlog] at h1
  have h2 : Complex.exp ((s : ℂ) * (((a : ℝ) : ℂ) * Complex.I) - (s : ℂ) * (((b : ℝ) : ℂ) * Complex.I)) = 1 := by
    rw [Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
  have h3 : (s : ℂ) * (((a : ℝ) : ℂ) * Complex.I) - (s : ℂ) * (((b : ℝ) : ℂ) * Complex.I) = (Real.pi : ℂ) * Complex.I := by
    have h4 : s * (a - b) = Real.pi := div_mul_cancel₀ _ hd
    have h5 : ((s : ℝ) : ℂ) * (((a : ℝ) : ℂ) - ((b : ℝ) : ℂ)) = (Real.pi : ℂ) := by exact_mod_cast h4
    linear_combination Complex.I * h5
  rw [h3, Complex.exp_pi_mul_I] at h2
  norm_num at h2

theorem exists_units_extensionEmbedding_eq (w : InfinitePlace K) (r : ℝ) (hr : 0 < r) :
    ∃ x : (w.Completion)ˣ, extensionEmbedding w (x : w.Completion) = (r : ℂ) := by
  by_cases hw : w.IsReal
  · have hx0 : (ringEquivRealOfIsReal hw).symm r ≠ 0 := by
      intro h
      apply hr.ne'
      have := congrArg (ringEquivRealOfIsReal hw) h
      rw [RingEquiv.apply_symm_apply, map_zero] at this
      exact this
    refine ⟨Units.mk0 _ hx0, ?_⟩
    rw [Units.val_mk0, ← extensionEmbeddingOfIsReal_apply hw, ← ringEquivRealOfIsReal_apply, RingEquiv.apply_symm_apply]
  · have hw' := NumberField.InfinitePlace.not_isReal_iff_isComplex.1 hw
    have hx0 : (ringEquivComplexOfIsComplex hw').symm (r : ℂ) ≠ 0 := by
      intro h
      apply hr.ne'
      have := congrArg (ringEquivComplexOfIsComplex hw') h
      rw [RingEquiv.apply_symm_apply, map_zero] at this
      exact_mod_cast this
    exact ⟨Units.mk0 _ hx0, (ringEquivComplexOfIsComplex hw').apply_symm_apply _⟩

theorem norm_extensionEmbedding (w : InfinitePlace K) (x : w.Completion) :
    ‖extensionEmbedding w x‖ = ‖x‖ :=
  (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

theorem exists_units_ideleNorm_archUnitHom_eq (w : InfinitePlace K) (r : ℝ) (hr : 0 < r) :
    ∃ x : (w.Completion)ˣ, 0 < (extensionEmbedding w (x : w.Completion)).re ∧
      (extensionEmbedding w (x : w.Completion)).im = 0 ∧ ideleNorm K (archUnitHom w x) = r := by
  have hn0 : (mult w) ≠ 0 := mult_ne_zero
  set ρ : ℝ := r ^ ((mult w : ℝ))⁻¹ with hρ
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos hr _
  obtain ⟨x, hx⟩ := exists_units_extensionEmbedding_eq w ρ hρpos
  refine ⟨x, by rw [hx, Complex.ofReal_re]; exact hρpos, by rw [hx, Complex.ofReal_im], ?_⟩
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K (archUnitHom w x) rfl,
    Finset.prod_eq_single w (fun w' _ hw' => ?_) (fun h => absurd (Finset.mem_univ w) h)]
  · rw [archUnitHom_apply, archCentralUnit_fst_self, ← norm_extensionEmbedding, hx, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hρpos, hρ]
    exact Real.rpow_inv_natCast_pow hr.le hn0
  · rw [archUnitHom_apply, archCentralUnit_fst_of_ne w x hw', norm_one, one_pow]

theorem ofReal_cpow_mul_I_mul {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    ((r : ℂ)) ^ (((a : ℝ) : ℂ) * Complex.I) * ((r : ℂ)) ^ (((b : ℝ) : ℂ) * Complex.I) =
      ((r : ℂ)) ^ ((((a + b : ℝ)) : ℂ) * Complex.I) := by
  rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hr.ne'), Complex.ofReal_add, add_mul]

theorem archLocalChar_mul_apply (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ((archLocalChar (χ₁ * χ₂) w x : ℂˣ) : ℂ) = ((archLocalChar χ₁ w x : ℂˣ) : ℂ) * ((archLocalChar χ₂ w x : ℂˣ) : ℂ) := rfl

theorem archLocalChar_pow_two_apply (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ((archLocalChar (χ ^ 2) w x : ℂˣ) : ℂ) = ((archLocalChar χ w x : ℂˣ) : ℂ) ^ 2 := rfl

theorem archLocalChar_inv_apply (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ((archLocalChar χ⁻¹ w x : ℂˣ) : ℂ) = (((archLocalChar χ w x : ℂˣ) : ℂ))⁻¹ := by
  show ((((χ (archUnitHom w x))⁻¹ : ℂˣ)) : ℂ) = _
  rw [Units.val_inv_eq_inv_val]; rfl

theorem localChar_mul (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) :
    localChar (χ₁ * χ₂) v u = localChar χ₁ v u * localChar χ₂ v u := rfl

theorem localChar_pow_two (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) :
    localChar (χ ^ 2) v u = localChar χ v u ^ 2 := rfl

theorem isUnitaryChar_mul {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (h₁ : IsUnitaryChar (𝓞 K) K χ₁)
    (h₂ : IsUnitaryChar (𝓞 K) K χ₂) : IsUnitaryChar (𝓞 K) K (χ₁ * χ₂) := fun x => by
  show ‖((χ₁ x * χ₂ x : ℂˣ) : ℂ)‖ = 1
  rw [Units.val_mul, norm_mul, h₁ x, h₂ x, mul_one]

theorem isIdeleClassChar_mul {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (h₁ : IsIdeleClassChar (𝓞 K) K χ₁)
    (h₂ : IsIdeleClassChar (𝓞 K) K χ₂) : IsIdeleClassChar (𝓞 K) K (χ₁ * χ₂) := fun u => by
  show χ₁ _ * χ₂ _ = 1
  rw [h₁ u, h₂ u, mul_one]

theorem continuous_coe_mul {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (h₁ : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₁ z : ℂˣ) : ℂ))
    (h₂ : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₂ z : ℂˣ) : ℂ)) :
    Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => (((χ₁ * χ₂) z : ℂˣ) : ℂ) := by
  have e : (fun z : (AdeleRing (𝓞 K) K)ˣ => (((χ₁ * χ₂) z : ℂˣ) : ℂ)) =
      fun z => ((χ₁ z : ℂˣ) : ℂ) * ((χ₂ z : ℂˣ) : ℂ) := by
    funext z; rfl
  rw [e]; exact h₁.mul h₂

theorem isUnramifiedCharAt_mul {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {v : HeightOneSpectrum (𝓞 K)}
    (h₁ : IsUnramifiedCharAt χ₁ v) (h₂ : IsUnramifiedCharAt χ₂ v) : IsUnramifiedCharAt (χ₁ * χ₂) v :=
  fun t ht ht' => by rw [localChar_mul, h₁ t ht ht', h₂ t ht ht', mul_one]

end Elementary

section Data

variable (K)

structure T1Data where
  B₁ : ℝ
  hB₁ : 0 ≤ B₁
  ηf : (InfinitePlace K → ℝ) → (InfinitePlace K → ℤ) → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
  τf : (InfinitePlace K → ℝ) → (InfinitePlace K → ℤ) → InfinitePlace K → ℝ
  mf : (InfinitePlace K → ℝ) → (InfinitePlace K → ℤ) → InfinitePlace K → ℤ
  unitary : ∀ σ b, IsUnitaryChar (𝓞 K) K (ηf σ b)
  ic : ∀ σ b, IsIdeleClassChar (𝓞 K) K (ηf σ b)
  cont : ∀ σ b, Continuous (ηf σ b)
  unram : ∀ σ b (v : HeightOneSpectrum (𝓞 K)), IsUnramifiedCharAt (ηf σ b) v
  hτ : ∀ σ b (v : InfinitePlace K) (x : (v.Completion)ˣ),
    0 < (extensionEmbedding v (x : v.Completion)).re → (extensionEmbedding v (x : v.Completion)).im = 0 →
    ((archLocalChar (ηf σ b) v x : ℂˣ) : ℂ) =
      (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τf σ b v : ℝ) : ℂ) * Complex.I)
  hm : ∀ σ b (v : InfinitePlace K) (x : (v.Completion)ˣ), ‖extensionEmbedding v (x : v.Completion)‖ = 1 →
    ((archLocalChar (ηf σ b) v x : ℂˣ) : ℂ) = (extensionEmbedding v (x : v.Completion)) ^ (mf σ b v)
  real : ∀ σ b (v : InfinitePlace K), v.IsReal → mf σ b v = 0
  τnear : ∀ σ b (v : InfinitePlace K), |τf σ b v - σ v| ≤ B₁
  mnear : ∀ σ b (v : InfinitePlace K), v.IsComplex → (|mf σ b v - b v| : ℝ) ≤ B₁
  pin : ∀ σ b, ∑ v : InfinitePlace K, (v.mult : ℝ) * (τf σ b v - σ v) = 0

theorem nonempty_T1Data : Nonempty (T1Data K) := by
  obtain ⟨B, hB, h⟩ :=
    NumberField.TateGlobal.exists_forall_exists_isIdeleClassChar_isUnramifiedCharAt_archLocalChar_eq_abs_sub_le K
  choose η τ m hu hic hc hun hτ hm hreal hτn hmn hpin using h
  exact ⟨⟨B, hB, η, τ, m, hu, hic, hc, hun, hτ, hm, hreal, hτn, hmn, hpin⟩⟩

variable {K}

noncomputable def σOf (τμ τν : InfinitePlace K → ℝ) : InfinitePlace K → ℝ := fun v => -(τμ v + τν v) / 2

def bOf (mμ : InfinitePlace K → ℤ) : InfinitePlace K → ℤ := fun v => -mμ v

end Data

section Central

variable (K)

structure Adm (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (nρ : ℕ) (ρs : Fin nρ → ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (n₀ : ℕ)
    (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τμ τν : InfinitePlace K → ℝ) (mμ mν : InfinitePlace K → ℤ) : Prop where
  uμ : IsUnitaryChar (𝓞 K) K μ
  uν : IsUnitaryChar (𝓞 K) K ν
  icμ : IsIdeleClassChar (𝓞 K) K μ
  icν : IsIdeleClassChar (𝓞 K) K ν
  cμ : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ)
  cν : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ)
  ram : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S₀ → IsUnramifiedCharAt μ v ∧ IsUnramifiedCharAt ν v
  pat : ∃ r r' : Fin nρ, ∀ v ∈ S₀, ∀ u : (v.adicCompletion K)ˣ,
    (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
    ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      localChar μ v u = ρs r v u ∧ localChar ν v u = ρs r' v u
  hτμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
    0 < (extensionEmbedding v (x : v.Completion)).re → (extensionEmbedding v (x : v.Completion)).im = 0 →
    ((archLocalChar μ v x : ℂˣ) : ℂ) = (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τμ v : ℝ) : ℂ) * Complex.I)
  hτν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
    0 < (extensionEmbedding v (x : v.Completion)).re → (extensionEmbedding v (x : v.Completion)).im = 0 →
    ((archLocalChar ν v x : ℂˣ) : ℂ) = (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τν v : ℝ) : ℂ) * Complex.I)
  hmμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ), ‖extensionEmbedding v (x : v.Completion)‖ = 1 →
    ((archLocalChar μ v x : ℂˣ) : ℂ) = (extensionEmbedding v (x : v.Completion)) ^ (mμ v)
  hmν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ), ‖extensionEmbedding v (x : v.Completion)‖ = 1 →
    ((archLocalChar ν v x : ℂˣ) : ℂ) = (extensionEmbedding v (x : v.Completion)) ^ (mν v)
  real : ∀ v : InfinitePlace K, v.IsReal → (mμ v = 0 ∨ mμ v = 1) ∧ (mν v = 0 ∨ mν v = 1)
  diff : ∀ v : InfinitePlace K, v.IsComplex → |mμ v - mν v| ≤ (n₀ : ℤ)

variable {K}
variable (D : T1Data K)

noncomputable def ηOf (τμ τν : InfinitePlace K → ℝ) (mμ : InfinitePlace K → ℤ) : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ :=
  D.ηf (σOf τμ τν) (bOf mμ)

noncomputable def τηOf (τμ τν : InfinitePlace K → ℝ) (mμ : InfinitePlace K → ℤ) : InfinitePlace K → ℝ :=
  D.τf (σOf τμ τν) (bOf mμ)

noncomputable def mηOf (τμ τν : InfinitePlace K → ℝ) (mμ : InfinitePlace K → ℤ) : InfinitePlace K → ℤ :=
  D.mf (σOf τμ τν) (bOf mμ)

noncomputable def ξOf (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τμ τν : InfinitePlace K → ℝ) (mμ : InfinitePlace K → ℤ) :
    (AdeleRing (𝓞 K) K)ˣ →* ℂˣ :=
  μ * ν * (ηOf D τμ τν mμ) ^ 2

noncomputable def τξOf (τμ τν : InfinitePlace K → ℝ) (mμ : InfinitePlace K → ℤ) : InfinitePlace K → ℝ :=
  fun v => τμ v + τν v + 2 * τηOf D τμ τν mμ v

noncomputable def mξOf (τμ τν : InfinitePlace K → ℝ) (mμ mν : InfinitePlace K → ℤ) : InfinitePlace K → ℤ :=
  fun v => mμ v + mν v + 2 * mηOf D τμ τν mμ v

variable {S₀ : Finset (HeightOneSpectrum (𝓞 K))} {nρ : ℕ}
  {ρs : Fin nρ → ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {n₀ : ℕ}
  {μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {τμ τν : InfinitePlace K → ℝ} {mμ mν : InfinitePlace K → ℤ}

theorem abs_τξOf_le (v : InfinitePlace K) : |τξOf D τμ τν mμ v| ≤ 2 * D.B₁ := by
  have h := D.τnear (σOf τμ τν) (bOf mμ) v
  have e : τξOf D τμ τν mμ v = 2 * (τηOf D τμ τν mμ v - σOf τμ τν v) := by
    simp only [τξOf, τηOf, σOf]; ring
  rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

theorem sum_mult_mul_τξOf : ∑ v : InfinitePlace K, (v.mult : ℝ) * τξOf D τμ τν mμ v = 0 := by
  have h := D.pin (σOf τμ τν) (bOf mμ)
  have e : ∀ v : InfinitePlace K, (v.mult : ℝ) * τξOf D τμ τν mμ v =
      2 * ((v.mult : ℝ) * (D.τf (σOf τμ τν) (bOf mμ) v - σOf τμ τν v)) := fun v => by
    simp only [τξOf, τηOf, σOf]; ring
  simp only [e, ← Finset.mul_sum, h, mul_zero]

theorem abs_mμ_add_mη_le (hA : Adm K S₀ nρ ρs n₀ μ ν τμ τν mμ mν) (v : InfinitePlace K) :
    (|mμ v + mηOf D τμ τν mμ v| : ℝ) ≤ D.B₁ + 1 := by
  by_cases hv : v.IsReal
  · have h0 : mηOf D τμ τν mμ v = 0 := D.real _ _ v hv
    have h1 : |mμ v + mηOf D τμ τν mμ v| ≤ 1 := by
      rw [h0, add_zero]
      rcases (hA.real v hv).1 with h | h <;> rw [h] <;> norm_num
    have h2 : (|mμ v + mηOf D τμ τν mμ v| : ℝ) ≤ 1 := by exact_mod_cast h1
    linarith [D.hB₁]
  · have hc : v.IsComplex := not_isReal_iff_isComplex.mp hv
    have h := D.mnear (σOf τμ τν) (bOf mμ) v hc
    have e : ((D.mf (σOf τμ τν) (bOf mμ) v : ℤ) : ℝ) - ((bOf mμ v : ℤ) : ℝ) =
        (mμ v : ℝ) + (mηOf D τμ τν mμ v : ℝ) := by
      simp only [mηOf, bOf]; push_cast; ring
    rw [e] at h
    linarith

theorem abs_mν_add_mη_le (hA : Adm K S₀ nρ ρs n₀ μ ν τμ τν mμ mν) (v : InfinitePlace K) :
    (|mν v + mηOf D τμ τν mμ v| : ℝ) ≤ n₀ + D.B₁ + 1 := by
  by_cases hv : v.IsReal
  · have h0 : mηOf D τμ τν mμ v = 0 := D.real _ _ v hv
    have h1 : |mν v + mηOf D τμ τν mμ v| ≤ 1 := by
      rw [h0, add_zero]
      rcases (hA.real v hv).2 with h | h <;> rw [h] <;> norm_num
    have h2 : (|mν v + mηOf D τμ τν mμ v| : ℝ) ≤ 1 := by exact_mod_cast h1
    have h3 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
    linarith [D.hB₁]
  · have hc : v.IsComplex := not_isReal_iff_isComplex.mp hv
    have h1 := abs_mμ_add_mη_le D hA v
    have h2 : (|mμ v - mν v| : ℝ) ≤ n₀ := by exact_mod_cast hA.diff v hc
    have e : ((mν v + mηOf D τμ τν mμ v : ℤ) : ℝ) =
        ((mμ v + mηOf D τμ τν mμ v : ℤ) : ℝ) - ((mμ v - mν v : ℤ) : ℝ) := by push_cast; ring
    have h3 : (|mν v + mηOf D τμ τν mμ v| : ℝ) = |((mν v + mηOf D τμ τν mμ v : ℤ) : ℝ)| := by push_cast; rfl
    have h4 : (|mμ v + mηOf D τμ τν mμ v| : ℝ) = |((mμ v + mηOf D τμ τν mμ v : ℤ) : ℝ)| := by push_cast; rfl
    have h5 : (|mμ v - mν v| : ℝ) = |((mμ v - mν v : ℤ) : ℝ)| := by push_cast; rfl
    rw [h3, e]
    rw [h4] at h1; rw [h5] at h2
    calc |((mμ v + mηOf D τμ τν mμ v : ℤ) : ℝ) - ((mμ v - mν v : ℤ) : ℝ)|
        ≤ |((mμ v + mηOf D τμ τν mμ v : ℤ) : ℝ)| + |((mμ v - mν v : ℤ) : ℝ)| := abs_sub _ _
      _ ≤ (D.B₁ + 1) + n₀ := add_le_add h1 h2
      _ = n₀ + D.B₁ + 1 := by ring

theorem abs_mξOf_le (hA : Adm K S₀ nρ ρs n₀ μ ν τμ τν mμ mν) (v : InfinitePlace K) :
    (|mξOf D τμ τν mμ mν v| : ℝ) ≤ n₀ + 3 * (D.B₁ + 1) := by
  have h1 := abs_mμ_add_mη_le D hA v
  have h2 := abs_mν_add_mη_le D hA v
  have e : ((mξOf D τμ τν mμ mν v : ℤ) : ℝ) =
      ((mμ v + mηOf D τμ τν mμ v : ℤ) : ℝ) + ((mν v + mηOf D τμ τν mμ v : ℤ) : ℝ) := by
    simp only [mξOf]; push_cast; ring
  have h3 : (|mξOf D τμ τν mμ mν v| : ℝ) = |((mξOf D τμ τν mμ mν v : ℤ) : ℝ)| := rfl
  have h4 : (|mμ v + mηOf D τμ τν mμ v| : ℝ) = |((mμ v + mηOf D τμ τν mμ v : ℤ) : ℝ)| := by push_cast; rfl
  have h5 : (|mν v + mηOf D τμ τν mμ v| : ℝ) = |((mν v + mηOf D τμ τν mμ v : ℤ) : ℝ)| := by push_cast; rfl
  rw [h4] at h1; rw [h5] at h2
  rw [h3, e]
  calc |((mμ v + mηOf D τμ τν mμ v : ℤ) : ℝ) + ((mν v + mηOf D τμ τν mμ v : ℤ) : ℝ)|
      ≤ |((mμ v + mηOf D τμ τν mμ v : ℤ) : ℝ)| + |((mν v + mηOf D τμ τν mμ v : ℤ) : ℝ)| := abs_add_le _ _
    _ ≤ (D.B₁ + 1) + (n₀ + D.B₁ + 1) := add_le_add h1 h2
    _ ≤ n₀ + 3 * (D.B₁ + 1) := by linarith [D.hB₁]

theorem isUnitaryChar_ξOf (hA : Adm K S₀ nρ ρs n₀ μ ν τμ τν mμ mν) : IsUnitaryChar (𝓞 K) K (ξOf D μ ν τμ τν mμ) := by
  unfold ξOf; rw [pow_two]
  exact isUnitaryChar_mul (isUnitaryChar_mul hA.uμ hA.uν) (isUnitaryChar_mul (D.unitary _ _) (D.unitary _ _))

theorem isIdeleClassChar_ξOf (hA : Adm K S₀ nρ ρs n₀ μ ν τμ τν mμ mν) :
    IsIdeleClassChar (𝓞 K) K (ξOf D μ ν τμ τν mμ) := by
  unfold ξOf; rw [pow_two]
  exact isIdeleClassChar_mul (isIdeleClassChar_mul hA.icμ hA.icν) (isIdeleClassChar_mul (D.ic _ _) (D.ic _ _))

theorem continuous_coe_ξOf (hA : Adm K S₀ nρ ρs n₀ μ ν τμ τν mμ mν) :
    Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξOf D μ ν τμ τν mμ z : ℂˣ) : ℂ) := by
  unfold ξOf; rw [pow_two]
  have hη : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ηOf D τμ τν mμ z : ℂˣ) : ℂ) :=
    Units.continuous_val.comp (D.cont _ _)
  exact continuous_coe_mul (continuous_coe_mul hA.cμ hA.cν) (continuous_coe_mul hη hη)

theorem isUnramifiedCharAt_ξOf (hA : Adm K S₀ nρ ρs n₀ μ ν τμ τν mμ mν) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S₀) :
    IsUnramifiedCharAt (ξOf D μ ν τμ τν mμ) v := by
  unfold ξOf; rw [pow_two]
  exact isUnramifiedCharAt_mul (isUnramifiedCharAt_mul (hA.ram v hv).1 (hA.ram v hv).2)
    (isUnramifiedCharAt_mul (D.unram _ _ v) (D.unram _ _ v))

theorem localChar_ξOf (hA : Adm K S₀ nρ ρs n₀ μ ν τμ τν mμ mν) :
    ∃ r r' : Fin nρ, ∀ v ∈ S₀, ∀ u : (v.adicCompletion K)ˣ,
      (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        localChar (ξOf D μ ν τμ τν mμ) v u = ρs r v u * ρs r' v u := by
  obtain ⟨r, r', h⟩ := hA.pat
  refine ⟨r, r', fun v hv u hu hu' => ?_⟩
  have hη1 : localChar (ηOf D τμ τν mμ) v u = 1 := D.unram _ _ v u hu hu'
  unfold ξOf
  rw [localChar_mul, localChar_mul, localChar_pow_two, (h v hv u hu hu').1, (h v hv u hu hu').2,
    hη1, one_pow, mul_one]

theorem archLocalChar_ξOf_of_pos (hA : Adm K S₀ nρ ρs n₀ μ ν τμ τν mμ mν) (v : InfinitePlace K) (x : (v.Completion)ˣ)
    (hre : 0 < (extensionEmbedding v (x : v.Completion)).re) (him : (extensionEmbedding v (x : v.Completion)).im = 0) :
    ((archLocalChar (ξOf D μ ν τμ τν mμ) v x : ℂˣ) : ℂ) =
      (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τξOf D τμ τν mμ v : ℝ) : ℂ) * Complex.I) := by
  have hN : 0 < ideleNorm K (archUnitHom v x) := ideleNorm_pos _
  have hη := D.hτ (σOf τμ τν) (bOf mμ) v x hre him
  change ((archLocalChar (ηOf D τμ τν mμ) v x : ℂˣ) : ℂ) =
    (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τηOf D τμ τν mμ v : ℝ) : ℂ) * Complex.I) at hη
  unfold ξOf
  rw [archLocalChar_mul_apply, archLocalChar_mul_apply, archLocalChar_pow_two_apply, hA.hτμ v x hre him,
    hA.hτν v x hre him, hη, pow_two, ofReal_cpow_mul_I_mul hN, ofReal_cpow_mul_I_mul hN,
    ofReal_cpow_mul_I_mul hN]
  have e : τμ v + τν v + (τηOf D τμ τν mμ v + τηOf D τμ τν mμ v) = τξOf D τμ τν mμ v := by
    simp only [τξOf]; ring
  rw [e]

theorem archLocalChar_ξOf_of_norm_eq_one (hA : Adm K S₀ nρ ρs n₀ μ ν τμ τν mμ mν) (v : InfinitePlace K)
    (x : (v.Completion)ˣ) (h1 : ‖extensionEmbedding v (x : v.Completion)‖ = 1) :
    ((archLocalChar (ξOf D μ ν τμ τν mμ) v x : ℂˣ) : ℂ) =
      (extensionEmbedding v (x : v.Completion)) ^ (mξOf D τμ τν mμ mν v) := by
  have hz : extensionEmbedding v (x : v.Completion) ≠ 0 := norm_ne_zero_iff.mp (by rw [h1]; exact one_ne_zero)
  have hη := D.hm (σOf τμ τν) (bOf mμ) v x h1
  change ((archLocalChar (ηOf D τμ τν mμ) v x : ℂˣ) : ℂ) =
    (extensionEmbedding v (x : v.Completion)) ^ (mηOf D τμ τν mμ v) at hη
  unfold ξOf
  rw [archLocalChar_mul_apply, archLocalChar_mul_apply, archLocalChar_pow_two_apply, hA.hmμ v x h1, hA.hmν v x h1,
    hη, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hz, ← zpow_add₀ hz]
  have e : mμ v + mν v + mηOf D τμ τν mμ v * ((2 : ℕ) : ℤ) = mξOf D τμ τν mμ mν v := by
    simp only [mξOf]; push_cast; ring
  rw [e]

end Central

section Distinct

theorem eq_of_forall_mem_normOneIdeles_eq {ξ ξ' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (hu : IsUnitaryChar (𝓞 K) K ξ) (hu' : IsUnitaryChar (𝓞 K) K ξ')
    (hc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ z : ℂˣ) : ℂ))
    (hc' : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ' z : ℂˣ) : ℂ))
    (τ τ' : InfinitePlace K → ℝ)
    (hτ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      0 < (extensionEmbedding v (x : v.Completion)).re → (extensionEmbedding v (x : v.Completion)).im = 0 →
      ((archLocalChar ξ v x : ℂˣ) : ℂ) = (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ v : ℝ) : ℂ) * Complex.I))
    (hτ' : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      0 < (extensionEmbedding v (x : v.Completion)).re → (extensionEmbedding v (x : v.Completion)).im = 0 →
      ((archLocalChar ξ' v x : ℂˣ) : ℂ) = (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ' v : ℝ) : ℂ) * Complex.I))
    (hsum : ∑ v : InfinitePlace K, (v.mult : ℝ) * τ v = 0)
    (hsum' : ∑ v : InfinitePlace K, (v.mult : ℝ) * τ' v = 0)
    (heq : ∀ z ∈ normOneIdeles K, ξ z = ξ' z) : ξ = ξ' := by

  set χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := ξ' * ξ⁻¹ with hχ
  have hχu : IsUnitaryChar (𝓞 K) K χ := fun z => by
    show ‖((ξ' z * (ξ z)⁻¹ : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hu z, hu' z, inv_one, mul_one]
  have hχc : Continuous χ := by
    have h1 : Continuous ξ := continuous_units_of_isUnitaryChar hu hc
    have h2 : Continuous ξ' := continuous_units_of_isUnitaryChar hu' hc'
    have e : (χ : (AdeleRing (𝓞 K) K)ˣ → ℂˣ) = fun z => ξ' z * (ξ z)⁻¹ := by funext z; rfl
    rw [e]; exact h2.mul h1.inv
  have hχ1 : ∀ z ∈ normOneIdeles K, χ z = 1 := fun z hz => by
    show ξ' z * (ξ z)⁻¹ = 1
    rw [← heq z hz, mul_inv_cancel]
  obtain ⟨t, ht⟩ := NumberField.TateGlobal.exists_eq_normPowChar_of_forall_mem_normOneIdeles K χ hχc hχu hχ1

  have hτeq : ∀ v : InfinitePlace K, τ' v = t + τ v := by
    intro v
    refine eq_of_forall_cpow_mul_I_eq fun r hr => ?_
    obtain ⟨x, hre, him, hN⟩ := exists_units_ideleNorm_archUnitHom_eq v r hr
    have h1 : ((archLocalChar χ v x : ℂˣ) : ℂ) = ((archLocalChar ξ' v x : ℂˣ) : ℂ) * (((archLocalChar ξ v x : ℂˣ) : ℂ))⁻¹ := by
      rw [hχ, archLocalChar_mul_apply, archLocalChar_inv_apply]
    have h2 : ((archLocalChar χ v x : ℂˣ) : ℂ) = ((r : ℂ)) ^ (((t : ℝ) : ℂ) * Complex.I) := by
      rw [ht, archLocalChar_apply, ← archUnitHom_apply, coe_normPowChar_apply, hN, mul_comm]
    rw [hτ' v x hre him, hτ v x hre him, hN] at h1
    rw [h1] at h2
    have hne : ((r : ℂ)) ^ (((τ v : ℝ) : ℂ) * Complex.I) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')]; exact Complex.exp_ne_zero _
    have h3 : ((r : ℂ)) ^ (((τ' v : ℝ) : ℂ) * Complex.I) =
        ((r : ℂ)) ^ (((t : ℝ) : ℂ) * Complex.I) * ((r : ℂ)) ^ (((τ v : ℝ) : ℂ) * Complex.I) := by
      rw [← h2, inv_mul_cancel_right₀ hne]
    rw [h3, ofReal_cpow_mul_I_mul hr]

  have ht0 : t = 0 := by
    have h1 : ∑ v : InfinitePlace K, (v.mult : ℝ) * τ' v = t * ∑ v : InfinitePlace K, (v.mult : ℝ) +
        ∑ v : InfinitePlace K, (v.mult : ℝ) * τ v := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun v _ => by rw [hτeq v]; ring
    rw [hsum, hsum', add_zero] at h1
    have hmultpos : (0 : ℝ) < ∑ w : InfinitePlace K, (mult w : ℝ) := by
      have h : ((∑ w : InfinitePlace K, mult w : ℕ) : ℝ) = ∑ w : InfinitePlace K, (mult w : ℝ) := by push_cast; rfl
      rw [← h, sum_mult_eq]
      exact_mod_cast Module.finrank_pos
    exact (mul_eq_zero.mp h1.symm).resolve_right hmultpos.ne'
  have hχone : χ = 1 := by rw [ht, ht0, normPowChar_zero]
  ext z
  have : ξ' z * (ξ z)⁻¹ = 1 := by
    have := congrArg (fun φ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ => φ z) hχone
    simpa [hχ] using this
  rw [mul_inv_eq_one] at this
  rw [this]

end Distinct

section Finite

variable (D : T1Data K) (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (nρ : ℕ)
  (ρs : Fin nρ → ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (n₀ : ℕ)

def Xi : Set ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) :=
  {ξ | ∃ (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τμ τν : InfinitePlace K → ℝ) (mμ mν : InfinitePlace K → ℤ),
    Adm K S₀ nρ ρs n₀ μ ν τμ τν mμ mν ∧ ξ = ξOf D μ ν τμ τν mμ}

noncomputable def ρs2 : Fin (nρ * nρ) → ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ :=
  fun k v => ρs (finProdFinEquiv.symm k).1 v * ρs (finProdFinEquiv.symm k).2 v

theorem mem_Xi_props {ξ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hξ : ξ ∈ Xi D S₀ nρ ρs n₀) :
    IsUnitaryChar (𝓞 K) K ξ ∧ IsIdeleClassChar (𝓞 K) K ξ ∧
      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ z : ℂˣ) : ℂ) := by
  obtain ⟨μ, ν, τμ, τν, mμ, mν, hA, rfl⟩ := hξ
  exact ⟨isUnitaryChar_ξOf D hA, isIdeleClassChar_ξOf D hA, continuous_coe_ξOf D hA⟩

theorem finite_Xi : (Xi D S₀ nρ ρs n₀).Finite := by
  set Ξ := Xi D S₀ nρ ρs n₀ with hΞ

  have hgen : ∀ e : Ξ, ∃ (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τμ τν : InfinitePlace K → ℝ) (mμ mν : InfinitePlace K → ℤ),
      Adm K S₀ nρ ρs n₀ μ ν τμ τν mμ mν ∧ (e : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) = ξOf D μ ν τμ τν mμ := fun e => e.2
  choose μf νf τμf τνf mμf mνf hAf hef using hgen

  set τF : Ξ → InfinitePlace K → ℝ := fun e => τξOf D (τμf e) (τνf e) (mμf e) with hτF
  set mF : Ξ → InfinitePlace K → ℤ := fun e => mξOf D (τμf e) (τνf e) (mμf e) (mνf e) with hmF
  set M₀ : ℕ := n₀ + 3 * (⌈D.B₁⌉₊ + 1) with hM₀
  obtain ⟨C, hC0, hcount⟩ :=
    AutomorphicForm.exists_forall_finite_and_ncard_archParam_spread_le_of_isUnitaryChar_of_pairwise_ne_normOneIdeles
      K S₀ M₀ (nρ * nρ) (ρs2 nρ ρs)
  have huF : ∀ e : Ξ, IsUnitaryChar (𝓞 K) K (e : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := fun e => by
    rw [hef e]; exact isUnitaryChar_ξOf D (hAf e)
  have hicF : ∀ e : Ξ, IsIdeleClassChar (𝓞 K) K (e : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := fun e => by
    rw [hef e]; exact isIdeleClassChar_ξOf D (hAf e)
  have hcF : ∀ e : Ξ, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => (((e : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) z : ℂˣ) : ℂ) :=
    fun e => by rw [hef e]; exact continuous_coe_ξOf D (hAf e)
  have hτFc : ∀ (e : Ξ) (v : InfinitePlace K) (x : (v.Completion)ˣ),
      0 < (extensionEmbedding v (x : v.Completion)).re → (extensionEmbedding v (x : v.Completion)).im = 0 →
      ((archLocalChar (e : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) v x : ℂˣ) : ℂ) =
        (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τF e v : ℝ) : ℂ) * Complex.I) := fun e v x hre him => by
    rw [hef e]; exact archLocalChar_ξOf_of_pos D (hAf e) v x hre him
  have hmFc : ∀ (e : Ξ) (v : InfinitePlace K) (x : (v.Completion)ˣ), ‖extensionEmbedding v (x : v.Completion)‖ = 1 →
      ((archLocalChar (e : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) v x : ℂˣ) : ℂ) =
        (extensionEmbedding v (x : v.Completion)) ^ (mF e v) := fun e v x h1 => by
    rw [hef e]; exact archLocalChar_ξOf_of_norm_eq_one D (hAf e) v x h1
  have hM₀c : ∀ e : Ξ, 0 < (1 : ℕ) → ∀ v : InfinitePlace K, |mF e v| ≤ (M₀ : ℤ) := fun e _ v => by
    have h1 : (|mF e v| : ℝ) ≤ n₀ + 3 * (D.B₁ + 1) := abs_mξOf_le D (hAf e) v
    have h2 : (n₀ : ℝ) + 3 * (D.B₁ + 1) ≤ (M₀ : ℝ) := by
      rw [hM₀]; push_cast; linarith [Nat.le_ceil D.B₁]
    have h3 : ((|mF e v| : ℤ) : ℝ) ≤ ((M₀ : ℤ) : ℝ) := by
      have := h1.trans h2; push_cast at this ⊢; exact this
    exact_mod_cast h3
  have hramc : ∀ e : Ξ, 0 < (1 : ℕ) →
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S₀ → IsUnramifiedCharAt (e : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) v) ∧
      ∃ r : Fin (nρ * nρ), ∀ v ∈ S₀, ∀ u : (v.adicCompletion K)ˣ,
        (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
          localChar (e : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) v u = ρs2 nρ ρs r v u := fun e _ => by
    refine ⟨fun v hv => by rw [hef e]; exact isUnramifiedCharAt_ξOf D (hAf e) hv, ?_⟩
    obtain ⟨r, r', h⟩ := localChar_ξOf D (hAf e)
    refine ⟨finProdFinEquiv (r, r'), fun v hv u hu hu' => ?_⟩
    rw [hef e, h v hv u hu hu', ρs2, Equiv.symm_apply_apply]
    rfl
  have hdist : ∀ e e' : Ξ, e ≠ e' → 0 < (1 : ℕ) → 0 < (1 : ℕ) →
      ∃ z ∈ normOneIdeles K, (e : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) z ≠ (e' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) z := by
    intro e e' hne _ _
    by_contra hall
    have hall' : ∀ z ∈ normOneIdeles K,
        (e : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) z = (e' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) z := fun z hz => by
      by_contra hz'
      exact hall ⟨z, hz, hz'⟩
    apply hne
    apply Subtype.ext
    exact eq_of_forall_mem_normOneIdeles_eq (huF e) (huF e') (hcF e) (hcF e') (τF e) (τF e') (hτFc e) (hτFc e')
      (sum_mult_mul_τξOf D) (sum_mult_mul_τξOf D) hall'

  have hfin := (hcount Ξ (fun e => (e : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)) huF hicF hcF (fun _ => 1) hdist τF hτFc mF hmFc
    hM₀c hramc)
  set R : ℝ := ∑ v : InfinitePlace K, ∑ v' : InfinitePlace K, (4 * D.B₁) with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by linarith [D.hB₁]
  have hall : {e : Ξ | 0 < (1 : ℕ) ∧ ∑ v : InfinitePlace K, ∑ v' : InfinitePlace K, |τF e v - τF e v'| ≤ R} = Set.univ := by
    refine Set.eq_univ_of_forall fun e => ⟨Nat.one_pos, ?_⟩
    refine Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun v' _ => ?_
    calc |τF e v - τF e v'| ≤ |τF e v| + |τF e v'| := abs_sub _ _
      _ ≤ 2 * D.B₁ + 2 * D.B₁ := add_le_add (abs_τξOf_le D v) (abs_τξOf_le D v')
      _ = 4 * D.B₁ := by ring
  have huniv : (Set.univ : Set Ξ).Finite := by rw [← hall]; exact (hfin R hR0).1
  exact Set.finite_coe_iff.mp (Set.finite_univ_iff.mp huniv)

end Finite

section Main

variable (K)

theorem main
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (nρ : ℕ) (ρs : Fin nρ → ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (n₀ : ℕ) :
    ∃ (B : ℝ) (Ξ : Set ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ)), 0 ≤ B ∧ Ξ.Finite ∧
    (∀ ξ ∈ Ξ, IsUnitaryChar (𝓞 K) K ξ ∧ IsIdeleClassChar (𝓞 K) K ξ ∧
      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ z : ℂˣ) : ℂ)) ∧
    ∀ (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hram : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S₀ → IsUnramifiedCharAt μ v ∧ IsUnramifiedCharAt ν v)
      (_hρ : ∃ r r' : Fin nρ, ∀ v ∈ S₀, ∀ u : (v.adicCompletion K)ˣ,
        (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
          localChar μ v u = ρs r v u ∧ localChar ν v u = ρs r' v u)
      (τμ τν : InfinitePlace K → ℝ)
      (_hτμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (extensionEmbedding v (x : v.Completion)).re → (extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar μ v x : ℂˣ) : ℂ) = (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τμ v : ℝ) : ℂ) * Complex.I))
      (_hτν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (extensionEmbedding v (x : v.Completion)).re → (extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar ν v x : ℂˣ) : ℂ) = (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τν v : ℝ) : ℂ) * Complex.I))
      (mμ mν : InfinitePlace K → ℤ)
      (_hmμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ), ‖extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar μ v x : ℂˣ) : ℂ) = (extensionEmbedding v (x : v.Completion)) ^ (mμ v))
      (_hmν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ), ‖extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar ν v x : ℂˣ) : ℂ) = (extensionEmbedding v (x : v.Completion)) ^ (mν v))
      (_hreal : ∀ v : InfinitePlace K, v.IsReal → (mμ v = 0 ∨ mμ v = 1) ∧ (mν v = 0 ∨ mν v = 1))
      (_hdiff : ∀ v : InfinitePlace K, v.IsComplex → |mμ v - mν v| ≤ (n₀ : ℤ)),
    ∃ (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τη : InfinitePlace K → ℝ) (mη : InfinitePlace K → ℤ),
      IsUnitaryChar (𝓞 K) K η ∧ IsIdeleClassChar (𝓞 K) K η ∧ Continuous η ∧
      (∀ v : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt η v) ∧
      (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (extensionEmbedding v (x : v.Completion)).re → (extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar η v x : ℂˣ) : ℂ) = (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τη v : ℝ) : ℂ) * Complex.I)) ∧
      (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ), ‖extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar η v x : ℂˣ) : ℂ) = (extensionEmbedding v (x : v.Completion)) ^ (mη v)) ∧
      (∀ v : InfinitePlace K, v.IsReal → mη v = 0) ∧
      μ * ν * η ^ 2 ∈ Ξ ∧
      (∀ v : InfinitePlace K, |τμ v + τν v + 2 * τη v| ≤ B) ∧
      (∀ v : InfinitePlace K, (|mμ v + mη v| : ℝ) ≤ B ∧ (|mν v + mη v| : ℝ) ≤ B) ∧
      (∀ t : ℝ, 1 + ∑ v : InfinitePlace K,
          (|t + (τμ v + τη v)| + |t - (τν v + τη v)| + (|mμ v + mη v| : ℝ) + (|mν v + mη v| : ℝ)) ≤
        B * (1 + ∑ v : InfinitePlace K, |2 * t + (τμ v - τν v)|)) := by
  obtain ⟨D⟩ := nonempty_T1Data K

  set C₀ : ℝ := 4 * D.B₁ + 2 * n₀ + 2 with hC₀
  set r : ℝ := (Fintype.card (InfinitePlace K) : ℝ) with hr
  set B : ℝ := 1 + r * C₀ + C₀ with hB
  have hC₀0 : 0 ≤ C₀ := by have := D.hB₁; have : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _; rw [hC₀]; linarith
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hBC : C₀ ≤ B := by rw [hB]; nlinarith
  refine ⟨B, Xi D S₀ nρ ρs n₀, hB0, finite_Xi D S₀ nρ ρs n₀, fun ξ hξ => mem_Xi_props D S₀ nρ ρs n₀ hξ, ?_⟩
  intro μ ν hμ hν hμic hνic hμc hνc hram hρ τμ τν hτμ hτν mμ mν hmμ hmν hreal hdiff
  have hA : Adm K S₀ nρ ρs n₀ μ ν τμ τν mμ mν :=
    ⟨hμ, hν, hμic, hνic, hμc, hνc, hram, hρ, hτμ, hτν, hmμ, hmν, hreal, hdiff⟩
  set η := ηOf D τμ τν mμ with hη
  set τη := τηOf D τμ τν mμ with hτη
  set mη := mηOf D τμ τν mμ with hmη

  have hbτ : ∀ v : InfinitePlace K, |τμ v + τν v + 2 * τη v| ≤ 2 * D.B₁ := fun v => abs_τξOf_le D v
  have hbm₁ : ∀ v : InfinitePlace K, (|mμ v + mη v| : ℝ) ≤ D.B₁ + 1 := fun v => abs_mμ_add_mη_le D hA v
  have hbm₂ : ∀ v : InfinitePlace K, (|mν v + mη v| : ℝ) ≤ n₀ + D.B₁ + 1 := fun v => abs_mν_add_mη_le D hA v
  refine ⟨η, τη, mη, D.unitary _ _, D.ic _ _, D.cont _ _, D.unram _ _, D.hτ _ _, D.hm _ _, D.real _ _,
    ⟨μ, ν, τμ, τν, mμ, mν, hA, rfl⟩, fun v => (hbτ v).trans (by rw [hC₀] at hBC; linarith [D.hB₁]),
    fun v => ⟨(hbm₁ v).trans ?_, (hbm₂ v).trans ?_⟩, fun t => ?_⟩
  · have : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
    rw [hC₀] at hBC; linarith [D.hB₁]
  · rw [hC₀] at hBC; linarith [D.hB₁]
  ·
    have hterm : ∀ v : InfinitePlace K,
        |t + (τμ v + τη v)| + |t - (τν v + τη v)| + (|mμ v + mη v| : ℝ) + (|mν v + mη v| : ℝ) ≤
          |2 * t + (τμ v - τν v)| + C₀ := by
      intro v
      have e1 : t + (τμ v + τη v) = (2 * t + (τμ v - τν v)) / 2 + (τμ v + τν v + 2 * τη v) / 2 := by ring
      have e2 : t - (τν v + τη v) = (2 * t + (τμ v - τν v)) / 2 - (τμ v + τν v + 2 * τη v) / 2 := by ring
      have h1 : |t + (τμ v + τη v)| ≤ |2 * t + (τμ v - τν v)| / 2 + D.B₁ := by
        rw [e1]
        calc |(2 * t + (τμ v - τν v)) / 2 + (τμ v + τν v + 2 * τη v) / 2|
            ≤ |(2 * t + (τμ v - τν v)) / 2| + |(τμ v + τν v + 2 * τη v) / 2| := abs_add_le _ _
          _ ≤ |2 * t + (τμ v - τν v)| / 2 + D.B₁ := by
              rw [abs_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
              linarith [hbτ v]
      have h2 : |t - (τν v + τη v)| ≤ |2 * t + (τμ v - τν v)| / 2 + D.B₁ := by
        rw [e2]
        calc |(2 * t + (τμ v - τν v)) / 2 - (τμ v + τν v + 2 * τη v) / 2|
            ≤ |(2 * t + (τμ v - τν v)) / 2| + |(τμ v + τν v + 2 * τη v) / 2| := abs_sub _ _
          _ ≤ |2 * t + (τμ v - τν v)| / 2 + D.B₁ := by
              rw [abs_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
              linarith [hbτ v]
      have h3 := hbm₁ v
      have h4 := hbm₂ v
      rw [hC₀]; linarith
    have hsum : ∑ v : InfinitePlace K,
        (|t + (τμ v + τη v)| + |t - (τν v + τη v)| + (|mμ v + mη v| : ℝ) + (|mν v + mη v| : ℝ)) ≤
          ∑ v : InfinitePlace K, |2 * t + (τμ v - τν v)| + r * C₀ := by
      calc ∑ v : InfinitePlace K,
            (|t + (τμ v + τη v)| + |t - (τν v + τη v)| + (|mμ v + mη v| : ℝ) + (|mν v + mη v| : ℝ))
          ≤ ∑ v : InfinitePlace K, (|2 * t + (τμ v - τν v)| + C₀) := Finset.sum_le_sum fun v _ => hterm v
        _ = ∑ v : InfinitePlace K, |2 * t + (τμ v - τν v)| + r * C₀ := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hr, Finset.card_univ]
    have hS0 : 0 ≤ ∑ v : InfinitePlace K, |2 * t + (τμ v - τν v)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    calc 1 + ∑ v : InfinitePlace K,
          (|t + (τμ v + τη v)| + |t - (τν v + τη v)| + (|mμ v + mη v| : ℝ) + (|mν v + mη v| : ℝ))
        ≤ 1 + (∑ v : InfinitePlace K, |2 * t + (τμ v - τν v)| + r * C₀) := by linarith
      _ ≤ (1 + r * C₀) * (1 + ∑ v : InfinitePlace K, |2 * t + (τμ v - τν v)|) := by
          nlinarith [mul_nonneg hr0 hC₀0]
      _ ≤ B * (1 + ∑ v : InfinitePlace K, |2 * t + (τμ v - τν v)|) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          rw [hB]; linarith

end Main

end R4TwistNorm

theorem solution
    (K : Type) [Field K] [NumberField K]
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (nρ : ℕ) (ρs : Fin nρ → ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (n₀ : ℕ) :
    ∃ (B : ℝ) (Ξ : Set ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ)), 0 ≤ B ∧ Ξ.Finite ∧
    (∀ ξ ∈ Ξ, IsUnitaryChar (𝓞 K) K ξ ∧ IsIdeleClassChar (𝓞 K) K ξ ∧
      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ z : ℂˣ) : ℂ)) ∧
    ∀ (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hram : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S₀ →
        NumberField.TateGlobal.IsUnramifiedCharAt μ v ∧ NumberField.TateGlobal.IsUnramifiedCharAt ν v)
      (_hρ : ∃ r r' : Fin nρ, ∀ v ∈ S₀, ∀ u : (v.adicCompletion K)ˣ,
        (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
          NumberField.TateGlobal.localChar μ v u = ρs r v u ∧ NumberField.TateGlobal.localChar ν v u = ρs r' v u)
      (τμ τν : InfinitePlace K → ℝ)
      (_hτμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τμ v : ℝ) : ℂ) * Complex.I))
      (_hτν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τν v : ℝ) : ℂ) * Complex.I))
      (mμ mν : InfinitePlace K → ℤ)
      (_hmμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ v))
      (_hmν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν v))
      (_hreal : ∀ v : InfinitePlace K, v.IsReal → (mμ v = 0 ∨ mμ v = 1) ∧ (mν v = 0 ∨ mν v = 1))
      (_hdiff : ∀ v : InfinitePlace K, v.IsComplex → |mμ v - mν v| ≤ (n₀ : ℤ)),
    ∃ (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τη : InfinitePlace K → ℝ) (mη : InfinitePlace K → ℤ),
      IsUnitaryChar (𝓞 K) K η ∧ IsIdeleClassChar (𝓞 K) K η ∧ Continuous η ∧
      (∀ v : HeightOneSpectrum (𝓞 K), NumberField.TateGlobal.IsUnramifiedCharAt η v) ∧
      (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar η v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τη v : ℝ) : ℂ) * Complex.I)) ∧
      (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar η v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mη v)) ∧
      (∀ v : InfinitePlace K, v.IsReal → mη v = 0) ∧
      μ * ν * η ^ 2 ∈ Ξ ∧
      (∀ v : InfinitePlace K, |τμ v + τν v + 2 * τη v| ≤ B) ∧
      (∀ v : InfinitePlace K, (|mμ v + mη v| : ℝ) ≤ B ∧ (|mν v + mη v| : ℝ) ≤ B) ∧
      (∀ t : ℝ, 1 + ∑ v : InfinitePlace K,
          (|t + (τμ v + τη v)| + |t - (τν v + τη v)| + (|mμ v + mη v| : ℝ) + (|mν v + mη v| : ℝ)) ≤
        B * (1 + ∑ v : InfinitePlace K, |2 * t + (τμ v - τν v)|)) :=
  R4TwistNorm.main K S₀ nρ ρs n₀

end S_NumberField_TateGlobal_exists_finite_forall_exists_isUnramifiedCharAt_mul_mul_pow_two_mem_abs_archParam_le_of_localChar_eq
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_finite_forall_exists_isUnramifiedCharAt_mul_mul_pow_two_mem_abs_archParam_le_of_localChar_eq (solution)
