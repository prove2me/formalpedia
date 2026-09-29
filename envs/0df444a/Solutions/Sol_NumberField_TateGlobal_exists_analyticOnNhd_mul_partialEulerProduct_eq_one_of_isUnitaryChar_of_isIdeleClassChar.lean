-- Prove2me | solution 1 for NumberField.TateGlobal.exists_analyticOnNhd_mul_partialEulerProduct_eq_one_of_isUnitaryChar_of_isIdeleClassChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/5e594624-e33a-5b7b-8dbf-4ba5c6586a52

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Theorems.Thm_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct
import Theorems.Thm_NumberField_TateGlobal_not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar
import Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
import Theorems.Thm_NumberField_TateGlobal_ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_analyticOnNhd_mul_partialEulerProduct_eq_one_of_isUnitaryChar_of_isIdeleClassChar
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false
set_option linter.unusedVariables false

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal Complex Filter NumberField.AdelicLevel
open scoped Topology

noncomputable section

namespace R4InvL

section normPow
variable (K : Type) [Field K] [NumberField K]

theorem isIdeleClassChar_normPowChar (t : ℝ) : IsIdeleClassChar (𝓞 K) K (normPowChar K t) := by
  intro u
  apply normPowChar_eq_one_of_ideleNorm_eq_one
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := ⟨rfl⟩
  have := NumberField.AdeleRing.distribHaarChar_algebraMap K u
  unfold ideleNorm
  rw [show (Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom u) =
    Units.map (↑(algebraMap K (AdeleRing (𝓞 K) K))) u from rfl] at this
  rw [this]; simp

theorem isUnitaryChar_normPowChar (t : ℝ) : IsUnitaryChar (𝓞 K) K (normPowChar K t) :=
  fun x => norm_coe_normPowChar_apply t x

theorem continuous_normPowChar (t : ℝ) :
    Continuous (normPowChar K t : (AdeleRing (𝓞 K) K)ˣ → ℂˣ) := by
  have hc := NumberField.TateGlobal.continuous_ideleNorm K
  have hval : Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((normPowChar K t x : ℂˣ) : ℂ) := by
    simp_rw [coe_normPowChar_apply]
    refine Continuous.cpow (continuous_ofReal.comp hc) continuous_const fun x => ?_
    exact Or.inl (by simpa using ideleNorm_pos x)
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  have : (fun x : (AdeleRing (𝓞 K) K)ˣ => ((normPowChar K t x)⁻¹ : ℂˣ).val) =
      fun x => (((normPowChar K t x : ℂˣ) : ℂ))⁻¹ := by
    funext x; simp
  rw [this]
  exact hval.inv₀ fun x => Units.ne_zero _

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem absNorm_cast_ne_zero (v : HeightOneSpectrum (𝓞 K)) : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by have := two_le_absNorm K v; omega)

theorem isUnramifiedCharAt_normPowChar (t : ℝ) (v : HeightOneSpectrum (𝓞 K)) :
    IsUnramifiedCharAt (normPowChar K t) v := by
  by_contra h
  have key := NumberField.TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg K t v
  rw [if_neg h] at key
  have : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(Complex.I * t)) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl (absNorm_cast_ne_zero K v)
  exact this key.symm

theorem normPowChar_uniformizerIdele (t : ℝ) (v : HeightOneSpectrum (𝓞 K)) :
    ((normPowChar K t (uniformizerIdele K v) : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(Complex.I * t)) := by
  have key := NumberField.TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg K t v
  rwa [if_pos (isUnramifiedCharAt_normPowChar K t v)] at key

end normPow

section Local
variable {K : Type} [Field K] [NumberField K]

theorem localChar_mul (χ ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (t : (v.adicCompletion K)ˣ) : localChar (χ * ψ) v t = localChar χ v t * localChar ψ v t := by
  simp [localChar_apply]

theorem isUnramifiedCharAt_mul {χ ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {v : HeightOneSpectrum (𝓞 K)}
    (hχ : IsUnramifiedCharAt χ v) (hψ : IsUnramifiedCharAt ψ v) : IsUnramifiedCharAt (χ * ψ) v := by
  intro t h1 h2
  rw [localChar_mul, hχ t h1 h2, hψ t h1 h2, one_mul]

theorem isUnramifiedCharAt_of_mul {χ ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {v : HeightOneSpectrum (𝓞 K)}
    (h : IsUnramifiedCharAt (χ * ψ) v) (hψ : IsUnramifiedCharAt ψ v) : IsUnramifiedCharAt χ v := by
  intro t h1 h2
  have := h t h1 h2
  rwa [localChar_mul, hψ t h1 h2, mul_one] at this

theorem localChar_eq_apply_uniformizerIdele {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {v : HeightOneSpectrum (𝓞 K)}
    (hχ : IsUnramifiedCharAt χ v) (ϖ : (v.adicCompletion K)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)) :
    localChar χ v ϖ = χ (uniformizerIdele K v) := by
  have huU : Valued.v (uniformizerUnit K v : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ) :=
    valued_uniformizerUnit K v
  set u : (v.adicCompletion K)ˣ := ϖ * (uniformizerUnit K v)⁻¹ with hu_def
  have hne : (Valued.v (uniformizerUnit K v : v.adicCompletion K)) ≠ 0 := by
    rw [huU]; exact WithZero.coe_ne_zero
  have hu : Valued.v (u : v.adicCompletion K) = 1 := by
    rw [hu_def, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hϖ, huU]
    exact mul_inv_cancel₀ WithZero.coe_ne_zero
  have h1 : (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu]
  have h2 : ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  have hkill := hχ u h1 h2
  have hϖeq : ϖ = u * uniformizerUnit K v := by rw [hu_def, inv_mul_cancel_right]
  calc localChar χ v ϖ = localChar χ v (u * uniformizerUnit K v) := by rw [← hϖeq]
    _ = localChar χ v u * localChar χ v (uniformizerUnit K v) := map_mul _ _ _
    _ = χ (uniformizerIdele K v) := by rw [hkill, one_mul]; rfl

end Local

section Main

variable (F : Type) [Field F] [NumberField F]

theorem hasProd_inv₀ {ι : Type*} {f : ι → ℂ} {a : ℂ} (hf : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun i => (f i)⁻¹) a⁻¹ :=
  hf.inv₀ ha

theorem inv_tprod_inv_eq_tprod {ι : Type*} {g : ι → ℂ} (hg : Multipliable g) (hne : ∏' i, g i ≠ 0) :
    (∏' i, (g i)⁻¹)⁻¹ = ∏' i, g i := by
  obtain ⟨A, hA⟩ := hg
  rw [hA.tprod_eq] at hne ⊢
  rw [(hasProd_inv₀ hA hne).tprod_eq, inv_inv]

theorem nonneg_neg_of_not_pos (o : WithTop ℤ) (h : ¬ 0 < o) : 0 ≤ -o := by
  have ho : o ≤ 0 := not_lt.mp h
  have hne : o ≠ ⊤ := by rintro rfl; simp at ho
  obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.mp hne
  have : (n : WithTop ℤ) ≤ 0 := ho
  rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
  norm_cast at this ⊢
  omega

theorem main
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    (hχF : IsIdeleClassChar (𝓞 F) F χ) :
    ∃ (U : Set ℂ) (P : ℂ → ℂ), IsOpen U ∧ {w : ℂ | 1 ≤ w.re} ⊆ U ∧ AnalyticOnNhd ℂ P U ∧
      ∀ w : ℂ, 1 < w.re →
        P w * (∏' v : {v // v ∉ S},
          (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹) = 1 := by
  classical

  set q : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} → ℂ := fun x => ((Ideal.absNorm x.1.asIdeal : ℕ) : ℂ) with hq
  have hq0 : ∀ x, q x ≠ 0 := fun x => absNorm_cast_ne_zero F x.1
  have hq2 : ∀ x, (2 : ℝ) ≤ ‖q x‖ := by
    intro x
    simp only [hq, Complex.norm_natCast]
    exact_mod_cast two_le_absNorm F x.1
  set a : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} → ℂ := fun x => ((localChar χ x.1 (ϖ x.1) : ℂˣ) : ℂ) with ha
  have ha1 : ∀ x, ‖a x‖ = 1 := fun x => by simp only [ha, localChar_apply]; exact hχu _
  have ha1' : ∀ x, ‖a x‖ ≤ 1 := fun x => (ha1 x).le

  set fac : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} → ℂ → ℂ := fun x w => (1 - a x * q x ^ (-w))⁻¹ with hfac
  set Z : ℂ → ℂ := fun w => ∏' x : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, fac x w with hZ

  obtain ⟨hZmul, hZdiff, hZne⟩ :=
    NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one F S a ha1'

  obtain ⟨L, hLmer, hLZ⟩ :=
    NumberField.TateGlobal.exists_meromorphicOn_eq_partialEulerProduct F S ϖ hϖ χ hχc hχu hχF
  have hLZ' : ∀ w : ℂ, 1 < w.re → L w = Z w := by
    intro w hw
    rw [hLZ w hw]
    have h1 : (∏' x : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (1 - a x * q x ^ (-w)))
        = ∏' x : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (fac x w)⁻¹ :=
      tprod_congr fun x => by simp only [hfac, inv_inv]
    show (∏' x : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (1 - a x * q x ^ (-w)))⁻¹ = Z w
    rw [h1]
    exact inv_tprod_inv_eq_tprod (hZmul w hw) (hZne w hw)
  set V₁ : Set ℂ := {w : ℂ | 1 < w.re} with hV₁
  have hV₁o : IsOpen V₁ := isOpen_lt continuous_const Complex.continuous_re
  have hLdiff : DifferentiableOn ℂ L V₁ := hZdiff.congr fun w hw => hLZ' w hw
  have hLan : AnalyticOnNhd ℂ L V₁ := hLdiff.analyticOnNhd hV₁o

  have hmerInv : MeromorphicOn L⁻¹ Set.univ := hLmer.inv
  set P : ℂ → ℂ := toMeromorphicNFOn L⁻¹ Set.univ with hP
  set U : Set ℂ := {w : ℂ | AnalyticAt ℂ P w} with hU
  have hUo : IsOpen U := isOpen_analyticAt ℂ P
  have hPan : AnalyticOnNhd ℂ P U := fun w hw => hw

  have hV₁P : ∀ w ∈ V₁, AnalyticAt ℂ P w ∧ P w = (L w)⁻¹ := by
    intro w hw
    have hLw : L w ≠ 0 := by rw [hLZ' w hw]; exact hZne w hw
    have hinv_an : AnalyticAt ℂ L⁻¹ w := (hLan w hw).inv hLw
    have hNF : MeromorphicNFAt L⁻¹ w := hinv_an.meromorphicNFAt
    have h1 : P =ᶠ[𝓝 w] toMeromorphicNFAt L⁻¹ w :=
      toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hmerInv (Set.mem_univ w)
    have h2 : toMeromorphicNFAt L⁻¹ w = L⁻¹ := toMeromorphicNFAt_eq_self.2 hNF
    rw [h2] at h1
    exact ⟨(analyticAt_congr h1).mpr hinv_an, h1.eq_of_nhds⟩

  have key : ∀ w₀ : ℂ, w₀.re = 1 → ¬ Tendsto L (𝓝[≠] w₀) (𝓝 0) := by
    intro w₀ hw₀ hT
    set t : ℝ := w₀.im with ht
    have hw₀eq : w₀ = 1 + t * I := by
      apply Complex.ext <;> simp [ht, hw₀]

    set χt : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ := χ * normPowChar F t with hχt
    have hχtF : IsIdeleClassChar (𝓞 F) F χt := by
      intro u
      simp only [hχt, MonoidHom.mul_apply, hχF u, isIdeleClassChar_normPowChar F t u, mul_one]
    have hχtc : Continuous χt := by
      have : (χt : (AdeleRing (𝓞 F) F)ˣ → ℂˣ) = fun x => χ x * normPowChar F t x := by
        funext x; simp [hχt]
      rw [this]
      exact hχc.mul (continuous_normPowChar F t)
    have hχtu : IsUnitaryChar (𝓞 F) F χt := by
      intro x
      simp only [hχt, MonoidHom.mul_apply, Units.val_mul, norm_mul, hχu x, isUnitaryChar_normPowChar F t x,
        mul_one]

    have hunr : ∀ v, IsUnramifiedCharAt χt v ↔ IsUnramifiedCharAt χ v := fun v =>
      ⟨fun h => isUnramifiedCharAt_of_mul h (isUnramifiedCharAt_normPowChar F t v),
        fun h => isUnramifiedCharAt_mul h (isUnramifiedCharAt_normPowChar F t v)⟩

    obtain ⟨Sram, hSram⟩ := NumberField.TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous F χ hχc
    set sram : Finset {v : HeightOneSpectrum (𝓞 F) // v ∉ S} :=
      (Sram.filter fun v => ¬ IsUnramifiedCharAt χ v).subtype (fun v => v ∉ S) with hsram
    have hmem_sram : ∀ x : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, x ∈ sram ↔ ¬ IsUnramifiedCharAt χ x.1 := by
      intro x
      simp only [hsram, Finset.mem_subtype, Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        by_contra hx
        exact h (hSram x.1 hx)

    set c : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} → ℂ := fun x =>
      if IsUnramifiedCharAt χt x.1 then ((χt (uniformizerIdele F x.1) : ℂˣ) : ℂ) else 0 with hc
    have hc1 : ∀ x, ‖c x‖ ≤ 1 := by
      intro x
      simp only [hc]
      split_ifs
      · exact (hχtu _).le
      · simp
    set ET : ℝ → ℂ := fun σ => ∏' x : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
      (1 - c x * q x ^ (-(σ : ℂ)))⁻¹ with hET
    obtain ⟨hEmul, -, hEne⟩ :=
      NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one F S c hc1

    set γ : ℝ → ℂ := fun σ => (σ : ℂ) + t * I with hγ
    have hγc : Continuous γ := (continuous_ofReal).add continuous_const
    have hγre : ∀ σ : ℝ, (γ σ).re = σ := by intro σ; simp [hγ]
    have hγ1 : γ 1 = w₀ := by rw [hw₀eq]; simp [hγ]

    have hterm_unr : ∀ (σ : ℝ) (x : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}), IsUnramifiedCharAt χ x.1 →
        (1 - c x * q x ^ (-(σ : ℂ)))⁻¹ = fac x (γ σ) := by
      intro σ x hx
      have hxt : IsUnramifiedCharAt χt x.1 := (hunr x.1).mpr hx
      have hcx : c x = a x * q x ^ (-(I * t)) := by
        have h1 : c x = ((χt (uniformizerIdele F x.1) : ℂˣ) : ℂ) := by simp only [hc, if_pos hxt]
        rw [h1, hχt, MonoidHom.mul_apply, Units.val_mul, normPowChar_uniformizerIdele,
          ← localChar_eq_apply_uniformizerIdele hx (ϖ x.1) (hϖ x.1)]
      have he : -(I * t) + -(σ : ℂ) = -γ σ := by simp only [hγ]; ring
      simp only [hfac]
      rw [hcx, mul_assoc, ← cpow_add _ _ (hq0 x), he]

    have hterm_ram : ∀ (σ : ℝ) (x : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}), ¬ IsUnramifiedCharAt χ x.1 →
        (1 - c x * q x ^ (-(σ : ℂ)))⁻¹ = 1 := by
      intro σ x hx
      have hxt : ¬ IsUnramifiedCharAt χt x.1 := fun h => hx ((hunr x.1).mp h)
      simp only [hc, if_neg hxt, zero_mul, sub_zero, inv_one]

    set R : ℂ → ℂ := fun w => ∏ x ∈ sram, fac x w with hR
    have hfac_ne : ∀ (x : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) (w : ℂ), 0 < w.re → fac x w ≠ 0 := by
      intro x w hw
      simp only [hfac]
      refine inv_ne_zero (sub_ne_zero.mpr ?_)
      intro h
      have hn : ‖a x * q x ^ (-w)‖ < 1 := by
        rw [norm_mul, ha1 x, one_mul]
        have hqpos : 0 < ((Ideal.absNorm x.1.asIdeal : ℕ) : ℝ) := by
          have := two_le_absNorm F x.1; positivity
        have : ‖q x ^ (-w)‖ = ((Ideal.absNorm x.1.asIdeal : ℕ) : ℝ) ^ (-w.re) := by
          simp only [hq]
          rw [Complex.norm_natCast_cpow_of_pos (by have := two_le_absNorm F x.1; omega)]
          simp
        rw [this]
        have h1 : (1 : ℝ) < ((Ideal.absNorm x.1.asIdeal : ℕ) : ℝ) := by
          have := two_le_absNorm F x.1; exact_mod_cast (by omega : 1 < Ideal.absNorm x.1.asIdeal)
        exact Real.rpow_lt_one_of_one_lt_of_neg h1 (by linarith)
      rw [← h] at hn
      simp at hn
    have hfac_cont : ∀ (x : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) (w : ℂ), 0 < w.re →
        ContinuousAt (fac x) w := by
      intro x w hw
      simp only [hfac]
      have h1 : Continuous fun w : ℂ => 1 - a x * q x ^ (-w) :=
        continuous_const.sub (continuous_const.mul (continuous_neg.const_cpow (Or.inl (hq0 x))))
      refine (h1.continuousAt).inv₀ (sub_ne_zero.mpr ?_)
      intro h
      exact hfac_ne x w hw (by simp only [hfac]; rw [← h, sub_self, inv_zero])
    have hRne : R w₀ ≠ 0 := by
      simp only [hR]
      exact Finset.prod_ne_zero_iff.mpr fun x hx => hfac_ne x w₀ (by rw [hw₀]; exact one_pos)
    have hRcont : ContinuousAt R w₀ := by
      simp only [hR]
      have := tendsto_finsetProd sram (fun x _ => (hfac_cont x w₀ (by rw [hw₀]; exact one_pos)).tendsto)
      exact this

    have hfactor : ∀ σ : ℝ, 1 < σ → Z (γ σ) = ET σ * R (γ σ) := by
      intro σ hσ
      set r : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} → ℂ := fun x =>
        if IsUnramifiedCharAt χ x.1 then 1 else fac x (γ σ) with hr
      have hr1 : ∀ x ∉ sram, r x = 1 := by
        intro x hx
        have : IsUnramifiedCharAt χ x.1 := by
          by_contra h; exact hx ((hmem_sram x).mpr h)
        simp only [hr, if_pos this]
      have hrmul : Multipliable r := multipliable_of_ne_finset_one hr1
      have hσ' : 1 < ((σ : ℂ)).re := by simpa using hσ
      have hEmulσ := hEmul (σ : ℂ) hσ'
      have hterm : ∀ x, fac x (γ σ) = (1 - c x * q x ^ (-(σ : ℂ)))⁻¹ * r x := by
        intro x
        by_cases hx : IsUnramifiedCharAt χ x.1
        · rw [hterm_unr σ x hx]; simp only [hr, if_pos hx, mul_one]
        · rw [hterm_ram σ x hx]; simp only [hr, if_neg hx, one_mul]
      have hZeq : Z (γ σ) = ∏' x, (1 - c x * q x ^ (-(σ : ℂ)))⁻¹ * r x := by
        simp only [hZ]
        exact tprod_congr hterm
      rw [hZeq, hEmulσ.tprod_mul hrmul, tprod_eq_prod hr1]
      simp only [hET, hR]
      congr 1
      refine Finset.prod_congr rfl fun x hx => ?_
      simp only [hr, if_neg ((hmem_sram x).mp hx)]

    have hγlim : Tendsto γ (𝓝[>] (1 : ℝ)) (𝓝[≠] w₀) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have := hγc.tendsto (1 : ℝ)
        rw [hγ1] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with σ hσ
        intro h
        have : (γ σ).re = w₀.re := by rw [h]
        rw [hγre, hw₀] at this
        exact (ne_of_gt hσ) this
    have hLlim : Tendsto (fun σ : ℝ => L (γ σ)) (𝓝[>] (1 : ℝ)) (𝓝 0) := hT.comp hγlim
    have hRlim : Tendsto (fun σ : ℝ => (R (γ σ))⁻¹) (𝓝[>] (1 : ℝ)) (𝓝 ((R w₀)⁻¹)) := by
      have h1 : Tendsto (fun σ : ℝ => R (γ σ)) (𝓝[>] (1 : ℝ)) (𝓝 (R w₀)) := by
        have := hγc.tendsto (1 : ℝ)
        rw [hγ1] at this
        exact (hRcont.tendsto.comp this).mono_left nhdsWithin_le_nhds
      exact h1.inv₀ hRne
    have hprod : Tendsto (fun σ : ℝ => L (γ σ) * (R (γ σ))⁻¹) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      have := hLlim.mul hRlim
      rwa [zero_mul] at this
    have hETlim : Tendsto ET (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      refine hprod.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      have hσ1 : 1 < σ := hσ
      have hRσ : R (γ σ) ≠ 0 := by
        simp only [hR]
        exact Finset.prod_ne_zero_iff.mpr fun x hx => hfac_ne x _ (by rw [hγre]; linarith)
      rw [hLZ' (γ σ) (by rw [hγre]; exact hσ1), hfactor σ hσ1, mul_inv_cancel_right₀ hRσ]

    exact NumberField.TateGlobal.not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar F χt hχtF hχtc hχtu S
      hETlim

  have hline : ∀ w₀ : ℂ, w₀.re = 1 → AnalyticAt ℂ P w₀ := by
    intro w₀ hw₀
    have hPNF : MeromorphicNFAt P w₀ := meromorphicNFOn_toMeromorphicNFOn L⁻¹ Set.univ (Set.mem_univ w₀)
    rw [← hPNF.meromorphicOrderAt_nonneg_iff_analyticAt]
    have h1 : meromorphicOrderAt P w₀ = meromorphicOrderAt L⁻¹ w₀ :=
      meromorphicOrderAt_congr (hmerInv.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ w₀))
    rw [h1, meromorphicOrderAt_inv]
    refine nonneg_neg_of_not_pos _ fun hpos => ?_
    exact key w₀ hw₀ (tendsto_zero_of_meromorphicOrderAt_pos hpos)

  refine ⟨U, P, hUo, ?_, hPan, ?_⟩
  · intro w hw
    have hw' : (1 : ℝ) ≤ w.re := hw
    rcases hw'.eq_or_lt with h | h
    · exact hline w h.symm
    · exact (hV₁P w h).1
  · intro w hw
    have hLw : L w ≠ 0 := by rw [hLZ' w hw]; exact hZne w hw
    rw [(hV₁P w hw).2, hLZ' w hw]
    exact inv_mul_cancel₀ (hZne w hw)

end Main

end R4InvL

end

open NumberField AutomorphicForm IsDedekindDomain

theorem solution
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    (hχF : IsIdeleClassChar (𝓞 F) F χ) :
    ∃ (U : Set ℂ) (P : ℂ → ℂ), IsOpen U ∧ {w : ℂ | 1 ≤ w.re} ⊆ U ∧ AnalyticOnNhd ℂ P U ∧
      ∀ w : ℂ, 1 < w.re →
        P w * (∏' v : {v // v ∉ S},
          (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹) = 1 :=
  R4InvL.main F S ϖ hϖ χ hχc hχu hχF

end S_NumberField_TateGlobal_exists_analyticOnNhd_mul_partialEulerProduct_eq_one_of_isUnitaryChar_of_isIdeleClassChar
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_analyticOnNhd_mul_partialEulerProduct_eq_one_of_isUnitaryChar_of_isIdeleClassChar (solution)
