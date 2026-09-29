-- Prove2me | solution 1 for NumberField.TateGlobal.exists_pos_forall_partialEulerProduct_continuation_ne_zero_of_norm_sub_le_of_sq_eq_normPowChar_of_admitsModulus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/fd132c63-6dde-5310-afc3-d586a7a938b6

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_NarrowRayClassGroup
import Theorems.Thm_NumberField_TateGlobal_not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar
import Theorems.Thm_NumberField_TateGlobal_exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one
import Theorems.Thm_NumberField_TateGlobal_ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_HeckeCharacter_raySymbol_apply_uniformizerIdele_eq_prod_archLocalChar_neg_one_of_admitsModulus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_pos_forall_partialEulerProduct_continuation_ne_zero_of_norm_sub_le_of_sq_eq_normPowChar_of_admitsModulus
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq"

set_option autoImplicit false

noncomputable section

namespace R4LDD2

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal MeasureTheory Complex Filter Topology
open scoped NNReal nonZeroDivisors

section NormPow

variable (K : Type) [Field K] [NumberField K]

theorem ofReal_ideleNorm_ne_zero (x : (AdeleRing (𝓞 K) K)ˣ) : ((ideleNorm K x : ℝ) : ℂ) ≠ 0 :=
  ofReal_ne_zero.2 (ideleNorm_pos x).ne'

theorem normPowChar_mul (a b : ℝ) : normPowChar K a * normPowChar K b = normPowChar K (a + b) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [MonoidHom.mul_apply, Units.val_mul, coe_normPowChar_apply, coe_normPowChar_apply,
    coe_normPowChar_apply, ← cpow_add _ _ (ofReal_ideleNorm_ne_zero K x)]
  congr 1
  push_cast
  ring

theorem isIdeleClassChar_normPowChar (t : ℝ) : IsIdeleClassChar (𝓞 K) K (normPowChar K t) := by
  intro u
  apply normPowChar_eq_one_of_ideleNorm_eq_one
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := ⟨rfl⟩
  have := NumberField.AdeleRing.distribHaarChar_algebraMap K u
  unfold ideleNorm
  rw [show (Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom u) =
    Units.map (↑(algebraMap K (AdeleRing (𝓞 K) K))) u from rfl] at this
  rw [this]
  simp

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

theorem ideleNorm_eq_one_of_forall_valued_eq_one (u : (AdeleRing (𝓞 K) K)ˣ)
    (h1 : (u : AdeleRing (𝓞 K) K).1 = 1)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v ((u : AdeleRing (𝓞 K) K).2 v) = 1) :
    ideleNorm K u = 1 := by
  unfold ideleNorm
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm K u]
  have ha : ∏ w : InfinitePlace K, ‖(u : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult = 1 :=
    Finset.prod_eq_one fun w _ => by
      rw [h1, show (1 : InfiniteAdeleRing K) w = 1 from rfl, norm_one, one_pow]
  have hb : ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(u : AdeleRing (𝓞 K) K).2 v‖ = 1 := by
    rw [finprod_congr (g := fun _ => (1 : ℝ)) fun v => ?_, finprod_one]
    rw [NumberField.FinitePlace.norm_def, h2 v, map_one, NNReal.coe_one]
  rw [ha, hb, one_mul]

theorem admitsModulus_normPowChar (t : ℝ) (𝔣 : Ideal (𝓞 K)) :
    HeckeCharacter.AdmitsModulus K (normPowChar K t) 𝔣 := fun u h1 h2 =>
  normPowChar_eq_one_of_ideleNorm_eq_one t
    (ideleNorm_eq_one_of_forall_valued_eq_one K u h1 fun v => (h2 v).1)

theorem natCast_absNorm_ne_zero (v : HeightOneSpectrum (𝓞 K)) :
    ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem isUnramifiedCharAt_normPowChar (t : ℝ) (v : HeightOneSpectrum (𝓞 K)) :
    IsUnramifiedCharAt (normPowChar K t) v := by
  by_contra h
  have := NumberField.TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
    K t v
  rw [if_neg h] at this
  exact (natCast_absNorm_ne_zero K v) ((cpow_eq_zero_iff _ _).1 this.symm).1

theorem coe_normPowChar_uniformizerIdele (t : ℝ) (v : HeightOneSpectrum (𝓞 K)) :
    ((normPowChar K t (uniformizerIdele K v) : ℂˣ) : ℂ)
      = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(I * t)) := by
  have := NumberField.TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
    K t v
  rwa [if_pos (isUnramifiedCharAt_normPowChar K t v)] at this

theorem isUnramifiedCharAt_mul {χ η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (v : HeightOneSpectrum (𝓞 K))
    (hχ : IsUnramifiedCharAt χ v) (hη : IsUnramifiedCharAt η v) : IsUnramifiedCharAt (χ * η) v := by
  intro t ht hti
  rw [localChar_apply, MonoidHom.mul_apply, ← localChar_apply, ← localChar_apply, hχ t ht hti, hη t ht hti,
    mul_one]

theorem isIdeleClassChar_mul_normPowChar {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (hχ : IsIdeleClassChar (𝓞 K) K χ) (t : ℝ) : IsIdeleClassChar (𝓞 K) K (χ * normPowChar K t) :=
  fun u => by rw [MonoidHom.mul_apply, hχ u, isIdeleClassChar_normPowChar K t u, one_mul]

theorem continuous_mul_normPowChar {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχ : Continuous χ) (t : ℝ) :
    Continuous (χ * normPowChar K t : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := by
  show Continuous fun x => (χ * normPowChar K t) x
  simp only [MonoidHom.mul_apply]
  exact hχ.mul (continuous_normPowChar K t)

theorem isUnitaryChar_mul_normPowChar {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχ : IsUnitaryChar (𝓞 K) K χ)
    (t : ℝ) : IsUnitaryChar (𝓞 K) K (χ * normPowChar K t) := fun x => by
  rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hχ x, isUnitaryChar_normPowChar K t x, one_mul]

theorem pow_apply' (f : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (n : ℕ) (x : (AdeleRing (𝓞 K) K)ˣ) :
    (f ^ n) x = f x ^ n := rfl

theorem one_apply' (x : (AdeleRing (𝓞 K) K)ˣ) : (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) x = 1 := rfl

end NormPow

section Finiteness

variable (K : Type) [Field K] [NumberField K]

structure Adm (T : Finset (HeightOneSpectrum (𝓞 K))) (𝔣 : Ideal (𝓞 K))
    (ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : Prop where
  icc : IsIdeleClassChar (𝓞 K) K ψ
  cont : Continuous ψ
  unit : IsUnitaryChar (𝓞 K) K ψ
  ne : ∃ x ∈ normOneIdeles K, ψ x ≠ 1
  modl : HeckeCharacter.AdmitsModulus K ψ 𝔣
  unr : ∀ v ∉ T, IsUnramifiedCharAt ψ v
  sq : ψ ^ 2 = 1

def coef (T : Finset (HeightOneSpectrum (𝓞 K))) (ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) :
    {v : HeightOneSpectrum (𝓞 K) // v ∉ T} → ℂ :=
  fun v => ((ψ (uniformizerIdele K v.1) : ℂˣ) : ℂ)

def E (T : Finset (HeightOneSpectrum (𝓞 K))) (c : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} → ℂ) (s : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
    (1 - c v * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹

theorem finite_setOf_pow_eq_one (n : ℕ) (hn : 0 < n) : {z : ℂˣ | z ^ n = 1}.Finite := by
  have h1 : {w : ℂ | w ^ n = 1}.Finite := by
    refine (Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.subset fun w hw => ?_
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
    exact hw
  refine (h1.preimage Units.val_injective.injOn).subset fun z hz => ?_
  show ((z : ℂˣ) : ℂ) ^ n = 1
  have hz' : z ^ n = 1 := hz
  rw [← Units.val_pow_eq_pow_val, hz', Units.val_one]

theorem raySymbol_eq_one {T : Finset (HeightOneSpectrum (𝓞 K))} {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    {ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hψ : Adm K T 𝔣 ψ)
    (α : 𝓞 K) (hα : α ≠ 0) (hα1 : α - 1 ∈ 𝔣) (hpos : ∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) :
    Deep.NTSupply.raySymbol K (fun v => ψ (uniformizerIdele K v))
      ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = 1 := by
  have hfin : IsOfFinOrder ψ := isOfFinOrder_iff_pow_eq_one.2 ⟨2, two_pos, hψ.sq⟩
  rw [HeckeCharacter.raySymbol_apply_uniformizerIdele_eq_prod_archLocalChar_neg_one_of_admitsModulus K ψ
    hψ.icc hfin 𝔣 h𝔣 hψ.modl α hα hα1]
  refine Finset.prod_eq_one fun τ hτ => ?_
  exact absurd (Finset.mem_filter.1 hτ).2 (not_lt.2 (hpos τ).le)

theorem finite_range_coef (T : Finset (HeightOneSpectrum (𝓞 K))) (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥) :
    (Set.range fun a : {ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ // Adm K T 𝔣 ψ} => coef K T a.1).Finite := by
  classical
  haveI : Finite (Deep.NTSupply.NarrowRayClassGroup K 𝔣) := Deep.NTSupply.finite K h𝔣
  have hD : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔣}.Finite :=
    Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot])
  haveI : Finite {v : HeightOneSpectrum (𝓞 K) // v.asIdeal ∣ 𝔣} := hD.to_subtype

  let desc : {ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ // Adm K T 𝔣 ψ} →
      (Deep.NTSupply.NarrowRayClassGroup K 𝔣 →* ℂˣ) := fun a =>
    Deep.NTSupply.raySymbolDescend K (fun v => a.1 (uniformizerIdele K v)) (raySymbol_eq_one K h𝔣 a.2)

  let key : {ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ // Adm K T 𝔣 ψ} →
      ({v : HeightOneSpectrum (𝓞 K) // v.asIdeal ∣ 𝔣} → ℂˣ) × (Deep.NTSupply.NarrowRayClassGroup K 𝔣 → ℂˣ) :=
    fun a => (fun d => a.1 (uniformizerIdele K d.1), fun g => desc a g)
  have hn : 0 < Nat.card (Deep.NTSupply.NarrowRayClassGroup K 𝔣) := Nat.card_pos
  have hkey : (Set.range key).Finite := by
    refine ((Set.Finite.pi fun _ => finite_setOf_pow_eq_one 2 two_pos).prod
      (Set.Finite.pi fun _ => finite_setOf_pow_eq_one _ hn)).subset ?_
    rintro _ ⟨a, rfl⟩
    refine Set.mem_prod.2 ⟨Set.mem_univ_pi.2 fun d => ?_, Set.mem_univ_pi.2 fun g => ?_⟩
    · show a.1 (uniformizerIdele K d.1) ^ 2 = 1
      rw [← pow_apply', a.2.sq, one_apply']
    · show desc a g ^ Nat.card (Deep.NTSupply.NarrowRayClassGroup K 𝔣) = 1
      rw [← map_pow, pow_card_eq_one', map_one]
  let Φ : ({v : HeightOneSpectrum (𝓞 K) // v.asIdeal ∣ 𝔣} → ℂˣ) ×
      (Deep.NTSupply.NarrowRayClassGroup K 𝔣 → ℂˣ) → ({v : HeightOneSpectrum (𝓞 K) // v ∉ T} → ℂ) :=
    fun p v => if h : v.1.asIdeal ∣ 𝔣 then ((p.1 ⟨v.1, h⟩ : ℂˣ) : ℂ)
      else ((p.2 (Deep.NTSupply.primeClass K 𝔣 v.1 h) : ℂˣ) : ℂ)
  have hcomp : (fun a : {ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ // Adm K T 𝔣 ψ} => coef K T a.1) = Φ ∘ key := by
    funext a
    funext v
    show ((a.1 (uniformizerIdele K v.1) : ℂˣ) : ℂ) = Φ (key a) v
    simp only [Φ, key]
    split_ifs with h
    · rfl
    · show _ = ((desc a (Deep.NTSupply.primeClass K 𝔣 v.1 h) : ℂˣ) : ℂ)
      rw [Deep.NTSupply.raySymbolDescend_primeClass]
  rw [hcomp, Set.range_comp]
  exact hkey.image Φ

end Finiteness

section Analytic

variable (K : Type) [Field K] [NumberField K]

def U : Set ℂ := {s : ℂ | 1 / 2 < s.re}

theorem isOpen_U : IsOpen U := isOpen_lt continuous_const continuous_re

theorem eqOn_of_eq_of_one_lt_re {L₁ L₂ : ℂ → ℂ} (h₁ : DifferentiableOn ℂ L₁ U) (h₂ : DifferentiableOn ℂ L₂ U)
    (h : ∀ s : ℂ, 1 < s.re → L₁ s = L₂ s) : Set.EqOn L₁ L₂ U := by
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have h2 : (2 : ℂ) ∈ U := by show (1 / 2 : ℝ) < (2 : ℂ).re; norm_num
  have hev : L₁ =ᶠ[𝓝 (2 : ℂ)] L₂ := by
    have hV : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
    have h2V : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by show (1 : ℝ) < (2 : ℂ).re; norm_num
    exact Filter.eventuallyEq_of_mem (hV.mem_nhds h2V) fun s hs => h s hs
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (h₁.analyticOnNhd isOpen_U)
    (h₂.analyticOnNhd isOpen_U) hpre h2 hev

variable {K}

theorem ne_zero_on_line {T : Finset (HeightOneSpectrum (𝓞 K))} {𝔣 : Ideal (𝓞 K)}
    {ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hψ : Adm K T 𝔣 ψ)
    {L₀ : ℂ → ℂ} (hL₀d : Differentiable ℂ L₀) (hL₀E : ∀ s : ℂ, 1 < s.re → L₀ s = E K T (coef K T ψ) s)
    (u : ℝ) : L₀ (1 + u * I) ≠ 0 := by
  intro h0
  set ψu : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := ψ * normPowChar K u with hψu
  apply NumberField.TateGlobal.not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar K ψu
    (isIdeleClassChar_mul_normPowChar K hψ.icc u) (continuous_mul_normPowChar K hψ.cont u)
    (isUnitaryChar_mul_normPowChar K hψ.unit u) T
  have ht : Tendsto (fun σ : ℝ => L₀ ((σ : ℂ) + u * I)) (𝓝[>] 1) (𝓝 0) := by
    have hc : Continuous fun σ : ℝ => L₀ ((σ : ℂ) + u * I) :=
      hL₀d.continuous.comp (continuous_ofReal.add continuous_const)
    have := hc.tendsto 1
    simp only [ofReal_one] at this
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hσ' : 1 < ((σ : ℂ) + u * I).re := by simpa using hσ
  rw [hL₀E _ hσ']
  refine tprod_congr fun v => ?_
  rw [if_pos (isUnramifiedCharAt_mul K v.1 (hψ.unr v.1 v.2) (isUnramifiedCharAt_normPowChar K u v.1))]
  simp only [coef, hψu, MonoidHom.mul_apply, Units.val_mul, coe_normPowChar_uniformizerIdele]
  rw [mul_assoc, ← cpow_add _ _ (natCast_absNorm_ne_zero K v.1)]
  have hexp : -(I * (u : ℂ)) + -(σ : ℂ) = -((σ : ℂ) + u * I) := by
    ring
  rw [hexp]

def GoodRadius (T : Finset (HeightOneSpectrum (𝓞 K))) (c : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} → ℂ)
    (δ : ℝ) : Prop :=
  ∀ L : ℂ → ℂ, DifferentiableOn ℂ L U → (∀ s : ℂ, 1 < s.re → L s = E K T c s) →
    ∀ s : ℂ, ‖s - 1‖ ≤ δ → s ∈ U → L s ≠ 0

theorem exists_goodRadius {T : Finset (HeightOneSpectrum (𝓞 K))} {𝔣 : Ideal (𝓞 K)}
    {ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hψ : Adm K T 𝔣 ψ) :
    ∃ r : ℝ, 0 < r ∧ GoodRadius T (coef K T ψ) r := by
  obtain ⟨L₀, hL₀d, hL₀E⟩ :=
    NumberField.TateGlobal.exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one K ψ
      hψ.icc hψ.cont hψ.unit hψ.ne T
  have hL₀E' : ∀ s : ℂ, 1 < s.re → L₀ s = E K T (coef K T ψ) s := fun s hs => by
    rw [hL₀E s hs]
    exact tprod_congr fun v => by rw [if_pos (hψ.unr v.1 v.2)]; rfl
  have h1 : L₀ 1 ≠ 0 := by simpa using ne_zero_on_line hψ hL₀d hL₀E' 0
  have hev : ∀ᶠ s in 𝓝 (1 : ℂ), L₀ s ≠ 0 := hL₀d.continuous.continuousAt.eventually_ne h1
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε / 2, half_pos hε, fun L hLd hLE s hs hsU => ?_⟩
  have heq : Set.EqOn L L₀ U :=
    eqOn_of_eq_of_one_lt_re hLd hL₀d.differentiableOn fun z hz => by rw [hLE z hz, hL₀E' z hz]
  rw [heq hsU]
  exact hball (by rw [dist_eq_norm]; linarith)

variable (K)

theorem exists_delta (T : Finset (HeightOneSpectrum (𝓞 K))) (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
      ∀ ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, Adm K T 𝔣 ψ → GoodRadius T (coef K T ψ) δ := by
  have hF := finite_range_coef K T 𝔣 h𝔣
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∀ c ∈ Set.range (fun a : {ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ // Adm K T 𝔣 ψ} => coef K T a.1),
        GoodRadius T c δ := by
    rw [hF.eventually_all]
    rintro c ⟨a, rfl⟩
    obtain ⟨r, hr, hQ⟩ := exists_goodRadius a.2
    filter_upwards [Ioo_mem_nhdsGT hr] with δ hδ
    intro L hLd hLE s hs hsU
    exact hQ L hLd hLE s (hs.trans hδ.2.le) hsU
  have hev2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Set.Ioo 0 (1 / 2) := Ioo_mem_nhdsGT (by norm_num)
  obtain ⟨δ, hδQ, hδ0, hδ2⟩ := (hev.and hev2).exists
  exact ⟨δ, hδ0, hδ2, fun ψ hψ => hδQ _ ⟨⟨ψ, hψ⟩, rfl⟩⟩

end Analytic

section Modulus

variable (K : Type) [Field K] [NumberField K]

theorem idealMultiplicity_bot (v : HeightOneSpectrum (𝓞 K)) :
    HeckeCharacter.idealMultiplicity K v (⊥ : Ideal (𝓞 K)) = 0 := by
  classical
  unfold HeckeCharacter.idealMultiplicity
  rw [show (⊥ : Ideal (𝓞 K)) = 0 from rfl, Associates.mk_zero, Associates.factors_zero]
  unfold Associates.count
  rw [dif_pos (Associates.irreducible_mk.mpr v.irreducible)]
  rfl

theorem exists_ne_bot_admitsModulus (𝔣 : Ideal (𝓞 K)) :
    ∃ 𝔣' : Ideal (𝓞 K), 𝔣' ≠ ⊥ ∧ ∀ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ,
      HeckeCharacter.AdmitsModulus K χ 𝔣 → HeckeCharacter.AdmitsModulus K χ 𝔣' := by
  by_cases h : 𝔣 = ⊥
  · subst h
    refine ⟨⊤, bot_ne_top.symm, fun χ hχ u h1 h2 => hχ u h1 fun v => ⟨(h2 v).1, ?_⟩⟩
    rw [idealMultiplicity_bot, Nat.cast_zero, neg_zero, WithZero.exp_zero]
    exact Valuation.map_sub_le _ (h2 v).1.le (by rw [map_one])
  · exact ⟨𝔣, h, fun χ hχ => hχ⟩

end Modulus

section Main

variable (K : Type) [Field K] [NumberField K]

open scoped Classical in
theorem main (T : Finset (HeightOneSpectrum (𝓞 K))) (𝔣 : Ideal (𝓞 K)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
      ∀ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ), IsIdeleClassChar (𝓞 K) K χ → Continuous χ →
        IsUnitaryChar (𝓞 K) K χ → (∃ x ∈ normOneIdeles K, χ x ≠ 1) →
        HeckeCharacter.AdmitsModulus K χ 𝔣 → (∀ v ∉ T, IsUnramifiedCharAt χ v) →
      ∀ (θ : ℝ), χ ^ 2 = normPowChar K θ →
      ∀ (L : ℂ → ℂ), DifferentiableOn ℂ L {s : ℂ | 1 / 2 < s.re} →
        (∀ s : ℂ, 1 < s.re → L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
              (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) →
      ∀ s : ℂ, ‖s - (1 - θ / 2 * Complex.I)‖ ≤ δ → L s ≠ 0 := by
  obtain ⟨𝔣', h𝔣', hmodimp⟩ := exists_ne_bot_admitsModulus K 𝔣
  obtain ⟨δ, hδ0, hδ2, hQ⟩ := exists_delta K T 𝔣' h𝔣'
  refine ⟨δ, hδ0, hδ2, ?_⟩
  intro χ hχK hχc hχu hχ1 hmod hT θ hθ L hLd hLE s hs
  set ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := χ * normPowChar K (-(θ / 2)) with hψdef
  have hχψ : χ = ψ * normPowChar K (θ / 2) := by
    refine MonoidHom.ext fun x => ?_
    rw [MonoidHom.mul_apply, hψdef, MonoidHom.mul_apply, mul_assoc, ← MonoidHom.mul_apply (normPowChar K _),
      normPowChar_mul, neg_add_cancel, normPowChar_zero, one_apply', mul_one]
  have hAdm : Adm K T 𝔣' ψ :=
    { icc := isIdeleClassChar_mul_normPowChar K hχK _
      cont := continuous_mul_normPowChar K hχc _
      unit := isUnitaryChar_mul_normPowChar K hχu _
      ne := by
        obtain ⟨x, hx, hx1⟩ := hχ1
        refine ⟨x, hx, ?_⟩
        rwa [hψdef, MonoidHom.mul_apply,
          normPowChar_eq_one_of_ideleNorm_eq_one _ ((mem_normOneIdeles_iff x).1 hx), mul_one]
      modl := fun u h1 h2 => by
        rw [hψdef, MonoidHom.mul_apply, hmodimp χ hmod u h1 h2,
          admitsModulus_normPowChar K _ 𝔣' u h1 h2, one_mul]
      unr := fun v hv => isUnramifiedCharAt_mul K v (hT v hv) (isUnramifiedCharAt_normPowChar K _ v)
      sq := by
        refine MonoidHom.ext fun x => ?_
        have h2 : (χ ^ 2) x = normPowChar K θ x := by rw [hθ]
        rw [pow_apply'] at h2 ⊢
        rw [one_apply', hψdef, MonoidHom.mul_apply, mul_pow, h2, sq, ← MonoidHom.mul_apply,
          ← MonoidHom.mul_apply, normPowChar_mul, normPowChar_mul,
          show θ + (-(θ / 2) + -(θ / 2)) = 0 by ring, normPowChar_zero, one_apply'] }

  set M : ℂ → ℂ := fun z => L (z - θ / 2 * I) with hMdef
  have hMd : DifferentiableOn ℂ M U := by
    refine hLd.comp (differentiableOn_id.sub_const _) fun z hz => ?_
    simpa [U] using hz
  have hME : ∀ z : ℂ, 1 < z.re → M z = E K T (coef K T ψ) z := by
    intro z hz
    have hz' : 1 < (z - θ / 2 * I).re := by simpa using hz
    show L (z - θ / 2 * I) = _
    rw [hLE _ hz']
    refine tprod_congr fun v => ?_
    rw [if_pos (hT v.1 v.2), hχψ]
    simp only [coef, MonoidHom.mul_apply, Units.val_mul, coe_normPowChar_uniformizerIdele]
    rw [mul_assoc, ← cpow_add _ _ (natCast_absNorm_ne_zero K v.1),
      show -(I * ((θ / 2 : ℝ) : ℂ)) + -(z - θ / 2 * I) = -z by push_cast; ring]
  have hs' : ‖(s + θ / 2 * I) - 1‖ ≤ δ := by
    rwa [show s + θ / 2 * I - 1 = s - (1 - θ / 2 * I) by ring]
  have hsU : s + θ / 2 * I ∈ U := by
    show 1 / 2 < (s + θ / 2 * I).re
    have h1 : |(s + θ / 2 * I - 1).re| ≤ ‖s + θ / 2 * I - 1‖ := abs_re_le_norm _
    have h2 : (s + θ / 2 * I - 1).re = (s + θ / 2 * I).re - 1 := by simp
    rw [h2] at h1
    have := (abs_lt.1 (lt_of_le_of_lt (h1.trans hs') hδ2)).1
    linarith
  have h := hQ ψ hAdm M hMd hME (s + θ / 2 * I) hs' hsU
  simpa [hMdef] using h

end Main

end R4LDD2

end

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal

open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (T : Finset (HeightOneSpectrum (𝓞 K))) (𝔣 : Ideal (𝓞 K)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
      ∀ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ), IsIdeleClassChar (𝓞 K) K χ → Continuous χ →
        IsUnitaryChar (𝓞 K) K χ → (∃ x ∈ normOneIdeles K, χ x ≠ 1) →
        HeckeCharacter.AdmitsModulus K χ 𝔣 → (∀ v ∉ T, IsUnramifiedCharAt χ v) →
      ∀ (θ : ℝ), χ ^ 2 = normPowChar K θ →
      ∀ (L : ℂ → ℂ), DifferentiableOn ℂ L {s : ℂ | 1 / 2 < s.re} →
        (∀ s : ℂ, 1 < s.re → L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
              (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) →
      ∀ s : ℂ, ‖s - (1 - θ / 2 * Complex.I)‖ ≤ δ → L s ≠ 0 :=
  R4LDD2.main K T 𝔣

end S_NumberField_TateGlobal_exists_pos_forall_partialEulerProduct_continuation_ne_zero_of_norm_sub_le_of_sq_eq_normPowChar_of_admitsModulus
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_pos_forall_partialEulerProduct_continuation_ne_zero_of_norm_sub_le_of_sq_eq_normPowChar_of_admitsModulus (solution)
