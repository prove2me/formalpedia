-- Prove2me | solution 1 for NumberField.TateGlobal.sum_localChar_det_heckeWord_eq_pow_mul_pow_of_isUnramifiedCharAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/1be55c76-6fee-50d7-bca6-f0a46c3fdb9c

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_NumberField_TateGlobal_sum_localChar_det_heckeWord_eq_pow_mul_pow_of_isUnramifiedCharAt

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open IsDedekindDomain AutomorphicForm LocalGL2

namespace ChiDetHeckeWord

variable {K : Type} [Field K] [NumberField K]

def idl (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)

def idlHom (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  (Units.map (finIncl (𝓞 K) K : FiniteAdeleRing (𝓞 K) K →* AdeleRing (𝓞 K) K)).comp (localUnit (𝓞 K) K v)

theorem idlHom_apply (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) : idlHom K v t = idl K v t := rfl

theorem idl_mul (v : HeightOneSpectrum (𝓞 K)) (t t' : (v.adicCompletion K)ˣ) :
    idl K v (t * t') = idl K v t * idl K v t' := by
  rw [← idlHom_apply, map_mul, idlHom_apply, idlHom_apply]

theorem localChar_eq_idl (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (t : (v.adicCompletion K)ˣ) : TateGlobal.localChar χ v t = χ (idl K v t) := rfl

theorem uniformizerIdele_eq_idl (v : HeightOneSpectrum (𝓞 K)) :
    uniformizerIdele K v = idl K v (uniformizerUnit K v) := rfl

section Integral

variable {v : HeightOneSpectrum (𝓞 K)}

local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers K v
local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem mul_mem_localIntegralSet {g h : GL (Fin 2) (Kv)} (hg : g ∈ localIntegralSet K v)
    (hh : h ∈ localIntegralSet K v) : g * h ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet] at hg hh ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hg.1 i k) (hh.1 k j)
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hh.2 i k) (hg.2 k j)

theorem inv_mem_localIntegralSet {g : GL (Fin 2) (Kv)} (hg : g ∈ localIntegralSet K v) :
    g⁻¹ ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet] at hg ⊢
  rw [inv_inv]
  exact ⟨hg.2, hg.1⟩

theorem mul_mem_localIntegralSet_iff_left {g h : GL (Fin 2) (Kv)} (hg : g ∈ localIntegralSet K v) :
    g * h ∈ localIntegralSet K v ↔ h ∈ localIntegralSet K v := by
  refine ⟨fun hgh => ?_, fun hh => mul_mem_localIntegralSet hg hh⟩
  have := mul_mem_localIntegralSet (inv_mem_localIntegralSet hg) hgh
  rwa [inv_mul_cancel_left] at this

theorem mul_mem_localIntegralSet_iff_right {g h : GL (Fin 2) (Kv)} (hh : h ∈ localIntegralSet K v) :
    g * h ∈ localIntegralSet K v ↔ g ∈ localIntegralSet K v := by
  refine ⟨fun hgh => ?_, fun hg => mul_mem_localIntegralSet hg hh⟩
  have := mul_mem_localIntegralSet hgh (inv_mem_localIntegralSet hh)
  rwa [mul_inv_cancel_right] at this

theorem mem_localIntegralSet_of_mem_integralSubgroup {u : GL (Fin 2) (Kv)}
    (hu : u ∈ integralSubgroup (𝓞v) (Kv)) : u ∈ localIntegralSet K v := by
  obtain ⟨y, rfl⟩ := hu
  refine (mem_localIntegralSet K v).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Matrix.GeneralLinearGroup.map_apply]
    exact SetLike.coe_mem _
  · rw [← map_inv, Matrix.GeneralLinearGroup.map_apply]
    exact SetLike.coe_mem _

theorem valued_eq_one_of_mem_of_inv_mem {t : Kv} (ht : t ∈ 𝓞v) (ht' : t⁻¹ ∈ 𝓞v) (ht0 : t ≠ 0) :
    Valued.v t = 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ht ht'
  rw [map_inv₀] at ht'
  have h0 : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).mpr ht0
  exact le_antisymm ht ((inv_le_one₀ (zero_lt_iff.mpr h0)).mp ht')

theorem valued_det_eq_one_of_mem_localIntegralSet {g : GL (Fin 2) (Kv)} (hg : g ∈ localIntegralSet K v) :
    Valued.v ((Matrix.GeneralLinearGroup.det g : (Kv)ˣ) : Kv) = 1 := by
  rw [mem_localIntegralSet] at hg
  have hdet : ∀ M : Matrix (Fin 2) (Fin 2) (Kv), (∀ i j, M i j ∈ 𝓞v) → M.det ∈ 𝓞v := by
    intro M hM
    rw [Matrix.det_fin_two]
    exact Subring.sub_mem _ (Subring.mul_mem _ (hM 0 0) (hM 1 1)) (Subring.mul_mem _ (hM 0 1) (hM 1 0))
  refine valued_eq_one_of_mem_of_inv_mem ?_ ?_ (Units.ne_zero _)
  · rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact hdet _ hg.1
  · rw [← Units.val_inv_eq_inv_val, ← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
    exact hdet _ hg.2

theorem valued_eq_exp_neg_one_of_irreducible {ϖ : 𝓞v} (hirr : Irreducible ϖ) :
    Valued.v (ϖ : Kv) = WithZero.exp (-1 : ℤ) := by
  have hmax : IsLocalRing.maximalIdeal (𝓞v) = Ideal.span {ϖ} := hirr.maximalIdeal_eq
  have hlt : Valued.v (ϖ : Kv) < 1 := by
    rw [← NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one (𝓞 K) K v]
    exact (IsLocalRing.mem_maximalIdeal _).2 hirr.not_isUnit
  set π₀ : 𝓞v := ⟨(uniformizerUnit K v : Kv),
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [valued_uniformizerUnit]; exact le_of_lt (by
      rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by norm_num)))⟩ with hπ₀
  have hπ₀v : Valued.v (π₀ : Kv) = WithZero.exp (-1 : ℤ) := valued_uniformizerUnit K v
  have hπ₀mem : π₀ ∈ IsLocalRing.maximalIdeal (𝓞v) := by
    rw [NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one (𝓞 K) K v, hπ₀v, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.2 (by norm_num)
  rw [hmax, Ideal.mem_span_singleton'] at hπ₀mem
  obtain ⟨c, hc⟩ := hπ₀mem
  have hle : WithZero.exp (-1 : ℤ) ≤ Valued.v (ϖ : Kv) := by
    rw [← hπ₀v, ← hc]
    show Valued.v ((c : Kv) * (ϖ : Kv)) ≤ _
    rw [Valuation.map_mul]
    exact mul_le_of_le_one_left' c.2
  have hne : Valued.v (ϖ : Kv) ≠ 0 := by
    intro h0
    rw [h0] at hle
    exact WithZero.exp_ne_zero (le_antisymm hle zero_le')
  rw [← WithZero.exp_log hne] at hlt hle ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [WithZero.exp_le_exp] at hle
  congr 1
  omega

theorem apply_idl_eq_of_isUnramifiedCharAt {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (hχ : TateGlobal.IsUnramifiedCharAt χ v) {t t' : (Kv)ˣ}
    (h : Valued.v (t : Kv) = Valued.v (t' : Kv)) : χ (idl K v t) = χ (idl K v t') := by
  have ht0 : Valued.v (t : Kv) ≠ 0 := (Valuation.ne_zero_iff _).mpr t.ne_zero
  have hu : Valued.v ((t⁻¹ * t' : (Kv)ˣ) : Kv) = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Valuation.map_mul, map_inv₀, ← h, inv_mul_cancel₀ ht0]
  have hu' : Valued.v (((t⁻¹ * t')⁻¹ : (Kv)ˣ) : Kv) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  have key := hχ (t⁻¹ * t') ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hu.le)
    ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hu'.le)
  rw [localChar_eq_idl] at key
  calc χ (idl K v t) = χ (idl K v t) * χ (idl K v (t⁻¹ * t')) := by rw [key, mul_one]
    _ = χ (idl K v t') := by rw [← map_mul, ← idl_mul, mul_inv_cancel_left]

theorem apply_idl_eq_one_of_isUnramifiedCharAt {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (hχ : TateGlobal.IsUnramifiedCharAt χ v) {t : (Kv)ˣ} (h : Valued.v (t : Kv) = 1) : χ (idl K v t) = 1 := by
  have h1 : Valued.v ((1 : (Kv)ˣ) : Kv) = 1 := by rw [Units.val_one, map_one]
  rw [apply_idl_eq_of_isUnramifiedCharAt hχ (h.trans h1.symm), ← idlHom_apply, map_one, map_one]

end Integral

section CosetSystem

variable {G : Type*} [Group G] {U : Subgroup G} {g₀ : G}

theorem cosetSum_eq_of_isHeckeCosetSystem {ι₀ ι₁ : Type*} [Fintype ι₀] [Fintype ι₁]
    {reps₀ : ι₀ → G} {reps₁ : ι₁ → G}
    (h₀ : HeckeIntegralSeam.IsHeckeCosetSystem U g₀ reps₀) (h₁ : HeckeIntegralSeam.IsHeckeCosetSystem U g₀ reps₁)
    (F : G → ℂ) (hFU : ∀ y : G, ∀ u ∈ U, F (y * u) = F y) :
    ∑ i, F (reps₀ i) = ∑ j, F (reps₁ j) := by
  have hcov : ∀ i, ∃ j, (QuotientGroup.mk (reps₀ i) : G ⧸ U) = QuotientGroup.mk (reps₁ j) :=
    fun i => h₁.covers (reps₀ i) (h₀.mem_doubleCoset i)
  choose e he using hcov
  have hinj : Function.Injective e := by
    intro i i' hii'
    apply h₀.mk_injective
    simp only
    rw [he i, he i', hii']
  have hsurj : Function.Surjective e := by
    intro j
    obtain ⟨i, hi⟩ := h₀.covers (reps₁ j) (h₁.mem_doubleCoset j)
    refine ⟨i, h₁.mk_injective ?_⟩
    simp only
    rw [← he i, hi]
  refine Fintype.sum_bijective e ⟨hinj, hsurj⟩ _ _ fun i => ?_
  have hu : (reps₀ i)⁻¹ * reps₁ (e i) ∈ U := QuotientGroup.eq.1 (he i)
  have eq : reps₁ (e i) = reps₀ i * ((reps₀ i)⁻¹ * reps₁ (e i)) := by group
  rw [eq, hFU _ _ hu]

theorem nonempty_of_isHeckeCosetSystem {ι : Type*} {reps : ι → G}
    (h : HeckeIntegralSeam.IsHeckeCosetSystem U g₀ reps) : Nonempty ι := by
  obtain ⟨i, -⟩ := h.covers g₀ (HeckePair.self_mem_doubleCoset g₀)
  exact ⟨i⟩

end CosetSystem

section Explicit

variable (v : HeightOneSpectrum (𝓞 K))

local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers K v
local notation "Kv" => HeightOneSpectrum.adicCompletion K v

def explicitRep (ϖ : 𝓞v) (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0) : Option (𝓞 K ⧸ v.asIdeal) → GL (Fin 2) (Kv)
  | none => localRepInf ϖ hϖ0
  | some c => localRepSome ϖ hϖ0 (algebraMap (𝓞 K) (𝓞v) (Quotient.out c))

theorem algebraMap_mem_maximalIdeal_iff (a : 𝓞 K) :
    algebraMap (𝓞 K) (𝓞v) a ∈ IsLocalRing.maximalIdeal (𝓞v) ↔ a ∈ v.asIdeal := by
  rw [NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one (𝓞 K) K v]
  simp only [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_lt_one_iff_mem v a

variable {v}

theorem sub_mem_maximalIdeal_of_mk_eq {a b : 𝓞 K}
    (h : (Ideal.Quotient.mk v.asIdeal a) = Ideal.Quotient.mk v.asIdeal b) :
    algebraMap (𝓞 K) (𝓞v) a - algebraMap (𝓞 K) (𝓞v) b ∈ IsLocalRing.maximalIdeal (𝓞v) := by
  rw [← map_sub, algebraMap_mem_maximalIdeal_iff]
  exact Ideal.Quotient.eq.1 h

theorem isHeckeCosetSystem_explicitRep (ϖ : 𝓞v) (hirr : Irreducible ϖ)
    (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0) :
    HeckeIntegralSeam.IsHeckeCosetSystem (integralSubgroup (𝓞v) (Kv)) (diagPi ϖ hϖ0)
      (explicitRep v ϖ hϖ0) := by
  have hmax : IsLocalRing.maximalIdeal (𝓞v) = Ideal.span {ϖ} := hirr.maximalIdeal_eq
  constructor
  · rintro (_ | c)
    · exact HeckePair.mem_doubleCoset_iff.mpr ⟨weylInt (𝓞v) (Kv), weylInt_mem, weylInt (𝓞v) (Kv),
        weylInt_mem, rfl⟩
    · exact HeckePair.mem_doubleCoset_iff.mpr ⟨unipotentInt (Kv) _, unipotentInt_mem _, 1, one_mem _,
        by rw [mul_one]; rfl⟩
  · intro x hx
    obtain ⟨u, hu, u', hu', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
    have hxu : (QuotientGroup.mk (u * diagPi ϖ hϖ0 * u') : GL (Fin 2) (Kv) ⧸ integralSubgroup (𝓞v) (Kv)) =
        QuotientGroup.mk (u * diagPi ϖ hϖ0) := by
      rw [QuotientGroup.eq]
      rw [show (u * diagPi ϖ hϖ0 * u')⁻¹ * (u * diagPi ϖ hϖ0) = u'⁻¹ by group]
      exact inv_mem hu'
    rw [hxu]
    have hmem : u * diagPi ϖ hϖ0 ∈ heckeMulSet ϖ hϖ0 := (mem_heckeMulSet_iff ϖ hϖ0).mpr ⟨u, hu, rfl⟩
    rcases exists_rep_of_mem_heckeMulSet ϖ hϖ0 hirr hmem with ⟨b, hb⟩ | hinf
    · obtain ⟨a, ha⟩ := NumberField.AdelicHaar.exists_valued_algebraMap_sub_lt_one (𝓞 K) K v b
      refine ⟨some (Ideal.Quotient.mk v.asIdeal a), ?_⟩
      show _ = QuotientGroup.mk (localRepSome ϖ hϖ0 (algebraMap (𝓞 K) (𝓞v)
        (Quotient.out (Ideal.Quotient.mk v.asIdeal a))))
      rw [← hb]
      refine mk_localRepSome_eq_of_dvd_sub ϖ hϖ0 ?_
      rw [← Ideal.mem_span_singleton, ← hmax]
      have h1 : algebraMap (𝓞 K) (𝓞v) (Quotient.out (Ideal.Quotient.mk v.asIdeal a)) -
          algebraMap (𝓞 K) (𝓞v) a ∈ IsLocalRing.maximalIdeal (𝓞v) :=
        sub_mem_maximalIdeal_of_mk_eq (Ideal.Quotient.mk_out _)
      have h2 : algebraMap (𝓞 K) (𝓞v) a - b ∈ IsLocalRing.maximalIdeal (𝓞v) := by
        rw [NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one (𝓞 K) K v]
        simp at ha ⊢
        exact ha
      have := add_mem h1 h2
      rwa [sub_add_sub_cancel] at this
    · exact ⟨none, hinf.symm⟩
  · rintro (_ | c) (_ | c') h
    · rfl
    · exact absurd h.symm (mk_localRepSome_ne_mk_localRepInf ϖ hϖ0 hirr.not_isUnit _)
    · exact absurd h (mk_localRepSome_ne_mk_localRepInf ϖ hϖ0 hirr.not_isUnit _)
    · have hd := dvd_sub_of_mk_localRepSome_eq ϖ hϖ0 h
      rw [← Ideal.mem_span_singleton, ← hmax, ← map_sub, algebraMap_mem_maximalIdeal_iff,
        ← Ideal.Quotient.eq, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out] at hd
      rw [hd]

theorem card_quotient_eq_absNorm [Fintype (𝓞 K ⧸ v.asIdeal)] :
    Fintype.card (𝓞 K ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

def piUnit (ϖ : 𝓞v) (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0) : (Kv)ˣ := Units.mk0 _ hϖ0

theorem valued_det_of_mem_doubleCoset {ϖ : 𝓞v} (hirr : Irreducible ϖ) (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0)
    {x : GL (Fin 2) (Kv)} (hx : x ∈ HeckePair.doubleCoset (integralSubgroup (𝓞v) (Kv)) (diagPi ϖ hϖ0)) :
    Valued.v ((Matrix.GeneralLinearGroup.det x : (Kv)ˣ) : Kv) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨u, hu, u', hu', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  have hdiag : ((Matrix.GeneralLinearGroup.det (diagPi ϖ hϖ0) : (Kv)ˣ) : Kv) = (ϖ : Kv) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagPi, Matrix.det_fin_two_of]
    simp
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Valuation.map_mul, Valuation.map_mul,
    valued_det_eq_one_of_mem_localIntegralSet (mem_localIntegralSet_of_mem_integralSubgroup hu),
    valued_det_eq_one_of_mem_localIntegralSet (mem_localIntegralSet_of_mem_integralSubgroup hu'), hdiag,
    valued_eq_exp_neg_one_of_irreducible hirr, one_mul, mul_one]

end Explicit

section Psi

variable (v : HeightOneSpectrum (𝓞 K))

local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers K v
local notation "Kv" => HeightOneSpectrum.adicCompletion K v

def psi (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : GL (Fin 2) (Kv) →* ℂ :=
  (Units.coeHom ℂ).comp (χ.comp ((idlHom K v).comp
    (Matrix.GeneralLinearGroup.det : GL (Fin 2) (Kv) →* (Kv)ˣ)))

def chiHat (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : ℂ :=
  ((χ (uniformizerIdele K v) : ℂˣ) : ℂ)

variable {v}

theorem psi_apply (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (y : GL (Fin 2) (Kv)) :
    psi v χ y = ((χ (idl K v (Matrix.GeneralLinearGroup.det y)) : ℂˣ) : ℂ) := rfl

theorem chiHat_ne_zero (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : chiHat v χ ≠ 0 := Units.ne_zero _

theorem psi_eq_chiHat_of_isUnramifiedCharAt {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (hχ : TateGlobal.IsUnramifiedCharAt χ v) {y : GL (Fin 2) (Kv)}
    (hy : Valued.v ((Matrix.GeneralLinearGroup.det y : (Kv)ˣ) : Kv) = WithZero.exp (-1 : ℤ)) :
    psi v χ y = chiHat v χ := by
  rw [psi_apply, chiHat, uniformizerIdele_eq_idl,
    apply_idl_eq_of_isUnramifiedCharAt hχ (hy.trans (valued_uniformizerUnit K v).symm)]

theorem psi_eq_one_of_isUnramifiedCharAt {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (hχ : TateGlobal.IsUnramifiedCharAt χ v) {u : GL (Fin 2) (Kv)} (hu : u ∈ localIntegralSet K v) :
    psi v χ u = 1 := by
  rw [psi_apply, apply_idl_eq_one_of_isUnramifiedCharAt hχ (valued_det_eq_one_of_mem_localIntegralSet hu),
    Units.val_one]

theorem heckeSum_psi {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχ : TateGlobal.IsUnramifiedCharAt χ v)
    (ϖ : 𝓞v) (hirr : Irreducible ϖ) (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0)
    {n : ℕ} {r : Fin n → GL (Fin 2) (Kv)}
    (hcos : HeckeIntegralSeam.IsHeckeCosetSystem (integralSubgroup (𝓞v) (Kv)) (diagPi ϖ hϖ0) r) :
    ∑ i, psi v χ (r i) = (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 1) * chiHat v χ := by
  classical
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  have hexp := isHeckeCosetSystem_explicitRep ϖ hirr hϖ0
  rw [cosetSum_eq_of_isHeckeCosetSystem hcos hexp (psi v χ) (fun y u hu => by
    rw [map_mul, psi_eq_one_of_isUnramifiedCharAt hχ (mem_localIntegralSet_of_mem_integralSubgroup hu), mul_one])]
  have hval : ∀ o, psi v χ (explicitRep v ϖ hϖ0 o) = chiHat v χ := fun o =>
    psi_eq_chiHat_of_isUnramifiedCharAt hχ (valued_det_of_mem_doubleCoset hirr hϖ0 (hexp.mem_doubleCoset o))
  simp only [hval, Finset.sum_const, Finset.card_univ, Fintype.card_option, card_quotient_eq_absNorm,
    nsmul_eq_mul]
  push_cast
  ring

theorem psi_central {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχ : TateGlobal.IsUnramifiedCharAt χ v)
    (ϖ : 𝓞v) (hirr : Irreducible ϖ) (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0)
    (z : GL (Fin 2) (Kv))
    (hz : (z : Matrix (Fin 2) (Fin 2) (Kv)) = algebraMap (𝓞v) (Kv) ϖ • (1 : Matrix (Fin 2) (Fin 2) (Kv))) :
    psi v χ z = chiHat v χ ^ 2 := by
  have hdet : Matrix.GeneralLinearGroup.det z = piUnit ϖ hϖ0 * piUnit ϖ hϖ0 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hz, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin, Units.val_mul]
    show (ϖ : Kv) ^ 2 = (ϖ : Kv) * (ϖ : Kv)
    ring
  have hvalϖ : Valued.v ((piUnit ϖ hϖ0 : (Kv)ˣ) : Kv) = Valued.v ((uniformizerUnit K v : (Kv)ˣ) : Kv) := by
    rw [valued_uniformizerUnit]
    exact valued_eq_exp_neg_one_of_irreducible hirr
  rw [psi_apply, hdet, idl_mul, map_mul, Units.val_mul, apply_idl_eq_of_isUnramifiedCharAt hχ hvalϖ,
    ← uniformizerIdele_eq_idl, chiHat, sq]

theorem wordSum_psi {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχ : TateGlobal.IsUnramifiedCharAt χ v)
    (ϖ : 𝓞v) (hirr : Irreducible ϖ) (hϖ0 : algebraMap (𝓞v) (Kv) ϖ ≠ 0)
    {n : ℕ} {r : Fin n → GL (Fin 2) (Kv)}
    (hcos : HeckeIntegralSeam.IsHeckeCosetSystem (integralSubgroup (𝓞v) (Kv)) (diagPi ϖ hϖ0) r)
    (z : GL (Fin 2) (Kv))
    (hz : (z : Matrix (Fin 2) (Fin 2) (Kv)) = algebraMap (𝓞v) (Kv) ϖ • (1 : Matrix (Fin 2) (Fin 2) (Kv)))
    (k j : ℕ) :
    ∑ ι : Fin k → Fin n, psi v χ ((List.ofFn fun m => r (ι m)).prod * z ^ j) =
      ((((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 1) * chiHat v χ) ^ k * (chiHat v χ ^ 2) ^ j := by
  classical
  have h1 : ∀ ι : Fin k → Fin n, psi v χ ((List.ofFn fun m => r (ι m)).prod * z ^ j) =
      (∏ m, psi v χ (r (ι m))) * (chiHat v χ ^ 2) ^ j := by
    intro ι
    rw [map_mul, map_pow, map_list_prod, List.map_ofFn, List.prod_ofFn, psi_central hχ ϖ hirr hϖ0 z hz]
    rfl
  simp_rw [h1]
  rw [← Finset.sum_mul]
  congr 1
  have h2 := (Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset (Fin n)))
    (fun _ i => psi v χ (r i)))
  rw [Fintype.piFinset_univ] at h2
  rw [← h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin, heckeSum_psi hχ ϖ hirr hϖ0 hcos]

end Psi

end ChiDetHeckeWord

open ChiDetHeckeWord in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχ : NumberField.TateGlobal.IsUnramifiedCharAt χ v)
    (ϖ : v.adicCompletionIntegers K) (hirr : Irreducible ϖ)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (n : ℕ) (r : Fin n → GL (Fin 2) (v.adicCompletion K))
    (hr : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖ hϖ0) r)
    (z : GL (Fin 2) (v.adicCompletion K))
    (hz : (z : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (k j : ℕ) :
    ∑ ι : Fin k → Fin n,
        ((NumberField.TateGlobal.localChar χ v
          (Matrix.GeneralLinearGroup.det ((List.ofFn fun m => r (ι m)).prod * z ^ j)) : ℂˣ) : ℂ) =
      ((((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 1) *
          ((χ (AutomorphicForm.uniformizerIdele K v) : ℂˣ) : ℂ)) ^ k *
        (((χ (AutomorphicForm.uniformizerIdele K v) : ℂˣ) : ℂ) ^ 2) ^ j :=
  wordSum_psi hχ ϖ hirr hϖ0 hr z hz k j

end

end S_NumberField_TateGlobal_sum_localChar_det_heckeWord_eq_pow_mul_pow_of_isUnramifiedCharAt
end P2MW
export P2MW.S_NumberField_TateGlobal_sum_localChar_det_heckeWord_eq_pow_mul_pow_of_isUnramifiedCharAt (solution)
