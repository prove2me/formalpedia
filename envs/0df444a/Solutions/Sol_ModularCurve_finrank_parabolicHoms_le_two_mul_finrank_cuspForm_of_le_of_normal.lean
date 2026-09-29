-- Prove2me | solution 1 for ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/4235979a-285c-5ece-8f92-aabb78a04442

import Mathlib
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_PeriodOf
import Theorems.Thm_CuspForm_finiteDimensional_of_isArithmetic
import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree
import Theorems.Thm_ModularCurve_eq_zero_of_forall_re_periodOf_eq_zero
import Theorems.Thm_ModularCurve_periodMapOf_mem_parabolicHoms
import Theorems.Thm_ModularCurve_periodMapOf_apply_eq_periodOf
import Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitiveOf
import Theorems.Thm_ModularCurve_periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal
p2m_attr_erase "instance" "ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ModularForm

open UpperHalfPlane Filter Topology

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "Period.IsEquivariantPrimitive Period.IsParabolicHom Period.parabolicHoms periodOf HasEquivariantPrimitiveOf periodMapOf period Period.exists_basis_parabolicHoms_of_isAddTorsionFree eq_zero_of_forall_re_periodOf_eq_zero periodMapOf_mem_parabolicHoms periodMapOf_apply_eq_periodOf exists_hasEquivariantPrimitiveOf periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf"
namespace ESDescent
p2m_open "ModularCurve"

section RealPeriodMap

variable (Δ : Subgroup SL(2, ℤ)) [Δ.FiniteIndex]

def rePeriod (f : CuspForm Δ 2) : Additive Δ →+ ℝ :=
  Complex.reLm.toAddMonoidHom.comp (ModularCurve.periodMapOf Δ f)

theorem rePeriod_apply (f : CuspForm Δ 2) (γ : Δ) :
    rePeriod Δ f (Additive.ofMul γ) = (ModularCurve.periodOf Δ γ f).re := by
  simp only [rePeriod, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
    Complex.reLm_coe]
  rw [ModularCurve.periodMapOf_apply_eq_periodOf]

theorem rePeriod_apply' (f : CuspForm Δ 2) (a : Additive Δ) :
    rePeriod Δ f a = (ModularCurve.periodOf Δ (Additive.toMul a) f).re :=
  rePeriod_apply Δ f (Additive.toMul a)

omit [Δ.FiniteIndex] in
theorem rePeriod_isParabolicHom (f : CuspForm Δ 2) :
    ModularCurve.Period.IsParabolicHom Δ (rePeriod Δ f) := by
  intro γ hγ
  have h := ModularCurve.periodMapOf_mem_parabolicHoms Δ f
  have h0 : ModularCurve.periodMapOf Δ f (Additive.ofMul γ) = 0 := h γ hγ
  simp only [rePeriod, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
    Complex.reLm_coe, h0, Complex.zero_re]

theorem rePeriod_add (f g : CuspForm Δ 2) : rePeriod Δ (f + g) = rePeriod Δ f + rePeriod Δ g := by
  refine AddMonoidHom.ext fun a => ?_
  rw [AddMonoidHom.add_apply, rePeriod_apply', rePeriod_apply', rePeriod_apply', map_add,
    Complex.add_re]

theorem rePeriod_smul (c : ℝ) (f : CuspForm Δ 2) : rePeriod Δ (c • f) = c • rePeriod Δ f := by
  refine AddMonoidHom.ext fun a => ?_
  have hc : (c • f : CuspForm Δ 2) = (c : ℂ) • f := rfl
  rw [AddMonoidHom.smul_apply, rePeriod_apply', rePeriod_apply', hc, map_smul, smul_eq_mul,
    Complex.re_ofReal_mul, smul_eq_mul]

def realPeriodMap : CuspForm Δ 2 →ₗ[ℝ] ModularCurve.Period.parabolicHoms ℝ Δ ℝ where
  toFun f := ⟨rePeriod Δ f, rePeriod_isParabolicHom Δ f⟩
  map_add' f g := by
    apply Subtype.ext
    simp only [Submodule.coe_add, rePeriod_add]
  map_smul' c f := by
    apply Subtype.ext
    simp only [RingHom.id_apply, Submodule.coe_smul, rePeriod_smul]

theorem realPeriodMap_apply (f : CuspForm Δ 2) (γ : Δ) :
    (realPeriodMap Δ f : Additive Δ →+ ℝ) (Additive.ofMul γ) = (ModularCurve.periodOf Δ γ f).re :=
  rePeriod_apply Δ f γ

theorem realPeriodMap_injective : Function.Injective (realPeriodMap Δ) := by
  intro f g hfg
  rw [← sub_eq_zero]
  apply ModularCurve.eq_zero_of_forall_re_periodOf_eq_zero Δ (f - g)
  intro γ
  have h := congrArg (fun φ : ModularCurve.Period.parabolicHoms ℝ Δ ℝ =>
    (φ : Additive Δ →+ ℝ) (Additive.ofMul γ)) hfg
  simp only [realPeriodMap_apply] at h
  rw [map_sub, Complex.sub_re, h, sub_self]

theorem finite_and_finrank_parabolicHoms_real_eq :
    Module.Finite ℝ (ModularCurve.Period.parabolicHoms ℝ Δ ℝ) ∧
      Module.finrank ℝ (ModularCurve.Period.parabolicHoms ℝ Δ ℝ) =
        Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ Δ ℤ) := by
  obtain ⟨n, b, hb⟩ := ModularCurve.Period.exists_basis_parabolicHoms_of_isAddTorsionFree Δ
  obtain ⟨bR, -⟩ := hb ℝ
  refine ⟨Module.Finite.of_basis bR, ?_⟩
  rw [Module.finrank_eq_card_basis bR, Module.finrank_eq_card_basis b]

scoped instance finiteDimensional_cuspForm : FiniteDimensional ℂ (CuspForm Δ 2) :=
  CuspForm.finiteDimensional_of_isArithmetic (Δ : Subgroup (GL (Fin 2) ℝ)) 2

theorem finrank_real_cuspForm :
    Module.finrank ℝ (CuspForm Δ 2) = 2 * Module.finrank ℂ (CuspForm Δ 2) :=
  finrank_real_of_complex (CuspForm Δ 2)

theorem realPeriodMap_bijective_of_le
    (h : Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ Δ ℤ) ≤
      2 * Module.finrank ℂ (CuspForm Δ 2)) :
    Function.Bijective (realPeriodMap Δ) := by
  obtain ⟨hfin, heq⟩ := finite_and_finrank_parabolicHoms_real_eq Δ
  haveI := hfin
  have hinj := realPeriodMap_injective Δ
  have h1 : Module.finrank ℝ (CuspForm Δ 2) ≤
      Module.finrank ℝ (ModularCurve.Period.parabolicHoms ℝ Δ ℝ) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : Module.finrank ℝ (ModularCurve.Period.parabolicHoms ℝ Δ ℝ) ≤
      Module.finrank ℝ (CuspForm Δ 2) := by
    rw [heq, finrank_real_cuspForm]; exact h
  have hdim : Module.finrank ℝ (CuspForm Δ 2) =
      Module.finrank ℝ (ModularCurve.Period.parabolicHoms ℝ Δ ℝ) := le_antisymm h1 h2
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

end RealPeriodMap

section Lower

variable {Γ' Γ : Subgroup SL(2, ℤ)}

theorem map_mono_GL (hle : Γ' ≤ Γ) :
    (Γ' : Subgroup (GL (Fin 2) ℝ)) ≤ (Γ : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono hle

def lower (hle : Γ' ≤ Γ) (f : CuspForm Γ 2) : CuspForm Γ' 2 where
  toFun := f
  slash_action_eq' A hA := SlashInvariantFormClass.slash_action_eq f A (map_mono_GL hle hA)
  holo' := f.holo'
  zero_at_cusps' hc := CuspFormClass.zero_at_cusps f (hc.mono (map_mono_GL hle))

@[scoped simp] theorem lower_apply (hle : Γ' ≤ Γ) (f : CuspForm Γ 2) (z : ℍ) : lower hle f z = f z := rfl

theorem coe_lower (hle : Γ' ≤ Γ) (f : CuspForm Γ 2) :
    ((lower hle f : CuspForm Γ' 2) : ℍ → ℂ) = f := rfl

theorem periodOf_lower (hle : Γ' ≤ Γ) (f : CuspForm Γ 2) (γ : Γ') :
    ModularCurve.periodOf Γ' γ (lower hle f) = ModularCurve.periodOf Γ ⟨γ, hle γ.2⟩ f := rfl

def res (hle : Γ' ≤ Γ) :
    ModularCurve.Period.parabolicHoms ℝ Γ ℝ →ₗ[ℝ] ModularCurve.Period.parabolicHoms ℝ Γ' ℝ where
  toFun x := ⟨(x : Additive Γ →+ ℝ).comp (MonoidHom.toAdditive (Subgroup.inclusion hle)),
    fun γ hγ => x.2 (Subgroup.inclusion hle γ) hγ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem res_apply (hle : Γ' ≤ Γ) (x : ModularCurve.Period.parabolicHoms ℝ Γ ℝ) (γ : Γ') :
    (res hle x : Additive Γ' →+ ℝ) (Additive.ofMul γ) =
      (x : Additive Γ →+ ℝ) (Additive.ofMul ⟨(γ : SL(2, ℤ)), hle γ.2⟩) := rfl

theorem res_injective [Γ'.FiniteIndex] (hle : Γ' ≤ Γ) : Function.Injective (res hle) := by
  intro x y hxy
  rw [← sub_eq_zero]
  set w := x - y with hw
  have hw0 : res hle w = 0 := by rw [hw, map_sub, hxy, sub_self]
  apply Subtype.ext
  refine AddMonoidHom.ext fun a => ?_

  obtain ⟨n, hn, -, hmem⟩ :=
    Subgroup.exists_pow_mem_of_index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := Γ'))
      ((Additive.toMul a : Γ) : SL(2, ℤ))
  have hpow : ((Additive.toMul a ^ n : Γ) : SL(2, ℤ)) = ((Additive.toMul a : Γ) : SL(2, ℤ)) ^ n := by
    simp
  have hval : (w : Additive Γ →+ ℝ) (Additive.ofMul (Additive.toMul a ^ n)) = 0 := by
    have := congrArg (fun φ : ModularCurve.Period.parabolicHoms ℝ Γ' ℝ =>
      (φ : Additive Γ' →+ ℝ) (Additive.ofMul ⟨((Additive.toMul a : Γ) : SL(2, ℤ)) ^ n, hmem⟩)) hw0
    simp only [res_apply, Submodule.coe_zero, AddMonoidHom.zero_apply] at this
    convert this using 3 <;> first | rfl | exact Subtype.ext hpow
  rw [ofMul_pow, map_nsmul, nsmul_eq_mul, mul_eq_zero] at hval
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h0 : (w : Additive Γ →+ ℝ) a = 0 := by
    rcases hval with h | h
    · exact absurd h hn'
    · simpa using h
  simpa using h0

theorem res_realPeriodMap [Γ'.FiniteIndex] [Γ.FiniteIndex] (hle : Γ' ≤ Γ) (f : CuspForm Γ 2) :
    res hle (realPeriodMap Γ f) = realPeriodMap Γ' (lower hle f) := by
  apply Subtype.ext
  refine AddMonoidHom.ext fun a => ?_
  rw [← ofMul_toMul a, res_apply, realPeriodMap_apply, realPeriodMap_apply, periodOf_lower]

end Lower

section Action

variable {Γ' Γ : Subgroup SL(2, ℤ)} (hle : Γ' ≤ Γ) (hn : (Γ'.subgroupOf Γ).Normal)

include hle hn in
theorem conj_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Γ') (δ : Γ) : (δ : SL(2, ℤ)) * γ * (δ : SL(2, ℤ))⁻¹ ∈ Γ' :=
  (Subgroup.normal_subgroupOf_iff hle).mp hn γ δ hγ δ.2

include hle hn in
theorem conj_mem' {γ : SL(2, ℤ)} (hγ : γ ∈ Γ') (δ : Γ) : (δ : SL(2, ℤ))⁻¹ * γ * (δ : SL(2, ℤ)) ∈ Γ' := by
  have := conj_mem hle hn hγ δ⁻¹
  simpa using this

open scoped Pointwise in
include hle hn in

theorem smul_coe_eq (δ : Γ) :
    ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ (δ : SL(2, ℤ)))⁻¹ •
      (Γ' : Subgroup (GL (Fin 2) ℝ)) = (Γ' : Subgroup (GL (Fin 2) ℝ)) := by
  ext A
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, ConjAct.smul_def,
    ConjAct.ofConjAct_toConjAct]
  constructor
  · rintro ⟨γ, hγ, hA⟩

    refine ⟨(δ : SL(2, ℤ))⁻¹ * γ * (δ : SL(2, ℤ)), conj_mem' hle hn hγ δ, ?_⟩
    have hA' : A = (Matrix.SpecialLinearGroup.mapGL ℝ (δ : SL(2, ℤ)))⁻¹ *
        Matrix.SpecialLinearGroup.mapGL ℝ γ * Matrix.SpecialLinearGroup.mapGL ℝ (δ : SL(2, ℤ)) := by
      rw [hA]; group
    rw [hA', map_mul, map_mul, map_inv]
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨(δ : SL(2, ℤ)) * γ * (δ : SL(2, ℤ))⁻¹, conj_mem hle hn hγ δ, ?_⟩
    rw [map_mul, map_mul, map_inv]

def act (δ : Γ) (g : CuspForm Γ' 2) : CuspForm Γ' 2 :=
  (CuspForm.translate g (Matrix.SpecialLinearGroup.mapGL ℝ (δ : SL(2, ℤ)))).copy
    ((g : ℍ → ℂ) ∣[(2 : ℤ)] (δ : SL(2, ℤ))) rfl (smul_coe_eq hle hn δ).symm

theorem coe_act (δ : Γ) (g : CuspForm Γ' 2) :
    ((act hle hn δ g : CuspForm Γ' 2) : ℍ → ℂ) = (g : ℍ → ℂ) ∣[(2 : ℤ)] (δ : SL(2, ℤ)) := rfl

theorem act_apply (δ : Γ) (g : CuspForm Γ' 2) (z : ℍ) :
    act hle hn δ g z = ((g : ℍ → ℂ) ∣[(2 : ℤ)] (δ : SL(2, ℤ))) z := rfl

theorem hasDerivAt_smul_ofComplex (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ))
      (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ)) ↑τ := by
  set G : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ γ with hG
  have hdet : (G : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hG, Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  have hpos : (0:ℝ) < (G : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; norm_num
  have h1 := (UpperHalfPlane.hasStrictDerivAt_smul hpos τ).hasDerivAt
  have h2 : (fun z : ℂ => ((G • ofComplex z : ℍ) : ℂ))
      = fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ) := by
    funext z
    rw [MulAction.compHom_smul_def]
  rw [h2] at h1
  convert h1 using 1 <;> try rfl
  rw [hdet]
  push_cast
  rw [zpow_neg, one_div]
  norm_cast

theorem hasDerivAt_comp_smul {G : ℍ → ℂ} {g : ℍ → ℂ}
    (hG : ∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) ↑τ) (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => G (γ • ofComplex z)) ((g ∣[(2:ℤ)] γ) τ) ↑τ := by
  have hfun : (fun z : ℂ => G (γ • ofComplex z))
      = (G ∘ ofComplex) ∘ (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ)) := by
    funext z
    simp only [Function.comp_apply, ofComplex_apply]
  have houter : HasDerivAt (G ∘ ofComplex) (g (γ • τ))
      ((fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ)) ↑τ) := by
    simpa only [ofComplex_apply] using hG (γ • τ)
  have hcomp := houter.comp (↑τ : ℂ) (hasDerivAt_smul_ofComplex γ τ)
  rw [← hfun] at hcomp
  convert hcomp using 1 <;> try rfl
  exact ModularForm.SL_slash_apply (g : ℍ → ℂ) γ τ

theorem hasEquivariantPrimitiveOf_act (δ : Γ) (g : CuspForm Γ' 2) {G : ℍ → ℂ}
    (hG : ModularCurve.HasEquivariantPrimitiveOf Γ' g G) :
    ∃ L : ℂ, ModularCurve.HasEquivariantPrimitiveOf Γ' (act hle hn δ g)
      (fun z => G ((δ : SL(2, ℤ)) • z) - L) := by
  obtain ⟨hder, _, hequiv, hlim⟩ := hG
  obtain ⟨L, hL⟩ := hlim (δ : SL(2, ℤ))
  refine ⟨L, ?_, ?_, ?_, ?_⟩
  ·
    intro τ
    have h := (hasDerivAt_comp_smul (G := G) (g := (g : ℍ → ℂ)) hder (δ : SL(2, ℤ)) τ).sub_const L
    exact h
  ·
    have : Tendsto (fun w : ℍ => G ((δ : SL(2, ℤ)) • w) - L) atImInfty (𝓝 (L - L)) :=
      hL.sub_const L
    rwa [sub_self] at this
  ·
    intro γ
    refine ⟨hequiv.period ⟨(δ : SL(2, ℤ)) * γ * (δ : SL(2, ℤ))⁻¹, conj_mem hle hn γ.2 δ⟩, fun z => ?_⟩
    have hz : (δ : SL(2, ℤ)) • ((γ : SL(2, ℤ)) • z) =
        ((δ : SL(2, ℤ)) * γ * (δ : SL(2, ℤ))⁻¹) • ((δ : SL(2, ℤ)) • z) := by
      rw [← mul_smul, ← mul_smul]
      congr 1
      group
    show G ((δ : SL(2, ℤ)) • ((γ : SL(2, ℤ)) • z)) - L - (G ((δ : SL(2, ℤ)) • z) - L) = _
    rw [hz, sub_sub_sub_cancel_right]
    exact hequiv.sub_eq_period ⟨_, conj_mem hle hn γ.2 δ⟩ ((δ : SL(2, ℤ)) • z)
  ·
    intro δ₁
    obtain ⟨L₁, hL₁⟩ := hlim ((δ : SL(2, ℤ)) * δ₁)
    refine ⟨L₁ - L, ?_⟩
    have : (fun w : ℍ => G ((δ : SL(2, ℤ)) • (δ₁ • w)) - L) =
        fun w : ℍ => G (((δ : SL(2, ℤ)) * δ₁) • w) - L := by
      funext w; rw [mul_smul]
    rw [this]
    exact hL₁.sub_const L

theorem periodOf_act [Γ'.FiniteIndex] (δ : Γ) (g : CuspForm Γ' 2) (γ : Γ') :
    ModularCurve.periodOf Γ' γ (act hle hn δ g) =
      ModularCurve.periodOf Γ' ⟨(δ : SL(2, ℤ)) * γ * (δ : SL(2, ℤ))⁻¹, conj_mem hle hn γ.2 δ⟩ g := by
  obtain ⟨G, hG⟩ := ModularCurve.exists_hasEquivariantPrimitiveOf Γ' g
  obtain ⟨L, hG'⟩ := hasEquivariantPrimitiveOf_act hle hn δ g hG
  rw [ModularCurve.periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf Γ' _ hG' γ,
    ModularCurve.periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf Γ' _ hG _]
  have hequiv : ModularCurve.Period.IsEquivariantPrimitive Γ' G := hG.2.2.1
  set ε : Γ' := ⟨(δ : SL(2, ℤ)) * γ * (δ : SL(2, ℤ))⁻¹, conj_mem hle hn γ.2 δ⟩ with hε
  have hz : (δ : SL(2, ℤ)) • ((γ : SL(2, ℤ)) • UpperHalfPlane.I) =
      (ε : SL(2, ℤ)) • ((δ : SL(2, ℤ)) • UpperHalfPlane.I) := by
    rw [← mul_smul, ← mul_smul, hε]
    congr 1
    group
  simp only [sub_sub_sub_cancel_right]
  rw [hz]
  have h1 := hequiv.sub_eq_period ε ((δ : SL(2, ℤ)) • UpperHalfPlane.I)
  have h2 := hequiv.sub_eq_period ε UpperHalfPlane.I
  rw [h1, ← h2]

end Action

section Descent

variable {Γ' Γ : Subgroup SL(2, ℤ)} [Γ'.FiniteIndex]

private theorem _root_.ModularCurve.ESDescent.finiteIndex_of_le (hle : Γ' ≤ Γ) : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hle

p2m_export "ModularCurve.ESDescent" "finiteIndex_of_le"

theorem isCusp_iff [Γ.FiniteIndex] {c : OnePoint ℝ} :
    IsCusp c (Γ : Subgroup (GL (Fin 2) ℝ)) ↔ IsCusp c (Γ' : Subgroup (GL (Fin 2) ℝ)) := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (Γ : Subgroup (GL (Fin 2) ℝ)),
    Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (Γ' : Subgroup (GL (Fin 2) ℝ))]

def lift [Γ.FiniteIndex] (g : CuspForm Γ' 2)
    (hg : ∀ δ : Γ, ((g : ℍ → ℂ) ∣[(2 : ℤ)] (δ : SL(2, ℤ))) = g) : CuspForm Γ 2 where
  toFun := g
  slash_action_eq' A hA := by
    obtain ⟨δ, hδ, rfl⟩ := hA
    exact hg ⟨δ, hδ⟩
  holo' := g.holo'
  zero_at_cusps' hc := CuspFormClass.zero_at_cusps g ((isCusp_iff (Γ' := Γ') (Γ := Γ)).mp hc)

theorem lower_lift [Γ.FiniteIndex] (hle : Γ' ≤ Γ) (g : CuspForm Γ' 2)
    (hg : ∀ δ : Γ, ((g : ℍ → ℂ) ∣[(2 : ℤ)] (δ : SL(2, ℤ))) = g) :
    lower hle (lift (Γ' := Γ') g hg) = g := by
  ext z; rfl

theorem realPeriodMap_surjective [Γ.FiniteIndex] (hle : Γ' ≤ Γ) (hn : (Γ'.subgroupOf Γ).Normal)
    (hbij : Function.Bijective (realPeriodMap Γ')) :
    Function.Surjective (realPeriodMap Γ) := by
  intro x
  obtain ⟨g, hg⟩ := hbij.2 (res hle x)

  have hinv : ∀ δ : Γ, act hle hn δ g = g := by
    intro δ
    apply hbij.1
    apply Subtype.ext
    refine AddMonoidHom.ext fun a => ?_
    rw [← ofMul_toMul a, realPeriodMap_apply, realPeriodMap_apply, periodOf_act hle hn δ g]
    set γ : Γ' := Additive.toMul a
    have h1 := congrArg (fun φ : ModularCurve.Period.parabolicHoms ℝ Γ' ℝ =>
      (φ : Additive Γ' →+ ℝ) (Additive.ofMul
        (⟨(δ : SL(2, ℤ)) * γ * (δ : SL(2, ℤ))⁻¹, conj_mem hle hn γ.2 δ⟩ : Γ'))) hg
    have h2 := congrArg (fun φ : ModularCurve.Period.parabolicHoms ℝ Γ' ℝ =>
      (φ : Additive Γ' →+ ℝ) (Additive.ofMul γ)) hg
    simp only [realPeriodMap_apply, res_apply] at h1 h2
    rw [h1, h2]

    have hconj : (⟨(δ : SL(2, ℤ)) * γ * (δ : SL(2, ℤ))⁻¹, hle (conj_mem hle hn γ.2 δ)⟩ : Γ) =
        δ * ⟨(γ : SL(2, ℤ)), hle γ.2⟩ * δ⁻¹ := rfl
    rw [hconj, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
    ring
  have hinv' : ∀ δ : Γ, ((g : ℍ → ℂ) ∣[(2 : ℤ)] (δ : SL(2, ℤ))) = g := fun δ => by
    have := congrArg (fun F : CuspForm Γ' 2 => (F : ℍ → ℂ)) (hinv δ)
    simpa only [coe_act] using this
  refine ⟨lift (Γ' := Γ') g hinv', ?_⟩
  apply res_injective hle
  rw [res_realPeriodMap hle, lower_lift hle g hinv', hg]

theorem main (hle : Γ' ≤ Γ) (hn : (Γ'.subgroupOf Γ).Normal)
    (h : Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ Γ' ℤ) ≤
      2 * Module.finrank ℂ (CuspForm Γ' 2)) :
    Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ) ≤
      2 * Module.finrank ℂ (CuspForm Γ 2) := by
  haveI : Γ.FiniteIndex := finiteIndex_of_le hle
  have hbij := realPeriodMap_bijective_of_le Γ' h
  have hsurj := realPeriodMap_surjective hle hn hbij
  obtain ⟨hfin, heq⟩ := finite_and_finrank_parabolicHoms_real_eq Γ
  haveI := hfin
  rw [← heq, ← finrank_real_cuspForm]
  exact LinearMap.finrank_le_finrank_of_surjective hsurj

end Descent

end ModularCurve.ESDescent
p2m_reactivate "P2MW.S_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal.ModularCurve P2MW.S_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal.ModularCurve.ESDescent"
p2m_reactivate "P2MW.S_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal.ModularCurve P2MW.S_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal.ModularCurve.ESDescent"

theorem solution
    (Γ' Γ : Subgroup SL(2, ℤ)) [Γ'.FiniteIndex] (hle : Γ' ≤ Γ) (hn : (Γ'.subgroupOf Γ).Normal)
    (h : Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ Γ' ℤ) ≤
      2 * Module.finrank ℂ (CuspForm Γ' 2)) :
    Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ) ≤
      2 * Module.finrank ℂ (CuspForm Γ 2) :=
  ModularCurve.ESDescent.main hle hn h

end S_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal
end P2MW
export P2MW.S_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal (solution)
