-- Prove2me | solution 1 for GlobalTheory.QNorm.sUnits_fg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:11.201802+00:00
-- url     : https://prove2.me/submissions/b4403919-6726-4495-a2af-e0de61d13930

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsNumberFieldFg
import Theorems.Thm_GlobalTheory_QNorm_mem_sUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
noncomputable section
namespace GlobalTheory.QNorm
open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma valuation_algebraMap_unit_eq_one {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (u : (𝓞 F)ˣ) : v.valuation F (algebraMap (𝓞 F) F u) = 1 := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  exact fun h => v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h u.isUnit)
open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma exists_unit_of_valuation_eq_one {F : Type} [Field F] [NumberField F] (y : Fˣ)
    (hy : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F y = 1) :
    ∃ u : (𝓞 F)ˣ, algebraMap (𝓞 F) F u = y := by
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (y : F)
    fun v => (hy v).le
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F ((y⁻¹ : Fˣ) : F)
    fun v => by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hy v, inv_one]
  have hab : a * b = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  exact ⟨⟨a, b, hab, by rw [mul_comm, hab]⟩, ha⟩
end GlobalTheory.QNorm
end
end

set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
noncomputable section
open GlobalTheory GlobalTheory.QNorm
open NumberField IsDedekindDomain
open scoped WithZero
namespace GlobalTheory.QNorm
namespace _root_.GlobalTheory.QNorm
theorem _root_.solution :
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
      Group.FG (_root_.GlobalTheory.QNorm.sUnits F S) := by
  intro F _ _ S
  set G := _root_.GlobalTheory.QNorm.sUnits F S
  let val : HeightOneSpectrum (𝓞 F) → G →* Multiplicative ℤ := fun v =>
    (WithZero.unitsWithZeroEquiv.toMonoidHom.comp
      (Units.map (v.valuation F : F →* ℤᵐ⁰))).comp G.subtype
  have hval : ∀ v x, val v x = 1 ↔ v.valuation F ((x : Fˣ) : F) = 1 := by
    intro v x
    simp only [val, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, Units.ext_iff, Units.coe_map, Units.val_one]
    rfl
  let f : Additive G →+ (S → ℤ) :=
    { toFun := fun x v => Multiplicative.toAdd (val v.1 x.toMul)
      map_zero' := by ext v; simp
      map_add' := fun x y => by ext v; simp }
  let ψ : (𝓞 F)ˣ →* G :=
    { toFun := fun u => ⟨Units.map (algebraMap (𝓞 F) F : (𝓞 F) →* F) u, by
        rw [_root_.GlobalTheory.QNorm.mem_sUnits]
        intro v _
        exact valuation_algebraMap_unit_eq_one v u⟩
      map_one' := by ext; simp
      map_mul' := fun u w => by ext; simp }
  let g : Additive (𝓞 F)ˣ →+ Additive G := MonoidHom.toAdditive ψ
  have hker : f.toIntLinearMap.ker = LinearMap.range g.toIntLinearMap := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.mem_range, AddMonoidHom.coe_toIntLinearMap]
    constructor
    · intro hx
      obtain ⟨u, hu⟩ := exists_unit_of_valuation_eq_one ((x.toMul : G) : Fˣ) fun v => by
        by_cases hv : v ∈ S
        · rw [← hval]
          have := congrFun hx ⟨v, hv⟩
          simpa [f] using this
        · exact (_root_.GlobalTheory.QNorm.mem_sUnits F S _).mp x.toMul.2 v hv
      refine ⟨Additive.ofMul u, ?_⟩
      apply Additive.toMul.injective
      ext
      simpa [g, ψ] using hu
    · rintro ⟨u, rfl⟩
      ext v
      have : val v.1 (ψ u.toMul) = 1 :=
        (hval _ _).mpr (valuation_algebraMap_unit_eq_one v.1 u.toMul)
      simpa [f, g] using this
  have htop : (⊤ : Submodule ℤ (Additive G)).FG := by
    refine Submodule.fg_of_fg_map_of_fg_inf_ker f.toIntLinearMap (IsNoetherian.noetherian _) ?_
    rw [top_inf_eq, hker, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  have : Module.Finite ℤ (Additive G) := ⟨htop⟩
  rw [Group.fg_iff_monoid_fg, Monoid.fg_iff_add_fg, ← AddGroup.fg_iff_addMonoid_fg]
  exact Module.Finite.iff_addGroup_fg.mp this
end _root_.GlobalTheory.QNorm
end GlobalTheory.QNorm
