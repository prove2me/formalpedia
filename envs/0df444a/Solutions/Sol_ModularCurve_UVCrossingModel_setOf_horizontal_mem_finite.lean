-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.setOf_horizontal_mem_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/17cf6466-9938-5931-bcb8-a367c1f91a64

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices
import Definitions.Def_ModularCurve_UVCrossingChart
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_range_chartHom_eq_fixedSubring
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_mem_fixedSubring_eq_add_mul_U
import Theorems.Thm_ModularCurve_UVCrossingModel_chartHom_C
import Theorems.Thm_ModularCurve_UVCrossingModel_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_setOf_horizontal_mem_finite

set_option maxHeartbeats 800000
set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing
open scoped TensorProduct

namespace P1Arch

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing
open scoped TensorProduct

section Toolkit
variable {W : Type u} [CommRing W]
variable {R : Type u} [CommRing R] [Algebra W R]

noncomputable def mulQuot (x y : R) : (R ⧸ Ideal.span {y}) →ₗ[R] (R ⧸ Ideal.span {x * y}) :=
  Submodule.mapQ (Ideal.span {y}) (Ideal.span {x * y}) (LinearMap.mulLeft R x) (by
    intro z hz
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    exact Ideal.mem_span_singleton'.mpr ⟨c, by ring⟩)

theorem mulQuot_mk (x y r : R) :
    mulQuot x y (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (x * r) := rfl

noncomputable def projQuot (x y : R) : (R ⧸ Ideal.span {x * y}) →ₗ[R] (R ⧸ Ideal.span {x}) :=
  Submodule.mapQ (Ideal.span {x * y}) (Ideal.span {x}) LinearMap.id (by
    intro z hz
    rw [Submodule.mem_comap, LinearMap.id_apply]
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    exact Ideal.mem_span_singleton'.mpr ⟨c * y, by ring⟩)

theorem projQuot_mk (x y r : R) :
    projQuot x y (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ r := rfl

theorem projQuot_surjective (x y : R) : Function.Surjective (projQuot x y) := by
  intro m
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  exact ⟨Ideal.Quotient.mk _ r, rfl⟩

theorem exact_mulQuot_projQuot (x y : R) : Function.Exact (mulQuot x y) (projQuot x y) := by
  intro m
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [projQuot_mk, Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hr
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    exact ⟨Ideal.Quotient.mk _ c, by rw [mulQuot_mk, mul_comm x c]⟩
  · rintro ⟨m', hm'⟩
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective m'
    rw [mulQuot_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hm'
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hm'
    refine Ideal.mem_span_singleton'.mpr ⟨r' - s * y, ?_⟩
    have : r = x * r' - s * (x * y) := by rw [hs]; ring
    rw [this]; ring

theorem tensor_eq_zero_of_smul_eq_zero {K : Type*} [CommRing K] [Algebra W K] {M : Type*} [AddCommGroup M]
    [Module W M] (w : W) (hw : IsUnit (algebraMap W K w)) (hM : ∀ m : M, w • m = 0) (z : K ⊗[W] M) : z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul k m =>
    obtain ⟨u, hu⟩ := hw
    have hk : k = w • (k * ↑u⁻¹) := by
      rw [Algebra.smul_def, ← hu, ← mul_assoc, mul_comm (↑u) k, mul_assoc, Units.mul_inv, mul_one]
    rw [hk, TensorProduct.smul_tmul, hM, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

theorem subsingleton_tensor_of_smul_eq_zero {K : Type*} [CommRing K] [Algebra W K] {M : Type*} [AddCommGroup M]
    [Module W M] (w : W) (hw : IsUnit (algebraMap W K w)) (hM : ∀ m : M, w • m = 0) :
    Subsingleton (K ⊗[W] M) :=
  ⟨fun x y => by rw [tensor_eq_zero_of_smul_eq_zero w hw hM x, tensor_eq_zero_of_smul_eq_zero w hw hM y]⟩

theorem smul_quotient_eq_zero_of_algebraMap_mem (w : W) (J : Ideal R) (hJ : algebraMap W R w ∈ J)
    (m : R ⧸ J) : w • m = 0 := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [← Ideal.Quotient.mkₐ_eq_mk W, ← map_smul, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  convert J.mul_mem_right r hJ using 1
  exact Algebra.smul_def w r

theorem finite_tensor_quotient_mul_of_torsion [IsDomain W] (x y : R) (w : W)
    (hw : IsUnit (algebraMap W (FractionRing W) w)) (hy : algebraMap W R w ∈ Ideal.span {y})
    [Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] (R ⧸ Ideal.span {x}))] :
    Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] (R ⧸ Ideal.span {x * y})) := by
  let f := ((mulQuot x y).restrictScalars W).baseChange (FractionRing W)
  let g := ((projQuot x y).restrictScalars W).baseChange (FractionRing W)
  have hgsurj : Function.Surjective g := by
    change Function.Surjective (((projQuot x y).restrictScalars W).baseChange (FractionRing W))
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective _ (projQuot_surjective x y)
  have hexact : Function.Exact f g := by
    change Function.Exact (((mulQuot x y).restrictScalars W).baseChange (FractionRing W))
      (((projQuot x y).restrictScalars W).baseChange (FractionRing W))
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact (FractionRing W) (exact_mulQuot_projQuot x y) (projQuot_surjective x y)
  haveI : Subsingleton ((FractionRing W) ⊗[W] (R ⧸ Ideal.span {y})) :=
    subsingleton_tensor_of_smul_eq_zero w hw (smul_quotient_eq_zero_of_algebraMap_mem w _ hy)
  exact Module.Finite.of_exact hexact hgsurj

end Toolkit

section Wside
variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

local notation "addv" => (IsDiscreteValuationRing.addVal W : W → ℕ∞)

theorem exists_eq_mul_C_pow_of_ne_zero (ϖ : W) (hϖ : Irreducible ϖ) (g : PowerSeries W) (hg : g ≠ 0) :
    ∃ (m : ℕ) (g' : PowerSeries W), (∃ k, IsUnit (PowerSeries.coeff k g')) ∧ g = g' * PowerSeries.C (ϖ ^ m) := by
  classical
  have hex : ∃ m : ℕ, ∃ k, addv (PowerSeries.coeff k g) = m := by
    obtain ⟨k, hk⟩ : ∃ k, PowerSeries.coeff k g ≠ 0 := by
      by_contra h
      push_neg at h
      exact hg (PowerSeries.ext fun k => by simpa using h k)
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
      (mt IsDiscreteValuationRing.addVal_eq_top_iff.mp hk)
    exact ⟨m, k, hm.symm⟩
  let m := Nat.find hex
  obtain ⟨k₀, hk₀⟩ : ∃ k, addv (PowerSeries.coeff k g) = m := Nat.find_spec hex
  have hmin : ∀ k, (m : ℕ∞) ≤ addv (PowerSeries.coeff k g) := by
    intro k
    by_cases h0 : PowerSeries.coeff k g = 0
    · rw [h0, (IsDiscreteValuationRing.addVal W).map_zero]; exact le_top
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (mt IsDiscreteValuationRing.addVal_eq_top_iff.mp h0)
      rw [← hn]
      exact_mod_cast Nat.find_min' hex ⟨k, hn.symm⟩
  have hdvd : ∀ k, ϖ ^ m ∣ PowerSeries.coeff k g := by
    intro k
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ]
    simpa using hmin k
  choose c hc using hdvd
  refine ⟨m, PowerSeries.mk c, ⟨k₀, ?_⟩, ?_⟩
  · rw [PowerSeries.coeff_mk, ← IsDiscreteValuationRing.addVal_eq_zero_iff]
    have h1 : addv (PowerSeries.coeff k₀ g) = (m : ℕ∞) + addv (c k₀) := by
      rw [hc k₀, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
        IsDiscreteValuationRing.addVal_uniformizer hϖ]
      simp
    rw [hk₀] at h1
    have h2 : (m : ℕ∞) + addv (c k₀) = (m : ℕ∞) + 0 := by rw [add_zero]; exact h1.symm
    exact (WithTop.add_left_inj (ENat.coe_ne_top m)).mp h2
  · ext k
    rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_mk, mul_comm]
    exact hc k

variable [IsAdicComplete (maximalIdeal W) W]

theorem moduleFinite_quotient_of_isUnit_coeff (g : PowerSeries W) (hg : ∃ k, IsUnit (PowerSeries.coeff k g)) :
    Module.Finite W (PowerSeries W ⧸ Ideal.span {g}) := by
  classical
  have hres : PowerSeries.map (IsLocalRing.residue W) g ≠ 0 := by
    obtain ⟨k, hk⟩ := hg
    intro h
    have := congrArg (PowerSeries.coeff k) h
    rw [PowerSeries.coeff_map, map_zero] at this
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hk this
  set d : ℕ := (PowerSeries.map (IsLocalRing.residue W) g).order.toNat with hd

  let φ : Polynomial.degreeLT W d →ₗ[W] (PowerSeries W ⧸ Ideal.span {g}) :=
    ((Ideal.Quotient.mkₐ W (Ideal.span {g})).toLinearMap.comp
      (Polynomial.coeToPowerSeries.algHom W).toLinearMap).comp (Polynomial.degreeLT W d).subtype
  haveI : Module.Finite W (Polynomial.degreeLT W d) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv W d).symm
  refine Module.Finite.of_surjective φ ?_
  intro q
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨q', r, hdiv⟩ := PowerSeries.exists_isWeierstrassDivision f (g := g) hres
  refine ⟨⟨r, Polynomial.mem_degreeLT.mpr hdiv.degree_lt⟩, ?_⟩
  change Ideal.Quotient.mk (Ideal.span {g}) ((r : PowerSeries W)) = Ideal.Quotient.mk _ f
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, hdiv.eq_mul_add]
  exact Ideal.mem_span_singleton'.mpr ⟨-q', by ring⟩

omit [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] in
theorem algebraMap_powerSeries_apply (w : W) : algebraMap W (PowerSeries W) w = PowerSeries.C w := by
  rw [PowerSeries.algebraMap_apply]
  rfl

theorem finite_tensor_powerSeries_quotient (ϖ : W) (hϖ : Irreducible ϖ) (g : PowerSeries W) (hg : g ≠ 0) :
    Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] (PowerSeries W ⧸ Ideal.span {g})) := by
  obtain ⟨m, g', hunit, rfl⟩ := exists_eq_mul_C_pow_of_ne_zero ϖ hϖ g hg
  haveI := moduleFinite_quotient_of_isUnit_coeff g' hunit
  haveI : Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] (PowerSeries W ⧸ Ideal.span {g'})) :=
    inferInstance
  refine finite_tensor_quotient_mul_of_torsion g' (PowerSeries.C (ϖ ^ m)) (ϖ ^ m) ?_ ?_
  · exact isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective W (FractionRing W))).mpr (pow_ne_zero m hϖ.ne_zero))
  · rw [algebraMap_powerSeries_apply]
    exact Ideal.subset_span rfl

end Wside

end P1Arch

namespace P1Arch

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing
open scoped TensorProduct

section Rside
variable {W : Type u} [CommRing W]

theorem algebraMap_eq_const (π w : W) : algebraMap W (UVCrossingModel W π) w = const π w := by
  change Ideal.Quotient.mk _ (algebraMap W (MvPowerSeries (Fin 2) W) w) = _
  rw [MvPowerSeries.algebraMap_apply]
  rfl

theorem isUnit_of_isUnit_const_self (π : W) (h : IsUnit (const π π)) : IsUnit π := by
  obtain ⟨y, hy⟩ := h.exists_right_inv
  obtain ⟨G, rfl⟩ := mk_surjective π y
  rw [const, ← map_mul, ← (mk π).map_one] at hy
  change Ideal.Quotient.mk (uvCrossingIdeal W π) _ = Ideal.Quotient.mk (uvCrossingIdeal W π) _ at hy
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hy
  obtain ⟨H, hH⟩ := Ideal.mem_span_singleton'.mp hy
  have h0 := congrArg MvPowerSeries.constantCoeff hH
  simp only [map_mul, map_sub, map_one, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C] at h0
  exact isUnit_iff_exists_inv.mpr ⟨MvPowerSeries.constantCoeff G + MvPowerSeries.constantCoeff H,
    by linear_combination (-1 : W) * h0⟩

theorem crossingSwap_crossingSwap (π : W) (x : UVCrossingModel W π) :
    crossingSwap π (crossingSwap π x) = x := by
  obtain ⟨F, rfl⟩ := mk_surjective π x
  rw [crossingSwap_mk, crossingSwap_mk]
  congr 1
  change (MvPowerSeries.renameEquiv W (Equiv.swap (0 : Fin 2) 1))
      ((MvPowerSeries.renameEquiv W (Equiv.swap (0 : Fin 2) 1)) F) = F
  conv_lhs => rw [← Equiv.symm_swap, ← MvPowerSeries.renameEquiv_symm]
  exact (MvPowerSeries.renameEquiv W (Equiv.swap (0 : Fin 2) 1)).symm_apply_apply F

theorem isPrecomplete_span_pow (ϖ : W) (e : ℕ) (he : 1 ≤ e) [IsPrecomplete (Ideal.span {ϖ}) W] :
    IsPrecomplete (Ideal.span {ϖ ^ e}) W := by
  have key : ∀ k, (Ideal.span {ϖ ^ e}) ^ k = (Ideal.span {ϖ}) ^ (e * k) := by
    intro k
    rw [Ideal.span_singleton_pow, ← pow_mul, ← Ideal.span_singleton_pow]
  constructor
  intro f hf
  have hf' : ∀ {m n}, m ≤ n → f m ≡ f n [SMOD (Ideal.span {ϖ}) ^ m • (⊤ : Submodule W W)] := by
    intro m n hmn
    refine SModEq.mono ?_ (hf hmn)
    rw [key]
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by nlinarith))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' f hf'
  refine ⟨L, fun n => ?_⟩
  have h1 : f n ≡ f (e * n) [SMOD (Ideal.span {ϖ ^ e}) ^ n • (⊤ : Submodule W W)] := hf (by nlinarith)
  have h2 : f (e * n) ≡ L [SMOD (Ideal.span {ϖ ^ e}) ^ n • (⊤ : Submodule W W)] := by
    rw [key]; exact hL (e * n)
  exact h1.trans h2

end Rside

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

local notation "addv" => (IsDiscreteValuationRing.addVal W : W → ℕ∞)

variable [IsAdicComplete (maximalIdeal W) W]

theorem finite_tensor_quotient (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0) :
    Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})) := by
  classical
  obtain ⟨hdom, hloc, -⟩ :=
    ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete ϖ hϖ e he
  haveI := hdom
  haveI := hloc
  haveI : IsNoetherianRing (UVCrossingModel W (ϖ ^ e)) := UVCrossingModel.isNoetherianRing (ϖ ^ e)
  have hmax : maximalIdeal W = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  haveI : IsAdicComplete (Ideal.span {ϖ}) W := hmax ▸ (inferInstance : IsAdicComplete (maximalIdeal W) W)
  haveI : IsPrecomplete (Ideal.span {ϖ ^ e}) W := isPrecomplete_span_pow ϖ e he

  have hreg : ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C (ϖ ^ e)) ∈
      nonZeroDivisors (MvPowerSeries (Fin 2) W) := by
    apply mem_nonZeroDivisors_of_ne_zero
    intro h
    have h0 := congrArg MvPowerSeries.constantCoeff h
    simp only [map_sub, map_mul, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C, map_zero,
      mul_zero, zero_sub, neg_eq_zero] at h0
    exact pow_ne_zero e hϖ.ne_zero h0
  have hsep : ∀ y : UVCrossingModel W (ϖ ^ e), (∀ B : ℕ, y ∈ Ideal.span {const (ϖ ^ e) (ϖ ^ e)} ^ B) → y = 0 := by
    intro y hy
    have hne : Ideal.span {const (ϖ ^ e) (ϖ ^ e)} ≠ ⊤ := by
      apply Ideal.span_singleton_ne_top
      intro hu
      exact hϖ.1 ((isUnit_pow_iff (by omega)).mp (isUnit_of_isUnit_const_self _ hu))
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing _ hne
    have hmem : y ∈ (⨅ i : ℕ, Ideal.span {const (ϖ ^ e) (ϖ ^ e)} ^ i) := Ideal.mem_iInf.mpr hy
    rw [hbot] at hmem
    exact Ideal.mem_bot.mp hmem
  have hrange := ModularCurve.UVCrossingModel.range_chartHom_eq_fixedSubring (π := ϖ ^ e) hreg hsep

  have hn_fixed : x * crossingSwap (ϖ ^ e) x ∈ fixedSubring (ϖ ^ e) := by
    rw [mem_fixedSubring_iff, map_mul, crossingSwap_crossingSwap, mul_comm]
  have hn_range : x * crossingSwap (ϖ ^ e) x ∈ (chartHom (ϖ ^ e)).range := hrange ▸ hn_fixed
  obtain ⟨n, hn⟩ := RingHom.mem_range.mp hn_range
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [map_zero] at hn
    exact mul_ne_zero hx ((RingEquiv.map_ne_zero_iff (crossingSwap (ϖ ^ e))).mpr hx) hn.symm
  haveI hfinQ := finite_tensor_powerSeries_quotient ϖ hϖ n hn0

  let χ : PowerSeries W →ₐ[W] UVCrossingModel W (ϖ ^ e) := AlgHom.mk (chartHom (ϖ ^ e)) (fun w => by
    change chartHom (ϖ ^ e) (algebraMap W (PowerSeries W) w) = algebraMap W _ w
    rw [algebraMap_powerSeries_apply, ModularCurve.UVCrossingModel.chartHom_C, algebraMap_eq_const])
  let ψ : UVCrossingModel W (ϖ ^ e) → (PowerSeries W →ₗ[W] (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})) :=
    fun r₀ => (Ideal.Quotient.mkₐ W (Ideal.span {x})).toLinearMap ∘ₗ (LinearMap.mulRight W r₀) ∘ₗ χ.toLinearMap
  have hψ : ∀ r₀ f, ψ r₀ f = Ideal.Quotient.mk (Ideal.span {x}) (chartHom (ϖ ^ e) f * r₀) := fun _ _ => rfl
  have hker : ∀ r₀, (Ideal.span {n}).restrictScalars W ≤ LinearMap.ker (ψ r₀) := by
    intro r₀ z hz
    rw [Submodule.restrictScalars_mem] at hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    rw [LinearMap.mem_ker, hψ, (chartHom (ϖ ^ e)).map_mul, hn, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton'.mpr ⟨chartHom (ϖ ^ e) c * crossingSwap (ϖ ^ e) x * r₀, by ring⟩
  let P : Submodule W (PowerSeries W) := (Ideal.span {n}).restrictScalars W
  let Φ : ((PowerSeries W ⧸ P) × (PowerSeries W ⧸ P)) →ₗ[W] (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) :=
    (P.liftQ (ψ 1) (hker 1)).coprod (P.liftQ (ψ (U (ϖ ^ e))) (hker _))
  have hΦ : Function.Surjective Φ := by
    intro q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, b, ha, hb, rfl⟩ := ModularCurve.UVCrossingModel.exists_mem_fixedSubring_eq_add_mul_U (ϖ ^ e) r
    rw [← hrange] at ha hb
    obtain ⟨f, rfl⟩ := RingHom.mem_range.mp ha
    obtain ⟨g, rfl⟩ := RingHom.mem_range.mp hb
    refine ⟨(Submodule.Quotient.mk f, Submodule.Quotient.mk g), ?_⟩
    rw [LinearMap.coprod_apply, Submodule.liftQ_apply, Submodule.liftQ_apply, hψ, hψ, ← map_add, mul_one]

  let eQ : (PowerSeries W ⧸ P) ≃ₗ[W] (PowerSeries W ⧸ Ideal.span {n}) :=
    Submodule.Quotient.restrictScalarsEquiv W (Ideal.span {n})
  haveI : Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] (PowerSeries W ⧸ P)) :=
    Module.Finite.equiv (LinearEquiv.baseChange W (FractionRing W) _ _ eQ).symm
  haveI : Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] ((PowerSeries W ⧸ P) × (PowerSeries W ⧸ P))) :=
    Module.Finite.equiv (TensorProduct.prodRight W (FractionRing W) (FractionRing W) (PowerSeries W ⧸ P)
      (PowerSeries W ⧸ P)).symm
  refine Module.Finite.of_surjective (Φ.baseChange (FractionRing W)) ?_
  rw [LinearMap.baseChange_eq_ltensor]
  exact LinearMap.lTensor_surjective _ hΦ

end P1Arch

namespace P1Arch
open ModularCurve ModularCurve.UVCrossingModel IsLocalRing
open scoped TensorProduct

section Fin
variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem setOf_prime_disjoint_finite (B : Type u) [CommRing B] [Algebra W B]
    [Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] B)] :
    {P : PrimeSpectrum B | Disjoint (↑(Algebra.algebraMapSubmonoid B (nonZeroDivisors W)) : Set B) ↑P.asIdeal}.Finite := by
  classical
  set A := (FractionRing W) ⊗[W] B with hA
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors W)) A :=
    IsLocalization.tensorRight (FractionRing W) (nonZeroDivisors W)
  haveI : IsArtinianRing A := IsArtinianRing.of_finite (FractionRing W) A
  refine (Set.finite_range (PrimeSpectrum.comap (algebraMap B A))).subset ?_
  intro P hP
  haveI : P.asIdeal.IsPrime := P.isPrime
  haveI hQ : (Ideal.map (algebraMap B A) P.asIdeal).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ A P.asIdeal P.isPrime hP
  refine ⟨⟨Ideal.map (algebraMap B A) P.asIdeal, hQ⟩, ?_⟩
  ext1
  exact IsLocalization.under_map_of_isPrime_disjoint (Algebra.algebraMapSubmonoid B (nonZeroDivisors W)) A
    P.isPrime hP

variable [IsAdicComplete (maximalIdeal W) W]

theorem setOf_horizontal_mem_finite (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0) :
    {P : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)) |
      P.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ P.asIdeal ∧ x ∈ P.asIdeal}.Finite := by
  classical
  haveI : Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})) :=
    finite_tensor_quotient ϖ hϖ e he x hx
  have hfin := setOf_prime_disjoint_finite (W := W) (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})

  let g : PrimeSpectrum (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) → PrimeSpectrum (UVCrossingModel W (ϖ ^ e)) :=
    PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {x}))
  refine ((hfin.image g).subset ?_)
  rintro P ⟨hP0, hPϖ, hxP⟩
  have hle : Ideal.span {x} ≤ P.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hxP
  have hker : RingHom.ker (Ideal.Quotient.mk (Ideal.span {x})) ≤ P.asIdeal := by rw [Ideal.mk_ker]; exact hle
  haveI : P.asIdeal.IsPrime := P.isPrime
  haveI hPbar : (Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) P.asIdeal).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hback : Ideal.comap (Ideal.Quotient.mk (Ideal.span {x})) (Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) P.asIdeal)
      = P.asIdeal := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hle
  refine ⟨⟨Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) P.asIdeal, hPbar⟩, ?_, ?_⟩
  ·
    change Disjoint (↑(Algebra.algebraMapSubmonoid (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) (nonZeroDivisors W)) :
        Set (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}))
      ↑(Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) P.asIdeal)
    rw [Set.disjoint_left]
    intro b hb hbP
    obtain ⟨w, hw, rfl⟩ := Submonoid.mem_map.mp hb
    have hw0 : (w : W) ≠ 0 := nonZeroDivisors.ne_zero hw

    rw [← Ideal.Quotient.mk_algebraMap, algebraMap_eq_const] at hbP
    have hmem : const (ϖ ^ e) w ∈ P.asIdeal := by
      rw [← hback]; exact Ideal.mem_comap.mpr hbP
    obtain ⟨n, u, hwu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw0 hϖ
    have hmem' : const (ϖ ^ e) ϖ ^ n ∈ P.asIdeal := by
      have h1 : const (ϖ ^ e) w = const (ϖ ^ e) (u : W) * const (ϖ ^ e) ϖ ^ n := by
        rw [hwu, ← constHom_apply, ← constHom_apply, ← constHom_apply, map_mul, map_pow]
      rw [h1] at hmem
      have hu : IsUnit (const (ϖ ^ e) (u : W)) := by
        rw [← constHom_apply]; exact (Units.isUnit u).map _
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hmem
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn, pow_zero] at hmem'
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hmem')
    · exact hPϖ (P.isPrime.mem_of_pow_mem n hmem')
  · ext1
    exact hback

end Fin

end P1Arch

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing in
theorem solution
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0) :
    {P : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)) | P.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ P.asIdeal ∧ x ∈ P.asIdeal}.Finite :=
  P1Arch.setOf_horizontal_mem_finite ϖ hϖ e he x hx

end S_ModularCurve_UVCrossingModel_setOf_horizontal_mem_finite
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_setOf_horizontal_mem_finite (solution)
