-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.hasValue_nodeResidueFst_div_nodeResidueFst_y_pow_of_sub_mul_V_pow_mem_of_hasValue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/0e44d155-a325-5dbf-85f3-b2993db710b1

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_nodeResidueFst_div_nodeResidueFst_y_pow_of_sub_mul_V_pow_mem_of_hasValue

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

universe u v

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_nodeResidueFst_div_nodeResidueFst_y_pow_of_sub_mul_V_pow_mem_of_hasValue.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_nodeResidueFst_div_nodeResidueFst_y_pow_of_sub_mul_V_pow_mem_of_hasValue.ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence ssPlaces modularFunctionFieldFullC NodeLocalized.coeffSubring NodeLocalized.redRestrict uvCrossingIdeal UVCrossingModel UVCrossingModel.mk UVCrossingModel.U UVCrossingModel.V UVCrossingModel.const"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "mk U V const mk_surjective S D"
namespace Model
p2m_open "ModularCurve.UVCrossingModel ModularCurve"

variable {W : Type u} [CommRing W] (a : W)

theorem constantCoeff_crossing :
    MvPowerSeries.constantCoeff ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C a) = -a := by
  simp [MvPowerSeries.constantCoeff_X]

theorem constantCoeff_sub_mem_span_of_mk_eq {G G' : MvPowerSeries (Fin 2) W} (h : mk a G = mk a G') :
    MvPowerSeries.constantCoeff G - MvPowerSeries.constantCoeff G' ∈ Ideal.span {a} := by
  have hI : G - G' ∈ uvCrossingIdeal W a := (Ideal.Quotient.eq).mp h
  obtain ⟨H, hH⟩ := Ideal.mem_span_singleton'.mp hI
  have := congrArg MvPowerSeries.constantCoeff hH
  rw [map_mul, constantCoeff_crossing, map_sub] at this
  rw [← this]
  exact Ideal.mem_span_singleton'.mpr ⟨-MvPowerSeries.constantCoeff H, by ring⟩

theorem mem_span_X_of_constantCoeff_eq_zero {G : MvPowerSeries (Fin 2) W} (hG : MvPowerSeries.constantCoeff G = 0) :
    G ∈ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1} := by
  classical

  let G0 : MvPowerSeries (Fin 2) W := fun m => if m 0 = 0 then 0 else G m
  let G1 : MvPowerSeries (Fin 2) W := fun m => if m 0 = 0 then G m else 0
  have hsplit : G = G0 + G1 := by
    funext m
    show G m = G0 m + G1 m
    simp only [G0, G1]
    split_ifs <;> simp
  have h0 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) ∣ G0 := by
    apply MvPowerSeries.X_dvd_iff.mpr
    intro m hm
    change G0 m = 0
    simp only [G0, hm, if_true]
  have h1 : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W) ∣ G1 := by
    apply MvPowerSeries.X_dvd_iff.mpr
    intro m hm
    change G1 m = 0
    simp only [G1]
    split_ifs with h00
    · have : m = 0 := Finsupp.ext fun i => by fin_cases i <;> simp [h00, hm]
      rw [this]
      exact hG
    · rfl
  obtain ⟨H0, hH0⟩ := h0
  obtain ⟨H1, hH1⟩ := h1
  rw [hsplit, hH0, hH1]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))

theorem mk_mem_span_U_V_of_constantCoeff_eq_zero {G : MvPowerSeries (Fin 2) W} (hG : MvPowerSeries.constantCoeff G = 0) :
    mk a G ∈ Ideal.span {U a, V a} := by
  have h := Ideal.mem_map_of_mem (mk a) (mem_span_X_of_constantCoeff_eq_zero hG)
  rw [Ideal.map_span, Set.image_pair] at h
  exact h

theorem apply_constantCoeff_eq_zero_of_mem_span {k : Type*} [CommRing k] (ρ : W →+* k) (π : W)
    (hρπ : ρ π = 0) (hρa : ρ a = 0)
    {Z : UVCrossingModel W a} (hZ : Z ∈ Ideal.span {const a π, U a, V a})
    (G : MvPowerSeries (Fin 2) W) (hG : mk a G = Z) : ρ (MvPowerSeries.constantCoeff G) = 0 := by

  rw [Ideal.mem_span_insert] at hZ
  obtain ⟨r, y, hy, rfl⟩ := hZ
  rw [Ideal.mem_span_pair] at hy
  obtain ⟨s, t, rfl⟩ := hy
  obtain ⟨R, rfl⟩ := mk_surjective a r
  obtain ⟨S, rfl⟩ := mk_surjective a s
  obtain ⟨T, rfl⟩ := mk_surjective a t
  have hrep : mk a G = mk a (R * MvPowerSeries.C π + (S * MvPowerSeries.X 0 + T * MvPowerSeries.X 1)) := by
    rw [hG]; simp only [map_add, map_mul]; rfl
  have hc := constantCoeff_sub_mem_span_of_mk_eq a hrep
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.mp hc
  have : MvPowerSeries.constantCoeff G = h * a + MvPowerSeries.constantCoeff (R * MvPowerSeries.C π + (S * MvPowerSeries.X 0 + T * MvPowerSeries.X 1)) := by
    rw [hh]; ring
  rw [this]
  simp [MvPowerSeries.constantCoeff_X, hρπ, hρa]

theorem isUnit_constantCoeff_of_isUnit_mk [IsLocalRing W] (ha : a ∈ IsLocalRing.maximalIdeal W)
    {G : MvPowerSeries (Fin 2) W} (hG : IsUnit (mk a G)) : IsUnit (MvPowerSeries.constantCoeff G) := by
  obtain ⟨δ, hδ⟩ := hG.exists_right_inv
  obtain ⟨D, rfl⟩ := mk_surjective a δ
  have h1 : mk a (G * D) = mk a 1 := by rw [map_mul, hδ, map_one]
  have hc := constantCoeff_sub_mem_span_of_mk_eq a h1
  rw [map_mul, map_one] at hc
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hc

  have hu : IsUnit (MvPowerSeries.constantCoeff G * MvPowerSeries.constantCoeff D) := by
    rw [show MvPowerSeries.constantCoeff G * MvPowerSeries.constantCoeff D = 1 + t * a by rw [ht]; ring]
    have hmem : t * a ∈ IsLocalRing.maximalIdeal W := Ideal.mul_mem_left _ _ ha
    by_contra hnu
    have : (1 : W) ∈ IsLocalRing.maximalIdeal W := by
      have h2 : 1 + t * a ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      simpa using (IsLocalRing.maximalIdeal W).sub_mem h2 hmem
    exact (IsLocalRing.maximalIdeal.isMaximal W).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)
  exact isUnit_of_mul_isUnit_left hu

theorem exists_const_sub_mul_pow_mem [IsLocalRing W] (π : W) (ha : a ∈ IsLocalRing.maximalIdeal W)
    (γ β : UVCrossingModel W a) (hγ : IsUnit γ) (hβ : IsUnit β) (n : ℕ) (F : UVCrossingModel W a)
    (hF : F - γ * V a ^ n ∈ Ideal.span {const a π, U a})
    (Gγ Gβ : MvPowerSeries (Fin 2) W) (hGγ : mk a Gγ = γ) (hGβ : mk a Gβ = β) :
    ∃ c : W, (MvPowerSeries.constantCoeff Gβ) ^ n * c = MvPowerSeries.constantCoeff Gγ ∧
      const a c * β ^ n - γ ∈ Ideal.span {const a π, U a, V a} ∧
      F - const a c * (V a * β) ^ n ∈ Ideal.span {const a π, U a, V a ^ (n + 1)} := by
  have hβ0 : IsUnit (MvPowerSeries.constantCoeff Gβ) := isUnit_constantCoeff_of_isUnit_mk a ha (hGβ ▸ hβ)
  obtain ⟨u, hu⟩ := hβ0
  set c : W := ((u⁻¹ : Wˣ) : W) ^ n * MvPowerSeries.constantCoeff Gγ with hc
  have hB : const a c * β ^ n - γ ∈ Ideal.span {const a π, U a, V a} := by
    have hrep : const a c * β ^ n - γ = mk a (MvPowerSeries.C c * Gβ ^ n - Gγ) := by
      rw [map_sub, map_mul, map_pow, hGγ, hGβ]; rfl
    rw [hrep]
    have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.C c * Gβ ^ n - Gγ) = 0 := by
      rw [map_sub, map_mul, map_pow, MvPowerSeries.constantCoeff_C, ← hu, hc]
      rw [mul_assoc, mul_comm (MvPowerSeries.constantCoeff Gγ), ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul,
        sub_self]
    have hUV := mk_mem_span_U_V_of_constantCoeff_eq_zero a h0
    exact Ideal.span_mono (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto) hUV
  refine ⟨c, ?_, hB, ?_⟩
  · rw [hc, ← hu, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]
  ·
    have hsplit : F - const a c * (V a * β) ^ n = (F - γ * V a ^ n) - (const a c * β ^ n - γ) * V a ^ n := by ring
    rw [hsplit]
    refine Ideal.sub_mem _ ?_ ?_
    · exact Ideal.span_mono (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto) hF
    · rw [Ideal.mem_span_insert] at hB
      obtain ⟨r, y, hy, hxy⟩ := hB
      rw [Ideal.mem_span_pair] at hy
      obtain ⟨s, t, rfl⟩ := hy
      rw [hxy]
      refine Ideal.mem_span_insert.mpr ⟨r * V a ^ n, _, Ideal.mem_span_pair.mpr ⟨s * V a ^ n, t, rfl⟩, by ring⟩

end ModularCurve.UVCrossingModel.Model

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence ssPlaces modularFunctionFieldFullC NodeLocalized.coeffSubring NodeLocalized.redRestrict uvCrossingIdeal UVCrossingModel UVCrossingModel.mk UVCrossingModel.U UVCrossingModel.V UVCrossingModel.const"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "mk U V const mk_surjective S D"
namespace Model
p2m_open "ModularCurve.UVCrossingModel ModularCurve"

section Closed

variable {B : Type u} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]

theorem mem_sup_pow_of_algebraMap_mem_map (I : Ideal B) (g : B) (m : ℕ)
    (hg : algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) g ∈
      I.map (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B))) :
    g ∈ I ⊔ IsLocalRing.maximalIdeal B ^ m := by
  set 𝔪 := IsLocalRing.maximalIdeal B
  have h1 := Ideal.mem_map_of_mem ((AdicCompletion.evalₐ 𝔪 m).toRingHom) hg
  rw [Ideal.map_map] at h1
  have hcomp : (AdicCompletion.evalₐ 𝔪 m).toRingHom.comp (algebraMap B (AdicCompletion 𝔪 B)) =
      Ideal.Quotient.mk (𝔪 ^ m) := by
    ext x
    simp [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
  rw [hcomp] at h1
  have h2 : (AdicCompletion.evalₐ 𝔪 m).toRingHom (algebraMap B (AdicCompletion 𝔪 B) g) = Ideal.Quotient.mk (𝔪 ^ m) g := by
    rw [← hcomp]; rfl
  rw [h2, ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h1
  exact h1

theorem mem_of_forall_mem_sup_pow (I : Ideal B) (g : B) (hg : ∀ m : ℕ, g ∈ I ⊔ IsLocalRing.maximalIdeal B ^ m) : g ∈ I := by
  set 𝔪 := IsLocalRing.maximalIdeal B
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (I := 𝔪) (M := B ⧸ I) (IsLocalRing.maximalIdeal.isMaximal B).ne_top
  have hmem : (Ideal.Quotient.mk I g : B ⧸ I) ∈ (⨅ i : ℕ, 𝔪 ^ i • ⊤ : Submodule B (B ⧸ I)) := by
    rw [Submodule.mem_iInf]
    intro m
    obtain ⟨i, hi, x, hx, rfl⟩ := Submodule.mem_sup.mp (hg m)
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hi, zero_add]
    have : (Ideal.Quotient.mk I x : B ⧸ I) = x • (1 : B ⧸ I) := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [this]
    exact Submodule.smul_mem_smul hx Submodule.mem_top
  rw [hK, Submodule.mem_bot] at hmem
  exact Ideal.Quotient.eq_zero_iff_mem.mp hmem

theorem mem_of_algebraMap_mem_map_adicCompletion (I : Ideal B) (g : B)
    (hg : algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) g ∈
      I.map (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B))) : g ∈ I :=
  mem_of_forall_mem_sup_pow I g fun m => mem_sup_pow_of_algebraMap_mem_map I g m hg

theorem smul_top_le_map_restrictScalars (I : Ideal B) :
    (I • ⊤ : Submodule B (AdicCompletion (IsLocalRing.maximalIdeal B) B)) ≤
      (I.map (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B))).restrictScalars B := by
  apply Submodule.smul_le.mpr
  intro r hr y _
  change r • y ∈ I.map (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B))
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hr)

theorem exists_sub_algebraMap_mem_map_maximalIdeal (bh : AdicCompletion (IsLocalRing.maximalIdeal B) B) :
    ∃ b : B, bh - algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) b ∈
      (IsLocalRing.maximalIdeal B).map (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)) := by
  obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (IsLocalRing.maximalIdeal B) B 1 bh)
  refine ⟨b, ?_⟩
  have hker : bh - algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) b ∈
      LinearMap.ker (AdicCompletion.eval (IsLocalRing.maximalIdeal B) B 1) := by
    rw [LinearMap.mem_ker, map_sub]
    have : algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) b = AdicCompletion.of (IsLocalRing.maximalIdeal B) B b := rfl
    rw [this, AdicCompletion.eval_of, ← hb]
    exact sub_self _
  rw [← AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian (IsLocalRing.maximalIdeal B)), pow_one] at hker
  exact smul_top_le_map_restrictScalars (IsLocalRing.maximalIdeal B) hker

end Closed

section Transport

variable {W : Type u} [CommRing W] (a : W) {B : Type v} [CommRing B] (φ : B →+* UVCrossingModel W a)
  (π : W) (pϖ px py : B) (αU βV : UVCrossingModel W a) (hαU : IsUnit αU) (hβV : IsUnit βV)
  (hϖ : φ pϖ = const a π) (hx : φ px = U a * αU) (hy : φ py = V a * βV)

include hαU hβV hϖ hx hy in
theorem map_span_eq (n : ℕ) :
    (Ideal.span {pϖ, px, py ^ (n + 1)}).map φ = Ideal.span {const a π, U a, V a ^ (n + 1)} := by
  rw [Ideal.map_span]
  have himg : (φ : B → UVCrossingModel W a) '' {pϖ, px, py ^ (n + 1)} = {const a π, U a * αU, (V a * βV) ^ (n + 1)} := by
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, hϖ, hx, map_pow, hy]
  rw [himg]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact Ideal.subset_span (by simp)
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    · rw [mul_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact Ideal.subset_span (by simp)
    · have hmem : U a * αU ∈ Ideal.span {const a π, U a * αU, (V a * βV) ^ (n + 1)} := Ideal.subset_span (by simp)
      have h2 := Ideal.mul_mem_right ((hαU.unit⁻¹ : (UVCrossingModel W a)ˣ) : UVCrossingModel W a) _ hmem
      rw [mul_assoc, IsUnit.mul_val_inv, mul_one] at h2
      exact h2
    · have hmem : (V a * βV) ^ (n + 1) ∈ Ideal.span {const a π, U a * αU, (V a * βV) ^ (n + 1)} := Ideal.subset_span (by simp)
      have h2 := Ideal.mul_mem_right (((hβV.unit⁻¹ : (UVCrossingModel W a)ˣ) : UVCrossingModel W a) ^ (n + 1)) _ hmem
      rw [← mul_pow, mul_assoc, IsUnit.mul_val_inv, mul_one] at h2
      exact h2

include hαU hβV hϖ hx hy in

theorem span_le_map_span (n : ℕ) :
    Ideal.span {const a π, U a, V a ^ (n + 1)} ≤ (Ideal.span {pϖ, px, py ^ (n + 1)}).map φ :=
  (map_span_eq a φ π pϖ px py αU βV hαU hβV hϖ hx hy n).ge

include hαU hβV hϖ hx hy in

theorem map_span_pair_eq : (Ideal.span {pϖ, px}).map φ = Ideal.span {const a π, U a} := by
  rw [Ideal.map_span, Set.image_pair, hϖ, hx]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact Ideal.subset_span (by simp)
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact Ideal.subset_span (by simp)
    · have hmem : U a * αU ∈ Ideal.span {const a π, U a * αU} := Ideal.subset_span (by simp)
      have h2 := Ideal.mul_mem_right ((hαU.unit⁻¹ : (UVCrossingModel W a)ˣ) : UVCrossingModel W a) _ hmem
      rw [mul_assoc, IsUnit.mul_val_inv, mul_one] at h2
      exact h2

end Transport

end ModularCurve.UVCrossingModel.Model

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence ssPlaces modularFunctionFieldFullC NodeLocalized.coeffSubring NodeLocalized.redRestrict uvCrossingIdeal UVCrossingModel UVCrossingModel.mk UVCrossingModel.U UVCrossingModel.V UVCrossingModel.const"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "mk U V const mk_surjective S D"
namespace Model
p2m_open "ModularCurve.UVCrossingModel ModularCurve"

theorem map_span_triple_eq {W : Type u} [CommRing W] (a : W) {B : Type*} [CommRing B] (φ : B →+* UVCrossingModel W a)
    (π : W) (pϖ px py : B) (αU βV : UVCrossingModel W a) (hαU : IsUnit αU) (hβV : IsUnit βV)
    (hϖ : φ pϖ = const a π) (hx : φ px = U a * αU) (hy : φ py = V a * βV) :
    (Ideal.span {pϖ, px, py}).map φ = Ideal.span {const a π, U a, V a} := by
  have h := map_span_eq a φ π pϖ px py αU βV hαU hβV hϖ hx hy 0
  simpa only [zero_add, pow_one] using h
end ModularCurve.UVCrossingModel.Model

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.evalAt_algebraMap H1"
namespace Place
p2m_export "AlgebraicCurve.Place" "HasValue hasValue_algebraMap ext ResidueField ord toValuationSubring mk evalAt evalAt_algebraMap"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

namespace HasValue p2m_export "AlgebraicCurve.Place.HasValue" "mul ne_zero ord_eq_zero" end HasValue
namespace HasValue
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in
private theorem _root_.AlgebraicCurve.Place.HasValue.add {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

end HasValue
p2m_export "AlgebraicCurve.Place" "HasValue.add"
namespace HasValue
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in
private theorem _root_.AlgebraicCurve.Place.HasValue.congr {g g' : F} {a : K} (h : v.HasValue g a) (e : g = g') : v.HasValue g' a := e ▸ h

end HasValue
p2m_export "AlgebraicCurve.Place" "HasValue.congr"
end AlgebraicCurve.Place

namespace X6ValueAssembly

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_nodeResidueFst_div_nodeResidueFst_y_pow_of_sub_mul_V_pow_mem_of_hasValue.AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
  {B : Type*} [CommRing B] (res : B →+* F)

theorem hasValue_div_pow
    (pϖ px py po f : B) (n : ℕ) (rv : K)
    (hϖ : res pϖ = 0) (hx : res px = 0)
    (hy0 : v.HasValue (res py) 0) (hyne : res py ≠ 0)
    (hall : ∀ b : B, ∃ a : K, v.HasValue (res b) a)
    (ho : v.HasValue (res po) rv)
    (hdec : f - po * py ^ n ∈ Ideal.span {pϖ, px, py ^ (n + 1)}) :
    v.HasValue (res f / res py ^ n) rv := by
  obtain ⟨r, s, t, hrst⟩ := Submodule.mem_span_triple.mp hdec
  simp only [smul_eq_mul] at hrst

  have hf : res f = res po * res py ^ n + res py ^ (n + 1) * res t := by
    have := congrArg res hrst
    simp only [map_add, map_mul, map_sub, map_pow, hϖ, hx, mul_zero, zero_add] at this

    linear_combination -this
  have hYn : res py ^ n ≠ 0 := pow_ne_zero _ hyne
  have hq : res f / res py ^ n = res po + res py * res t := by
    rw [hf]; field_simp; ring
  obtain ⟨a, ha⟩ := hall t
  have := (ho.add v (hy0.mul ha))
  rw [zero_mul, add_zero] at this
  exact this.congr v hq.symm

end X6ValueAssembly

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.evalAt_algebraMap H1"
namespace Place
p2m_export "AlgebraicCurve.Place" "HasValue hasValue_algebraMap ext ResidueField ord toValuationSubring mk evalAt evalAt_algebraMap"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"
section E11

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace HasValue
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in

private theorem _root_.AlgebraicCurve.Place.HasValue.eq_zero_of_ord_ne_zero {v : Place K F} {g : F} {a : K}
    (h : v.HasValue g a) (hord : v.ord g ≠ 0) : a = 0 := by
  by_contra ha
  exact hord (h.ord_eq_zero ha)

end HasValue
p2m_export "AlgebraicCurve.Place" "HasValue.eq_zero_of_ord_ne_zero"
namespace HasValue
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in

private theorem _root_.AlgebraicCurve.Place.HasValue.hasValue_zero_of_ord_ne_zero {v : Place K F} {g : F} {a : K}
    (h : v.HasValue g a) (hord : v.ord g ≠ 0) : v.HasValue g 0 := by
  obtain rfl := h.eq_zero_of_ord_ne_zero hord
  exact h

end HasValue
p2m_export "AlgebraicCurve.Place" "HasValue.hasValue_zero_of_ord_ne_zero"
namespace HasValue
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in

private theorem _root_.AlgebraicCurve.Place.HasValue.hasValue_zero_of_ord_eq_one {v : Place K F} {g : F} {a : K}
    (h : v.HasValue g a) (hord : v.ord g = 1) : v.HasValue g 0 :=
  h.hasValue_zero_of_ord_ne_zero (by rw [hord]; exact one_ne_zero)

end HasValue
p2m_export "AlgebraicCurve.Place" "HasValue.hasValue_zero_of_ord_eq_one"

theorem hasValue_const (v : Place K F) (c : K) : v.HasValue (algebraMap K F c) c :=
  v.hasValue_algebraMap c

theorem evalAt_const (v : Place K F) (c : K) : v.evalAt (algebraMap K F c) = c :=
  v.evalAt_algebraMap c

end E11
end AlgebraicCurve.Place

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence ssPlaces modularFunctionFieldFullC NodeLocalized.coeffSubring NodeLocalized.redRestrict uvCrossingIdeal UVCrossingModel UVCrossingModel.mk UVCrossingModel.U UVCrossingModel.V UVCrossingModel.const"
p2m_open "ModularCurve"

theorem evalAt_algebraMap_modularFunctionFieldBar (M : ℕ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) (c : AlgebraicClosure ℚ) :
    V.evalAt (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar M) c) = c :=
  V.evalAt_algebraMap c

theorem hasValue_algebraMap_modularFunctionFieldBar (M : ℕ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) (c : AlgebraicClosure ℚ) :
    V.HasValue (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar M) c) c :=
  V.hasValue_algebraMap c

namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "coeffSubring redRestrict"
p2m_open "ModularCurve.NodeLocalized"

theorem redRestrict_apply {k : Type*} [Field k] {A : ValuationSubring (AlgebraicClosure ℚ)} (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (o : coeffSubring A K) :
    redRestrict red K o = red ⟨(o : AlgebraicClosure ℚ), o.2.1⟩ := rfl

theorem redRestrict_apply' {k : Type*} [Field k] {A : ValuationSubring (AlgebraicClosure ℚ)} (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (o : coeffSubring A K) (ho : (o : AlgebraicClosure ℚ) ∈ A) :
    redRestrict red K o = red ⟨(o : AlgebraicClosure ℚ), ho⟩ := rfl

end NodeLocalized
end ModularCurve

noncomputable scoped instance (priority := high) AnnulusLocBranch.instAlgebraResidueFieldFullC
    {L : Type*} [Field L] (A : ValuationSubring L) (N : ℕ) :
    Algebra (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N) :=
  SubalgebraClass.toAlgebra (modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N)

namespace AnnulusLocBranch

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

noncomputable def res₁ (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) :
    ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k N) :=
  (R.nodeResidue₁ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w))

theorem res₁_apply (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (b : ↥(R.nodeIntegersOver K w)) :
    res₁ R K w b = R.nodeResidue₁ w ⟨b, b.2.1⟩ := rfl

def toR₁ (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) : ↥(R.nodeIntegersOver K w) →+* ↥R.R₁.integers where
  toFun v := ⟨v, v.2.1.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem res₁_eq (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (v : ↥(R.nodeIntegersOver K w)) :
    res₁ R K w v = R.ι (R.R₁.residue (toR₁ R K w v)) := rfl

theorem coe_toR₁ (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (v : ↥(R.nodeIntegersOver K w)) :
    ((toR₁ R K w v : ↥R.R₁.integers) : ↥(modularFunctionFieldBar (N * q))) = v := rfl

theorem not_isUnit_toR₁_nodeConst (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : NodeLocalized.redRestrict red K ϖ = 0) :
    ¬ IsUnit (toR₁ R K w (R.nodeConst K w ϖ)) := by
  set a : A := ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ with ha
  have hred : red a = 0 := hϖ
  have hanu : ¬ IsUnit a := fun hu => by
    have := hu.map red
    rw [hred] at this
    exact not_isUnit_zero this
  have hfval : ((toR₁ R K w (R.nodeConst K w ϖ) : ↥R.R₁.integers) : ↥(modularFunctionFieldBar (N * q))) =
      algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) := rfl
  intro hu
  obtain ⟨g, hg⟩ := hu.exists_right_inv
  have hg' : ((toR₁ R K w (R.nodeConst K w ϖ) : ↥R.R₁.integers) : ↥(modularFunctionFieldBar (N * q))) *
      (g : ↥(modularFunctionFieldBar (N * q))) = 1 := by
    rw [← MulMemClass.coe_mul, hg]; rfl
  have ha0 : (a : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    rw [hfval, h0, map_zero, zero_mul] at hg'
    exact zero_ne_one hg'
  have hginv : (g : ↥(modularFunctionFieldBar (N * q))) =
      algebraMap (AlgebraicClosure ℚ) _ ((a : AlgebraicClosure ℚ)⁻¹) := by
    rw [map_inv₀, ← hfval]
    exact (eq_inv_of_mul_eq_one_right hg')
  have hmemA : (a : AlgebraicClosure ℚ)⁻¹ ∈ A := by
    have := g.2
    rw [hginv] at this
    exact (R.R₁.algebraMap_mem_iff _).mp this
  exact hanu (isUnit_iff_exists_inv.mpr ⟨⟨(a : AlgebraicClosure ℚ)⁻¹, hmemA⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩)

theorem res₁_nodeConst_eq_zero (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : NodeLocalized.redRestrict red K ϖ = 0) :
    res₁ R K w (R.nodeConst K w ϖ) = 0 := by
  rw [res₁_apply, nodeResidue₁_apply, residue₁_apply]
  set a : A := ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ with ha
  have hred : red a = 0 := hϖ
  have hanu : ¬ IsUnit a := fun hu => by
    have := hu.map red
    rw [hred] at this
    exact not_isUnit_zero this
  set f : ↥R.R₁.integers := ⟨((R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))),
      (R.nodeConst K w ϖ).2.1.1⟩ with hf
  have hfval : (f : ↥(modularFunctionFieldBar (N * q))) =
      algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) := rfl
  have hfnu : ¬ IsUnit f := by
    intro hu
    obtain ⟨g, hg⟩ := hu.exists_right_inv
    have hg' : (f : ↥(modularFunctionFieldBar (N * q))) * (g : ↥(modularFunctionFieldBar (N * q))) = 1 := by
      rw [← MulMemClass.coe_mul, hg]; rfl
    have ha0 : (a : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      rw [hfval, h0, map_zero, zero_mul] at hg'
      exact zero_ne_one hg'
    have hginv : (g : ↥(modularFunctionFieldBar (N * q))) =
        algebraMap (AlgebraicClosure ℚ) _ ((a : AlgebraicClosure ℚ)⁻¹) := by
      rw [map_inv₀, ← hfval]
      exact (eq_inv_of_mul_eq_one_right hg')
    have hmemA : (a : AlgebraicClosure ℚ)⁻¹ ∈ A := by
      have := g.2
      rw [hginv] at this
      exact (R.R₁.algebraMap_mem_iff _).mp this
    apply hanu
    exact isUnit_iff_exists_inv.mpr ⟨⟨(a : AlgebraicClosure ℚ)⁻¹, hmemA⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩
  have hmem : f ∈ maximalIdeal ↥R.R₁.integers := (mem_maximalIdeal _).mpr hfnu
  rw [← R.R₁.ker_residue, RingHom.mem_ker] at hmem
  show R.ι (R.R₁.residue f) = 0
  rw [hmem, map_zero]

end AnnulusLocBranch

set_option maxHeartbeats 6400000 in
open Classical in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hmax : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (hVI : R.ValueIntegralityLaw w) [DecidableEq k] (hwss : w ∈ ssPlaces q N k)
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))

    (wmap : ↥(NodeLocalized.coeffSubring A K) →+* W) (hwϖ : wmap ϖ = π)
    (hιw : ∀ o : ↥(NodeLocalized.coeffSubring A K), ι (algebraMap _ _ (R.nodeConst K w o)) = UVCrossingModel.const (π ^ E) (wmap o))
    (ρ : W →+* k) (hρ : ∀ o : ↥(NodeLocalized.coeffSubring A K), ρ (wmap o) = NodeLocalized.redRestrict red K o)

    (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV₀ : P.reduceFst V₀ = w)
    (hVAL : ∀ (g : ↥(R.nodeIntegersOver K w)) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
      (hV : P.reduceFst V = w),
      w.HasValue (R.nodeResidue₁ w ⟨(g : ↥(modularFunctionFieldBar (N * q))), g.2.1⟩ : ↥(modularFunctionFieldC k N))
        (red ⟨V.evalAt (g : ↥(modularFunctionFieldBar (N * q))),
          hVI (g : ↥(modularFunctionFieldBar (N * q))) (R.nodeIntegersOver_le K w g.2) V hV⟩))

    (βV : UVCrossingModel W (π ^ E)) (hβV : IsUnit βV) (hιy : ι (algebraMap _ _ c.y) = UVCrossingModel.V (π ^ E) * βV)
    (αU : UVCrossingModel W (π ^ E)) (hαU : IsUnit αU) (hιx : ι (algebraMap _ _ c.x) = UVCrossingModel.U (π ^ E) * αU)
    (Gβ : MvPowerSeries (Fin 2) W) (hGβ : UVCrossingModel.mk (π ^ E) Gβ = βV)

    (f : ↥(R.nodeIntegersOver K w)) (n : ℕ)
    (hf : R.nodeResidue₁ w ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1⟩ ≠ 0)
    (hn : w.ord (R.nodeResidue₁ w ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1⟩) = (n : ℤ))
    (γ : UVCrossingModel W (π ^ E)) (hγ : IsUnit γ)
    (hfγ : ι (algebraMap _ _ f) - γ * UVCrossingModel.V (π ^ E) ^ n ∈ Ideal.span {UVCrossingModel.const (π ^ E) π, UVCrossingModel.U (π ^ E)})
    (Gγ : MvPowerSeries (Fin 2) W) (hGγ : UVCrossingModel.mk (π ^ E) Gγ = γ) :
    w.HasValue
      ((R.nodeResidue₁ w ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1⟩ : ↥(modularFunctionFieldC k N)) /
        (R.nodeResidue₁ w ⟨(c.y : ↥(modularFunctionFieldBar (N * q))), c.y.2.1⟩ : ↥(modularFunctionFieldC k N)) ^ n)
      (ρ (MvPowerSeries.constantCoeff Gγ) * (ρ (MvPowerSeries.constantCoeff Gβ))⁻¹ ^ n) := by

  have hE0 : E ≠ 0 := by omega
  have hϖred : NodeLocalized.redRestrict red K ϖ = 0 := (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩
  have hρπ : ρ π = 0 := by rw [← hwϖ, hρ]; exact hϖred
  have hρa : ρ (π ^ E) = 0 := by rw [map_pow, hρπ, zero_pow hE0]
  have hπmax : π ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit
  have ha : π ^ E ∈ IsLocalRing.maximalIdeal W := Ideal.pow_mem_of_mem _ hπmax E (by omega)

  obtain ⟨cW, hc1, hc2, hc3⟩ := UVCrossingModel.Model.exists_const_sub_mul_pow_mem (π ^ E) π ha γ βV hγ hβV n
    (ι (algebraMap _ _ f)) hfγ Gγ Gβ hGγ hGβ

  obtain ⟨b, hb⟩ := UVCrossingModel.Model.exists_sub_algebraMap_mem_map_maximalIdeal (B := ↥(R.nodeIntegersOver K w)) (ι.symm (UVCrossingModel.const (π ^ E) cW))
  obtain ⟨o, ho⟩ := hres b
  have hbo : b - R.nodeConst K w o ∈ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) := (IsLocalRing.mem_maximalIdeal _).mpr ho

  set φ : ↥(R.nodeIntegersOver K w) →+* UVCrossingModel W (π ^ E) := ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w) (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))) with hφ
  have hφapp : ∀ g : ↥(R.nodeIntegersOver K w), φ g = ι (algebraMap _ _ g) := fun g => rfl
  have hφϖ : φ (R.nodeConst K w ϖ) = UVCrossingModel.const (π ^ E) π := by rw [hφapp, hιw, hwϖ]
  have hφx : φ c.x = UVCrossingModel.U (π ^ E) * αU := by rw [hφapp, hιx]
  have hφy : φ c.y = UVCrossingModel.V (π ^ E) * βV := by rw [hφapp, hιy]
  have hmaxφ : (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)).map φ =
      Ideal.span {UVCrossingModel.const (π ^ E) π, UVCrossingModel.U (π ^ E), UVCrossingModel.V (π ^ E)} := by
    rw [hmax]
    exact UVCrossingModel.Model.map_span_triple_eq (π ^ E) φ π _ _ _ αU βV hαU hβV hφϖ hφx hφy

  have hdiff : UVCrossingModel.const (π ^ E) cW - UVCrossingModel.const (π ^ E) (wmap o) ∈
      Ideal.span {UVCrossingModel.const (π ^ E) π, UVCrossingModel.U (π ^ E), UVCrossingModel.V (π ^ E)} := by
    have h1 : ι.symm (UVCrossingModel.const (π ^ E) cW) - algebraMap _ _ (R.nodeConst K w o) ∈
        (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)).map (algebraMap ↥(R.nodeIntegersOver K w) (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))) := by
      have : ι.symm (UVCrossingModel.const (π ^ E) cW) - algebraMap _ _ (R.nodeConst K w o) =
          (ι.symm (UVCrossingModel.const (π ^ E) cW) - algebraMap _ _ b) + algebraMap _ _ (b - R.nodeConst K w o) := by
        rw [map_sub]; ring
      rw [this]
      exact Ideal.add_mem _ hb (Ideal.mem_map_of_mem _ hbo)
    have h2 := Ideal.mem_map_of_mem ι.toRingHom h1
    rw [Ideal.map_map, ← hφ, hmaxφ] at h2
    have h3 : ι.toRingHom (ι.symm (UVCrossingModel.const (π ^ E) cW) - algebraMap _ _ (R.nodeConst K w o)) =
        UVCrossingModel.const (π ^ E) cW - UVCrossingModel.const (π ^ E) (wmap o) := by
      rw [map_sub]
      show ι (ι.symm _) - ι (algebraMap _ _ (R.nodeConst K w o)) = _
      rw [RingEquiv.apply_symm_apply, hιw]
    rwa [h3] at h2

  have hρc : ρ cW = NodeLocalized.redRestrict red K o := by
    have hz := UVCrossingModel.Model.apply_constantCoeff_eq_zero_of_mem_span (π ^ E) ρ π hρπ hρa hdiff
      (MvPowerSeries.C (cW - wmap o)) (by
        rw [map_sub]
        show UVCrossingModel.mk (π ^ E) (MvPowerSeries.C cW) - UVCrossingModel.mk (π ^ E) (MvPowerSeries.C (wmap o)) = _
        rfl)
    rw [MvPowerSeries.constantCoeff_C, map_sub, sub_eq_zero] at hz
    rw [hz, hρ]

  have hmodel : φ (f - R.nodeConst K w o * c.y ^ n) ∈
      Ideal.span {UVCrossingModel.const (π ^ E) π, UVCrossingModel.U (π ^ E), UVCrossingModel.V (π ^ E) ^ (n + 1)} := by
    have hsplit : φ (f - R.nodeConst K w o * c.y ^ n) =
        (ι (algebraMap _ _ f) - UVCrossingModel.const (π ^ E) cW * (UVCrossingModel.V (π ^ E) * βV) ^ n) +
        (UVCrossingModel.const (π ^ E) cW - UVCrossingModel.const (π ^ E) (wmap o)) * (UVCrossingModel.V (π ^ E) * βV) ^ n := by
      rw [map_sub, map_mul, map_pow, hφy, hφapp f, hφapp, hιw]; ring
    rw [hsplit]
    refine Ideal.add_mem _ hc3 ?_
    rw [Ideal.mem_span_insert] at hdiff
    obtain ⟨r, yy, hyy, hxy⟩ := hdiff
    rw [Ideal.mem_span_pair] at hyy
    obtain ⟨s, t, rfl⟩ := hyy
    rw [hxy, mul_pow]
    refine Ideal.mem_span_insert.mpr ⟨r * (UVCrossingModel.V (π ^ E) ^ n * βV ^ n), _,
      Ideal.mem_span_pair.mpr ⟨s * (UVCrossingModel.V (π ^ E) ^ n * βV ^ n), t * βV ^ n, rfl⟩, by ring⟩

  have hdec : f - R.nodeConst K w o * c.y ^ n ∈ Ideal.span {R.nodeConst K w ϖ, c.x, c.y ^ (n + 1)} := by
    have hle := UVCrossingModel.Model.span_le_map_span (π ^ E) φ π (R.nodeConst K w ϖ) c.x c.y αU βV hαU hβV hφϖ hφx hφy n
    have h1 := hle hmodel
    rw [hφ, ← Ideal.map_map] at h1
    obtain ⟨z, hz, hzeq⟩ := (Ideal.mem_map_iff_of_surjective ι.toRingHom ι.surjective).mp h1
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom] at hzeq
    have hz' : z = algebraMap _ _ (f - R.nodeConst K w o * c.y ^ n) := ι.injective hzeq
    rw [hz'] at hz
    exact UVCrossingModel.Model.mem_of_algebraMap_mem_map_adicCompletion _ _ hz

  have hVAL' : ∀ g : ↥(R.nodeIntegersOver K w), w.HasValue (AnnulusLocBranch.res₁ R K w g)
      (red ⟨V₀.evalAt (g : ↥(modularFunctionFieldBar (N * q))),
        hVI (g : ↥(modularFunctionFieldBar (N * q))) (R.nodeIntegersOver_le K w g.2) V₀ hV₀⟩) :=
    fun g => hVAL g V₀ hV₀
  have hyord : w.ord (AnnulusLocBranch.res₁ R K w c.y) = 1 := c.y_fst
  have hy0 : w.HasValue (AnnulusLocBranch.res₁ R K w c.y) 0 := (hVAL' c.y).hasValue_zero_of_ord_eq_one hyord
  have hx0 : AnnulusLocBranch.res₁ R K w c.x = 0 := c.x_fst
  have hyne : AnnulusLocBranch.res₁ R K w c.y ≠ 0 := c.nodeResidue₁_y_ne_zero
  have hov : w.HasValue (AnnulusLocBranch.res₁ R K w (R.nodeConst K w o)) (NodeLocalized.redRestrict red K o) := by
    have h := hVAL' (R.nodeConst K w o)
    have he : (⟨V₀.evalAt ((R.nodeConst K w o : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))),
        hVI _ (R.nodeIntegersOver_le K w (R.nodeConst K w o).2) V₀ hV₀⟩ : A) = ⟨(o : AlgebraicClosure ℚ), o.2.1⟩ :=
      Subtype.ext (V₀.evalAt_algebraMap (o : AlgebraicClosure ℚ))
    have hv : red ⟨V₀.evalAt ((R.nodeConst K w o : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))),
        hVI _ (R.nodeIntegersOver_le K w (R.nodeConst K w o).2) V₀ hV₀⟩ = NodeLocalized.redRestrict red K o := by
      rw [he]; rfl
    exact hv ▸ h
  have hval := X6ValueAssembly.hasValue_div_pow w (AnnulusLocBranch.res₁ R K w) (R.nodeConst K w ϖ) c.x c.y (R.nodeConst K w o) f n
    (NodeLocalized.redRestrict red K o) (AnnulusLocBranch.res₁_nodeConst_eq_zero R K w ϖ hϖred) hx0 hy0
    hyne (fun bb => ⟨_, hVAL' bb⟩) hov hdec

  have hβ0u : IsUnit (MvPowerSeries.constantCoeff Gβ) :=
    UVCrossingModel.Model.isUnit_constantCoeff_of_isUnit_mk (π ^ E) ha (hGβ ▸ hβV)
  have hρβ : ρ (MvPowerSeries.constantCoeff Gβ) ≠ 0 := (hβ0u.map ρ).ne_zero
  have hvalue : NodeLocalized.redRestrict red K o =
      ρ (MvPowerSeries.constantCoeff Gγ) * (ρ (MvPowerSeries.constantCoeff Gβ))⁻¹ ^ n := by
    rw [← hρc]
    have h := congrArg ρ hc1
    rw [map_mul, map_pow] at h
    rw [← h, inv_pow]
    field_simp

  have hfin : w.HasValue (AnnulusLocBranch.res₁ R K w f / AnnulusLocBranch.res₁ R K w c.y ^ n)
      (ρ (MvPowerSeries.constantCoeff Gγ) * (ρ (MvPowerSeries.constantCoeff Gβ))⁻¹ ^ n) := hvalue ▸ hval
  simpa only [AnnulusLocBranch.res₁_apply] using hfin

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_nodeResidueFst_div_nodeResidueFst_y_pow_of_sub_mul_V_pow_mem_of_hasValue
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_nodeResidueFst_div_nodeResidueFst_y_pow_of_sub_mul_V_pow_mem_of_hasValue (solution)
