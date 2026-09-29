-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.mem_iff_ringEquiv_adicCompletion_mem_span_or_swap_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/1668822b-4011-50ed-a3fa-f58e46b107bd

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_mem_iff_ringEquiv_adicCompletion_mem_span_or_swap_of_ne

set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

namespace L1BUV

section General

variable {W k : Type} [CommRing W] [CommRing k] (ρ : W →+* k)

noncomputable def brHom : MvPowerSeries (Fin 2) W →+* PowerSeries k where
  toFun f := PowerSeries.mk fun n => ρ (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n) f)
  map_one' := by
    classical
    ext n
    rw [PowerSeries.coeff_mk, MvPowerSeries.coeff_one, PowerSeries.coeff_one]
    by_cases hn : n = 0
    · subst hn; simp
    · rw [if_neg (by rwa [Finsupp.single_eq_zero]), if_neg hn, map_zero]
  map_mul' f g := by
    classical
    ext n
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single,
      Finset.sum_map, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd,
      PowerSeries.coeff_mk, map_mul]
  map_zero' := by ext n; simp
  map_add' f g := by ext n; simp

theorem coeff_brHom (f : MvPowerSeries (Fin 2) W) (n : ℕ) :
    PowerSeries.coeff n (brHom ρ f) = ρ (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n) f) := by
  show PowerSeries.coeff n (PowerSeries.mk fun n => ρ (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n) f)) = _
  rw [PowerSeries.coeff_mk]

theorem brHom_X_zero : brHom ρ (MvPowerSeries.X 0) = 0 := by
  classical
  ext n
  rw [coeff_brHom, MvPowerSeries.coeff_X, map_zero]
  rw [if_neg, map_zero]
  intro h
  have := congrArg (fun m : Fin 2 →₀ ℕ => m 0) h
  simp at this

theorem brHom_X_one : brHom ρ (MvPowerSeries.X 1) = PowerSeries.X := by
  classical
  ext n
  rw [coeff_brHom, MvPowerSeries.coeff_X, PowerSeries.coeff_X]
  by_cases hn : n = 1
  · subst hn; simp
  · rw [if_neg, if_neg hn, map_zero]
    intro h
    have := congrArg (fun m : Fin 2 →₀ ℕ => m 1) h
    simp [hn] at this

theorem brHom_C (a : W) : brHom ρ (MvPowerSeries.C a) = PowerSeries.C (ρ a) := by
  classical
  ext n
  rw [coeff_brHom, MvPowerSeries.coeff_C, PowerSeries.coeff_C]
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg (by rwa [Finsupp.single_eq_zero]), if_neg hn, map_zero]

theorem brHom_surjective (hρ : Function.Surjective ρ) : Function.Surjective (brHom ρ) := by
  classical
  intro g
  choose lift hlift using hρ
  refine ⟨fun m => if m 0 = 0 then lift (PowerSeries.coeff (m 1) g) else 0, ?_⟩
  ext n
  rw [coeff_brHom]
  show ρ (if (Finsupp.single (1 : Fin 2) n) 0 = 0 then lift (PowerSeries.coeff ((Finsupp.single (1 : Fin 2) n) 1) g) else 0) = _
  simp [hlift]

theorem mem_ker_brHom_iff (f : MvPowerSeries (Fin 2) W) :
    brHom ρ f = 0 ↔ ∀ n : ℕ, ρ (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n) f) = 0 := by
  constructor
  · intro h n; have := congrArg (PowerSeries.coeff n) h; rwa [coeff_brHom, map_zero] at this
  · intro h; ext n; rw [coeff_brHom, h, map_zero]

theorem ker_brHom_eq_span (π : W) (hker : ∀ a : W, ρ a = 0 ↔ π ∣ a) :
    RingHom.ker (brHom ρ) = Ideal.span {MvPowerSeries.C π, MvPowerSeries.X 0} := by
  classical
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker, mem_ker_brHom_iff] at hf

    let h : MvPowerSeries (Fin 2) W := fun m => if m 0 = 0 then MvPowerSeries.coeff m f else 0
    have hdiv : MvPowerSeries.X (0 : Fin 2) ∣ f - h := by
      rw [MvPowerSeries.X_dvd_iff]
      intro m hm
      rw [map_sub]
      show MvPowerSeries.coeff m f - (if m 0 = 0 then MvPowerSeries.coeff m f else 0) = 0
      rw [if_pos hm, sub_self]

    have hcoef : ∀ m : Fin 2 →₀ ℕ, π ∣ MvPowerSeries.coeff m h := by
      intro m
      show π ∣ (if m 0 = 0 then MvPowerSeries.coeff m f else 0)
      split_ifs with hm
      ·
        have : m = Finsupp.single (1 : Fin 2) (m 1) := by
          ext i; fin_cases i <;> simp [hm]
        rw [this]; exact (hker _).mp (hf (m 1))
      · exact dvd_zero π
    choose c hc using hcoef
    let h' : MvPowerSeries (Fin 2) W := fun m => c m
    have hh : h = MvPowerSeries.C π * h' := by
      ext m
      rw [MvPowerSeries.coeff_C_mul]
      exact hc m
    obtain ⟨g, hg⟩ := hdiv
    have : f = MvPowerSeries.X 0 * g + MvPowerSeries.C π * h' := by
      rw [← hh, ← hg]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
  · rw [Ideal.span_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [SetLike.mem_coe, RingHom.mem_ker, brHom_C, (hker π).mpr (dvd_refl π), map_zero]
    · rw [SetLike.mem_coe, RingHom.mem_ker, brHom_X_zero]

theorem exists_ringHom_killU (W : Type) [CommRing W] :
    ∃ Ψ : MvPowerSeries (Fin 2) W →+* PowerSeries W,
      Ψ (MvPowerSeries.X 0) = 0 ∧ Ψ (MvPowerSeries.X 1) = PowerSeries.X ∧
      (∀ a : W, Ψ (MvPowerSeries.C a) = PowerSeries.C a) ∧
      (∀ F : MvPowerSeries (Fin 2) W, Ψ F = 0 ↔ MvPowerSeries.X (0 : Fin 2) ∣ F) ∧
      Function.Surjective Ψ := by
  classical
  refine ⟨brHom (RingHom.id W), brHom_X_zero _, brHom_X_one _, fun a => brHom_C _ a, fun F => ?_,
    brHom_surjective _ Function.surjective_id⟩
  rw [mem_ker_brHom_iff, MvPowerSeries.X_dvd_iff]
  constructor
  · intro h m hm
    have : m = Finsupp.single (1 : Fin 2) (m 1) := by
      ext i; fin_cases i <;> simp [hm]
    rw [this]; exact h (m 1)
  · intro h n
    exact h _ (by simp)

end General

section Crossing

variable {W : Type} [CommRing W] [IsLocalRing W] (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (w : ℕ) (hw : 1 ≤ w)

noncomputable def brQuot : UVCrossingModel W (π ^ w) →+* PowerSeries (ResidueField W) :=
  Ideal.Quotient.lift (uvCrossingIdeal W (π ^ w)) (brHom (IsLocalRing.residue W)) (by
    intro f hf
    rw [Ideal.mem_span_singleton] at hf
    obtain ⟨g, rfl⟩ := hf
    rw [map_mul, map_sub, map_mul, brHom_X_zero, zero_mul, brHom_C, map_pow,
      (IsLocalRing.residue_eq_zero_iff π).mpr (by rw [hπ]; exact Ideal.mem_span_singleton_self π),
      zero_pow (by omega), map_zero, sub_zero, zero_mul])

include hπ hw in
theorem brQuot_mk (f : MvPowerSeries (Fin 2) W) :
    brQuot π hπ w hw (UVCrossingModel.mk (π ^ w) f) = brHom (IsLocalRing.residue W) f := rfl

include hπ hw in
theorem brQuot_U : brQuot π hπ w hw (U (π ^ w)) = 0 := by
  show brQuot π hπ w hw (UVCrossingModel.mk (π ^ w) (MvPowerSeries.X 0)) = 0
  rw [brQuot_mk, brHom_X_zero]

include hπ hw in
theorem brQuot_V : brQuot π hπ w hw (V (π ^ w)) = PowerSeries.X := by
  show brQuot π hπ w hw (UVCrossingModel.mk (π ^ w) (MvPowerSeries.X 1)) = _
  rw [brQuot_mk, brHom_X_one]

include hπ hw in
theorem brQuot_const (a : W) : brQuot π hπ w hw (const (π ^ w) a) = PowerSeries.C (IsLocalRing.residue W a) := by
  show brQuot π hπ w hw (UVCrossingModel.mk (π ^ w) (MvPowerSeries.C a)) = _
  rw [brQuot_mk, brHom_C]

include hπ hw in
theorem brQuot_surjective : Function.Surjective (brQuot π hπ w hw) := by
  intro g
  obtain ⟨f, hf⟩ := brHom_surjective (IsLocalRing.residue W) Ideal.Quotient.mk_surjective g
  exact ⟨UVCrossingModel.mk (π ^ w) f, by rw [brQuot_mk, hf]⟩

include hπ hw in

theorem ker_brQuot : RingHom.ker (brQuot π hπ w hw) = Ideal.span {const (π ^ w) π, U (π ^ w)} := by
  classical
  have hker : ∀ a : W, IsLocalRing.residue W a = 0 ↔ π ∣ a := fun a => by
    rw [IsLocalRing.residue_eq_zero_iff, hπ, Ideal.mem_span_singleton]
  have h1 : RingHom.ker (brQuot π hπ w hw) = (RingHom.ker (brHom (IsLocalRing.residue W))).map (UVCrossingModel.mk (π ^ w)) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨f, rfl⟩ := UVCrossingModel.mk_surjective (π ^ w) x
      exact Ideal.mem_map_of_mem _ (by rw [RingHom.mem_ker, ← brQuot_mk π hπ w hw]; exact hx)
    · rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap, RingHom.mem_ker, brQuot_mk]
      exact hf
  rw [h1, ker_brHom_eq_span _ π hker, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  rfl

include hπ hw in

theorem isPrime_span_const_U : (Ideal.span {const (π ^ w) π, U (π ^ w)} : Ideal (UVCrossingModel W (π ^ w))).IsPrime := by
  rw [← ker_brQuot π hπ w hw]
  exact RingHom.ker_isPrime _

include hπ hw in

theorem isMaximal_span_const_U_V :
    (Ideal.span {const (π ^ w) π, U (π ^ w), V (π ^ w)} : Ideal (UVCrossingModel W (π ^ w))).IsMaximal := by
  classical
  let χ : UVCrossingModel W (π ^ w) →+* ResidueField W := (PowerSeries.constantCoeff).comp (brQuot π hπ w hw)
  have hχs : Function.Surjective χ := by
    intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨const (π ^ w) a, by show PowerSeries.constantCoeff (brQuot π hπ w hw (const (π ^ w) a)) = _; rw [brQuot_const, PowerSeries.constantCoeff_C]; rfl⟩
  have hχker : RingHom.ker χ = Ideal.span {const (π ^ w) π, U (π ^ w), V (π ^ w)} := by
    apply le_antisymm
    · intro x hx
      rw [RingHom.mem_ker] at hx

      have hx' : PowerSeries.constantCoeff (brQuot π hπ w hw x) = 0 := hx
      obtain ⟨g, hg⟩ : PowerSeries.X ∣ brQuot π hπ w hw x := by
        rw [PowerSeries.X_dvd_iff]; exact hx'
      obtain ⟨y, hy⟩ := brQuot_surjective π hπ w hw g
      have : x - V (π ^ w) * y ∈ RingHom.ker (brQuot π hπ w hw) := by
        rw [RingHom.mem_ker, map_sub, map_mul, brQuot_V, hy, hg, sub_self]
      rw [ker_brQuot] at this
      have hsplit : x = (x - V (π ^ w) * y) + V (π ^ w) * y := by ring
      rw [hsplit]
      refine Ideal.add_mem _ (Ideal.span_mono ?_ this) (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto
    · rw [Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rw [SetLike.mem_coe, RingHom.mem_ker]
      show PowerSeries.constantCoeff (brQuot π hπ w hw z) = 0
      rcases hz with rfl | rfl | rfl
      · rw [brQuot_const, PowerSeries.constantCoeff_C, (IsLocalRing.residue_eq_zero_iff π).mpr (by rw [hπ]; exact Ideal.mem_span_singleton_self π)]
      · rw [brQuot_U, map_zero]
      · rw [brQuot_V, PowerSeries.constantCoeff_X]
  rw [← hχker]
  exact RingHom.ker_isMaximal_of_surjective χ hχs

include hπ hw in

theorem eq_span_triple_of_lt {𝔓 : Ideal (UVCrossingModel W (π ^ w))} [𝔓.IsPrime]
    (hle : Ideal.span {const (π ^ w) π, U (π ^ w)} ≤ 𝔓) (hne : Ideal.span {const (π ^ w) π, U (π ^ w)} ≠ 𝔓) :
    𝔓 = Ideal.span {const (π ^ w) π, U (π ^ w), V (π ^ w)} := by
  classical

  obtain ⟨f, hf𝔓, hfU⟩ : ∃ f ∈ 𝔓, f ∉ Ideal.span {const (π ^ w) π, U (π ^ w)} := by
    by_contra h; push Not at h
    exact hne (le_antisymm hle fun f hf => h f hf)
  have hf0 : brQuot π hπ w hw f ≠ 0 := by rwa [← ker_brQuot π hπ w hw] at hfU
  have hV : V (π ^ w) ∈ 𝔓 := by

    obtain ⟨n, u, hu⟩ : ∃ (n : ℕ) (u : (PowerSeries (ResidueField W))ˣ),
        brQuot π hπ w hw f = PowerSeries.X ^ n * (u : PowerSeries (ResidueField W)) := by
      haveI : IsDiscreteValuationRing (PowerSeries (ResidueField W)) := inferInstance
      obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hf0 PowerSeries.X_irreducible
      refine ⟨n, u, ?_⟩
      rw [h]; exact mul_comm _ _
    have hn : n ≠ 0 := by
      rintro rfl
      simp only [pow_zero, one_mul] at hu

      obtain ⟨g, hg⟩ := brQuot_surjective π hπ w hw (↑u⁻¹ : PowerSeries (ResidueField W))
      have : f * g - 1 ∈ RingHom.ker (brQuot π hπ w hw) := by
        rw [RingHom.mem_ker, map_sub, map_mul, hu, hg, Units.mul_inv, map_one, sub_self]
      rw [ker_brQuot] at this
      have h1 : (1 : UVCrossingModel W (π ^ w)) ∈ 𝔓 := by
        have := 𝔓.sub_mem (Ideal.mul_mem_right g _ hf𝔓) (hle this)
        rwa [sub_sub_cancel] at this
      exact (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one _).mpr h1)

    obtain ⟨y, hy⟩ := brQuot_surjective π hπ w hw (u : PowerSeries (ResidueField W))
    obtain ⟨y', hy'⟩ := brQuot_surjective π hπ w hw (↑u⁻¹ : PowerSeries (ResidueField W))
    have hVy : V (π ^ w) ^ n * y ∈ 𝔓 := by
      have : f - V (π ^ w) ^ n * y ∈ RingHom.ker (brQuot π hπ w hw) := by
        rw [RingHom.mem_ker, map_sub, map_mul, map_pow, brQuot_V, hy, hu]; exact sub_self _
      rw [ker_brQuot] at this
      have := 𝔓.sub_mem hf𝔓 (hle this)
      rwa [sub_sub_cancel] at this
    have hy𝔓 : y ∉ 𝔓 := by
      intro hy𝔓
      have : y * y' - 1 ∈ RingHom.ker (brQuot π hπ w hw) := by
        rw [RingHom.mem_ker, map_sub, map_mul, hy, hy', Units.mul_inv, map_one, sub_self]
      rw [ker_brQuot] at this
      have h1 : (1 : UVCrossingModel W (π ^ w)) ∈ 𝔓 := by
        have := 𝔓.sub_mem (Ideal.mul_mem_right y' _ hy𝔓) (hle this)
        rwa [sub_sub_cancel] at this
      exact (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one _).mpr h1)
    have := (Ideal.IsPrime.mem_or_mem ‹_› hVy).resolve_right hy𝔓
    exact Ideal.IsPrime.mem_of_pow_mem ‹_› n this

  have hle3 : Ideal.span {const (π ^ w) π, U (π ^ w), V (π ^ w)} ≤ 𝔓 := by
    rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hle (Ideal.subset_span (by simp))
    · exact hle (Ideal.subset_span (by simp))
    · exact hV
  exact ((isMaximal_span_const_U_V π hπ w hw).eq_of_le (Ideal.IsPrime.ne_top ‹_›) hle3).symm

end Crossing

end L1BUV

namespace L1BUV

section Swap

variable {W : Type} [CommRing W] [IsLocalRing W] (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (w : ℕ) (hw : 1 ≤ w)

theorem crossingSwap_U : crossingSwap (π ^ w) (U (π ^ w)) = V (π ^ w) := by
  show crossingSwap (π ^ w) (UVCrossingModel.mk (π ^ w) (MvPowerSeries.X 0)) = UVCrossingModel.mk (π ^ w) (MvPowerSeries.X 1)
  rw [crossingSwap_mk, uvSwapEquiv_X_zero]

theorem crossingSwap_V : crossingSwap (π ^ w) (V (π ^ w)) = U (π ^ w) := by
  show crossingSwap (π ^ w) (UVCrossingModel.mk (π ^ w) (MvPowerSeries.X 1)) = UVCrossingModel.mk (π ^ w) (MvPowerSeries.X 0)
  rw [crossingSwap_mk, uvSwapEquiv_X_one]

theorem crossingSwap_const (a : W) : crossingSwap (π ^ w) (const (π ^ w) a) = const (π ^ w) a := by
  show crossingSwap (π ^ w) (UVCrossingModel.mk (π ^ w) (MvPowerSeries.C a)) = UVCrossingModel.mk (π ^ w) (MvPowerSeries.C a)
  rw [crossingSwap_mk, uvSwapEquiv_C]

theorem map_crossingSwap_span_V :
    (Ideal.span {const (π ^ w) π, V (π ^ w)}).map (crossingSwap (π ^ w)).toRingHom =
      Ideal.span {const (π ^ w) π, U (π ^ w)} := by
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  show Ideal.span {crossingSwap (π ^ w) (const (π ^ w) π), crossingSwap (π ^ w) (V (π ^ w))} = _
  rw [crossingSwap_const, crossingSwap_V]

theorem map_crossingSwap_span_triple :
    (Ideal.span {const (π ^ w) π, U (π ^ w), V (π ^ w)}).map (crossingSwap (π ^ w)).toRingHom =
      Ideal.span {const (π ^ w) π, U (π ^ w), V (π ^ w)} := by
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  show Ideal.span {crossingSwap (π ^ w) (const (π ^ w) π), crossingSwap (π ^ w) (U (π ^ w)),
    crossingSwap (π ^ w) (V (π ^ w))} = _
  rw [crossingSwap_const, crossingSwap_U, crossingSwap_V, Set.pair_comm]

include hπ hw in
theorem isPrime_span_const_V : (Ideal.span {const (π ^ w) π, V (π ^ w)} : Ideal (UVCrossingModel W (π ^ w))).IsPrime := by
  let σ := (crossingSwap (π ^ w)).toRingHom
  have hσbij : Function.Bijective σ := (crossingSwap (π ^ w)).bijective
  have h := isPrime_span_const_U π hπ w hw
  rw [← map_crossingSwap_span_V π w] at h
  have : (Ideal.span {const (π ^ w) π, V (π ^ w)} : Ideal (UVCrossingModel W (π ^ w))) =
      ((Ideal.span {const (π ^ w) π, V (π ^ w)}).map σ).comap σ :=
    (Ideal.comap_map_of_bijective σ hσbij).symm
  rw [this]
  exact Ideal.comap_isPrime σ _

include hπ hw in
theorem eq_span_triple_of_lt_V {𝔓 : Ideal (UVCrossingModel W (π ^ w))} [𝔓.IsPrime]
    (hle : Ideal.span {const (π ^ w) π, V (π ^ w)} ≤ 𝔓) (hne : Ideal.span {const (π ^ w) π, V (π ^ w)} ≠ 𝔓) :
    𝔓 = Ideal.span {const (π ^ w) π, U (π ^ w), V (π ^ w)} := by
  let σ := (crossingSwap (π ^ w)).toRingHom
  have hσbij : Function.Bijective σ := (crossingSwap (π ^ w)).bijective
  haveI : (𝔓.map σ).IsPrime := Ideal.map_isPrime_of_equiv (crossingSwap (π ^ w))
  have hle' : Ideal.span {const (π ^ w) π, U (π ^ w)} ≤ 𝔓.map σ := by
    rw [← map_crossingSwap_span_V π w]; exact Ideal.map_mono hle
  have hne' : Ideal.span {const (π ^ w) π, U (π ^ w)} ≠ 𝔓.map σ := by
    intro h; apply hne
    have := congrArg (Ideal.comap σ) h
    rwa [← map_crossingSwap_span_V π w, Ideal.comap_map_of_bijective _ hσbij,
      Ideal.comap_map_of_bijective _ hσbij] at this
  have h3 := eq_span_triple_of_lt π hπ w hw hle' hne'
  have := congrArg (Ideal.comap σ) h3
  rw [Ideal.comap_map_of_bijective _ hσbij] at this
  rw [this]
  conv_lhs => rw [← map_crossingSwap_span_triple π w]
  exact Ideal.comap_map_of_bijective σ hσbij

include hw in

theorem U_mul_V : U (π ^ w) * V (π ^ w) = const (π ^ w) (π ^ w) := by
  show UVCrossingModel.mk (π ^ w) (MvPowerSeries.X 0) * UVCrossingModel.mk (π ^ w) (MvPowerSeries.X 1) =
    UVCrossingModel.mk (π ^ w) (MvPowerSeries.C (π ^ w))
  rw [← map_mul, ← sub_eq_zero, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)

include hπ hw in

theorem eq_span_or_of_const_mem {𝔓 : Ideal (UVCrossingModel W (π ^ w))} [𝔓.IsPrime] (hπ𝔓 : const (π ^ w) π ∈ 𝔓) :
    𝔓 = Ideal.span {const (π ^ w) π, U (π ^ w)} ∨ 𝔓 = Ideal.span {const (π ^ w) π, V (π ^ w)} ∨
      𝔓 = Ideal.span {const (π ^ w) π, U (π ^ w), V (π ^ w)} := by
  have hUV : U (π ^ w) * V (π ^ w) ∈ 𝔓 := by
    rw [U_mul_V π w hw]
    have : const (π ^ w) (π ^ w) = const (π ^ w) π ^ w := by
      show UVCrossingModel.mk (π ^ w) (MvPowerSeries.C (π ^ w)) = UVCrossingModel.mk (π ^ w) (MvPowerSeries.C π) ^ w
      rw [← map_pow, ← map_pow]
    rw [this]
    exact Ideal.pow_mem_of_mem 𝔓 hπ𝔓 w hw
  rcases Ideal.IsPrime.mem_or_mem ‹_› hUV with hU | hV
  · have hle : Ideal.span {const (π ^ w) π, U (π ^ w)} ≤ 𝔓 := by
      rw [Ideal.span_le]; intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl <;> assumption
    by_cases h : Ideal.span {const (π ^ w) π, U (π ^ w)} = 𝔓
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr (eq_span_triple_of_lt π hπ w hw hle h))
  · have hle : Ideal.span {const (π ^ w) π, V (π ^ w)} ≤ 𝔓 := by
      rw [Ideal.span_le]; intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl <;> assumption
    by_cases h : Ideal.span {const (π ^ w) π, V (π ^ w)} = 𝔓
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr (eq_span_triple_of_lt_V π hπ w hw hle h))

end Swap

end L1BUV

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem solution
    {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (w : ℕ) (hw : 1 ≤ w)
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (ι : AdicCompletion (maximalIdeal O) O ≃+* UVCrossingModel W (π ^ w))
    (t : O) (ht : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) t) = const (π ^ w) π)

    (𝔭₁ 𝔭₂ : Ideal O) [𝔭₁.IsPrime] [𝔭₂.IsPrime] (h₁₂ : 𝔭₁ ≠ 𝔭₂)
    (ht₁ : t ∈ 𝔭₁) (ht₂ : t ∈ 𝔭₂) (h₁ : 𝔭₁ ≠ maximalIdeal O) (h₂ : 𝔭₂ ≠ maximalIdeal O) :
    ((∀ f : O, f ∈ 𝔭₁ ↔
        ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) ∈ Ideal.span {const (π ^ w) π, U (π ^ w)}) ∧
      (∀ f : O, f ∈ 𝔭₂ ↔
        ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) ∈ Ideal.span {const (π ^ w) π, V (π ^ w)})) ∨
    ((∀ f : O, f ∈ 𝔭₁ ↔
        ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) ∈ Ideal.span {const (π ^ w) π, V (π ^ w)}) ∧
      (∀ f : O, f ∈ 𝔭₂ ↔
        ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) ∈ Ideal.span {const (π ^ w) π, U (π ^ w)})) := by
  classical

  have hfg : (maximalIdeal O).FG := IsNoetherian.noetherian _
  set J : Ideal (AdicCompletion (maximalIdeal O) O) :=
    (maximalIdeal O).map (algebraMap O (AdicCompletion (maximalIdeal O) O)) with hJ
  have hker : ∀ (n : ℕ) (x : AdicCompletion (maximalIdeal O) O),
      AdicCompletion.evalₐ (maximalIdeal O) n x = 0 ↔ x ∈ J ^ n := by
    intro n x
    rw [hJ, ← Ideal.map_pow]
    have h1 : x ∈ ((maximalIdeal O) ^ n).map (algebraMap O (AdicCompletion (maximalIdeal O) O)) ↔
        x ∈ ((maximalIdeal O) ^ n • ⊤ : Submodule O (AdicCompletion (maximalIdeal O) O)) := by
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
    rw [h1, AdicCompletion.pow_smul_top_eq_ker_eval hfg, LinearMap.mem_ker]
    constructor
    · intro h0
      rw [← AdicCompletion.factor_evalₐ_eq_eval (maximalIdeal O) x (le_of_eq (by rw [smul_eq_mul, Ideal.mul_top])), h0,
        map_zero]
    · intro h0
      rw [← AdicCompletion.factor_eval_eq_evalₐ (maximalIdeal O) x (le_of_eq (by rw [smul_eq_mul, Ideal.mul_top])), h0,
        map_zero]
  haveI : ((maximalIdeal O) ^ 1).IsMaximal := by rw [pow_one]; infer_instance
  have hJker : J = RingHom.ker (AdicCompletion.evalₐ (maximalIdeal O) 1).toRingHom := by
    ext x; rw [RingHom.mem_ker]; exact ((hker 1 x).trans (by rw [pow_one])).symm
  haveI hJmax : J.IsMaximal := by
    letI : Field (O ⧸ (maximalIdeal O) ^ 1) := Ideal.Quotient.field ((maximalIdeal O) ^ 1)
    rw [hJker]
    exact RingHom.ker_isMaximal_of_surjective _ (AdicCompletion.surjective_evalₐ (maximalIdeal O) 1)
  haveI : IsAdicComplete J (AdicCompletion (maximalIdeal O) O) :=
    (IsAdicComplete.map_algebraMap_iff (I := (maximalIdeal O)) (S := AdicCompletion (maximalIdeal O) O)
      (M := AdicCompletion (maximalIdeal O) O)).mpr (AdicCompletion.isAdicComplete hfg)
  haveI hlocC : IsLocalRing (AdicCompletion (maximalIdeal O) O) := isLocalRing_of_isAdicComplete_maximal J
  have hmaxC : maximalIdeal (AdicCompletion (maximalIdeal O) O) = J := (IsLocalRing.eq_maximalIdeal hJmax).symm

  haveI : IsLocalHom (algebraMap O (AdicCompletion (maximalIdeal O) O)) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : algebraMap O (AdicCompletion (maximalIdeal O) O) a ∈ J :=
      Ideal.mem_map_of_mem _ ((mem_maximalIdeal a).mpr hna)
    rw [← hmaxC] at h1
    exact (mem_maximalIdeal _).mp h1 ha
  haveI : Module.Flat O (AdicCompletion (maximalIdeal O) O) := AdicCompletion.flat_of_isNoetherian _
  haveI : Module.FaithfullyFlat O (AdicCompletion (maximalIdeal O) O) := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hsurj := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := O) (B := AdicCompletion (maximalIdeal O) O)

  have key : ∀ (𝔭 : Ideal O) [𝔭.IsPrime], t ∈ 𝔭 → 𝔭 ≠ maximalIdeal O →
      (∀ f : O, f ∈ 𝔭 ↔ ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) ∈
          Ideal.span {const (π ^ w) π, U (π ^ w)}) ∨
      (∀ f : O, f ∈ 𝔭 ↔ ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) ∈
          Ideal.span {const (π ^ w) π, V (π ^ w)}) := by
    intro 𝔭 _ ht𝔭 h𝔭
    obtain ⟨⟨𝔓', h𝔓'⟩, hcomap⟩ := hsurj ⟨𝔭, ‹_›⟩
    have h𝔭eq : 𝔭 = 𝔓'.comap (algebraMap O (AdicCompletion (maximalIdeal O) O)) :=
      (congrArg PrimeSpectrum.asIdeal hcomap).symm
    have hmem : ∀ f : O, f ∈ 𝔭 ↔ algebraMap O (AdicCompletion (maximalIdeal O) O) f ∈ 𝔓' := fun f => by
      rw [h𝔭eq, Ideal.mem_comap]
    set 𝔓 : Ideal (UVCrossingModel W (π ^ w)) := 𝔓'.map ι.toRingHom with h𝔓
    haveI : 𝔓.IsPrime := Ideal.map_isPrime_of_equiv ι
    have hmem2 : ∀ x, x ∈ 𝔓' ↔ ι x ∈ 𝔓 := fun x => by
      conv_lhs => rw [← Ideal.comap_map_of_bijective ι.toRingHom ι.bijective (I := 𝔓')]
      rw [Ideal.mem_comap]
      rfl
    have hπ𝔓 : const (π ^ w) π ∈ 𝔓 := by
      rw [← ht]; exact (hmem2 _).mp ((hmem t).mp ht𝔭)
    rcases L1BUV.eq_span_or_of_const_mem π hπ w hw hπ𝔓 with h | h | h
    · left; intro f; rw [hmem, hmem2, h]
    · right; intro f; rw [hmem, hmem2, h]
    · exfalso
      apply h𝔭

      haveI : 𝔓.IsMaximal := h ▸ L1BUV.isMaximal_span_const_U_V π hπ w hw
      have h𝔓'max : 𝔓'.IsMaximal := by
        have : 𝔓' = 𝔓.comap ι.toRingHom := by
          rw [h𝔓, Ideal.comap_map_of_bijective ι.toRingHom ι.bijective]
        rw [this]
        exact Ideal.comap_isMaximal_of_surjective ι.toRingHom ι.surjective
      have h𝔓'J : 𝔓' = J := by rw [← hmaxC]; exact IsLocalRing.eq_maximalIdeal h𝔓'max
      have hle : maximalIdeal O ≤ 𝔭 := by
        rw [h𝔭eq, h𝔓'J, hJ]
        exact Ideal.le_comap_map
      exact ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (Ideal.IsPrime.ne_top ‹_›) hle).symm
  rcases key 𝔭₁ ht₁ h₁ with A1 | B1 <;> rcases key 𝔭₂ ht₂ h₂ with A2 | B2
  · exact absurd (Ideal.ext fun f => (A1 f).trans (A2 f).symm) h₁₂
  · exact Or.inl ⟨A1, B2⟩
  · exact Or.inr ⟨B1, A2⟩
  · exact absurd (Ideal.ext fun f => (B1 f).trans (B2 f).symm) h₁₂

end S_ModularCurve_UVCrossingModel_mem_iff_ringEquiv_adicCompletion_mem_span_or_swap_of_ne
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_mem_iff_ringEquiv_adicCompletion_mem_span_or_swap_of_ne (solution)
