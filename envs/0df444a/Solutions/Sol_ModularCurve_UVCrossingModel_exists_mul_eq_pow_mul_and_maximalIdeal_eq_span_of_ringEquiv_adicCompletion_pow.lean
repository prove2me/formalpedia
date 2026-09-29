-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_mul_eq_pow_mul_and_maximalIdeal_eq_span_of_ringEquiv_adicCompletion_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/771096f4-5a61-5994-a16e-7df4aca6bb38

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_mem_span_U_of_mul_mem_of_notMem
import Theorems.Thm_ModularCurve_UVCrossingModel_maximalIdeal_eq_map_maximalIdeal_sup_span_pair
import Theorems.Thm_IsLocalRing_comap_map_adicCompletion_eq
import Theorems.Thm_ModularCurve_UVCrossingModel_mem_iff_ringEquiv_adicCompletion_mem_span_or_swap_of_ne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_mul_eq_pow_mul_and_maximalIdeal_eq_span_of_ringEquiv_adicCompletion_pow

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 12800000

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel TensorProduct

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

end Crossing

end L1BUV

namespace KFCD

theorem mem_map_colon_of_flat {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (J : Ideal A) (s : A) (r : B) (h : algebraMap A B s * r ∈ J.map (algebraMap A B)) :
    r ∈ (J.colon {s}).map (algebraMap A B) := by
  classical
  let f : A →ₗ[A] (A ⧸ J) := (Ideal.Quotient.mkₐ A J).toLinearMap.comp (LinearMap.mul A A s)
  have hf : ∀ a : A, f a = Ideal.Quotient.mk J (s * a) := fun _ => rfl
  have hkerf : ∀ a : A, a ∈ LinearMap.ker f ↔ a ∈ J.colon {s} := by
    intro a
    rw [LinearMap.mem_ker, hf, Ideal.Quotient.eq_zero_iff_mem, Submodule.mem_colon_singleton, smul_eq_mul,
      mul_comm]
  have hexact : Function.Exact (LinearMap.ker f).subtype f := LinearMap.exact_subtype_ker_map f
  have hT := Module.Flat.lTensor_exact B hexact

  have h0 : (f.lTensor B) (r ⊗ₜ[A] (1 : A)) = 0 := by
    rw [LinearMap.lTensor_tmul, hf]
    apply (TensorProduct.tensorQuotEquivQuotSMul B J).injective
    rw [map_zero, TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, Submodule.Quotient.mk_eq_zero, mul_one]
    have hmem : s • r ∈ J • (⊤ : Submodule A B) := by
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Algebra.smul_def]; exact h
    exact hmem

  obtain ⟨z, hz⟩ := (hT _).mp h0

  have key : ∀ z : B ⊗[A] (LinearMap.ker f),
      TensorProduct.rid A B (((LinearMap.ker f).subtype.lTensor B) z) ∈ (J.colon {s}).map (algebraMap A B) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b k =>
      rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Submodule.coe_subtype, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ((hkerf k).mp k.2))
    | add x y hx hy => rw [map_add, map_add]; exact Ideal.add_mem _ hx hy
  have := key z
  rwa [hz, TensorProduct.rid_tmul, one_smul] at this

end KFCD

namespace KFCD

theorem exists_brQuotU {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (w : ℕ) (hw : 1 ≤ w) :
    ∃ β : UVCrossingModel W (π ^ w) →+* PowerSeries (ResidueField W),
      β (U (π ^ w)) = 0 ∧ β (V (π ^ w)) = PowerSeries.X ∧
      (∀ a : W, β (const (π ^ w) a) = PowerSeries.C (IsLocalRing.residue W a)) ∧
      Function.Surjective β ∧ RingHom.ker β = Ideal.span {const (π ^ w) π, U (π ^ w)} :=
  ⟨L1BUV.brQuot π hπ w hw, L1BUV.brQuot_U π hπ w hw, L1BUV.brQuot_V π hπ w hw, L1BUV.brQuot_const π hπ w hw,
    L1BUV.brQuot_surjective π hπ w hw, L1BUV.ker_brQuot π hπ w hw⟩

theorem exists_brQuotV {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (w : ℕ) (hw : 1 ≤ w) :
    ∃ β : UVCrossingModel W (π ^ w) →+* PowerSeries (ResidueField W),
      β (V (π ^ w)) = 0 ∧ β (U (π ^ w)) = PowerSeries.X ∧
      (∀ a : W, β (const (π ^ w) a) = PowerSeries.C (IsLocalRing.residue W a)) ∧
      Function.Surjective β ∧ RingHom.ker β = Ideal.span {const (π ^ w) π, V (π ^ w)} := by
  obtain ⟨β, hU, hV, hc, hs, hk⟩ := exists_brQuotU π hπ w hw
  let σ := crossingSwap (W := W) (π ^ w)
  have hσU : σ (U (π ^ w)) = V (π ^ w) := by
    show σ (UVCrossingModel.mk (π ^ w) (MvPowerSeries.X 0)) = UVCrossingModel.mk (π ^ w) (MvPowerSeries.X 1)
    rw [crossingSwap_mk, uvSwapEquiv_X_zero]
  have hσV : σ (V (π ^ w)) = U (π ^ w) := by
    show σ (UVCrossingModel.mk (π ^ w) (MvPowerSeries.X 1)) = UVCrossingModel.mk (π ^ w) (MvPowerSeries.X 0)
    rw [crossingSwap_mk, uvSwapEquiv_X_one]
  have hσc : ∀ a : W, σ (const (π ^ w) a) = const (π ^ w) a := fun a => by
    show σ (UVCrossingModel.mk (π ^ w) (MvPowerSeries.C a)) = UVCrossingModel.mk (π ^ w) (MvPowerSeries.C a)
    rw [crossingSwap_mk, uvSwapEquiv_C]
  refine ⟨β.comp σ.toRingHom, ?_, ?_, ?_, ?_, ?_⟩
  · show β (σ (V (π ^ w))) = 0; rw [hσV, hU]
  · show β (σ (U (π ^ w))) = PowerSeries.X; rw [hσU, hV]
  · intro a; show β (σ (const (π ^ w) a)) = _; rw [hσc, hc]
  · exact hs.comp σ.surjective
  · rw [← RingHom.comap_ker, hk]
    have : (Ideal.span {const (π ^ w) π, V (π ^ w)}).map σ.toRingHom = Ideal.span {const (π ^ w) π, U (π ^ w)} := by
      rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
      show Ideal.span {σ (const (π ^ w) π), σ (V (π ^ w))} = _
      rw [hσc, hσV]
    rw [← this, Ideal.comap_map_of_bijective σ.toRingHom (show Function.Bijective σ.toRingHom from σ.bijective)]

private theorem _root_.KFCD.exists_ringHom_killU (W : Type) [CommRing W] :
    ∃ Ψ : MvPowerSeries (Fin 2) W →+* PowerSeries W,
      Ψ (MvPowerSeries.X 0) = 0 ∧ Ψ (MvPowerSeries.X 1) = PowerSeries.X ∧
      (∀ a : W, Ψ (MvPowerSeries.C a) = PowerSeries.C a) ∧
      (∀ F, Ψ F = 0 ↔ MvPowerSeries.X 0 ∣ F) ∧ Function.Surjective Ψ :=
  L1BUV.exists_ringHom_killU W

p2m_export "KFCD" "exists_ringHom_killU"

theorem sup_pow_le_pow_sup {R : Type} [CommRing R] (A B : Ideal R) (n : ℕ) :
    (A ⊔ B) ^ n ≤ A ^ n ⊔ B := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    calc (A ⊔ B) ^ n * (A ⊔ B) ≤ (A ^ n ⊔ B) * (A ⊔ B) := Ideal.mul_mono_left ih
      _ ≤ A ^ n * A ⊔ B := by
        rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
        refine sup_le (sup_le le_sup_left ?_) (sup_le ?_ ?_)
        · exact le_sup_right.trans' Ideal.mul_le_right
        · exact le_sup_right.trans' Ideal.mul_le_left
        · exact le_sup_right.trans' Ideal.mul_le_left

theorem sup_span_pow_le {R : Type} [CommRing R] (A : Ideal R) (v : R) (n : ℕ) :
    (A ⊔ Ideal.span {v}) ^ n ≤ A ⊔ Ideal.span {v ^ n} := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    calc (A ⊔ Ideal.span {v}) ^ n * (A ⊔ Ideal.span {v}) ≤ (A ⊔ Ideal.span {v ^ n}) * (A ⊔ Ideal.span {v}) :=
          Ideal.mul_mono_left ih
      _ ≤ A ⊔ Ideal.span {v ^ n * v} := by
        rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton]
        refine sup_le (sup_le ?_ ?_) (sup_le ?_ le_sup_right)
        · exact le_sup_left.trans' Ideal.mul_le_left
        · exact le_sup_left.trans' Ideal.mul_le_left
        · exact le_sup_left.trans' Ideal.mul_le_right

end KFCD

namespace KFCD

theorem core
    {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (w : ℕ) (hw : 1 ≤ w)
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (ι : AdicCompletion (maximalIdeal O) O ≃+* UVCrossingModel W (π ^ w))
    (t : O) (ht : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) t) = const (π ^ w) π)
    (f : O)
    (hfU : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) ∈ Ideal.span {const (π ^ w) π, U (π ^ w)})
    (hfV : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) f) ∉ Ideal.span {const (π ^ w) π, V (π ^ w)}) :
    ∃ (xn yn u : O) (γ γ' : UVCrossingModel W (π ^ w)),
      IsUnit u ∧ IsUnit γ ∧ IsUnit γ' ∧
      ι (algebraMap O (AdicCompletion (maximalIdeal O) O) xn) = γ * U (π ^ w) ∧
      ι (algebraMap O (AdicCompletion (maximalIdeal O) O) yn) = γ' * V (π ^ w) ∧
      xn * yn = t ^ w * u ∧
      maximalIdeal O = Ideal.span {xn, yn, t} := by
  classical

  let R := UVCrossingModel W (π ^ w)
  let Oh := AdicCompletion (maximalIdeal O) O
  let φ : O →+* R := ι.toRingHom.comp (algebraMap O Oh)
  have hφ : ∀ x : O, φ x = ι (algebraMap O Oh x) := fun _ => rfl
  set cπ : R := const (π ^ w) π with hcπ
  set uU : R := U (π ^ w) with huU
  set vV : R := V (π ^ w) with hvV
  have hφt : φ t = cπ := ht

  have hπirr : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ
  have hπ0 : π ≠ 0 := hπirr.ne_zero
  have hπnu : ¬ IsUnit π := hπirr.not_isUnit
  have hπwnu : ¬ IsUnit (π ^ w) := fun h => hπnu (isUnit_pow_iff (by omega) |>.mp h)
  have hconst : ∀ a b : W, const (π ^ w) (a * b) = const (π ^ w) a * const (π ^ w) b := fun a b =>
    map_mul (constHom (π ^ w)) a b
  have hconstpow : ∀ (a : W) (n : ℕ), const (π ^ w) (a ^ n) = const (π ^ w) a ^ n := fun a n =>
    map_pow (constHom (π ^ w)) a n
  have hUV : uU * vV = cπ ^ w := by
    rw [huU, hvV, hcπ, ← hconstpow]
    show mk (π ^ w) (MvPowerSeries.X 0) * mk (π ^ w) (MvPowerSeries.X 1) = mk (π ^ w) (MvPowerSeries.C (π ^ w))
    rw [← map_mul, ← sub_eq_zero, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

  have hfg : (maximalIdeal O).FG := IsNoetherian.noetherian _
  set J : Ideal Oh := (maximalIdeal O).map (algebraMap O Oh) with hJ
  have hker : ∀ (n : ℕ) (x : Oh), AdicCompletion.evalₐ (maximalIdeal O) n x = 0 ↔ x ∈ J ^ n := by
    intro n x
    rw [hJ, ← Ideal.map_pow]
    have h1 : x ∈ ((maximalIdeal O) ^ n).map (algebraMap O Oh) ↔
        x ∈ ((maximalIdeal O) ^ n • ⊤ : Submodule O Oh) := by
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
  haveI : IsAdicComplete J Oh :=
    (IsAdicComplete.map_algebraMap_iff (I := (maximalIdeal O)) (S := Oh) (M := Oh)).mpr
      (AdicCompletion.isAdicComplete hfg)
  haveI hOhloc : IsLocalRing Oh := isLocalRing_of_isAdicComplete_maximal J
  have hmaxOh : maximalIdeal Oh = J := (IsLocalRing.eq_maximalIdeal hJmax).symm
  haveI : Nontrivial R := ι.injective.nontrivial
  haveI hRloc : IsLocalRing R := IsLocalRing.of_surjective' ι.toRingHom ι.surjective

  have hcm : ∀ I : Ideal O, (I.map φ).comap φ = I := by
    intro I
    have := IsLocalRing.comap_map_adicCompletion_eq I
    rw [show φ = ι.toRingHom.comp (algebraMap O Oh) from rfl, ← Ideal.map_map, ← Ideal.comap_comap,
      Ideal.comap_map_of_bijective ι.toRingHom (show Function.Bijective ι.toRingHom from ι.bijective)]
    exact this
  have hmem : ∀ (I : Ideal O) (x : O), φ x ∈ I.map φ ↔ x ∈ I := fun I x => by
    rw [← Ideal.mem_comap, hcm]
  have hunit : ∀ x : O, IsUnit (φ x) → IsUnit x := by
    intro x hx
    rw [← Ideal.span_singleton_eq_top, ← hcm (Ideal.span {x}), Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_eq_top.mpr hx, Ideal.comap_top]

  have hmR : maximalIdeal R = Ideal.span {cπ, uU, vV} := by
    have := ModularCurve.UVCrossingModel.maximalIdeal_eq_map_maximalIdeal_sup_span_pair (W := W) (π := π ^ w) hπwnu
    rw [this, hπ, Ideal.map_span, Set.image_singleton, constHom_apply, ← hcπ, ← huU, ← hvV,
      ← Ideal.span_union, Set.singleton_union]
  have hmRφ : (maximalIdeal O).map φ = maximalIdeal R := by
    rw [show φ = ι.toRingHom.comp (algebraMap O Oh) from rfl, ← Ideal.map_map, ← hJ, ← hmaxOh]

    have hmax' : (Ideal.map ι (maximalIdeal Oh)).IsMaximal := Ideal.map_isMaximal_of_equiv ι
    show Ideal.map ι (maximalIdeal Oh) = maximalIdeal R
    exact IsLocalRing.eq_maximalIdeal hmax'

  letI algOR : Algebra O R := φ.toAlgebra
  haveI : Module.Flat O R := by
    haveI : Module.Flat O Oh := AdicCompletion.flat_of_isNoetherian (maximalIdeal O)
    let e : Oh ≃ₗ[O] R :=
      { toFun := ι, invFun := ι.symm, map_add' := fun x y => map_add ι x y,
        map_smul' := fun c x => by
          show ι (c • x) = φ c * ι x
          rw [Algebra.smul_def, map_mul]; rfl
        left_inv := ι.left_inv, right_inv := ι.right_inv }
    exact Module.Flat.of_linearEquiv e.symm

  have hdense : ∀ (r : R) (N : ℕ), ∃ x : O, r - φ x ∈ maximalIdeal R ^ N := by
    intro r N
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal O) N (ι.symm r))
    refine ⟨a, ?_⟩
    have h1 : ι.symm r - algebraMap O Oh a ∈ J ^ N := by
      rw [← hker, map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of, Algebra.algebraMap_self,
        RingHom.id_apply, ha, sub_self]
    have h2 : ι (ι.symm r - algebraMap O Oh a) ∈ (J ^ N).map ι.toRingHom := Ideal.mem_map_of_mem _ h1
    rw [map_sub, RingEquiv.apply_symm_apply, Ideal.map_pow, ← hmaxOh] at h2
    rwa [show Ideal.map ι.toRingHom (maximalIdeal Oh) = maximalIdeal R from
      IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv ι (p := maximalIdeal Oh))] at h2

  obtain ⟨βU, hβU_U, hβU_V, hβU_c, hβU_surj, hβU_ker⟩ := exists_brQuotU π hπ w hw
  obtain ⟨βV, hβV_V, hβV_U, hβV_c, hβV_surj, hβV_ker⟩ := exists_brQuotV π hπ w hw
  let 𝔓 : Ideal R := Ideal.span {cπ, uU}
  haveI h𝔓p : 𝔓.IsPrime := by
    show (Ideal.span {cπ, uU}).IsPrime
    rw [hcπ, huU, ← hβU_ker]
    exact RingHom.ker_isPrime βU

  have hβU_cπ : βU cπ = 0 := by
    rw [hcπ, hβU_c, (IsLocalRing.residue_eq_zero_iff π).mpr (hπ.symm ▸ Ideal.mem_span_singleton_self π), map_zero]
  have hβV_cπ : βV cπ = 0 := by
    rw [hcπ, hβV_c, (IsLocalRing.residue_eq_zero_iff π).mpr (hπ.symm ▸ Ideal.mem_span_singleton_self π), map_zero]
  have hβU_m : (maximalIdeal R).map βU ≤ Ideal.span {PowerSeries.X} := by
    rw [hmR, Ideal.map_span, Ideal.span_le]
    rintro y ⟨x, hx, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · rw [hβU_cπ]; exact Ideal.zero_mem _
    · rw [huU, hβU_U]; exact Ideal.zero_mem _
    · rw [hvV, hβU_V]; exact Ideal.mem_span_singleton_self _
  have hβU_mpow : ∀ (N : ℕ) (x : R), x ∈ maximalIdeal R ^ N → βU x ∈ Ideal.span {(PowerSeries.X : PowerSeries (ResidueField W)) ^ N} := by
    intro N x hx
    have : βU x ∈ ((maximalIdeal R) ^ N).map βU := Ideal.mem_map_of_mem _ hx
    rw [Ideal.map_pow] at this
    rw [← Ideal.span_singleton_pow]
    exact Ideal.pow_right_mono hβU_m N this

  have hXpow : ∀ N : ℕ, 2 ≤ N → (PowerSeries.X : PowerSeries (ResidueField W)) ∉ Ideal.span {(PowerSeries.X : PowerSeries (ResidueField W)) ^ N} := by
    intro N hN hmem
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have h1 : PowerSeries.order ((PowerSeries.X : PowerSeries (ResidueField W)) ^ N * c) = PowerSeries.order (PowerSeries.X : PowerSeries (ResidueField W)) := by rw [← hc]
    rw [PowerSeries.order_mul, PowerSeries.order_X_pow, PowerSeries.order_X] at h1
    have : (N : ℕ∞) ≤ 1 := by rw [← h1]; exact le_self_add
    have : N ≤ 1 := by exact_mod_cast this
    omega

  let 𝔭 : Ideal O := 𝔓.comap φ
  haveI h𝔭p : 𝔭.IsPrime := Ideal.comap_isPrime φ 𝔓
  have hcπ𝔓 : cπ ∈ 𝔓 := Ideal.subset_span (by simp)
  have huU𝔓 : uU ∈ 𝔓 := Ideal.subset_span (by simp)
  have ht𝔭 : t ∈ 𝔭 := by show φ t ∈ 𝔓; rw [hφt]; exact hcπ𝔓
  have hf𝔭 : f ∈ 𝔭 := hfU
  have hI₁le : 𝔭.map φ ≤ 𝔓 := Ideal.map_comap_le
  have hcπI : cπ ∈ 𝔭.map φ := hφt ▸ Ideal.mem_map_of_mem φ ht𝔭
  have hfI : φ f ∈ 𝔭.map φ := Ideal.mem_map_of_mem φ hf𝔭

  obtain ⟨m, hUm⟩ : ∃ m : ℕ, uU ^ (m + 1) ∈ Ideal.span {φ f, cπ} := by
    have hg : βV (φ f) ≠ 0 := by
      intro h0
      apply hfV
      have : φ f ∈ RingHom.ker βV := h0
      rw [hβV_ker] at this
      exact this
    set g := βV (φ f) with hgdef
    let m := g.order.toNat
    set q := PowerSeries.Inv_divided_by_X_pow_order hg with hq
    have hInv : PowerSeries.divXPowOrder g * q = 1 := PowerSeries.Inv_divided_by_X_pow_order_rightInv hg
    have hsplitg : (PowerSeries.X : PowerSeries (ResidueField W)) ^ m * PowerSeries.divXPowOrder g = g :=
      PowerSeries.X_pow_order_mul_divXPowOrder
    obtain ⟨c, hc⟩ := hβV_surj q
    have hXm : (PowerSeries.X : PowerSeries (ResidueField W)) ^ m = g * βV c := by
      rw [hc]
      calc (PowerSeries.X : PowerSeries (ResidueField W)) ^ m
          = (PowerSeries.X : PowerSeries (ResidueField W)) ^ m * (PowerSeries.divXPowOrder g * q) := by rw [hInv, mul_one]
        _ = ((PowerSeries.X : PowerSeries (ResidueField W)) ^ m * PowerSeries.divXPowOrder g) * q := by rw [mul_assoc]
        _ = g * q := by rw [hsplitg]
    have hdiff : uU ^ m - φ f * c ∈ Ideal.span {cπ, vV} := by
      rw [← hβV_ker, RingHom.mem_ker, map_sub, map_mul, map_pow, hβV_U, ← hgdef, hXm, sub_self]
    rw [Ideal.mem_span_pair] at hdiff
    obtain ⟨a, b, hab⟩ := hdiff
    refine ⟨m, ?_⟩
    have : uU ^ (m + 1) = (uU * c) * φ f + (a * uU + b * cπ ^ (w - 1)) * cπ := by
      have e1 : uU ^ (m + 1) = uU * (uU ^ m - φ f * c) + uU * c * φ f := by ring
      rw [e1, ← hab]
      have e2 : uU * vV = cπ ^ (w - 1) * cπ := by rw [hUV, ← pow_succ, Nat.sub_add_cancel hw]
      calc uU * (a * cπ + b * vV) + uU * c * φ f = a * uU * cπ + b * (uU * vV) + uU * c * φ f := by ring
        _ = (uU * c) * φ f + (a * uU + b * cπ ^ (w - 1)) * cπ := by rw [e2]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  have hUmI : uU ^ (m + 1) ∈ 𝔭.map φ := by
    refine (Ideal.span_le.mpr ?_) hUm
    rintro y hy
    rcases hy with rfl | hy
    · exact hfI
    · rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hcπI

  obtain ⟨d, hd⟩ := hdense vV (m + w + 2)
  set h : R := vV - φ d with hh
  have hφd : φ d = vV - h := by rw [hh]; ring
  have hd𝔭 : d ∉ 𝔭 := by
    intro hdp
    have h1 : βU (φ d) = 0 := by
      have : φ d ∈ 𝔓 := hdp
      rw [show 𝔓 = Ideal.span {cπ, uU} from rfl, ← hβU_ker] at this
      exact this
    have h2 : βU h ∈ Ideal.span {(PowerSeries.X : PowerSeries (ResidueField W)) ^ (m + w + 2)} := hβU_mpow _ _ hd
    rw [hh, map_sub, h1, sub_zero, hβU_V] at h2
    exact hXpow (m + w + 2) (by omega) h2

  have hdecomp : maximalIdeal R = 𝔓 ⊔ Ideal.span {vV} := by
    rw [hmR, show 𝔓 = Ideal.span {cπ, uU} from rfl, ← Ideal.span_union]
    have : ({cπ, uU, vV} : Set R) = {cπ, uU} ∪ {vV} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      tauto
    rw [this]
  have h𝔓pow : ∀ N : ℕ, 𝔓 ^ N ≤ Ideal.span {cπ} ⊔ Ideal.span {uU ^ N} := by
    intro N
    have : 𝔓 = Ideal.span {cπ} ⊔ Ideal.span {uU} := by
      rw [show 𝔓 = Ideal.span {cπ, uU} from rfl, ← Ideal.span_union]; rfl
    rw [this]; exact sup_span_pow_le _ _ N
  have hmpow_U : ∀ (N : ℕ) (x : R), x ∈ maximalIdeal R ^ N →
      x * uU ∈ Ideal.span {cπ} ⊔ Ideal.span {uU ^ (N + 1)} := by
    intro N x hx
    rw [hdecomp] at hx
    have hx' := sup_pow_le_pow_sup 𝔓 (Ideal.span {vV}) N hx
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hx'
    obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := Submodule.mem_sup.mp (h𝔓pow N hp)
    rw [Ideal.mem_span_singleton] at hp₁ hp₂ hq
    obtain ⟨a₁, rfl⟩ := hp₁
    obtain ⟨a₂, rfl⟩ := hp₂
    obtain ⟨b, rfl⟩ := hq
    have : (cπ * a₁ + uU ^ N * a₂ + vV * b) * uU = cπ * (a₁ * uU + cπ ^ (w - 1) * b) + uU ^ (N + 1) * a₂ := by
      have e2 : vV * uU = cπ ^ (w - 1) * cπ := by rw [mul_comm, hUV, ← pow_succ, Nat.sub_add_cancel hw]
      calc (cπ * a₁ + uU ^ N * a₂ + vV * b) * uU = cπ * a₁ * uU + uU ^ N * uU * a₂ + (vV * uU) * b := by ring
        _ = _ := by rw [e2]; ring
    rw [this]
    exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hcπw : cπ ^ w ∈ 𝔭.map φ := Ideal.pow_mem_of_mem _ hcπI w (by omega)
  have hdU : φ d * uU ∈ 𝔭.map φ := by
    rw [hφd, sub_mul, mul_comm vV uU, hUV]
    refine Ideal.sub_mem _ hcπw ?_
    have := hmpow_U (m + w + 2) h hd
    obtain ⟨p₁, hp₁, p₂, hp₂, hsum⟩ := Submodule.mem_sup.mp this
    rw [← hsum]
    rw [Ideal.mem_span_singleton] at hp₁ hp₂
    obtain ⟨a₁, rfl⟩ := hp₁
    obtain ⟨a₂, rfl⟩ := hp₂
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hcπI) ?_
    rw [show uU ^ (m + w + 2 + 1) * a₂ = uU ^ (m + 1) * (uU ^ (w + 2) * a₂) by ring]
    exact Ideal.mul_mem_right _ _ hUmI

  have hcolon𝔭 : 𝔭.colon {d} = 𝔭 := by
    ext x
    rw [Submodule.mem_colon_singleton, smul_eq_mul]
    exact ⟨fun hx => (h𝔭p.mem_or_mem hx).resolve_right hd𝔭, fun hx => Ideal.mul_mem_right _ _ hx⟩
  have hUI : uU ∈ 𝔭.map φ := by
    have := mem_map_colon_of_flat (A := O) (B := R) 𝔭 d uU hdU
    rwa [hcolon𝔭] at this
  have h𝔭R : 𝔭.map φ = 𝔓 := by
    refine le_antisymm hI₁le ?_
    rw [show 𝔓 = Ideal.span {cπ, uU} from rfl, Ideal.span_le]
    rintro y hy
    rcases hy with rfl | hy
    · exact hcπI
    · rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hUI

  let I : Ideal O := (𝔭 ^ w).colon {d}
  have h𝔓w_le : 𝔓 ^ w ≤ Ideal.span {uU} := by
    have e : 𝔓 = Ideal.span {uU} ⊔ Ideal.span {cπ} := by
      rw [show 𝔓 = Ideal.span {cπ, uU} from rfl, ← Ideal.span_union]
      congr 1; ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]; tauto
    rw [e]
    refine (sup_span_pow_le _ _ w).trans (sup_le le_rfl ?_)
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton, ← hUV]
    exact dvd_mul_right _ _
  have h𝔭w : (𝔭 ^ w).map φ = 𝔓 ^ w := by rw [Ideal.map_pow, h𝔭R]
  have hd𝔓 : φ d ∉ 𝔓 := hd𝔭

  have h2a : ∀ x ∈ I, φ x ∈ Ideal.span {uU} := by
    intro x hx
    have hx' : x * d ∈ 𝔭 ^ w := by
      have := (Submodule.mem_colon_singleton.mp hx); rwa [smul_eq_mul] at this
    have h1 : φ d * φ x ∈ Ideal.span {uU} := by
      rw [← map_mul, mul_comm]; exact h𝔓w_le (h𝔭w ▸ Ideal.mem_map_of_mem φ hx')
    rw [huU] at h1 ⊢
    exact ModularCurve.UVCrossingModel.mem_span_U_of_mul_mem_of_notMem π hπirr w hw (φ d) (φ x)
      (by rw [← hcπ, ← huU]; exact hd𝔓) h1

  have hUI₂ : uU ∈ I.map φ := by
    apply mem_map_colon_of_flat (A := O) (B := R) (𝔭 ^ w) d uU
    show φ d * uU ∈ (𝔭 ^ w).map φ
    rw [h𝔭w, hφd, sub_mul, mul_comm vV uU, hUV]
    refine Ideal.sub_mem _ (Ideal.pow_mem_pow hcπ𝔓 w) ?_

    have hx := hd
    rw [hdecomp] at hx
    have hx' := sup_pow_le_pow_sup 𝔓 (Ideal.span {vV}) (m + w + 2) hx
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hx'
    rw [← hpq, add_mul]
    refine Ideal.add_mem _ ?_ ?_
    · exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (by omega) hp)
    · rw [Ideal.mem_span_singleton] at hq
      obtain ⟨b, rfl⟩ := hq
      rw [mul_assoc, mul_comm b uU, ← mul_assoc, mul_comm vV uU, hUV, mul_comm]
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hcπ𝔓 w)

  have hU0 : uU ≠ 0 := by
    intro h0
    have e : βV uU = PowerSeries.X := hβV_U
    rw [h0, map_zero] at e
    exact PowerSeries.X_ne_zero e.symm
  obtain ⟨xn, hxnI, hxn⟩ : ∃ x ∈ I, φ x ∉ Ideal.span {uU} * maximalIdeal R := by
    by_contra hall
    push_neg at hall
    have hle : I.map φ ≤ Ideal.span {uU} * maximalIdeal R := by
      rw [Ideal.map_le_iff_le_comap]; intro x hx; exact hall x hx
    have := hle hUI₂
    rw [Ideal.mem_span_singleton_mul] at this
    obtain ⟨b, hb, hbU⟩ := this
    have h1b : IsUnit (1 - b) := by
      by_contra hnu
      have : (1 : R) - b ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      have : (1 : R) ∈ maximalIdeal R := by simpa using Ideal.add_mem _ this hb
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr this)
    apply hU0
    have : uU * (1 - b) = 0 := by rw [mul_sub, mul_one, hbU, sub_self]
    exact (h1b.mul_left_eq_zero).mp this
  obtain ⟨γ, hγ⟩ := Ideal.mem_span_singleton'.mp (h2a xn hxnI)
  have hγu : IsUnit γ := by
    by_contra hnu
    apply hxn
    rw [← hγ, mul_comm]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ((IsLocalRing.mem_maximalIdeal _).mpr hnu)

  have hUnzd : ∀ y : R, uU * y = 0 → y = 0 := by
    intro y hy
    obtain ⟨Ψ, hΨ0, hΨ1, hΨC, hΨker, -⟩ := exists_ringHom_killU W
    obtain ⟨G, rfl⟩ := mk_surjective (π ^ w) y
    have h1 : mk (π ^ w) (MvPowerSeries.X 0 * G) = 0 := by
      rw [map_mul]; exact hy
    rw [show mk (π ^ w) = Ideal.Quotient.mk (uvCrossingIdeal W (π ^ w)) from rfl, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton] at h1
    obtain ⟨H, hH⟩ := h1

    have h2 : Ψ H = 0 := by
      have := congrArg Ψ hH
      rw [map_mul, hΨ0, zero_mul, map_mul, map_sub, map_mul, hΨ0, zero_mul, hΨC, zero_sub, neg_mul,
        eq_comm, neg_eq_zero, mul_eq_zero] at this
      rcases this with h | h
      · exfalso
        apply pow_ne_zero w hπ0
        have := congrArg (PowerSeries.constantCoeff) h
        rwa [PowerSeries.constantCoeff_C, map_zero] at this
      · exact h
    obtain ⟨H', rfl⟩ := (hΨker H).mp h2
    have h3 : MvPowerSeries.X 0 * (G - (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C (π ^ w)) * H') = 0 := by
      rw [mul_sub, hH]; ring
    rcases mul_eq_zero.mp h3 with h | h
    · exfalso
      have := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) h
      rw [MvPowerSeries.coeff_X, if_pos rfl, MvPowerSeries.coeff_zero] at this
      exact one_ne_zero this
    · rw [sub_eq_zero] at h
      rw [h, show mk (π ^ w) = Ideal.Quotient.mk (uvCrossingIdeal W (π ^ w)) from rfl, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

  have hxnφ : φ xn = γ * uU := hγ.symm
  obtain ⟨γi, hγi⟩ := hγu.exists_left_inv
  have htw : t ^ w ∈ Ideal.span {xn} := by
    rw [← hmem, map_pow, hφt, ← hUV, Ideal.map_span, Set.image_singleton, hxnφ, Ideal.mem_span_singleton]
    exact ⟨γi * vV, by rw [show γ * uU * (γi * vV) = (γi * γ) * (uU * vV) by ring, hγi, one_mul]⟩
  obtain ⟨yn, hyn⟩ := Ideal.mem_span_singleton'.mp htw
  have hynφ : φ yn = γi * vV := by
    have h1 : φ yn * φ xn = uU * vV := by rw [← map_mul, hyn, map_pow, hφt, hUV]
    rw [hxnφ] at h1
    have : uU * (γ * φ yn - vV) = 0 := by
      rw [mul_sub, show uU * (γ * φ yn) = φ yn * (γ * uU) by ring, h1, sub_self]
    have h2 := hUnzd _ this
    rw [sub_eq_zero] at h2
    rw [← h2, ← mul_assoc, hγi, one_mul]
  have hγiu : IsUnit γi := isUnit_iff_exists_inv.mpr ⟨γ, hγi⟩

  have hspanR : Ideal.span {φ xn, φ yn, φ t} = maximalIdeal R := by
    rw [hmR]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · rw [hxnφ]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
      · rw [hynφ]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
      · rw [hφt]; exact Ideal.subset_span (by simp)
    · rw [Ideal.span_le]
      rintro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · rw [← hφt]; exact Ideal.subset_span (by simp)
      · have : uU = γi * φ xn := by rw [hxnφ, ← mul_assoc, hγi, one_mul]
        rw [this]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
      · have : vV = γ * φ yn := by
          rw [hynφ, ← mul_assoc, mul_comm γ γi, hγi, one_mul]
        rw [this]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  have hmO : maximalIdeal O = Ideal.span {xn, yn, t} := by
    rw [← hcm (maximalIdeal O), ← hcm (Ideal.span {xn, yn, t}), hmRφ, Ideal.map_span]
    congr 1
    rw [← hspanR]
    congr 1
    simp only [Set.image_insert_eq, Set.image_singleton]

  refine ⟨xn, yn, 1, γ, γi, isUnit_one, hγu, hγiu, hxnφ, hynφ, ?_, hmO⟩
  rw [mul_one, mul_comm, hyn]

end KFCD

theorem solution
    {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (w : ℕ) (hw : 1 ≤ w)
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (ι : AdicCompletion (maximalIdeal O) O ≃+* UVCrossingModel W (π ^ w))
    (t : O) (ht : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) t) = const (π ^ w) π)

    (𝔭₁ 𝔭₂ : Ideal O) [𝔭₁.IsPrime] [𝔭₂.IsPrime] (h₁₂ : 𝔭₁ ≠ 𝔭₂)
    (ht₁ : t ∈ 𝔭₁) (ht₂ : t ∈ 𝔭₂) (h₁ : 𝔭₁ ≠ maximalIdeal O) (h₂ : 𝔭₂ ≠ maximalIdeal O) :
    ∃ (xn yn u : O) (γ γ' : UVCrossingModel W (π ^ w)),
      IsUnit u ∧ IsUnit γ ∧ IsUnit γ' ∧
      ι (algebraMap O (AdicCompletion (maximalIdeal O) O) xn) = γ * U (π ^ w) ∧
      ι (algebraMap O (AdicCompletion (maximalIdeal O) O) yn) = γ' * V (π ^ w) ∧
      xn * yn = t ^ w * u ∧
      maximalIdeal O = Ideal.span {xn, yn, t} := by
  classical

  let SU : Ideal (UVCrossingModel W (π ^ w)) := Ideal.span {const (π ^ w) π, U (π ^ w)}
  let SV : Ideal (UVCrossingModel W (π ^ w)) := Ideal.span {const (π ^ w) π, V (π ^ w)}
  let φ : O → UVCrossingModel W (π ^ w) := fun x => ι (algebraMap O (AdicCompletion (maximalIdeal O) O) x)
  have hBM := ModularCurve.UVCrossingModel.mem_iff_ringEquiv_adicCompletion_mem_span_or_swap_of_ne
    π hπ w hw ι t ht 𝔭₁ 𝔭₂ h₁₂ ht₁ ht₂ h₁ h₂
  have hne : ∃ g : O, (g ∈ 𝔭₁ ∧ g ∉ 𝔭₂) ∨ (g ∈ 𝔭₂ ∧ g ∉ 𝔭₁) := by
    by_contra hall
    apply h₁₂
    ext g
    constructor
    · intro hg; by_contra h'; exact hall ⟨g, Or.inl ⟨hg, h'⟩⟩
    · intro hg; by_contra h'; exact hall ⟨g, Or.inr ⟨hg, h'⟩⟩
  have hsplit : (∃ f : O, φ f ∈ SU ∧ φ f ∉ SV) ∨ (∃ f : O, φ f ∈ SV ∧ φ f ∉ SU) := by
    obtain ⟨g, hg⟩ := hne
    rcases hBM with ⟨hA1, hA2⟩ | ⟨hB1, hB2⟩
    · rcases hg with ⟨hg1, hg2⟩ | ⟨hg2, hg1⟩
      · exact Or.inl ⟨g, (hA1 g).mp hg1, fun h => hg2 ((hA2 g).mpr h)⟩
      · exact Or.inr ⟨g, (hA2 g).mp hg2, fun h => hg1 ((hA1 g).mpr h)⟩
    · rcases hg with ⟨hg1, hg2⟩ | ⟨hg2, hg1⟩
      · exact Or.inr ⟨g, (hB1 g).mp hg1, fun h => hg2 ((hB2 g).mpr h)⟩
      · exact Or.inl ⟨g, (hB2 g).mp hg2, fun h => hg1 ((hB1 g).mpr h)⟩
  rcases hsplit with ⟨f, hfU, hfV⟩ | ⟨f, hfV, hfU⟩
  ·
    exact KFCD.core π hπ w hw ι t ht f hfU hfV
  ·
    let σ := crossingSwap (W := W) (π ^ w)
    have hσU : σ (U (π ^ w)) = V (π ^ w) := by
      show σ (UVCrossingModel.mk (π ^ w) (MvPowerSeries.X 0)) = UVCrossingModel.mk (π ^ w) (MvPowerSeries.X 1)
      rw [crossingSwap_mk, uvSwapEquiv_X_zero]
    have hσV : σ (V (π ^ w)) = U (π ^ w) := by
      show σ (UVCrossingModel.mk (π ^ w) (MvPowerSeries.X 1)) = UVCrossingModel.mk (π ^ w) (MvPowerSeries.X 0)
      rw [crossingSwap_mk, uvSwapEquiv_X_one]
    have hσc : ∀ a : W, σ (const (π ^ w) a) = const (π ^ w) a := fun a => by
      show σ (UVCrossingModel.mk (π ^ w) (MvPowerSeries.C a)) = UVCrossingModel.mk (π ^ w) (MvPowerSeries.C a)
      rw [crossingSwap_mk, uvSwapEquiv_C]
    have hσSV : SV.map σ.toRingHom = SU := by
      show (Ideal.span {const (π ^ w) π, V (π ^ w)}).map σ.toRingHom = Ideal.span {const (π ^ w) π, U (π ^ w)}
      rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
      show Ideal.span {σ (const (π ^ w) π), σ (V (π ^ w))} = _
      rw [hσc, hσV]
    have hσSU : SU.map σ.toRingHom = SV := by
      show (Ideal.span {const (π ^ w) π, U (π ^ w)}).map σ.toRingHom = Ideal.span {const (π ^ w) π, V (π ^ w)}
      rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
      show Ideal.span {σ (const (π ^ w) π), σ (U (π ^ w))} = _
      rw [hσc, hσU]
    let ι' : AdicCompletion (maximalIdeal O) O ≃+* UVCrossingModel W (π ^ w) := ι.trans σ
    have hι' : ∀ x, ι' x = σ (ι x) := fun _ => rfl
    have ht' : ι' (algebraMap O (AdicCompletion (maximalIdeal O) O) t) = const (π ^ w) π := by
      rw [hι', ht, hσc]
    have hfU' : ι' (algebraMap O (AdicCompletion (maximalIdeal O) O) f) ∈ Ideal.span {const (π ^ w) π, U (π ^ w)} := by
      rw [hι']
      have : σ (ι (algebraMap O _ f)) ∈ SV.map σ.toRingHom := Ideal.mem_map_of_mem _ hfV
      rwa [hσSV] at this
    have hfV' : ι' (algebraMap O (AdicCompletion (maximalIdeal O) O) f) ∉ Ideal.span {const (π ^ w) π, V (π ^ w)} := by
      rw [hι']
      intro hmem
      apply hfU
      have : ι (algebraMap O _ f) ∈ (SU.map σ.toRingHom).comap σ.toRingHom := by
        rw [hσSU]; exact hmem
      rwa [Ideal.comap_map_of_bijective σ.toRingHom (show Function.Bijective σ.toRingHom from σ.bijective)] at this
    obtain ⟨xn', yn', u, γ, γ', hu, hγ, hγ', hx', hy', hprod, hm⟩ := KFCD.core π hπ w hw ι' t ht' f hfU' hfV'
    rw [hι'] at hx' hy'

    have hsU : σ.symm (U (π ^ w)) = V (π ^ w) := by rw [← hσV, RingEquiv.symm_apply_apply]
    have hsV : σ.symm (V (π ^ w)) = U (π ^ w) := by rw [← hσU, RingEquiv.symm_apply_apply]
    have hx'' : ι (algebraMap O _ xn') = σ.symm γ * V (π ^ w) := by
      have := congrArg σ.symm hx'
      rw [RingEquiv.symm_apply_apply, map_mul, hsU] at this
      exact this
    have hy'' : ι (algebraMap O _ yn') = σ.symm γ' * U (π ^ w) := by
      have := congrArg σ.symm hy'
      rw [RingEquiv.symm_apply_apply, map_mul, hsV] at this
      exact this
    refine ⟨yn', xn', u, σ.symm γ', σ.symm γ, hu, hγ'.map σ.symm, hγ.map σ.symm, hy'', hx'', ?_, ?_⟩
    · rw [mul_comm]; exact hprod
    · rw [hm, Set.insert_comm]

end S_ModularCurve_UVCrossingModel_exists_mul_eq_pow_mul_and_maximalIdeal_eq_span_of_ringEquiv_adicCompletion_pow
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_mul_eq_pow_mul_and_maximalIdeal_eq_span_of_ringEquiv_adicCompletion_pow (solution)
