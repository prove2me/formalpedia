-- Prove2me | solution 1 for IsDiscreteValuationRing.exists_ringEquiv_forall_apply_eq_comp_of_forall_exists_sub_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/63255800-18f6-5340-b3cb-fb817eab5fea

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_exists_ringEquiv_forall_apply_eq_comp_of_forall_exists_sub_mem_maximalIdeal

set_option autoImplicit false
set_option maxHeartbeats 3200000

open IsLocalRing

namespace T1Aux

theorem mem_pow_iff
    (A W : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    (σ : A →+* W) (hσ : maximalIdeal W = Ideal.span {σ ϖ})
    (x : A) (m : ℕ) : σ x ∈ maximalIdeal W ^ m ↔ x ∈ maximalIdeal A ^ m := by
  classical
  rw [hϖ, hσ, Ideal.span_singleton_pow, Ideal.span_singleton_pow, Ideal.mem_span_singleton',
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩
    by_cases hx : x = 0
    · exact ⟨0, by rw [hx, zero_mul]⟩
    have hϖ0 : ϖ ≠ 0 := by
      intro h0
      apply IsDiscreteValuationRing.not_a_field A
      rw [hϖ, h0, Ideal.span_singleton_eq_bot]
    have hirr : Irreducible ϖ := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal ϖ hϖ0 hϖ
    obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx hirr

    by_cases hkm : m ≤ k
    · refine ⟨ϖ ^ (k - m) * (u⁻¹ : Aˣ), ?_⟩
      calc ϖ ^ (k - m) * ((u⁻¹ : Aˣ) : A) * ϖ ^ m = ϖ ^ (k - m + m) * ((u⁻¹ : Aˣ) : A) := by ring
        _ = ϖ ^ k * ((u⁻¹ : Aˣ) : A) := by rw [Nat.sub_add_cancel hkm]
        _ = x * u * ((u⁻¹ : Aˣ) : A) := by rw [hu]
        _ = x := by rw [mul_assoc, Units.mul_inv, mul_one]
    · exfalso
      have hlt : k < m := Nat.lt_of_not_le hkm
      have hσϖ0 : σ ϖ ≠ 0 := by
        intro h0
        apply IsDiscreteValuationRing.not_a_field W
        rw [hσ, h0, Ideal.span_singleton_eq_bot]

      have h1 : σ ϖ ^ k = c * σ ϖ ^ m * σ u := by
        rw [← map_pow, ← hu, map_mul, ← hc]
      have hpow : σ ϖ ^ m = σ ϖ ^ k * σ ϖ ^ (m - k) := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le]
      have h2 : σ ϖ ^ k * (1 - c * σ ϖ ^ (m - k) * σ u) = 0 := by
        have : c * σ ϖ ^ m * σ u = σ ϖ ^ k * (c * σ ϖ ^ (m - k) * σ u) := by
          rw [hpow]; ring
        rw [mul_sub, mul_one, ← this, ← h1, sub_self]
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact pow_ne_zero k hσϖ0 h3
      · have hmem : c * σ ϖ ^ (m - k) * σ u ∈ maximalIdeal W := by
          rw [hσ]
          refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ?_)
          exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ (by omega)
        have heq : (1 : W) = c * σ ϖ ^ (m - k) * σ u := sub_eq_zero.mp h3
        have h1mem : (1 : W) ∈ maximalIdeal W := by rw [heq]; exact hmem
        exact (maximalIdeal.isMaximal W).ne_top ((Ideal.eq_top_iff_one _).mpr h1mem)
  · rintro ⟨c, rfl⟩
    exact ⟨σ c, by rw [map_mul, map_pow]⟩

theorem dense
    (A W : Type) [CommRing A] [CommRing W] [IsLocalRing W]
    (ϖ : A) (σ : A →+* W) (hσ : maximalIdeal W = Ideal.span {σ ϖ})
    (hres : ∀ w : W, ∃ a : A, w - σ a ∈ maximalIdeal W) :
    ∀ (w : W) (m : ℕ), ∃ a : A, w - σ a ∈ maximalIdeal W ^ m := by
  intro w m
  induction m generalizing w with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨a₀, ha₀⟩ := hres w
    rw [hσ, Ideal.mem_span_singleton'] at ha₀
    obtain ⟨w', hw'⟩ := ha₀
    obtain ⟨a', ha'⟩ := ih w'
    refine ⟨a₀ + ϖ * a', ?_⟩
    have : w - σ (a₀ + ϖ * a') = (w' - σ a') * σ ϖ := by
      rw [map_add, map_mul]; linear_combination (-1 : W) * hw'
    rw [this, pow_succ]
    exact Ideal.mul_mem_mul ha' (hσ ▸ Ideal.mem_span_singleton_self _)

theorem dir
    (A W₀ W : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    (σ₀ : A →+* W₀) (hσ₀ : maximalIdeal W₀ = Ideal.span {σ₀ ϖ})
    (hres₀ : ∀ w : W₀, ∃ a : A, w - σ₀ a ∈ maximalIdeal W₀)
    (σ : A →+* W) (hσ : maximalIdeal W = Ideal.span {σ ϖ}) :
    ∃ φ : W₀ →+* W, (∀ a : A, φ (σ₀ a) = σ a) ∧
      ∀ (w : W₀) (a : ℕ → A), (∀ m, w - σ₀ (a m) ∈ maximalIdeal W₀ ^ m) →
        ∀ m, φ w - σ (a m) ∈ maximalIdeal W ^ m := by
  classical
  have hdense := dense A W₀ ϖ σ₀ hσ₀ hres₀

  have htrans : ∀ (x y : A) (m : ℕ), σ₀ x - σ₀ y ∈ maximalIdeal W₀ ^ m → σ x - σ y ∈ maximalIdeal W ^ m := by
    intro x y m h
    rw [← map_sub] at h ⊢
    exact (mem_pow_iff A W ϖ hϖ σ hσ _ m).mpr ((mem_pow_iff A W₀ ϖ hϖ σ₀ hσ₀ _ m).mp h)

  choose apx hapx using hdense

  have hcauchy : ∀ (w : W₀) {m n : ℕ}, m ≤ n →
      σ (apx w m) ≡ σ (apx w n) [SMOD (maximalIdeal W ^ m • ⊤ : Submodule W W)] := by
    intro w m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    apply htrans
    have h1 := hapx w m
    have h2 : w - σ₀ (apx w n) ∈ maximalIdeal W₀ ^ m := Ideal.pow_le_pow_right hmn (hapx w n)
    have := Ideal.sub_mem _ h2 h1
    rwa [sub_sub_sub_cancel_left] at this
  have hlim : ∀ w : W₀, ∃ L : W, ∀ m, σ (apx w m) ≡ L [SMOD (maximalIdeal W ^ m • ⊤ : Submodule W W)] :=
    fun w => IsPrecomplete.prec' (fun m => σ (apx w m)) (hcauchy w)
  choose φf hφf using hlim
  have hφf' : ∀ w m, φf w - σ (apx w m) ∈ maximalIdeal W ^ m := by
    intro w m
    have := (hφf w m).symm
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this

  have hchar : ∀ (w : W₀) (a : ℕ → A), (∀ m, w - σ₀ (a m) ∈ maximalIdeal W₀ ^ m) →
      ∀ m, φf w - σ (a m) ∈ maximalIdeal W ^ m := by
    intro w a ha m
    have h1 : σ (apx w m) - σ (a m) ∈ maximalIdeal W ^ m := by
      apply htrans
      have := Ideal.sub_mem _ (ha m) (hapx w m)
      rwa [sub_sub_sub_cancel_left] at this
    have := Ideal.add_mem _ (hφf' w m) h1
    rwa [sub_add_sub_cancel] at this

  have huniq : ∀ (L L' : W) (a : ℕ → A), (∀ m, L - σ (a m) ∈ maximalIdeal W ^ m) →
      (∀ m, L' - σ (a m) ∈ maximalIdeal W ^ m) → L = L' := by
    intro L L' a hL hL'
    rw [← sub_eq_zero]
    refine IsHausdorff.haus' (I := maximalIdeal W) (L - L') fun m => ?_
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
    have := Ideal.sub_mem _ (hL m) (hL' m)
    rwa [sub_sub_sub_cancel_right] at this

  refine ⟨{ toFun := φf, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_, ?_⟩
  · apply huniq _ _ (fun _ => 1) (hchar 1 (fun _ => 1) (fun m => by simp))
    intro m; simp
  · intro x y
    apply huniq _ _ (fun m => apx x m * apx y m) (hchar (x * y) _ ?_)
    · intro m
      have : φf x * φf y - σ (apx x m * apx y m) =
          φf x * (φf y - σ (apx y m)) + (φf x - σ (apx x m)) * σ (apx y m) := by rw [map_mul]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hφf' y m)) (Ideal.mul_mem_right _ _ (hφf' x m))
    · intro m
      have : x * y - σ₀ (apx x m * apx y m) =
          x * (y - σ₀ (apx y m)) + (x - σ₀ (apx x m)) * σ₀ (apx y m) := by rw [map_mul]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hapx y m)) (Ideal.mul_mem_right _ _ (hapx x m))
  · apply huniq _ _ (fun _ => 0) (hchar 0 (fun _ => 0) (fun m => by simp))
    intro m; simp
  · intro x y
    apply huniq _ _ (fun m => apx x m + apx y m) (hchar (x + y) _ ?_)
    · intro m
      have : φf x + φf y - σ (apx x m + apx y m) = (φf x - σ (apx x m)) + (φf y - σ (apx y m)) := by
        rw [map_add]; ring
      rw [this]; exact Ideal.add_mem _ (hφf' x m) (hφf' y m)
    · intro m
      have : x + y - σ₀ (apx x m + apx y m) = (x - σ₀ (apx x m)) + (y - σ₀ (apx y m)) := by
        rw [map_add]; ring
      rw [this]; exact Ideal.add_mem _ (hapx x m) (hapx y m)
  · intro a
    show φf (σ₀ a) = σ a
    apply huniq _ _ (fun _ => a) (hchar (σ₀ a) (fun _ => a) (fun m => by simp))
    intro m; simp
  · intro w a ha m
    exact hchar w a ha m

end T1Aux

theorem solution
    (A W₀ W S : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀] [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    [CommRing S] (I : Ideal S) [IsHausdorff I S]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (σ₀ : A →+* W₀) (hσ₀ : IsLocalRing.maximalIdeal W₀ = Ideal.span {σ₀ ϖ})
    (hres₀ : ∀ w : W₀, ∃ a : A, w - σ₀ a ∈ IsLocalRing.maximalIdeal W₀)
    (σ : A →+* W) (hσ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
    (hres : ∀ w : W, ∃ a : A, w - σ a ∈ IsLocalRing.maximalIdeal W)
    (C₀ : W₀ →+* S) (C : W →+* S)
    (hC₀ : ∀ w ∈ IsLocalRing.maximalIdeal W₀, C₀ w ∈ I) (hC : ∀ w ∈ IsLocalRing.maximalIdeal W, C w ∈ I)
    (h : ∀ a : A, C₀ (σ₀ a) = C (σ a)) :
    ∃ βW : W₀ ≃+* W, (∀ w : W₀, C₀ w = C (βW w)) ∧ (∀ a : A, βW (σ₀ a) = σ a) := by
  classical
  obtain ⟨φ, hφσ, hφchar⟩ := T1Aux.dir A W₀ W ϖ hϖ σ₀ hσ₀ hres₀ σ hσ
  obtain ⟨ψ, hψσ, hψchar⟩ := T1Aux.dir A W W₀ ϖ hϖ σ hσ hres σ₀ hσ₀
  have hd₀ := T1Aux.dense A W₀ ϖ σ₀ hσ₀ hres₀
  have hd := T1Aux.dense A W ϖ σ hσ hres

  have huniq₀ : ∀ (L L' : W₀) (a : ℕ → A), (∀ m, L - σ₀ (a m) ∈ maximalIdeal W₀ ^ m) →
      (∀ m, L' - σ₀ (a m) ∈ maximalIdeal W₀ ^ m) → L = L' := by
    intro L L' a hL hL'
    rw [← sub_eq_zero]
    refine IsHausdorff.haus' (I := maximalIdeal W₀) (L - L') fun m => ?_
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
    have := Ideal.sub_mem _ (hL m) (hL' m)
    rwa [sub_sub_sub_cancel_right] at this
  have huniq : ∀ (L L' : W) (a : ℕ → A), (∀ m, L - σ (a m) ∈ maximalIdeal W ^ m) →
      (∀ m, L' - σ (a m) ∈ maximalIdeal W ^ m) → L = L' := by
    intro L L' a hL hL'
    rw [← sub_eq_zero]
    refine IsHausdorff.haus' (I := maximalIdeal W) (L - L') fun m => ?_
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
    have := Ideal.sub_mem _ (hL m) (hL' m)
    rwa [sub_sub_sub_cancel_right] at this

  have h1 : ∀ w : W₀, ψ (φ w) = w := by
    intro w
    choose a ha using hd₀ w
    exact huniq₀ _ _ a (hψchar (φ w) a (hφchar w a ha)) ha
  have h2 : ∀ w : W, φ (ψ w) = w := by
    intro w
    choose a ha using hd w
    exact huniq _ _ a (hφchar (ψ w) a (hψchar w a ha)) ha
  let βW : W₀ ≃+* W := RingEquiv.ofRingHom φ ψ (RingHom.ext h2) (RingHom.ext h1)
  refine ⟨βW, ?_, hφσ⟩
  intro w
  show C₀ w = C (φ w)
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := I) (C₀ w - C (φ w)) fun m => ?_
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
  choose a ha using hd₀ w
  have hC₀m : Ideal.map C₀ (maximalIdeal W₀ ^ m) ≤ I ^ m := by
    rw [Ideal.map_pow]; exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr fun y hy => hC₀ y hy) m
  have hCm : Ideal.map C (maximalIdeal W ^ m) ≤ I ^ m := by
    rw [Ideal.map_pow]; exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr fun y hy => hC y hy) m
  have e1 : C₀ w - C₀ (σ₀ (a m)) ∈ I ^ m := by
    rw [← map_sub]; exact hC₀m (Ideal.mem_map_of_mem _ (ha m))
  have e2 : C (φ w) - C (σ (a m)) ∈ I ^ m := by
    rw [← map_sub]; exact hCm (Ideal.mem_map_of_mem _ (hφchar w a ha m))
  have := Ideal.sub_mem _ e1 e2
  rwa [h (a m), sub_sub_sub_cancel_right] at this

end S_IsDiscreteValuationRing_exists_ringEquiv_forall_apply_eq_comp_of_forall_exists_sub_mem_maximalIdeal
end P2MW
export P2MW.S_IsDiscreteValuationRing_exists_ringEquiv_forall_apply_eq_comp_of_forall_exists_sub_mem_maximalIdeal (solution)
