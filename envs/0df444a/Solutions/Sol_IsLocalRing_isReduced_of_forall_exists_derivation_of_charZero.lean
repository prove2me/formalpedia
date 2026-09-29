-- Prove2me | solution 1 for IsLocalRing.isReduced_of_forall_exists_derivation_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/31841614-3164-5993-849c-22578ce0294c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_isReduced_of_forall_exists_derivation_of_charZero

set_option autoImplicit false

open MvPolynomial

namespace FormalCartier

variable {k : Type} [Field k] {A : Type} [CommRing A] [Algebra k A]

theorem derivation_apply_mem_pow (D : Derivation k A A) (I : Ideal A) :
    ∀ (d : ℕ) (a : A), a ∈ I ^ (d + 1) → D a ∈ I ^ d := by
  intro d
  induction d with
  | zero => intro a _; simp
  | succ d ih =>
    intro a ha
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha (fun b hb c hc => ?_) (fun b c hb hc => ?_)
    · rw [Derivation.leibniz, pow_succ, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hb) ?_
      exact Submodule.mul_mem_mul_rev (ih b hb) hc
    · rw [map_add]; exact Ideal.add_mem _ hb hc

theorem isHomogeneous_pderiv {σ : Type} [DecidableEq σ] (F : MvPolynomial σ k) (d : ℕ) (hF : F.IsHomogeneous (d + 1))
    (i : σ) : (pderiv i F).IsHomogeneous d := by
  rw [F.as_sum, map_sum]
  refine IsHomogeneous.sum _ _ _ fun s hs => ?_
  rw [pderiv_monomial]
  by_cases hsi : s i = 0
  · rw [hsi, Nat.cast_zero, mul_zero, monomial_zero]; exact isHomogeneous_zero _ _ _
  · apply isHomogeneous_monomial
    have hdeg : Finsupp.weight (1 : σ → ℕ) s = d + 1 := hF (mem_support_iff.1 hs)
    have h2 : Finsupp.weight (1 : σ → ℕ) (s - Finsupp.single i 1) + 1 = d + 1 := by
      have := Finsupp.weight_sub_single_add (w := (1 : σ → ℕ)) hsi
      rw [hdeg] at this
      exact this
    rw [Finsupp.degree_eq_weight_one]
    exact Nat.add_right_cancel h2

theorem derivation_aeval {n : ℕ} (D : Derivation k A A) (x : Fin n → A) (F : MvPolynomial (Fin n) k) :
    D (aeval x F) = ∑ j, aeval x (pderiv j F) * D (x j) := by
  induction F using MvPolynomial.induction_on with
  | C c =>
    simp [pderiv_C]
  | add p q hp hq =>
    simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    rw [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hp]
    simp only [pderiv_mul, map_add, map_mul, aeval_X, add_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    · rw [Finset.sum_eq_single j]
      · simp [pderiv_X_self]
      · intro i _ hij
        simp [pderiv_X_of_ne (Ne.symm hij)]
      · simp

theorem aeval_mem_pow {n : ℕ} (x : Fin n → A) (I : Ideal A) (hx : ∀ j, x j ∈ I) (F : MvPolynomial (Fin n) k) (d : ℕ)
    (hF : F.IsHomogeneous d) : aeval x F ∈ I ^ d := by
  rw [F.as_sum, map_sum]
  refine Ideal.sum_mem _ fun s hs => ?_
  rw [aeval_monomial]
  refine Ideal.mul_mem_left _ _ ?_
  have hdeg : s.degree = d := by
    rw [Finsupp.degree_eq_weight_one]; exact hF (mem_support_iff.1 hs)
  have key : ∀ t : Finset (Fin n), ∏ a ∈ t, x a ^ s a ∈ I ^ (∑ a ∈ t, s a) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t hat ih =>
      rw [Finset.prod_insert hat, Finset.sum_insert hat, pow_add]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (hx a) _) ih
  have hd : d = ∑ a ∈ s.support, s a := by rw [← hdeg]; rfl
  rw [Finsupp.prod, hd]
  exact key _

open IsLocalRing in

theorem exists_coords [IsLocalRing A] [IsNoetherianRing A]
    (hk : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ maximalIdeal A)
    (hder : ∀ φ : A →ₗ[k] k, (∀ a ∈ (maximalIdeal A) ^ 2, φ a = 0) → (∀ c : k, φ (algebraMap k A c) = 0) →
      ∃ D : Derivation k A A, ∀ a : A, D a - algebraMap k A (φ a) ∈ maximalIdeal A) :
    ∃ (n : ℕ) (x : Fin n → A) (D : Fin n → Derivation k A A),
      (∀ j, x j ∈ maximalIdeal A) ∧ Ideal.span (Set.range x) = maximalIdeal A ∧
      ∀ i j, D i (x j) - (if i = j then 1 else 0) ∈ maximalIdeal A := by
  classical
  set 𝔪 := maximalIdeal A with h𝔪

  have hunit : ∀ c : k, algebraMap k A c ∈ 𝔪 → c = 0 := by
    intro c hc
    by_contra h
    have h1 : algebraMap k A (c⁻¹ * c) ∈ 𝔪 := by rw [map_mul]; exact 𝔪.mul_mem_left _ hc
    rw [inv_mul_cancel₀ h, map_one] at h1
    exact (Ideal.ne_top_iff_one _).1 (maximalIdeal.isMaximal A).ne_top h1

  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian 𝔪 : 𝔪.FG)

  let K0 : Submodule k A := LinearMap.range (Algebra.linearMap k A) ⊔ (𝔪 ^ 2).restrictScalars k
  let π : A →ₗ[k] (A ⧸ K0) := K0.mkQ
  have hπ0 : ∀ a, a ∈ 𝔪 ^ 2 → π a = 0 := fun a ha =>
    (Submodule.Quotient.mk_eq_zero K0).2 (Submodule.mem_sup_right ha)
  have hπc : ∀ c : k, π (algebraMap k A c) = 0 := fun c =>
    (Submodule.Quotient.mk_eq_zero K0).2 (Submodule.mem_sup_left ⟨c, rfl⟩)
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' k (fun s : S => π s.1)
  haveI : Fintype κ := Fintype.ofInjective a ha

  let n := Fintype.card κ
  let e : κ ≃ Fin n := Fintype.equivFin κ
  let x : Fin n → A := fun j => (a (e.symm j)).1
  have hxS : ∀ j, x j ∈ (S : Set A) := fun j => (a (e.symm j)).2
  have hx𝔪 : ∀ j, x j ∈ 𝔪 := fun j => hS ▸ Ideal.subset_span (hxS j)

  let B := Module.Basis.span hli
  have hφ : ∀ i : Fin n, ∃ φ : A →ₗ[k] k, (∀ b ∈ 𝔪 ^ 2, φ b = 0) ∧ (∀ c : k, φ (algebraMap k A c) = 0) ∧
      ∀ j, φ (x j) = if i = j then 1 else 0 := by
    intro i
    obtain ⟨g, hg⟩ := LinearMap.exists_extend (B.coord (e.symm i))
    refine ⟨g ∘ₗ π, fun b hb => by simp [hπ0 b hb], fun c => by simp [hπc c], fun j => ?_⟩
    have hmem : π (x j) ∈ Submodule.span k (Set.range ((fun s : S => π s.1) ∘ a)) :=
      Submodule.subset_span ⟨e.symm j, rfl⟩
    have h1 : g (π (x j)) = B.coord (e.symm i) ⟨π (x j), hmem⟩ := by
      rw [← hg]; rfl
    rw [LinearMap.comp_apply, h1]
    have h2 : (⟨π (x j), hmem⟩ : Submodule.span k (Set.range ((fun s : S => π s.1) ∘ a))) = B (e.symm j) := by
      rw [Module.Basis.span_apply]; rfl
    rw [h2, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    simp [e.symm.injective.eq_iff, eq_comm]
  choose φ hφ0 hφc hφx using hφ
  have hD : ∀ i, ∃ D : Derivation k A A, ∀ b, D b - algebraMap k A (φ i b) ∈ 𝔪 :=
    fun i => hder (φ i) (hφ0 i) (hφc i)
  choose D hD using hD
  refine ⟨n, x, D, hx𝔪, ?_, fun i j => by simpa [hφx, apply_ite] using hD i (x j)⟩
  apply le_antisymm (Ideal.span_le.2 (Set.range_subset_iff.2 hx𝔪))
  have hfg : (𝔪 : Submodule A A).FG := IsNoetherian.noetherian _
  refine Submodule.le_of_le_smul_of_le_jacobson_bot hfg (maximalIdeal_le_jacobson ⊥) ?_
  have key : Ideal.span (S : Set A) ≤ Ideal.span (Set.range x) ⊔ 𝔪 • 𝔪 := by
    refine Ideal.span_le.2 fun s hs => ?_

    have hmem : π s ∈ Submodule.span k (Set.range ((fun s : S => π s.1) ∘ a)) := by
      rw [hspan]; exact Submodule.subset_span ⟨⟨s, hs⟩, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hmem

    set y := s - ∑ i, algebraMap k A (c i) * (a i).1 with hy
    have hys : s = (∑ i, algebraMap k A (c i) * (a i).1) + y := by rw [hy]; abel
    have hπy : π y = 0 := by
      simp only [hy, map_sub, map_sum]
      rw [sub_eq_zero, ← hc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Algebra.smul_def, LinearMap.map_smul]; rfl
    have hyK : y ∈ K0 := (Submodule.Quotient.mk_eq_zero K0).1 hπy
    obtain ⟨u, hu, q, hq, huq⟩ := Submodule.mem_sup.1 hyK
    obtain ⟨c₀, rfl⟩ := LinearMap.mem_range.1 hu
    have hq' : q ∈ 𝔪 ^ 2 := hq
    have hy𝔪 : y ∈ 𝔪 := by
      rw [hy]
      refine Ideal.sub_mem _ (hS ▸ Ideal.subset_span hs) (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ?_)
      exact hS ▸ Ideal.subset_span (a i).2
    have hc₀ : c₀ = 0 := by
      apply hunit
      have : (Algebra.linearMap k A) c₀ = y - q := by rw [← huq]; abel
      rw [Algebra.linearMap_apply] at this
      rw [this]
      exact Ideal.sub_mem _ hy𝔪 (Ideal.pow_le_self two_ne_zero hq')
    have hyq : y = q := by rw [← huq, hc₀, map_zero, zero_add]
    rw [hys]
    refine Submodule.add_mem_sup ?_ ?_
    · refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range.2 ⟨e i, ?_⟩))
      simp [x]
    · rw [hyq, Ideal.smul_eq_mul, ← pow_two]; exact hq'
  exact (le_of_eq hS.symm).trans key

open IsLocalRing in

theorem form_eq_zero [IsLocalRing A] [CharZero k] {n : ℕ} (x : Fin n → A) (D : Fin n → Derivation k A A)
    (hx : ∀ j, x j ∈ maximalIdeal A) (hD : ∀ i j, D i (x j) - (if i = j then 1 else 0) ∈ maximalIdeal A)
    (hunit : ∀ c : k, algebraMap k A c ∈ maximalIdeal A → c = 0) :
    ∀ (d : ℕ) (F : MvPolynomial (Fin n) k), F.IsHomogeneous d → aeval x F ∈ maximalIdeal A ^ (d + 1) → F = 0 := by
  classical
  intro d
  induction d with
  | zero =>
    intro F hF hFm

    have hF' : F = C (F.coeff 0) := by
      rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hF; exact hF
    rw [hF'] at hFm ⊢
    rw [aeval_C, zero_add, pow_one] at hFm
    rw [hunit _ hFm, C_0]
  | succ d ih =>
    intro F hF hFm

    have hpd : ∀ i, pderiv i F = 0 := by
      intro i
      refine ih _ (isHomogeneous_pderiv F d hF i) ?_

      have h1 : D i (aeval x F) ∈ maximalIdeal A ^ (d + 1) := derivation_apply_mem_pow (D i) _ _ _ hFm
      rw [derivation_aeval] at h1
      have h2 : ∀ j, aeval x (pderiv j F) * (D i (x j) - (if i = j then 1 else 0)) ∈ maximalIdeal A ^ (d + 1) := by
        intro j
        rw [pow_succ]
        exact Ideal.mul_mem_mul (aeval_mem_pow x _ hx _ _ (isHomogeneous_pderiv F d hF j)) (hD i j)
      have h3 : ∑ j, aeval x (pderiv j F) * D i (x j) =
          ∑ j, aeval x (pderiv j F) * (D i (x j) - (if i = j then 1 else 0)) + aeval x (pderiv i F) := by
        have hs : ∑ j, aeval x (pderiv j F) * (if i = j then 1 else 0 : A) = aeval x (pderiv i F) := by
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji; simp [Ne.symm hji]
          · simp
        simp only [mul_sub, Finset.sum_sub_distrib, hs, sub_add_cancel]
      rw [h3] at h1
      have h4 : ∑ j, aeval x (pderiv j F) * (D i (x j) - (if i = j then 1 else 0)) ∈ maximalIdeal A ^ (d + 1) :=
        Ideal.sum_mem _ fun j _ => h2 j
      have := Ideal.sub_mem _ h1 h4
      rwa [add_sub_cancel_left] at this

    have hE := hF.sum_X_mul_pderiv
    simp only [hpd, mul_zero, Finset.sum_const_zero] at hE

    have : ((d + 1 : ℕ) : k) • F = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact hE.symm
    exact (smul_eq_zero.1 this).resolve_left (Nat.cast_ne_zero.2 (Nat.succ_ne_zero d))

open IsLocalRing in
theorem algebraMap_mem_imp_eq_zero [IsLocalRing A] (c : k) (hc : algebraMap k A c ∈ maximalIdeal A) : c = 0 := by
  by_contra h
  have h1 : algebraMap k A (c⁻¹ * c) ∈ maximalIdeal A := by rw [map_mul]; exact (maximalIdeal A).mul_mem_left _ hc
  rw [inv_mul_cancel₀ h, map_one] at h1
  exact (Ideal.ne_top_iff_one _).1 (maximalIdeal.isMaximal A).ne_top h1

open IsLocalRing in

theorem exists_linear_form [IsLocalRing A] {n : ℕ} (x : Fin n → A) (hx : ∀ j, x j ∈ maximalIdeal A)
    (hk : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ maximalIdeal A)
    (c : A) (hc : c ∈ Ideal.span (Set.range x)) :
    ∃ G : MvPolynomial (Fin n) k, G.IsHomogeneous 1 ∧ c - aeval x G ∈ maximalIdeal A ^ 2 := by
  induction hc using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact ⟨X j, isHomogeneous_X _ _, by simp⟩
  | zero => exact ⟨0, isHomogeneous_zero _ _ _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨G₁, hG₁, h₁⟩ := hy
    obtain ⟨G₂, hG₂, h₂⟩ := hz
    refine ⟨G₁ + G₂, hG₁.add hG₂, ?_⟩
    have : y + z - aeval x (G₁ + G₂) = (y - aeval x G₁) + (z - aeval x G₂) := by rw [map_add]; ring
    rw [this]; exact Ideal.add_mem _ h₁ h₂
  | smul r y _ hy =>
    obtain ⟨G, hG, h⟩ := hy
    obtain ⟨r₀, hr₀⟩ := hk r
    refine ⟨C r₀ * G, by simpa using hG.C_mul r₀, ?_⟩
    have e : r • y - aeval x (C r₀ * G) = r * (y - aeval x G) + (r - algebraMap k A r₀) * aeval x G := by
      rw [map_mul, aeval_C, smul_eq_mul]; ring
    rw [e, pow_two]
    refine Ideal.add_mem _ ?_ (Ideal.mul_mem_mul hr₀ ?_)
    · rw [← pow_two]; exact Ideal.mul_mem_left _ _ h
    · simpa using aeval_mem_pow x _ hx G 1 hG

open IsLocalRing in

theorem exists_form [IsLocalRing A] {n : ℕ} (x : Fin n → A) (hx : ∀ j, x j ∈ maximalIdeal A)
    (hspan : Ideal.span (Set.range x) = maximalIdeal A)
    (hk : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ maximalIdeal A) :
    ∀ (d : ℕ) (a : A), a ∈ maximalIdeal A ^ d →
      ∃ F : MvPolynomial (Fin n) k, F.IsHomogeneous d ∧ a - aeval x F ∈ maximalIdeal A ^ (d + 1) := by
  intro d
  induction d with
  | zero =>
    intro a _
    obtain ⟨c, hc⟩ := hk a
    exact ⟨C c, isHomogeneous_C _ _, by simpa [aeval_C] using hc⟩
  | succ d ih =>
    intro a ha
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha (fun b hb c hc => ?_) (fun b c hb hc => ?_)
    · obtain ⟨F, hF, hFb⟩ := ih b hb
      obtain ⟨G, hG, hGc⟩ := exists_linear_form x hx hk c (hspan.symm ▸ hc)
      refine ⟨F * G, hF.mul hG, ?_⟩
      have e : b * c - aeval x (F * G) = (b - aeval x F) * c + aeval x F * (c - aeval x G) := by
        rw [map_mul]; ring
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_succ]; exact Ideal.mul_mem_mul hFb hc
      · rw [show d + 1 + 1 = d + 2 from rfl, pow_add]
        exact Ideal.mul_mem_mul (aeval_mem_pow x _ hx F d hF) hGc
    · obtain ⟨F₁, hF₁, h₁⟩ := hb
      obtain ⟨F₂, hF₂, h₂⟩ := hc
      refine ⟨F₁ + F₂, hF₁.add hF₂, ?_⟩
      have e : b + c - aeval x (F₁ + F₂) = (b - aeval x F₁) + (c - aeval x F₂) := by rw [map_add]; ring
      rw [e]; exact Ideal.add_mem _ h₁ h₂

end FormalCartier

open IsLocalRing FormalCartier MvPolynomial in
theorem solution
    (k : Type) [Field k] [CharZero k] (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A]
    (hk : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ IsLocalRing.maximalIdeal A)
    (hder : ∀ φ : A →ₗ[k] k, (∀ a ∈ (IsLocalRing.maximalIdeal A) ^ 2, φ a = 0) → (∀ c : k, φ (algebraMap k A c) = 0) →
      ∃ D : Derivation k A A, ∀ a : A, D a - algebraMap k A (φ a) ∈ IsLocalRing.maximalIdeal A) :
    IsReduced A := by
  classical
  obtain ⟨n, x, D, hx, hspan, hD⟩ := exists_coords (k := k) (A := A) hk hder
  have hunit : ∀ c : k, algebraMap k A c ∈ maximalIdeal A → c = 0 := fun c hc => algebraMap_mem_imp_eq_zero c hc
  refine ⟨fun a ha => ?_⟩
  by_contra hne
  obtain ⟨r, hr⟩ := ha

  have hK : ⨅ i : ℕ, maximalIdeal A ^ i = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal A).ne_top
  have hex : ∃ d, a ∉ maximalIdeal A ^ (d + 1) := by
    by_contra h
    push_neg at h
    have : a ∈ ⨅ i : ℕ, maximalIdeal A ^ i := by
      refine Ideal.mem_iInf.2 fun i => ?_
      cases i with
      | zero => simp
      | succ i => exact h i
    rw [hK] at this
    exact hne this
  let d := Nat.find hex
  have hd1 : a ∉ maximalIdeal A ^ (d + 1) := Nat.find_spec hex
  have hd0 : a ∈ maximalIdeal A ^ d := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · rw [h0]; simp
    · have := Nat.find_min hex (m := d - 1) (by omega)
      push_neg at this
      rwa [Nat.sub_add_cancel hpos] at this
  obtain ⟨F, hF, hFa⟩ := exists_form x hx hspan hk d a hd0
  have hF0 : F ≠ 0 := by
    intro h; apply hd1; rw [h, map_zero, sub_zero] at hFa; exact hFa

  have hpow : ∀ r : ℕ, a ^ r - aeval x (F ^ r) ∈ maximalIdeal A ^ (d * r + 1) := by
    intro r
    induction r with
    | zero => simp
    | succ r ihr =>
      have e : a ^ (r + 1) - aeval x (F ^ (r + 1)) = a * (a ^ r - aeval x (F ^ r)) + (a - aeval x F) * aeval x (F ^ r) := by
        simp only [map_pow, map_mul, pow_succ]; ring
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · have := Ideal.mul_mem_mul hd0 ihr
        rwa [← pow_add, show d + (d * r + 1) = d * (r + 1) + 1 by ring] at this
      · have := Ideal.mul_mem_mul hFa (aeval_mem_pow x _ hx (F ^ r) (d * r) (hF.pow r))
        rwa [← pow_add, show d + 1 + d * r = d * (r + 1) + 1 by ring] at this
  have hz : aeval x (F ^ r) ∈ maximalIdeal A ^ (d * r + 1) := by
    have := hpow r
    rw [hr, zero_sub] at this
    exact (Ideal.neg_mem_iff _).1 this
  have hFr : F ^ r = 0 := form_eq_zero x D hx hD hunit (d * r) (F ^ r) (hF.pow r) hz
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hr
    exact one_ne_zero hr
  exact hF0 (pow_eq_zero_iff hr0 |>.1 hFr)

end S_IsLocalRing_isReduced_of_forall_exists_derivation_of_charZero
end P2MW
export P2MW.S_IsLocalRing_isReduced_of_forall_exists_derivation_of_charZero (solution)
