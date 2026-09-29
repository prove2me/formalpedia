-- Prove2me | solution 1 for LinearMap.exists_span_eq_top_forall_exists_bijective_and_apply_eq_of_comp_eq_smul_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/90a56e4b-5a70-523f-bc14-320b871ae645

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_exists_span_eq_top_forall_exists_bijective_and_apply_eq_of_comp_eq_smul_comp

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v w

namespace SvNSol

open Finset

section Ortho

variable {R : Type u} [CommRing R]
  {H : Type v} [AddCommGroup H] [Fintype H]
  {H' : Type w} [AddCommGroup H'] [Fintype H']
  (e : H → H' → Rˣ)
  (he₁ : ∀ (h₁ h₂ : H) (χ : H'), e (h₁ + h₂) χ = e h₁ χ * e h₂ χ)
  (he₂ : ∀ (h : H) (χ₁ χ₂ : H'), e h (χ₁ + χ₂) = e h χ₁ * e h χ₂)

include he₁ in
theorem e_zero_left (χ : H') : e 0 χ = 1 := by
  have h := he₁ 0 0 χ
  rw [add_zero] at h
  have : e 0 χ * e 0 χ = e 0 χ * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel this

include he₂ in
theorem e_zero_right (h : H) : e h 0 = 1 := by
  have hh := he₂ h 0 0
  rw [add_zero] at hh
  have : e h 0 * e h 0 = e h 0 * 1 := by rw [mul_one]; exact hh.symm
  exact mul_left_cancel this

include he₁ in
theorem e_neg_left (h : H) (χ : H') : e (-h) χ = (e h χ)⁻¹ := by
  have hh := he₁ (-h) h χ
  rw [neg_add_cancel, e_zero_left e he₁] at hh
  exact eq_inv_of_mul_eq_one_left hh.symm

include he₂ in
theorem e_neg_right (h : H) (χ : H') : e h (-χ) = (e h χ)⁻¹ := by
  have hh := he₂ h (-χ) χ
  rw [neg_add_cancel, e_zero_right e he₂] at hh
  exact eq_inv_of_mul_eq_one_left hh.symm

include he₂ in

theorem sum_e_eq_zero (h : H) (hu : ∃ χ : H', IsUnit ((e h χ : R) - 1)) :
    ∑ χ : H', (e h χ : R) = 0 := by
  obtain ⟨χ₀, hχ₀⟩ := hu
  have hS : (∑ χ : H', (e h χ : R)) * (e h χ₀ : R) = ∑ χ : H', (e h χ : R) := by
    rw [Finset.sum_mul]
    refine (Fintype.sum_equiv (Equiv.addRight χ₀) _ _ fun χ => ?_)
    simp only [Equiv.coe_addRight, he₂, Units.val_mul]
  have : (∑ χ : H', (e h χ : R)) * ((e h χ₀ : R) - 1) = 0 := by rw [mul_sub, mul_one, hS, sub_self]
  exact (hχ₀.mul_left_eq_zero).mp this

include he₁ in

theorem sum_e_inv_eq_zero (χ : H') (hu : ∃ h : H, IsUnit ((e h χ : R) - 1)) :
    ∑ h : H, ((e h χ)⁻¹ : Rˣ).val = 0 := by
  obtain ⟨h₀, hh₀⟩ := hu
  have hS : (∑ h : H, ((e h χ)⁻¹ : Rˣ).val) * ((e h₀ χ)⁻¹ : Rˣ).val = ∑ h : H, ((e h χ)⁻¹ : Rˣ).val := by
    rw [Finset.sum_mul]
    refine (Fintype.sum_equiv (Equiv.addRight h₀) _ _ fun h => ?_)
    simp only [Equiv.coe_addRight, he₁, mul_inv, Units.val_mul]

  have h1 : (∑ h : H, ((e h χ)⁻¹ : Rˣ).val) * (1 - (e h₀ χ : R)) = 0 := by
    have := congrArg (fun x => x * (e h₀ χ : R)) hS
    simp only [mul_assoc, Units.inv_mul, mul_one] at this
    rw [mul_sub, mul_one, ← this, sub_self]
  have hu' : IsUnit (1 - (e h₀ χ : R)) := by
    rw [← neg_sub]; exact hh₀.neg
  exact (hu'.mul_left_eq_zero).mp h1

end Ortho

section Weights

variable {R : Type u} [CommRing R]
  {H : Type v} [AddCommGroup H] [Fintype H]
  {H' : Type w} [AddCommGroup H'] [Fintype H']
  (hcard : Fintype.card H' = Fintype.card H) (hd : IsUnit ((Fintype.card H : ℕ) : R))
  (e : H → H' → Rˣ)
  (he₁ : ∀ (h₁ h₂ : H) (χ : H'), e (h₁ + h₂) χ = e h₁ χ * e h₂ χ)
  (he₂ : ∀ (h : H) (χ₁ χ₂ : H'), e h (χ₁ + χ₂) = e h χ₁ * e h χ₂)
  (hsep : ∀ h : H, h ≠ 0 → ∃ χ : H', IsUnit ((e h χ : R) - 1))
  (hsep' : ∀ χ : H', χ ≠ 0 → ∃ h : H, IsUnit ((e h χ : R) - 1))
  {M : Type*} [AddCommGroup M] [Module R M]
  (U : H → M →ₗ[R] M) (hU0 : U 0 = LinearMap.id) (hU : ∀ h₁ h₂ : H, U (h₁ + h₂) = U h₁ ∘ₗ U h₂)
  (V : H' → M →ₗ[R] M) (hV0 : V 0 = LinearMap.id) (hV : ∀ χ₁ χ₂ : H', V (χ₁ + χ₂) = V χ₁ ∘ₗ V χ₂)
  (hHeis : ∀ (h : H) (χ : H'), V χ ∘ₗ U h = (e h χ : R) • (U h ∘ₗ V χ))

def IsWeight (e : H → H' → Rˣ) (V : H' → M →ₗ[R] M) (h : H) (m : M) : Prop := ∀ χ : H', V χ m = (e h χ : R) • m

noncomputable def proj (hd : IsUnit ((Fintype.card H : ℕ) : R)) (e : H → H' → Rˣ) (V : H' → M →ₗ[R] M) (h : H) :
    M →ₗ[R] M :=
  ((hd.unit⁻¹ : Rˣ) : R) • ∑ χ : H', ((e h χ)⁻¹ : Rˣ).val • V χ

theorem proj_apply (h : H) (m : M) :
    proj hd e V h m = ((hd.unit⁻¹ : Rˣ) : R) • ∑ χ : H', ((e h χ)⁻¹ : Rˣ).val • V χ m := by
  simp only [proj, LinearMap.smul_apply, LinearMap.sum_apply]

include he₂ hV in

theorem isWeight_proj (h : H) (m : M) : IsWeight e V h (proj hd e V h m) := by
  intro ψ
  have key : ∑ χ : H', ((e h χ)⁻¹ : Rˣ).val • V ψ (V χ m) =
      (e h ψ : R) • ∑ χ : H', ((e h χ)⁻¹ : Rˣ).val • V χ m := by
    rw [Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.addLeft ψ) _ _ fun χ => ?_
    rw [Equiv.coe_addLeft, ← LinearMap.comp_apply, ← hV, smul_smul, he₂, mul_inv, Units.val_mul, ← mul_assoc,
      Units.mul_inv, one_mul]
  rw [proj_apply, map_smul, map_sum]
  simp only [map_smul]
  rw [key, smul_comm]

include hcard in

theorem proj_apply_of_isWeight (h : H) (m : M) (hm : IsWeight e V h m) : proj hd e V h m = m := by
  rw [proj_apply]
  have : ∀ χ : H', ((e h χ)⁻¹ : Rˣ).val • V χ m = m := fun χ => by
    rw [hm χ, smul_smul, Units.inv_mul, one_smul]
  simp only [this, Finset.sum_const, Finset.card_univ, hcard]
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul, IsUnit.val_inv_mul, one_smul]

include he₁ he₂ hsep in

theorem proj_apply_of_isWeight_ne (h h' : H) (hne : h ≠ h') (m : M) (hm : IsWeight e V h m) :
    proj hd e V h' m = 0 := by
  rw [proj_apply]
  have : ∀ χ : H', ((e h' χ)⁻¹ : Rˣ).val • V χ m = (e (h - h') χ : R) • m := fun χ => by
    rw [hm χ, smul_smul, sub_eq_add_neg, he₁, e_neg_left e he₁, Units.val_mul, mul_comm]
  simp only [this]
  rw [← Finset.sum_smul, sum_e_eq_zero e he₂ (h - h') (hsep _ (sub_ne_zero.mpr hne)), zero_smul, smul_zero]

include he₁ he₂ hsep' hV0 in

theorem sum_proj_apply (m : M) : ∑ h : H, proj hd e V h m = m := by
  classical
  simp only [proj_apply]
  rw [← Finset.smul_sum, Finset.sum_comm]
  have : ∀ χ : H', ∑ h : H, ((e h χ)⁻¹ : Rˣ).val • V χ m = if χ = 0 then (Fintype.card H : R) • V χ m else 0 := by
    intro χ
    rw [← Finset.sum_smul]
    split_ifs with hχ
    · subst hχ
      simp only [e_zero_right e he₂, inv_one, Units.val_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    · rw [sum_e_inv_eq_zero e he₁ χ (hsep' χ hχ), zero_smul]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true, hV0, LinearMap.id_apply]
  rw [smul_smul, IsUnit.val_inv_mul, one_smul]

include he₁ hHeis in

theorem isWeight_U (k h : H) (m : M) (hm : IsWeight e V h m) : IsWeight e V (k + h) (U k m) := by
  intro χ
  have := LinearMap.congr_fun (hHeis k χ) m
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at this
  rw [this, hm χ, map_smul, smul_smul, he₁, Units.val_mul]

include hU0 hU in
theorem U_neg_apply (k : H) (m : M) : U (-k) (U k m) = m := by
  rw [← LinearMap.comp_apply, ← hU, neg_add_cancel, hU0, LinearMap.id_apply]

include hU0 hU in
theorem U_apply_neg (k : H) (m : M) : U k (U (-k) m) = m := by
  rw [← LinearMap.comp_apply, ← hU, add_neg_cancel, hU0, LinearMap.id_apply]

include hU0 hU in
theorem U_injective (k : H) : Function.Injective (U k) := fun x y hxy => by
  have := congrArg (U (-k)) hxy
  rwa [U_neg_apply U hU0 hU, U_neg_apply U hU0 hU] at this

def weightZero (e : H → H' → Rˣ) (V : H' → M →ₗ[R] M) : Submodule R M where
  carrier := {m | IsWeight e V 0 m}
  add_mem' {a b} ha hb := fun χ => by rw [map_add, ha χ, hb χ, smul_add]
  zero_mem' := fun χ => by rw [map_zero, smul_zero]
  smul_mem' c {x} hx := fun χ => by rw [map_smul, hx χ, smul_comm]

theorem mem_weightZero {m : M} : m ∈ weightZero e V ↔ IsWeight e V 0 m := Iff.rfl

def decomp (e : H → H' → Rˣ) (U : H → M →ₗ[R] M) (V : H' → M →ₗ[R] M) : (H → weightZero e V) →ₗ[R] M where
  toFun c := ∑ h : H, U h (c h)
  map_add' c c' := by simp only [Pi.add_apply, Submodule.coe_add, map_add, Finset.sum_add_distrib]
  map_smul' a c := by simp only [Pi.smul_apply, Submodule.coe_smul, map_smul, RingHom.id_apply, Finset.smul_sum]

theorem decomp_apply (c : H → weightZero e V) : decomp e U V c = ∑ h : H, U h (c h) := rfl

include he₁ he₂ hsep hcard hHeis in

theorem proj_decomp (c : H → weightZero e V) (h : H) : proj hd e V h (decomp e U V c) = U h (c h) := by
  classical
  rw [decomp_apply, map_sum]
  rw [Finset.sum_eq_single h]
  · refine proj_apply_of_isWeight hcard hd e V h _ ?_
    have := isWeight_U e he₁ U V hHeis h 0 (c h) (c h).2
    rwa [add_zero] at this
  · intro h' _ hh'
    refine proj_apply_of_isWeight_ne hd e he₁ he₂ hsep V h' h hh' _ ?_
    have := isWeight_U e he₁ U V hHeis h' 0 (c h') (c h').2
    rwa [add_zero] at this
  · exact fun hh => absurd (Finset.mem_univ h) hh

include hcard hd he₁ he₂ hsep hsep' hU0 hU hV0 hV hHeis in

theorem decomp_bijective : Function.Bijective (decomp e U V) := by
  classical
  refine ⟨fun c c' hcc' => ?_, fun m => ?_⟩
  · funext h
    apply Subtype.ext
    apply U_injective U hU0 hU h
    rw [← proj_decomp hcard hd e he₁ he₂ hsep U V hHeis c h, ← proj_decomp hcard hd e he₁ he₂ hsep U V hHeis c' h, hcc']
  · refine ⟨fun h => ⟨U (-h) (proj hd e V h m), ?_⟩, ?_⟩
    · rw [mem_weightZero]
      have := isWeight_U e he₁ U V hHeis (-h) h _ (isWeight_proj hd e he₂ V hV h m)
      rwa [neg_add_cancel] at this
    · rw [decomp_apply]
      simp only [U_apply_neg U hU0 hU]
      exact sum_proj_apply hd e he₁ he₂ hsep' V hV0 m

end Weights

section RankOne

variable {R : Type u} [CommRing R] {P : Type*} [AddCommGroup P] [Module R P]

def LocGen (r : R) (w : P) : Prop :=
  (∀ m : P, ∃ (a : R) (k : ℕ), r ^ k • m = a • w) ∧ (∀ a : R, a • w = 0 → ∃ k : ℕ, r ^ k * a = 0)

theorem locGen_of_pow_eq_zero {r : R} {k : ℕ} (hk : r ^ k = 0) : LocGen r (0 : P) :=
  ⟨fun m => ⟨0, k, by rw [hk, zero_smul, zero_smul]⟩, fun a _ => ⟨k, by rw [hk, zero_mul]⟩⟩

theorem exists_locGen_of_free (r : R)
    [Module.Free (Localization (Submonoid.powers r)) (LocalizedModule (Submonoid.powers r) P)]
    (h1 : Module.finrank (Localization (Submonoid.powers r)) (LocalizedModule (Submonoid.powers r) P) = 1) :
    ∃ w : P, LocGen r w := by
  classical
  set S := Submonoid.powers r with hS
  set L := Localization S
  set A := LocalizedModule S P
  rcases subsingleton_or_nontrivial L with hL | hL
  ·
    have h10 : algebraMap R L 1 = 0 := Subsingleton.elim _ _
    obtain ⟨⟨m, hm⟩, hm0⟩ := (IsLocalization.map_eq_zero_iff S L 1).mp h10
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp hm
    refine ⟨0, locGen_of_pow_eq_zero (k := k) ?_⟩
    rw [hk]; simpa using hm0
  · haveI : Module.Finite L A := Module.finite_of_finrank_pos (by rw [h1]; exact one_pos)
    let bL := Module.Free.chooseBasis L A
    have hcard : Fintype.card (Module.Free.ChooseBasisIndex L A) = 1 := by
      rw [← Module.finrank_eq_card_chooseBasisIndex, h1]
    obtain ⟨i₀, hi₀⟩ := Fintype.card_eq_one_iff.mp hcard

    have hsurj : ∀ x : A, ∃ a : L, x = a • bL i₀ := fun x => by
      refine ⟨bL.repr x i₀, ?_⟩
      conv_lhs => rw [← bL.sum_repr x]
      rw [Fintype.sum_eq_single i₀ (fun j hj => absurd (hi₀ j) hj)]
    have hinj : ∀ a : L, a • bL i₀ = 0 → a = 0 := fun a ha => by
      have := congrArg (fun x => bL.repr x i₀) ha
      simpa [bL.repr_self, Finsupp.single_eq_same] using this

    obtain ⟨w₀, s₀, hws⟩ : ∃ (w₀ : P) (s₀ : S), LocalizedModule.mk w₀ s₀ = bL i₀ :=
      LocalizedModule.induction_on (β := fun x => ∃ (w₀ : P) (s₀ : S), LocalizedModule.mk w₀ s₀ = x)
        (fun w s => ⟨w, s, rfl⟩) (bL i₀)
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp s₀.2
    refine ⟨w₀, fun m => ?_, fun a ha => ?_⟩
    · obtain ⟨a', ha'⟩ := hsurj (LocalizedModule.mk m 1)
      obtain ⟨a, s, rfl⟩ : ∃ (a : R) (s : S), Localization.mk a s = a' :=
        Localization.induction_on (p := fun x => ∃ (a : R) (s : S), Localization.mk a s = x) a'
          (fun y => ⟨y.1, y.2, rfl⟩)
      obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
      rw [← hws, LocalizedModule.mk_smul_mk] at ha'
      obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp ha'
      obtain ⟨l, hl⟩ := (Submonoid.mem_powers_iff _ _).mp u.2
      refine ⟨r ^ l * a, l + (i + j), ?_⟩
      have hu' : (r ^ l * (r ^ i * r ^ j)) • m = (r ^ l * a) • w₀ := by
        have h2 := hu
        simp only [Submonoid.smul_def, Submonoid.coe_mul, OneMemClass.coe_one, one_smul, smul_smul] at h2
        rw [hl, hi, hj]
        exact h2
      rw [pow_add, pow_add]
      exact hu'
    · have h0 : algebraMap R L a • bL i₀ = 0 := by
        rw [← hws, algebraMap_smul, LocalizedModule.smul'_mk, ha, LocalizedModule.zero_mk]
      have := hinj _ h0
      obtain ⟨⟨m, hm⟩, hm0⟩ := (IsLocalization.map_eq_zero_iff S L a).mp this
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp hm
      exact ⟨k, by rw [hk]; exact hm0⟩

theorem exists_locGen_of_rankAtStalk_eq_one [Module.Finite R P] [Module.Projective R P]
    (p : PrimeSpectrum R) (hp : Module.rankAtStalk P p = 1) :
    ∃ r : R, r ∉ p.asIdeal ∧ ∃ w : P, LocGen r w := by
  haveI : Module.FinitePresentation R P := Module.finitePresentation_of_projective R P
  set S := p.asIdeal.primeCompl
  haveI : Module.Finite (Localization.AtPrime p.asIdeal) (LocalizedModule S P) :=
    Module.Finite.of_isLocalizedModule S (LocalizedModule.mkLinearMap S P)
  haveI : Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule S P) := Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hrS, hfree, hrank⟩ := Module.FinitePresentation.exists_free_localizedModule_powers S
      (LocalizedModule.mkLinearMap S P) (Localization.AtPrime p.asIdeal)
  refine ⟨r, hrS, ?_⟩
  haveI := hfree
  apply exists_locGen_of_free r
  rw [hrank]
  exact hp

theorem exists_cover_locGen [Module.Finite R P] [Module.Projective R P]
    (hrk : ∀ p : PrimeSpectrum R, Module.rankAtStalk P p = 1) :
    ∃ (n : ℕ) (r : Fin n → R), Ideal.span (Set.range r) = ⊤ ∧ ∀ j, ∃ w : P, LocGen (r j) w := by
  classical
  set G : Set R := {r | ∃ w : P, LocGen r w} with hG
  have htop : Ideal.span G = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr, w, hw⟩ := exists_locGen_of_rankAtStalk_eq_one (P := P) ⟨𝔪, h𝔪.isPrime⟩ (hrk _)
    exact hr (hle (Ideal.subset_span ⟨w, hw⟩))
  have h1 : (1 : R) ∈ Ideal.span G := by rw [htop]; exact Submodule.mem_top
  obtain ⟨T, hTG, h1T⟩ := Submodule.mem_span_finite_of_mem_span h1
  refine ⟨T.card, fun j => (T.equivFin.symm j : R), ?_, fun j => ?_⟩
  · rw [eq_top_iff, ← Ideal.span_singleton_one, Ideal.span_le, Set.singleton_subset_iff]
    refine Submodule.span_mono ?_ h1T
    intro x hx
    exact ⟨T.equivFin ⟨x, hx⟩, by simp⟩
  · exact hTG (T.equivFin.symm j).2

end RankOne

section Transport

variable {R : Type u} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {H : Type v} [Fintype H]

theorem bijective_sum_smul_of_locGen (r : R) (v : H → M)
    (hgen : ∀ m : M, ∃ (a : H → R) (k : ℕ), r ^ k • m = ∑ h, a h • v h)
    (hind : ∀ a : H → R, ∑ h, a h • v h = 0 → ∃ k : ℕ, ∀ h, r ^ k * a h = 0)
    (Rj : Type*) [CommRing Rj] [Algebra R Rj] [IsLocalization.Away r Rj]
    (Mj : Type*) [AddCommGroup Mj] [Module R Mj] [Module Rj Mj] [IsScalarTower R Rj Mj]
    (ℓ : M →ₗ[R] Mj) [IsLocalizedModule (Submonoid.powers r) ℓ] :
    Function.Bijective (fun c : H → Rj => ∑ h, c h • ℓ (v h)) := by
  classical
  have hunit : ∀ k : ℕ, IsUnit (algebraMap R Rj (r ^ k)) := fun k => by
    rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit r).pow k

  have hlin : ∀ c c' : H → Rj, (∑ h, (c - c') h • ℓ (v h)) = (∑ h, c h • ℓ (v h)) - ∑ h, c' h • ℓ (v h) := by
    intro c c'
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  refine ⟨fun c c' hcc' => ?_, fun y => ?_⟩
  ·
    rw [← sub_eq_zero]
    set d := c - c' with hd
    have hd0 : ∑ h, d h • ℓ (v h) = 0 := by rw [hd, hlin]; exact sub_eq_zero.mpr hcc'

    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (Submonoid.powers r) (Finset.univ : Finset H) d
    choose a ha using fun h => (hb h (Finset.mem_univ h))

    have hsum : ℓ (∑ h, a h • v h) = 0 := by
      rw [map_sum]
      have : ∀ h, ℓ (a h • v h) = (b : R) • (d h • ℓ (v h)) := fun h => by
        rw [map_smul, ← algebraMap_smul Rj (a h), ha h, smul_assoc]
      simp only [this, ← Finset.smul_sum, hd0, smul_zero]
    obtain ⟨u, hu⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers r) (f := ℓ)
      (x₁ := ∑ h, a h • v h) (x₂ := 0) (hsum.trans (map_zero ℓ).symm)
    rw [smul_zero, Finset.smul_sum] at hu
    simp only [smul_smul, Submonoid.smul_def] at hu
    obtain ⟨k, hk⟩ := hind _ hu
    funext h
    have hk' := congrArg (algebraMap R Rj) (hk h)
    rw [map_zero, map_mul, map_mul, ha h] at hk'

    obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).mp u.2
    obtain ⟨i', hi'⟩ := (Submonoid.mem_powers_iff _ _).mp b.2
    rw [Algebra.smul_def, ← hi, ← hi', ← mul_assoc, ← mul_assoc] at hk'
    have hU : IsUnit (algebraMap R Rj (r ^ k) * algebraMap R Rj (r ^ i) * algebraMap R Rj (r ^ i')) :=
      ((hunit k).mul (hunit i)).mul (hunit i')
    simpa [Pi.zero_apply] using (hU.mul_right_eq_zero).mp hk'
  ·
    obtain ⟨⟨m, s⟩, hms⟩ := IsLocalizedModule.surj (Submonoid.powers r) ℓ y
    obtain ⟨a, k, hk⟩ := hgen m
    obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    have hU : IsUnit (algebraMap R Rj (r ^ k * r ^ i)) := by rw [map_mul]; exact (hunit k).mul (hunit i)
    refine ⟨fun h => ((hU.unit⁻¹ : Rjˣ) : Rj) * algebraMap R Rj (a h), ?_⟩
    simp only [mul_smul, ← Finset.smul_sum]
    have h1 : ∑ h, algebraMap R Rj (a h) • ℓ (v h) = ℓ (r ^ k • m) := by
      rw [hk, map_sum]; simp only [map_smul, algebraMap_smul]
    have h2 : ℓ (r ^ k • m) = algebraMap R Rj (r ^ k * r ^ i) • y := by

      rw [map_smul, ← hms, Submonoid.smul_def, ← hi, smul_smul, algebraMap_smul]
    rw [h1, h2, smul_smul, IsUnit.val_inv_mul, one_smul]

end Transport

end SvNSol

theorem solution
    {R : Type u} [CommRing R]
    {H : Type v} [AddCommGroup H] [Fintype H]
    {H' : Type w} [AddCommGroup H'] [Fintype H']
    (hcard : Fintype.card H' = Fintype.card H) (hd : IsUnit ((Fintype.card H : ℕ) : R))
    (e : H → H' → Rˣ)
    (he₁ : ∀ (h₁ h₂ : H) (χ : H'), e (h₁ + h₂) χ = e h₁ χ * e h₂ χ)
    (he₂ : ∀ (h : H) (χ₁ χ₂ : H'), e h (χ₁ + χ₂) = e h χ₁ * e h χ₂)
    (hsep : ∀ h : H, h ≠ 0 → ∃ χ : H', IsUnit ((e h χ : R) - 1))
    (hsep' : ∀ χ : H', χ ≠ 0 → ∃ h : H, IsUnit ((e h χ : R) - 1))
    {M : Type u} [AddCommGroup M] [Module R M]
    {ι : Type u} [Fintype ι] (b : Module.Basis ι R M) (hrank : Fintype.card ι = Fintype.card H)
    (U : H → M →ₗ[R] M) (hU0 : U 0 = LinearMap.id) (hU : ∀ h₁ h₂ : H, U (h₁ + h₂) = U h₁ ∘ₗ U h₂)
    (V : H' → M →ₗ[R] M) (hV0 : V 0 = LinearMap.id) (hV : ∀ χ₁ χ₂ : H', V (χ₁ + χ₂) = V χ₁ ∘ₗ V χ₂)
    (hHeis : ∀ (h : H) (χ : H'), V χ ∘ₗ U h = (e h χ : R) • (U h ∘ₗ V χ)) :
    ∃ (n : ℕ) (r : Fin n → R), Ideal.span (Set.range r) = ⊤ ∧
      ∀ (j : Fin n) (Rj : Type u) [CommRing Rj] [Algebra R Rj] [IsLocalization.Away (r j) Rj]
        (Mj : Type u) [AddCommGroup Mj] [Module R Mj] [Module Rj Mj] [IsScalarTower R Rj Mj]
        (ℓ : M →ₗ[R] Mj) [IsLocalizedModule (Submonoid.powers (r j)) ℓ]
        (U' : H → Mj →ₗ[Rj] Mj) (_hU' : ∀ (h : H) (m : M), U' h (ℓ m) = ℓ (U h m))
        (V' : H' → Mj →ₗ[Rj] Mj) (_hV' : ∀ (χ : H') (m : M), V' χ (ℓ m) = ℓ (V χ m)),
        ∃ σ : H → Mj,
          Function.Bijective (fun c : H → Rj => ∑ h, c h • σ h) ∧
          (∀ k h : H, U' k (σ h) = σ (k + h)) ∧
          (∀ (χ : H') (h : H), V' χ (σ h) = algebraMap R Rj (e h χ : R) • σ h) := by
  classical
  haveI : Module.Finite R M := Module.Finite.of_basis b
  haveI : Module.Free R M := Module.Free.of_basis b

  let M₀ := SvNSol.weightZero e V
  let p₀ : M →ₗ[R] M₀ := LinearMap.codRestrict M₀ (SvNSol.proj hd e V 0) fun m => SvNSol.isWeight_proj hd e he₂ V hV 0 m
  have hsplit : p₀ ∘ₗ M₀.subtype = LinearMap.id := by
    apply LinearMap.ext; intro x; apply Subtype.ext
    exact SvNSol.proj_apply_of_isWeight hcard hd e V 0 (x : M) x.2
  haveI : Module.Projective R M₀ := Module.Projective.of_split M₀.subtype p₀ hsplit
  haveI : Module.Finite R M₀ :=
    Module.Finite.of_surjective p₀ (Function.RightInverse.surjective (g := M₀.subtype) fun x => LinearMap.congr_fun hsplit x)

  let Φ : (H → M₀) ≃ₗ[R] M :=
    LinearEquiv.ofBijective (SvNSol.decomp e U V) (SvNSol.decomp_bijective hcard hd e he₁ he₂ hsep hsep' U hU0 hU V hV0 hV hHeis)
  have hH : Fintype.card H ≠ 0 := Fintype.card_ne_zero
  have hrk : ∀ p : PrimeSpectrum R, Module.rankAtStalk (↥M₀) p = 1 := by
    intro p
    haveI : Nontrivial R := ⟨⟨1, 0, fun h10 => p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ (h10 ▸ Submodule.zero_mem _ : (1 : R) ∈ p.asIdeal) isUnit_one)⟩⟩
    have h1 : Module.rankAtStalk M p = Fintype.card H := by
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_eq_card_basis b, hrank]; rfl
    have h2 : Module.rankAtStalk (H → ↥M₀) p = Fintype.card H * Module.rankAtStalk (↥M₀) p := by
      rw [Module.rankAtStalk_pi, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    have h3 := congrFun (Module.rankAtStalk_eq_of_equiv Φ) p
    rw [h2, h1] at h3
    exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hH) (h3.trans (mul_one _).symm))

  obtain ⟨n, r, hspan, hw⟩ := SvNSol.exists_cover_locGen (P := ↥M₀) hrk
  refine ⟨n, r, hspan, ?_⟩
  intro j Rj _ _ _ Mj _ _ _ _ ℓ _ U' hU' V' hV'
  obtain ⟨w, hw₁, hw₂⟩ := hw j

  let v : H → M := fun h => U h (w : M)
  have hvW : ∀ h, SvNSol.IsWeight e V h (v h) := fun h => by
    have := SvNSol.isWeight_U e he₁ U V hHeis h 0 (w : M) w.2
    rwa [add_zero] at this

  have hgen : ∀ m : M, ∃ (a : H → R) (k : ℕ), r j ^ k • m = ∑ h, a h • v h := by
    intro m
    obtain ⟨c, rfl⟩ := (SvNSol.decomp_bijective hcard hd e he₁ he₂ hsep hsep' U hU0 hU V hV0 hV hHeis).2 m
    choose a k hak using fun h => hw₁ (c h)
    set K := ∑ h', k h' with hKdef
    have hle : ∀ h, k h ≤ K := fun h => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ h)
    have hK : ∀ h, r j ^ K = r j ^ (K - k h) * r j ^ k h := fun h => by rw [← pow_add, Nat.sub_add_cancel (hle h)]
    refine ⟨fun h => r j ^ (K - k h) * a h, K, ?_⟩
    rw [SvNSol.decomp_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    have hak' : r j ^ k h • ((c h : ↥M₀) : M) = a h • (w : M) := by
      simpa only [Submodule.coe_smul] using congrArg Subtype.val (hak h)
    show r j ^ K • U h (c h : M) = (r j ^ (K - k h) * a h) • U h (w : M)
    rw [← map_smul, hK h, mul_smul, hak', smul_smul, map_smul]

  have hind : ∀ a : H → R, ∑ h, a h • v h = 0 → ∃ k : ℕ, ∀ h, r j ^ k * a h = 0 := by
    intro a ha
    have hcomp : ∀ h₀, a h₀ • (w : ↥M₀) = 0 := fun h₀ => by
      let c : H → ↥M₀ := fun h => a h • w
      have hc : SvNSol.decomp e U V c = 0 := by
        rw [SvNSol.decomp_apply, ← ha]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [Submodule.coe_smul, map_smul]
      have := SvNSol.proj_decomp hcard hd e he₁ he₂ hsep U V hHeis c h₀
      rw [hc, map_zero] at this
      apply Subtype.ext
      apply SvNSol.U_injective U hU0 hU h₀
      rw [Submodule.coe_zero, map_zero]
      exact this.symm
    choose k hk using fun h => hw₂ (a h) (hcomp h)
    refine ⟨∑ h', k h', fun h => ?_⟩
    have hle : k h ≤ ∑ h', k h' := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ h)
    rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, hk h, mul_zero]

  have hbij := SvNSol.bijective_sum_smul_of_locGen (r j) v hgen hind Rj Mj ℓ
  refine ⟨fun h => ℓ (v h), hbij, fun k h => ?_, fun χ h => ?_⟩
  · show U' k (ℓ (U h (w : M))) = ℓ (U (k + h) (w : M))
    rw [hU', hU k h, LinearMap.comp_apply]
  · show V' χ (ℓ (U h (w : M))) = algebraMap R Rj (e h χ : R) • ℓ (U h (w : M))
    rw [hV', hvW h χ, map_smul, algebraMap_smul]

end S_LinearMap_exists_span_eq_top_forall_exists_bijective_and_apply_eq_of_comp_eq_smul_comp
end P2MW
export P2MW.S_LinearMap_exists_span_eq_top_forall_exists_bijective_and_apply_eq_of_comp_eq_smul_comp (solution)
