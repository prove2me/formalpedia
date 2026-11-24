-- Prove2me | solution 1 for GlobalTheory.lift_of_compatible_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:34:45.668646+00:00
-- url     : https://prove2.me/submissions/812d6e8b-82a1-4768-9e3c-4998903251b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HenselRootsCompatible
import Theorems.Thm_GlobalTheory_mem_ideal_smul_top_iff_mem
import Theorems.Thm_GlobalTheory_eval_map_mem_maximalIdeal_pow_of_coeff_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {A R V : Type} [CommRing A] [IsLocalRing A] [CommRing R]
    [IsLocalRing R] [CommRing V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V]
    (φ : A →+* R) (α : A →+* V), IsLocalHom α → ∀ (θ : R) (η : V) (q : Polynomial A), q.Monic →
    (q.map φ).eval θ = 0 → (q.map α).eval η = 0 →
    (∀ (n : ℕ) (r : R), ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R ^ n) →
    (∀ (n : ℕ) (P : Polynomial A), P.natDegree < q.natDegree →
      (P.map φ).eval θ ∈ maximalIdeal R ^ n → ∀ i, P.coeff i ∈ maximalIdeal A ^ n) →
    ∃ ψ : R →+* V, ψ.comp φ = α ∧ IsLocalHom ψ := by
  intro A R V _ _ _ _ _ _ _ φ α hα θ η q hq hqθ hqη happ hinj
  classical
  have hq1 : q ≠ 1 := by
    rintro rfl
    simp at hqθ
  have key : ∀ (n : ℕ) (P P' : Polynomial A),
      (P.map φ).eval θ - (P'.map φ).eval θ ∈ maximalIdeal R ^ n →
      (P.map α).eval η - (P'.map α).eval η ∈ maximalIdeal V ^ n := by
    intro n P P' h
    have hD := Polynomial.modByMonic_add_div (P - P') q
    have e1 : (P.map φ).eval θ - (P'.map φ).eval θ = (((P - P') %ₘ q).map φ).eval θ := by
      rw [← Polynomial.eval_sub, ← Polynomial.map_sub]
      conv_lhs => rw [← hD]
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.eval_add,
        Polynomial.eval_mul, hqθ, zero_mul, add_zero]
    have e2 : (P.map α).eval η - (P'.map α).eval η = (((P - P') %ₘ q).map α).eval η := by
      rw [← Polynomial.eval_sub, ← Polynomial.map_sub]
      conv_lhs => rw [← hD]
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.eval_add,
        Polynomial.eval_mul, hqη, zero_mul, add_zero]
    rw [e2]
    rw [e1] at h
    exact eval_map_mem_maximalIdeal_pow_of_coeff_mem α n _
      (hinj n _ (Polynomial.natDegree_modByMonic_lt _ hq hq1) h) η
  have hmem : ∀ (n : ℕ) (x : V),
      x ∈ (maximalIdeal V ^ n) • (⊤ : Submodule V V) ↔ x ∈ maximalIdeal V ^ n :=
    fun n x => mem_ideal_smul_top_iff_mem _ x
  have ex : ∀ r : R, ∃ L : V, ∀ (n : ℕ) (P : Polynomial A),
      r - (P.map φ).eval θ ∈ maximalIdeal R ^ n → L - (P.map α).eval η ∈ maximalIdeal V ^ n := by
    intro r
    choose Pn hPn using fun n => happ n r
    have hc : ∀ {m n : ℕ}, m ≤ n → ((Pn m).map α).eval η ≡ ((Pn n).map α).eval η
        [SMOD (maximalIdeal V ^ m • (⊤ : Submodule V V))] := by
      intro m n hmn
      rw [SModEq.sub_mem, hmem]
      apply key
      have h1 : r - ((Pn n).map φ).eval θ ∈ maximalIdeal R ^ m :=
        Ideal.pow_le_pow_right hmn (hPn n)
      have := Ideal.sub_mem _ h1 (hPn m)
      convert this using 1
      ring
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (f := fun k => ((Pn k).map α).eval η) inferInstance hc
    refine ⟨L, fun n P hP => ?_⟩
    have h1 := (hmem n _).1 ((SModEq.sub_mem).1 (hL n))
    have h2 : ((Pn n).map α).eval η - (P.map α).eval η ∈ maximalIdeal V ^ n := by
      apply key
      have := Ideal.sub_mem _ hP (hPn n)
      convert this using 1
      ring
    have := Ideal.sub_mem _ h2 h1
    convert this using 1
    ring
  have haus : ∀ x : V, (∀ n, x ∈ maximalIdeal V ^ n) → x = 0 := by
    intro x hx
    exact IsHausdorff.haus inferInstance x fun n =>
      SModEq.sub_mem.2 (by rw [sub_zero, hmem]; exact hx n)
  choose ψ0 hψ0 using ex
  have char : ∀ (x : R) (b : V), (∀ n, ∃ P : Polynomial A,
      x - (P.map φ).eval θ ∈ maximalIdeal R ^ n ∧ b - (P.map α).eval η ∈ maximalIdeal V ^ n) →
      ψ0 x = b := by
    intro x b h
    rw [← sub_eq_zero]
    apply haus
    intro n
    obtain ⟨P, h1, h2⟩ := h n
    have := Ideal.sub_mem _ (hψ0 x n P h1) h2
    convert this using 1
    ring
  let ψ : R →+* V :=
    { toFun := ψ0
      map_one' := char 1 1 fun n => ⟨1, by simp, by simp⟩
      map_zero' := char 0 0 fun n => ⟨0, by simp, by simp⟩
      map_add' := fun x y => char _ _ fun n => by
        obtain ⟨Px, hx⟩ := happ n x
        obtain ⟨Py, hy⟩ := happ n y
        refine ⟨Px + Py, ?_, ?_⟩
        · have := Ideal.add_mem _ hx hy
          convert this using 1
          simp only [Polynomial.map_add, Polynomial.eval_add]
          ring
        · have := Ideal.add_mem _ (hψ0 x n Px hx) (hψ0 y n Py hy)
          convert this using 1
          simp only [Polynomial.map_add, Polynomial.eval_add]
          ring
      map_mul' := fun x y => char _ _ fun n => by
        obtain ⟨Px, hx⟩ := happ n x
        obtain ⟨Py, hy⟩ := happ n y
        refine ⟨Px * Py, ?_, ?_⟩
        · have := Ideal.add_mem _ (Ideal.mul_mem_right y _ hx)
            (Ideal.mul_mem_left _ ((Px.map φ).eval θ) hy)
          convert this using 1
          simp only [Polynomial.map_mul, Polynomial.eval_mul]
          ring
        · have := Ideal.add_mem _ (Ideal.mul_mem_right (ψ0 y) _ (hψ0 x n Px hx))
            (Ideal.mul_mem_left _ ((Px.map α).eval η) (hψ0 y n Py hy))
          convert this using 1
          simp only [Polynomial.map_mul, Polynomial.eval_mul]
          ring }
  refine ⟨ψ, ?_, ⟨fun r hr => ?_⟩⟩
  · ext a
    show ψ0 (φ a) = α a
    exact char _ _ fun n => ⟨Polynomial.C a, by simp, by simp⟩
  · by_contra hnu
    have hrm : r ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal r).2 hnu
    obtain ⟨P, hP⟩ := happ 1 r
    rw [pow_one] at hP
    have h1 : (P.map φ).eval θ - ((0 : Polynomial A).map φ).eval θ ∈ maximalIdeal R ^ 1 := by
      simp only [Polynomial.map_zero, Polynomial.eval_zero, sub_zero, pow_one]
      have := Ideal.sub_mem _ hrm hP
      convert this using 1
      ring
    have h2 := key 1 P 0 h1
    have h3 := hψ0 r 1 P (by rw [pow_one]; exact hP)
    have h4 := Ideal.add_mem _ h3 h2
    rw [pow_one] at h4
    have h5 : ψ0 r ∈ maximalIdeal V := by
      convert h4 using 1
      simp
    exact (IsLocalRing.mem_maximalIdeal _).1 h5 hr
end GlobalTheory
