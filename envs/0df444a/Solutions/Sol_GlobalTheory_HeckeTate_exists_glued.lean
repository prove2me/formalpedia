-- Prove2me | solution 1 for GlobalTheory.HeckeTate.exists_glued
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:54:04.719805+00:00
-- url     : https://prove2.me/submissions/6e70dbb0-5a4b-47c9-b4dd-d23a5aac724d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem
import Theorems.Thm_GlobalTheory_HeckeTate_dvd_of_idem
import Theorems.Thm_GlobalTheory_HeckeTate_dvd_mul_of_idem
import Theorems.Thm_GlobalTheory_HeckeTate_IsPart_of_dvd
import Theorems.Thm_GlobalTheory_HeckeTate_IsPart_unique
import Theorems.Thm_GlobalTheory_HeckeTate_IsPart_exists_inv
import Theorems.Thm_GlobalTheory_HeckeTate_exists_isPart
import Theorems.Thm_GlobalTheory_HeckeTate_mem_mults
import Theorems.Thm_GlobalTheory_HeckeTate_smul_mem_mults
import Theorems.Thm_GlobalTheory_HeckeTate_comp_sub_mem
import Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_skew
import Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_adj
import Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_ext
import Theorems.Thm_GlobalTheory_HeckeTate_exists_adjoint
import Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_smul_cancel
import Theorems.Thm_GlobalTheory_HeckeTate_map_mem_mults

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HeckeTate
variable {R : Type} [CommRing R] {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
variable {σ : R ≃+* R} {B : M →+ M →+ ℤ} {B' : M' →+ M' →+ ℤ}
namespace GlobalTheory.HeckeTate
theorem _root_.solution [IsDedekindDomain R] [CharZero R] (h : IsUnimod σ B) (h' : IsUnimod σ B')
    (hσ : ∀ a, σ (σ a) = a) {P : Ideal R} (hP : P.IsMaximal) (hPP : P ⊔ P.map (σ : R →+* R) = ⊤)
    {p : ℕ} (hp0 : p ≠ 0) (hpP : (p : R) ∈ P) (i : M' →ₗ[R] M) (hi : Function.Injective i)
    (hB : ∀ x y, B (i x) (i y) = (p : ℤ) ^ 2 * B' x y)
    (hsq : ∀ a, ∃ y, i y = (p : R) ^ 2 • a) (hlow : ∀ γ ∈ P, ∀ a, ∃ y, i y = (γ * p) • a)
    (φ : M →ₗ[R] M') (φ' : M' →ₗ[R] M) {s : R} (hs : s ∉ P) (hφ : ∀ a, φ' (φ a) = s • a)
    (hφ' : ∀ y, φ (φ' y) = s • y) :
    ∃ G : ℕ → M →ₗ[R] M',
      (∀ n : ℕ, 0 < n → ∀ a, G n a ∈ mults M' (n : R) → a ∈ mults M (n : R)) ∧
      (∀ n : ℕ, 0 < n → ∀ y, ∃ a, G n a - y ∈ mults M' (n : R)) ∧
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, G (n * m) a - G n a ∈ mults M' (n : R)) ∧
      (∀ n : ℕ, 0 < n → ∀ a b, (n : ℤ) ∣ B' (G n a) (G n b) - B a b) ∧
      (∀ n : ℕ, 0 < n → n.Coprime p → ∀ a, i (G n a) - (p : R) • a ∈ mults M (n : R)) := by
  have hpR : (p : R) ≠ 0 := Nat.cast_ne_zero.2 hp0

  have hex : ∀ n : ℕ, ∃ e : R, 1 - e ∈ P ∧ σ e ∈ P ∧ (0 < n → IsPart P ((n : R) * p ^ 2) e) := by
    intro n
    obtain ⟨e, he⟩ := exists_isPart hP (N := ((max n 1 : ℕ) : R) * p ^ 2)
      (mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (pow_ne_zero _ hpR))
    refine ⟨e, he.2.1, ?_, fun hn => by rwa [max_eq_left (show 1 ≤ n from hn)] at he⟩
    have hq : (P.comap (σ : R →+* R)).IsMaximal := Ideal.comap_isMaximal_of_surjective _ σ.surjective
    refine he.2.2 _ hq ?_ fun hne => ?_
    · rw [Ideal.mem_comap, map_mul, map_pow, map_natCast, map_natCast]
      exact P.mul_mem_left _ (Ideal.pow_mem_of_mem P hpP 2 two_pos)
    · apply hP.ne_top
      rw [← hPP, eq_comm, sup_eq_left, Ideal.map_le_iff_le_comap, hne]
  choose e he1 heσ he using hex
  have hexw : ∀ n : ℕ, ∃ w : R, 0 < n → (n : R) * p ^ 2 ∣ w * s * e n - e n := fun n => by
    by_cases hn : 0 < n
    · obtain ⟨w, hw⟩ := (he n hn).exists_inv hs
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose w hw using hexw
  have hexπ : ∀ n : ℕ, ∃ π : M →ₗ[R] M', ∀ a, i (π a) = ((1 - e n - σ (e n)) * p) • a := fun n => by
    choose f hf using hlow _ (P.sub_mem (he1 n) (heσ n))
    exact ⟨⟨⟨f, fun x y => hi (by rw [map_add, hf, hf, hf, smul_add])⟩,
      fun r x => hi (by simp only [RingHom.id_apply]; rw [map_smul, hf, hf, smul_comm])⟩, hf⟩
  choose π hπ using hexπ
  choose ρ hρ using fun n => exists_adjoint h h' hσ (π n)
  obtain ⟨φa, hφa⟩ := exists_adjoint h h' hσ φ
  obtain ⟨χ, hχ0⟩ := exists_adjoint h' h hσ φ'
  have hχ : ∀ a y, B' (χ a) y = B a (φ' y) := fun a y => by rw [h'.skew, ← hχ0, ← h.skew]
  have hφχ : ∀ a, φa (χ a) = σ s • a := fun a => h.ext fun b => by
    rw [← hφa, ← hχ0, hφ, h.adj]
  have hχφ : ∀ y, χ (φa y) = σ s • y := fun y => h'.ext fun b => by
    rw [← hχ0, ← hφa, hφ', h'.adj]
  have hσ3 : ∀ n, σ (1 - e n - σ (e n)) = 1 - e n - σ (e n) := fun n => by
    rw [map_sub, map_sub, map_one, hσ]; ring
  have hρp : ∀ n y, (p : R) • ρ n y = (1 - e n - σ (e n)) • i y := fun n y => h.ext fun a => by
    apply mul_left_cancel₀ (Int.natCast_ne_zero.2 hp0)
    have h1 := hB (π n a) y
    rw [hπ, hρ, h.adj, map_mul, map_natCast, hσ3, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul,
      map_nsmul, nsmul_eq_mul] at h1
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul, h1]
    ring
  have hρπ : ∀ n a, ρ n (π n a) = ((1 - e n - σ (e n)) ^ 2) • a := fun n a =>
    h.smul_cancel hp0 (by rw [hρp, hπ]; module)
  have hπρ : ∀ n y, π n (ρ n y) = ((1 - e n - σ (e n)) ^ 2) • y := fun n y =>
    hi (by rw [hπ, mul_smul, hρp, map_smul]; module)
  have hσdvd : ∀ (n : ℕ) (x : R), (n : R) * p ^ 2 ∣ x → (n : R) * p ^ 2 ∣ σ x := fun n x hx => by
    simpa using map_dvd σ hx

  let G : ℕ → M →ₗ[R] M' := fun n =>
    e n • φ + (σ (e n) * σ (w n)) • χ + (1 - e n - σ (e n)) • π n
  let H : ℕ → M' →ₗ[R] M := fun n =>
    σ (e n) • φa + (e n * w n) • φ' + (1 - e n - σ (e n)) • ρ n
  have hGH : ∀ n a y, B' (G n a) y = B a (H n y) := fun n a y => by
    simp only [G, H, LinearMap.add_apply, LinearMap.smul_apply, map_add, AddMonoidHom.add_apply,
      h'.adj, hφa, hχ, hρ, map_smul, map_mul, hσ, hσ3]
  have hcong : ∀ n : ℕ, 0 < n → ∃ c₁ c₂ c₃ c₄ c₅ : R,
      e n * (1 - e n) = n * c₁ ∧ σ (e n) * (1 - σ (e n)) = n * c₂ ∧ e n * σ (e n) = n * c₃ ∧
      w n * s * e n - e n = n * c₄ ∧ σ (w n) * σ s * σ (e n) - σ (e n) = n * c₅ := fun n hn => by
    have d : (n : R) ∣ (n : R) * p ^ 2 := dvd_mul_right _ _
    have d2 := hσdvd n _ (he n hn).1
    rw [map_mul, map_sub, map_one] at d2
    have d5 := hσdvd n _ (hw n hn)
    rw [map_sub, map_mul, map_mul] at d5
    have d3 := dvd_mul_of_idem (he n hn).1 d2 fun q hq hN => by
      by_cases hqP : q = P
      · exact Or.inr (hqP ▸ heσ n)
      · exact Or.inl ((he n hn).2.2 q hq hN hqP)
    obtain ⟨c₁, h₁⟩ := d.trans (he n hn).1
    obtain ⟨c₂, h₂⟩ := d.trans d2
    obtain ⟨c₃, h₃⟩ := d.trans d3
    obtain ⟨c₄, h₄⟩ := d.trans (hw n hn)
    obtain ⟨c₅, h₅⟩ := d.trans d5
    exact ⟨c₁, c₂, c₃, c₄, c₅, h₁, h₂, h₃, h₄, h₅⟩
  have hdv : ∀ n : ℕ, 0 < n → ∀ x : R,
      Ideal.Quotient.mk (Ideal.span {(n : R)}) x = 0 → (n : R) ∣ x := fun n _ x hx =>
    Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 hx)
  have hinv : ∀ n : ℕ, 0 < n → (∀ a, H n (G n a) - a ∈ mults M (n : R)) ∧
      ∀ y, G n (H n y) - y ∈ mults M' (n : R) := fun n hn => by
    obtain ⟨c₁, c₂, c₃, c₄, c₅, h₁, h₂, h₃, h₄, h₅⟩ := hcong n hn
    have k13 : (n : R) ∣ e n * (1 - e n - σ (e n)) := ⟨c₁ - c₃, by linear_combination h₁ - h₃⟩
    have k23 : (n : R) ∣ σ (e n) * (1 - e n - σ (e n)) := ⟨c₂ - c₃, by linear_combination h₂ - h₃⟩
    have k12 : (n : R) ∣ e n * σ (e n) := ⟨c₃, h₃⟩
    have k : (n : R) ∣ e n * (e n * w n) * s + σ (e n) * σ (w n) * σ (e n) * σ s +
        (1 - e n - σ (e n)) * (1 - e n - σ (e n)) * (1 - e n - σ (e n)) ^ 2 - 1 := by
      have := ((((k13.add k23).mul_left
        (1 + (1 - e n - σ (e n)) + (1 - e n - σ (e n)) ^ 2)).neg_right.sub ⟨c₁, h₁⟩).sub ⟨c₂, h₂⟩).add
        ((Dvd.dvd.mul_left ⟨c₄, h₄⟩ (e n)).add (Dvd.dvd.mul_left ⟨c₅, h₅⟩ (σ (e n))))
      convert this using 1
      ring
    have hH : H n = (e n * w n) • φ' + σ (e n) • φa + (1 - e n - σ (e n)) • ρ n := by
      simp only [H]; abel
    refine ⟨fun a => ?_, fun y => ?_⟩
    · rw [hH]
      refine comp_sub_mem φ χ (π n) φ' φa (ρ n) hφ hφχ (hρπ n) k12 k13 ?_ ?_ ?_ ?_ k a
      · convert k12.mul_left (σ (w n) * w n) using 1; ring
      · convert k23.mul_left (σ (w n)) using 1; ring
      · convert k13.mul_left (w n) using 1; ring
      · rwa [mul_comm]
    · rw [hH]
      refine comp_sub_mem φ' φa (ρ n) φ χ (π n) hφ' hχφ (hπρ n) ?_ ?_ ?_ k23 ?_ ?_ ?_ y
      · convert k12.mul_left (σ (w n) * w n) using 1; ring
      · convert k13.mul_left (w n) using 1; ring
      · rwa [mul_comm]
      · rwa [mul_comm]
      · convert k23.mul_left (σ (w n)) using 1; ring
      · convert k using 1; ring
  refine ⟨G, fun n hn a ha => ?_, fun n hn y => ⟨H n y, (hinv n hn).2 y⟩, fun n m hn hm a => ?_,
    fun n hn a b => ?_, fun n hn hnp a => ?_⟩
  · simpa using (mults M (n : R)).sub_mem (map_mem_mults (H n) ha) ((hinv n hn).1 a)
  · have hnm : 0 < n * m := Nat.mul_pos hn hm
    have d0 : (n : R) * p ^ 2 ∣ ((n * m : ℕ) : R) * p ^ 2 := ⟨m, by push_cast; ring⟩
    have d : (n : R) ∣ (n : R) * p ^ 2 := dvd_mul_right _ _
    have u1 := ((he _ hnm).of_dvd d0).unique (he n hn)
    have u2 := hσdvd n _ u1
    rw [map_sub] at u2
    have u3 : (n : R) * p ^ 2 ∣ e (n * m) * w (n * m) - e n * w n := by
      have := ((u1.mul_left (w (n * m) - w (n * m) * s * w n)).add
        ((d0.trans (hw _ hnm)).mul_left (w n))).sub ((hw n hn).mul_left (w (n * m)))
      have := this.add (u1.mul_left (w n))
      convert this using 1
      ring
    have u4 := hσdvd n _ u3
    rw [map_sub, map_mul, map_mul] at u4
    obtain ⟨c, hc⟩ := (u1.add u2).mul_left
      (-((1 - e (n * m) - σ (e (n * m))) + (1 - e n - σ (e n))))
    obtain ⟨y, hy⟩ := hsq ((c * p) • a)
    have u5 : (1 - e (n * m) - σ (e (n * m))) • π (n * m) a - (1 - e n - σ (e n)) • π n a =
        (n : R) • y := by
      apply hi
      rw [map_sub, map_smul, map_smul, map_smul, hπ, hπ, hy, smul_smul, smul_smul, smul_smul, smul_smul,
        ← sub_smul]
      congr 1
      linear_combination (p : R) * hc
    have : G (n * m) a - G n a = (e (n * m) - e n) • φ a +
        (σ (e (n * m)) * σ (w (n * m)) - σ (e n) * σ (w n)) • χ a + (n : R) • y := by
      rw [← u5]
      simp only [G, LinearMap.add_apply, LinearMap.smul_apply]
      module
    rw [this]
    exact add_mem (add_mem (smul_mem_mults (d.trans u1) _) (smul_mem_mults (d.trans u4) _))
      (smul_mem_mults dvd_rfl _)
  · obtain ⟨y, hy⟩ := mem_mults.1 ((hinv n hn).1 b)
    rw [hGH, ← map_sub, hy, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]
    exact dvd_mul_right _ _
  · have d : (n : R) ∣ (n : R) * p ^ 2 := dvd_mul_right _ _
    have hen : (n : R) ∣ e n := by
      have he' := (he n hn).of_dvd d
      refine dvd_of_idem he'.1 fun q hq hN => he'.2.2 q hq hN fun hqP => hP.ne_top ?_
      obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 hnp).map (Int.castRingHom R)
      rw [Ideal.eq_top_iff_one, ← huv]
      exact P.add_mem (P.mul_mem_left _ (by simpa [hqP] using hN)) (P.mul_mem_left _ (by simpa using hpP))
    have hen' : (n : R) ∣ σ (e n) := by simpa using map_dvd σ hen
    have : i (G n a) - (p : R) • a = e n • i (φ a) + (σ (e n) * σ (w n)) • i (χ a) +
        ((e n + σ (e n)) * ((e n + σ (e n) - 2) * p)) • a := by
      simp only [G, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, hπ]
      module
    rw [this]
    exact add_mem (add_mem (smul_mem_mults hen _) (smul_mem_mults (hen'.mul_right _) _))
      (smul_mem_mults ((hen.add hen').mul_right _) _)
end GlobalTheory.HeckeTate
