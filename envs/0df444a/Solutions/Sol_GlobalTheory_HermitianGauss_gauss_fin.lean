-- Prove2me | solution 1 for GlobalTheory.HermitianGauss.gauss_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:06:01.64286+00:00
-- url     : https://prove2.me/submissions/191c9765-b444-4182-be0f-7d35710adb87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussSumNondegenerateFiniteHermitianModule
import Theorems.Thm_GlobalTheory_HermitianGauss_mem_pts
import Theorems.Thm_GlobalTheory_HermitianGauss_card_pts_pos
import Theorems.Thm_GlobalTheory_HermitianGauss_card_pts_dvd
import Theorems.Thm_GlobalTheory_HermitianGauss_eq_of_card_pts
import Theorems.Thm_GlobalTheory_HermitianGauss_sum_pts_add
import Theorems.Thm_GlobalTheory_HermitianGauss_sum_char
import Theorems.Thm_GlobalTheory_HermitianGauss_finite_quot
import Theorems.Thm_GlobalTheory_HermitianGauss_sum_sup
import Theorems.Thm_GlobalTheory_HermitianGauss_card_sup
import Theorems.Thm_GlobalTheory_HermitianGauss_card_perp
import Theorems.Thm_GlobalTheory_HermitianGauss_quad_add
import Theorems.Thm_GlobalTheory_NormFormGauss_gauss_quotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermitianGauss.mem_pts
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
namespace GlobalTheory.HermitianGauss
section Fin
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype M]
variable {σ : R →+* R} {β : M → M → ℂ}
private theorem exists_mem_not_mem_annihilator_maximal_of_lt {C B : Submodule R M} (hCB : C ≤ B) (hne : C ≠ B) :
    ∃ x ∈ B, x ∉ C ∧ ∃ P : Ideal R, P.IsMaximal ∧ ∀ r : R, r • x ∈ C ↔ r ∈ P := by
  have hne' : (pts B \ pts C).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h
    exact hne (le_antisymm hCB fun y hy => mem_pts.mp (h (mem_pts.mpr hy)))
  obtain ⟨x, hx, hmin⟩ :=
    Finset.exists_min_image _ (fun x => (pts (C ⊔ Submodule.span R {x})).card) hne'
  rw [Finset.mem_sdiff, mem_pts, mem_pts] at hx
  let I : Ideal R := Submodule.comap (LinearMap.toSpanSingleton R M x) C
  have hI : ∀ r : R, r ∈ I ↔ r • x ∈ C := fun r => by
    simp [I, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
  refine ⟨x, hx.1, hx.2, I, ?_, fun r => (hI r).symm⟩
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h1 => hx.2 (by simpa using (hI 1).mp h1), fun J r hIJ hr hrJ => ?_⟩
  have hrx : r • x ∈ pts B \ pts C := by
    rw [Finset.mem_sdiff, mem_pts, mem_pts]
    exact ⟨B.smul_mem r hx.1, fun h => hr ((hI r).mpr h)⟩
  have h1 := hmin _ hrx
  have hle : C ⊔ Submodule.span R {r • x} ≤ C ⊔ Submodule.span R {x} := by
    refine sup_le_sup_left ?_ C
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  have heq := eq_of_card_pts hle h1
  have hxm : x ∈ C ⊔ Submodule.span R {r • x} := by
    rw [heq]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  obtain ⟨c, hc, z, hz, hcz⟩ := Submodule.mem_sup.mp hxm
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have h2 : (1 - s * r) ∈ I := by
    rw [hI]
    have e : (1 - s * r) • x = c := by
      rw [sub_smul, one_smul, mul_smul, sub_eq_iff_eq_add]
      exact hcz.symm
    rw [e]
    exact hc
  have h3 := J.add_mem (hIJ h2) (J.mul_mem_left s hrJ)
  simpa using h3
private theorem sum_pts_eq_sum_pts_orth {w : R} (hσ : ∀ r, σ (σ r) = r) (hw : w + σ w = 1)
    (hadd : ∀ x y z, β (x + y) z = β x z * β y z) (hsym : ∀ x y, β x y = β y x)
    (hadj : ∀ (r : R) x y, β (r • x) y = β x (σ r • y)) {B N N' : Submodule R M} (hNB : N ≤ B)
    (hN' : ∀ y, y ∈ N' ↔ y ∈ B ∧ ∀ z ∈ N, β y z = 1) (hQ : ∀ n ∈ N, β (w • n) n = 1) :
    ∑ y ∈ pts B, β (w • y) y = ∑ y ∈ pts N', β (w • y) y := by
  have hr : ∀ a b c, β a (b + c) = β a b * β a c := fun a b c => by
    rw [hsym a, hadd, hsym b, hsym c]
  have hN0 : ((pts N).card : ℂ) ≠ 0 := by exact_mod_cast (card_pts_pos N).ne'
  have step1 : ∀ n ∈ pts N, ∑ y ∈ pts B, β (w • (y + n)) (y + n) = ∑ y ∈ pts B, β (w • y) y :=
    fun n hn => sum_pts_add B (fun y => β (w • y) y) (hNB (mem_pts.mp hn))
  have step2 : ∀ y ∈ pts B, ∑ n ∈ pts N, β (w • (y + n)) (y + n) =
      β (w • y) y * (if ∀ z ∈ N, β y z = 1 then ((pts N).card : ℂ) else 0) := by
    intro y _
    have e : ∀ n ∈ pts N, β (w • (y + n)) (y + n) = β (w • y) y * β y n := by
      intro n hn
      rw [quad_add hσ hw hadd hsym hadj, hQ n (mem_pts.mp hn), mul_one, hsym n y]
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, sum_char N (β y) (hr y)]
  apply mul_left_cancel₀ hN0
  calc ((pts N).card : ℂ) * ∑ y ∈ pts B, β (w • y) y
      = ∑ n ∈ pts N, ∑ y ∈ pts B, β (w • (y + n)) (y + n) := by
        rw [Finset.sum_congr rfl step1, Finset.sum_const, nsmul_eq_mul]
    _ = ∑ y ∈ pts B, ∑ n ∈ pts N, β (w • (y + n)) (y + n) := Finset.sum_comm
    _ = ∑ y ∈ pts B, β (w • y) y * (if ∀ z ∈ N, β y z = 1 then ((pts N).card : ℂ) else 0) :=
        Finset.sum_congr rfl step2
    _ = ((pts N).card : ℂ) * ∑ y ∈ pts N', β (w • y) y := by
        rw [Finset.mul_sum]
        simp_rw [mul_ite, mul_zero]
        rw [← Finset.sum_filter]
        have hf : (pts B).filter (fun y => ∀ z ∈ N, β y z = 1) = pts N' := by
          ext y
          simp [pts, hN']
        rw [hf]
        exact Finset.sum_congr rfl fun y _ => mul_comm _ _
end Fin
end GlobalTheory.HermitianGauss
end

set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.HermitianGauss
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype M]
variable {σ : R →+* R} {β : M → M → ℂ}
namespace GlobalTheory.HermitianGauss
theorem _root_.solution {w : R} (hσ : ∀ r, σ (σ r) = r) (hw : w + σ w = 1) {lam : ℕ →* ℂ} (hlam : GoodNorm σ lam)
    (hadd : ∀ x y z, β (x + y) z = β x z * β y z) (hsym : ∀ x y, β x y = β y x)
    (hadj : ∀ (r : R) x y, β (r • x) y = β x (σ r • y)) (h0 : ∀ y, β 0 y = 1) (n : ℕ) :
    ∀ B C : Submodule R M, C ≤ B → (∀ x ∈ B, x ∈ C ↔ ∀ y ∈ B, β x y = 1) → (pts B).card = n * (pts C).card →
      ∑ y ∈ pts B, β (w • y) y = (pts C).card * lam n ∧ lam n ^ 2 = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih => ?_
  intro B C hCB hrad hcard
  have hr : ∀ a b c, β a (b + c) = β a b * β a c := fun a b c => by
    rw [hsym a, hadd, hsym b, hsym c]
  have hC1 : ∀ c ∈ C, ∀ y ∈ B, β c y = 1 := fun c hc y hy => (hrad c (hCB hc)).mp hc y hy
  have hQC : ∀ c ∈ C, β (w • c) c = 1 := fun c hc => by
    rw [hsym]; exact hC1 c hc _ (B.smul_mem w (hCB hc))
  have hCpos := card_pts_pos C
  by_cases hBC : C = B
  · subst hBC
    have hn : n = 1 := by
      have h1 : n * (pts C).card = 1 * (pts C).card := by rw [← hcard, one_mul]
      exact Nat.eq_of_mul_eq_mul_right hCpos h1
    subst hn
    rw [Finset.sum_congr rfl fun c hc => hQC c (mem_pts.mp hc)]
    simp
  obtain ⟨x, hxB, hxC, P, hPm, hP⟩ := exists_mem_not_mem_annihilator_maximal_of_lt hCB hBC
  haveI : Finite (R ⧸ P) := finite_quot hP
  letI : Fintype (R ⧸ P) := Fintype.ofFinite _
  set q := Fintype.card (R ⧸ P)
  have hqc : Nat.card (R ⧸ P) = q := Nat.card_eq_fintype_card
  have hq2 : 2 ≤ q := by
    haveI : P.IsMaximal := hPm
    exact Fintype.one_lt_card
  obtain ⟨hlq, hlqσ⟩ := hlam.2 P hPm inferInstance
  rw [hqc] at hlq hlqσ
  set N := C ⊔ Submodule.span R {x}
  have hNcard : (pts N).card = q * (pts C).card := card_sup hP
  have hCN : C ≤ N := le_sup_left
  have hxN : x ∈ N := Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  have hNB : N ≤ B := sup_le hCB (by rw [Submodule.span_le, Set.singleton_subset_iff]; exact hxB)
  set N' := perp hadd hadj h0 B N
  have hN' : ∀ y, y ∈ N' ↔ y ∈ B ∧ ∀ z ∈ N, β y z = 1 := fun y => Iff.rfl
  have hperp := card_perp hadd hsym hCN hNB hrad hN'
  have hCN' : C ≤ N' := fun c hc => (hN' c).mpr ⟨hCB hc, fun z hz => hC1 c hc z (hNB hz)⟩
  have hN'B : N' ≤ B := fun y hy => ((hN' y).mp hy).1
  have hBpos := card_pts_pos B
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, zero_mul] at hcard; omega
    · exact h
  have hmemN : ∀ z ∈ N, ∃ c ∈ C, ∃ a : R, c + a • x = z := by
    intro z hz
    obtain ⟨c, hc, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact ⟨c, hc, a, rfl⟩
  by_cases hiso : ∀ r : R, β x (r • x) = 1
  · have hxN' : x ∈ N' := (hN' x).mpr ⟨hxB, fun z hz => by
      obtain ⟨c, hc, a, rfl⟩ := hmemN z hz
      rw [hr, hiso, mul_one, hsym]
      exact hC1 c hc x hxB⟩
    have hNN' : N ≤ N' :=
      sup_le hCN' (by rw [Submodule.span_le, Set.singleton_subset_iff]; exact hxN')
    have hQN : ∀ z ∈ N, β (w • z) z = 1 := by
      intro z hz
      obtain ⟨c, hc, a, rfl⟩ := hmemN z hz
      rw [quad_add hσ hw hadd hsym hadj, hQC c hc, one_mul, hsym (a • x) c,
        hC1 c hc _ (B.smul_mem a hxB), mul_one, smul_smul, hadj, smul_smul]
      exact hiso _
    obtain ⟨m, hm⟩ := card_pts_dvd hNN'
    have hn : n = q * q * m := by
      have h1 : (pts C).card * (n * (pts C).card) = q * (pts C).card * m * (q * (pts C).card) := by
        rw [← hcard, hperp, hm, hNcard]
      have h2 : n * ((pts C).card * (pts C).card) = q * q * m * ((pts C).card * (pts C).card) := by
        calc n * ((pts C).card * (pts C).card) = (pts C).card * (n * (pts C).card) := by ring
          _ = q * (pts C).card * m * (q * (pts C).card) := h1
          _ = q * q * m * ((pts C).card * (pts C).card) := by ring
      exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hCpos hCpos) h2
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hn; omega
      · exact h
    have hmn : m < n := by
      have h4 : 2 * m ≤ q * q * m := Nat.mul_le_mul_right m (by nlinarith)
      omega
    have hrad' : ∀ y ∈ N', y ∈ N ↔ ∀ z ∈ N', β y z = 1 := by
      intro y hy
      constructor
      · intro hyN z hz
        rw [hsym]
        exact ((hN' z).mp hz).2 y hyN
      · intro h
        have hN'' : ∀ u, u ∈ perp hadd hadj h0 B N' ↔ u ∈ B ∧ ∀ z ∈ N', β u z = 1 := fun u => Iff.rfl
        have h2 := card_perp hadd hsym hCN' hN'B hrad hN''
        have hNN'' : N ≤ perp hadd hadj h0 B N' := fun u hu =>
          (hN'' u).mpr ⟨hNB hu, fun z hz => by rw [hsym]; exact ((hN' z).mp hz).2 u hu⟩
        have hc : (pts (perp hadd hadj h0 B N')).card ≤ (pts N).card := by
          have h3 : (pts (perp hadd hadj h0 B N')).card * (pts N').card = (pts N).card * (pts N').card := by
            rw [← h2, hperp, mul_comm]
          exact (Nat.eq_of_mul_eq_mul_right (card_pts_pos N') h3).le
        have h4 := eq_of_card_pts hNN'' hc
        rw [h4]
        exact (hN'' y).mpr ⟨hN'B hy, h⟩
    obtain ⟨hs, hl⟩ := ih m hmn N' N hNN' hrad' (by rw [hm, mul_comm])
    rw [sum_pts_eq_sum_pts_orth hσ hw hadd hsym hadj hNB hN' hQN, hs, hNcard, hn]
    have hlq2 : lam q * lam q = q := by rw [← sq]; exact hlq
    refine ⟨?_, ?_⟩
    · rw [map_mul, map_mul, hlq2]
      push_cast
      ring
    · rw [map_mul, map_mul, mul_pow, mul_pow, hl, hlq]
      push_cast
      ring
  · push Not at hiso
    obtain ⟨r0, hr0⟩ := hiso
    let χ : R → ℂ := fun t => β x (t • x)
    have hχadd : ∀ s t, χ (s + t) = χ s * χ t := fun s t => by
      simp only [χ]
      rw [add_smul, hr]
    have hχ0 : χ 0 = 1 := by
      simp only [χ]
      rw [zero_smul, hsym]
      exact h0 x
    have hχP : ∀ t ∈ P, χ t = 1 := fun t ht => by
      simp only [χ]
      rw [hsym]
      exact hC1 _ ((hP t).mpr ht) x hxB
    have hχσ : ∀ t, χ (σ t) = χ t := fun t => by
      simp only [χ]
      rw [← hadj, hsym]
    have hσP : ∀ p ∈ P, σ p ∈ P := by
      intro p hp
      by_contra hsp
      obtain ⟨y, i, hi, hyi⟩ := hPm.exists_inv hsp
      apply hr0
      show χ r0 = 1
      have e1 : r0 = r0 * i + σ (σ (r0 * y) * p) := by
        rw [map_mul, hσ]
        linear_combination (-r0) * hyi
      rw [e1, hχadd, hχP _ (P.mul_mem_left r0 hi), hχσ, hχP _ (P.mul_mem_left _ hp), mul_one]
    obtain ⟨hlqv, hex⟩ := hlqσ hσP
    have hG := NormFormGauss.gauss_quotient σ w hσ hw P hPm inferInstance hσP hex χ hχadd hχ0 hχP hχσ ⟨r0, hr0⟩
    rw [hqc, finsum_eq_sum_of_fintype] at hG
    have hP' : ∀ r, r • x ∈ N' ↔ r ∈ P := by
      intro r
      constructor
      · intro h
        by_contra hrP
        have hsr : σ r ∉ P := fun h' => hrP (by rw [← hσ r]; exact hσP _ h')
        obtain ⟨y, i, hi, hyi⟩ := hPm.exists_inv hsr
        apply hr0
        show χ r0 = 1
        have e1 : r0 = r0 * i + σ r * (y * r0) := by linear_combination (-r0) * hyi
        rw [e1, hχadd, hχP _ (P.mul_mem_left r0 hi), one_mul]
        simp only [χ]
        rw [← smul_smul, ← hadj]
        exact ((hN' _).mp h).2 _ (N.smul_mem _ hxN)
      · intro hrP
        refine (hN' _).mpr ⟨B.smul_mem r hxB, fun z hz => ?_⟩
        obtain ⟨c, hc, a, rfl⟩ := hmemN z hz
        rw [hr, hC1 _ ((hP r).mpr hrP) c (hCB hc), one_mul, hadj, smul_smul]
        exact hχP _ (P.mul_mem_right a (hσP r hrP))
    have hsupB : N' ⊔ Submodule.span R {x} = B := by
      apply eq_of_card_pts (sup_le hN'B (by rw [Submodule.span_le, Set.singleton_subset_iff]; exact hxB))
      rw [card_sup hP']
      have h1 : (pts B).card * (pts C).card = q * (pts N').card * (pts C).card := by
        rw [mul_comm, hperp, hNcard]
        ring
      exact (Nat.eq_of_mul_eq_mul_right hCpos h1).le
    obtain ⟨m, hm⟩ := card_pts_dvd hCN'
    have hnqm : n = q * m := by
      have h1 : n * (pts C).card * (pts C).card = q * m * (pts C).card * (pts C).card := by
        calc n * (pts C).card * (pts C).card = (pts C).card * (pts B).card := by rw [hcard]; ring
          _ = (pts N').card * (pts N).card := hperp
          _ = q * m * (pts C).card * (pts C).card := by rw [hm, hNcard]; ring
      exact Nat.eq_of_mul_eq_mul_right hCpos (Nat.eq_of_mul_eq_mul_right hCpos h1)
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hnqm; omega
      · exact h
    have hmn : m < n := by
      have h4 : 2 * m ≤ q * m := Nat.mul_le_mul_right m hq2
      omega
    have hrad' : ∀ y ∈ N', y ∈ C ↔ ∀ z ∈ N', β y z = 1 := by
      intro y hy
      constructor
      · intro hyC z hz
        exact hC1 y hyC z (hN'B hz)
      · intro h
        refine (hrad y (hN'B hy)).mpr fun b hb => ?_
        rw [← hsupB] at hb
        obtain ⟨d, hd, u, hu, rfl⟩ := Submodule.mem_sup.mp hb
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
        rw [hr, h d hd, one_mul]
        exact ((hN' y).mp hy).2 _ (N.smul_mem a hxN)
    obtain ⟨hs, hl⟩ := ih m hmn N' C hCN' hrad' (by rw [hm, mul_comm])
    have hsum : ∑ y ∈ pts B, β (w • y) y = (∑ d ∈ pts N', β (w • d) d) *
        ∑ q' : R ⧸ P, χ (w * (Quotient.out q' : R) * σ (Quotient.out q' : R)) := by
      rw [← hsupB, sum_sup hP', Finset.sum_comm, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun q' _ => ?_
      have hdN' := mem_pts.mp hd
      rw [quad_add hσ hw hadd hsym hadj, hsym ((Quotient.out q' : R) • x) d,
        ((hN' d).mp hdN').2 _ (N.smul_mem _ hxN), mul_one]
      congr 1
      simp only [χ]
      rw [hsym, hadj, smul_smul, smul_smul]
      congr 2
      ring
    rw [hsum, hs, hG, hnqm, ← hlqv]
    refine ⟨?_, ?_⟩
    · rw [map_mul]
      push_cast
      ring
    · rw [map_mul, mul_pow, hl, hlq]
      push_cast
      ring
end GlobalTheory.HermitianGauss
