-- Prove2me | solution 1 for KonyaginUnitVectors.Alon.alon_system
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T14:27:01.331167+00:00
-- url     : https://prove2.me/submissions/b9224560-a981-452d-a034-2c6bc23ed9d6

import Mathlib
import Definitions.Def_KonyaginUnitVectors_AlonConstruction
import Theorems.Thm_KonyaginUnitVectors_Alon_fourier_system
import Theorems.Thm_KonyaginUnitVectors_Alon_S_structure
import Theorems.Thm_KonyaginUnitVectors_Alon_S_spectrum

set_option autoImplicit false

/-!
The Alon-type system of unit vectors for `q = |F| ≥ 256`: assembled from the Fourier construction
(`fourier_system`), the structure of the connection set `S` (`S_structure`) and its spectral bound (`S_spectrum`).
-/

open KonyaginUnitVectors.Alon

theorem solution (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (hq : 256 ≤ Fintype.card F) :
    ∃ u : F × F × F → EuclideanSpace ℝ (F × F × F),
      (∀ g, ‖u g‖ = 1) ∧
      (∀ g h k : F × F × F, g ≠ h → h ≠ k → g ≠ k →
        inner ℝ (u g) (u h) = 0 ∨ inner ℝ (u h) (u k) = 0 ∨ inner ℝ (u g) (u k) = 0) ∧
      (1 / 13 : ℝ) * ((Fintype.card F : ℝ) ^ 3) ^ ((2 : ℝ) / 3) ≤ ‖∑ g, u g‖ := by
  classical
  obtain ⟨hinj, hne, htri, hcard, hpart⟩ := S_structure F
  obtain ⟨hspec, hdiff⟩ := S_spectrum F hinj
  set q : ℝ := (Fintype.card F : ℝ) with hq_def
  have hq256 : (256 : ℝ) ≤ q := by rw [hq_def]; exact_mod_cast hq
  set s : ℝ := Real.sqrt q with hs_def
  have hs2 : s ^ 2 = q := Real.sq_sqrt (by linarith)
  have hs16 : 16 ≤ s := by
    rw [hs_def]
    apply Real.le_sqrt_of_sq_le
    linarith
  set R : ℝ := 8 * s + 1 with hR
  have hRpos : 0 < R := by positivity
  set κ : ℝ := 4 / R ^ 2 with hκdef
  have hκpos : 0 < κ := by positivity
  have hκ : ∀ w : F × F × F, 0 ≤ 1 + κ * ∑ t ∈ Sset F, chi F w t := by
    intro w
    have h1 : -(R ^ 2 / 4) ≤ ∑ t ∈ Sset F, chi F w t := hspec w
    have h2 : κ * (-(R ^ 2 / 4)) ≤ κ * ∑ t ∈ Sset F, chi F w t :=
      mul_le_mul_of_nonneg_left h1 hκpos.le
    have h3 : κ * (-(R ^ 2 / 4)) = -1 := by
      rw [hκdef]; field_simp
    linarith
  obtain ⟨u, hgram, hnorm⟩ := fourier_system F (Sset F) κ hκ
  have hdbl : ∀ g : F × F × F, g + g = 0 := by
    intro g
    ext <;> simp [CharTwo.add_self_eq_zero]
  have h0 : (0 : F × F × F) ∉ Sset F := by
    intro h0
    simp only [Sset, Finset.mem_image] at h0
    obtain ⟨p, hp, hp0⟩ := h0
    exact hne p hp hp0
  refine ⟨u, ?_, ?_, ?_⟩
  · intro g
    have h := hgram g g
    rw [if_pos rfl, hdbl g, if_neg h0, mul_zero, add_zero] at h
    have h' : ‖u g‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact h
    have hnn : 0 ≤ ‖u g‖ := norm_nonneg _
    nlinarith
  · intro g h k hgh hhk hgk
    by_contra hcon
    push Not at hcon
    obtain ⟨c1, c2, c3⟩ := hcon
    have mem : ∀ a b : F × F × F, a ≠ b → inner ℝ (u a) (u b) ≠ 0 → a + b ∈ Sset F := by
      intro a b hab hne'
      have e := hgram a b
      rw [if_neg hab] at e
      by_contra hnot
      rw [if_neg hnot] at e
      apply hne'
      rw [e]; ring
    have m1 := mem g h hgh c1
    have m2 := mem h k hhk c2
    have m3 := mem g k hgk c3
    apply htri _ m1 _ m2 _ m3
    have : g + h + (h + k) + (g + k) = (g + g) + (h + h) + (k + k) := by abel
    rw [this, hdbl g, hdbl h, hdbl k]; simp
  · -- the norm bound
    set m0 : ℝ := ((W0 F).card : ℝ) with hm0
    set m1 : ℝ := ((W1 F).card : ℝ) with hm1
    have hsum : m0 + m1 = q - 1 := by
      have : ((W0 F).card : ℝ) + ((W1 F).card : ℝ) + 1 = (Fintype.card F : ℝ) := by exact_mod_cast hpart
      linarith
    have hdiff' : |m0 - m1| ≤ R := hdiff
    have hsq : (m0 - m1) ^ 2 ≤ R ^ 2 := by
      have := sq_le_sq' (abs_le.mp hdiff').1 (abs_le.mp hdiff').2
      exact this
    have h4 : 4 * (m0 * m1) ≥ (q - 1) ^ 2 - R ^ 2 := by nlinarith
    have hR2 : R ^ 2 ≤ 81 * q := by nlinarith
    have hhalf : (q - 1) ^ 2 - R ^ 2 ≥ q ^ 2 / 2 := by nlinarith
    have hk : q / 162 ≤ κ * (m0 * m1) := by
      rw [hκdef, div_mul_eq_mul_div, div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    have hcardS : ((Sset F).card : ℝ) = m0 * m1 := by rw [hcard]; push_cast; ring
    have hn : ‖∑ g, u g‖ ^ 2 = q ^ 3 * (1 + κ * (m0 * m1)) := by
      rw [hnorm, hcardS]
    have hrp : ((Fintype.card F : ℝ) ^ 3) ^ ((2 : ℝ) / 3) = q ^ 2 := by
      rw [← hq_def]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    rw [hrp]
    have hnn : 0 ≤ ‖∑ g, u g‖ := norm_nonneg _
    have hlow : (1 / 13 * q ^ 2) ^ 2 ≤ ‖∑ g, u g‖ ^ 2 := by
      rw [hn]
      have : q ^ 3 * (q / 162) ≤ q ^ 3 * (κ * (m0 * m1)) := mul_le_mul_of_nonneg_left hk (by positivity)
      nlinarith [pow_pos (show (0:ℝ) < q by linarith) 4]
    exact le_of_sq_le_sq hlow hnn |>.trans_eq rfl

#print axioms solution
