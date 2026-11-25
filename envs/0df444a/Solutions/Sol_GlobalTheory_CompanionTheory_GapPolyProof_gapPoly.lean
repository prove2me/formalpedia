-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapPolyProof.gapPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:34:59.190661+00:00
-- url     : https://prove2.me/submissions/bbb71289-dc82-49eb-888b-58e32d53c8f2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CountLeOfDvd
import Theorems.Thm_GlobalTheory_CompanionTheory_GapPolyProof_pow_dvd_dd
import Theorems.Thm_GlobalTheory_CompanionTheory_GapPolyProof_count_le_of_dvd
import Theorems.Thm_GlobalTheory_CompanionTheory_GapPolyProof_rel_of_pair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapPolyProof
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
namespace GlobalTheory.CompanionTheory.GapPolyProof
theorem _root_.solution : PositivityTheory.Rg.Rs.GapPoly := by
  intro q n hq V _ _ B W U Z S hpos hcard h0S hZ0 hUW hZW hexp hZtop hrec hpair z hz
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)

  obtain ⟨s, hsdef⟩ : ∃ s : ℂ, s = (q : ℂ) ^ (((2 : ℕ) : ℂ)⁻¹) := ⟨_, rfl⟩
  have hs2 : s ^ 2 = q := by rw [hsdef]; exact Complex.cpow_nat_inv_pow _ (by norm_num)
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs2; exact hq0 (by simpa using hs2.symm)
  have hsn : ‖s‖ ^ 2 = q := by
    rw [← norm_pow, hs2]; simp
  have hpow : ∀ j ≤ n + 1, (q : ℂ) ^ (((j : ℂ) * (((n + 1 : ℕ) : ℂ) - j)) / 2) = s ^ (j * (n + 1 - j)) := by
    intro j hj
    have : ((j : ℂ) * (((n + 1 : ℕ) : ℂ) - j)) / 2 = ((j * (n + 1 - j) : ℕ) : ℂ) * (((2 : ℕ) : ℂ)⁻¹) := by
      rw [Nat.cast_mul, Nat.cast_sub hj]; push_cast; ring
    rw [this, Complex.cpow_nat_mul, ← hsdef]

  obtain ⟨b, hbdef⟩ : ∃ b : ℕ → ℂ, ∀ j, b j = (-1) ^ j * s ^ (j * (j - 1)) * (s ^ (n * j))⁻¹ := ⟨_, fun _ => rfl⟩
  have hbtop : ∀ j ≤ n + 1, b j * s ^ (j * (n + 1 - j)) = (-1) ^ j := by
    intro j hj
    have e : j * (j - 1) + j * (n + 1 - j) = n * j := by
      obtain ⟨i, hi⟩ := Nat.exists_eq_add_of_le hj
      cases j with
      | zero => simp
      | succ j =>
        have : n + 1 - (j + 1) = i := by omega
        have hn' : n = j + i := by omega
        rw [this, hn']; simp only [Nat.add_sub_cancel]; ring
    rw [hbdef, mul_assoc, mul_assoc, mul_comm (s ^ (n * j))⁻¹, ← mul_assoc (s ^ (j * (j - 1))), ← pow_add, e]
    rw [mul_inv_cancel₀ (pow_ne_zero _ hs0), mul_one]
  have hbrec : ∀ j, b (j + 1) = -((s ^ n)⁻¹ * b j * (q : ℂ) ^ j) := by
    intro j
    have e : (j + 1) * (j + 1 - 1) = j * (j - 1) + 2 * j := by
      cases j with
      | zero => simp
      | succ j => simp only [Nat.add_sub_cancel]; ring
    rw [hbdef, hbdef, e, pow_add, ← hs2, ← pow_mul, Nat.mul_succ, pow_add s (n * j) n, mul_inv]
    ring

  obtain ⟨Ee, hEe⟩ : ∃ Ee : Submodule ℂ V, Ee = Submodule.span ℂ (Z '' (Finset.range (n + 1) : Set ℕ)) := ⟨_, rfl⟩
  have : FiniteDimensional ℂ Ee := by
    rw [hEe]; exact FiniteDimensional.span_of_finite ℂ ((Finset.finite_toSet _).image _)
  have hEmem : ∀ j ≤ n + 1, Z j ∈ Ee := by
    intro j hj
    rcases Nat.lt_or_ge j (n + 1) with h | h
    · rw [hEe]; exact Submodule.subset_span ⟨j, by simpa using h, rfl⟩
    · have : j = n + 1 := by omega
      rw [this, hZtop]; exact Ee.zero_mem
  have hEW : ∀ y ∈ Ee, y ∈ W := by
    intro y hy
    have : Ee ≤ W := by
      rw [hEe, Submodule.span_le]; rintro _ ⟨j, _, rfl⟩; exact hZW j
    exact this hy
  have hEU : ∀ y ∈ Ee, U y ∈ Ee := by
    have : Ee ≤ Ee.comap U := by
      conv_lhs => rw [hEe]
      rw [Submodule.span_le]
      rintro _ ⟨j, hj, rfl⟩
      have hj' : j ≤ n := by simpa using hj
      show U (Z j) ∈ Ee
      rw [hrec j hj']
      exact Ee.smul_mem _ (Ee.sub_mem (Ee.smul_mem _ (hEmem 0 (by omega))) (hEmem _ (by omega)))
    exact fun y hy => this hy
  obtain ⟨T, hT⟩ : ∃ T : Module.End ℂ Ee, ∀ y : Ee, ((T y : Ee) : V) = (s ^ n)⁻¹ • U y :=
    ⟨(s ^ n)⁻¹ • U.restrict hEU, fun y => rfl⟩
  obtain ⟨Zs, hZs⟩ : ∃ Zs : ℕ → Ee, ∀ j ≤ n + 1, ((Zs j : Ee) : V) = Z j :=
    ⟨fun j => if h : j ≤ n + 1 then ⟨Z j, hEmem j h⟩ else 0, fun j hj => by simp [hj]⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : Ee →ₗ[ℂ] ℂ, ∀ y : Ee, φ y = B y (Z 0) :=
    ⟨{ toFun := fun y => B y (Z 0), map_add' := by simp, map_smul' := by simp }, fun _ => rfl⟩
  have h0 : (fun j => b j • Zs j) 0 = Zs 0 := by simp [hbdef]
  have hn : (fun j => b j • Zs j) (n + 1) = 0 := by
    apply Subtype.ext
    simp [hZs (n + 1) le_rfl, hZtop]
  have hrec' : ∀ j ≤ n, (fun j => b j • Zs j) (j + 1) - T ((fun j => b j • Zs j) j) =
      (((-1 : ℂ) ^ (j + 1)) * S.esymm (j + 1)) • Zs 0 := by
    intro j hj
    apply Subtype.ext
    have h1 := hbtop (j + 1) (by omega)
    have h2 := hbrec j
    simp only [map_smul, Submodule.coe_sub, Submodule.coe_smul, hT, hZs (j + 1) (by omega), hZs j (by omega),
      hZs 0 (by omega), hrec j hj, hpow (j + 1) (by omega)]
    have key : ∀ w : V, b j • (s ^ n)⁻¹ • (q : ℂ) ^ j • w = (-b (j + 1)) • w := by
      intro w
      rw [smul_smul, smul_smul, h2]
      congr 1
      ring
    rw [key, ← h1]
    module
  have hzE : ¬ T.HasEigenvalue z := by
    intro h
    obtain ⟨y, hy⟩ := h.exists_hasEigenvector
    have hy1 := congrArg (Subtype.val) hy.apply_eq_smul
    rw [hT] at hy1
    have hy0 : (y : V) ≠ 0 := fun h => hy.2 (Subtype.ext h)
    have hUy : U y = (s ^ n * z) • (y : V) := by
      calc U y = s ^ n • (s ^ n)⁻¹ • U y := by
            rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hs0), one_smul]
        _ = _ := by rw [hy1, Submodule.coe_smul, smul_smul]
    have hr := hpos y hy0
    have h1 := hexp y (hEW y y.2)
    have h2 : (B ((s ^ n * z) • (y : V)) ((s ^ n * z) • (y : V))).re =
        ‖s ^ n * z‖ ^ 2 * (B y y).re := by
      simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [← mul_assoc, mul_comm ((starRingEnd ℂ) _), Complex.mul_conj, Complex.re_ofReal_mul,
        Complex.normSq_eq_norm_sq]
    rw [hUy, h2] at h1
    have h3 := le_of_mul_le_mul_right h1 hr
    have h4 : ‖s ^ n * z‖ ^ 2 = (q : ℝ) ^ n * ‖z‖ ^ 2 := by
      rw [norm_mul, norm_pow, mul_pow, ← pow_mul, mul_comm n 2, pow_mul, hsn]
    have hz2 : ‖z‖ ^ 2 < (q : ℝ)⁻¹ := by
      have := pow_lt_pow_left₀ hz (norm_nonneg z) two_ne_zero
      rw [← Real.rpow_natCast ((q : ℝ) ^ (-(1 / 2) : ℝ)), ← Real.rpow_mul hqR.le] at this
      norm_num at this
      rw [Real.rpow_neg_one] at this
      simpa using this
    have h5 : (q : ℝ) ^ ((n : ℝ) - 1) = (q : ℝ) ^ n * (q : ℝ)⁻¹ := by
      rw [Real.rpow_sub_one hqR.ne', Real.rpow_natCast, div_eq_mul_inv]
    rw [h4, h5] at h3
    exact absurd h3 (not_le.2 (mul_lt_mul_of_pos_left hz2 (pow_pos hqR n)))
  have hc : B (Z 0) (Z 0) ≠ 0 := by
    intro h
    have := hpos _ hZ0
    rw [h] at this
    simp at this
  refine count_le_of_dvd S q (B (Z 0) (Z 0)) ((q : ℂ) ^ (n + 1) - 1) z hq0 hc
    (dd n (fun j => b j • Zs j) φ) (pow_dvd_dd S n hcard T _ (Zs 0) h0 hn hrec' φ z hzE)
    (rel_of_pair S n hcard q _ _ _ φ ?_)
  intro j hj
  have hp := hpair j (by omega)
  rw [hpow j (by omega)] at hp
  show _ * φ (b j • Zs j) = _
  rw [map_smul, hφ, hZs j (by omega), smul_eq_mul, ← hbtop j (by omega)]
  calc ((q : ℂ) ^ (n + 1) - 1) * (b j * B (Z j) (Z 0))
      = b j * (((q : ℂ) ^ (n + 1) - 1) * B (Z j) (Z 0)) := by ring
    _ = _ := by rw [hp]; ring
end GlobalTheory.CompanionTheory.GapPolyProof
