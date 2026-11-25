-- Prove2me | solution 1 for GlobalTheory.SW.Vac.vacuum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:14:26.837914+00:00
-- url     : https://prove2.me/submissions/ce6f0e6a-44f9-401c-9352-49631760bf74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
import Theorems.Thm_GlobalTheory_SW_Vac_pr_smul_left
import Theorems.Thm_GlobalTheory_SW_Vac_pr_zero_left
import Theorems.Thm_GlobalTheory_SW_Vac_pr_sub_left
import Theorems.Thm_GlobalTheory_SW_Vac_pr_smul_right
import Theorems.Thm_GlobalTheory_SW_Vac_pr_zero_right
import Theorems.Thm_GlobalTheory_SW_Vac_pr_int
import Theorems.Thm_GlobalTheory_SW_Vac_om_eq
import Theorems.Thm_GlobalTheory_SW_Vac_ex_add
import Theorems.Thm_GlobalTheory_SW_Vac_ex_zero
import Theorems.Thm_GlobalTheory_SW_Vac_ex_ne_zero
import Theorems.Thm_GlobalTheory_SW_Vac_ex_two_eq_one
import Theorems.Thm_GlobalTheory_SW_Vac_intM_smul
import Theorems.Thm_GlobalTheory_SW_Vac_exists_den
import Theorems.Thm_GlobalTheory_SW_Vac_exists_den_fg
import Theorems.Thm_GlobalTheory_SW_Vac_ip_smul_self
import Theorems.Thm_GlobalTheory_SW_Vac_fg_map
import Theorems.Thm_GlobalTheory_SW_Vac_fixed_iff
import Theorems.Thm_GlobalTheory_SW_Vac_fac_add
import Theorems.Thm_GlobalTheory_SW_Vac_exists_base
import Theorems.Thm_GlobalTheory_SW_Vac_exists_lift
import Theorems.Thm_GlobalTheory_T_schwartzBruhatInnerProduct_self_nonneg_bounds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Vac
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.Vac
theorem _root_.solution (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (A : AddSubgroup (Matrix κ ι ℚ × Matrix κ ι ℚ)) (ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ) : A.FG → (∀ y, y ∈ A ↔ ∀ y' ∈ A, ∃ m : ℤ, (∑ k, (y.1 k ⬝ᵥ y'.2 k - y'.1 k ⬝ᵥ y.2 k) : ℚ) = m) → (∀ y ∈ A, ‖ε y‖ = 1) → (∀ y ∈ A, ∀ y' ∈ A, ε (y + y') = ε y * ε y' * cexp (π * I * ((∑ k, (y.1 k ⬝ᵥ y'.2 k - y'.1 k ⬝ᵥ y.2 k) : ℚ) : ℂ))) → (∃ m : ℕ, 0 < m ∧ ∀ y ∈ A, ε (m • y) = 1) → ∃ v : Matrix κ ι ℚ → ℂ, IsSB v ∧ ip v v = 1 ∧ (∀ y ∈ A, ε y • heisS y.1 y.2 v = v) ∧ ∀ w, IsSB w → (∀ y ∈ A, ε y • heisS y.1 y.2 w = w) → ∃ c : ℂ, w = c • v := by
  classical
  intro hA hd hnorm hε ⟨m, hm, hm'⟩
  simp only [om_eq] at hd hε
  replace hε : ∀ y ∈ A, ∀ y' ∈ A, ε (y + y') = ε y * ε y' * ex (pr y.1 y'.2 - pr y'.1 y.2) := hε
  have hn : ∀ y ∈ A, ε y ≠ 0 := fun y hy h => by simpa [h] using hnorm y hy
  have h0 : ε 0 = 1 := by simpa using hm' 0 A.zero_mem
  obtain ⟨x₀, hx₀⟩ := exists_base A ε hA hε hm hm'
  simp only [fixed_iff]
  let v : Matrix κ ι ℚ → ℂ := fun x =>
    if h : ∃ y ∈ A, x = x₀ + y.2 then fac ε h.choose x else 0
  have hv : ∀ y ∈ A, v (x₀ + y.2) = fac ε y (x₀ + y.2) := by
    intro y hy
    have h : ∃ y' ∈ A, x₀ + y.2 = x₀ + y'.2 := ⟨y, hy, rfl⟩
    have e : v (x₀ + y.2) = fac ε h.choose (x₀ + y.2) := dif_pos h
    obtain ⟨hy', e'⟩ := h.choose_spec
    rw [e]
    generalize h.choose = y' at hy' e'
    have e2 : y' = y + (y'.1 - y.1, 0) := Prod.ext (by simp) (by simpa using e'.symm)
    have hmem : (y'.1 - y.1, 0) ∈ A := by
      have : (y'.1 - y.1, 0) = y' - y := by rw [eq_sub_iff_add_eq, add_comm]; exact e2.symm
      rw [this]; exact A.sub_mem hy' hy
    rw [e2, fac_add (hε _ hy _ hmem), add_sub_cancel_right]
    have : fac ε (y'.1 - y.1, 0) x₀ = 1 := by
      rw [← hx₀ _ hmem, fac, pr_zero_right, sub_zero]
    rw [this, mul_one]
  have hv0 : ∀ x, (¬ ∃ y ∈ A, x = x₀ + y.2) → v x = 0 := fun x h => dif_neg h
  have hvx : v x₀ = 1 := by
    have := hv 0 A.zero_mem
    simpa [fac, h0, pr_zero_right, ex_zero] using this
  have hfix : ∀ y ∈ A, ∀ x, fac ε y x * v (x - y.2) = v x := by
    intro y hy x
    by_cases h : ∃ y' ∈ A, x = x₀ + y'.2
    · obtain ⟨y', hy', rfl⟩ := h
      have e : x₀ + y'.2 - y.2 = x₀ + (y' - y).2 := by simp [add_sub_assoc]
      rw [hv _ hy', e, hv _ (A.sub_mem hy' hy), ← e, ← fac_add (hε _ hy _ (A.sub_mem hy' hy)),
        add_sub_cancel]
    · rw [hv0 _ h, hv0, mul_zero]
      rintro ⟨y', hy', e⟩
      exact h ⟨y' + y, A.add_mem hy' hy, by rw [Prod.snd_add, ← add_assoc, ← e, sub_add_cancel]⟩
  have huniq : ∀ w : Matrix κ ι ℚ → ℂ, (∀ y ∈ A, ∀ x, fac ε y x * w (x - y.2) = w x) →
      w = w x₀ • v := by
    intro w hw
    funext x
    rw [Pi.smul_apply, smul_eq_mul]
    by_cases h : ∃ y' ∈ A, x = x₀ + y'.2
    · obtain ⟨y, hy, rfl⟩ := h
      rw [hv _ hy, ← hw y hy, add_sub_cancel_right, mul_comm]
    · rw [hv0 _ h, mul_zero]
      by_contra hne
      apply h
      obtain ⟨a, ha⟩ := exists_lift A hA hd (x - x₀) fun a ha => by
        have h1 := hw _ ha x
        simp only [sub_zero, fac, pr_zero_right] at h1
        have h2 : ε (a, 0) * ex (2 * pr x a) = 1 := by
          apply mul_right_cancel₀ hne; rw [h1, one_mul]
        apply ex_two_eq_one
        apply mul_left_cancel₀ (mul_ne_zero (hn _ ha) (ex_ne_zero (2 * pr x₀ a)))
        rw [mul_assoc, ← ex_add, pr_sub_left, hx₀ _ ha, mul_one, ← h2]
        congr 2; ring
      exact ⟨_, ha, by simp⟩
  obtain ⟨N₁, hN₁, hN₁'⟩ := exists_den_fg (A.map (AddMonoidHom.fst _ _)) (fg_map hA _)
  obtain ⟨N₂, hN₂, hN₂'⟩ := exists_den_fg (A.map (AddMonoidHom.snd _ _)) (fg_map hA _)
  obtain ⟨D, hD, hD'⟩ := exists_den x₀
  have hR : 0 < m * N₁ * N₂ * D := by positivity
  have hlev : HasLevel (m * N₁ * N₂ * D) v := by
    constructor
    · intro x hx
      obtain ⟨y, hy, rfl⟩ : ∃ y ∈ A, x = x₀ + y.2 := by
        by_contra h; exact hx (hv0 _ h)
      have h1 := intM_smul (m * N₁ * N₂) hD'
      have h2 := intM_smul (m * N₁ * D) (hN₂' y.2 ⟨y, hy, rfl⟩)
      rw [smul_smul] at h1 h2
      have e1 : ((m * N₁ * N₂ : ℕ) : ℚ) * D = ((m * N₁ * N₂ * D : ℕ) : ℚ) := by push_cast; ring
      have e2 : ((m * N₁ * D : ℕ) : ℚ) * N₂ = ((m * N₁ * N₂ * D : ℕ) : ℚ) := by push_cast; ring
      rw [e1] at h1; rw [e2] at h2
      intro k i
      rw [smul_add]
      exact (h1 k i).add (h2 k i)
    · intro x z hz
      have hz' := intM_smul (N₂ * D) hz
      have hmem : ((0 : Matrix κ ι ℚ), (N₁ : ℚ) • ((N₂ * D : ℕ) : ℚ) • z) ∈ A := by
        refine (hd _).2 fun y hy => ?_
        obtain ⟨n, hn⟩ := pr_int (hN₁' y.1 ⟨y, hy, rfl⟩) hz'
        refine ⟨-n, ?_⟩
        rw [pr_smul_left] at hn
        simp only [pr_zero_left]
        rw [pr_smul_right, hn]; simp
      have e : m • ((0 : Matrix κ ι ℚ), (N₁ : ℚ) • ((N₂ * D : ℕ) : ℚ) • z) =
          (0, ((m * N₁ * N₂ * D : ℕ) : ℚ) • z) := by
        refine Prod.ext (by simp) ?_
        rw [Prod.smul_snd, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, smul_smul]
        congr 1; push_cast; ring
      have h1 := hm' _ hmem
      have h2 := hfix _ (A.nsmul_mem hmem m) (x + ((m * N₁ * N₂ * D : ℕ) : ℚ) • z)
      rw [e] at h1 h2
      rw [← h2, fac, h1]
      simp [pr_zero_left, pr_zero_right, ex_zero]
  obtain ⟨him, hre, hsup, -⟩ := GlobalTheory.T.schwartzBruhatInnerProduct_self_nonneg_bounds ℚ κ ι _ v hR hlev
  have hpos : 0 < (ip v v).re := by
    refine lt_of_le_of_ne hre fun h => ?_
    have := hsup x₀
    rw [← h, hvx] at this
    norm_num at this
  set t : ℝ := (ip v v).re with ht
  have hip : ip v v = (t : ℂ) := Complex.ext rfl (by simpa using him)
  have hs : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 hpos
  have hc : (((Real.sqrt t)⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (inv_pos.2 hs).ne'
  refine ⟨(((Real.sqrt t)⁻¹ : ℝ) : ℂ) • v, ⟨_, hR, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x hx
    exact hlev.1 x fun h => hx (by simp [h])
  · intro x z hz
    simp only [Pi.smul_apply, hlev.2 x z hz]
  · rw [ip_smul_self _ hc, hip, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      ← mul_inv, Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one]
  · intro y hy x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_left_comm, hfix y hy x]
  · intro w _ hw
    refine ⟨w x₀ * (((Real.sqrt t)⁻¹ : ℝ) : ℂ)⁻¹, ?_⟩
    rw [smul_smul, inv_mul_cancel_right₀ hc]
    exact huniq w hw
end GlobalTheory.SW.Vac
