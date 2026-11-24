-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.Sphere.count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:28:50.779839+00:00
-- url     : https://prove2.me/submissions/b5ea88b0-31dc-47d7-a908-37fe0b33aa15

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianSpaceAnisotropicUnitStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianVectorValuesCard
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_Sphere_card_fibre
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_Sphere_sum_ite_card
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_Sphere_arith_unit
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_Sphere_arith_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_card_fibre
import Theorems.Thm_GlobalTheory_T_hermitian_space_anisotropic_unit
import Theorems.Thm_GlobalTheory_T_norm_fibre_card_nonzero
import Theorems.Thm_GlobalTheory_T_norm_fibre_card_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.Sphere
namespace GlobalTheory.CompanionTheory.UnrDens.Sphere
theorem _root_.solution : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nat.card V = q ^ (2 * m) → (∀ c : E, τ c = c → c ≠ 0 → (Nat.card {v : V // B.h v v = c} : ℝ) = (q : ℝ) ^ (2 * m) / q * (1 - ((ε : ℝ) / q) ^ m)) ∧ (Nat.card {v : V // B.h v v = 0} : ℝ) = (q : ℝ) ^ (2 * m) / q * (1 + ((q : ℝ) - 1) * ((ε : ℝ) / q) ^ m) := by
  intro E _ τ q ε hR m
  have hq1 : 1 < q := hR.one_lt
  have hq0 : (q : ℝ) ≠ 0 := by
    have : 0 < q := by omega
    exact_mod_cast this.ne'
  induction m with
  | zero =>
    intro V _ _ B hc
    have hc1 : Nat.card V = 1 := by simpa using hc
    obtain ⟨hs, -⟩ := Nat.card_eq_one_iff_unique.1 hc1
    refine ⟨?_, ?_⟩
    · intro c _ hc0
      have : IsEmpty {v : V // B.h v v = c} :=
        ⟨fun x => hc0 (by
          have h := x.2
          rw [Subsingleton.elim x.1 0, B.zero_left] at h
          exact h.symm)⟩
      rw [Nat.card_of_isEmpty]
      simp
    · have : Subsingleton {v : V // B.h v v = 0} := inferInstance
      rw [Nat.card_of_subsingleton (⟨0, B.zero_left 0⟩ : {v : V // B.h v v = 0})]
      field_simp
      ring
  | succ m ih =>
    intro V _ _ B hc
    have hpow : 1 < q ^ (2 * (m + 1)) := Nat.one_lt_pow (by omega) hq1
    have hfin : Finite V := Nat.finite_of_card_ne_zero (by omega)
    have hfinE : Finite E := Nat.finite_of_card_ne_zero (by
      rw [hR.card]; exact pow_ne_zero _ (by omega))
    have hnt : Nontrivial V := Finite.one_lt_card_iff_nontrivial.1 (by omega)
    obtain ⟨w, hw⟩ := GlobalTheory.T.hermitian_space_anisotropic_unit E τ q ε hR V B hnt
    have hP : Nat.card (B.perp w) = q ^ (2 * m) := by
      have h1 : Nat.card E * Nat.card (B.perp w) = Nat.card V := by
        rw [← Nat.card_prod]; exact Nat.card_congr (B.perpEquiv hw)
      rw [hR.card, hc] at h1
      have hq2 : 0 < q ^ 2 := pow_pos (by omega) _
      apply Nat.eq_of_mul_eq_mul_left hq2
      rw [h1]; ring
    obtain ⟨ihc, ihz⟩ := ih (B.perp w) (B.perpForm hw) hP
    classical
    haveI := Fintype.ofFinite E
    have hdfix : τ (B.h w w) = B.h w w := (B.symm w w).symm
    obtain ⟨di, hdi⟩ : ∃ di, B.h w w * di = 1 := hw.exists_right_inv
    have hdifix : τ di = di := by
      have h1 : B.h w w * τ di = 1 := by
        have := congrArg τ hdi
        rwa [map_mul, hdfix, map_one] at this
      calc τ di = (B.h w w * di) * τ di := by rw [hdi, one_mul]
        _ = di * (B.h w w * τ di) := by ring
        _ = di := by rw [h1, mul_one]
    set A : ℝ := (q : ℝ) ^ (2 * m) / q * (1 - ((ε : ℝ) / q) ^ m) with hA
    set B₀ : ℝ := (q : ℝ) ^ (2 * m) / q * (1 + ((q : ℝ) - 1) * ((ε : ℝ) / q) ^ m) with hB₀
    have key : ∀ c : E, τ c = c → (Nat.card {v : V // B.h v v = c} : ℝ) =
        (Nat.card {a : E // a * τ a = c * di} : ℝ) * B₀ +
          ((q : ℝ) ^ 2 - Nat.card {a : E // a * τ a = c * di}) * A := by
      intro c hcf
      have hiff : ∀ a : E, a * τ a * B.h w w = c ↔ a * τ a = c * di := by
        intro a
        constructor
        · intro h
          rw [← h, mul_assoc, hdi, mul_one]
        · intro h
          rw [h, mul_assoc, mul_comm di, hdi, mul_one]
      have hterm : ∀ a : E,
          (Nat.card {v : B.perp w // (B.perpForm hw).h v v = c - a * τ a * B.h w w} : ℝ) =
            if a * τ a = c * di then B₀ else A := by
        intro a
        split_ifs with h
        · have h0 : c - a * τ a * B.h w w = 0 := by rw [(hiff a).2 h, sub_self]
          rw [h0]; exact ihz
        · refine ihc _ ?_ ?_
          · rw [map_sub, map_mul, map_mul, hcf, hdfix, hR.inv a]
            ring
          · intro h0
            exact h ((hiff a).1 (sub_eq_zero.1 h0).symm)
      rw [card_fibre B hw c]
      push_cast
      rw [Finset.sum_congr rfl (fun a _ => hterm a), sum_ite_card, hR.card]
      push_cast
      rfl
    have hpw : (q : ℝ) ^ (2 * (m + 1)) = (q : ℝ) ^ (2 * m) * (q : ℝ) ^ 2 := by ring
    refine ⟨?_, ?_⟩
    · intro c hcf hc0
      have hn : (Nat.card {a : E // a * τ a = c * di} : ℝ) = (q : ℝ) - ε := by
        have := GlobalTheory.T.norm_fibre_card_nonzero E τ q ε hR (c * di)
          (by rw [map_mul, hcf, hdifix])
          (by
            intro h0
            apply hc0
            calc c = c * (di * B.h w w) := by rw [mul_comm di, hdi, mul_one]
              _ = (c * di) * B.h w w := by ring
              _ = 0 := by rw [h0, zero_mul])
        exact_mod_cast this
      rw [key c hcf, hn, hpw, pow_succ ((ε : ℝ) / q) m]
      exact arith_unit _ _ _ _ hq0
    · have hn : (Nat.card {a : E // a * τ a = (0 : E) * di} : ℝ) = (q : ℝ) * (1 + ε) - ε := by
        have := GlobalTheory.T.norm_fibre_card_zero E τ q ε hR
        rw [zero_mul]
        exact_mod_cast this
      rw [key 0 (map_zero τ), hn, hpw, pow_succ ((ε : ℝ) / q) m]
      exact arith_zero _ _ _ _ hq0
end GlobalTheory.CompanionTheory.UnrDens.Sphere
