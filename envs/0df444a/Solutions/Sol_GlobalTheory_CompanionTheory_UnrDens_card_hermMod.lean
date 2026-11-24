-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.card_hermMod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:12:47.819874+00:00
-- url     : https://prove2.me/submissions/d3849f01-a566-4d6e-aa25-3028f5791766

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianMatricesDvdSq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardHermitianMatricesModPow
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_hermMod_eq
import Theorems.Thm_GlobalTheory_GramCount_Prim_map
import Theorems.Thm_GlobalTheory_GramCount_card_hermitian_dvd_sq
import Theorems.Thm_GlobalTheory_T_unramified_quotient_card


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens
namespace GlobalTheory.CompanionTheory.UnrDens
theorem _root_.solution : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ),
    IsUnrQuad R σ ϖ q ε → ∀ n k : ℕ, Nat.card (hermMod σ ϖ n k) = q ^ (k * n ^ 2) := by
  intro R _ σ ϖ q ε h n k
  rw [hermMod_eq h n k]
  have hcard := GlobalTheory.T.unramified_quotient_card R σ ϖ q ε h k
  have hq : 1 < q := h.one_lt
  haveI : Finite (R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))
  obtain ⟨u, hu, -⟩ := h.basis
  have hinv : ∀ x, barσ σ ϖ h.fix_ϖ k (barσ σ ϖ h.fix_ϖ k x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [barσ_mk, barσ_mk, h.inv]
  have hω : IsUnit (Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) u -
      barσ σ ϖ h.fix_ϖ k (Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) u)) := by
    rw [barσ_mk, ← map_sub]
    exact hu.map _
  have key := GlobalTheory.GramCount.card_hermitian_dvd_sq (barσ σ ϖ h.fix_ϖ k) hinv _ hω 1 (map_one _) n
  have e2 : Nat.card {x : R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k // (1 : R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k) ∣ x} = q ^ (2 * k) := by
    rw [← hcard]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv fun x => one_dvd x)
  apply Nat.pow_left_injective two_ne_zero
  show _ ^ 2 = _ ^ 2
  calc Nat.card ↥{H : Matrix (Fin n) (Fin n) (R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k) |
          ∀ a b, barσ σ ϖ h.fix_ϖ k (H b a) = H a b} ^ 2
      = Nat.card {H : Fin n → Fin n → R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k //
          (∀ a b : Fin n, barσ σ ϖ h.fix_ϖ k (H b a) = H a b) ∧
            ∀ a b : Fin n, (1 : R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k) ∣ H a b} ^ 2 := by
        congr 1
        exact Nat.card_congr
          { toFun := fun H => ⟨H.1, H.2, fun _ _ => one_dvd _⟩
            invFun := fun H => ⟨H.1, H.2.1⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
    _ = Nat.card {x : R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k // (1 : R ⧸ PositivityTheory.PfSWUS.Loc.lev ϖ k) ∣ x} ^ (n * n) := key
    _ = (q ^ (k * n ^ 2)) ^ 2 := by
        rw [e2, ← pow_mul, ← pow_mul]
        ring_nf
end GlobalTheory.CompanionTheory.UnrDens
