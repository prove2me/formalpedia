-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BlockIwahoriUML.factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:30:51.242233+00:00
-- url     : https://prove2.me/submissions/d85c4e86-99d2-465e-975b-69a5053f9a8a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsPrincipalCongruence
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriBlockUpperLeviLower
import Theorems.Thm_GlobalTheory_CompanionTheory_BlockIwahoriUML_exists_udl
import Theorems.Thm_GlobalTheory_CompanionTheory_BlockIwahoriUML_up_split
import Theorems.Thm_GlobalTheory_CompanionTheory_BlockIwahoriUML_cong_transpose
import Theorems.Thm_GlobalTheory_CompanionTheory_BlockIwahoriUML_units_conj
import Theorems.Thm_GlobalTheory_CompanionTheory_BlockIwahoriUML_blockDiag_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BlockIwahoriUML
variable {k Γ : Type*} [Field k] [LinearOrderedCommGroupWithZero Γ]
namespace GlobalTheory.CompanionTheory.BlockIwahoriUML
theorem _root_.solution (v : Valuation k Γ) {r : Γ} (hr : r < 1) {n : ℕ} (β : Fin n → ℕ)
    (hβ : Monotone β) (g : GL (Fin n) k) (hg : Cong v r (g : Matrix (Fin n) (Fin n) k)) :
    ∃ nm : GL (Fin n) k, Cong v r (nm : Matrix (Fin n) (Fin n) k) ∧
    ∃ l : GL (Fin n) k, Cong v r (l : Matrix (Fin n) (Fin n) k) ∧
    ∃ np : GL (Fin n) k, Cong v r (np : Matrix (Fin n) (Fin n) k) ∧
      (∀ i j, β i ≤ β j → (nm : Matrix (Fin n) (Fin n) k) i j =
        (1 : Matrix (Fin n) (Fin n) k) i j) ∧
      (∀ i j, β i ≠ β j → (l : Matrix (Fin n) (Fin n) k) i j = 0) ∧
      (∀ i j, β j ≤ β i → (np : Matrix (Fin n) (Fin n) k) i j =
        (1 : Matrix (Fin n) (Fin n) k) i j) ∧ g = np * l * nm := by
  classical
  obtain ⟨u, d, t, hu, ht, hu0, hu1, hd0, ht0, ht1, hudt⟩ := exists_udl v hr n _ hg
  obtain ⟨a, m, had, hmd, haC, hmC, hab, hmb, huam⟩ := up_split v hr β hβ u hu hu0 hu1
  have htC : Cong v r tᵀ := cong_transpose v ht
  obtain ⟨b, c, hbd, hcd, hbC, hcC, hbb, hcb, htbc⟩ :=
    up_split v hr β hβ tᵀ htC (fun i j h => ht0 j i h) ht1
  have htt : t = cᵀ * bᵀ := by
    rw [← Matrix.transpose_mul, ← htbc, Matrix.transpose_transpose]
  have hbtC : Cong v r bᵀ := cong_transpose v hbC
  let npg : GL (Fin n) k := Matrix.nonsingInvUnit a (by simp [had])
  let nmg : GL (Fin n) k := Matrix.nonsingInvUnit bᵀ (by simp [hbd])
  have hnpK : npg ∈ PrincipalCongruence.principalCongruence v r hr := haC
  have hnmK : nmg ∈ PrincipalCongruence.principalCongruence v r hr := hbtC
  have hgK : g ∈ PrincipalCongruence.principalCongruence v r hr := hg
  have hlK := mul_mem (mul_mem (inv_mem hnpK) hgK) (inv_mem hnmK)
  have hprod : (g : Matrix (Fin n) (Fin n) k) =
      (npg : Matrix (Fin n) (Fin n) k) * (m * d * cᵀ) * (nmg : Matrix (Fin n) (Fin n) k) := by
    show (g : Matrix (Fin n) (Fin n) k) = a * (m * d * cᵀ) * bᵀ
    rw [hudt, huam, htt]
    simp only [Matrix.mul_assoc]
  have hlev : ((npg⁻¹ * g * nmg⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = m * d * cᵀ := by
    rw [Units.val_mul, Units.val_mul, hprod]
    exact units_conj npg nmg _
  refine ⟨nmg, hnmK, npg⁻¹ * g * nmg⁻¹, hlK, npg, hnpK, ?_, ?_, hab, by group⟩
  · intro i j hij
    show bᵀ i j = _
    rw [Matrix.transpose_apply, hbb j i hij, ← Matrix.transpose_apply (1 : Matrix (Fin n) (Fin n) k) j i, Matrix.transpose_one]
  · rw [hlev]
    refine blockDiag_mul β (blockDiag_mul β hmb ?_) ?_
    · intro i j hij
      exact hd0 i j (fun e => hij (by rw [e]))
    · intro i j hij
      exact hcb j i hij.symm
end GlobalTheory.CompanionTheory.BlockIwahoriUML
