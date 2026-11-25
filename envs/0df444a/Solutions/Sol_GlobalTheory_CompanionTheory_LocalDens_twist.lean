-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalDens.twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:41:12.720949+00:00
-- url     : https://prove2.me/submissions/6e0ca734-eeab-42bd-8115-2694dd33dc32

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardPreimageHom
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_cT_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_cT_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_cT_one
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_red_pow_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_inv_mod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalDens
open PositivityTheory.PfSWUS.Loc
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.LocalDens
theorem _root_.solution {σ : R →+* R} {ϖ : R} (hσ : σ ϖ = ϖ) {n : ℕ} {T T' H : Matrix (Fin n) (Fin n) R} {t : R}
    (ht : t + σ t = 1) (hH : cT σ H = H) (e b : ℕ)
    (h1 : T * T' = ϖ ^ e • (1 : Matrix (Fin n) (Fin n) R))
    (h2 : cT σ T' * T = ϖ ^ e • (1 : Matrix (Fin n) (Fin n) R)) :
    ∃ g h : Matrix (Fin n) (Fin n) R, red ϖ (e + b + 1 + 1) (g * h) = 1 ∧ red ϖ (e + b + 1 + 1) (h * g) = 1 ∧
      red ϖ (e + b + 1 + 1) (cT σ g * T * g) = red ϖ (e + b + 1 + 1) (T + ϖ ^ (e + b + 1) • H) := by
  obtain ⟨h, hgh, hhg⟩ := inv_mod ϖ (e + b + 1 + 1) ((ϖ ^ b * t) • (T' * H))
  refine ⟨_, h, hgh, hhg, ?_⟩
  have hs : σ t = 1 - t := by rw [← ht]; ring
  have hcg : cT σ (1 + ϖ • (ϖ ^ b * t) • (T' * H)) = 1 + (ϖ ^ (b + 1) * (1 - t)) • (H * cT σ T') := by
    rw [cT_add, cT_one, cT_smul, cT_smul, cT_mul, hH, hσ, map_mul, map_pow, hσ, hs, smul_smul, pow_succ]
    congr 2
    ring
  have e1 : (1 + (ϖ ^ (b + 1) * (1 - t)) • (H * cT σ T')) * T
      = T + (ϖ ^ (b + 1) * (1 - t) * ϖ ^ e) • H := by
    rw [add_mul, one_mul, Matrix.smul_mul, Matrix.mul_assoc, h2, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  have e2 : T * (T' * H) = ϖ ^ e • H := by
    rw [← Matrix.mul_assoc, h1, Matrix.smul_mul, Matrix.one_mul]
  have e3 : cT σ (1 + ϖ • (ϖ ^ b * t) • (T' * H)) * T * (1 + ϖ • (ϖ ^ b * t) • (T' * H))
      = (T + ϖ ^ (e + b + 1) • H) + ϖ ^ ((e + b + 1 + 1) + b) • ((t * (1 - t)) • (H * (T' * H))) := by
    rw [hcg, e1, mul_add, add_mul, add_mul, Matrix.mul_one, Matrix.mul_one]
    simp only [Matrix.mul_smul, Matrix.smul_mul, e2]
    simp only [smul_smul]
    have c1 : ϖ ^ ((e + b + 1 + 1) + b) = ϖ ^ (b + 1) * ϖ ^ (b + 1) * ϖ ^ e := by ring
    have c2 : ϖ ^ (e + b + 1) = ϖ ^ (b + 1) * ϖ ^ e := by ring
    rw [c1, c2]
    module
  rw [e3, red_add, red_pow_smul, add_zero]
end GlobalTheory.CompanionTheory.LocalDens
