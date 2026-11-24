-- Prove2me | solution 1 for GlobalTheory.BorelAlg.Equivariant.exists_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:51:39.20634+00:00
-- url     : https://prove2.me/submissions/faedb4f5-aba6-4a5a-96e2-2ad3d8232f6f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Theorems.Thm_GlobalTheory_BorelAlg_gen_isRelPrime
import Theorems.Thm_GlobalTheory_BorelAlg_Equivariant_det_pow_dvd
import Theorems.Thm_GlobalTheory_BorelAlg_Equivariant_isHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.BorelAlg
variable {ι : Type} (m : ι → ℕ) (L : Type) [Field L]
variable [Fintype ι]
variable {m L} {S : Type} [CommRing S] [Algebra (MvPolynomial (Lt m) L) S]
  [IsLocalization.Away (∏ τ, (gen m L τ).det) S]
namespace GlobalTheory.BorelAlg
namespace Equivariant
theorem _root_.solution {a : ι × ℕ → ℕ} {f : S} (hf : Equivariant m L S a f) :
    ∃ P : MvPolynomial (Lt m) L, algebraMap _ S P = f ∧
      P.IsHomogeneous (∑ τ, ∑ i : Fin (m τ), a (τ, (i : ℕ))) := by
  obtain ⟨⟨P, ⟨_, N, rfl⟩⟩, hP⟩ :=
    IsLocalization.surj (Submonoid.powers (∏ τ, (gen m L τ).det)) f
  simp only at hP
  have hd : (∏ τ, (gen m L τ).det) ^ N ∣ P := by
    rw [← Finset.prod_pow]
    exact Finset.prod_dvd_of_isRelPrime
      (fun τ _ τ' _ h => (gen_isRelPrime m L h).pow) fun τ _ => hf.det_pow_dvd hP τ
  obtain ⟨Q, rfl⟩ := hd
  have hu : IsUnit (algebraMap _ S ((∏ τ, (gen m L τ).det) ^ N)) := by
    rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit _).pow N
  rw [map_mul, mul_comm] at hP
  obtain rfl : f = algebraMap _ S Q := hu.mul_left_cancel hP
  exact ⟨Q, rfl, hf.isHomogeneous⟩
end Equivariant
end GlobalTheory.BorelAlg
