-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HatBound.exists_nsmul_mem_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:49:10.334746+00:00
-- url     : https://prove2.me/submissions/9c43fb17-3f98-43c8-8b3c-d26f415433b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_NefEffectiveCones_ExistsNsmulMulVecMemHat
import Theorems.Thm_GlobalTheory_CompanionTheory_HatBound_exists_nat_mul_integer
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HatBound
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.CompanionTheory.HatBound
theorem _root_.solution [NumberField E] (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ m : ℕ, 0 < m ∧ m • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hx⟩ := hx
    obtain ⟨m', hm', hy⟩ := hy
    refine ⟨m * m', mul_pos hm hm', ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hx _
    · rw [mul_smul]; exact nsmul_mem hy _
  | smul c x _ hx =>
    obtain ⟨m, hm, hx⟩ := hx
    obtain ⟨m', hm', r, hr⟩ := exists_nat_mul_integer E c
    refine ⟨m * m', mul_pos hm hm', ?_⟩
    have : (m * m') • c • x = r • (m • x) := by
      funext i
      change (m * m') • (c * x i) = (r : E) * (m • x i)
      rw [hr, nsmul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    rw [this]
    exact L.smul_mem r hx
end GlobalTheory.CompanionTheory.HatBound
