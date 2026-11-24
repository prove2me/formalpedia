-- Prove2me | solution 1 for GlobalTheory.CubeColim.exists_cocycle_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:20:46.985401+00:00
-- url     : https://prove2.me/submissions/ac00c48d-a083-4a3e-815c-d1476d57f05d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechComplexDirectLimit
import Theorems.Thm_GlobalTheory_CubeColim_termMap_comp
import Theorems.Thm_GlobalTheory_CubeColim_trans_congr
import Theorems.Thm_GlobalTheory_CubeColim_exists_lift
import Theorems.Thm_GlobalTheory_CubeColim_exists_kill

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits Filter
open GlobalTheory
open GlobalTheory.CubeColim
variable {ι : Type} [LinearOrder ι] [Fintype ι]
namespace GlobalTheory.CubeColim
theorem _root_.solution {A : ℕ → Cube.{0} ι ℤ} {B : Cube.{0} ι ℤ}
    (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d)) (ρ : ∀ c, A c ⟶ B)
    (h1 : ∀ j c d h, μ j c d h ≫ ρ d = ρ c)
    (h2 : ∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e),
      μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'')
    (h3 : ∀ s : Finset ι, s.Nonempty → ∀ b : B.obj s, ∃ c, ∃ a : (A c).obj s, (ρ c).app s a = b)
    (h4 : ∀ s : Finset ι, s.Nonempty → ∀ c (a : (A c).obj s), (ρ c).app s a = 0 →
      ∃ j, (μ j c (c + j) rfl).app s a = 0)
    {m : ℕ} (hm : 0 < m) (z : Cube.Term B m) (hz : Cube.d B m z = 0) :
    ∃ C, ∀ c, C ≤ c → ∃ a : Cube.Term (A c) m,
      Cube.termMap (ρ c) m a = z ∧ Cube.d (A c) m a = 0 := by
  obtain ⟨C₀, a, ha⟩ := exists_lift μ ρ h1 h3 hm z
  have hda : Cube.termMap (ρ C₀) (m + 1) (Cube.d (A C₀) m a) = 0 := by
    rw [Cube.termMap_d, ha, hz]
  obtain ⟨J, hJ⟩ := exists_kill μ ρ h2 h4 (Nat.succ_pos m) C₀ _ hda
  refine ⟨C₀ + J, fun c hc => ⟨Cube.termMap (μ (c - C₀) C₀ c (by omega)) m a, ?_, ?_⟩⟩
  · rw [← termMap_comp, h1, ha]
  · rw [← Cube.termMap_d]
    have e : μ (c - C₀) C₀ c (by omega) =
        μ J C₀ (C₀ + J) rfl ≫ μ (c - C₀ - J) (C₀ + J) c (by omega) := by
      rw [h2 J (c - C₀ - J) C₀ (C₀ + J) c rfl (by omega) (by omega)]
      exact trans_congr μ _ _ (by omega)
    rw [e, termMap_comp, hJ, map_zero]
end GlobalTheory.CubeColim
