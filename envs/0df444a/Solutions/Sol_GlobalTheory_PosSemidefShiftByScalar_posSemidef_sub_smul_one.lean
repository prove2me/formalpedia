-- Prove2me | solution 1 for GlobalTheory.PosSemidefShiftByScalar.posSemidef_sub_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:28:19.456289+00:00
-- url     : https://prove2.me/submissions/45e0d6fd-dcc2-42f5-98a0-b17ed1d7fac7

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubSmulOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Unitary
open scoped ComplexOrder
open GlobalTheory GlobalTheory.PosSemidefShiftByScalar
namespace GlobalTheory.PosSemidefShiftByScalar
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ δ' : ℝ, δ' ≤ δ → (A - (δ' : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
  have hH := hA.isHermitian
  obtain ⟨δ, hδ, hle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ hH.eigenvalues i := by
    rcases isEmpty_or_nonempty n with h | h
    · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
    · obtain ⟨i0, -, hi0⟩ :=
        Finset.exists_min_image Finset.univ hH.eigenvalues Finset.univ_nonempty
      exact ⟨_, hA.eigenvalues_pos i0, fun i => hi0 i (Finset.mem_univ i)⟩
  refine ⟨δ, hδ, fun δ' hδ' => ?_⟩
  have e : A - (δ' : ℂ) • (1 : Matrix n n ℂ) = conjStarAlgAut ℂ _ hH.eigenvectorUnitary
      (diagonal (fun i => ((hH.eigenvalues i - δ' : ℝ) : ℂ))) := by
    have d : diagonal (fun i => ((hH.eigenvalues i - δ' : ℝ) : ℂ)) =
        diagonal (RCLike.ofReal ∘ hH.eigenvalues) - (δ' : ℂ) • (1 : Matrix n n ℂ) := by
      ext i j; by_cases h : i = j <;> simp [diagonal, one_apply, h]
    conv_lhs => rw [hH.spectral_theorem]
    rw [d, map_sub, map_smul, map_one]
  rw [e, conjStarAlgAut_apply, isUnit_coe.posSemidef_star_right_conjugate_iff]
  exact PosSemidef.diagonal fun i =>
    Complex.zero_le_real.2 (sub_nonneg.2 (hδ'.trans (hle i)))
end GlobalTheory.PosSemidefShiftByScalar
