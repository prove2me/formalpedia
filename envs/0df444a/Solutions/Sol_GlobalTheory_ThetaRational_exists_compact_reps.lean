-- Prove2me | solution 1 for GlobalTheory.ThetaRational.exists_compact_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:33:05.34821+00:00
-- url     : https://prove2.me/submissions/e30c74cc-1916-4d66-b183-b5064eac9751

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
namespace GlobalTheory.ThetaRational
theorem _root_.solution {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (h : Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) = ⊤) :
    ∃ K : Set (Fin g → ℂ), IsCompact K ∧
      ∀ z, ∃ k ∈ K, z - k ∈ (periodLattice τ : Set (Fin g → ℂ)) := by
  let Φ : (Fin g → ℝ) × (Fin g → ℝ) → Fin g → ℂ := fun v => τ *ᵥ ofRealVec v.1 + ofRealVec v.2
  have hΦ : Continuous Φ := by
    have h1 : Continuous (ofRealVec : (Fin g → ℝ) → Fin g → ℂ) := by
      unfold ofRealVec; fun_prop
    exact (continuous_const.matrix_mulVec (h1.comp continuous_fst)).add (h1.comp continuous_snd)
  have hadd : ∀ v w, Φ (v + w) = Φ v + Φ w := by
    intro v w
    have h1 : ∀ a b : Fin g → ℝ, ofRealVec (a + b) = ofRealVec a + ofRealVec b := fun a b => by
      ext i; simp [ofRealVec]
    simp only [Φ, Prod.fst_add, Prod.snd_add, h1, Matrix.mulVec_add]
    abel
  have hsmul : ∀ (r : ℝ) v, Φ (r • v) = r • Φ v := by
    intro r v
    have h1 : ∀ a : Fin g → ℝ, ofRealVec (r • a) = r • ofRealVec a := fun a => by
      ext i; simp [ofRealVec]
    simp only [Φ, Prod.smul_fst, Prod.smul_snd, h1, Matrix.mulVec_smul, smul_add]
  have hint : ∀ n n' : Fin g → ℤ,
      Φ (fun i => n i, fun i => n' i) = τ *ᵥ ofIntVec n + ofIntVec n' := by
    intro n n'
    have h1 : ∀ a : Fin g → ℤ, ofRealVec (fun i => (a i : ℝ)) = ofIntVec a := fun a => by
      ext i; simp [ofRealVec, ofIntVec]
    simp only [Φ, h1]
  have hsurj : ∀ z, ∃ v, Φ v = z := by
    intro z
    have hz : z ∈ Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) := h ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx => obtain ⟨n, n', rfl⟩ := hx; exact ⟨_, hint n n'⟩
    | zero => exact ⟨(0 : ℝ) • 0, by rw [hsmul, zero_smul]⟩
    | add x y _ _ hx hy =>
      obtain ⟨v, rfl⟩ := hx
      obtain ⟨w, rfl⟩ := hy
      exact ⟨_, hadd v w⟩
    | smul r x _ hx =>
      obtain ⟨v, rfl⟩ := hx
      exact ⟨_, hsmul r v⟩
  refine ⟨Φ '' Set.Icc 0 1, isCompact_Icc.image hΦ, fun z => ?_⟩
  obtain ⟨v, rfl⟩ := hsurj z
  refine ⟨_, ⟨(fun i => Int.fract (v.1 i), fun i => Int.fract (v.2 i)), ⟨⟨fun i => ?_, fun i => ?_⟩,
    fun i => ?_, fun i => ?_⟩, rfl⟩, fun i => ⌊v.1 i⌋, fun i => ⌊v.2 i⌋, ?_⟩
  · exact Int.fract_nonneg _
  · exact Int.fract_nonneg _
  · exact (Int.fract_lt_one _).le
  · exact (Int.fract_lt_one _).le
  · rw [← hint, sub_eq_iff_eq_add, ← hadd]
    congr 1
    ext i <;> simp
end GlobalTheory.ThetaRational
