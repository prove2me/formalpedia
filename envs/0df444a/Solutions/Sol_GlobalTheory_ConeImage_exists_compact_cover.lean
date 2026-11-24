-- Prove2me | solution 1 for GlobalTheory.ConeImage.exists_compact_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:58:42.12298+00:00
-- url     : https://prove2.me/submissions/b4151861-3f95-4b00-b421-24e49ec8a722

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsNhdsSubsetRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ConeImage
namespace GlobalTheory.ConeImage
theorem _root_.solution {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (h : Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) = ⊤) :
    ∃ K : Set (Fin g → ℂ), IsCompact K ∧ ∀ z, ∃ w ∈ K, ∃ n n' : Fin g → ℤ,
      z = w + τ *ᵥ ofIntVec n + ofIntVec n' := by
  let L : (Fin g → ℝ) × (Fin g → ℝ) → (Fin g → ℂ) :=
    fun x => τ *ᵥ ofRealVec x.1 + ofRealVec x.2
  have hc : Continuous L := by
    have h1 : Continuous (ofRealVec : (Fin g → ℝ) → (Fin g → ℂ)) := by
      unfold ofRealVec; fun_prop
    exact (continuous_const.matrix_mulVec (h1.comp continuous_fst)).add (h1.comp continuous_snd)
  have hadd : ∀ a b : Fin g → ℝ, ofRealVec (a + b) = ofRealVec a + ofRealVec b := by
    intro a b; ext i; simp [ofRealVec]
  have hsm : ∀ (r : ℝ) (a : Fin g → ℝ), ofRealVec (r • a) = (r : ℂ) • ofRealVec a := by
    intro r a; ext i; simp [ofRealVec]
  have hint : ∀ n : Fin g → ℤ, ofIntVec n = ofRealVec (fun i => (n i : ℝ)) := by
    intro n; ext i; simp [ofRealVec, ofIntVec]
  have hs : ∀ z, ∃ x, z = L x := by
    intro z
    have hz : z ∈ Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) := h ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, n', rfl⟩ := hx
      exact ⟨(fun i => (n i : ℝ), fun i => (n' i : ℝ)), by simp only [L, hint]⟩
    | zero =>
      refine ⟨0, ?_⟩
      have : ofRealVec (0 : Fin g → ℝ) = 0 := by ext i; simp [ofRealVec]
      simp [L, this]
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      refine ⟨a + b, ?_⟩
      simp only [L, Prod.fst_add, Prod.snd_add, hadd, Matrix.mulVec_add]; abel
    | smul r x _ hx =>
      obtain ⟨a, rfl⟩ := hx
      refine ⟨r • a, ?_⟩
      simp only [L, Prod.smul_fst, Prod.smul_snd, hsm, Matrix.mulVec_smul]
      ext i; simp [mul_add]
  refine ⟨L '' (Set.Icc 0 1), isCompact_Icc.image hc, fun z => ?_⟩
  obtain ⟨⟨a, b⟩, rfl⟩ := hs z
  refine ⟨L (fun i => Int.fract (a i), fun i => Int.fract (b i)), ⟨_, ?_, rfl⟩,
    fun i => ⌊a i⌋, fun i => ⌊b i⌋, ?_⟩
  · exact ⟨⟨fun i => Int.fract_nonneg _, fun i => Int.fract_nonneg _⟩,
      ⟨fun i => (Int.fract_lt_one _).le, fun i => (Int.fract_lt_one _).le⟩⟩
  · have ha : a = (fun i => Int.fract (a i)) + fun i => ((⌊a i⌋ : ℤ) : ℝ) := by ext i; simp
    have hb : b = (fun i => Int.fract (b i)) + fun i => ((⌊b i⌋ : ℤ) : ℝ) := by ext i; simp
    simp only [L, hint]
    conv_lhs => rw [ha, hb]
    simp only [hadd, Matrix.mulVec_add]; abel
end GlobalTheory.ConeImage
