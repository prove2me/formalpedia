-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.tubeChain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:50:49.112505+00:00
-- url     : https://prove2.me/submissions/b4a2040e-b58d-42c7-b66a-dda968dc6ad8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeTransformIndependentOfBaseStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianTubeTransformBoundStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianTubeTransformContinuousStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialDecayByMidpointsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformLocallyBoundedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformContinuousStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformHolomorphicLinesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformRecoversFunctionStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeChainHolds
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_continuous_pt
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_pt_re_im
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_gaussTube_of_tubeGood
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_gauss_bound
import Theorems.Thm_GlobalTheory_T_exponential_decay_by_midpoints
import Theorems.Thm_GlobalTheory_T_gaussian_tube_transform_bound
import Theorems.Thm_GlobalTheory_T_gaussian_tube_transform_continuous
import Theorems.Thm_GlobalTheory_T_inverse_transform_continuous
import Theorems.Thm_GlobalTheory_T_inverse_transform_holomorphic_lines
import Theorems.Thm_GlobalTheory_T_inverse_transform_locally_bounded
import Theorems.Thm_GlobalTheory_T_inverse_transform_recovers_function
import Theorems.Thm_GlobalTheory_T_tube_transform_independent_of_base

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
noncomputable section
namespace GlobalTheory.CompanionTheory.TubeFourier
private lemma pt_mem_tube_iff {x y : ℝ × ℝ} {S : Set (ℝ × ℝ)} : pt x y ∈ tube S ↔ x ∈ S := by
  simp [tube, pt]
end GlobalTheory.CompanionTheory.TubeFourier
end
end

set_option autoImplicit false
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier
namespace GlobalTheory.CompanionTheory.TubeFourier
theorem _root_.solution : TubeChain := by
  intro X _ _ _ T _ _ m Ω F hΩ hV hmid
  set G : Fin (m + 1) → T → ℂ × ℂ → X := fun i g => gauss (F i · g) with hGdef
  have hGT : ∀ i g, GaussTube (G i g) (Ω i) := fun i g => gaussTube_of_tubeGood (hΩ i).2.2 g
  have hind : ∀ i g, ∀ x ∈ Ω i, ∀ x' ∈ Ω i, ∀ t, phi (G i g) x t = phi (G i g) x' t :=
    fun i g => GlobalTheory.T.tube_transform_independent_of_base X (Ω i) (G i g) (hΩ i).1 (hΩ i).2.1 (hGT i g)
  have hstep : ∀ i : Fin m, ∀ g, ∀ x ∈ Ω i.castSucc, ∀ x' ∈ Ω i.succ, ∀ t,
      phi (G i.castSucc g) x t = phi (G i.succ g) x' t := by
    intro i g x hx x' hx' t
    obtain ⟨V, -, ⟨v, hv⟩, hVsub, hVeq⟩ := hV i
    rw [hind _ g x hx v (hVsub hv).1, hind _ g x' hx' v (hVsub hv).2]
    unfold phi
    congr 1
    funext y
    congr 1
    simp only [G, gauss]
    rw [hVeq (pt v y) (pt_mem_tube_iff.2 hv) g]
  have hQ : ∀ g t, ∀ k : Fin (m + 1), ∀ x ∈ Ω 0, ∀ x' ∈ Ω k,
      phi (G 0 g) x t = phi (G k g) x' t := by
    intro g t k
    induction k using Fin.induction with
    | zero => exact fun x hx x' hx' => hind 0 g x hx x' hx' t
    | succ i ih =>
      intro x hx x' hx'
      obtain ⟨V, -, ⟨v, hv⟩, hVsub, -⟩ := hV i
      rw [ih x hx v (hVsub hv).1]
      exact hstep i g v (hVsub hv).1 x' hx' t
  have hne0 : (Ω 0).Nonempty := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      obtain ⟨i, j, a, ha, b, hb, -⟩ := hmid 0
      obtain rfl : i = 0 := Fin.ext (Nat.lt_one_iff.1 i.isLt)
      exact ⟨a, ha⟩
    · obtain ⟨V, -, ⟨v, hv⟩, hVsub, -⟩ := hV ⟨0, hm⟩
      have h0 : (Fin.castSucc (⟨0, hm⟩ : Fin m)) = 0 := by
        ext
        simp
      exact ⟨v, h0 ▸ (hVsub hv).1⟩
  obtain ⟨x0, hx0⟩ := hne0
  set φ : ℝ × ℝ → T → X := fun t g => phi (G 0 g) x0 t with hφdef
  have hall : ∀ i g, ∀ x ∈ Ω i, ∀ t, phi (G i g) x t = φ t g :=
    fun i g x hx t => (hQ g t i x0 hx0 x hx).symm
  have hGcont : ∀ i, ∀ x ∈ Ω i, Continuous (fun p : (ℝ × ℝ) × T => G i p.2 (pt x p.1)) := by
    intro i x hx
    have hp : Continuous fun p : (ℝ × ℝ) × T => pt x p.1 := (continuous_pt x).comp continuous_fst
    have h1 : Continuous (fun p : (ℝ × ℝ) × T => F i (pt x p.1) p.2) := by
      refine (hΩ i).2.2.cont.comp_continuous (hp.prodMk continuous_snd) ?_
      intro p
      exact ⟨pt_mem_tube_iff.2 hx, Set.mem_univ _⟩
    have he : Continuous fun p : (ℝ × ℝ) × T =>
        Complex.exp ((pt x p.1).1 ^ 2 + (pt x p.1).2 ^ 2) :=
      Complex.continuous_exp.comp (((continuous_fst.comp hp).pow 2).add ((continuous_snd.comp hp).pow 2))
    exact he.smul h1
  have hGbd : ∀ i, ∀ x ∈ Ω i, ∀ g : T, ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ g' ∈ U, ∀ y : ℝ × ℝ,
      ‖G i g' (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2)) := by
    intro i x hx g
    obtain ⟨U, hU, M, hM⟩ := gauss_bound (hΩ i).2.2 (Set.singleton_subset_iff.2 hx)
      isCompact_singleton g
    refine ⟨U, hU, M, fun g' hg' y => ?_⟩
    have := hM g' hg' (pt x y) (pt_mem_tube_iff.2 rfl)
    simpa [pt] using this
  have hφcont : Continuous (fun p : (ℝ × ℝ) × T => φ p.1 p.2) :=
    GlobalTheory.T.gaussian_tube_transform_continuous X T (G 0) x0 (hGcont 0 x0 hx0) (fun g => hGbd 0 x0 hx0 g)
  have hφt : ∀ g : T, Continuous fun t => φ t g := fun g =>
    hφcont.comp (show Continuous (fun t : ℝ × ℝ => (t, g)) by fun_prop)
  have hdecay : ExpDecay φ := by
    refine GlobalTheory.T.exponential_decay_by_midpoints X T φ {a | ∃ i, a ∈ Ω i} ?_ ?_
    · rintro a ⟨i, ha⟩ g
      obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 ((hΩ i).1.mem_nhds ha)
      obtain ⟨U, hU, M, hM⟩ := gauss_bound (hΩ i).2.2 hsub (isCompact_closedBall a r) g
      refine ⟨r, hr, U, hU, M * Real.pi, fun x hx1 hx2 g' hg' t => ?_⟩
      have hxC : x ∈ Metric.closedBall a r := by
        rw [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff]
        exact ⟨hx1, hx2⟩
      rw [← hall i g' x (hsub hxC) t]
      refine GlobalTheory.T.gaussian_tube_transform_bound X (G i g') x M (fun y => ?_) t
      have := hM g' hg' (pt x y) (pt_mem_tube_iff.2 hxC)
      simpa [pt] using this
    · intro x
      obtain ⟨i, j, a, ha, b, hb, hx⟩ := hmid x
      exact ⟨a, ⟨i, ha⟩, b, ⟨j, hb⟩, hx⟩
  refine ⟨fun l g => inv (fun t => φ t g) l, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro g p v
    exact (GlobalTheory.T.inverse_transform_holomorphic_lines X T φ hdecay hφt g p v).differentiableOn
  · exact (GlobalTheory.T.inverse_transform_continuous X T φ hdecay hφcont).continuousOn
  · intro C _ hC g
    obtain ⟨U, hU, M, hM⟩ := GlobalTheory.T.inverse_transform_locally_bounded X T φ hdecay hφt C hC g
    exact ⟨U, hU, M, fun l hl g' hg' => hM l hl g' hg'⟩
  · intro i l hl g
    obtain ⟨x, hxdef⟩ : ∃ x : ℝ × ℝ, x = (l.1.re, l.2.re) := ⟨_, rfl⟩
    obtain ⟨y, hydef⟩ : ∃ y : ℝ × ℝ, y = (l.1.im, l.2.im) := ⟨_, rfl⟩
    have hx : x ∈ Ω i := hxdef ▸ hl
    have hphi : phi (G i g) x = fun t => φ t g := funext fun t => hall i g x hx t
    have hc1 : Continuous fun y' : ℝ × ℝ => G i g (pt x y') := by
      have h := (hGcont i x hx).comp (show Continuous (fun y' : ℝ × ℝ => (y', g)) by fun_prop)
      simpa only [Function.comp_def] using h
    obtain ⟨U, hU, M, hM⟩ := hGbd i x hx g
    obtain ⟨ε, hε, U', hU', M', hM'⟩ := hdecay x g
    have key := GlobalTheory.T.inverse_transform_recovers_function X (G i g) x hc1 ⟨M, fun y' => hM g (mem_of_mem_nhds hU) y'⟩
      (by rw [hphi]; exact hφt g)
      ⟨ε, hε, M', fun t => by
        rw [hall i g x hx t]
        exact hM' x (by simp [hε.le]) (by simp [hε.le]) g (mem_of_mem_nhds hU') t⟩ y
    rw [hphi, hxdef, hydef, pt_re_im] at key
    simpa [G, gauss] using key
end GlobalTheory.CompanionTheory.TubeFourier
