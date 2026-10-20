-- Prove2me | solution 1 for OAI.LipschitzCounterexample.CompactWSC.exists_smooth_finite_min
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:30:17.456205+00:00
-- url     : https://prove2.me/submissions/8ae6e6cf-97a8-4615-aad0-8f9fc2079d2c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/SmoothHilbert.lean:L131-L177
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.CompactWSC.exists_smooth_finite_min. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLocalization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompleteContinuity
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SupportedDuality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Multipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteMultipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactSupports
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CauchyReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBlocks
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothHilbert

-- ---- from OAI.Analysis.LipschitzEquivalence.SmoothHilbert ----
namespace OAI

universe uH uX

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open Filter Topology
open scoped NNReal ContDiff
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem regularNorm_nonneg {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (ε : ℝ) (x : H) : 0 ≤ regularNorm ε x := Real.sqrt_nonneg _

theorem regularNorm_sq {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (ε : ℝ) (x : H) : (regularNorm ε x)^2 = ‖x‖^2+ε^2 :=
  Real.sq_sqrt (by positivity)

theorem norm_le_regularNorm (ε : ℝ) (x : H) : ‖x‖ ≤ regularNorm ε x := by
  have := regularNorm_sq ε x
  have := regularNorm_nonneg ε x
  nlinarith [norm_nonneg x, sq_nonneg ε]

theorem regularNorm_le (ε : ℝ) (hε : 0 ≤ ε) (x : H) : regularNorm ε x ≤ ‖x‖+ε := by
  have := regularNorm_sq ε x
  have := regularNorm_nonneg ε x
  nlinarith [norm_nonneg x, mul_nonneg (norm_nonneg x) hε]

theorem regularNorm_sub_le (ε : ℝ) (x y : H) : regularNorm ε x - regularNorm ε y ≤ dist x y := by
  have hx := regularNorm_sq ε x
  have hy := regularNorm_sq ε y
  have hx0 := regularNorm_nonneg ε x
  have hy0 := regularNorm_nonneg ε y
  have hny := norm_le_regularNorm ε y
  have hxy : ‖x‖ ≤ ‖y‖+dist x y := by
    simpa [dist_eq_norm, add_comm] using norm_le_norm_add_norm_sub' x y
  have hs : ‖x‖^2 ≤ (‖y‖+dist x y)^2 := by
    exact sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hxy
  have hm := mul_nonneg (sub_nonneg.mpr hny) (dist_nonneg (x := x) (y := y))
  have hsq : (regularNorm ε x)^2 ≤ (regularNorm ε y+dist x y)^2 := by nlinarith
  have hle := (sq_le_sq₀ hx0 (add_nonneg hy0 dist_nonneg)).mp hsq
  linarith

theorem regularNorm_lipschitz (ε : ℝ) : LipschitzWith 1 (regularNorm (H := H) ε) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, abs_le]
  exact ⟨by have := regularNorm_sub_le ε y x; rw [dist_comm y x] at this; linarith, regularNorm_sub_le ε x y⟩

theorem regularNorm_contDiff {ε : ℝ} (hε : ε ≠ 0) : ContDiff ℝ ∞ (regularNorm (H := H) ε) := by
  apply ((contDiff_norm_sq ℝ).add contDiff_const).sqrt
  intro x
  have : 0 < ‖x‖^2+ε^2 := by positivity
  exact this.ne'

theorem softMin_mono_left (ε b : ℝ) : Monotone (fun a => softMin ε a b) := by
  intro a c hac
  have h := (regularNorm_lipschitz (H := ℝ) ε).dist_le_mul (c-b) (a-b)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, sub_sub_sub_cancel_right,
    abs_of_nonneg (sub_nonneg.mpr hac)] at h
  have := le_abs_self (regularNorm ε (c-b)-regularNorm ε (a-b))
  dsimp [softMin]
  linarith

theorem regularNorm_neg {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (ε : ℝ) (x : H) : regularNorm ε (-x) = regularNorm ε x := by
  simp [regularNorm]

theorem softMin_comm (ε a b : ℝ) : softMin ε a b = softMin ε b a := by
  rw [softMin, softMin, ← neg_sub a b, regularNorm_neg]
  ring

theorem softMin_mono_right (ε a : ℝ) : Monotone (softMin ε a) := by
  intro b c hbc
  simpa only [softMin_comm ε a] using softMin_mono_left ε a hbc

theorem softMin_mono (ε : ℝ) {a b c d : ℝ} (hac : a ≤ c) (hbd : b ≤ d) :
    softMin ε a b ≤ softMin ε c d :=
  (softMin_mono_left ε b hac).trans (softMin_mono_right ε c hbd)

theorem softMin_add (ε a b c : ℝ) : softMin ε (a+c) (b+c) = softMin ε a b+c := by
  simp only [softMin, add_sub_add_right_eq_sub]
  ring

theorem softMin_le_min (ε a b : ℝ) : softMin ε a b ≤ min a b := by
  have h := norm_le_regularNorm ε (a-b)
  rw [Real.norm_eq_abs] at h
  dsimp [softMin]
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, abs_of_nonpos (sub_nonpos.mpr hab)] at *
    linarith
  · rw [min_eq_right hba, abs_of_nonneg (sub_nonneg.mpr hba)] at *
    linarith

theorem min_sub_le_softMin (ε : ℝ) (hε : 0 ≤ ε) (a b : ℝ) :
    min a b-ε/2 ≤ softMin ε a b := by
  have h := regularNorm_le ε hε (a-b)
  rw [Real.norm_eq_abs] at h
  dsimp [softMin]
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, abs_of_nonpos (sub_nonpos.mpr hab)] at *
    linarith
  · rw [min_eq_right hba, abs_of_nonneg (sub_nonneg.mpr hba)] at *
    linarith

theorem softMin_lipschitz {X : Type uX} [PseudoMetricSpace X] {C : ℝ≥0}
    (ε : ℝ) {f g : X → ℝ} (hf : LipschitzWith C f) (hg : LipschitzWith C g) :
    LipschitzWith C (fun x => softMin ε (f x) (g x)) := by
  have hle (x y : X) : softMin ε (f x) (g x) - softMin ε (f y) (g y) ≤ C*dist x y := by
    have hf' := (abs_le.mp (hf.dist_le_mul x y)).2
    have hg' := (abs_le.mp (hg.dist_le_mul x y)).2
    have h := softMin_mono ε (show f x ≤ f y+C*dist x y by linarith)
      (show g x ≤ g y+C*dist x y by linarith)
    rw [softMin_add] at h
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, abs_le]
  exact ⟨by have := hle y x; rw [dist_comm y x] at this; linarith, hle x y⟩

theorem softMin_contDiff {ε : ℝ} (hε : ε ≠ 0) {f g : H → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x => softMin ε (f x) (g x)) :=
  ((hf.add hg).sub ((regularNorm_contDiff hε).comp (hf.sub hg))).div_const 2

theorem exists_smooth_finite_min (S : Finset H) (hS : (0 : H) ∈ S)
    (f : H → ℝ) (hf : ∀ p ∈ S, ∀ q ∈ S, |f p-f q| ≤ dist p q)
    (δ : ℝ) (hδ : 0 < δ) (t : Finset H) (ht : t ⊆ S) :
    ∃ g : H → ℝ, ContDiff ℝ ∞ g ∧ LipschitzWith 1 g ∧
      (∀ q ∈ S, f q-(t.card : ℝ)*δ/2 ≤ g q) ∧
      (∀ p ∈ t, g p ≤ f p+δ) := by
  classical
  have hcone (p : H) (hp : p ∈ S) :
      ∀ q ∈ S, f q ≤ f p+regularNorm δ (q-p) := by
    intro q hq
    have h := (abs_le.mp (hf q hq p hp)).2
    rw [dist_eq_norm] at h
    have := norm_le_regularNorm δ (q-p)
    linarith
  have hcont (p : H) : ContDiff ℝ ∞ (fun x : H => f p+regularNorm δ (x-p)) :=
    contDiff_const.add ((regularNorm_contDiff hδ.ne').comp (contDiff_id.sub contDiff_const))
  have hlip (p : H) : LipschitzWith 1 (fun x : H => f p+regularNorm δ (x-p)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_add_left,dist_sub_right] using
      (regularNorm_lipschitz (H := H) δ).dist_le_mul (x-p) (y-p)
  induction t using Finset.induction_on with
  | empty =>
    refine ⟨fun x => f 0+regularNorm δ (x-0), hcont 0, hlip 0, ?_, by simp⟩
    intro q hq
    simpa using hcone 0 hS q hq
  | @insert a t ha ih =>
    have hat : a ∈ S := ht (Finset.mem_insert_self _ _)
    have htt : t ⊆ S := fun p hp => ht (Finset.mem_insert_of_mem hp)
    obtain ⟨g,hg,hgL,hlo,hup⟩ := ih htt
    refine ⟨fun x => softMin δ (g x) (f a+regularNorm δ (x-a)),
      softMin_contDiff hδ.ne' hg (hcont a), softMin_lipschitz δ hgL (hlip a), ?_, ?_⟩
    · intro q hq
      have hm := min_sub_le_softMin δ hδ.le (g q) (f a+regularNorm δ (q-a))
      have hc := hcone a hat q hq
      have hn : 0 ≤ (t.card : ℝ)*δ/2 := by positivity
      have hmin : f q-(t.card : ℝ)*δ/2 ≤ min (g q) (f a+regularNorm δ (q-a)) :=
        le_min (hlo q hq) (by linarith)
      rw [Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
      linarith
    · intro p hp
      have hm := softMin_le_min δ (g p) (f a+regularNorm δ (p-a))
      rcases Finset.mem_insert.mp hp with rfl | hp
      · have hreg : regularNorm δ (p-p) = δ := by
          simp [regularNorm, Real.sqrt_sq_eq_abs, abs_of_pos hδ]
        exact hm.trans ((min_le_right _ _).trans_eq (by rw [hreg]))
      · exact hm.trans ((min_le_left _ _).trans (hup p hp))

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
open Filter Topology
open scoped NNReal ContDiff


theorem solution.{uH} : type_of% @_root_.OAI.LipschitzCounterexample.CompactWSC.exists_smooth_finite_min.{uH} := @_root_.OAI.LipschitzCounterexample.CompactWSC.exists_smooth_finite_min.{uH}
