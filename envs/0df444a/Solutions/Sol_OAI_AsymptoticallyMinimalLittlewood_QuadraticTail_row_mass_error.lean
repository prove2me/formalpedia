-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.row_mass_error
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:29:46.845588+00:00
-- url     : https://prove2.me/submissions/54de2012-e110-4e11-b4e8-ac4fdbee53f6

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/QuadraticTail.lean:L495-L541
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.row_mass_error. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_circleChirp_coefficient
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_circleChirp_mass
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_latticeWeight_summable
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_offbox_weighted

-- ---- from OAI.Analysis.Littlewood.QuadraticTail ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
namespace OAI

universe uI uZ

namespace AsymptoticallyMinimalLittlewood
namespace QuadraticTail
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff

lemma phase_norm (t u x : ℝ) : ‖phase t u x‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Real.exp_zero]

lemma phase_smooth (t u : ℝ) : ContDiff ℝ ∞ (phase t u) := by
  have hc : ContDiff ℝ ∞ (fun x : ℝ ↦ 2*Real.pi*(t*x^2/2-u*x)) := by fun_prop
  exact ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ ↦ Complex.I)).mul
    (Complex.ofRealCLM.contDiff.comp hc)).cexp

lemma cutoff_zero {g : ℝ → ℂ} {α x : ℝ}
    (hs : tsupport g ⊆ Set.Icc (-α) α) (hx : x ∉ Set.Icc (-α) α) : g x=0 :=
  image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))

lemma circleChirp_continuous {g : ℝ → ℂ} (hg : Continuous g) {α : ℝ}
    (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α) (t : ℝ) :
    Continuous (circleChirp g t) := by
  apply AddCircle.liftIoc_continuous
  · have hleft : g (-1/2)=0 := cutoff_zero hs (by intro h; rcases h with ⟨h1,h2⟩; linarith)
    have hright : g (-1/2+1)=0 := cutoff_zero hs (by intro h; rcases h with ⟨h1,h2⟩; linarith)
    simp only [hleft,hright,zero_mul]
  · exact (hg.mul (phase_smooth t 0).continuous).continuousOn

lemma latticeWeight_pos (w : ℤ) : 0 < latticeWeight w := by
  dsimp [latticeWeight]
  positivity

lemma circle_fourier_norm (w : ℤ) (z : UnitAddCircle) : ‖fourier w z‖=1 :=
  Circle.norm_coe _

lemma circleChirp_norm {g : ℝ → ℂ} (hg : ∀ x, ‖g x‖ ≤ 1)
    (t : ℝ) (z : UnitAddCircle) : ‖circleChirp g t z‖ ≤ 1 := by
  dsimp [circleChirp, AddCircle.liftIoc, Function.comp_def, Set.domRestrict]
  rw [norm_mul, phase_norm, mul_one]
  exact hg _

lemma circle_parseval (f : C(UnitAddCircle,ℂ)) :
    HasSum (fun w : ℤ ↦ ‖fourierCoeff f w‖^2)
      (∫ z : UnitAddCircle, ‖f z‖^2 ∂AddCircle.haarAddCircle) := by
  have hh := hasSum_sq_fourierCoeff (f.toLp 2 AddCircle.haarAddCircle ℂ)
  simp only [fourierCoeff_toLp] at hh
  convert hh using 1
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle] with x hx
  rw [hx]

lemma coefficient_norm_le_one (f : C(UnitAddCircle,ℂ)) (hf : ∀ z, ‖f z‖≤1)
    (w : ℤ) : ‖fourierCoeff f w‖ ≤ 1 := by
  unfold fourierCoeff
  calc
    _ ≤ ∫ z : UnitAddCircle, ‖fourier (-w) z • f z‖ ∂AddCircle.haarAddCircle :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _z : UnitAddCircle, (1:ℝ) ∂AddCircle.haarAddCircle := by
      apply integral_mono
      · exact (show Continuous (fun z ↦ ‖fourier (-w) z • f z‖) by fun_prop).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact integrable_const _
      · intro z
        simpa only [norm_smul, circle_fourier_norm, one_mul] using hf z
    _ = 1 := by simp

/-- Retained squared Fourier mass loses only O(1/T), uniformly in the
quadratic modulation. This is the scalar Parseval ingredient for spreading. -/
theorem row_mass_error {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hg1 : ∀ x, ‖g x‖≤1) {α : ℝ}
    (hα0 : 0≤α) (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α)
    {β : ℝ} (hβ : β ≠ 0) :
    ∃ C : ℝ, 0≤C ∧ ∀ T : ℝ, 1≤T →
      (∫ x : ℝ, ‖g x‖^2) - C/T ≤
        ∑ w ∈ box T β, ‖∫ x : ℝ, g x*phase (T*β) w x‖^2 := by
  obtain ⟨C,hC,hbound⟩ := offbox_weighted hg hgs hα0 hα hs hβ 1
  refine ⟨C*(∑' w, latticeWeight w),mul_nonneg hC (tsum_nonneg (fun w ↦ (latticeWeight_pos w).le)),?_⟩
  intro T hT
  let f : C(UnitAddCircle,ℂ) := ⟨circleChirp g (T*β),circleChirp_continuous hgs.continuous hα hs _⟩
  have hf (w : ℤ) : fourierCoeff f w = ∫ x : ℝ, g x*phase (T*β) w x :=
    circleChirp_coefficient hα hs _ _
  have hp := circle_parseval f
  change HasSum _ (∫ z : UnitAddCircle, ‖circleChirp g (T*β) z‖^2 ∂AddCircle.haarAddCircle) at hp
  rw [circleChirp_mass hα hs] at hp
  have he := hp.summable.sum_add_tsum_compl (s := box T β)
  rw [hp.tsum_eq] at he
  change (∑ w ∈ box T β, ‖fourierCoeff f w‖^2) +
    (∑' w : {w : ℤ // w ∉ box T β}, ‖fourierCoeff f w.val‖^2) = _ at he
  have ht : (∑' w : {w : ℤ // w ∉ box T β}, ‖fourierCoeff f w.val‖^2) ≤
      C/T*(∑' w, latticeWeight w) := by
    calc
      _ ≤ ∑' w : {w : ℤ // w ∉ box T β}, C/T*latticeWeight w.val := by
        apply (hp.summable.subtype _).tsum_le_tsum
        · intro w
          have hn := coefficient_norm_le_one f (circleChirp_norm hg1 _) w.val
          have hb := hbound T hT w.val w.property
          change ‖fourierCoeff f w.val‖^2 ≤ _
          rw [hf]
          have hn' := norm_nonneg (fourierCoeff f w.val)
          rw [hf] at hn hn'
          simpa only [pow_one] using (show ‖∫ x : ℝ, g x*phase (T*β) w.val x‖^2 ≤
            C/T^1*latticeWeight w.val by nlinarith only [hn,hn',hb])
        · exact (latticeWeight_summable.mul_left (C/T)).subtype _
      _ ≤ ∑' w : ℤ, C/T*latticeWeight w := by
        exact ((latticeWeight_summable.mul_left (C/T)).subtype _).tsum_le_tsum_of_inj
          Subtype.val Subtype.val_injective
          (fun w _ ↦ mul_nonneg (div_nonneg hC (by linarith)) (latticeWeight_pos w).le)
          (fun _ ↦ le_rfl) (latticeWeight_summable.mul_left (C/T))
      _ = _ := tsum_mul_left
  simp_rw [hf] at he ht
  have heq : C/T*(∑' w, latticeWeight w) = (C*(∑' w, latticeWeight w))/T := by ring
  rw [heq] at ht
  linarith

end
end QuadraticTail
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.QuadraticTail
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.row_mass_error := @_root_.OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.row_mass_error
