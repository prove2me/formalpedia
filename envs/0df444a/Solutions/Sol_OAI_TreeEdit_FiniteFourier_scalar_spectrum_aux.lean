-- Prove2me | solution 1 for OAI.TreeEdit.FiniteFourier.scalar_spectrum_aux
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:59:18.311209+00:00
-- url     : https://prove2.me/submissions/c06cd883-da2c-43e2-aea5-abce39788541

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/FiniteFourier.lean:L145-L191
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.FiniteFourier.scalar_spectrum_aux. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier

-- ---- from OAI.Combinatorics.TreeEdit.FiniteFourier ----
namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

namespace FiniteFourier

open scoped ComplexConjugate
open RCLike

variable {A : Type*} [Fintype A] [AddCommGroup A]

lemma expansion (f : A → ℂ) (x : A) :
    ∑ χ : AddChar A ℂ, coefficient f χ * χ x = f x := by
  simpa [coefficient, AddChar.complexBasis_apply, Pi.smul_apply, smul_eq_mul]
    using congr_fun ((AddChar.complexBasis A).sum_repr f) x

omit [AddCommGroup A] in
lemma weighted_sum_right {ι : Type*} (s : Finset ι) (f : A → ℂ) (g : ι → A → ℂ) :
    ⟪f, ∑ i ∈ s, g i⟫ₙ_[ℂ] = ∑ i ∈ s, ⟪f, g i⟫ₙ_[ℂ] := by
  simp only [wInner, Finset.sum_apply, inner_sum, Finset.smul_sum]
  exact Finset.sum_comm

omit [AddCommGroup A] in
lemma weighted_sum_left {ι : Type*} (s : Finset ι) (f : ι → A → ℂ) (g : A → ℂ) :
    ⟪∑ i ∈ s, f i, g⟫ₙ_[ℂ] = ∑ i ∈ s, ⟪f i, g⟫ₙ_[ℂ] := by
  simp only [wInner, Finset.sum_apply, sum_inner, Finset.smul_sum]
  exact Finset.sum_comm

lemma coefficient_inner (f : A → ℂ) (χ : AddChar A ℂ) :
    coefficient f χ = ⟪(χ : A → ℂ), f⟫ₙ_[ℂ] := by
  classical
  conv_rhs => rw [← (AddChar.complexBasis A).sum_repr f]
  simp only [weighted_sum_right, AddChar.complexBasis_apply,
    wInner_smul_right, smul_eq_mul, AddChar.wInner_cWeight_eq_boole]
  simp [coefficient]

lemma parseval_complex (f : A → ℂ) :
    ⟪f, f⟫ₙ_[ℂ] = ∑ χ : AddChar A ℂ,
      conj (coefficient f χ) * coefficient f χ := by
  conv_lhs => lhs; rw [← (AddChar.complexBasis A).sum_repr f]
  simp only [weighted_sum_left, AddChar.complexBasis_apply, wInner_smul_left,
    smul_eq_mul, ← coefficient_inner, starRingEnd_apply, coefficient]

lemma coefficient_translate (f : A → ℂ) (z : A) (χ : AddChar A ℂ) :
    coefficient (fun x => f (x + z) - f x) χ = coefficient f χ * (χ z - 1) := by
  classical
  have hexp : (fun x => f (x + z) - f x) =
      ∑ ψ : AddChar A ℂ, (coefficient f ψ * (ψ z - 1)) • (ψ : A → ℂ) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← expansion f (x + z), ← expansion f x, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ψ _
    rw [AddChar.map_add_eq_mul]
    ring
  rw [hexp, coefficient_inner, weighted_sum_right]
  simp only [wInner_smul_right, smul_eq_mul, AddChar.wInner_cWeight_eq_boole]
  simp

lemma parseval (f : A → ℂ) :
    (Fintype.card A : ℝ)⁻¹ * ∑ x, ‖f x‖ ^ 2 =
      ∑ χ : AddChar A ℂ, ‖coefficient f χ‖ ^ 2 := by
  have h := congr_arg Complex.re (parseval_complex f)
  have hn (z : ℂ) : (conj z * z).re = ‖z‖ ^ 2 := by
    simp [Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]
  simpa only [wInner, cWeight, Function.const_apply, map_sum, Complex.re_sum,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id,
    id_eq, RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.ofReal_re, ← Finset.mul_sum, hn] using h

lemma displacement_parseval (f : A → ℂ) (z : A) :
    (Fintype.card A : ℝ)⁻¹ * ∑ x, ‖f (x + z) - f x‖ ^ 2 =
      ∑ χ : AddChar A ℂ, ‖1 - χ z‖ ^ 2 * ‖coefficient f χ‖ ^ 2 := by
  rw [parseval]
  apply Finset.sum_congr rfl
  intro χ _
  rw [coefficient_translate, norm_mul, mul_pow, norm_sub_rev]
  ring

lemma spectrum_zero : HasSpectrum (fun _ : A => 0) := by
  exact ⟨fun _ => 0, by simp, rfl, by simp⟩

lemma HasSpectrum.add {V W : A → ℝ} (hV : HasSpectrum V) (hW : HasSpectrum W) :
    HasSpectrum (fun z => V z + W z) := by
  obtain ⟨H, hH, hH0, heH⟩ := hV
  obtain ⟨K, hK, hK0, heK⟩ := hW
  refine ⟨fun χ => H χ + K χ, fun χ => add_nonneg (hH χ) (hK χ), by simp [hH0, hK0], ?_⟩
  intro z
  simp [heH, heK, mul_add, Finset.sum_add_distrib]

lemma HasSpectrum.mul {V : A → ℝ} (hV : HasSpectrum V) {c : ℝ} (hc : 0 ≤ c) :
    HasSpectrum (fun z => c * V z) := by
  obtain ⟨H, hH, hH0, heH⟩ := hV
  refine ⟨fun χ => c * H χ, fun χ => mul_nonneg hc (hH χ), by simp [hH0], ?_⟩
  intro z
  simp only [heH, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ _
  ring

lemma cut_spectrum (U : A → Bool) :
    HasSpectrum (fun z => average (fun x => |(if U (x + z) then 1 else 0 : ℝ) -
      (if U x then 1 else 0)|)) := by
  classical
  let f : A → ℂ := fun x => if U x then 1 else 0
  refine ⟨fun χ => if χ = 0 then 0 else ‖coefficient f χ‖ ^ 2, ?_, by simp, ?_⟩
  · intro χ; dsimp; split_ifs <;> positivity
  · intro z
    have hd (x : A) : |(if U (x + z) then 1 else 0 : ℝ) - (if U x then 1 else 0)| =
        ‖f (x + z) - f x‖ ^ 2 := by
      dsimp [f]
      cases U (x + z) <;> cases U x <;> norm_num
    simp only [average, hd]
    rw [displacement_parseval]
    apply Finset.sum_congr rfl
    intro χ _
    by_cases h : χ = 0
    · subst χ; simp [multiplier]
    · simp [h, multiplier]

lemma scalar_spectrum_aux (s : Finset ℝ) :
    ∀ g : A → ℝ, (∀ x, g x ∈ s) →
      HasSpectrum (fun z => average (fun x => |g (x + z) - g x|)) := by
  classical
  induction s using Finset.induction_on_min with
  | empty =>
      intro g hg
      simpa using hg 0
  | insert a s hmin ih =>
      intro g hg
      by_cases hs : s.Nonempty
      · let b := s.min' hs
        have hb : b ∈ s := s.min'_mem hs
        have hab : a < b := hmin b hb
        let g' : A → ℝ := fun x => if g x = a then b else g x
        let U : A → Bool := fun x => decide (g x ≠ a)
        have hg' (x : A) : g' x ∈ s := by
          dsimp [g']
          split_ifs with h
          · exact hb
          · exact (Finset.mem_insert.mp (hg x)).resolve_left h
        have hlow (x : A) (hx : g x ≠ a) : b ≤ g x :=
          s.min'_le _ ((Finset.mem_insert.mp (hg x)).resolve_left hx)
        have hid (x y : A) : |g x - g y| = |g' x - g' y| +
            (b - a) * |(if U x then 1 else 0 : ℝ) - (if U y then 1 else 0)| := by
          by_cases hx : g x = a <;> by_cases hy : g y = a
          · simp [g', U, hx, hy]
          · have hby := hlow y hy
            simp only [g', U, hx, hy, ↓reduceIte, ne_eq, decide_eq_true_eq,
              not_true_eq_false, not_false_eq_true,
              zero_sub, abs_neg, abs_one, mul_one]
            rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
            ring
          · have hbx := hlow x hx
            simp only [g', U, hy, hx, ↓reduceIte, ne_eq, decide_eq_true_eq,
              not_true_eq_false, not_false_eq_true, sub_zero, abs_one, mul_one]
            rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
            ring
          · simp [g', U, hx, hy]
        have hspec := (ih g' hg').add ((cut_spectrum U).mul (sub_nonneg.mpr hab.le))
        convert hspec using 1
        funext z
        simp only [average, hid, Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
      · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        have hc (x : A) : g x = a := by simpa [he] using hg x
        simpa [hc, average] using (spectrum_zero (A := A))

end FiniteFourier

namespace FiniteFourier

variable {A B : Type*} [Fintype A] [Fintype B] [AddCommGroup A] [AddCommGroup B]

end FiniteFourier

namespace FiniteFourier

variable {A B : Type*} [Fintype A] [Fintype B] [AddCommGroup A] [AddCommGroup B]

end FiniteFourier

namespace FiniteFourier

variable {A : Type*} [Fintype A] [AddCommGroup A]

end FiniteFourier

end TreeEdit

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.FiniteFourier
attribute [local instance] Classical.propDecidable
open scoped ComplexConjugate
open RCLike


theorem solution : type_of% @_root_.OAI.TreeEdit.FiniteFourier.scalar_spectrum_aux := @_root_.OAI.TreeEdit.FiniteFourier.scalar_spectrum_aux
