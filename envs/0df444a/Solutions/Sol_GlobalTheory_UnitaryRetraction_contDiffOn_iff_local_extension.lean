-- Prove2me | solution 1 for GlobalTheory.UnitaryRetraction.contDiffOn_iff_local_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:09:58.304741+00:00
-- url     : https://prove2.me/submissions/63c0569c-7f7e-497e-bc63-916fabe03788

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ContDiffOnIffLocalExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
open scoped ContDiff
noncomputable section
namespace GlobalTheory.UnitaryRetraction
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section Calculus
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {s : Set X}
end Calculus
variable {H : Matrix (Fin n) (Fin n) ℂ}
open Matrix in
open scoped ContDiff in
variable {n : ℕ} in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma herm_conj_mul_eq_one_of_mem {H g : Matrix (Fin n) (Fin n) ℂ} (h2 : H * H = 1)
    (hg : gᴴ * H * g = H) : H * gᴴ * H * g = 1 := by
  calc H * gᴴ * H * g = H * (gᴴ * H * g) := by simp only [mul_assoc]
    _ = 1 := by rw [hg, h2]
open Matrix in
open scoped ContDiff in
variable {n : ℕ} in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma contDiff_entry' (i j : Fin n) :
    ContDiff ℝ ∞ (fun A : Matrix (Fin n) (Fin n) ℂ => A i j) :=
  (contDiff_apply ℝ ℂ j).comp (contDiff_apply ℝ (Fin n → ℂ) i)
open Matrix in
open scoped ContDiff in
variable {n : ℕ} in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma contDiffAt_matrix_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : E → Matrix (Fin n) (Fin n) ℂ} {x : E} (hF : ContDiffAt ℝ ∞ F x)
    (hG : ContDiffAt ℝ ∞ G x) : ContDiffAt ℝ ∞ (fun y => F y * G y) x := by
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun k _ =>
    ((contDiff_entry' i k).comp_contDiffAt x hF).mul ((contDiff_entry' k j).comp_contDiffAt x hG)
open Matrix in
open scoped ContDiff in
variable {n : ℕ} in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma contDiffAt_conjTranspose_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → Matrix (Fin n) (Fin n) ℂ} {x : E} (hF : ContDiffAt ℝ ∞ F x) :
    ContDiffAt ℝ ∞ (fun y => (F y)ᴴ) x := by
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  simp only [Matrix.conjTranspose_apply]
  exact Complex.conjCLE.contDiff.comp_contDiffAt x ((contDiff_entry' j i).comp_contDiffAt x hF)
open Matrix in
open scoped ContDiff in
variable {n : ℕ} in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma contDiffAt_skew_projection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Matrix (Fin n) (Fin n) ℂ) {F : E → Matrix (Fin n) (Fin n) ℂ} {x : E}
    (hF : ContDiffAt ℝ ∞ F x) :
    ContDiffAt ℝ ∞ (fun y => _root_.GlobalTheory.UnitaryRetraction.skewPart H (F y)) x := by
  unfold _root_.GlobalTheory.UnitaryRetraction.skewPart
  exact (hF.sub (contDiffAt_matrix_mul (contDiffAt_matrix_mul contDiffAt_const (contDiffAt_conjTranspose_comp hF))
    contDiffAt_const)).const_smul _
open Matrix in
open scoped ContDiff in
variable {n : ℕ} in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma contDiff_det_jet_harmonics : ContDiff ℝ ∞ (fun A : Matrix (Fin n) (Fin n) ℂ => A.det) := by
  have : (fun A : Matrix (Fin n) (Fin n) ℂ => A.det) =
      fun A => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A (σ i) i := by
    funext A; exact Matrix.det_apply' A
  rw [this]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => contDiff_entry' _ _)
open Matrix in
open scoped ContDiff in
variable {n : ℕ} in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma contDiff_matrix_of_entries {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → Matrix (Fin n) (Fin n) ℂ) (h : ∀ i j, ContDiff ℝ ∞ (fun x => F x i j)) :
    ContDiff ℝ ∞ F :=
  contDiff_pi.2 fun i => contDiff_pi.2 fun j => h i j
open Matrix in
open scoped ContDiff in
variable {n : ℕ} in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma contDiff_adjugate_jet_harmonics :
    ContDiff ℝ ∞ (fun A : Matrix (Fin n) (Fin n) ℂ => A.adjugate) := by
  refine contDiff_matrix_of_entries _ fun i j => ?_
  simp_rw [Matrix.adjugate_apply]
  refine contDiff_det_jet_harmonics.comp (contDiff_matrix_of_entries _ fun k l => ?_)
  by_cases hk : k = j
  · subst hk; simp only [Matrix.updateRow_self]; exact contDiff_const
  · simp only [Matrix.updateRow_ne hk]; exact contDiff_entry' k l
open Matrix in
open scoped ContDiff in
variable {n : ℕ} in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma contDiffAt_inv_of_det_ne_zero {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.det ≠ 0) :
    ContDiffAt ℝ ∞ (fun B : Matrix (Fin n) (Fin n) ℂ => B⁻¹) A := by
  have : (fun B : Matrix (Fin n) (Fin n) ℂ => B⁻¹) = fun B => (B.det)⁻¹ • B.adjugate := by
    funext B; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact ((contDiffAt_inv ℝ hA).comp A contDiff_det_jet_harmonics.contDiffAt).smul contDiff_adjugate_jet_harmonics.contDiffAt
open Matrix in
open scoped ContDiff in
variable {n : ℕ} in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma contDiffAt_cay_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → Matrix (Fin n) (Fin n) ℂ} {x : E} (hF : ContDiffAt ℝ ∞ F x)
    (hdet : (1 + F x).det ≠ 0) : ContDiffAt ℝ ∞ (fun y => _root_.GlobalTheory.UnitaryRetraction.cay (F y)) x := by
  unfold _root_.GlobalTheory.UnitaryRetraction.cay
  exact contDiffAt_matrix_mul (contDiffAt_const.sub hF)
    ((contDiffAt_inv_of_det_ne_zero hdet).comp x (contDiffAt_const.add hF))
open Matrix in
open scoped ContDiff in
variable {n : ℕ} in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma mul_preserves_herm {H g h : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * H * g = H)
    (hh : hᴴ * H * h = H) : (g * h)ᴴ * H * (g * h) = H := by
  rw [conjTranspose_mul]
  calc hᴴ * gᴴ * H * (g * h) = hᴴ * (gᴴ * H * g) * h := by simp only [mul_assoc]
    _ = H := by rw [hg, hh]
open Matrix in
open scoped ContDiff in
variable {n : ℕ} in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma cay_preserves_herm_of_skew {H X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * H + H * X = 0)
    (hu : (1 + X).det ≠ 0) :
    (_root_.GlobalTheory.UnitaryRetraction.cay X)ᴴ * H * _root_.GlobalTheory.UnitaryRetraction.cay X = H := by
  have e : (1 + X)ᴴ * H * (1 + X) - (1 - X)ᴴ * H * (1 - X) =
      (Xᴴ * H + H * X) + (Xᴴ * H + H * X) := by
    simp only [conjTranspose_add, conjTranspose_sub, conjTranspose_one]
    noncomm_ring
  rw [hX, add_zero, sub_eq_zero] at e
  have hw : (1 + X) * (1 + X)⁻¹ = 1 := mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hu)
  calc (_root_.GlobalTheory.UnitaryRetraction.cay X)ᴴ * H * _root_.GlobalTheory.UnitaryRetraction.cay X
      = ((1 + X)⁻¹)ᴴ * ((1 - X)ᴴ * H * (1 - X)) * (1 + X)⁻¹ := by
        simp only [_root_.GlobalTheory.UnitaryRetraction.cay, conjTranspose_mul, mul_assoc]
    _ = ((1 + X) * (1 + X)⁻¹)ᴴ * H * ((1 + X) * (1 + X)⁻¹) := by
        rw [← e]; simp only [conjTranspose_mul, mul_assoc]
    _ = H := by rw [hw]; simp
open Matrix in
open scoped ContDiff in
variable {n : ℕ} in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma skew_projection_is_skew {H : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ = H) (h2 : H * H = 1)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    (_root_.GlobalTheory.UnitaryRetraction.skewPart H M)ᴴ * H + H * _root_.GlobalTheory.UnitaryRetraction.skewPart H M = 0 := by
  have hHH : ∀ X : Matrix (Fin n) (Fin n) ℂ, H * (H * X) = X := fun X => by
    rw [← mul_assoc, h2, one_mul]
  unfold _root_.GlobalTheory.UnitaryRetraction.skewPart
  rw [conjTranspose_smul, star_trivial]
  simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, hH, smul_mul_assoc,
    mul_smul_comm, sub_mul, mul_sub, mul_assoc, h2, mul_one, hHH]
  rw [← smul_add]
  simp
open Matrix in
open scoped ContDiff in
variable {n : ℕ} in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma skew_cay_eq_and_cay_cay_eq {H Y : Matrix (Fin n) (Fin n) ℂ} (h2 : H * H = 1) (hY : Yᴴ * H * Y = H)
    (hu : (1 + Y).det ≠ 0) :
    _root_.GlobalTheory.UnitaryRetraction.skewPart H (_root_.GlobalTheory.UnitaryRetraction.cay Y) = _root_.GlobalTheory.UnitaryRetraction.cay Y ∧
      _root_.GlobalTheory.UnitaryRetraction.cay (_root_.GlobalTheory.UnitaryRetraction.cay Y) = Y := by
  set w := (1 + Y)⁻¹ with hwdef
  have hw1 : (1 + Y) * w = 1 := mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hu)
  have hw2 : w * (1 + Y) = 1 := nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hu)
  set A := _root_.GlobalTheory.UnitaryRetraction.cay Y with hAdef
  have hA : A = (1 - Y) * w := rfl
  have hA1 : A * (1 + Y) = 1 - Y := by rw [hA, mul_assoc, hw2, mul_one]
  have hA2 : (1 + Y)ᴴ * Aᴴ = (1 - Y)ᴴ := by rw [← conjTranspose_mul, hA1]
  have hZ' : (1 + Y)ᴴ * (Aᴴ * H + H * A) * (1 + Y) = 0 := by
    calc (1 + Y)ᴴ * (Aᴴ * H + H * A) * (1 + Y)
        = ((1 + Y)ᴴ * Aᴴ) * H * (1 + Y) + (1 + Y)ᴴ * H * (A * (1 + Y)) := by
          simp only [mul_add, add_mul, mul_assoc]; abel
      _ = (1 - Y)ᴴ * H * (1 + Y) + (1 + Y)ᴴ * H * (1 - Y) := by rw [hA2, hA1]
      _ = (H - Yᴴ * H * Y) + (H - Yᴴ * H * Y) := by
          simp only [conjTranspose_add, conjTranspose_sub, conjTranspose_one]
          noncomm_ring
      _ = 0 := by rw [hY, sub_self, add_zero]
  have hZ : Aᴴ * H + H * A = 0 := by
    calc Aᴴ * H + H * A = ((1 + Y) * w)ᴴ * (Aᴴ * H + H * A) * ((1 + Y) * w) := by
          rw [hw1]; simp
      _ = wᴴ * ((1 + Y)ᴴ * (Aᴴ * H + H * A) * (1 + Y)) * w := by
          rw [conjTranspose_mul]; simp only [mul_assoc]
      _ = 0 := by rw [hZ']; simp
  have hsum : (1 + Y) + (1 - Y) = (2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [two_smul]; abel
  have hdiff : (1 + Y) - (1 - Y) = (2 : ℂ) • Y := by
    rw [two_smul]; abel
  have hB : 1 + A = (2 : ℂ) • w := by
    rw [hA]; nth_rw 1 [← hw1]; rw [← add_mul, hsum, smul_mul_assoc, one_mul]
  have hC : 1 - A = (2 : ℂ) • (Y * w) := by
    rw [hA]; nth_rw 1 [← hw1]; rw [← sub_mul, hdiff, smul_mul_assoc]
  have hinv : (1 + A) * ((1 / 2 : ℂ) • (1 + Y)) = 1 := by
    rw [hB, smul_mul_smul_comm, hw2]; norm_num
  refine ⟨?_, ?_⟩
  · have hHA : H * Aᴴ * H = -A := by
      have : Aᴴ * H = -(H * A) := eq_neg_of_add_eq_zero_left hZ
      rw [mul_assoc, this, mul_neg, ← mul_assoc, h2, one_mul]
    unfold _root_.GlobalTheory.UnitaryRetraction.skewPart
    rw [hHA, sub_neg_eq_add, ← two_smul ℝ A, smul_smul]
    norm_num
  · unfold _root_.GlobalTheory.UnitaryRetraction.cay
    rw [Matrix.inv_eq_right_inv hinv, hC, smul_mul_smul_comm, mul_assoc, hw2, mul_one]
    norm_num
end GlobalTheory.UnitaryRetraction
end
end

set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.UnitaryRetraction
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {H : Matrix (Fin n) (Fin n) ℂ}
open Matrix
open scoped ContDiff
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {H : Matrix (Fin n) (Fin n) ℂ}
namespace GlobalTheory.UnitaryRetraction
namespace _root_.GlobalTheory.UnitaryRetraction
theorem _root_.solution (hH : Hᴴ = H) (h2 : H * H = 1) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Matrix (Fin n) (Fin n) ℂ → E) :
    ContDiffOn ℝ ∞ f {g | gᴴ * H * g = H} ↔
      ∀ g₀, g₀ᴴ * H * g₀ = H → ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ))
        (F : Matrix (Fin n) (Fin n) ℂ → E), IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
          ∀ g ∈ U, gᴴ * H * g = H → f g = F g := by
  constructor
  · intro hf g₀ hg₀
    set k := H * g₀ᴴ * H with hk
    have hkg : k * g₀ = 1 := herm_conj_mul_eq_one_of_mem h2 hg₀
    have hgk : g₀ * k = 1 := mul_eq_one_comm.1 hkg
    have hkmem : kᴴ * H * k = H := by
      have hHH : ∀ X : Matrix (Fin n) (Fin n) ℂ, H * (H * X) = X := fun X => by
        rw [← mul_assoc, h2, one_mul]
      have e : g₀ * (H * (g₀ᴴ * H)) = 1 := by rw [← hgk, hk]; simp only [mul_assoc]
      rw [hk]
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, hH, mul_assoc, hHH]
      rw [e, mul_one]
    set ψ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
      fun g => _root_.GlobalTheory.UnitaryRetraction.skewPart H (_root_.GlobalTheory.UnitaryRetraction.cay (k * g)) with hψ
    set r : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
      fun g => g₀ * _root_.GlobalTheory.UnitaryRetraction.cay (ψ g) with hr
    set T : Set (Matrix (Fin n) (Fin n) ℂ) := {g | (1 + k * g).det ≠ 0 ∧ (1 + ψ g).det ≠ 0}
    have hlin : ∀ g, ContDiffAt ℝ ∞ (fun g : Matrix (Fin n) (Fin n) ℂ => k * g) g := fun g =>
      contDiffAt_matrix_mul contDiffAt_const contDiffAt_id
    have hψs : ∀ g, (1 + k * g).det ≠ 0 → ContDiffAt ℝ ∞ ψ g := fun g hg =>
      contDiffAt_skew_projection H (contDiffAt_cay_comp (hlin g) hg)
    have hrs : ∀ g ∈ T, ContDiffAt ℝ ∞ r g := fun g hg =>
      contDiffAt_matrix_mul contDiffAt_const (contDiffAt_cay_comp (hψs g hg.1) hg.2)
    have hval1 : (1 + k * g₀).det ≠ 0 := by
      rw [hkg]
      have hinv : (1 + 1 : Matrix (Fin n) (Fin n) ℂ) * ((1 / 2 : ℂ) • 1) = 1 := by
        rw [mul_smul_comm, mul_one, ← two_smul ℂ (1 : Matrix (Fin n) (Fin n) ℂ), smul_smul]
        norm_num
      exact isUnit_iff_ne_zero.1 (Matrix.isUnit_det_of_right_inverse hinv)
    have hψ0 : ψ g₀ = 0 := by
      show _root_.GlobalTheory.UnitaryRetraction.skewPart H (_root_.GlobalTheory.UnitaryRetraction.cay (k * g₀)) = 0
      rw [hkg]
      simp [_root_.GlobalTheory.UnitaryRetraction.cay, _root_.GlobalTheory.UnitaryRetraction.skewPart]
    have hval2 : (1 + ψ g₀).det ≠ 0 := by rw [hψ0]; simp
    have hc1 : ContinuousAt (fun g => (1 + k * g).det) g₀ :=
      (contDiff_det_jet_harmonics.comp_contDiffAt g₀ (contDiffAt_const.add (hlin g₀))).continuousAt
    have hc2 : ContinuousAt (fun g => (1 + ψ g).det) g₀ :=
      (contDiff_det_jet_harmonics.comp_contDiffAt g₀ (contDiffAt_const.add (hψs g₀ hval1))).continuousAt
    have hT : T ∈ nhds g₀ := (hc1.eventually_ne hval1).and (hc2.eventually_ne hval2)
    refine ⟨interior T, f ∘ r, isOpen_interior, mem_interior_iff_mem_nhds.2 hT, ?_, ?_⟩
    · refine hf.comp (fun g hg => (hrs g (interior_subset hg)).contDiffWithinAt) ?_
      intro g hg
      have hg' := interior_subset hg
      exact mul_preserves_herm hg₀ (cay_preserves_herm_of_skew (skew_projection_is_skew hH h2 _) hg'.2)
    · intro g hg hgS
      have hY : (k * g)ᴴ * H * (k * g) = H := mul_preserves_herm hkmem hgS
      obtain ⟨h1, h3⟩ := skew_cay_eq_and_cay_cay_eq h2 hY (interior_subset hg).1
      show f g = f (g₀ * _root_.GlobalTheory.UnitaryRetraction.cay (ψ g))
      rw [hψ]
      simp only
      rw [h1, h3, ← mul_assoc, hgk, one_mul]
  · intro h g₀ hg₀
    obtain ⟨U, F, hU, hmem, hF, hfF⟩ := h g₀ hg₀
    have hFg : ContDiffWithinAt ℝ ∞ F {g | gᴴ * H * g = H} g₀ :=
      (hF.contDiffAt (hU.mem_nhds hmem)).contDiffWithinAt
    refine hFg.congr_of_eventuallyEq ?_ (hfF g₀ hmem hg₀)
    exact Filter.mem_of_superset (inter_mem_nhdsWithin _ (hU.mem_nhds hmem))
      fun g hg => hfF g hg.2 hg.1
end _root_.GlobalTheory.UnitaryRetraction
end GlobalTheory.UnitaryRetraction
