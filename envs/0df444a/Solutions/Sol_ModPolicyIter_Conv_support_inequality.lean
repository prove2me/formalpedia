-- Prove2me | solution 1 for ModPolicyIter.Conv.support_inequality
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:03:06.716159+00:00
-- url     : https://prove2.me/submissions/58899ee8-db3f-4bc3-949c-d557946ce094

import Mathlib
import Definitions.Def_ModPolicyIter_Conv_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open ModPolicyIter.Conv

namespace MPIH

variable {S : Type*} [MeasurableSpace S] {ι : Type*} (m : Model S ι)

lemma integrable_bm (i : ι) (s : S) {f : S → ℝ} (hf : IsBM f) : Integrable f (m.P i s) := by
  have := m.isMarkov i
  obtain ⟨hm, C, hC⟩ := hf
  exact ⟨hm.aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := C) (ae_of_all _ (fun t => by simpa using hC t))⟩

lemma Pop_abs_le (i : ι) {f : S → ℝ} (hf : IsBM f) {C : ℝ} (hC : ∀ s, |f s| ≤ C) (s : S) :
    |Pop m i f s| ≤ C := by
  have := m.isMarkov i
  unfold Pop
  have h := norm_integral_le_of_norm_le_const (μ := m.P i s) (f := f) (C := C)
    (ae_of_all _ (fun t => by simpa using hC t))
  simpa using h

lemma Pop_bm (i : ι) {f : S → ℝ} (hf : IsBM f) : IsBM (Pop m i f) := by
  obtain ⟨hm, C, hC⟩ := hf
  refine ⟨?_, C, fun s => Pop_abs_le m i ⟨hm, C, hC⟩ hC s⟩
  exact (hm.stronglyMeasurable.integral_kernel (κ := m.P i)).measurable

lemma Pop_mono (i : ι) {f g : S → ℝ} (hf : IsBM f) (hg : IsBM g) (h : ∀ s, f s ≤ g s) (s : S) :
    Pop m i f s ≤ Pop m i g s :=
  integral_mono (integrable_bm m i s hf) (integrable_bm m i s hg) h

lemma Pop_nonneg (i : ι) {f : S → ℝ} (h : ∀ s, 0 ≤ f s) (s : S) : 0 ≤ Pop m i f s :=
  integral_nonneg h

lemma Pop_sub (i : ι) {f g : S → ℝ} (hf : IsBM f) (hg : IsBM g) (s : S) :
    Pop m i (f - g) s = Pop m i f s - Pop m i g s :=
  integral_sub (integrable_bm m i s hf) (integrable_bm m i s hg)

lemma Pop_add (i : ι) {f g : S → ℝ} (hf : IsBM f) (hg : IsBM g) (s : S) :
    Pop m i (f + g) s = Pop m i f s + Pop m i g s :=
  integral_add (integrable_bm m i s hf) (integrable_bm m i s hg)

lemma Pop_smul (i : ι) (c : ℝ) (f : S → ℝ) (s : S) :
    Pop m i (fun t => c * f t) s = c * Pop m i f s := by
  unfold Pop
  exact integral_const_mul c f

lemma Pop_sum (i : ι) (n : ℕ) (c : ℕ → ℝ) (g : ℕ → S → ℝ) (hg : ∀ j, IsBM (g j)) (s : S) :
    Pop m i (fun t => ∑ j ∈ Finset.range n, c j * g j t) s
      = ∑ j ∈ Finset.range n, c j * Pop m i (g j) s := by
  unfold Pop
  rw [integral_finsetSum _ (fun j _ => (integrable_bm m i s (hg j)).const_mul (c j))]
  exact Finset.sum_congr rfl (fun j _ => integral_const_mul (c j) (g j))

lemma bm_const_mul (c : ℝ) {f : S → ℝ} (hf : IsBM f) : IsBM (fun t => c * f t) := by
  obtain ⟨hm, C, hC⟩ := hf
  refine ⟨hm.const_mul c, |c| * C, fun s => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hC s) (abs_nonneg c)

lemma bm_add {f g : S → ℝ} (hf : IsBM f) (hg : IsBM g) : IsBM (f + g) := by
  obtain ⟨hm, C, hC⟩ := hf
  obtain ⟨hm', C', hC'⟩ := hg
  refine ⟨hm.add hm', C + C', fun s => ?_⟩
  exact (abs_add_le _ _).trans (add_le_add (hC s) (hC' s))

lemma bm_sub {f g : S → ℝ} (hf : IsBM f) (hg : IsBM g) : IsBM (f - g) := by
  have := bm_add hf (bm_const_mul (-1) hg)
  convert this using 1
  ext s; simp [sub_eq_add_neg]

lemma bm_sum (n : ℕ) (c : ℕ → ℝ) (g : ℕ → S → ℝ) (hg : ∀ j, IsBM (g j)) :
    IsBM (fun t => ∑ j ∈ Finset.range n, c j * g j t) := by
  induction n with
  | zero => exact ⟨measurable_const, 0, fun s => by simp⟩
  | succ n ih =>
    have := bm_add ih (bm_const_mul (c n) (hg n))
    convert this using 1
    ext s; simp [Finset.sum_range_succ]

lemma bm_const (c : ℝ) : IsBM (fun _ : S => c) := ⟨measurable_const, |c|, fun _ => le_rfl⟩

lemma iter_bm (i : ι) {f : S → ℝ} (hf : IsBM f) (j : ℕ) : IsBM ((Pop m i)^[j] f) := by
  induction j with
  | zero => simpa using hf
  | succ j ih => rw [Function.iterate_succ_apply']; exact Pop_bm m i ih

lemma iter_abs_le (i : ι) {f : S → ℝ} (hf : IsBM f) {C : ℝ} (hC : ∀ s, |f s| ≤ C) (j : ℕ)
    (s : S) : |(Pop m i)^[j] f s| ≤ C := by
  induction j generalizing s with
  | zero => simpa using hC s
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact Pop_abs_le m i (iter_bm m i hf j) ih s

lemma iter_mono (i : ι) {f g : S → ℝ} (hf : IsBM f) (hg : IsBM g) (h : ∀ s, f s ≤ g s) (j : ℕ) :
    ∀ s, (Pop m i)^[j] f s ≤ (Pop m i)^[j] g s := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    intro s
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact Pop_mono m i (iter_bm m i hf j) (iter_bm m i hg j) ih s

lemma iter_zero (i : ι) (j : ℕ) : (Pop m i)^[j] (fun _ : S => (0 : ℝ)) = fun _ => 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    funext s
    unfold Pop
    simp

lemma iter_nonneg (i : ι) {f : S → ℝ} (hf : IsBM f) (h : ∀ s, 0 ≤ f s) (j : ℕ) :
    ∀ s, 0 ≤ (Pop m i)^[j] f s := by
  have := iter_mono m i (bm_const (S := S) 0) hf (fun s => by simpa using h s) j
  intro s
  have h1 := this s
  rwa [iter_zero] at h1

lemma iter_sub (i : ι) {f g : S → ℝ} (hf : IsBM f) (hg : IsBM g) (j : ℕ) (s : S) :
    (Pop m i)^[j] (f - g) s = (Pop m i)^[j] f s - (Pop m i)^[j] g s := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply']
    have : (Pop m i)^[j] (f - g) = (Pop m i)^[j] f - (Pop m i)^[j] g := funext (fun s => by
      simpa using ih s)
    rw [this, Pop_sub m i (iter_bm m i hf j) (iter_bm m i hg j)]

lemma iter_add (i : ι) {f g : S → ℝ} (hf : IsBM f) (hg : IsBM g) (j : ℕ) (s : S) :
    (Pop m i)^[j] (f + g) s = (Pop m i)^[j] f s + (Pop m i)^[j] g s := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply']
    have : (Pop m i)^[j] (f + g) = (Pop m i)^[j] f + (Pop m i)^[j] g := funext (fun s => by
      simpa using ih s)
    rw [this, Pop_add m i (iter_bm m i hf j) (iter_bm m i hg j)]

lemma iter_smul (i : ι) (c : ℝ) (f : S → ℝ) (j : ℕ) (s : S) :
    (Pop m i)^[j] (fun t => c * f t) s = c * (Pop m i)^[j] f s := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have : (Pop m i)^[j] (fun t => c * f t) = fun t => c * (Pop m i)^[j] f t := funext ih
    rw [this, Pop_smul]

end MPIH

namespace MPIH

variable {S : Type*} [MeasurableSpace S] {ι : Type*} (m : Model S ι)

lemma c_bm (i : ι) : IsBM (m.c i) := ⟨m.c_meas i, m.M, m.c_bdd i⟩

lemma term_bdd {v : S → ℝ} (hv : IsBM v) (s : S) :
    BddAbove (Set.range fun j => m.c j s + m.lam * Pop m j v s) := by
  have hv' := hv
  obtain ⟨_, C, hC⟩ := hv'
  refine ⟨m.M + m.lam * C, ?_⟩
  rintro _ ⟨j, rfl⟩
  have h1 := m.c_bdd j s
  have h2 := Pop_abs_le m j hv hC s
  have h3 := (abs_le.1 h1).2
  have h4 := (abs_le.1 h2).2
  have := m.lam_nonneg
  nlinarith

lemma B_eq {v : S → ℝ} (hv : IsBM v) {i : ι} (hatt : Attains m v i) (s : S) :
    B m v s = m.c i s + m.lam * Pop m i v s - v s := by
  have : Nonempty ι := ⟨i⟩
  unfold B
  congr 1
  exact le_antisymm (ciSup_le fun j => hatt j s) (le_ciSup (term_bdd m hv s) i)

lemma B_ge {v : S → ℝ} (hv : IsBM v) (i : ι) (s : S) :
    m.c i s + m.lam * Pop m i v s - v s ≤ B m v s := by
  unfold B
  exact sub_le_sub_right (le_ciSup (term_bdd m hv s) i) _

lemma B_bm {v : S → ℝ} (hv : IsBM v) {i : ι} (hatt : Attains m v i) : IsBM (B m v) := by
  have h : B m v = (m.c i + fun s => m.lam * Pop m i v s) - v := by
    funext s
    simp [B_eq m hv hatt s]
  rw [h]
  exact bm_sub (bm_add (c_bm m i) (bm_const_mul m.lam (Pop_bm m i hv))) hv


end MPIH

theorem support_inequality_proof {S : Type*} [MeasurableSpace S] {ι : Type*} (m : Model S ι) :
    ∀ v w : S → ℝ, IsBM v → IsBM w → ∀ i, Attains m v i →
      ∀ s, B m v s + (m.lam * Pop m i (w - v) s - (w - v) s) ≤ B m w s := by
  intro v w hv hw i hatt s
  rw [MPIH.B_eq m hv hatt s, MPIH.Pop_sub m i hw hv s]
  have := MPIH.B_ge m hw i s
  simp only [Pi.sub_apply]
  linarith


theorem solution {S : Type*} [MeasurableSpace S] {ι : Type*} (m : Model S ι) :
    ∀ v w : S → ℝ, IsBM v → IsBM w → ∀ i, Attains m v i →
      ∀ s, B m v s + (m.lam * Pop m i (w - v) s - (w - v) s) ≤ B m w s :=
  support_inequality_proof m
