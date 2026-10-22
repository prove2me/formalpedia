-- Prove2me | solution 1 for ModPolicyIter.Conv.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:06:40.42086+00:00
-- url     : https://prove2.me/submissions/d7a3533d-b21c-4f22-a509-942ab362fe9b

import Mathlib
import Definitions.Def_ModPolicyIter_Conv_Setting

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

namespace MPIH

variable {S : Type*} [MeasurableSpace S] {ι : Type*} (m : Model S ι)

/-- the term of `U^k` for policy `i`. -/
noncomputable def Uterm (k : ℕ) (i : ι) (v : S → ℝ) (s : S) : ℝ :=
  (∑ j ∈ Finset.range (k + 1), m.lam ^ j * (Pop m i)^[j] (m.c i) s)
    + m.lam ^ (k + 1) * (Pop m i)^[k + 1] v s

lemma Uterm_bdd (k : ℕ) {v : S → ℝ} (hv : IsBM v) (s : S) :
    BddAbove (Set.range fun i => Uterm m k i v s) := by
  have hv' := hv
  obtain ⟨_, C, hC⟩ := hv'
  have hl := m.lam_nonneg
  refine ⟨(∑ j ∈ Finset.range (k + 1), m.lam ^ j * m.M) + m.lam ^ (k + 1) * C, ?_⟩
  rintro _ ⟨i, rfl⟩
  unfold Uterm
  apply add_le_add
  · apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hl j)
    exact (abs_le.1 (iter_abs_le m i (c_bm m i) (m.c_bdd i) j s)).2
  · apply mul_le_mul_of_nonneg_left _ (pow_nonneg hl _)
    exact (abs_le.1 (iter_abs_le m i hv hC (k + 1) s)).2

lemma U_eq (k : ℕ) (v : S → ℝ) (s : S) : U m k v s = ⨆ i, Uterm m k i v s := rfl

lemma Uterm_le_U (k : ℕ) {v : S → ℝ} (hv : IsBM v) (i : ι) (s : S) :
    Uterm m k i v s ≤ U m k v s :=
  le_ciSup (Uterm_bdd m k hv s) i

lemma Apow_bm (i : ι) (k : ℕ) {f : S → ℝ} (hf : IsBM f) : IsBM (Apow m i k f) :=
  bm_sum (k + 1) (fun j => m.lam ^ j) (fun j => (Pop m i)^[j] f) (fun j => iter_bm m i hf j)

lemma tele (i : ι) {v : S → ℝ} (hv : IsBM v) (k : ℕ) (s : S) :
    v s + Apow m i k (fun t => m.c i t + m.lam * Pop m i v t - v t) s = Uterm m k i v s := by
  have hf : (fun t => m.c i t + m.lam * Pop m i v t - v t)
      = (m.c i + fun t => m.lam * Pop m i v t) - v := by
    funext t; simp
  have hbm1 : IsBM (fun t => m.lam * Pop m i v t) := bm_const_mul m.lam (Pop_bm m i hv)
  have hbm2 : IsBM (m.c i + fun t => m.lam * Pop m i v t) := bm_add (c_bm m i) hbm1
  induction k with
  | zero =>
    simp [Apow, Uterm]
  | succ k ih =>
    have e : Apow m i (k + 1) (fun t => m.c i t + m.lam * Pop m i v t - v t) s
        = Apow m i k (fun t => m.c i t + m.lam * Pop m i v t - v t) s
          + m.lam ^ (k + 1) * (Pop m i)^[k + 1]
            (fun t => m.c i t + m.lam * Pop m i v t - v t) s := by
      unfold Apow
      rw [Finset.sum_range_succ]
    have e2 : (Pop m i)^[k + 1] (fun t => m.c i t + m.lam * Pop m i v t - v t) s
        = (Pop m i)^[k + 1] (m.c i) s + m.lam * (Pop m i)^[k + 2] v s
          - (Pop m i)^[k + 1] v s := by
      rw [hf, iter_sub m i hbm2 hv, iter_add m i (c_bm m i) hbm1, iter_smul m i m.lam (Pop m i v)]
      rw [show (Pop m i)^[k + 2] v = (Pop m i)^[k + 1] (Pop m i v) from
        Function.iterate_succ_apply (Pop m i) (k + 1) v]
    rw [e, e2]
    have ih' := ih
    unfold Uterm at ih' ⊢
    rw [Finset.sum_range_succ _ (k + 1)]
    have : m.lam ^ (k + 1 + 1) = m.lam ^ (k + 1) * m.lam := pow_succ _ _
    rw [this] at *
    linarith

lemma A_step (i : ι) {f : S → ℝ} (hf : IsBM f) (k : ℕ) (s : S) :
    f s + m.lam * Pop m i (Apow m i k f) s - Apow m i k f s
      = m.lam ^ (k + 1) * (Pop m i)^[k + 1] f s := by
  have hP : Pop m i (Apow m i k f) s
      = ∑ j ∈ Finset.range (k + 1), m.lam ^ j * (Pop m i)^[j + 1] f s := by
    have := Pop_sum m i (k + 1) (fun j => m.lam ^ j) (fun j => (Pop m i)^[j] f)
      (fun j => iter_bm m i hf j) s
    refine this.trans ?_
    apply Finset.sum_congr rfl
    intro j _
    rw [Function.iterate_succ_apply']
  have h1 : Apow m i k f s = ∑ j ∈ Finset.range k, m.lam ^ (j + 1) * (Pop m i)^[j + 1] f s + f s := by
    unfold Apow
    rw [Finset.sum_range_succ']
    simp
  have h2 : m.lam * Pop m i (Apow m i k f) s
      = ∑ j ∈ Finset.range k, m.lam ^ (j + 1) * (Pop m i)^[j + 1] f s
        + m.lam ^ (k + 1) * (Pop m i)^[k + 1] f s := by
    rw [hP, Finset.mul_sum, Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl; intro j _; ring
    · ring
  rw [h1, h2]; ring

lemma Apow_ge (i : ι) {f : S → ℝ} (hf : IsBM f) (h0 : ∀ s, 0 ≤ f s) (k : ℕ) (s : S) :
    f s ≤ Apow m i k f s := by
  have h1 : Apow m i k f s = ∑ j ∈ Finset.range k, m.lam ^ (j + 1) * (Pop m i)^[j + 1] f s + f s := by
    unfold Apow
    rw [Finset.sum_range_succ']
    simp
  rw [h1]
  have : 0 ≤ ∑ j ∈ Finset.range k, m.lam ^ (j + 1) * (Pop m i)^[j + 1] f s :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (pow_nonneg m.lam_nonneg _) (iter_nonneg m i hf h0 _ s))
  linarith

end MPIH

theorem support_inequality_proof {S : Type*} [MeasurableSpace S] {ι : Type*} (m : Model S ι) :
    ∀ v w : S → ℝ, IsBM v → IsBM w → ∀ i, Attains m v i →
      ∀ s, B m v s + (m.lam * Pop m i (w - v) s - (w - v) s) ≤ B m w s := by
  intro v w hv hw i hatt s
  rw [MPIH.B_eq m hv hatt s, MPIH.Pop_sub m i hw hv s]
  have := MPIH.B_ge m hw i s
  simp only [Pi.sub_apply]
  linarith

theorem lemma_4_proof {S : Type*} [MeasurableSpace S] {ι : Type*} (m : Model S ι)
    (hmax : MaxAttained m) (k : ℕ) :
    ∀ u ∈ VB m, ∀ i, Attains m u i → (u + Apow m i k (B m u)) ∈ VB m := by
  intro u hu i hatt
  obtain ⟨hubm, hB⟩ := hu
  have hf : IsBM (B m u) := MPIH.B_bm m hubm hatt
  have hz : IsBM (Apow m i k (B m u)) := MPIH.Apow_bm m i k hf
  have hw : IsBM (u + Apow m i k (B m u)) := MPIH.bm_add hubm hz
  refine ⟨hw, fun s => ?_⟩
  have h1 := support_inequality_proof m u (u + Apow m i k (B m u)) hubm hw i hatt s
  have h2 : (u + Apow m i k (B m u)) - u = Apow m i k (B m u) := by
    funext t; simp
  rw [h2] at h1
  have h3 := MPIH.A_step m i hf k s
  have h4 : 0 ≤ m.lam ^ (k + 1) * (Pop m i)^[k + 1] (B m u) s :=
    mul_nonneg (pow_nonneg m.lam_nonneg _) (MPIH.iter_nonneg m i hf hB _ s)
  linarith

theorem solution {S : Type*} [MeasurableSpace S] {ι : Type*} (m : Model S ι)
    (hmax : MaxAttained m) (k : ℕ) :
    ∀ u ∈ VB m, ∀ i, Attains m u i → (u + Apow m i k (B m u)) ∈ VB m :=
  lemma_4_proof m hmax k
