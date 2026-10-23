-- Prove2me | solution 1 for ModPolicyIter.Conv.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T09:30:46.587805+00:00
-- url     : https://prove2.me/submissions/ab9e7074-aefd-4e3c-893d-9657ba465f3e

import Mathlib
import Definitions.Def_ModPolicyIter_Conv_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace ModPolicyIter.Conv.P8e8

open ModPolicyIter.Conv

variable {S : Type*} [MeasurableSpace S] {ι : Type*}

lemma bm_integrable (m : Model S ι) (i : ι) (s : S) {v : S → ℝ} (hv : IsBM v) :
    Integrable v (m.P i s) := by
  have := m.isMarkov i
  obtain ⟨hm, C, hC⟩ := hv
  exact Integrable.of_bound hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun t => by simpa [Real.norm_eq_abs] using hC t))

lemma abs_pop_le (m : Model S ι) (i : ι) {v : S → ℝ} {C : ℝ} (hC : ∀ t, |v t| ≤ C) (s : S) :
    |Pop m i v s| ≤ C := by
  have := m.isMarkov i
  have h := norm_integral_le_of_norm_le_const (μ := m.P i s) (f := v) (C := C)
    (Filter.Eventually.of_forall (fun t => by simpa [Real.norm_eq_abs] using hC t))
  simpa [Pop, Real.norm_eq_abs] using h

lemma pop_le_const (m : Model S ι) (i : ι) {v : S → ℝ} (hv : IsBM v) {C : ℝ}
    (hC : ∀ t, v t ≤ C) (s : S) : Pop m i v s ≤ C := by
  have := m.isMarkov i
  have h : ∫ t, v t ∂(m.P i s) ≤ ∫ _t, C ∂(m.P i s) :=
    integral_mono (bm_integrable m i s hv) (integrable_const C) hC
  simpa [Pop] using h

lemma pop_mono (m : Model S ι) (i : ι) {v w : S → ℝ} (hv : IsBM v) (hw : IsBM w)
    (h : ∀ t, v t ≤ w t) (s : S) : Pop m i v s ≤ Pop m i w s :=
  integral_mono (bm_integrable m i s hv) (bm_integrable m i s hw) h

lemma bm_pop (m : Model S ι) (i : ι) {v : S → ℝ} (hv : IsBM v) : IsBM (Pop m i v) := by
  obtain ⟨hm, C, hC⟩ := hv
  refine ⟨?_, C, abs_pop_le m i hC⟩
  exact (hm.stronglyMeasurable.integral_kernel (κ := m.P i)).measurable

lemma pop_sub (m : Model S ι) (i : ι) {v w : S → ℝ} (hv : IsBM v) (hw : IsBM w) (s : S) :
    Pop m i (fun t => v t - w t) s = Pop m i v s - Pop m i w s :=
  integral_sub (bm_integrable m i s hv) (bm_integrable m i s hw)

lemma pop_add (m : Model S ι) (i : ι) {v w : S → ℝ} (hv : IsBM v) (hw : IsBM w) (s : S) :
    Pop m i (fun t => v t + w t) s = Pop m i v s + Pop m i w s :=
  integral_add (bm_integrable m i s hv) (bm_integrable m i s hw)

lemma pop_smul (m : Model S ι) (i : ι) (a : ℝ) (v : S → ℝ) (s : S) :
    Pop m i (fun t => a * v t) s = a * Pop m i v s :=
  integral_const_mul a _

lemma bm_add {v w : S → ℝ} (hv : IsBM v) (hw : IsBM w) : IsBM (fun t => v t + w t) := by
  obtain ⟨hv1, C, hC⟩ := hv
  obtain ⟨hw1, D, hD⟩ := hw
  refine ⟨hv1.add hw1, C + D, fun t => ?_⟩
  exact (abs_add_le _ _).trans (add_le_add (hC t) (hD t))

lemma bm_sub {v w : S → ℝ} (hv : IsBM v) (hw : IsBM w) : IsBM (fun t => v t - w t) := by
  obtain ⟨hv1, C, hC⟩ := hv
  obtain ⟨hw1, D, hD⟩ := hw
  refine ⟨hv1.sub hw1, C + D, fun t => ?_⟩
  exact (abs_sub _ _).trans (add_le_add (hC t) (hD t))

lemma bm_smul (a : ℝ) {v : S → ℝ} (hv : IsBM v) : IsBM (fun t => a * v t) := by
  obtain ⟨hv1, C, hC⟩ := hv
  refine ⟨hv1.const_mul a, |a| * C, fun t => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hC t) (abs_nonneg a)

lemma bm_c (m : Model S ι) (i : ι) : IsBM (m.c i) := ⟨m.c_meas i, m.M, m.c_bdd i⟩

lemma bm_iter (m : Model S ι) (i : ι) {g : S → ℝ} (hg : IsBM g) (j : ℕ) :
    IsBM ((Pop m i)^[j] g) := by
  induction j with
  | zero => simpa using hg
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact bm_pop m i ih

lemma apow_zero (m : Model S ι) (i : ι) (g : S → ℝ) (s : S) : Apow m i 0 g s = g s := by
  simp [Apow]

lemma apow_succ (m : Model S ι) (i : ι) {g : S → ℝ} (hg : IsBM g) (k : ℕ) (s : S) :
    Apow m i (k + 1) g s = g s + m.lam * Pop m i (Apow m i k g) s := by
  have := m.isMarkov i
  have hint : ∀ j ∈ Finset.range (k + 1),
      Integrable (fun t => m.lam ^ j * (Pop m i)^[j] g t) (m.P i s) := fun j _ =>
    (bm_integrable m i s (bm_iter m i hg j)).const_mul _
  have h1 : Pop m i (Apow m i k g) s =
      ∑ j ∈ Finset.range (k + 1), m.lam ^ j * (Pop m i)^[j + 1] g s := by
    simp only [Pop, Apow]
    rw [integral_finsetSum _ hint]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_const_mul, Function.iterate_succ_apply']
    rfl
  rw [h1, Finset.mul_sum]
  simp only [Apow]
  rw [Finset.sum_range_succ' _ (k + 1)]
  simp only [pow_zero, one_mul, Function.iterate_zero, id_eq, pow_succ]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

lemma bm_apow (m : Model S ι) (i : ι) {g : S → ℝ} (hg : IsBM g) (k : ℕ) :
    IsBM (Apow m i k g) := by
  induction k with
  | zero =>
    have : Apow m i 0 g = g := funext (apow_zero m i g)
    rw [this]; exact hg
  | succ k ih =>
    have : Apow m i (k + 1) g = fun s => g s + m.lam * Pop m i (Apow m i k g) s :=
      funext (apow_succ m i hg k)
    rw [this]
    exact bm_add hg (bm_smul _ (bm_pop m i ih))

lemma B_eq (m : Model S ι) {v : S → ℝ} {i : ι} (h : Attains m v i) (s : S) :
    B m v s = m.c i s + m.lam * Pop m i v s - v s := by
  have hb : BddAbove (Set.range fun j => m.c j s + m.lam * Pop m j v s) :=
    ⟨_, by rintro _ ⟨j, rfl⟩; exact h j s⟩
  haveI : Nonempty ι := ⟨i⟩
  have : (⨆ j, (m.c j s + m.lam * Pop m j v s)) = m.c i s + m.lam * Pop m i v s :=
    le_antisymm (ciSup_le (fun j => h j s)) (le_ciSup hb i)
  simp only [B, this]

lemma abs_le_supNorm {v : S → ℝ} (hv : IsBM v) (s : S) : |v s| ≤ supNorm v := by
  obtain ⟨_, C, hC⟩ := hv
  exact le_ciSup (f := fun s => |v s|) ⟨C, by rintro _ ⟨t, rfl⟩; exact hC t⟩ s

lemma supNorm_nonneg (v : S → ℝ) : 0 ≤ supNorm v :=
  Real.iSup_nonneg (fun s => abs_nonneg (v s))

lemma supNorm_le {v : S → ℝ} {C : ℝ} (h : ∀ s, |v s| ≤ C) (hC : 0 ≤ C) : supNorm v ≤ C :=
  Real.iSup_le h hC

lemma opNorm_bdd (m : Model S ι) (i j : ι) :
    BddAbove (Set.range fun x : {x : S → ℝ // IsBM x ∧ supNorm x ≤ 1} =>
      supNorm (Pop m i x.1 - Pop m j x.1)) := by
  refine ⟨2, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx : ∀ t, |x.1 t| ≤ 1 := fun t => (abs_le_supNorm x.2.1 t).trans x.2.2
  refine supNorm_le (fun s => ?_) (by norm_num)
  simp only [Pi.sub_apply]
  calc |Pop m i x.1 s - Pop m j x.1 s| ≤ |Pop m i x.1 s| + |Pop m j x.1 s| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add (abs_pop_le m i hx s) (abs_pop_le m j hx s)
    _ = 2 := by norm_num

lemma opNorm_nonneg (m : Model S ι) (i j : ι) : 0 ≤ opNormDiff m i j :=
  Real.iSup_nonneg (fun _ => supNorm_nonneg _)

lemma diff_le_opNorm (m : Model S ι) (i j : ι) {d : S → ℝ} (hd : IsBM d) (s : S) :
    |Pop m i d s - Pop m j d s| ≤ opNormDiff m i j * supNorm d := by
  rcases (supNorm_nonneg d).lt_or_eq with hpos | hzero
  · have hxbm : IsBM (fun t => (supNorm d)⁻¹ * d t) := bm_smul _ hd
    have hxn : supNorm (fun t => (supNorm d)⁻¹ * d t) ≤ 1 := by
      refine supNorm_le (fun t => ?_) (by norm_num)
      rw [abs_mul, abs_inv, abs_of_pos hpos, inv_mul_le_iff₀ hpos, mul_one]
      exact abs_le_supNorm hd t
    have h1 : |Pop m i (fun t => (supNorm d)⁻¹ * d t) s - Pop m j (fun t => (supNorm d)⁻¹ * d t) s|
        ≤ opNormDiff m i j := by
      have := abs_le_supNorm (bm_sub (bm_pop m i hxbm) (bm_pop m j hxbm)) s
      refine this.trans ?_
      exact le_ciSup (opNorm_bdd m i j) ⟨_, hxbm, hxn⟩
    rw [pop_smul, pop_smul, ← mul_sub, abs_mul, abs_inv, abs_of_pos hpos,
      inv_mul_le_iff₀ hpos] at h1
    linarith [h1]
  · have hd0 : ∀ t, d t = 0 := fun t => by
      have := abs_le_supNorm hd t
      rw [← hzero] at this
      exact abs_nonpos_iff.mp this
    have hd0' : d = fun _ => 0 := funext hd0
    rw [← hzero, mul_zero]
    simp [hd0', Pop]

/-- If `w ≤ L_P w` and `L_P v* ≤ v*` (with `w`, `v*` bounded measurable) then `w ≤ v*`. -/
lemma le_of_sub (m : Model S ι) (P : ι) {w vs : S → ℝ} (hw : IsBM w) (hvs : IsBM vs)
    (h1 : ∀ s, w s ≤ m.c P s + m.lam * Pop m P w s)
    (h2 : ∀ s, m.c P s + m.lam * Pop m P vs s ≤ vs s) (s : S) : w s ≤ vs s := by
  haveI : Nonempty S := ⟨s⟩
  have hd : IsBM (fun t => w t - vs t) := bm_sub hw hvs
  obtain ⟨_, C, hC⟩ := hd
  have hb : BddAbove (Set.range fun t => w t - vs t) :=
    ⟨C, by rintro _ ⟨t, rfl⟩; exact (le_abs_self _).trans (hC t)⟩
  have hle : ∀ t, w t - vs t ≤ ⨆ t, (w t - vs t) := fun t => le_ciSup hb t
  have key : ∀ t, w t - vs t ≤ m.lam * ⨆ t, (w t - vs t) := by
    intro t
    have e1 := h1 t
    have e2 := h2 t
    have e3 : Pop m P w t - Pop m P vs t ≤ ⨆ t, (w t - vs t) := by
      rw [← pop_sub m P hw hvs]
      exact pop_le_const m P (bm_sub hw hvs) hle t
    have := mul_le_mul_of_nonneg_left e3 m.lam_nonneg
    linarith
  have hM : (⨆ t, (w t - vs t)) ≤ m.lam * ⨆ t, (w t - vs t) := ciSup_le key
  have hM0 : (⨆ t, (w t - vs t)) ≤ 0 := by nlinarith [m.lam_lt_one]
  linarith [hle s]

/-- One policy-evaluation step `L_P w = c_P + λ P w`. -/
noncomputable def Lop (m : Model S ι) (i : ι) (w : S → ℝ) : S → ℝ :=
  fun s => m.c i s + m.lam * Pop m i w s

/-- The partial iterate `u + A^kk_P (B u)`. -/
noncomputable def Wseq (m : Model S ι) (u : S → ℝ) (P : ι) (kk : ℕ) : S → ℝ :=
  fun s => u s + Apow m P kk (B m u) s

lemma bm_Lop (m : Model S ι) (P : ι) {w : S → ℝ} (hw : IsBM w) : IsBM (Lop m P w) :=
  bm_add (bm_c m P) (bm_smul _ (bm_pop m P hw))

lemma Lop_mono (m : Model S ι) (P : ι) {w w' : S → ℝ} (hw : IsBM w) (hw' : IsBM w')
    (h : ∀ s, w s ≤ w' s) (s : S) : Lop m P w s ≤ Lop m P w' s := by
  have := mul_le_mul_of_nonneg_left (pop_mono m P hw hw' h s) m.lam_nonneg
  simp only [Lop]
  linarith

lemma B_fun (m : Model S ι) {u : S → ℝ} {P : ι} (hP : Attains m u P) :
    B m u = fun s => Lop m P u s - u s := funext (fun s => by rw [B_eq m hP s]; rfl)

lemma bm_B (m : Model S ι) {u : S → ℝ} (hu : IsBM u) {P : ι} (hP : Attains m u P) :
    IsBM (B m u) := by
  rw [B_fun m hP]
  exact bm_sub (bm_Lop m P hu) hu

lemma Wseq_zero (m : Model S ι) {u : S → ℝ} {P : ι} (hP : Attains m u P) :
    Wseq m u P 0 = Lop m P u := by
  funext s
  simp only [Wseq]
  rw [apow_zero, B_fun m hP]
  ring

lemma Wseq_succ (m : Model S ι) {u : S → ℝ} (hu : IsBM u) {P : ι} (hP : Attains m u P)
    (kk : ℕ) : Wseq m u P (kk + 1) = Lop m P (Wseq m u P kk) := by
  funext s
  have hg := bm_B m hu hP
  have hW : Wseq m u P kk = fun t => u t + Apow m P kk (B m u) t := rfl
  simp only [Lop]
  rw [hW, pop_add m P hu (bm_apow m P hg kk) s]
  simp only [Wseq]
  rw [apow_succ m P hg kk s, B_eq m hP s]
  ring

lemma Wseq_props (m : Model S ι) {u : S → ℝ} (hu : IsBM u) {P : ι} (hP : Attains m u P)
    (hBu : ∀ s, 0 ≤ B m u s) (kk : ℕ) :
    IsBM (Wseq m u P kk) ∧ (∀ s, Wseq m u P kk s ≤ Lop m P (Wseq m u P kk) s) ∧
      (∀ s, Lop m P u s ≤ Wseq m u P kk s) := by
  induction kk with
  | zero =>
    rw [Wseq_zero m hP]
    have hu_le : ∀ s, u s ≤ Lop m P u s := fun s => by
      have := hBu s; rw [B_fun m hP] at this; simp only at this; linarith
    exact ⟨bm_Lop m P hu, Lop_mono m P hu (bm_Lop m P hu) hu_le, fun s => le_rfl⟩
  | succ kk ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    rw [Wseq_succ m hu hP kk]
    exact ⟨bm_Lop m P ih1, Lop_mono m P ih1 (bm_Lop m P ih1) ih2,
      fun s => (ih3 s).trans (ih2 s)⟩

end ModPolicyIter.Conv.P8e8

open ModPolicyIter.Conv.P8e8 in
open MeasureTheory ProbabilityTheory in
open ModPolicyIter.Conv in
theorem solution {S : Type*} [MeasurableSpace S] {ι : Type*} (m : Model S ι)
    (hmax : MaxAttained m) (k : ℕ) (v : ℕ → S → ℝ) (pol : ℕ → ι)
    (hrun : IsRun m k v pol) (hv0 : IsBM (v 0)) (hB0 : ∀ s, 0 ≤ B m (v 0) s)
    (vstar : S → ℝ) (hvstar : IsBM vstar) (hBstar : ∀ s, B m vstar s = 0)
    (Pstar : ι) (hPstar : Attains m vstar Pstar) :
    ∀ n, supNorm (vstar - v (n + 1)) ≤
      min m.lam (m.lam * (1 - m.lam ^ k) / (1 - m.lam) * opNormDiff m (pol n) Pstar
        + m.lam ^ (k + 1)) * supNorm (v n - vstar) := by
  have hlam0 := m.lam_nonneg
  have hlam1 := m.lam_lt_one
  -- v* is a fixed point of L_{P*} and dominates every L_j v*
  have hvfix : ∀ s, Lop m Pstar vstar s = vstar s := by
    intro s
    have := B_eq m hPstar s
    rw [hBstar s] at this
    simp only [Lop]; linarith
  have hvdom : ∀ j s, Lop m j vstar s ≤ vstar s := fun j s => (hPstar j s).trans (hvfix s).le
  have hvn_eq : ∀ n, v (n + 1) = Wseq m (v n) (pol n) k := by
    intro n
    rw [(hrun n).2]; rfl
  -- Theorem 1: every iterate is BM with Bv_n ≥ 0
  have thm1 : ∀ n, IsBM (v n) ∧ ∀ s, 0 ≤ B m (v n) s := by
    intro n
    induction n with
    | zero => exact ⟨hv0, hB0⟩
    | succ n ih =>
      obtain ⟨ih1, ih2⟩ := ih
      obtain ⟨h1, h2, _⟩ := Wseq_props m ih1 (hrun n).1 ih2 k
      rw [← hvn_eq n] at h1 h2
      refine ⟨h1, fun s => ?_⟩
      rw [B_eq m (hrun (n + 1)).1 s]
      have e1 := (hrun (n + 1)).1 (pol n) s
      have e2 := h2 s
      simp only [Lop] at e2
      linarith
  intro n
  obtain ⟨hu, hBu⟩ := thm1 n
  have hPatt : Attains m (v n) (pol n) := (hrun n).1
  have hD0 : 0 ≤ supNorm (v n - vstar) := supNorm_nonneg _
  have hdbm : IsBM (fun t => vstar t - v n t) := bm_sub hvstar hu
  have hdD : ∀ t, |vstar t - v n t| ≤ supNorm (v n - vstar) := by
    intro t
    have := abs_le_supNorm (bm_sub hu hvstar) t
    rw [abs_sub_comm]
    exact this
  have hdD' : ∀ t, vstar t - v n t ≤ supNorm (v n - vstar) :=
    fun t => (le_abs_self _).trans (hdD t)
  have hopN0 : 0 ≤ opNormDiff m (pol n) Pstar := opNorm_nonneg m (pol n) Pstar
  -- v* - L_P u ≤ λ D
  have hC1 : ∀ s, vstar s - Lop m (pol n) (v n) s ≤ m.lam * supNorm (v n - vstar) := by
    intro s
    have h1 := hPatt Pstar s
    have h2 := hvfix s
    simp only [Lop] at h2 ⊢
    have h3 : Pop m Pstar vstar s - Pop m Pstar (v n) s ≤ supNorm (v n - vstar) := by
      rw [← pop_sub m Pstar hvstar hu]
      exact pop_le_const m Pstar hdbm hdD' s
    have := mul_le_mul_of_nonneg_left h3 hlam0
    linarith
  have hC2 : ∀ kk : ℕ, ∀ s, vstar s - Wseq m (v n) (pol n) kk s ≤
      (m.lam * (1 - m.lam ^ kk) / (1 - m.lam) * opNormDiff m (pol n) Pstar + m.lam ^ (kk + 1))
        * supNorm (v n - vstar) := by
    intro kk
    induction kk with
    | zero =>
      intro s
      rw [Wseq_zero m hPatt]
      simpa using hC1 s
    | succ kk ih =>
      intro s
      obtain ⟨hWbm, _, _⟩ := Wseq_props m hu hPatt hBu kk
      rw [Wseq_succ m hu hPatt kk]
      have h1 := hPatt Pstar s
      have h2 := hvfix s
      simp only [Lop] at h1 h2 ⊢
      have hdiff : Pop m Pstar (fun t => vstar t - v n t) s
          - Pop m (pol n) (fun t => vstar t - v n t) s
          ≤ opNormDiff m (pol n) Pstar * supNorm (v n - vstar) := by
        have := diff_le_opNorm m (pol n) Pstar hdbm s
        have hsn : supNorm (fun t => vstar t - v n t) ≤ supNorm (v n - vstar) :=
          supNorm_le hdD hD0
        have h4 := mul_le_mul_of_nonneg_left hsn hopN0
        have h5 := neg_abs_le (Pop m (pol n) (fun t => vstar t - v n t) s -
          Pop m Pstar (fun t => vstar t - v n t) s)
        linarith
      rw [pop_sub m Pstar hvstar hu, pop_sub m (pol n) hvstar hu] at hdiff
      have hT : Pop m (pol n) vstar s - Pop m (pol n) (Wseq m (v n) (pol n) kk) s ≤
          (m.lam * (1 - m.lam ^ kk) / (1 - m.lam) * opNormDiff m (pol n) Pstar
            + m.lam ^ (kk + 1)) * supNorm (v n - vstar) := by
        rw [← pop_sub m (pol n) hvstar hWbm]
        exact pop_le_const m (pol n) (bm_sub hvstar hWbm) ih s
      have e1 := mul_le_mul_of_nonneg_left hdiff hlam0
      have e2 := mul_le_mul_of_nonneg_left hT hlam0
      have hne : (1 - m.lam) ≠ 0 := by linarith
      have hid : (m.lam * (1 - m.lam ^ (kk + 1)) / (1 - m.lam) * opNormDiff m (pol n) Pstar
            + m.lam ^ (kk + 1 + 1)) * supNorm (v n - vstar)
          = m.lam * (opNormDiff m (pol n) Pstar * supNorm (v n - vstar)) +
            m.lam * ((m.lam * (1 - m.lam ^ kk) / (1 - m.lam) * opNormDiff m (pol n) Pstar
              + m.lam ^ (kk + 1)) * supNorm (v n - vstar)) := by
        field_simp
        ring
      rw [hid]
      linarith
  -- assemble
  obtain ⟨hWbm, hWle, hWge⟩ := Wseq_props m hu hPatt hBu k
  have hnonneg : ∀ s, 0 ≤ vstar s - Wseq m (v n) (pol n) k s := by
    intro s
    have := le_of_sub m (pol n) hWbm hvstar hWle (hvdom (pol n)) s
    linarith
  rw [hvn_eq n]
  have hX0 : 0 ≤ m.lam * (1 - m.lam ^ k) / (1 - m.lam) * opNormDiff m (pol n) Pstar
      + m.lam ^ (k + 1) := by
    have : m.lam ^ k ≤ 1 := pow_le_one₀ hlam0 hlam1.le
    have h1l : 0 < 1 - m.lam := by linarith
    have h2l : 0 ≤ 1 - m.lam ^ k := by linarith
    have : 0 ≤ m.lam * (1 - m.lam ^ k) / (1 - m.lam) * opNormDiff m (pol n) Pstar :=
      mul_nonneg (div_nonneg (mul_nonneg hlam0 h2l) h1l.le) hopN0
    have : 0 ≤ m.lam ^ (k + 1) := pow_nonneg hlam0 _
    linarith
  refine supNorm_le (fun s => ?_) (mul_nonneg (le_min hlam0 hX0) hD0)
  simp only [Pi.sub_apply]
  rw [abs_of_nonneg (hnonneg s), min_mul_of_nonneg _ _ hD0]
  refine le_min ?_ (hC2 k s)
  have := hC1 s
  have := hWge s
  linarith
