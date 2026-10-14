-- Prove2me | solution 1 for OAI.AlternatingNS.energy_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T02:30:53.838018+00:00
-- url     : https://prove2.me/submissions/f4ef0b4c-3a16-4f8f-bc83-ad4dc60deadd

import Mathlib
import Definitions.Def_NavierStokesAlternating
set_option autoImplicit false
open scoped BigOperators ENNReal Topology ContDiff
open MeasureTheory OAI OAI.AlternatingNS

namespace AN_E

lemma hasLineDerivAt_clm {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) {f : E → F} {f' : F} {x v : E} (h : HasLineDerivAt ℝ f f' x v) :
    HasLineDerivAt ℝ (fun y => L (f y)) (L f') x v :=
  L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

lemma hasLineDerivAt_sub {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {f' g' : F} {x v : E} (hf : HasLineDerivAt ℝ f f' x v)
    (hg : HasLineDerivAt ℝ g g' x v) :
    HasLineDerivAt ℝ (fun y => f y - g y) (f' - g') x v :=
  HasDerivAt.sub hf hg

lemma hasLineDerivAt_norm_sq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : E → F} {f' : F} {x v : E} (hf : HasLineDerivAt ℝ f f' x v) :
    HasLineDerivAt ℝ (fun y => ‖f y‖ ^ 2) (2 * inner ℝ (f x) f') x v := by
  have := HasDerivAt.norm_sq hf
  simpa [HasLineDerivAt] using this

lemma coord_apply (x : Space) (j : Fin 3) : (EuclideanSpace.proj j : Space →L[ℝ] ℝ) x = x j := rfl

lemma hasLineDerivAt_coord {f : Space → Space} {f' : Space} {x v : Space} (j : Fin 3)
    (h : HasLineDerivAt ℝ f f' x v) : HasLineDerivAt ℝ (fun y => f y j) (f' j) x v :=
  hasLineDerivAt_clm (EuclideanSpace.proj j : Space →L[ℝ] ℝ) h

lemma aesm_coord {f : Space → Space} (hf : AEStronglyMeasurable f volume) (j : Fin 3) :
    AEStronglyMeasurable (fun x => f x j) volume :=
  (EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hf

/-- transport term -/
lemma ibp_transport (a w wj : Space → Space) (a1 : Space → Space) (j : Fin 3)
    (ha : ∀ x, HasLineDerivAt ℝ a (a1 x) x (e j)) (hw : ∀ x, HasLineDerivAt ℝ w (wj x) x (e j))
    (h1 : Integrable (fun x => a1 x j * ‖w x‖ ^ 2) volume)
    (h2 : Integrable (fun x => a x j * inner ℝ (w x) (wj x)) volume)
    (h3 : Integrable (fun x => a x j * ‖w x‖ ^ 2) volume) :
    ∫ x, a x j * inner ℝ (w x) (wj x) = -(1/2) * ∫ x, a1 x j * ‖w x‖ ^ 2 := by
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure Space)) (B := ContinuousLinearMap.mul ℝ ℝ)
    (f := fun x => a x j) (f' := fun x => a1 x j) (g := fun x => ‖w x‖ ^ 2)
    (g' := fun x => 2 * inner ℝ (w x) (wj x)) (v := e j)
    (by simpa using h1) ((h2.const_mul 2).congr (Filter.Eventually.of_forall fun x => by simp only [ContinuousLinearMap.mul_apply']; ring)) (by simpa using h3)
    (fun x _ => hasLineDerivAt_coord j (ha x)) (fun x _ => hasLineDerivAt_norm_sq (hw x))
  simp only [ContinuousLinearMap.mul_apply'] at key
  have e2 : ∫ x, a x j * (2 * inner ℝ (w x) (wj x)) = 2 * ∫ x, a x j * inner ℝ (w x) (wj x) := by
    rw [← integral_const_mul]; congr 1; ext x; ring
  rw [e2] at key
  linarith

/-- pressure term -/
lemma ibp_pressure (P P1 : Space → ℝ) (w wj : Space → Space) (j : Fin 3)
    (hP : ∀ x, HasLineDerivAt ℝ P (P1 x) x (e j)) (hw : ∀ x, HasLineDerivAt ℝ w (wj x) x (e j))
    (h1 : Integrable (fun x => w x j * P1 x) volume)
    (h2 : Integrable (fun x => wj x j * P x) volume)
    (h3 : Integrable (fun x => w x j * P x) volume) :
    ∫ x, w x j * P1 x = -∫ x, wj x j * P x := by
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure Space)) (B := ContinuousLinearMap.mul ℝ ℝ)
    (f := P) (f' := P1) (g := fun x => w x j)
    (g' := fun x => wj x j) (v := e j)
    (by simpa [mul_comm] using h1) (by simpa [mul_comm] using h2) (by simpa [mul_comm] using h3)
    (fun x _ => hP x) (fun x _ => hasLineDerivAt_coord j (hw x))
  simp only [ContinuousLinearMap.mul_apply'] at key
  simp only [mul_comm (P1 _), mul_comm (P _)] at key
  linarith

/-- viscous term -/
lemma ibp_viscous (w wj wjj : Space → Space) (j : Fin 3)
    (hw : ∀ x, HasLineDerivAt ℝ w (wj x) x (e j)) (hwj : ∀ x, HasLineDerivAt ℝ wj (wjj x) x (e j))
    (h1 : Integrable (fun x => inner ℝ (wj x) (wj x)) volume)
    (h2 : Integrable (fun x => inner ℝ (w x) (wjj x)) volume)
    (h3 : Integrable (fun x => inner ℝ (w x) (wj x)) volume) :
    ∫ x, inner ℝ (w x) (wjj x) ≤ 0 := by
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure Space)) (B := innerSL ℝ (E := Space))
    (f := w) (f' := wj) (g := wj) (g' := wjj) (v := e j)
    h1 h2 h3
    (fun x _ => hw x) (fun x _ => hwj x)
  change ∫ x, inner ℝ (w x) (wjj x) = -∫ x, inner ℝ (wj x) (wj x) at key
  rw [key, neg_nonpos]
  exact integral_nonneg fun x => real_inner_self_nonneg

lemma clm_expand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Space →L[ℝ] E) (y : Space) : L y = ∑ i, y i • L (e i) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr y]
  simp [map_sum, map_smul, e]

lemma inner_eq_sum (x y : Space) : inner ℝ x y = ∑ i, x i * y i := by
  simp [PiLp.inner_apply, mul_comm]

lemma inner_grad (x : Space) (q : Fin 3 → ℝ) :
    inner ℝ x ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) = ∑ i, x i * q i := by
  rw [inner_eq_sum]; rfl

lemma integrable_of_le_mul {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
    [NormedAddCommGroup F] {f : Space → E₁} {g : Space → E₂} {h : Space → F} (c : ℝ)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (hh : AEStronglyMeasurable h volume)
    (hb : ∀ x, ‖h x‖ ≤ c * (‖f x‖ * ‖g x‖)) : Integrable h volume := by
  have h1 : Integrable (fun x => ‖f x‖ * ‖g x‖) volume := by
    have := hf.norm.integrable_mul (q := 2) hg.norm
    simpa [Pi.mul_def] using this
  exact (h1.const_mul c).mono' hh (Filter.Eventually.of_forall hb)

lemma norm_coord_le (x : Space) (i : Fin 3) : ‖x i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i

lemma energy_core (ν : ℝ) (hν : 0 ≤ ν) (a w : Space → Space) (a1 wj wjj : Fin 3 → Space → Space)
    (P : Space → ℝ) (P1 : Fin 3 → Space → ℝ) (Db : Space → Space →L[ℝ] Space)
    (ha : ∀ j x, HasLineDerivAt ℝ a (a1 j x) x (e j))
    (hw : ∀ j x, HasLineDerivAt ℝ w (wj j x) x (e j))
    (hwj : ∀ j x, HasLineDerivAt ℝ (wj j) (wjj j x) x (e j))
    (hP : ∀ j x, HasLineDerivAt ℝ P (P1 j x) x (e j))
    (hdiva : ∀ x, ∑ j, a1 j x j = 0) (hdivw : ∀ x, ∑ j, wj j x j = 0)
    (Ca Cw Cb : ℝ) (hCa : ∀ x, ‖a x‖ ≤ Ca) (hCw : ∀ x, ‖w x‖ ≤ Cw) (hCb : ∀ x, ‖Db x‖ ≤ Cb)
    (hMa : AEStronglyMeasurable a volume) (hMDb : AEStronglyMeasurable Db volume)
    (hLw : MemLp w 2 volume) (hLa1 : ∀ j, MemLp (a1 j) 2 volume)
    (hLwj : ∀ j, MemLp (wj j) 2 volume) (hLwjj : ∀ j, MemLp (wjj j) 2 volume)
    (hLP : MemLp P 2 volume) (hLP1 : ∀ j, MemLp (P1 j) 2 volume) :
    ∫ x, (-(∑ j, a x j * inner ℝ (w x) (wj j x)) - inner ℝ (w x) (Db x (w x))
        - ∑ j, w x j * P1 j x + ν * ∑ j, inner ℝ (w x) (wjj j x))
      ≤ Cb * ∫ x, ‖w x‖ ^ 2 := by
  have hCa0 : 0 ≤ Ca := (norm_nonneg _).trans (hCa 0)
  have hCw0 : 0 ≤ Cw := (norm_nonneg _).trans (hCw 0)
  have hCb0 : 0 ≤ Cb := (norm_nonneg _).trans (hCb 0)
  have mw := hLw.aestronglyMeasurable
  have mwj := fun j => (hLwj j).aestronglyMeasurable
  have mwjj := fun j => (hLwjj j).aestronglyMeasurable
  have ma1 := fun j => (hLa1 j).aestronglyMeasurable
  have mP := hLP.aestronglyMeasurable
  have mP1 := fun j => (hLP1 j).aestronglyMeasurable
  -- integrability
  have iT1 : ∀ j, Integrable (fun x => a x j * inner ℝ (w x) (wj j x)) volume := fun j =>
    integrable_of_le_mul Ca hLw (hLwj j) ((aesm_coord hMa j).mul (mw.inner (mwj j))) fun x => by
      rw [norm_mul]
      exact mul_le_mul ((norm_coord_le _ _).trans (hCa x)) (norm_inner_le_norm _ _)
        (norm_nonneg _) hCa0
  have iT1a : ∀ j, Integrable (fun x => a1 j x j * ‖w x‖ ^ 2) volume := fun j =>
    integrable_of_le_mul Cw (hLa1 j) hLw ((aesm_coord (ma1 j) j).mul (mw.norm.pow 2)) fun x => by
      rw [norm_mul, norm_pow, norm_norm, sq]
      have h1 := norm_coord_le (a1 j x) j
      have h2 := hCw x
      have h3 := norm_nonneg (w x)
      have h4 := norm_nonneg (a1 j x j)
      nlinarith [mul_le_mul h1 h2 h3 (norm_nonneg _)]
  have iT1b : ∀ j, Integrable (fun x => a x j * ‖w x‖ ^ 2) volume := fun j =>
    integrable_of_le_mul Ca hLw hLw ((aesm_coord hMa j).mul (mw.norm.pow 2)) fun x => by
      rw [norm_mul, norm_pow, norm_norm, sq]
      have h1 := (norm_coord_le (a x) j).trans (hCa x)
      nlinarith [mul_nonneg (norm_nonneg (w x)) (norm_nonneg (w x))]
  have mT2 : AEStronglyMeasurable (fun x => inner ℝ (w x) (Db x (w x))) volume :=
    mw.inner ((ContinuousLinearMap.apply ℝ Space).aestronglyMeasurable_comp₂ mw hMDb)
  have bT2 : ∀ x, ‖inner ℝ (w x) (Db x (w x))‖ ≤ Cb * (‖w x‖ * ‖w x‖) := fun x => by
    refine (norm_inner_le_norm _ _).trans ?_
    have := (Db x).le_opNorm (w x)
    have h2 : ‖Db x‖ * ‖w x‖ ≤ Cb * ‖w x‖ := mul_le_mul_of_nonneg_right (hCb x) (norm_nonneg _)
    nlinarith [norm_nonneg (w x)]
  have iT2 : Integrable (fun x => inner ℝ (w x) (Db x (w x))) volume :=
    integrable_of_le_mul Cb hLw hLw mT2 bT2
  have iT3 : ∀ j, Integrable (fun x => w x j * P1 j x) volume := fun j =>
    integrable_of_le_mul 1 hLw (hLP1 j) ((aesm_coord mw j).mul (mP1 j)) fun x => by
      rw [norm_mul, one_mul]
      exact mul_le_mul_of_nonneg_right (norm_coord_le _ _) (norm_nonneg _)
  have iT3a : ∀ j, Integrable (fun x => wj j x j * P x) volume := fun j =>
    integrable_of_le_mul 1 (hLwj j) hLP ((aesm_coord (mwj j) j).mul mP) fun x => by
      rw [norm_mul, one_mul]
      exact mul_le_mul_of_nonneg_right (norm_coord_le _ _) (norm_nonneg _)
  have iT3b : ∀ j, Integrable (fun x => w x j * P x) volume := fun j =>
    integrable_of_le_mul 1 hLw hLP ((aesm_coord mw j).mul mP) fun x => by
      rw [norm_mul, one_mul]
      exact mul_le_mul_of_nonneg_right (norm_coord_le _ _) (norm_nonneg _)
  have iT4 : ∀ j, Integrable (fun x => inner ℝ (w x) (wjj j x)) volume := fun j =>
    integrable_of_le_mul 1 hLw (hLwjj j) (mw.inner (mwjj j)) fun x => by
      rw [one_mul]; exact norm_inner_le_norm _ _
  have iT4a : ∀ j, Integrable (fun x => inner ℝ (wj j x) (wj j x)) volume := fun j =>
    integrable_of_le_mul 1 (hLwj j) (hLwj j) ((mwj j).inner (mwj j)) fun x => by
      rw [one_mul]; exact norm_inner_le_norm _ _
  have iT4b : ∀ j, Integrable (fun x => inner ℝ (w x) (wj j x)) volume := fun j =>
    integrable_of_le_mul 1 hLw (hLwj j) (mw.inner (mwj j)) fun x => by
      rw [one_mul]; exact norm_inner_le_norm _ _
  have iW : Integrable (fun x => ‖w x‖ ^ 2) volume :=
    integrable_of_le_mul 1 hLw hLw (mw.norm.pow 2) fun x => by
      rw [norm_pow, norm_norm, one_mul, sq]
  -- the three integrated identities
  have hS1 : ∫ x, ∑ j, a x j * inner ℝ (w x) (wj j x) = 0 := by
    rw [integral_finsetSum _ (fun j _ => iT1 j)]
    calc ∑ j, ∫ x, a x j * inner ℝ (w x) (wj j x)
        = ∑ j, (-(1/2) * ∫ x, a1 j x j * ‖w x‖ ^ 2) :=
          Finset.sum_congr rfl fun j _ =>
            ibp_transport a w (wj j) (a1 j) j (ha j) (hw j) (iT1a j) (iT1 j) (iT1b j)
      _ = -(1/2) * ∫ x, ∑ j, a1 j x j * ‖w x‖ ^ 2 := by
          rw [integral_finsetSum _ (fun j _ => iT1a j), Finset.mul_sum]
      _ = 0 := by simp_rw [← Finset.sum_mul, hdiva]; simp
  have hS3 : ∫ x, ∑ j, w x j * P1 j x = 0 := by
    rw [integral_finsetSum _ (fun j _ => iT3 j)]
    calc ∑ j, ∫ x, w x j * P1 j x
        = ∑ j, (-∫ x, wj j x j * P x) :=
          Finset.sum_congr rfl fun j _ =>
            ibp_pressure P (P1 j) w (wj j) j (hP j) (hw j) (iT3 j) (iT3a j) (iT3b j)
      _ = -∫ x, ∑ j, wj j x j * P x := by
          rw [integral_finsetSum _ (fun j _ => iT3a j), Finset.sum_neg_distrib]
      _ = 0 := by simp_rw [← Finset.sum_mul, hdivw]; simp
  have hS4 : ∫ x, ν * ∑ j, inner ℝ (w x) (wjj j x) ≤ 0 := by
    rw [integral_const_mul, integral_finsetSum _ (fun j _ => iT4 j)]
    exact mul_nonpos_of_nonneg_of_nonpos hν (Finset.sum_nonpos fun j _ =>
      ibp_viscous w (wj j) (wjj j) j (hw j) (hwj j) (iT4a j) (iT4 j) (iT4b j))
  have hT2 : -∫ x, inner ℝ (w x) (Db x (w x)) ≤ Cb * ∫ x, ‖w x‖ ^ 2 := by
    rw [← integral_neg, ← integral_const_mul]
    refine integral_mono iT2.neg (iW.const_mul Cb) fun x => ?_
    have := bT2 x
    have h2 := neg_le_abs (inner ℝ (w x) (Db x (w x)))
    simp only [Real.norm_eq_abs] at this
    simp only [sq]; linarith
  have iS1 : Integrable (fun x => ∑ j, a x j * inner ℝ (w x) (wj j x)) volume :=
    integrable_finsetSum _ fun j _ => iT1 j
  have iS3 : Integrable (fun x => ∑ j, w x j * P1 j x) volume :=
    integrable_finsetSum _ fun j _ => iT3 j
  have iS4 : Integrable (fun x => ν * ∑ j, inner ℝ (w x) (wjj j x)) volume :=
    (integrable_finsetSum _ fun j _ => iT4 j).const_mul ν
  have i12 : Integrable (fun x => -(∑ j, a x j * inner ℝ (w x) (wj j x))
      - inner ℝ (w x) (Db x (w x))) volume := iS1.neg.sub iT2
  have i123 : Integrable (fun x => -(∑ j, a x j * inner ℝ (w x) (wj j x))
      - inner ℝ (w x) (Db x (w x)) - ∑ j, w x j * P1 j x) volume := i12.sub iS3
  have i1 : Integrable (fun x => -(∑ j, a x j * inner ℝ (w x) (wj j x))) volume := iS1.neg
  rw [integral_add i123 iS4, integral_sub i12 iS3, integral_sub i1 iT2, integral_neg, hS1, hS3]
  linarith


lemma pointwise_identity (ν : ℝ) (A B : Space →L[ℝ] Space) (a b : Space) (gp : Fin 3 → ℝ)
    (A2 B2 : Fin 3 → Space) :
    inner ℝ (a - b) (-(A a - B b) - (EuclideanSpace.equiv (Fin 3) ℝ).symm gp
        + ν • (∑ j, A2 j - ∑ j, B2 j))
      = -(∑ j, a j * inner ℝ (a - b) (A (e j) - B (e j))) - inner ℝ (a - b) (B (a - b))
        - ∑ j, (a - b) j * gp j + ν * ∑ j, inner ℝ (a - b) (A2 j - B2 j) := by
  have hA : A a - B b = ∑ j, a j • (A (e j) - B (e j)) + B (a - b) := by
    rw [clm_expand A a, map_sub, clm_expand B a]
    simp only [smul_sub, Finset.sum_sub_distrib]
    abel
  rw [hA, inner_add_right, inner_sub_right, inner_neg_right, inner_add_right, inner_sum,
    inner_grad, inner_smul_right, ← Finset.sum_sub_distrib, inner_sum]
  simp only [inner_smul_right]
  ring

lemma spatial_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ → Space → E) :
    spatial 0 F = F := rfl

lemma spatial_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ → Space → E)
    (j : Fin 3) : spatial (Pi.single j 1) F = dx j F := by
  fin_cases j <;> rfl

lemma spatial_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ → Space → E)
    (j : Fin 3) : spatial (Pi.single j 2) F = dx j (dx j F) := by
  fin_cases j <;> rfl

lemma memLp_of_H {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} {F : ℝ → Space → E}
    {T : ℝ} (h : ContinuousInH k F T) (α : MultiIndex) (hα : ∑ i, α i ≤ k) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) : MemLp (spatial α F t) 2 volume := by
  obtain ⟨g, -, hg⟩ := h α hα
  exact (Lp.memLp (g t)).ae_eq (hg t ht)

lemma memLp_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} {F : ℝ → Space → E}
    {T : ℝ} (h : ContinuousInH k F T) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    MemLp (F t) 2 volume := by
  simpa [spatial_zero] using memLp_of_H h 0 (by simp) ht

lemma memLp_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} {F : ℝ → Space → E}
    {T : ℝ} (h : ContinuousInH k F T) (hk : 1 ≤ k) (j : Fin 3) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) : MemLp (dx j F t) 2 volume := by
  have := memLp_of_H h (Pi.single j 1) (by simpa using hk) ht
  rwa [spatial_one] at this

lemma memLp_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ → Space → E}
    {T : ℝ} (h : ContinuousInH 2 F T) (j : Fin 3) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) : MemLp (dx j (dx j F) t) 2 volume := by
  have := memLp_of_H h (Pi.single j 2) (by simp) ht
  rwa [spatial_two] at this

lemma gronwall_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : ℝ) (G G' : ℝ → E)
    (hG : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt G (G' t) (Set.Icc 0 T) t) (h0 : G 0 = 0) (C : ℝ)
    (hb : ∀ t ∈ Set.Icc 0 T, inner ℝ (G t) (G' t) ≤ C * ‖G t‖ ^ 2) :
    ∀ t ∈ Set.Icc 0 T, G t = 0 := by
  have hφ : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt (fun s => ‖G s‖ ^ 2) (2 * inner ℝ (G t) (G' t)) (Set.Icc 0 T) t :=
    fun t ht => (hG t ht).norm_sq
  have hcont : ContinuousOn (fun s => ‖G s‖ ^ 2) (Set.Icc 0 T) :=
    fun t ht => (hφ t ht).continuousWithinAt
  have key := le_gronwallBound_of_liminf_deriv_right_le (f := fun s => ‖G s‖ ^ 2)
    (f' := fun t => 2 * inner ℝ (G t) (G' t)) (δ := 0) (K := 2 * C) (ε := 0) hcont
    (fun x hx r hr => by
      have hmem : Set.Icc 0 T ∈ 𝓝[Set.Ici x] x :=
        Filter.mem_of_superset (Icc_mem_nhdsGE hx.2) (Set.Icc_subset_Icc hx.1 le_rfl)
      exact ((hφ x (Set.Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin hmem).liminf_right_slope_le hr)
    (by simp [h0])
    (fun x hx => by have := hb x (Set.Ico_subset_Icc_self hx); linarith)
  intro t ht
  have h1 := key t ht
  rw [gronwallBound_ε0_δ0] at h1
  have h2 : ‖G t‖ ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
  simpa using h2

lemma L2_inner_eq (F F' : Lp Space 2 (volume : Measure Space)) (f f' : Space → Space)
    (hF : (F : Space → Space) =ᵐ[volume] f) (hF' : (F' : Space → Space) =ᵐ[volume] f') :
    inner ℝ F F' = ∫ x, inner ℝ (f x) (f' x) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hF, hF'] with x h1 h2
  rw [h1, h2]

lemma L2_norm_sq_eq (F : Lp Space 2 (volume : Measure Space)) (f : Space → Space)
    (hF : (F : Space → Space) =ᵐ[volume] f) :
    ‖F‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2_inner_eq F F f f hF hF]
  simp_rw [real_inner_self_eq_norm_sq]


end AN_E

open AN_E in
theorem solution (ν : ℝ) (hν : 0 < ν) (U : Velocity) (K : Set Space) (hK : IsCompact K)
    (hU : Smooth U) (hs : SupportedIn U K) (hr : Rapid U)
    (hNS : NavierStokes ν (residual ν U) U (fun _ _ => 0)) (hE : EnergyClass U (fun _ _ => 0))
    (v : Velocity) (p : Pressure) (hv : NavierStokes ν (residual ν U) v p)
    (hc : CompetitorEnergyClass v p) :
    ∀ t, 0 ≤ t → ∀ x, v t x = U t x ∧ p t x = 0 := by
  obtain ⟨⟨-, hv_diff, hv_diff2, hp_diff, -⟩, hv0, hv_eq⟩ := hv
  obtain ⟨⟨-, hU_diff, hU_diff2, -, -⟩, hU0, hU_eq⟩ := hNS
  have grad0 : ∀ t x, grad (fun _ _ => (0:ℝ)) t x = 0 := by
    intro t x
    ext i
    simp [grad, dx]
  have hdt : ∀ t, 0 ≤ t → ∀ x, dt v t x - dt U t x =
      -(advection v t x - advection U t x) - grad p t x
        + ν • (laplacian v t x - laplacian U t x) := by
    intro t ht x
    have h1 := eq_sub_of_add_eq (hv_eq t ht x).2
    have h2 := eq_sub_of_add_eq (hU_eq t ht x).2
    rw [h1, h2, grad0, smul_sub]
    abel
  -- Step 1 : velocity uniqueness on every [0, T]
  have hvU : ∀ T, 0 ≤ T → ∀ t ∈ Set.Icc 0 T, v t = U t := by
    intro T hT
    obtain ⟨hvH2, hvC1, hpH1, Cv, hCv⟩ := hc T hT
    obtain ⟨hUH2, hUC1, -, -⟩ := hE.1 T hT
    obtain ⟨CU, hCU⟩ := hE.2 T hT
    have henergy : ∀ t ∈ Set.Icc 0 T,
        ∫ x, inner ℝ (v t x - U t x) (dt v t x - dt U t x)
          ≤ CU * ∫ x, ‖v t x - U t x‖ ^ 2 := by
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      have hpt : ∀ x, inner ℝ (v t x - U t x) (dt v t x - dt U t x) =
          -(∑ j, v t x j * inner ℝ (v t x - U t x) (dx j v t x - dx j U t x))
            - inner ℝ (v t x - U t x) (fderiv ℝ (U t) x (v t x - U t x))
            - ∑ j, (v t x - U t x) j * dx j p t x
            + ν * ∑ j, inner ℝ (v t x - U t x) (dx j (dx j v) t x - dx j (dx j U) t x) := by
        intro x
        rw [hdt t ht0 x]
        exact pointwise_identity ν (fderiv ℝ (v t) x) (fderiv ℝ (U t) x) (v t x) (U t x)
          (fun j => dx j p t x) (fun j => dx j (dx j v) t x) (fun j => dx j (dx j U) t x)
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      have hUb : ∀ x, ‖U t x‖ ≤ CU := fun x => by
        have := hCU t ht x; linarith [norm_nonneg (fderiv ℝ (U t) x)]
      have hDUb : ∀ x, ‖fderiv ℝ (U t) x‖ ≤ CU := fun x => by
        have := hCU t ht x; linarith [norm_nonneg (U t x)]
      exact energy_core ν hν.le (v t) (fun x => v t x - U t x) (fun j => dx j v t)
        (fun j x => dx j v t x - dx j U t x)
        (fun j x => dx j (dx j v) t x - dx j (dx j U) t x) (p t) (fun j => dx j p t)
        (fderiv ℝ (U t))
        (fun j x => ((hv_diff t ht0) x).hasFDerivAt.hasLineDerivAt (e j))
        (fun j x => hasLineDerivAt_sub (((hv_diff t ht0) x).hasFDerivAt.hasLineDerivAt (e j))
          (((hU_diff t ht0) x).hasFDerivAt.hasLineDerivAt (e j)))
        (fun j x => hasLineDerivAt_sub
          (((hv_diff2 t ht0 j) x).hasFDerivAt.hasLineDerivAt (e j))
          (((hU_diff2 t ht0 j) x).hasFDerivAt.hasLineDerivAt (e j)))
        (fun j x => ((hp_diff t ht0) x).hasFDerivAt.hasLineDerivAt (e j))
        (fun x => (hv_eq t ht0 x).1)
        (fun x => by
          have h1 := (hv_eq t ht0 x).1
          have h2 := (hU_eq t ht0 x).1
          simp only [div] at h1 h2
          simp only [PiLp.sub_apply, Finset.sum_sub_distrib]
          linarith)
        Cv (Cv + CU) CU (fun x => hCv t ht x)
        (fun x => (norm_sub_le _ _).trans (add_le_add (hCv t ht x) (hUb x))) hDUb
        (memLp_zero hvH2 ht).aestronglyMeasurable
        (measurable_fderiv ℝ (U t)).aestronglyMeasurable
        ((memLp_zero hvH2 ht).sub (memLp_zero hUH2 ht))
        (fun j => memLp_one hvH2 (by norm_num) j ht)
        (fun j => (memLp_one hvH2 (by norm_num) j ht).sub (memLp_one hUH2 (by norm_num) j ht))
        (fun j => (memLp_two hvH2 j ht).sub (memLp_two hUH2 j ht))
        (memLp_zero hpH1 ht) (fun j => memLp_one hpH1 le_rfl j ht)
    obtain ⟨gv, gv', -, -, hgvd, hgv, hgv'⟩ := hvC1
    obtain ⟨gU, gU', -, -, hgUd, hgU, hgU'⟩ := hUC1
    have hGae : ∀ s ∈ Set.Icc 0 T,
        ((gv s - gU s : Lp Space 2 (volume : Measure Space)) : Space → Space)
          =ᵐ[volume] fun x => v s x - U s x := fun s hs =>
      (Lp.coeFn_sub _ _).trans (Filter.EventuallyEq.sub (hgv s hs) (hgU s hs))
    have hG'ae : ∀ s ∈ Set.Icc 0 T,
        ((gv' s - gU' s : Lp Space 2 (volume : Measure Space)) : Space → Space)
          =ᵐ[volume] fun x => dt v s x - dt U s x := fun s hs =>
      (Lp.coeFn_sub _ _).trans (Filter.EventuallyEq.sub (hgv' s hs) (hgU' s hs))
    have h0 : gv 0 - gU 0 = 0 := by
      rw [Lp.eq_zero_iff_ae_eq_zero]
      refine (hGae 0 ⟨le_rfl, hT⟩).trans (Filter.Eventually.of_forall fun x => ?_)
      simp [hv0, hU0]
    have hzero := gronwall_zero T (fun s => gv s - gU s) (fun s => gv' s - gU' s)
      (fun s hs => (hgvd s hs).sub (hgUd s hs)) h0 CU (fun s hs => by
        rw [L2_inner_eq _ _ _ _ (hGae s hs) (hG'ae s hs), L2_norm_sq_eq _ _ (hGae s hs)]
        exact henergy s hs)
    intro t ht
    have hw0 : (fun x => v t x - U t x) =ᵐ[volume] 0 := by
      refine (hGae t ht).symm.trans ?_
      have := hzero t ht
      rw [this]
      exact Lp.coeFn_zero _ _ _
    have hae : v t =ᵐ[volume] U t := hw0.mono fun x hx => sub_eq_zero.1 hx
    exact (Continuous.ae_eq_iff_eq volume (hv_diff t ht.1).continuous
      (hU_diff t ht.1).continuous).1 hae
  have hvU' : ∀ s, 0 ≤ s → v s = U s := fun s hs => hvU s hs s ⟨hs, le_rfl⟩
  intro t ht x
  refine ⟨by rw [hvU' t ht], ?_⟩
  -- Step 2 : the pressure vanishes
  have hgradp : ∀ y, grad p t y = 0 := by
    intro y
    have hdt_eq : dt v t y = dt U t y := by
      simp only [dt]
      rw [fderivWithin_congr (fun s hs => by rw [hvU' s hs]) (by rw [hvU' t ht])]
    have hadv_eq : advection v t y = advection U t y := by
      simp only [advection, hvU' t ht]
    have hdxe : ∀ i, dx i v t = dx i U t := fun i => by
      funext z
      show fderiv ℝ (v t) z (e i) = fderiv ℝ (U t) z (e i)
      rw [hvU' t ht]
    have hlap_eq : laplacian v t y = laplacian U t y := by
      show ∑ i, fderiv ℝ (dx i v t) y (e i) = ∑ i, fderiv ℝ (dx i U t) y (e i)
      simp only [hdxe]
    have h1 := (hv_eq t ht y).2
    have h2 := (hU_eq t ht y).2
    rw [hdt_eq, hadv_eq, hlap_eq] at h1
    have h3 := h1.symm.trans h2
    have h4 := add_right_cancel (add_right_cancel h3)
    rw [grad0] at h4
    simpa using h4
  have hfd : ∀ y, fderiv ℝ (p t) y = 0 := by
    intro y
    have hi : ∀ i, fderiv ℝ (p t) y (e i) = 0 := by
      intro i
      have := congrArg (fun z : Space => z i) (hgradp y)
      simpa [grad, dx] using this
    ext1 z
    rw [clm_expand, zero_apply]
    simp [hi]
  have hconst : ∀ y, p t y = p t 0 := fun y =>
    is_const_of_fderiv_eq_zero (hp_diff t ht) hfd y 0
  have hmem : MemLp (fun _ : Space => p t 0) 2 (volume : Measure Space) := by
    have := memLp_zero (hc t ht).2.2.1 ⟨ht, le_rfl⟩
    have hfun : p t = fun _ => p t 0 := funext hconst
    rwa [hfun] at this
  rw [memLp_const_iff (by norm_num) (by norm_num)] at hmem
  rcases hmem with h | h
  · rw [hconst x, h]
  · exfalso
    rw [measure_univ_of_isAddLeftInvariant] at h
    exact lt_irrefl _ h
