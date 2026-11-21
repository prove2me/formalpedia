-- Prove2me | solution 1 for MulticlassOmni.Lipschitz.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T19:33:35.055968+00:00
-- url     : https://prove2.me/submissions/2fd708f5-70f5-45da-bd4a-722700e83918

import Mathlib
import Definitions.Def_MulticlassOmni_Lipschitz_Packings
import Definitions.Def_MulticlassOmni_Lipschitz_Construction
import Definitions.Def_MulticlassOmni_Lipschitz_ProperLosses
import Definitions.Def_MulticlassOmni_Lipschitz_OmniRegret
import Definitions.Def_MulticlassOmni_Lipschitz_StatLowerBound
import Theorems.Thm_MulticlassOmni_Lipschitz_lemma_B_2
import Theorems.Thm_MulticlassOmni_Lipschitz_lemma_B_3
import Theorems.Thm_MulticlassOmni_Lipschitz_lemma_4_4
import Theorems.Thm_MulticlassOmni_Lipschitz_lemma_B_4

section
namespace MulticlassOmni.Dev.B3
open MulticlassOmni.Lipschitz

theorem eOne_eq {k : ℕ} (h : 0 < k) : eOne k = Pi.single (⟨0, h⟩ : Fin k) (1:ℝ) := by
  funext y
  by_cases hy : (y : ℕ) = 0
  · have : y = ⟨0, h⟩ := Fin.ext hy
    subst this; simp [eOne]
  · have : y ≠ ⟨0, h⟩ := fun e => hy (by simp [e])
    simp [eOne, hy, Pi.single_apply, this]

theorem dot_eOne {k : ℕ} (h : 0 < k) (v : Fin k → ℝ) : dot (eOne k) v = v ⟨0, h⟩ := by
  rw [eOne_eq h]
  simp only [dot]
  rw [Finset.sum_eq_single (⟨0, h⟩ : Fin k)]
  · simp
  · intro y _ hy; simp [Pi.single_apply, hy]
  · intro hh; exact absurd (Finset.mem_univ _) hh

theorem sum_eOne {k : ℕ} (h : 0 < k) : ∑ y, eOne k y = 1 := by
  rw [eOne_eq h]; simp

end MulticlassOmni.Dev.B3
end

section
namespace MulticlassOmni.Dev.F43
open MulticlassOmni.Lipschitz MulticlassOmni.Dev.B3

variable {k N : ℕ}

theorem dot_sub (v u w : Fin k → ℝ) : dot v (u - w) = dot v u - dot v w := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

theorem some_mem_avail (π : Fin N → Fin 2) (i : Fin N) : some i ∈ avail π ↔ π i = 1 := by
  simp [avail]

theorem aSel_min (x : Fin N → Fin k → ℝ) (η : ℝ) (π : Fin N → Fin 2) (σ : Equiv.Perm (Fin N))
    (r : Fin k → ℝ) : ∀ a' ∈ avail π, dot r (cost x η (aSel x η π σ r)) ≤ dot r (cost x η a') := by
  classical
  intro a' ha'
  by_cases h1 : ∀ a ∈ avail π, dot r (costA k) ≤ dot r (cost x η a)
  · have : aSel x η π σ r = none := by unfold aSel; rw [if_pos h1]
    rw [this]; exact h1 a' ha'
  · have h1' := h1
    push Not at h1'
    obtain ⟨a0, ha0, ha0lt⟩ := h1'
    obtain ⟨b, hb, hbmin⟩ := Finset.exists_min_image (avail π) (fun a => dot r (cost x η a)) ⟨a0, ha0⟩
    have hbn : b ≠ none := by
      rintro rfl
      have := hbmin a0 ha0
      have e : cost x η none = costA k := rfl
      rw [e] at this
      linarith
    obtain ⟨i, rfl⟩ := Option.ne_none_iff_exists'.1 hbn
    have hπ : π i = 1 := by
      simp only [avail, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and] at hb
      rcases hb with h | ⟨j, hj, hji⟩
      · exact absurd h (by simp)
      · cases hji; exact hj
    have hMne : ((Finset.univ.filter
      (fun i => π i = 1 ∧ ∀ a ∈ avail π, dot r (costB x η i) ≤ dot r (cost x η a))).image σ).Nonempty :=
      ⟨σ i, Finset.mem_image.2 ⟨i, by simp [hπ]; exact hbmin, rfl⟩⟩
    have hsel : aSel x η π σ r = some (σ.symm ((Finset.univ.filter
      (fun i => π i = 1 ∧ ∀ a ∈ avail π, dot r (costB x η i) ≤ dot r (cost x η a))).image σ |>.min' hMne)) := by
      unfold aSel; rw [if_neg h1]; simp only; rw [dif_pos hMne]
    rw [hsel]
    have hmem := Finset.min'_mem _ hMne
    obtain ⟨m, hm, hm2⟩ := Finset.mem_image.1 hmem
    rw [← hm2]
    simp only [Equiv.symm_apply_apply]
    exact (Finset.mem_filter.1 hm).2.2 a' ha'

theorem aSel_none (x : Fin N → Fin k → ℝ) (η : ℝ) (π : Fin N → Fin 2) (σ : Equiv.Perm (Fin N))
    (r : Fin k → ℝ) (h : ∀ a ∈ avail π, dot r (costA k) ≤ dot r (cost x η a)) :
    aSel x η π σ r = none := by
  classical
  unfold aSel; rw [if_pos h]

theorem aSel_some (x : Fin N → Fin k → ℝ) (η : ℝ) (π : Fin N → Fin 2) (σ : Equiv.Perm (Fin N))
    (r : Fin k → ℝ) (i : Fin N) (hπ : π i = 1)
    (h : ∀ a ∈ avail π, a ≠ some i → dot r (cost x η (some i)) < dot r (cost x η a)) :
    aSel x η π σ r = some i := by
  classical
  have hA : none ∈ avail π := by simp [avail]
  have hi : some i ∈ avail π := by simp [avail, hπ]
  have h1 : ¬ ∀ a ∈ avail π, dot r (costA k) ≤ dot r (cost x η a) := by
    intro hh
    have := hh _ hi
    have := h none hA (by simp)
    simp only [cost] at *
    linarith
  have hM : (Finset.univ.filter
      (fun j => π j = 1 ∧ ∀ a ∈ avail π, dot r (costB x η j) ≤ dot r (cost x η a))) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hj, hj2⟩
      by_contra hne
      have hjm : some j ∈ avail π := by simp [avail, hj]
      have := h (some j) hjm (by simpa using hne)
      have := hj2 (some i) hi
      simp only [cost] at *
      linarith
    · rintro rfl
      refine ⟨hπ, fun a ha => ?_⟩
      by_cases hai : a = some j
      · subst hai; exact le_refl _
      · exact (h a ha hai).le
  have hne : (({i} : Finset (Fin N)).image σ).Nonempty := by simp
  unfold aSel
  rw [if_neg h1]
  simp only [hM]
  rw [dif_pos (by simpa using hne)]
  simp

end MulticlassOmni.Dev.F43
end

section
namespace MulticlassOmni.Dev.F43
open MulticlassOmni.Lipschitz MulticlassOmni.Dev.B3

variable {k N : ℕ}

theorem sum_vbar (hk : 0 < k) : ∑ y, vbar k y = 1 := by
  have : (k:ℝ) ≠ 0 := by positivity
  simp [vbar]; field_simp

theorem dot_costB (x : Fin N → Fin k → ℝ) (η : ℝ) (j : Fin N) (v : Fin k → ℝ) :
    dot v (costB x η j - costA k) =
      -(k:ℝ) * dot v (x j - vbar k) + (1 / 256 - 2 * η) * ∑ y, v y := by
  have : ∀ y, v y * (costB x η j - costA k) y =
      -(k:ℝ) * (v y * (x j - vbar k) y) + (1 / 256 - 2 * η) * v y := by
    intro y; simp [costB]; ring
  simp only [dot]
  rw [Finset.sum_congr rfl (fun y _ => this y), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]

theorem dot_x_w (hk : 0 < k) (xi xj : Fin k → ℝ) (hi : ∑ y, xi y = 1) (hj : ∑ y, xj y = 1) :
    dot xi (xj - vbar k) = dot (xi - vbar k) (xj - vbar k) := by
  have hw : ∑ y, (xj - vbar k) y = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hj, sum_vbar hk, sub_self]
  have : dot (xi - vbar k) (xj - vbar k) = dot xi (xj - vbar k) - dot (vbar k) (xj - vbar k) := by
    simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have h2 : dot (vbar k) (xj - vbar k) = 0 := by
    have e : dot (vbar k) (xj - vbar k) = (1 / (k:ℝ)) * ∑ y, (xj - vbar k) y := by
      simp only [dot, vbar, Finset.mul_sum]
    rw [e, hw]; simp
  linarith

theorem delta_e1 (hk : 0 < k) (x : Fin N → Fin k → ℝ) (η : ℝ) (j : Fin N) :
    dot (eOne k) (costB x η j - costA k) = 1 + 1 / 256 - (k:ℝ) * x j ⟨0, hk⟩ - 2 * η := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  simp [costB, costA, vbar, dot_eOne hk]
  field_simp
  ring

section gaps
variable (hk : 0 < k) (x : Fin N → Fin k → ℝ) (η : ℝ)
  (hs : ∀ i, x i ∈ stdSimplex ℝ (Fin k))
  (hsph : ∀ i, ∑ y, (x i y - vbar k y) ^ 2 = 1 / (256 * (k:ℝ)))
  (hsep : ∀ i j, i ≠ j → dot (x i - vbar k) (x j - vbar k) ≤ (1 - 1024 * η) / (256 * (k:ℝ)))

include hk hs hsph in
theorem delta_self (i : Fin N) : dot (x i) (costB x η i - costA k) = -2 * η := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  rw [dot_costB, (hs i).2, dot_x_w hk _ _ (hs i).2 (hs i).2]
  have : dot (x i - vbar k) (x i - vbar k) = 1 / (256 * (k:ℝ)) := by
    rw [← hsph i]; simp [dot, sq]
  rw [this]; field_simp; ring

include hk hs hsep in
theorem delta_other (i j : Fin N) (hij : i ≠ j) :
    2 * η ≤ dot (x i) (costB x η j - costA k) := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  rw [dot_costB, (hs i).2, dot_x_w hk _ _ (hs i).2 (hs j).2]
  have := hsep i j hij
  rw [le_div_iff₀ (by positivity)] at this
  have h2 : (k:ℝ) * dot (x i - vbar k) (x j - vbar k) ≤ (1 - 1024 * η) / 256 := by
    have : (k:ℝ) * dot (x i - vbar k) (x j - vbar k) * 256 ≤ 1 - 1024 * η := by nlinarith
    linarith
  nlinarith

end gaps

end MulticlassOmni.Dev.F43
end

section
namespace MulticlassOmni.Dev.F43

open MulticlassOmni.Lipschitz

theorem eta_small (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε)
    (hlt : ε < (δ ^ 2 / 192) ^ 2 / ((k : ℝ) * Real.log ((k : ℝ) + 1))) :
    0 < eta k ε ∧ eta k ε ≤ δ := by
  set m := δ ^ 2 / 192 with hm
  have hm0 : 0 < m := by positivity
  have hm1 : m ≤ 1 := by rw [hm]; nlinarith
  set c := m ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hk3 : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hL : 1 < Real.log ((k : ℝ) + 1) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  set L := Real.log ((k : ℝ) + 1) with hLdef
  have hs : (k:ℝ) * ε < c / L := by
    have := hlt
    rw [lt_div_iff₀ (by positivity)] at this
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  set s := (k:ℝ) * ε with hsdef
  have hs0 : 0 < s := by positivity
  have hsL : s * L < c := by rwa [lt_div_iff₀ (by positivity)] at hs
  have hsc : s < c := by
    have : c / L < c := by rw [div_lt_iff₀ (by linarith)]; nlinarith
    linarith
  have hc1 : c ≤ 1 := by rw [hc]; nlinarith
  have hε1 : ε < 1 := by
    have : ε ≤ s := by rw [hsdef]; nlinarith
    linarith
  have hlogε : 0 < Real.log (1 / ε) := Real.log_pos (by rw [lt_div_iff₀ hε]; linarith)
  have hX0 : 0 < (k:ℝ) * ε * Real.log (1 / ε) := by positivity
  refine ⟨by unfold eta; positivity, ?_⟩
  -- bound X
  have hlogk : Real.log (k:ℝ) ≤ L := Real.log_le_log (by linarith) (by linarith)
  have hsplit : Real.log (1 / ε) = Real.log (k:ℝ) - Real.log s := by
    rw [one_div, Real.log_inv, hsdef, Real.log_mul (by positivity) hε.ne']
    ring
  set u := Real.sqrt s with hu
  have hu0 : 0 < u := Real.sqrt_pos.2 hs0
  have hus : u ^ 2 = s := Real.sq_sqrt hs0.le
  have hlogs : Real.log s = 2 * Real.log u := by
    rw [← hus, Real.log_pow]; norm_num
  have hlu : -Real.log u ≤ 1 / u := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 / u by positivity)
    rw [one_div, Real.log_inv] at this
    rw [one_div]; linarith
  have hu_lt : u < m := by
    rw [hu]; rw [show m = Real.sqrt (m ^ 2) by rw [Real.sqrt_sq hm0.le]]
    exact Real.sqrt_lt_sqrt hs0.le hsc
  have h1 : s * Real.log (k:ℝ) ≤ s * L := mul_le_mul_of_nonneg_left hlogk hs0.le
  have h2 : s * (-Real.log s) ≤ 2 * u := by
    rw [hlogs, ← hus]
    have : u ^ 2 * (-(2 * Real.log u)) = 2 * u ^ 2 * (-Real.log u) := by ring
    rw [this]
    have h3 : 2 * u ^ 2 * (-Real.log u) ≤ 2 * u ^ 2 * (1 / u) :=
      mul_le_mul_of_nonneg_left hlu (by positivity)
    have h4 : 2 * u ^ 2 * (1 / u) = 2 * u := by field_simp
    linarith
  have hX : (k:ℝ) * ε * Real.log (1 / ε) ≤ (δ / 8) ^ 2 := by
    have : (k:ℝ) * ε * Real.log (1 / ε) = s * Real.log (k:ℝ) + s * (-Real.log s) := by
      rw [hsplit, ← hsdef]; ring
    rw [this]
    have : (δ / 8) ^ 2 = 3 * m := by rw [hm]; ring
    rw [this]
    have : c ≤ m := by rw [hc]; nlinarith
    nlinarith
  unfold eta
  have := Real.sqrt_le_sqrt hX
  rw [Real.sqrt_sq (by positivity)] at this
  linarith

end MulticlassOmni.Dev.F43
end

section
/-! Measure-theoretic bookkeeping for Theorem 4.1: a learner gives a randomized estimator, and
the output laws are probability measures under which the population regrets are integrable. -/

noncomputable section

open MeasureTheory

namespace MulticlassOmni.Dev.T41
open MulticlassOmni.Lipschitz

/-- `D_θ` on `↥X × [k]`, transported from `Fin N × [k]` along `e`. -/
def distOf {k N : ℕ} {X : Finset (Fin k → ℝ)} (e : Fin N ≃ ↥X) (q : Fin 2 → Fin N → Fin k → ℝ)
    (θ : Fin N → Fin 2) (z : ↥X × Fin k) : ℝ :=
  dataDist q θ (e.symm z.1, z.2)

/-- Predictors whose estimate has Hamming error at least `N/4`. -/
def badSet {k N : ℕ} {X : Finset (Fin k → ℝ)} (θhat : Predictor X → (Fin N → Fin 2))
    (θ : Fin N → Fin 2) : Set (Predictor X) :=
  {p | (N : ℝ) / 4 ≤ (hammingErr (θhat p) θ : ℝ)}

/-- A sample indexed by `Fin N`, transported to `↥X`. -/
def liftS {k N n : ℕ} {X : Finset (Fin k → ℝ)} (e : Fin N ≃ ↥X) (S : Fin n → Fin N × Fin k) :
    Sample X n :=
  fun j => (e (S j).1, (S j).2)

/-- The estimator induced by a learner and a measurable decoding map `θhat`. -/
def estOf {k N n : ℕ} {X : Finset (Fin k → ℝ)} (e : Fin N ≃ ↥X) (A : Learner X n)
    (θhat : Predictor X → (Fin N → Fin 2)) (S : Fin n → Fin N × Fin k) (t : Fin N → Fin 2) : ℝ :=
  ((A (liftS e S) : Measure (Predictor X)) (θhat ⁻¹' {t})).toReal

theorem measurableSet_fiber {k N : ℕ} {X : Finset (Fin k → ℝ)}
    {θhat : Predictor X → (Fin N → Fin 2)} (hθ : Measurable θhat) (T : Set (Fin N → Fin 2)) :
    MeasurableSet (θhat ⁻¹' T) :=
  hθ (Set.toFinite T).measurableSet

theorem isRandEstimator_estOf {k N n : ℕ} {X : Finset (Fin k → ℝ)} (e : Fin N ≃ ↥X)
    (A : Learner X n) {θhat : Predictor X → (Fin N → Fin 2)} (hθ : Measurable θhat) :
    IsRandEstimator (estOf e A θhat) := by
  intro S
  refine ⟨fun t => ENNReal.toReal_nonneg, ?_⟩
  set μ : Measure (Predictor X) := (A (liftS e S) : Measure (Predictor X))
  have h1 : ∑ t, μ (θhat ⁻¹' {t}) = μ (θhat ⁻¹' ↑(Finset.univ : Finset (Fin N → Fin 2))) :=
    sum_measure_preimage_singleton _ (fun t _ => measurableSet_fiber hθ _)
  simp only [Finset.coe_univ, Set.preimage_univ, measure_univ] at h1
  unfold estOf
  rw [← ENNReal.toReal_sum (fun t _ => measure_ne_top _ _)]
  change (∑ t, μ (θhat ⁻¹' {t})).toReal = 1
  rw [h1]; simp

theorem outputLaw_apply {k n : ℕ} {X : Finset (Fin k → ℝ)} (A : Learner X n)
    (D : ↥X × Fin k → ℝ) (s : Set (Predictor X)) :
    outputLaw A D s = ∑ S : Sample X n,
      ENNReal.ofReal (∏ j, D (S j)) * ((A S : ProbabilityMeasure _) : Measure _) s := by
  unfold outputLaw
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  rfl

theorem isProb_outputLaw {k n : ℕ} {X : Finset (Fin k → ℝ)} (A : Learner X n)
    (D : ↥X × Fin k → ℝ) (hD : IsDist D) : IsProbabilityMeasure (outputLaw A D) := by
  constructor
  rw [outputLaw_apply]
  simp only [measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun S _ => Finset.prod_nonneg (fun j _ => hD.1 _))]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (z : ↥X × Fin k) => D z)]
  simp [hD.2]

/-- The key identity: the Hamming failure probability of the induced estimator is the average
over `θ` of the output-law mass of the bad set. -/
theorem hammingFailProb_estOf {k N n : ℕ} {X : Finset (Fin k → ℝ)} (e : Fin N ≃ ↥X)
    (q : Fin 2 → Fin N → Fin k → ℝ) (hq : ∀ b i y, 0 ≤ q b i y)
    (A : Learner X n) {θhat : Predictor X → (Fin N → Fin 2)} (hθ : Measurable θhat) :
    hammingFailProb q (estOf e A θhat) = ∑ θ : Fin N → Fin 2, (1 / (2 : ℝ) ^ N) *
      (outputLaw A (distOf e q θ) (badSet θhat θ)).toReal := by
  unfold hammingFailProb
  refine Finset.sum_congr rfl (fun θ _ => ?_)
  congr 1
  have hdd : ∀ z, 0 ≤ dataDist q θ z := fun z => by
    unfold dataDist; exact div_nonneg (hq _ _ _) (Nat.cast_nonneg _)
  -- inner sum over t
  have hin : ∀ S : Fin n → Fin N × Fin k,
      ∑ t : Fin N → Fin 2, estOf e A θhat S t *
        (if (N : ℝ) / 4 ≤ (hammingErr t θ : ℝ) then 1 else 0) =
      ((A (liftS e S) : Measure (Predictor X)) (badSet θhat θ)).toReal := by
    intro S
    set μ : Measure (Predictor X) := (A (liftS e S) : Measure (Predictor X))
    set T : Finset (Fin N → Fin 2) :=
      Finset.univ.filter (fun t => (N : ℝ) / 4 ≤ (hammingErr t θ : ℝ))
    have hT : badSet θhat θ = θhat ⁻¹' ↑T := by
      ext p; simp [badSet, T]
    rw [hT, ← sum_measure_preimage_singleton T (fun t _ => measurableSet_fiber hθ _),
      ENNReal.toReal_sum (fun t _ => measure_ne_top _ _)]
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    rfl
  simp only [hin]
  rw [outputLaw_apply, ENNReal.toReal_sum (fun S _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  simp only [ENNReal.toReal_mul]
  -- reindex
  let E : (Fin n → Fin N × Fin k) ≃ Sample X n :=
    Equiv.arrowCongr (Equiv.refl _) (Equiv.prodCongr e (Equiv.refl _))
  have hE : ∀ S, E S = liftS e S := fun S => rfl
  rw [← Equiv.sum_comp E]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [hE]
  congr 1
  rw [ENNReal.toReal_ofReal (Finset.prod_nonneg (fun j _ => ?_))]
  · refine Finset.prod_congr rfl (fun j _ => ?_)
    simp [distOf, liftS]
  · simp only [distOf, liftS]; exact hdd _

/-- If every output law puts mass at most `1/2` on the bad set, the induced estimator fails
with probability at most `1/2`. -/
theorem exists_bad {k N n : ℕ} {X : Finset (Fin k → ℝ)} (e : Fin N ≃ ↥X)
    (q : Fin 2 → Fin N → Fin k → ℝ) (hq : ∀ b i y, 0 ≤ q b i y)
    (A : Learner X n) {θhat : Predictor X → (Fin N → Fin 2)} (hθ : Measurable θhat)
    (hB4 : 9 / 10 ≤ hammingFailProb q (estOf e A θhat)) :
    ∃ θ : Fin N → Fin 2, 1 / 2 < (outputLaw A (distOf e q θ) (badSet θhat θ)).toReal := by
  by_contra hcon
  push Not at hcon
  rw [hammingFailProb_estOf e q hq A hθ] at hB4
  have : ∑ θ : Fin N → Fin 2, (1 / (2 : ℝ) ^ N) *
      (outputLaw A (distOf e q θ) (badSet θhat θ)).toReal ≤
      ∑ θ : Fin N → Fin 2, (1 / (2 : ℝ) ^ N) * (1 / 2) :=
    Finset.sum_le_sum (fun θ _ => mul_le_mul_of_nonneg_left (hcon θ) (by positivity))
  rw [Finset.sum_const, Finset.card_univ] at this
  simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ,
    nsmul_eq_mul] at this
  have h2 : ((2 ^ N : ℕ) : ℝ) * (1 / (2 : ℝ) ^ N * (1 / 2)) = 1 / 2 := by
    push_cast; field_simp
  rw [h2] at this
  linarith

theorem distOf_isDist {k N : ℕ} {X : Finset (Fin k → ℝ)} (hN : 0 < N) (e : Fin N ≃ ↥X)
    (q : Fin 2 → Fin N → Fin k → ℝ) (hq : ∀ b i, q b i ∈ stdSimplex ℝ (Fin k))
    (θ : Fin N → Fin 2) : IsDist (distOf e q θ) := by
  refine ⟨fun z => div_nonneg ((hq _ _).1 _) (Nat.cast_nonneg _), ?_⟩
  let E : Fin N × Fin k ≃ ↥X × Fin k := Equiv.prodCongr e (Equiv.refl _)
  rw [← Equiv.sum_comp E, Fintype.sum_prod_type]
  simp only [E, distOf, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq,
    Equiv.symm_apply_apply, dataDist]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [← Finset.sum_div, (hq _ _).2]
  simp; omega

/-- The population regret in coordinates `Fin N`. -/
theorem popRegret_distOf {k N : ℕ} {X : Finset (Fin k → ℝ)} (e : Fin N ≃ ↥X)
    (q : Fin 2 → Fin N → Fin k → ℝ) (θ : Fin N → Fin 2) (ℓ : Loss k) (p f : Predictor X) :
    popRegret (distOf e q θ) ℓ p f = (1 / (N : ℝ)) * ∑ i, expect (q (θ i) i)
      (fun y => ℓ (p (e i) : Fin k → ℝ) y - ℓ (f (e i) : Fin k → ℝ) y) := by
  unfold popRegret
  let E : Fin N × Fin k ≃ ↥X × Fin k := Equiv.prodCongr e (Equiv.refl _)
  rw [← Equiv.sum_comp E, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [E, distOf, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq,
    Equiv.symm_apply_apply, dataDist, expect, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  ring

/-- A loss in `L_lip-proper` is continuous on the simplex. -/
theorem continuous_loss {k : ℕ} {ℓ : Loss k} (hℓ : IsLipProper ℓ) (y : Fin k) :
    Continuous (fun r : Simplex k => ℓ (r : Fin k → ℝ) y) := by
  refine (LipschitzWith.of_dist_le_mul (K := (k : NNReal)) (fun r r' => ?_)).continuous
  rw [Real.dist_eq]
  refine (hℓ.2 r r.2 r' r'.2 y).trans ?_
  unfold l1dist
  have : ∀ i, |(r : Fin k → ℝ) i - (r' : Fin k → ℝ) i| ≤ dist r r' := by
    intro i
    rw [Subtype.dist_eq, ← Real.dist_eq]
    exact dist_le_pi_dist (r : Fin k → ℝ) (r' : Fin k → ℝ) i
  calc ∑ i, |(r : Fin k → ℝ) i - (r' : Fin k → ℝ) i| ≤ ∑ _i : Fin k, dist r r' :=
        Finset.sum_le_sum (fun i _ => this i)
    _ = ((k : NNReal) : ℝ) * dist r r' := by simp

theorem continuous_popRegret {k : ℕ} {X : Finset (Fin k → ℝ)} {ℓ : Loss k}
    (hℓ : IsLipProper ℓ) (D : ↥X × Fin k → ℝ) (f : Predictor X) :
    Continuous (fun p : Predictor X => popRegret D ℓ p f) := by
  unfold popRegret
  refine continuous_finsetSum _ (fun z _ => ?_)
  exact continuous_const.mul
    (((continuous_loss hℓ z.2).comp (continuous_apply z.1)).sub continuous_const)

theorem abs_popRegret_le {k : ℕ} {X : Finset (Fin k → ℝ)} {ℓ : Loss k}
    (hℓ : IsLipProper ℓ) {D : ↥X × Fin k → ℝ} (hD : IsDist D) (p f : Predictor X) :
    |popRegret D ℓ p f| ≤ 1 := by
  unfold popRegret
  rw [← hD.2]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun z _ => ?_))
  rw [abs_mul, abs_of_nonneg (hD.1 z)]
  have h1 : ℓ (p z.1 : Fin k → ℝ) z.2 ∈ Set.Icc (0:ℝ) 1 := hℓ.1.2 _ (p z.1).2 z.2
  have h2 : ℓ (f z.1 : Fin k → ℝ) z.2 ∈ Set.Icc (0:ℝ) 1 := hℓ.1.2 _ (f z.1).2 z.2
  have : |ℓ (p z.1 : Fin k → ℝ) z.2 - ℓ (f z.1 : Fin k → ℝ) z.2| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  calc D z * |ℓ (p z.1 : Fin k → ℝ) z.2 - ℓ (f z.1 : Fin k → ℝ) z.2| ≤ D z * 1 :=
        mul_le_mul_of_nonneg_left this (hD.1 z)
    _ = D z := mul_one _

theorem integrable_popRegret {k n : ℕ} {X : Finset (Fin k → ℝ)} {ℓ : Loss k}
    (hℓ : IsLipProper ℓ) (A : Learner X n) {D : ↥X × Fin k → ℝ} (hD : IsDist D)
    (f : Predictor X) :
    Integrable (fun p : Predictor X => popRegret D ℓ p f) (outputLaw A D) := by
  have := isProb_outputLaw A D hD
  exact Integrable.of_bound (continuous_popRegret hℓ D f).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs]; exact abs_popRegret_le hℓ hD p f))

end MulticlassOmni.Dev.T41
end
end

section
/-! Theorem 4.1: the estimator `θ̂_p` and the regret–Hamming inequality (49)–(51). -/

noncomputable section

open MeasureTheory

namespace MulticlassOmni.Dev.T41
open MulticlassOmni.Lipschitz MulticlassOmni.Dev.F43 MulticlassOmni.Dev.B3

/-- `π_β(θ)(x_i) := 1{θ(x_i) = β - 1}`. -/
def piB {N : ℕ} (θ : Fin N → Fin 2) (β : ℕ) : Fin N → Fin 2 :=
  fun i => if ((θ i : ℕ) = β - 1) then 1 else 0

theorem piB_spec {N : ℕ} (θ : Fin N → Fin 2) (β : ℕ) (i : Fin N) :
    piB θ β i = 1 → ((θ i : ℕ) = β - 1) := by
  unfold piB; split_ifs with h <;> simp [h]

/-- The local test at `x_i`: `0` if `⟨r, c_{B_i} - c_A⟩ ≥ 0`, else `1`. -/
def localEst {k N : ℕ} (x : Fin N → Fin k → ℝ) (η : ℝ) (i : Fin N) (r : Fin k → ℝ) : Fin 2 :=
  if 0 ≤ dot r (costB x η i - costA k) then 0 else 1

/-- The estimator `θ̂_p`. -/
def thetaHat {k N : ℕ} {X : Finset (Fin k → ℝ)} (x : Fin N → Fin k → ℝ) (η : ℝ)
    (e : Fin N ≃ ↥X) (p : Predictor X) : Fin N → Fin 2 :=
  fun i => localEst x η i (p (e i) : Fin k → ℝ)

theorem measurable_thetaHat {k N : ℕ} {X : Finset (Fin k → ℝ)} (x : Fin N → Fin k → ℝ) (η : ℝ)
    (e : Fin N ≃ ↥X) : Measurable (thetaHat x η e) := by
  refine measurable_pi_lambda _ (fun i => ?_)
  have hc : Continuous (fun p : Predictor X =>
      dot (p (e i) : Fin k → ℝ) (costB x η i - costA k)) := by
    have hv : Continuous (fun p : Predictor X => (p (e i) : Fin k → ℝ)) :=
      continuous_subtype_val.comp (continuous_apply (e i))
    unfold dot
    refine continuous_finsetSum _ (fun y _ => ?_)
    exact ((continuous_apply y).comp hv).mul continuous_const
  unfold thetaHat localEst
  exact Measurable.ite (measurableSet_le measurable_const hc.measurable) measurable_const
    measurable_const

/-- The combinatorial fact (50) at one index. -/
theorem local_indicator {k N : ℕ} (hk : 3 ≤ k) (x : Fin N → Fin k → ℝ) (η : ℝ) (hη0 : 0 < η)
    (hη : η ≤ 1 / 32)
    (hs : ∀ i, x i ∈ stdSimplex ℝ (Fin k))
    (h1 : ∀ i, ∀ y : Fin k, (y : ℕ) = 0 → x i y ≤ 15 / (16 * (k : ℝ)))
    (hsph : ∀ i, ∑ y, (x i y - vbar k y) ^ 2 = 1 / (256 * (k : ℝ)))
    (hsep : ∀ i j, i ≠ j → dot (x i - vbar k) (x j - vbar k) ≤ (1 - 1024 * η) / (256 * (k : ℝ)))
    (σ : Equiv.Perm (Fin N)) (θ : Fin N → Fin 2) (i : Fin N) (r : Fin k → ℝ) :
    (if localEst x η i r ≠ θ i then (1 : ℝ) else 0) ≤
      (if aSel x η (piB θ 1) σ r ≠ aSel x η (piB θ 1) σ (bench x 1 i) then (1 : ℝ) else 0) +
      (if aSel x η (piB θ 2) σ r ≠ aSel x η (piB θ 2) σ (bench x 2 i) then (1 : ℝ) else 0) := by
  have hk0 : 0 < k := by omega
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
  have cn : cost x η none = costA k := rfl
  have cs : ∀ j, cost x η (some j) = costB x η j := fun _ => rfl
  have nn : ∀ (a b : Prop) [Decidable a] [Decidable b],
      (0 : ℝ) ≤ (if a then (1 : ℝ) else 0) := by intros; split_ifs <;> norm_num
  by_cases hloc : localEst x η i r = θ i
  · simp only [hloc, ne_eq, not_true_eq_false, if_false]
    have := nn (aSel x η (piB θ 1) σ r ≠ aSel x η (piB θ 1) σ (bench x 1 i)) True
    have := nn (aSel x η (piB θ 2) σ r ≠ aSel x η (piB θ 2) σ (bench x 2 i)) True
    linarith
  simp only [hloc, ne_eq, not_false_eq_true, if_true]
  have hθ : (θ i : ℕ) = 0 ∨ (θ i : ℕ) = 1 := by have := (θ i).isLt; omega
  rcases hθ with h0 | h1'
  · -- θ i = 0, the estimate is 1: use β = 1
    have hl : localEst x η i r = 1 := by
      have : θ i = 0 := Fin.ext h0
      have h2 : localEst x η i r ≠ 0 := by rw [← this]; exact hloc
      unfold localEst at h2 ⊢; split_ifs at h2 ⊢ with h <;> simp_all
    have hneg : dot r (costB x η i) < dot r (costA k) := by
      unfold localEst at hl
      split_ifs at hl with h
      · simp at hl
      · rw [dot_sub] at h; linarith
    have hπ : piB θ 1 i = 1 := by simp [piB, h0]
    have hbench : aSel x η (piB θ 1) σ (bench x 1 i) = none := by
      apply aSel_none
      intro a ha
      cases a with
      | none => exact le_refl _
      | some j =>
        rw [cs]
        simp only [bench, if_true]
        have hd := delta_e1 hk0 x η j
        have hx : (k : ℝ) * x j ⟨0, hk0⟩ ≤ 15 / 16 := by
          have := h1 j ⟨0, hk0⟩ rfl
          rw [le_div_iff₀ (by positivity)] at this
          nlinarith
        rw [dot_sub] at hd
        linarith
    have hr : aSel x η (piB θ 1) σ r ≠ none := by
      intro hn
      have := aSel_min x η (piB θ 1) σ r (some i) ((some_mem_avail _ _).2 hπ)
      rw [hn, cn, cs] at this
      linarith
    rw [hbench, if_pos hr]
    have := nn (aSel x η (piB θ 2) σ r ≠ aSel x η (piB θ 2) σ (bench x 2 i)) True
    linarith
  · -- θ i = 1, the estimate is 0: use β = 2
    have hl : localEst x η i r = 0 := by
      have : θ i = 1 := Fin.ext h1'
      have h2 : localEst x η i r ≠ 1 := by rw [← this]; exact hloc
      unfold localEst at h2 ⊢; split_ifs at h2 ⊢ with h <;> simp_all
    have hpos : dot r (costA k) ≤ dot r (costB x η i) := by
      unfold localEst at hl
      split_ifs at hl with h
      · rw [dot_sub] at h; linarith
      · simp at hl
    have hπ : piB θ 2 i = 1 := by simp [piB, h1']
    have hbench : aSel x η (piB θ 2) σ (bench x 2 i) = some i := by
      have hb : bench x 2 i = x i := by simp [bench]
      rw [hb]
      apply aSel_some x η _ σ _ i hπ
      intro a ha hne
      have hself := delta_self hk0 x η hs hsph i
      rw [dot_sub] at hself
      cases a with
      | none => rw [cn, cs]; linarith
      | some j =>
        have hji : j ≠ i := fun h => hne (by rw [h])
        have := delta_other hk0 x η hs hsep i j (Ne.symm hji)
        rw [dot_sub] at this
        rw [cs, cs]; linarith
    have hr : aSel x η (piB θ 2) σ r ≠ some i := by
      intro hsome
      have hmin := aSel_min x η (piB θ 2) σ r
      rw [hsome, cs] at hmin
      have : aSel x η (piB θ 2) σ r = none := by
        apply aSel_none
        intro a ha
        have := hmin a ha
        linarith
      rw [hsome] at this
      exact absurd this (by simp)
    rw [hbench, if_pos hr]
    have := nn (aSel x η (piB θ 1) σ r ≠ aSel x η (piB θ 1) σ (bench x 1 i)) True
    linarith

/-- The regret–Hamming inequality (51). -/
theorem regret_sum_ge {k N : ℕ} {X : Finset (Fin k → ℝ)} (hk : 3 ≤ k) (hN : 0 < N)
    (x : Fin N → Fin k → ℝ) (η ε : ℝ) (hη0 : 0 < η) (hε : 0 ≤ ε)
    (hη : η ≤ 1 / 32)
    (hs : ∀ i, x i ∈ stdSimplex ℝ (Fin k))
    (h1 : ∀ i, ∀ y : Fin k, (y : ℕ) = 0 → x i y ≤ 15 / (16 * (k : ℝ)))
    (hsph : ∀ i, ∑ y, (x i y - vbar k y) ^ 2 = 1 / (256 * (k : ℝ)))
    (hsep : ∀ i j, i ≠ j → dot (x i - vbar k) (x j - vbar k) ≤ (1 - 1024 * η) / (256 * (k : ℝ)))
    (σ : Equiv.Perm (Fin N))
    (H44 : ∀ (i : Fin N) (b : Fin 2) (β : ℕ) (π : Fin N → Fin 2),
      (β = 1 ∨ β = 2) → (π i = 1 → (b : ℕ) = β - 1) →
        ∀ r ∈ stdSimplex ℝ (Fin k),
          24 * ε * (if aSel x η π σ r ≠ aSel x η π σ (bench x β i) then 1 else 0) - ε / 8 ≤
            expect (qLip x η b i)
              (fun y => smoothLoss x η ε π r y - smoothLoss x η ε π (bench x β i) y))
    (e : Fin N ≃ ↥X) (f₁ f₂ : Predictor X)
    (hf₁ : ∀ i, (f₁ (e i) : Fin k → ℝ) = bench x 1 i)
    (hf₂ : ∀ i, (f₂ (e i) : Fin k → ℝ) = bench x 2 i)
    (θ : Fin N → Fin 2) (p : Predictor X) :
    24 * ε / N * (hammingErr (thetaHat x η e p) θ : ℝ) - ε / 4 ≤
      popRegret (distOf e (qLip x η) θ) (smoothLoss x η ε (piB θ 1)) p f₁ +
      popRegret (distOf e (qLip x η) θ) (smoothLoss x η ε (piB θ 2)) p f₂ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [popRegret_distOf, popRegret_distOf]
  simp only [hf₁, hf₂]
  set I : ℕ → Fin N → ℝ := fun β i =>
    if aSel x η (piB θ β) σ (p (e i) : Fin k → ℝ) ≠ aSel x η (piB θ β) σ (bench x β i)
      then 1 else 0 with hI
  have hlow : ∀ β, (β = 1 ∨ β = 2) → ∀ i, 24 * ε * I β i - ε / 8 ≤
      expect (qLip x η (θ i) i) (fun y => smoothLoss x η ε (piB θ β) (p (e i) : Fin k → ℝ) y -
        smoothLoss x η ε (piB θ β) (bench x β i) y) :=
    fun β hβ i => H44 i (θ i) β (piB θ β) hβ (piB_spec θ β i) _ (p (e i)).2
  have hham : (hammingErr (thetaHat x η e p) θ : ℝ) =
      ∑ i, (if localEst x η i (p (e i) : Fin k → ℝ) ≠ θ i then (1 : ℝ) else 0) := by
    unfold hammingErr
    rw [Finset.natCast_card_filter]
    rfl
  have hloc := fun i => local_indicator hk x η hη0 hη hs h1 hsph hsep σ θ i (p (e i) : Fin k → ℝ)
  rw [hham]
  have hsum1 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlow 1 (Or.inl rfl) i)
  have hsum2 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlow 2 (Or.inr rfl) i)
  have hsum3 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hloc i)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_add_distrib] at hsum1 hsum2 hsum3
  set E1 := ∑ i, expect (qLip x η (θ i) i) (fun y => smoothLoss x η ε (piB θ 1)
    (p (e i) : Fin k → ℝ) y - smoothLoss x η ε (piB θ 1) (bench x 1 i) y)
  set E2 := ∑ i, expect (qLip x η (θ i) i) (fun y => smoothLoss x η ε (piB θ 2)
    (p (e i) : Fin k → ℝ) y - smoothLoss x η ε (piB θ 2) (bench x 2 i) y)
  set H := ∑ i, (if localEst x η i (p (e i) : Fin k → ℝ) ≠ θ i then (1 : ℝ) else 0)
  have key : 24 * ε * H - (N : ℝ) * (ε / 4) ≤ E1 + E2 := by
    nlinarith
  rw [one_div_mul_eq_div, one_div_mul_eq_div]
  calc 24 * ε / N * H - ε / 4 = (24 * ε * H - (N : ℝ) * (ε / 4)) / N := by
        field_simp
    _ ≤ (E1 + E2) / N := div_le_div_of_nonneg_right key hNr.le
    _ = E1 / N + E2 / N := add_div _ _ _

end MulticlassOmni.Dev.T41
end
end

section
/-! Theorem 4.1: the choice of the constant `C` (pure real arithmetic). -/

namespace MulticlassOmni.Dev.T41

/-- The constant `C := 64 (2 C₁ max(1, 1/c₀))⁴`. -/
noncomputable def Ccon (c₀ C₁ : ℝ) : ℝ := 64 * (2 * C₁ * max 1 (1 / c₀)) ^ 4

theorem Ccon_pos (c₀ C₁ : ℝ) (hC₁ : 2 ≤ C₁) : 0 < Ccon c₀ C₁ := by
  unfold Ccon
  have : 0 < max 1 (1 / c₀) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have : 0 < C₁ := by linarith
  positivity

theorem nat_le_two_pow (k : ℕ) : (k : ℝ) ≤ 2 ^ (k + 2) := by
  have : k < 2 ^ k := Nat.lt_two_pow_self
  have h : (k : ℝ) ≤ 2 ^ k := by exact_mod_cast this.le
  have : (2 : ℝ) ^ k ≤ 2 ^ (k + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

/-- If `N ≥ C₁^{-k} η^{-(k-2)/2}` with `η = 8 √u`, then `(C u)^{-(k+2)/4} ≤ c₀ N / (k η²)`. -/
theorem const_bound (c₀ C₁ : ℝ) (hc₀ : 0 < c₀) (hC₁ : 2 ≤ C₁) (k : ℕ) (hk : 3 ≤ k) (u : ℝ)
    (hu : 0 < u) (Nr : ℝ)
    (hN : C₁ ^ (-(k : ℝ)) * (8 * Real.sqrt u) ^ (-((k : ℝ) - 2) / 2) ≤ Nr) :
    (Ccon c₀ C₁ * u) ^ (-((k : ℝ) + 2) / 4) ≤ c₀ * Nr / (k * (8 * Real.sqrt u) ^ 2) := by
  set K := max 1 (1 / c₀) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKc : 1 / c₀ ≤ K := le_max_right _ _
  set B := 2 * C₁ * K with hB
  have hB0 : 0 < B := by positivity
  set w := 64 * u with hw
  have hw0 : 0 < w := by positivity
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hη : 8 * Real.sqrt u = w ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow, hw, Real.sqrt_mul (by norm_num)]
    congr 1
    rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hη2 : (8 * Real.sqrt u) ^ 2 = w := by
    rw [mul_pow, Real.sq_sqrt hu.le]; ring
  set a : ℝ := -((k : ℝ) + 2) / 4 with ha
  have hpowη : (8 * Real.sqrt u) ^ (-((k : ℝ) - 2) / 2) = w ^ a * w := by
    rw [hη, ← Real.rpow_mul hw0.le]
    conv_rhs => rw [show w ^ a * w = w ^ a * w ^ (1 : ℝ) by rw [Real.rpow_one]]
    rw [← Real.rpow_add hw0]
    congr 1; rw [ha]; ring
  have hC : Ccon c₀ C₁ * u = B ^ 4 * w := by
    simp only [Ccon, hB, hK, hw]; ring
  have hLHS : (Ccon c₀ C₁ * u) ^ a = (B ^ (k + 2))⁻¹ * w ^ a := by
    rw [hC, Real.mul_rpow (by positivity) hw0.le]
    congr 1
    rw [show (B ^ 4 : ℝ) = B ^ (4 : ℝ) by norm_cast, ← Real.rpow_mul hB0.le,
      show 4 * a = -((k + 2 : ℕ) : ℝ) by rw [ha]; push_cast; ring, Real.rpow_neg hB0.le,
      Real.rpow_natCast]
  have hC1 : C₁ ^ (-(k : ℝ)) = (C₁ ^ k)⁻¹ := by
    rw [Real.rpow_neg (by linarith), Real.rpow_natCast]
  rw [hpowη, hC1] at hN
  rw [hLHS, hη2]
  have hwa : 0 < w ^ a := Real.rpow_pos_of_pos hw0 _
  have hC1p : 0 < C₁ ^ k := by positivity
  -- core inequality: k C₁^k ≤ c₀ B^(k+2)
  have hcore : (k : ℝ) * C₁ ^ k ≤ c₀ * B ^ (k + 2) := by
    have e : B ^ (k + 2) = 2 ^ (k + 2) * C₁ ^ (k + 2) * K ^ (k + 2) := by
      rw [hB]; ring
    have h1 : C₁ ^ k ≤ C₁ ^ (k + 2) := pow_le_pow_right₀ (by linarith) (by omega)
    have h2 : K ≤ K ^ (k + 2) := by
      calc K = K ^ 1 := (pow_one K).symm
        _ ≤ K ^ (k + 2) := pow_le_pow_right₀ hK1 (by omega)
    have h3 : 1 ≤ c₀ * K ^ (k + 2) := by
      have : 1 ≤ c₀ * K := by
        rw [div_le_iff₀ hc₀] at hKc; linarith
      nlinarith
    have h4 := nat_le_two_pow k
    rw [e]
    have : (k : ℝ) * C₁ ^ k ≤ 2 ^ (k + 2) * C₁ ^ (k + 2) := by
      apply mul_le_mul h4 h1 hC1p.le (by positivity)
    have h5 : 0 ≤ 2 ^ (k + 2) * C₁ ^ (k + 2) := by positivity
    nlinarith
  rw [le_div_iff₀ (by positivity)]
  have hBp : 0 < B ^ (k + 2) := by positivity
  have hNlow : (C₁ ^ k)⁻¹ * (w ^ a * w) ≤ Nr := hN
  -- goal: (B^(k+2))⁻¹ * w^a * (k * w) ≤ c₀ * Nr
  calc (B ^ (k + 2))⁻¹ * w ^ a * (k * w) = ((k : ℝ) * C₁ ^ k / B ^ (k + 2)) *
        ((C₁ ^ k)⁻¹ * (w ^ a * w)) := by
          field_simp
    _ ≤ c₀ * ((C₁ ^ k)⁻¹ * (w ^ a * w)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [div_le_iff₀ hBp]; exact hcore
    _ ≤ c₀ * Nr := mul_le_mul_of_nonneg_left hNlow hc₀.le

end MulticlassOmni.Dev.T41
end

section
open MeasureTheory

namespace MulticlassOmni.Dev.T41
open MulticlassOmni.Lipschitz

theorem eOne_mem {k : ℕ} (hk : 0 < k) : eOne k ∈ stdSimplex ℝ (Fin k) := by
  refine ⟨fun y => ?_, MulticlassOmni.Dev.B3.sum_eOne hk⟩
  unfold eOne; split_ifs <;> norm_num

theorem toReal_quarter_add (a b : ENNReal) (ha : a ≤ 1 / 4) (hb : b ≤ 1 / 4) :
    (a + b).toReal ≤ 1 / 2 := by
  have h : a + b ≤ ENNReal.ofReal (1 / 2) := by
    calc a + b ≤ 1 / 4 + 1 / 4 := add_le_add ha hb
      _ = ENNReal.ofReal (1 / 2) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        simp only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
        rw [ENNReal.div_add_div_same, ENNReal.div_eq_div_iff] <;> norm_num
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) h

end MulticlassOmni.Dev.T41

namespace MulticlassOmni.Lipschitz
open MulticlassOmni.Dev.T41 MulticlassOmni.Dev.F43 MulticlassOmni.Dev.B3

theorem chk_theorem_4_1 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ε < c / ((k : ℝ) * Real.log ((k : ℝ) + 1)) →
        ∃ X : Finset (Fin k → ℝ), X.Nonempty ∧ (∀ x ∈ X, x ∈ stdSimplex ℝ (Fin k)) ∧
          ∃ f₁ f₂ : Predictor X, f₁ ≠ f₂ ∧
            ∀ n : ℕ, ∀ A : Learner X n,
              ((∀ D : ↥X × Fin k → ℝ, IsDist D →
                  tailOmniRegret D (outputLaw A D) (lipProperFamily k) {f₁, f₂} ε ≤ 1 / 4) →
                (C * k * ε * Real.log (1 / ε)) ^ (-((k : ℝ) + 2) / 4) ≤ (n : ℝ)) ∧
              ((∀ D : ↥X × Fin k → ℝ, IsDist D →
                  pseudoOmniRegret D (outputLaw A D) (lipProperFamily k) {f₁, f₂} ≤ (ε : EReal)) →
                (C * k * ε * Real.log (1 / ε)) ^ (-((k : ℝ) + 2) / 4) ≤ (n : ℝ)) := by
  obtain ⟨Cpack, ε₂, hCpack, hε₂, hB2⟩ := lemma_B_2
  obtain ⟨C₁, η₃, hC₁, hη₃, hB3⟩ := lemma_B_3 Cpack hCpack
  obtain ⟨c₄, hc₄, h44⟩ := lemma_4_4 Cpack hCpack
  obtain ⟨c₀, _, hc₀, _, hB4, _⟩ := lemma_B_4
  obtain ⟨η₄, hη₄, hB4'⟩ := hB4 Cpack hCpack
  set δ := min η₃ (min η₄ (min (125 * ε₂ / 16) (1 / 32))) with hδ
  have hδ0 : 0 < δ := lt_min hη₃ (lt_min hη₄ (lt_min (by positivity) (by norm_num)))
  have hδ1 : δ ≤ 1 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (by norm_num)))
  refine ⟨min ((δ ^ 2 / 192) ^ 2) c₄, Ccon c₀ C₁, lt_min (by positivity) hc₄,
    Ccon_pos c₀ C₁ hC₁, ?_⟩
  intro k hk ε hε hlt
  have hk0 : 0 < k := by omega
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hkL : 0 < (k : ℝ) * Real.log ((k : ℝ) + 1) :=
    mul_pos (by linarith) (Real.log_pos (by linarith))
  have hlt1 : ε < (δ ^ 2 / 192) ^ 2 / ((k : ℝ) * Real.log ((k : ℝ) + 1)) :=
    lt_of_lt_of_le hlt (div_le_div_of_nonneg_right (min_le_left _ _) hkL.le)
  have hlt4 : ε < c₄ / ((k : ℝ) * Real.log ((k : ℝ) + 1)) :=
    lt_of_lt_of_le hlt (div_le_div_of_nonneg_right (min_le_right _ _) hkL.le)
  obtain ⟨hη0, hηδ⟩ := eta_small δ hδ0 hδ1 k hk ε hε hlt1
  set η := eta k ε with hηdef
  have hη3 : η ≤ η₃ := hηδ.trans (min_le_left _ _)
  have hη4 : η ≤ η₄ := hηδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηε₂ : η ≤ 125 * ε₂ / 16 :=
    hηδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hη32 : η ≤ 1 / 32 :=
    hηδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  -- the packing and the domain
  obtain ⟨X₀, hX₀⟩ := hB2 k hk (16 * η / 125) (by positivity) (by linarith)
  set N := min X₀.card ⌊η ^ (-((k : ℝ) - 2) / 2)⌋₊ with hNdef
  set x : Fin N → Fin k → ℝ :=
    fun i => (X₀.equivFin.symm (Fin.castLE (min_le_left _ _) i) : Fin k → ℝ) with hxdef
  have hxinj : Function.Injective x := by
    intro i j hij
    have := Subtype.ext hij
    have := X₀.equivFin.symm.injective this
    exact Fin.castLE_injective _ this
  have hxmem : ∀ i, x i ∈ X₀ := fun i => (X₀.equivFin.symm _).2
  have hpack : IsSection41Packing Cpack k η x := ⟨X₀, hX₀, hxinj, hxmem, rfl⟩
  obtain ⟨⟨hNlow, -, hN128⟩, -, hqsimp⟩ := hB3 k hk η hη0 hη3 N x hpack
  obtain ⟨-, hB4est⟩ := hB4' k hk η hη0 hη4 N x hpack
  obtain ⟨hlip, hreg⟩ := h44 k hk ε hε hlt4 N x hpack
  have hNpos : 0 < N := by omega
  obtain ⟨-, hsimp, hcoord, hfirst, hsph, hsep⟩ := hX₀
  have hs : ∀ i, x i ∈ stdSimplex ℝ (Fin k) := fun i => hsimp _ (hxmem i)
  have h1 : ∀ i, ∀ y : Fin k, (y : ℕ) = 0 → x i y ≤ 15 / (16 * (k : ℝ)) :=
    fun i y hy => hfirst _ (hxmem i) y hy
  have hsph' : ∀ i, ∑ y, (x i y - vbar k y) ^ 2 = 1 / (256 * (k : ℝ)) :=
    fun i => hsph _ (hxmem i)
  have hsep' : ∀ i j, i ≠ j →
      dot (x i - vbar k) (x j - vbar k) ≤ (1 - 1024 * η) / (256 * (k : ℝ)) := by
    intro i j hij
    have := hsep _ (hxmem i) _ (hxmem j) (fun e => hij (hxinj e))
    have e : 8000 * (16 * η / 125) = 1024 * η := by ring
    rwa [e] at this
  set X : Finset (Fin k → ℝ) := Finset.univ.image x with hXdef
  have hxX : ∀ i, x i ∈ X := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hXsimp : ∀ v ∈ X, v ∈ stdSimplex ℝ (Fin k) := by
    intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
    exact hs i
  let e : Fin N ≃ ↥X := Equiv.ofBijective (fun i => ⟨x i, hxX i⟩) ⟨fun i j h => by
        have h' := congrArg Subtype.val h
        exact hxinj h', fun v => by
        obtain ⟨i, -, hi⟩ := Finset.mem_image.1 v.2
        exact ⟨i, Subtype.ext hi⟩⟩
  refine ⟨X, ⟨x ⟨0, hNpos⟩, hxX _⟩, hXsimp, ?_⟩
  let f₁ : Predictor X := fun _ => ⟨eOne k, eOne_mem hk0⟩
  let f₂ : Predictor X := fun v => ⟨v.1, hXsimp v.1 v.2⟩
  have hf₁ : ∀ i, (f₁ (e i) : Fin k → ℝ) = bench x 1 i := fun i => by simp [bench, f₁]; rfl
  have hf₂ : ∀ i, (f₂ (e i) : Fin k → ℝ) = bench x 2 i := fun i => by simp [bench, f₂]; rfl
  have hne : f₁ ≠ f₂ := by
    intro h
    have h' := congrArg Subtype.val (congrFun h (e ⟨0, hNpos⟩))
    have h2 : eOne k = x ⟨0, hNpos⟩ := h'
    have h3 := congrFun h2 ⟨1, by omega⟩
    have h4 : eOne k ⟨1, by omega⟩ = 0 := by simp [eOne]
    have h5 := (hcoord _ (hxmem ⟨0, hNpos⟩) ⟨1, by omega⟩).1
    have h6 : (0 : ℝ) < 7 / (8 * (k : ℝ)) := by positivity
    linarith
  refine ⟨f₁, f₂, hne, ?_⟩
  intro n A
  -- the reduction to the estimation lower bound
  have hq0 : ∀ (b : Fin 2) i y, 0 ≤ qLip x η b i y := fun b i y => (hqsimp i b).1 y
  have hθm := measurable_thetaHat x η e
  have hDθ : ∀ θ, IsDist (distOf e (qLip x η) θ) :=
    distOf_isDist hNpos e _ (fun b i => hqsimp i b)
  have hu : 0 < (k : ℝ) * ε * Real.log (1 / ε) := by
    have : 0 < Real.sqrt ((k : ℝ) * ε * Real.log (1 / ε)) := by
      have := hη0; rw [hηdef] at this; unfold eta at this; linarith
    exact Real.sqrt_pos.1 this
  have hsmall : ¬ (Ccon c₀ C₁ * k * ε * Real.log (1 / ε)) ^ (-((k : ℝ) + 2) / 4) ≤ (n : ℝ) →
      ∃ θ : Fin N → Fin 2, 1 / 2 <
        (outputLaw A (distOf e (qLip x η) θ) (badSet (thetaHat x η e) θ)).toReal := by
    intro hlt
    push Not at hlt
    have hb := const_bound c₀ C₁ hc₀ hC₁ k hk _ hu (N : ℝ) hNlow
    rw [show Ccon c₀ C₁ * (k * ε * Real.log (1 / ε)) = Ccon c₀ C₁ * k * ε * Real.log (1 / ε) by
      ring] at hb
    have hn : (n : ℝ) ≤ c₀ * N / (k * η ^ 2) := hlt.le.trans hb
    exact exists_bad e (qLip x η) hq0 A hθm
      (hB4est n hn _ (isRandEstimator_estOf e A hθm))
  have H44 : ∀ (i : Fin N) (b : Fin 2) (β : ℕ) (π : Fin N → Fin 2),
      (β = 1 ∨ β = 2) → (π i = 1 → (b : ℕ) = β - 1) →
        ∀ r ∈ stdSimplex ℝ (Fin k),
          24 * ε * (if aSel x η π (Equiv.refl _) r ≠ aSel x η π (Equiv.refl _) (bench x β i)
              then 1 else 0) - ε / 8 ≤
            expect (qLip x η b i)
              (fun y => smoothLoss x η ε π r y - smoothLoss x η ε π (bench x β i) y) :=
    fun i b β π hβ hπ r hr => hreg (Equiv.refl _) i b β π hβ hπ r hr
  have hsum := fun θ p => regret_sum_ge hk hNpos x η ε hη0 hε.le hη32 hs h1 hsph' hsep'
    (Equiv.refl _) H44 e f₁ f₂ hf₁ hf₂ θ p
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  -- on the bad set the two regrets sum to more than `2ε`
  have hbadR : ∀ θ, ∀ p ∈ badSet (thetaHat x η e) θ,
      6 * ε - ε / 4 ≤ popRegret (distOf e (qLip x η) θ) (smoothLoss x η ε (piB θ 1)) p f₁ +
        popRegret (distOf e (qLip x η) θ) (smoothLoss x η ε (piB θ 2)) p f₂ := by
    intro θ p hp
    have := hsum θ p
    have hp' : (N : ℝ) / 4 ≤ (hammingErr (thetaHat x η e p) θ : ℝ) := hp
    have : 6 * ε ≤ 24 * ε / N * (hammingErr (thetaHat x η e p) θ : ℝ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hNr]; nlinarith
    linarith
  have hmemF₁ : f₁ ∈ ({f₁, f₂} : Set (Predictor X)) := by simp
  have hmemF₂ : f₂ ∈ ({f₁, f₂} : Set (Predictor X)) := by simp
  refine ⟨fun htail => ?_, fun hexp => ?_⟩
  · by_contra hcon
    obtain ⟨θ, hθ⟩ := hsmall hcon
    set D := distOf e (qLip x η) θ
    set P := outputLaw A D
    have hT : ∀ β f, f ∈ ({f₁, f₂} : Set (Predictor X)) →
        P {p | ε < popRegret D (smoothLoss x η ε (piB θ β)) p f} ≤ 1 / 4 := by
      intro β f hf
      refine le_trans ?_ (htail D (hDθ θ))
      unfold tailOmniRegret
      exact le_iSup₂_of_le (f := fun ℓ (_ : ℓ ∈ lipProperFamily k) => ⨆ f ∈ ({f₁, f₂} :
        Set (Predictor X)), P {p | ε < popRegret D ℓ p f}) (smoothLoss x η ε (piB θ β))
        (hlip _) (le_iSup₂_of_le (f := fun f (_ : f ∈ ({f₁, f₂} : Set (Predictor X))) =>
          P {p | ε < popRegret D (smoothLoss x η ε (piB θ β)) p f}) f hf le_rfl)
    have hsub : badSet (thetaHat x η e) θ ⊆
        {p | ε < popRegret D (smoothLoss x η ε (piB θ 1)) p f₁} ∪
        {p | ε < popRegret D (smoothLoss x η ε (piB θ 2)) p f₂} := by
      intro p hp
      have := hbadR θ p hp
      by_contra hno
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hno
      linarith [hno.1, hno.2]
    have hfin : P (badSet (thetaHat x η e) θ) ≤
        P {p | ε < popRegret D (smoothLoss x η ε (piB θ 1)) p f₁} +
        P {p | ε < popRegret D (smoothLoss x η ε (piB θ 2)) p f₂} :=
      (measure_mono hsub).trans (measure_union_le _ _)
    have := isProb_outputLaw A D (hDθ θ)
    have h2 := toReal_quarter_add _ _ (hT 1 f₁ hmemF₁) (hT 2 f₂ hmemF₂)
    have h3 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
      hfin
    linarith
  · by_contra hcon
    obtain ⟨θ, hθ⟩ := hsmall hcon
    set D := distOf e (qLip x η) θ
    set P := outputLaw A D
    have hP := isProb_outputLaw A D (hDθ θ)
    have hE : ∀ β f, f ∈ ({f₁, f₂} : Set (Predictor X)) →
        ∫ p, popRegret D (smoothLoss x η ε (piB θ β)) p f ∂P ≤ ε := by
      intro β f hf
      have h := le_trans (?_ : ((∫ p, popRegret D (smoothLoss x η ε (piB θ β)) p f ∂P : ℝ) :
        EReal) ≤ pseudoOmniRegret D P (lipProperFamily k) {f₁, f₂}) (hexp D (hDθ θ))
      · exact EReal.coe_le_coe_iff.1 h
      unfold pseudoOmniRegret
      exact le_iSup₂_of_le (f := fun ℓ (_ : ℓ ∈ lipProperFamily k) => ⨆ f ∈ ({f₁, f₂} :
        Set (Predictor X)), ((∫ p, popRegret D ℓ p f ∂P : ℝ) : EReal))
        (smoothLoss x η ε (piB θ β)) (hlip _)
        (le_iSup₂_of_le (f := fun f (_ : f ∈ ({f₁, f₂} : Set (Predictor X))) =>
          ((∫ p, popRegret D (smoothLoss x η ε (piB θ β)) p f ∂P : ℝ) : EReal)) f hf le_rfl)
    have hi1 := integrable_popRegret (hlip (piB θ 1)) A (hDθ θ) f₁
    have hi2 := integrable_popRegret (hlip (piB θ 2)) A (hDθ θ) f₂
    have hbm : MeasurableSet (badSet (thetaHat x η e) θ) :=
      measurableSet_fiber hθm {t | (N : ℝ) / 4 ≤ (hammingErr t θ : ℝ)}
    have hig : Integrable (fun p => (badSet (thetaHat x η e) θ).indicator
        (fun _ => 6 * ε) p - ε / 4) P :=
      ((integrable_const _).indicator hbm).sub (integrable_const _)
    have hmono : ∫ p, ((badSet (thetaHat x η e) θ).indicator (fun _ => 6 * ε) p - ε / 4) ∂P ≤
        ∫ p, (popRegret D (smoothLoss x η ε (piB θ 1)) p f₁ +
          popRegret D (smoothLoss x η ε (piB θ 2)) p f₂) ∂P := by
      refine integral_mono hig (hi1.add hi2) (fun p => ?_)
      by_cases hp : p ∈ badSet (thetaHat x η e) θ
      · simp only [Set.indicator_of_mem hp]
        have := hbadR θ p hp
        linarith
      · simp only [Set.indicator_of_notMem hp]
        have h := hsum θ p
        have : 0 ≤ 24 * ε / N * (hammingErr (thetaHat x η e p) θ : ℝ) := by positivity
        linarith
    rw [integral_add hi1 hi2, integral_sub ((integrable_const _).indicator hbm)
      (integrable_const _), integral_indicator_const _ hbm, integral_const] at hmono
    simp only [probReal_univ, smul_eq_mul, one_mul] at hmono
    have e1 := hE 1 f₁ hmemF₁
    have e2 := hE 2 f₂ hmemF₂
    have hreal : P.real (badSet (thetaHat x η e) θ) =
        (P (badSet (thetaHat x η e) θ)).toReal := rfl
    rw [hreal] at hmono
    nlinarith

end MulticlassOmni.Lipschitz
end

theorem solution : type_of% @MulticlassOmni.Lipschitz.chk_theorem_4_1 := @MulticlassOmni.Lipschitz.chk_theorem_4_1
