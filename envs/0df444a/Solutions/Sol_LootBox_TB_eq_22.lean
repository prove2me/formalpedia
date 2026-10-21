-- Prove2me | solution 1 for LootBox.TB.eq_22
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:00:09.137148+00:00
-- url     : https://prove2.me/submissions/1fcda126-f762-47b7-ba5a-de2335edfd35

import Mathlib
import Definitions.Def_LootBox_TB_Setting

set_option autoImplicit false

open LootBox.TB MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

lemma lbtb_fp_attained (w : ℕ → ℝ) (t : ℝ) (j : ℕ) (h : firstPassage w t = (j : ℕ∞)) :
    1 ≤ j ∧ t ≤ ∑ i ∈ Finset.range j, w i := by
  classical
  unfold firstPassage at h
  by_cases hs : ∃ k : ℕ, 1 ≤ k ∧ t ≤ ∑ i ∈ Finset.range k, w i
  · have key : (⨅ (k : ℕ) (_ : 1 ≤ k ∧ t ≤ ∑ i ∈ Finset.range k, w i), (k : ℕ∞)) =
        (Nat.find hs : ℕ∞) := by
      apply le_antisymm
      · exact iInf₂_le (Nat.find hs) (Nat.find_spec hs)
      · refine le_iInf₂ fun k hk => ?_
        exact_mod_cast Nat.find_min' hs hk
    rw [key] at h
    have : Nat.find hs = j := by exact_mod_cast h
    rw [← this]
    exact Nat.find_spec hs
  · push_neg at hs
    have : (⨅ (k : ℕ) (_ : 1 ≤ k ∧ t ≤ ∑ i ∈ Finset.range k, w i), (k : ℕ∞)) = ⊤ := by
      refine iInf₂_eq_top.mpr fun k hk => ?_
      exact absurd hk.2 (not_le.mpr (hs k hk.1))
    rw [this] at h
    exact absurd h.symm (ENat.coe_ne_top j)

theorem solution (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ValLaw F) (hμ : 0 < mean F)
    (N : ℕ) [NeZero N] (p : ℝ) (hp : 0 < p) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    walkLaw F {w | ∃ j : ℕ, firstPassage w ((N : ℝ) * p) = j ∧
        (j : ℝ) ≤ (1 - ε) * N * p / mean F} ≤
      ENNReal.ofReal (var F / (ε ^ 2 / (1 - ε) * N * p * mean F)) := by
  classical
  set μ := mean F with hμdef
  set v := var F with hvdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hNp : 0 < (N : ℝ) * p := mul_pos hNpos hp
  set W := walkLaw F with hW
  have hWdef : W = Measure.infinitePi fun _ : ℕ => F := rfl
  haveI : IsProbabilityMeasure W := by rw [hWdef]; infer_instance
  -- coordinate facts
  have hmp : ∀ i : ℕ, MeasurePreserving (fun w : ℕ → ℝ => w i) W F := fun i => by
    rw [hWdef]; exact measurePreserving_eval_infinitePi (fun _ : ℕ => F) i
  have hmem : ∀ i : ℕ, MemLp (fun w : ℕ → ℝ => w i) 2 W := fun i =>
    (hF.sq_int).comp_measurePreserving (hmp i)
  have hnonneg : ∀ᵐ w ∂W, ∀ i, 0 ≤ w i := by
    rw [ae_all_iff]
    intro i
    have h0 : W {w | w i < 0} = 0 := by
      have := (hmp i).measure_preimage (s := Set.Iio 0) measurableSet_Iio.nullMeasurableSet
      simpa [Set.preimage, hF.nonneg] using this
    rw [ae_iff]
    simpa using h0
  have hcomp : ∀ (g : ℝ → ℝ), Continuous g → ∀ i : ℕ, ∫ w, g (w i) ∂W = ∫ x, g x ∂F := by
    intro g hg i
    have h1 : ∫ x, g x ∂(W.map (fun w : ℕ → ℝ => w i)) = ∫ w, g (w i) ∂W :=
      integral_map (hmp i).measurable.aemeasurable hg.aestronglyMeasurable
    rw [← h1, (hmp i).map_eq]
  have hmean : ∀ i : ℕ, ∫ w, w i ∂W = μ := fun i => hcomp (fun x => x) continuous_id i
  have hvar : ∀ i : ℕ, variance (fun w : ℕ → ℝ => w i) W = v := fun i => by
    rw [variance_eq_integral (hmp i).measurable.aemeasurable]
    have h2 : ∫ w, w i ∂W = μ := hmean i
    simp only [h2]
    exact hcomp (fun x => (x - μ) ^ 2) (by fun_prop) i
  have hv0 : 0 ≤ v := integral_nonneg fun x => sq_nonneg _
  have hindep : iIndepFun (fun (i : ℕ) (w : ℕ → ℝ) => w i) W := by
    rw [hWdef]
    exact iIndepFun_infinitePi (P := fun _ : ℕ => F) (X := fun _ x => x) (fun _ => measurable_id)
  -- partial sums
  have hSmem : ∀ m : ℕ, MemLp (fun w : ℕ → ℝ => ∑ i ∈ Finset.range m, w i) 2 W := fun m => by
    have := memLp_finsetSum (Finset.range m) (fun i _ => hmem i)
    simpa using this
  have hSmean : ∀ m : ℕ, ∫ w, ∑ i ∈ Finset.range m, w i ∂W = m * μ := fun m => by
    rw [integral_finset_sum _ (fun i _ => (hmem i).integrable (by norm_num))]
    simp [hmean]
  have hSvar : ∀ m : ℕ, variance (fun w : ℕ → ℝ => ∑ i ∈ Finset.range m, w i) W = m * v := fun m => by
    have h := IndepFun.variance_sum (μ := W) (X := fun (i : ℕ) (w : ℕ → ℝ) => w i)
      (s := Finset.range m) (fun i _ => hmem i)
      (fun i _ j _ hij => hindep.indepFun hij)
    have e : (∑ i ∈ Finset.range m, fun w : ℕ → ℝ => w i) = fun w => ∑ i ∈ Finset.range m, w i := by
      ext w; simp
    rw [e] at h
    rw [h]; simp [hvar]
  -- the index bound
  set x : ℝ := (1 - ε) * N * p / μ with hx
  have hx0 : 0 ≤ x := by
    have : 0 < 1 - ε := by linarith
    positivity
  set m : ℕ := ⌊x⌋₊ with hm
  have hmx : (m : ℝ) ≤ x := Nat.floor_le hx0
  have hmμ : (m : ℝ) * μ ≤ (1 - ε) * N * p := by
    have := mul_le_mul_of_nonneg_right hmx hμ.le
    rwa [hx, div_mul_cancel₀ _ hμ.ne'] at this
  set c : ℝ := N * p - m * μ with hc
  have hcpos : ε * (N * p) ≤ c := by rw [hc]; nlinarith
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hcpos
  -- event inclusion (a.e.)
  have hsub : {w : ℕ → ℝ | ∃ j : ℕ, firstPassage w ((N : ℝ) * p) = j ∧ (j : ℝ) ≤ x} ≤ᵐ[W]
      {w : ℕ → ℝ | c ≤ |(∑ i ∈ Finset.range m, w i) - ∫ w', ∑ i ∈ Finset.range m, w' i ∂W|} := by
    filter_upwards [hnonneg] with w hw
    rintro ⟨j, hj, hjx⟩
    obtain ⟨hj1, hjS⟩ := lbtb_fp_attained w _ j hj
    have hjm : j ≤ m := Nat.le_floor hjx
    have hmono : ∑ i ∈ Finset.range j, w i ≤ ∑ i ∈ Finset.range m, w i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hjm) (fun i _ _ => hw i)
    show c ≤ _
    rw [hSmean m]
    refine le_trans ?_ (le_abs_self _)
    rw [hc]; linarith
  have hcheb : W {w : ℕ → ℝ | c ≤ |(∑ i ∈ Finset.range m, w i) - ∫ w', ∑ i ∈ Finset.range m, w' i ∂W|} ≤
      ENNReal.ofReal (variance (fun w : ℕ → ℝ => ∑ i ∈ Finset.range m, w i) W / c ^ 2) :=
    meas_ge_le_variance_div_sq (hSmem m) hc0
  refine (measure_mono_ae hsub).trans (hcheb.trans ?_)
  rw [hSvar m]
  apply ENNReal.ofReal_le_ofReal
  have hε' : 0 < 1 - ε := by linarith
  have hNp' : 0 < (N : ℝ) * p := hNp
  have hcsq : (ε * (N * p)) ^ 2 ≤ c ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) hcpos
  calc (m : ℝ) * v / c ^ 2 ≤ x * v / (ε * (N * p)) ^ 2 := by
        apply div_le_div₀ (mul_nonneg hx0 hv0) (mul_le_mul_of_nonneg_right hmx hv0)
          (by positivity) hcsq
    _ = v / (ε ^ 2 / (1 - ε) * N * p * μ) := by
        rw [hx]; field_simp
