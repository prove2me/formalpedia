-- Prove2me | solution 1 for LootBox.TB.eq_16
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:11:28.741191+00:00
-- url     : https://prove2.me/submissions/e8b3118e-16f0-4a6e-b157-aff4bdffb16d

import Mathlib
import Definitions.Def_LootBox_TB_Setting

set_option autoImplicit false

open LootBox.TB MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

lemma lbtb_sum_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Measure ℝ) {ι : Type*} (X : ι → Ω → ℝ) (hX : iIndepFun X P)
    (hm : ∀ i, Measurable (X i)) (hlaw : ∀ i, P.map (X i) = F) (k : ℕ) (g : Fin k → ι)
    (hg : Function.Injective g) (c : ℝ) :
    P {ω | c ≤ ∑ j, X (g j) ω} = (Measure.pi fun _ : Fin k => F) {y | c ≤ ∑ j, y j} := by
  have h := (iIndepFun_iff_map_fun_eq_pi_map (fun j => (hm (g j)).aemeasurable)).1
    (hX.precomp hg)
  simp only [hlaw] at h
  have hmeas : Measurable (fun (ω : Ω) (j : Fin k) => X (g j) ω) :=
    measurable_pi_lambda _ (fun j => hm (g j))
  have hs : MeasurableSet {y : Fin k → ℝ | c ≤ ∑ j, y j} :=
    measurableSet_le measurable_const (by fun_prop)
  rw [← h, Measure.map_apply hmeas hs]
  rfl

lemma lbtb_pi_law (F : Measure ℝ) [IsProbabilityMeasure F] (N : ℕ) (U : Finset (Fin N)) (c : ℝ) :
    (Measure.pi fun _ : Fin N => F) {v | c ≤ ∑ i ∈ U, v i} =
      (Measure.pi fun _ : Fin U.card => F) {y | c ≤ ∑ j, y j} := by
  have hX : iIndepFun (fun (i : Fin N) (v : Fin N → ℝ) => v i) (Measure.pi fun _ : Fin N => F) :=
    iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id)
  have := lbtb_sum_law (Measure.pi fun _ : Fin N => F) F (fun (i : Fin N) (v : Fin N → ℝ) => v i)
    hX (fun i => measurable_pi_apply i) (fun i => by
      exact (measurePreserving_eval (fun _ : Fin N => F) i).map_eq) U.card
    (U.orderEmbOfFin rfl) (U.orderEmbOfFin rfl).injective c
  rw [← this]
  congr 1
  ext v
  simp only [Set.mem_setOf_eq]
  rw [← Finset.sum_image (f := fun i => v i) (g := (U.orderEmbOfFin rfl)) (s := Finset.univ)
    (fun a _ b _ h => (U.orderEmbOfFin rfl).injective h)]
  congr! 3
  ext i; simp

lemma lbtb_walk_law (F : Measure ℝ) [IsProbabilityMeasure F] (k : ℕ) (c : ℝ) :
    walkLaw F {w | c ≤ ∑ i ∈ Finset.range k, w i} =
      (Measure.pi fun _ : Fin k => F) {y | c ≤ ∑ j, y j} := by
  have hX : iIndepFun (fun (i : ℕ) (w : ℕ → ℝ) => w i) (walkLaw F) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => F) (X := fun _ x => x) (fun _ => measurable_id)
  haveI : IsProbabilityMeasure (walkLaw F) := by unfold walkLaw; infer_instance
  have := lbtb_sum_law (walkLaw F) F (fun (i : ℕ) (w : ℕ → ℝ) => w i)
    hX (fun i => measurable_pi_apply i) (fun i => by
      exact Measure.infinitePi_map_eval (fun _ : ℕ => F) i) k (fun j => (j : ℕ)) Fin.val_injective c
  rw [← this]
  congr 1
  ext w
  simp only [Set.mem_setOf_eq]
  rw [Finset.sum_range]

noncomputable abbrev lbν (N : ℕ) [NeZero N] : Measure (Fin N) :=
  (PMF.uniformOfFintype (Fin N)).toMeasure

noncomputable abbrev lbB (N : ℕ) [NeZero N] : Measure (ℕ → Fin N) :=
  Measure.infinitePi fun _ : ℕ => lbν N

instance lbν_prob (N : ℕ) [NeZero N] : IsProbabilityMeasure (lbν N) := by
  unfold lbν; infer_instance

lemma lbν_apply (N : ℕ) [NeZero N] (V : Finset (Fin N)) : lbν N (V : Set (Fin N)) = (V.card : ℝ≥0∞) / N := by
  unfold lbν
  rw [PMF.toMeasure_apply_finset]
  simp [PMF.uniformOfFintype_apply, div_eq_mul_inv, mul_comm]

lemma lbtb_split (N : ℕ) [NeZero N] (s : ℕ) (E : Set (↥(Finset.range s) → Fin N))
    (V : (↥(Finset.range s) → Fin N) → Finset (Fin N)) :
    lbB N {d | (fun i : ↥(Finset.range s) => d i) ∈ E ∧ d s ∈ V (fun i : ↥(Finset.range s) => d i)} =
      ∫⁻ a, E.indicator (fun a => ((V a).card : ℝ≥0∞) / N) a
        ∂((lbB N).map (fun d (i : ↥(Finset.range s)) => d i)) := by
  have hX : iIndepFun (fun (i : ℕ) (d : ℕ → Fin N) => d i) (lbB N) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => lbν N) (X := fun _ x => x) (fun _ => measurable_id)
  have hind := hX.indepFun_finset (Finset.range s) {s} (by simp) (fun i => measurable_pi_apply i)
  have hf : Measurable (fun (d : ℕ → Fin N) (i : ↥(Finset.range s)) => d i) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have hg : Measurable (fun d : ℕ → Fin N => d s) := measurable_pi_apply s
  have hind2 : IndepFun (fun (d : ℕ → Fin N) (i : ↥(Finset.range s)) => d i) (fun d : ℕ → Fin N => d s) (lbB N) := by
    have := hind.comp measurable_id (measurable_pi_apply (⟨s, Finset.mem_singleton_self s⟩ : ↥({s} : Finset ℕ)))
    exact this
  have hjoint := (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).1 hind2
  have hgmap : (lbB N).map (fun d : ℕ → Fin N => d s) = lbν N :=
    Measure.infinitePi_map_eval (fun _ : ℕ => lbν N) s
  rw [hgmap] at hjoint
  set S : Set ((↥(Finset.range s) → Fin N) × Fin N) := {p | p.1 ∈ E ∧ p.2 ∈ V p.1} with hS
  have hSm : MeasurableSet S := (Set.toFinite S).measurableSet
  have hmeas2 : Measurable (fun d : ℕ → Fin N => ((fun i : ↥(Finset.range s) => d i), d s)) :=
    hf.prodMk hg
  have : {d : ℕ → Fin N | (fun i : ↥(Finset.range s) => d i) ∈ E ∧ d s ∈ V (fun i : ↥(Finset.range s) => d i)} =
      (fun d : ℕ → Fin N => ((fun i : ↥(Finset.range s) => d i), d s)) ⁻¹' S := rfl
  rw [this, ← Measure.map_apply hmeas2 hSm, hjoint, Measure.prod_apply hSm]
  congr 1
  ext a
  by_cases ha : a ∈ E
  · have : Prod.mk a ⁻¹' S = ((V a : Finset (Fin N)) : Set (Fin N)) := by
      ext x; simp [hS, ha]
    rw [this, lbν_apply]; simp [ha]
  · have : Prod.mk a ⁻¹' S = ∅ := by
      ext x; simp [hS, ha]
    rw [this]; simp [ha]

/-- number of not-yet-owned items after `s` draws -/
def lbU {N : ℕ} (s : ℕ) (d : ℕ → Fin N) : ℕ := (((Finset.range s).image d)ᶜ).card

noncomputable def lbP (N : ℕ) [NeZero N] (s k : ℕ) : ℝ≥0∞ := lbB N {d | lbU s d = k}

def lbC {N : ℕ} {s : ℕ} (a : ↥(Finset.range s) → Fin N) : ℕ := ((Finset.univ.image a)ᶜ).card

lemma lbU_eq {N : ℕ} (s : ℕ) (d : ℕ → Fin N) :
    lbU s d = lbC (fun i : ↥(Finset.range s) => d i) := by
  unfold lbU lbC
  congr 2
  ext x; simp

lemma lbU_succ {N : ℕ} (s : ℕ) (d : ℕ → Fin N) :
    lbU (s + 1) d = if d s ∈ (Finset.range s).image d then lbU s d else lbU s d - 1 := by
  unfold lbU
  rw [Finset.range_add_one, Finset.image_insert]
  split_ifs with h
  · rw [Finset.insert_eq_of_mem h]
  · rw [Finset.compl_insert, Finset.card_erase_of_mem (by simpa using h)]

lemma lbU_le {N : ℕ} (s : ℕ) (d : ℕ → Fin N) : lbU s d ≤ N := by
  unfold lbU
  calc _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ _
    _ = N := by simp

lemma lbU_pos {N : ℕ} (s : ℕ) (d : ℕ → Fin N) (h : d s ∉ (Finset.range s).image d) : 1 ≤ lbU s d := by
  unfold lbU
  exact Finset.card_pos.mpr ⟨d s, by simpa using h⟩

lemma lbU_zero {N : ℕ} (d : ℕ → Fin N) : lbU 0 d = N := by
  simp [lbU]

lemma lbP_zero (N : ℕ) [NeZero N] (k : ℕ) : lbP N 0 k = if k = N then 1 else 0 := by
  unfold lbP
  by_cases hk : k = N
  · subst hk; simp [lbU_zero]
  · simp [lbU_zero, Ne.symm hk, hk]

lemma lbP_gt (N : ℕ) [NeZero N] (s k : ℕ) (hk : N < k) : lbP N s k = 0 := by
  unfold lbP
  have : {d : ℕ → Fin N | lbU s d = k} = ∅ := by
    ext d; simp only [Set.mem_empty_iff_false, iff_false]
    intro h; have h' : lbU s d = k := h; have := lbU_le s d; omega
  rw [this]; simp

lemma lbtb_meas_split (N : ℕ) [NeZero N] (s : ℕ) (E : Set (↥(Finset.range s) → Fin N))
    (V : (↥(Finset.range s) → Fin N) → Finset (Fin N)) :
    MeasurableSet {d : ℕ → Fin N | (fun i : ↥(Finset.range s) => d i) ∈ E ∧ d s ∈ V (fun i : ↥(Finset.range s) => d i)} := by
  have hf : Measurable (fun (d : ℕ → Fin N) (i : ↥(Finset.range s)) => d i) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have hg : Measurable (fun d : ℕ → Fin N => d s) := measurable_pi_apply s
  have hmeas2 : Measurable (fun d : ℕ → Fin N => ((fun i : ↥(Finset.range s) => d i), d s)) :=
    hf.prodMk hg
  have hSm : MeasurableSet {p : (↥(Finset.range s) → Fin N) × Fin N | p.1 ∈ E ∧ p.2 ∈ V p.1} :=
    (Set.toFinite _).measurableSet
  exact hmeas2 hSm

lemma lbP_succ (N : ℕ) [NeZero N] (s k : ℕ) (hk : k ≤ N) :
    lbP N (s + 1) k = ((N - k : ℕ) : ℝ≥0∞) / N * lbP N s k + ((k + 1 : ℕ) : ℝ≥0∞) / N * lbP N s (k + 1) := by
  classical
  set E1 : Set (↥(Finset.range s) → Fin N) := {a | lbC a = k} with hE1
  set E2 : Set (↥(Finset.range s) → Fin N) := {a | lbC a = k + 1} with hE2
  set V1 : (↥(Finset.range s) → Fin N) → Finset (Fin N) := fun a => Finset.univ.image a with hV1
  set V2 : (↥(Finset.range s) → Fin N) → Finset (Fin N) := fun a => (Finset.univ.image a)ᶜ with hV2
  have hset : {d : ℕ → Fin N | lbU (s + 1) d = k} =
      {d | (fun i : ↥(Finset.range s) => d i) ∈ E1 ∧ d s ∈ V1 (fun i : ↥(Finset.range s) => d i)} ∪
      {d | (fun i : ↥(Finset.range s) => d i) ∈ E2 ∧ d s ∈ V2 (fun i : ↥(Finset.range s) => d i)} := by
    ext d
    have hv1 : V1 (fun i : ↥(Finset.range s) => d i) = (Finset.range s).image d := by
      simp only [hV1]; ext x; simp
    have hv2 : V2 (fun i : ↥(Finset.range s) => d i) = ((Finset.range s).image d)ᶜ := by
      simp only [hV2]; rw [← hv1]
    simp only [Set.mem_setOf_eq, Set.mem_union, hE1, hE2, ← lbU_eq, hv1, hv2, Finset.mem_compl]
    rw [lbU_succ]
    by_cases hmem : d s ∈ (Finset.range s).image d
    · simp [hmem]
    · have := lbU_pos s d hmem
      simp [hmem]
      omega
  have hdisj : Disjoint {d : ℕ → Fin N | (fun i : ↥(Finset.range s) => d i) ∈ E1 ∧ d s ∈ V1 (fun i : ↥(Finset.range s) => d i)}
      {d | (fun i : ↥(Finset.range s) => d i) ∈ E2 ∧ d s ∈ V2 (fun i : ↥(Finset.range s) => d i)} := by
    rw [Set.disjoint_left]
    rintro d ⟨-, h1⟩ ⟨-, h2⟩
    simp only [hV1, hV2, Finset.mem_compl] at h1 h2
    exact h2 h1
  unfold lbP
  rw [hset, measure_union hdisj (lbtb_meas_split N s E2 V2), lbtb_split, lbtb_split]
  have hmf : Measurable (fun (d : ℕ → Fin N) (i : ↥(Finset.range s)) => d i) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have hEm : ∀ e : Set (↥(Finset.range s) → Fin N), MeasurableSet e := fun e => (Set.toFinite e).measurableSet
  have key : ∀ (E : Set (↥(Finset.range s) → Fin N)) (c : ℝ≥0∞) (kk : ℕ) (hE : E = {a | lbC a = kk})
      (V : (↥(Finset.range s) → Fin N) → Finset (Fin N))
      (hV : ∀ a ∈ E, ((V a).card : ℝ≥0∞) / N = c),
      ∫⁻ a, E.indicator (fun a => ((V a).card : ℝ≥0∞) / N) a
        ∂((lbB N).map (fun d (i : ↥(Finset.range s)) => d i)) = c * lbB N {d | lbU s d = kk} := by
    intro E c kk hE V hV
    have h1 : ∫⁻ a, E.indicator (fun a => ((V a).card : ℝ≥0∞) / N) a
        ∂((lbB N).map (fun d (i : ↥(Finset.range s)) => d i)) =
        ∫⁻ a, E.indicator (fun _ => c) a ∂((lbB N).map (fun d (i : ↥(Finset.range s)) => d i)) := by
      refine lintegral_congr fun a => ?_
      by_cases ha : a ∈ E
      · simp [Set.indicator_of_mem ha, hV a ha]
      · simp [Set.indicator_of_notMem ha]
    rw [h1, lintegral_indicator_const (hEm E), Measure.map_apply hmf (hEm E)]
    congr 1
    congr 1
    ext d
    simp [hE, lbU_eq]
  have hc1 : ∀ a ∈ E1, ((V1 a).card : ℝ≥0∞) / N = ((N - k : ℕ) : ℝ≥0∞) / N := by
    intro a ha
    congr 2
    have : (V1 a).card + ((V1 a)ᶜ).card = N := by
      rw [Finset.card_add_card_compl]; simp
    have h2 : ((V1 a)ᶜ).card = k := ha
    omega
  have hc2 : ∀ a ∈ E2, ((V2 a).card : ℝ≥0∞) / N = ((k + 1 : ℕ) : ℝ≥0∞) / N := by
    intro a ha
    have h2 : ((V1 a)ᶜ).card = k + 1 := ha
    simp only [hV2]
    rw [h2]
  rw [key E1 _ k hE1 V1 hc1, key E2 _ (k+1) hE2 V2 hc2]

lemma lbtb_cast_div (n m : ℕ) (hm : 0 < m) : ((n : ℝ≥0∞) / m) = ENNReal.ofReal ((n : ℝ) / m) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hm)]; simp

lemma lbtb_arith1 (N k : ℕ) (hk1 : 1 ≤ k) (hkN : k < N) :
    ((N - k : ℕ) : ℝ≥0∞) / N * ((N : ℝ≥0∞) / k) + ((k + 1 : ℕ) : ℝ≥0∞) / N * ((N : ℝ≥0∞) / (k + 1 : ℕ)) =
      (N : ℝ≥0∞) / k := by
  have hN : 0 < N := by omega
  have hk : 0 < k := by omega
  rw [lbtb_cast_div _ _ hN, lbtb_cast_div N k hk, lbtb_cast_div _ _ hN, lbtb_cast_div N (k+1) (by omega)]
  have h1 : (0 : ℝ) ≤ ((N - k : ℕ) : ℝ) / N := by positivity
  have h2 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) / N := by positivity
  rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  have hNk : ((N - k : ℕ) : ℝ) = (N : ℝ) - k := by
    rw [Nat.cast_sub hkN.le]
  rw [hNk]
  push_cast
  have : (0 : ℝ) < N := by exact_mod_cast hN
  have : (0 : ℝ) < k := by exact_mod_cast hk
  field_simp
  ring

noncomputable def lbA (N : ℕ) [NeZero N] (S k : ℕ) : ℝ≥0∞ := ∑ s ∈ Finset.range S, lbP N s k

lemma lbA_succ (N : ℕ) [NeZero N] (S k : ℕ) (hk : k ≤ N) :
    lbA N (S + 1) k = (if k = N then 1 else 0) + ((N - k : ℕ) : ℝ≥0∞) / N * lbA N S k +
      ((k + 1 : ℕ) : ℝ≥0∞) / N * lbA N S (k + 1) := by
  unfold lbA
  rw [Finset.sum_range_succ', lbP_zero]
  simp only [lbP_succ N _ k hk, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

lemma lbA_zero (N : ℕ) [NeZero N] (k : ℕ) : lbA N 0 k = 0 := by simp [lbA]

lemma lbA_gt (N : ℕ) [NeZero N] (S k : ℕ) (hk : N < k) : lbA N S k = 0 := by
  simp [lbA, lbP_gt N _ k hk]

lemma lbA_le (N : ℕ) [NeZero N] : ∀ m k : ℕ, N - k = m → 1 ≤ k → k ≤ N → ∀ S, lbA N S k ≤ (N : ℝ≥0∞) / k := by
  intro m
  induction m with
  | zero =>
    intro k hm hk1 hkN S
    have hkN' : k = N := by omega
    induction S with
    | zero => simp [lbA_zero]
    | succ S ih =>
      rw [lbA_succ N S k hkN, lbA_gt N S (k + 1) (by omega)]
      have h1 : (N : ℝ≥0∞) / k = 1 := by
        rw [hkN']; exact ENNReal.div_self (by exact_mod_cast (by omega : N ≠ 0)) (ENNReal.natCast_ne_top N)
      rw [h1]
      simp [hkN']
  | succ m ihm =>
    intro k hm hk1 hkN S
    have hkN' : k < N := by omega
    have hup := ihm (k + 1) (by omega) (by omega) (by omega)
    induction S with
    | zero => simp [lbA_zero]
    | succ S ih =>
      rw [lbA_succ N S k hkN]
      simp only [show k ≠ N by omega, if_false, zero_add]
      calc ((N - k : ℕ) : ℝ≥0∞) / N * lbA N S k + ((k + 1 : ℕ) : ℝ≥0∞) / N * lbA N S (k + 1)
          ≤ ((N - k : ℕ) : ℝ≥0∞) / N * ((N : ℝ≥0∞) / k) + ((k + 1 : ℕ) : ℝ≥0∞) / N * ((N : ℝ≥0∞) / (k + 1 : ℕ)) := by
            gcongr
            · exact hup S
        _ = (N : ℝ≥0∞) / k := lbtb_arith1 N k hk1 hkN'

lemma lbtb_solve (N k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) (x : ℝ≥0∞) (hx : x ≠ ⊤)
    (h : x = 1 + ((N - k : ℕ) : ℝ≥0∞) / N * x) : x = (N : ℝ≥0∞) / k := by
  have hN : 0 < N := by omega
  have hk : 0 < k := by omega
  have hw : ((N - k : ℕ) : ℝ≥0∞) / N ≠ ⊤ := by
    rw [lbtb_cast_div _ _ hN]; exact ENNReal.ofReal_ne_top
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add ENNReal.one_ne_top (ENNReal.mul_ne_top hw hx), ENNReal.toReal_mul,
    lbtb_cast_div _ _ hN, ENNReal.toReal_ofReal (by positivity)] at h'
  simp only [ENNReal.toReal_one] at h'
  have hNk : ((N - k : ℕ) : ℝ) = (N : ℝ) - k := by rw [Nat.cast_sub hkN]
  rw [hNk] at h'
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hxr : x.toReal = (N : ℝ) / k := by
    field_simp at h' ⊢
    nlinarith
  rw [← ENNReal.ofReal_toReal hx, hxr, lbtb_cast_div _ _ hk]

noncomputable def lbT (N : ℕ) [NeZero N] (k : ℕ) : ℝ≥0∞ := ∑' s, lbP N s k

lemma lbT_succ (N : ℕ) [NeZero N] (k : ℕ) (hk : k ≤ N) :
    lbT N k = (if k = N then 1 else 0) + ((N - k : ℕ) : ℝ≥0∞) / N * lbT N k +
      ((k + 1 : ℕ) : ℝ≥0∞) / N * lbT N (k + 1) := by
  have e1 : lbT N k = lbP N 0 k + ∑' s, lbP N (s + 1) k := tsum_eq_zero_add' ENNReal.summable
  have e2 : (∑' s, lbP N (s + 1) k) = ((N - k : ℕ) : ℝ≥0∞) / N * lbT N k +
      ((k + 1 : ℕ) : ℝ≥0∞) / N * lbT N (k + 1) := by
    simp only [lbP_succ N _ k hk]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    rfl
  refine e1.trans ?_
  rw [e2, lbP_zero, add_assoc]

lemma lbT_le (N : ℕ) [NeZero N] (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) : lbT N k ≤ (N : ℝ≥0∞) / k := by
  unfold lbT
  rw [ENNReal.tsum_eq_iSup_nat]
  exact iSup_le fun S => lbA_le N (N - k) k rfl hk1 hkN S

lemma lbT_eq (N : ℕ) [NeZero N] : ∀ m k : ℕ, N - k = m → 1 ≤ k → k ≤ N → lbT N k = (N : ℝ≥0∞) / k := by
  intro m
  induction m with
  | zero =>
    intro k hm hk1 hkN
    have hkN' : k = N := by omega
    have h := lbT_succ N k hkN
    have h0 : lbT N (k + 1) = 0 := by simp [lbT, lbP_gt N _ (k + 1) (by omega)]
    rw [h0, mul_zero, add_zero] at h
    have hfin : lbT N k ≠ ⊤ := ne_top_of_le_ne_top (by
      exact ENNReal.div_ne_top (ENNReal.natCast_ne_top N) (by exact_mod_cast (by omega : k ≠ 0))) (lbT_le N k hk1 hkN)
    exact lbtb_solve N k hk1 hkN _ hfin (by simpa [hkN'] using h)
  | succ m ihm =>
    intro k hm hk1 hkN
    have hkN' : k < N := by omega
    have h := lbT_succ N k hkN
    have h1 := ihm (k + 1) (by omega) (by omega) (by omega)
    rw [h1] at h
    have hk1' : ((k + 1 : ℕ) : ℝ≥0∞) / N * ((N : ℝ≥0∞) / (k + 1 : ℕ)) = 1 := by
      rw [lbtb_cast_div _ _ (by omega : 0 < N), lbtb_cast_div N (k + 1) (by omega), ← ENNReal.ofReal_mul (by positivity)]
      have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      have : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k + 1)
      rw [show (((k + 1 : ℕ) : ℝ) / N * ((N : ℝ) / ((k + 1 : ℕ) : ℝ))) = 1 by field_simp]
      simp
    rw [hk1', if_neg (by omega), zero_add] at h
    have hfin : lbT N k ≠ ⊤ := ne_top_of_le_ne_top (by
      exact ENNReal.div_ne_top (ENNReal.natCast_ne_top N) (by exact_mod_cast (by omega : k ≠ 0))) (lbT_le N k hk1 hkN)
    exact lbtb_solve N k hk1 hkN _ hfin (h.trans (add_comm _ _))

lemma lbtb_enat_tsum (T : ℕ∞) : (T : ℝ≥0∞) = ∑' s : ℕ, if (s : ℕ∞) < T then (1 : ℝ≥0∞) else 0 := by
  induction T using ENat.recTopCoe with
  | top =>
    simp only [ENat.toENNReal_top]
    have : ∀ s : ℕ, ((s : ℕ∞) < ⊤) := fun s => ENat.natCast_lt_top s
    simp only [this, if_true]
    rw [ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero]
  | coe n =>
    rw [tsum_eq_sum (s := Finset.range n)]
    · simp only [Nat.cast_lt]
      rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞)) (fun s hs => by simp at hs; simp [hs])]
      simp
    · intro s hs
      simp only [Finset.mem_range, not_lt] at hs
      simp [not_lt.mpr hs]

lemma lbtb_lt_purchases {N : ℕ} (p : ℝ) (v : Fin N → ℝ) (d : ℕ → Fin N) (hv : ∀ i, 0 ≤ v i) (s : ℕ) :
    ((s : ℕ∞) < purchases p v d) ↔ 0 ≤ util p v d s := by
  have hanti : ∀ s t : ℕ, s ≤ t → util p v d t ≤ util p v d s := by
    intro s t hst
    unfold util
    have hsub : (owned d t)ᶜ ⊆ (owned d s)ᶜ := by
      apply Finset.compl_subset_compl.mpr
      unfold owned
      exact Finset.image_subset_image (Finset.range_mono hst)
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := v) (fun i _ _ => hv i)
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have := div_le_div_of_nonneg_right this hN
    linarith
  unfold purchases
  rw [← ENat.natCast_add_one_le_iff, le_iInf₂_iff]
  constructor
  · intro h
    by_contra hneg
    push Not at hneg
    have := h s hneg
    have h2 : s + 1 ≤ s := by exact_mod_cast this
    omega
  · intro h t ht
    have : s < t := by
      by_contra hts
      push Not at hts
      have := hanti t s hts
      linarith
    exact_mod_cast this

lemma lbtb_util_meas (N : ℕ) [NeZero N] (s : ℕ) (p : ℝ) :
    MeasurableSet {ω : (Fin N → ℝ) × (ℕ → Fin N) | 0 ≤ util p ω.1 ω.2 s} := by
  classical
  have hf : Measurable (fun (d : ℕ → Fin N) (i : ↥(Finset.range s)) => d i) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  set h : (Fin N → ℝ) × (↥(Finset.range s) → Fin N) → ℝ :=
    fun q => (∑ i ∈ (Finset.univ.image q.2)ᶜ, q.1 i) / N - p with hh
  have hhm : Measurable h := by
    apply measurable_from_prod_countable_left
    intro a
    simp only [hh]
    fun_prop
  have hφ : Measurable (fun ω : (Fin N → ℝ) × (ℕ → Fin N) =>
      (ω.1, (fun i : ↥(Finset.range s) => ω.2 i))) :=
    measurable_fst.prodMk (hf.comp measurable_snd)
  have : {ω : (Fin N → ℝ) × (ℕ → Fin N) | 0 ≤ util p ω.1 ω.2 s} =
      (fun ω : (Fin N → ℝ) × (ℕ → Fin N) => (ω.1, (fun i : ↥(Finset.range s) => ω.2 i))) ⁻¹'
        (h ⁻¹' Set.Ici 0) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici, hh, util, owned]
    have : (Finset.univ.image (fun i : ↥(Finset.range s) => ω.2 i)) = (Finset.range s).image ω.2 := by
      ext x; simp
    rw [this]
  rw [this]
  exact hφ (hhm measurableSet_Ici)

lemma lbtb_E_purchases (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ValLaw F) (N : ℕ) [NeZero N]
    (p : ℝ) :
    ∫⁻ ω, ((purchases p ω.1 ω.2 : ℕ∞) : ℝ≥0∞) ∂(law F N) =
      ∑' s, law F N {ω | 0 ≤ util p ω.1 ω.2 s} := by
  have hnn : ∀ᵐ v ∂(Measure.pi fun _ : Fin N => F), ∀ i, 0 ≤ v i := by
    rw [ae_all_iff]
    intro i
    have h0 : (Measure.pi fun _ : Fin N => F) {v | v i < 0} = 0 := by
      have := (measurePreserving_eval (fun _ : Fin N => F) i).measure_preimage
        (s := Set.Iio 0) measurableSet_Iio.nullMeasurableSet
      simpa [Set.preimage, hF.nonneg] using this
    rw [ae_iff]
    simpa using h0
  have hae : ∀ᵐ ω ∂(law F N), ∀ i, 0 ≤ ω.1 i :=
    (Measure.quasiMeasurePreserving_fst (μ := Measure.pi fun _ : Fin N => F)
      (ν := Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype (Fin N)).toMeasure)).ae hnn
  have h1 : ∫⁻ ω, ((purchases p ω.1 ω.2 : ℕ∞) : ℝ≥0∞) ∂(law F N) =
      ∫⁻ ω, ∑' s, ({ω : (Fin N → ℝ) × (ℕ → Fin N) | 0 ≤ util p ω.1 ω.2 s}.indicator (fun _ => (1 : ℝ≥0∞)) ω) ∂(law F N) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ω hω
    rw [lbtb_enat_tsum]
    congr 1
    ext s
    by_cases hs : 0 ≤ util p ω.1 ω.2 s
    · rw [Set.indicator_of_mem (show ω ∈ {ω : (Fin N → ℝ) × (ℕ → Fin N) | 0 ≤ util p ω.1 ω.2 s} from hs),
        if_pos ((lbtb_lt_purchases p ω.1 ω.2 hω s).2 hs)]
    · rw [Set.indicator_of_notMem (show ω ∉ {ω : (Fin N → ℝ) × (ℕ → Fin N) | 0 ≤ util p ω.1 ω.2 s} from hs),
        if_neg (fun h => hs ((lbtb_lt_purchases p ω.1 ω.2 hω s).1 h))]
  rw [h1, lintegral_tsum (fun s => (measurable_const.indicator (lbtb_util_meas N s p)).aemeasurable)]
  congr 1
  ext s
  rw [lintegral_indicator_const (lbtb_util_meas N s p), one_mul]

lemma lbtb_law_util (F : Measure ℝ) [IsProbabilityMeasure F] (N : ℕ) [NeZero N] (p : ℝ) (hp : 0 < p) (s : ℕ) :
    law F N {ω | 0 ≤ util p ω.1 ω.2 s} =
      ∫⁻ d, walkLaw F {w | (N : ℝ) * p ≤ ∑ i ∈ Finset.range (lbU s d), w i} ∂(lbB N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  unfold law
  rw [Measure.prod_apply_symm (lbtb_util_meas N s p)]
  refine lintegral_congr fun d => ?_
  have : (fun v : Fin N → ℝ => (v, d)) ⁻¹' {ω : (Fin N → ℝ) × (ℕ → Fin N) | 0 ≤ util p ω.1 ω.2 s} =
      {v | (N : ℝ) * p ≤ ∑ i ∈ (owned d s)ᶜ, v i} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_setOf_eq, util]
    rw [sub_nonneg, le_div_iff₀ hNpos, mul_comm]
  rw [this, lbtb_pi_law, lbtb_walk_law]
  rfl

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
  · push Not at hs
    have : (⨅ (k : ℕ) (_ : 1 ≤ k ∧ t ≤ ∑ i ∈ Finset.range k, w i), (k : ℕ∞)) = ⊤ := by
      refine iInf₂_eq_top.mpr fun k hk => ?_
      exact absurd hk.2 (not_le.mpr (hs k hk.1))
    rw [this] at h
    exact absurd h.symm (ENat.natCast_ne_top j)

noncomputable def lbQ (F : Measure ℝ) [IsProbabilityMeasure F] (N : ℕ) (p : ℝ) (k : ℕ) : ℝ≥0∞ :=
  walkLaw F {w | (N : ℝ) * p ≤ ∑ i ∈ Finset.range k, w i}

lemma lbQ_zero (F : Measure ℝ) [IsProbabilityMeasure F] (N : ℕ) [NeZero N] (p : ℝ) (hp : 0 < p) :
    lbQ F N p 0 = 0 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  unfold lbQ
  have : {w : ℕ → ℝ | (N : ℝ) * p ≤ ∑ i ∈ Finset.range 0, w i} = ∅ := by
    ext w; simp only [Finset.range_zero, Finset.sum_empty, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
    positivity
  rw [this]; simp

lemma lbtb_rhs (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ValLaw F) (N : ℕ) [NeZero N]
    (p : ℝ) (hp : 0 < p) :
    ∫⁻ w, ENNReal.ofReal (harmTail N (firstPassage w ((N : ℝ) * p))) ∂(walkLaw F) =
      ∑ k ∈ Finset.Icc 1 N, ENNReal.ofReal (1 / (k : ℝ)) * lbQ F N p k := by
  classical
  haveI : IsProbabilityMeasure (walkLaw F) := by unfold walkLaw; infer_instance
  have hnonneg : ∀ᵐ w ∂(walkLaw F), ∀ i, 0 ≤ w i := by
    rw [ae_all_iff]
    intro i
    have h0 : walkLaw F {w | w i < 0} = 0 := by
      have := (measurePreserving_eval_infinitePi (fun _ : ℕ => F) i).measure_preimage
        (s := Set.Iio 0) measurableSet_Iio.nullMeasurableSet
      simpa [walkLaw, Set.preimage, hF.nonneg] using this
    rw [ae_iff]
    simpa using h0
  have hmeasS : ∀ k : ℕ, MeasurableSet {w : ℕ → ℝ | (N : ℝ) * p ≤ ∑ i ∈ Finset.range k, w i} :=
    fun k => measurableSet_le measurable_const (by fun_prop)
  have h1 : ∀ᵐ w ∂(walkLaw F), ENNReal.ofReal (harmTail N (firstPassage w ((N : ℝ) * p))) =
      ∑ k ∈ Finset.Icc 1 N, {w : ℕ → ℝ | (N : ℝ) * p ≤ ∑ i ∈ Finset.range k, w i}.indicator
        (fun _ => ENNReal.ofReal (1 / (k : ℝ))) w := by
    filter_upwards [hnonneg] with w hw
    unfold harmTail
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity), Finset.sum_filter]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
    have hiff : (firstPassage w ((N : ℝ) * p) ≤ (k : ℕ∞)) ↔ (N : ℝ) * p ≤ ∑ i ∈ Finset.range k, w i := by
      constructor
      · intro h
        have hne : firstPassage w ((N : ℝ) * p) ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top k) h
        obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 hne
        have hj' : firstPassage w ((N : ℝ) * p) = (j : ℕ∞) := hj.symm
        obtain ⟨hj1, hjS⟩ := lbtb_fp_attained w _ j hj'
        rw [hj'] at h
        have hjk : j ≤ k := by exact_mod_cast h
        exact le_trans hjS (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hjk)
          (fun i _ _ => hw i))
      · intro h
        exact iInf₂_le k ⟨hk1, h⟩
    by_cases hc : firstPassage w ((N : ℝ) * p) ≤ (k : ℕ∞)
    · rw [if_pos hc, Set.indicator_of_mem (show w ∈ {w : ℕ → ℝ | (N : ℝ) * p ≤ ∑ i ∈ Finset.range k, w i} from hiff.1 hc)]
    · rw [if_neg hc, Set.indicator_of_notMem (show w ∉ {w : ℕ → ℝ | (N : ℝ) * p ≤ ∑ i ∈ Finset.range k, w i} from fun h => hc (hiff.2 h))]
  rw [lintegral_congr_ae h1, lintegral_finset_sum _ (fun k _ => measurable_const.indicator (hmeasS k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [lintegral_indicator_const (hmeasS k)]
  rfl

lemma lbtb_arith2 (N k : ℕ) (hN : 0 < N) (hk : 0 < k) :
    (N : ℝ≥0∞) / k / N = ENNReal.ofReal (1 / (k : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  rw [lbtb_cast_div N k hk, show (N : ℝ≥0∞) = ENNReal.ofReal (N : ℝ) by simp,
    ← ENNReal.ofReal_div_of_pos hNr]
  congr 1
  field_simp

lemma lbtb_int_Q (F : Measure ℝ) [IsProbabilityMeasure F] (N : ℕ) [NeZero N] (p : ℝ) (s : ℕ) :
    ∫⁻ d, lbQ F N p (lbU s d) ∂(lbB N) = ∑ k ∈ Finset.range (N + 1), lbQ F N p k * lbP N s k := by
  classical
  have hmeasU : ∀ k : ℕ, MeasurableSet {d : ℕ → Fin N | lbU s d = k} := by
    intro k
    have hf : Measurable (fun (d : ℕ → Fin N) (i : ↥(Finset.range s)) => d i) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply _)
    have : {d : ℕ → Fin N | lbU s d = k} =
        (fun (d : ℕ → Fin N) (i : ↥(Finset.range s)) => d i) ⁻¹' {a | lbC a = k} := by
      ext d; simp [lbU_eq]
    rw [this]
    exact hf ((Set.toFinite _).measurableSet)
  have h1 : ∀ d : ℕ → Fin N, lbQ F N p (lbU s d) =
      ∑ k ∈ Finset.range (N + 1), {d : ℕ → Fin N | lbU s d = k}.indicator (fun _ => lbQ F N p k) d := by
    intro d
    rw [Finset.sum_eq_single (lbU s d)]
    · simp
    · intro k _ hk
      simp [Set.indicator, Ne.symm hk]
    · intro h
      exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le (lbU_le s d))) h
  simp_rw [h1]
  rw [lintegral_finset_sum _ (fun k _ => measurable_const.indicator (hmeasU k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [lintegral_indicator_const (hmeasU k)]
  rfl

theorem solution (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ValLaw F) (N : ℕ) [NeZero N]
    (p : ℝ) (hp : 0 < p) :
    revenue F N p =
      ENNReal.ofReal p *
        ∫⁻ w, ENNReal.ofReal (harmTail N (firstPassage w ((N : ℝ) * p))) ∂(walkLaw F) := by
  classical
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  unfold revenue
  rw [lbtb_E_purchases F hF N p, lbtb_rhs F hF N p hp]
  have e1 : ∑' s, law F N {ω | 0 ≤ util p ω.1 ω.2 s} =
      ∑' s, ∑ k ∈ Finset.range (N + 1), lbQ F N p k * lbP N s k := by
    refine tsum_congr fun s => ?_
    rw [lbtb_law_util F N p hp s]
    exact lbtb_int_Q F N p s
  rw [e1, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  have e2 : ∀ k ∈ Finset.range (N + 1), ∑' s, lbQ F N p k * lbP N s k = lbQ F N p k * lbT N k := by
    intro k _
    rw [ENNReal.tsum_mul_left]; rfl
  rw [Finset.sum_congr rfl e2]
  have hrange : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext k; simp; omega
  rw [hrange, Finset.sum_insert (by simp), lbQ_zero F N p hp, zero_mul, zero_add]
  have e3 : ∀ k ∈ Finset.Icc 1 N, lbQ F N p k * lbT N k = lbQ F N p k * ((N : ℝ≥0∞) / k) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [lbT_eq N (N - k) k rfl hk.1 hk.2]
  rw [Finset.sum_congr rfl e3, mul_div_assoc, div_eq_mul_inv, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  rw [mul_assoc, ← div_eq_mul_inv, lbtb_arith2 N k hN (by omega), mul_comm]
