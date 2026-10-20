-- Prove2me | solution 1 for MomentDRO.Conf.corollary_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T22:27:38.962551+00:00
-- url     : https://prove2.me/submissions/337376c7-4f38-4deb-afa0-878181a3aa2e

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace PCe82

lemma int_of_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F : α → ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀ x, |F x| ≤ C) : Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hC x)

lemma abs_integral_le_of_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (F : α → ℝ) (C : ℝ) (hC : ∀ x, |F x| ≤ C) : |∫ x, F x ∂μ| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := C)
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
  simpa [Real.norm_eq_abs] using this

/-- Hoeffding step: a measurable function with oscillation at most `c`. -/
lemma hoeff_step {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (G : Ω → ℝ) (hG : Measurable G) (c B : ℝ) (hc : 0 ≤ c) (hB : ∀ z, |G z| ≤ B)
    (hosc : ∀ z z', G z' - G z ≤ c) (t : ℝ) :
    ∫ z, Real.exp (t * (G z - ∫ z', G z' ∂ν)) ∂ν ≤ Real.exp (c ^ 2 / 8 * t ^ 2) := by
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure ν
  have hbdd : BddBelow (Set.range G) := ⟨-B, by
    rintro _ ⟨z, rfl⟩; have := hB z; rw [abs_le] at this; linarith⟩
  set A := ⨅ z, G z with hA
  have hmem : ∀ z, G z ∈ Set.Icc A (A + c) := by
    intro z
    refine ⟨ciInf_le hbdd z, ?_⟩
    have : G z - c ≤ A := le_ciInf fun z' => by have := hosc z' z; linarith
    linarith
  have hs := hasSubgaussianMGF_of_mem_Icc (μ := ν) (X := G) (a := A) (b := A + c)
    hG.aemeasurable (Filter.Eventually.of_forall hmem)
  have h1 := hs.mgf_le t
  have hcoe : (((‖(A + c) - A‖₊ / 2) ^ 2 : NNReal) : ℝ) = c ^ 2 / 4 := by
    have : (A + c) - A = c := by ring
    rw [this]
    push_cast
    rw [Real.norm_eq_abs, abs_of_nonneg hc]
    ring
  rw [hcoe] at h1
  unfold mgf at h1
  calc ∫ z, Real.exp (t * (G z - ∫ z', G z' ∂ν)) ∂ν ≤ Real.exp (c ^ 2 / 4 * t ^ 2 / 2) := h1
    _ = Real.exp (c ^ 2 / 8 * t ^ 2) := by ring_nf

/-- McDiarmid's inequality, mgf form, uniform difference bound `c`. -/
theorem mcd_mgf {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (c B : ℝ) (hc : 0 ≤ c) : ∀ (n : ℕ) (f : (Fin n → Ω) → ℝ), Measurable f →
    (∀ S, |f S| ≤ B) → (∀ S i z, |f (Function.update S i z) - f S| ≤ c) → ∀ t : ℝ,
    ∫ S, Real.exp (t * (f S - ∫ S', f S' ∂(Measure.pi fun _ => ν))) ∂(Measure.pi fun _ => ν)
      ≤ Real.exp (n * c ^ 2 / 8 * t ^ 2) := by
  intro n
  induction n with
  | zero =>
    intro f _ _ _ t
    have hfS : ∀ S, f S = f default := fun S => congrArg f (Subsingleton.elim _ _)
    simp [hfS]
  | succ n ih =>
    intro f hf hB hdiff t
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0 with he
    have hmp : MeasurePreserving e (Measure.pi fun _ => ν)
        (ν.prod (Measure.pi fun _ : Fin n => ν)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0
    have hmps := hmp.symm e
    set g : Ω → (Fin n → Ω) → ℝ := fun z w => f (Fin.cons z w) with hg
    have hge : ∀ p : Ω × (Fin n → Ω), f (e.symm p) = g p.1 p.2 := by
      intro p; simp [g, e]; try rfl
    have hgm : Measurable (Function.uncurry g) := by
      have : Function.uncurry g = fun p => f (e.symm p) := by
        funext p; rw [hge p]; rfl
      rw [this]; exact hf.comp e.symm.measurable
    have hgB : ∀ z w, |g z w| ≤ B := fun z w => hB _
    set hw : (Fin n → Ω) → ℝ := fun w => ∫ z, g z w ∂ν with hhw
    have hwm : Measurable hw :=
      (StronglyMeasurable.integral_prod_left (μ := ν) hgm.stronglyMeasurable).measurable
    have hwB : ∀ w, |hw w| ≤ B := fun w => abs_integral_le_of_bdd ν _ B fun z => hgB z w
    have hgz : ∀ w, Measurable fun z => g z w := fun w => hgm.comp (measurable_id.prodMk measurable_const)
    have hwdiff : ∀ w j y, |hw (Function.update w j y) - hw w| ≤ c := by
      intro w j y
      simp only [hw]
      rw [← integral_sub (int_of_bdd ν _ (hgz _) B fun z => hgB z _)
        (int_of_bdd ν _ (hgz _) B fun z => hgB z _)]
      refine abs_integral_le_of_bdd ν _ c fun z => ?_
      simp only [g, Fin.cons_update]
      exact hdiff _ _ _
    have hih := ih hw hwm hwB hwdiff t
    -- the mean
    have hint_f : Integrable (fun p : Ω × (Fin n → Ω) => g p.1 p.2) (ν.prod (Measure.pi fun _ => ν)) :=
      int_of_bdd _ _ hgm B fun p => hgB p.1 p.2
    have hmean : ∫ S, f S ∂(Measure.pi fun _ => ν) = ∫ w, hw w ∂(Measure.pi fun _ => ν) := by
      rw [← hmps.integral_comp' (g := f)]
      simp_rw [hge]
      rw [integral_prod_symm _ hint_f]
    obtain ⟨m, hm⟩ : ∃ m, m = ∫ S, f S ∂(Measure.pi fun _ => ν) := ⟨_, rfl⟩
    rw [← hm]
    rw [← hm] at hmean
    have hexpm : Measurable fun p : Ω × (Fin n → Ω) => Real.exp (t * (g p.1 p.2 - m)) :=
      Real.measurable_exp.comp (measurable_const.mul (hgm.sub measurable_const))
    have hint_e : Integrable (fun p : Ω × (Fin n → Ω) => Real.exp (t * (g p.1 p.2 - m)))
        (ν.prod (Measure.pi fun _ => ν)) :=
      int_of_bdd _ _ hexpm (Real.exp (|t| * (B + |m|))) fun p => by
        rw [abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        have h1 := hgB p.1 p.2
        calc t * (g p.1 p.2 - m) ≤ |t * (g p.1 p.2 - m)| := le_abs_self _
          _ = |t| * |g p.1 p.2 - m| := abs_mul _ _
          _ ≤ |t| * (B + |m|) := by
            gcongr
            calc |g p.1 p.2 - m| ≤ |g p.1 p.2| + |m| := abs_sub _ _
              _ ≤ B + |m| := by linarith
    have hstep : ∀ w, ∫ z, Real.exp (t * (g z w - m)) ∂ν ≤
        Real.exp (t * (hw w - m)) * Real.exp (c ^ 2 / 8 * t ^ 2) := by
      intro w
      have hosc : ∀ z z', g z' w - g z w ≤ c := by
        intro z z'
        have := hdiff (Fin.cons z w) 0 z'
        rw [Fin.update_cons_zero] at this
        exact (abs_le.mp this).2
      have hh := hoeff_step ν (fun z => g z w) (hgz w) c B hc (fun z => hgB z w) hosc t
      have : ∀ z, Real.exp (t * (g z w - m)) =
          Real.exp (t * (hw w - m)) * Real.exp (t * (g z w - ∫ z', g z' w ∂ν)) := by
        intro z; rw [← Real.exp_add]; congr 1; simp only [hw]; ring
      simp_rw [this]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
    calc ∫ S, Real.exp (t * (f S - m)) ∂(Measure.pi fun _ => ν)
        = ∫ w, ∫ z, Real.exp (t * (g z w - m)) ∂ν ∂(Measure.pi fun _ => ν) := by
          rw [← hmps.integral_comp' (g := fun S => Real.exp (t * (f S - m)))]
          simp_rw [hge]
          rw [integral_prod_symm _ hint_e]
      _ ≤ ∫ w, Real.exp (t * (hw w - m)) * Real.exp (c ^ 2 / 8 * t ^ 2)
            ∂(Measure.pi fun _ => ν) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w =>
            integral_nonneg fun z => (Real.exp_pos _).le) ?_ (Filter.Eventually.of_forall hstep)
          refine Integrable.mul_const ?_ _
          refine int_of_bdd _ _ (Real.measurable_exp.comp
            (measurable_const.mul (hwm.sub measurable_const))) (Real.exp (|t| * (B + |m|))) fun w => ?_
          rw [abs_of_pos (Real.exp_pos _)]
          apply Real.exp_le_exp.mpr
          have h1 := hwB w
          calc t * (hw w - m) ≤ |t * (hw w - m)| := le_abs_self _
            _ = |t| * |hw w - m| := abs_mul _ _
            _ ≤ |t| * (B + |m|) := by
              gcongr
              calc |hw w - m| ≤ |hw w| + |m| := abs_sub _ _
                _ ≤ B + |m| := by linarith
      _ = (∫ w, Real.exp (t * (hw w - ∫ w', hw w' ∂(Measure.pi fun _ => ν)))
            ∂(Measure.pi fun _ => ν)) * Real.exp (c ^ 2 / 8 * t ^ 2) := by
          rw [integral_mul_const, ← hmean]
      _ ≤ Real.exp (n * c ^ 2 / 8 * t ^ 2) * Real.exp (c ^ 2 / 8 * t ^ 2) :=
          mul_le_mul_of_nonneg_right hih (Real.exp_pos _).le
      _ = Real.exp (((n + 1 : ℕ) : ℝ) * c ^ 2 / 8 * t ^ 2) := by
          rw [← Real.exp_add]; congr 1; push_cast; ring

lemma int_exp_of_bdd {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (f : α → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) (t : ℝ) :
    Integrable (fun x => Real.exp (t * f x)) ν := by
  refine Integrable.of_bound ((hf.const_mul t).exp.aestronglyMeasurable) (Real.exp (|t| * B))
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  calc t * f x ≤ |t * f x| := le_abs_self _
    _ = |t| * |f x| := abs_mul _ _
    _ ≤ |t| * B := mul_le_mul_of_nonneg_left (hB x) (abs_nonneg t)

section Hilb

variable {S : Type} [MeasurableSpace S]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]

theorem cross_zero (P : Measure S) [IsProbabilityMeasure P] (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    (ζ : S → H) (hζm : Measurable ζ) (R : ℝ) (hR : 0 ≤ R) (hζb : ∀ s, ‖ζ s‖ ≤ R)
    (hζ0 : ∀ u : H, ∫ s, inner (𝕜 := ℝ) u (ζ s) ∂P = 0) :
    ∫ D, inner (𝕜 := ℝ) (ζ (D i)) (ζ (D j)) ∂(Measure.pi fun _ : Fin n => P) = 0 := by
  have hind : IndepFun (fun D : Fin n → S => D i) (fun D => D j)
      (Measure.pi fun _ : Fin n => P) :=
    (iIndepFun_pi (X := fun _ => (id : S → S)) (fun _ => aemeasurable_id)).indepFun hij
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable).1 hind
  have hev : ∀ k : Fin n, (Measure.pi fun _ : Fin n => P).map (fun D => D k) = P :=
    fun k => (measurePreserving_eval (fun _ : Fin n => P) k).map_eq
  have hgm : Measurable fun p : S × S => inner (𝕜 := ℝ) (ζ p.1) (ζ p.2) :=
    (hζm.comp measurable_fst).inner (hζm.comp measurable_snd)
  have hgI : Integrable (fun p : S × S => inner (𝕜 := ℝ) (ζ p.1) (ζ p.2)) (P.prod P) := by
    refine Integrable.of_bound hgm.aestronglyMeasurable (R * R) (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs]
    calc |inner (𝕜 := ℝ) (ζ p.1) (ζ p.2)| ≤ ‖ζ p.1‖ * ‖ζ p.2‖ := abs_real_inner_le_norm _ _
      _ ≤ R * R := mul_le_mul (hζb _) (hζb _) (norm_nonneg _) hR
  have e1 : (∫ D, inner (𝕜 := ℝ) (ζ (D i)) (ζ (D j)) ∂(Measure.pi fun _ : Fin n => P)) =
      ∫ p, inner (𝕜 := ℝ) (ζ p.1) (ζ p.2)
        ∂((Measure.pi fun _ : Fin n => P).map (fun D => (D i, D j))) := by
    rw [integral_map ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
      hgm.aestronglyMeasurable]
  rw [e1, hmap, hev, hev, integral_prod _ hgI]
  simp only
  have : ∀ a : S, ∫ b, inner (𝕜 := ℝ) (ζ a) (ζ b) ∂P = 0 := fun a => hζ0 (ζ a)
  simp [this]


/-- concentration of the norm of a centred Hilbert-space sample mean (variance + difference form). -/
theorem conc2 (P : Measure S) [IsProbabilityMeasure P] (ζ : S → H) (hζm : Measurable ζ)
    (K : ℝ) (hK : 0 ≤ K) (hζb : ∀ s, ‖ζ s‖ ≤ K)
    (V : ℝ) (hV : ∫ s, ‖ζ s‖ ^ 2 ∂P ≤ V)
    (Dd : ℝ) (hDd : 0 ≤ Dd) (hζd : ∀ s s', ‖ζ s - ζ s'‖ ≤ Dd)
    (hζ0 : ∀ u : H, ∫ s, inner (𝕜 := ℝ) u (ζ s) ∂P = 0) (n : ℕ) (hn : 0 < n)
    (r : ℝ) (hr : 0 ≤ r) :
    (Measure.pi fun _ : Fin n => P).real
      {D | Real.sqrt (V / n) + r ≤ ‖(1 / (n : ℝ)) • ∑ i, ζ (D i)‖} ≤
      Real.exp (-r ^ 2 / (2 * (Dd ^ 2 / (4 * n)))) := by
  set μn := Measure.pi fun _ : Fin n => P with hμn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set Z : (Fin n → S) → ℝ := fun D => ‖(1 / (n : ℝ)) • ∑ i, ζ (D i)‖ with hZ
  have hsumm : Measurable fun D : Fin n → S => ∑ i, ζ (D i) :=
    Finset.measurable_sum _ fun i _ => hζm.comp (measurable_pi_apply i)
  have hZm : Measurable Z := (hsumm.const_smul _).norm
  have hZB : ∀ D, |Z D| ≤ K := by
    intro D
    rw [abs_of_nonneg (norm_nonneg _)]
    show ‖(1 / (n : ℝ)) • ∑ i, ζ (D i)‖ ≤ K
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have : ‖∑ i, ζ (D i)‖ ≤ n * K := by
      calc ‖∑ i, ζ (D i)‖ ≤ ∑ i : Fin n, ‖ζ (D i)‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin n, K := Finset.sum_le_sum fun i _ => hζb _
        _ = n * K := by simp
    rw [one_div, inv_mul_le_iff₀ hnpos]; linarith
  have hZd : ∀ (D : Fin n → S) (i : Fin n) (z : S),
      |Z (Function.update D i z) - Z D| ≤ Dd / n := by
    intro D i z
    have hdiff : (1 / (n : ℝ)) • ∑ j, ζ (Function.update D i z j) -
        (1 / (n : ℝ)) • ∑ j, ζ (D j) = (1 / (n : ℝ)) • (ζ z - ζ (D i)) := by
      have : ∑ j, ζ (Function.update D i z j) - ∑ j, ζ (D j) = ζ z - ζ (D i) := by
        rw [← Finset.sum_sub_distrib]
        rw [Finset.sum_eq_single i (fun j _ hj => by rw [Function.update_of_ne hj, sub_self])
          (by simp)]
        simp
      rw [← this, smul_sub]
    calc |Z (Function.update D i z) - Z D|
        ≤ ‖(1 / (n : ℝ)) • ∑ j, ζ (Function.update D i z j) -
          (1 / (n : ℝ)) • ∑ j, ζ (D j)‖ := abs_norm_sub_norm_le _ _
      _ = (1 / (n : ℝ)) * ‖ζ z - ζ (D i)‖ := by
          rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      _ ≤ (1 / (n : ℝ)) * Dd := by
          gcongr
          exact hζd _ _
      _ = Dd / n := by ring
  set mm := ∫ D, Z D ∂μn with hm
  have hZeq : ∀ D, Z D ^ 2 = (1 / (n : ℝ)) ^ 2 *
      ∑ i, ∑ j, inner (𝕜 := ℝ) (ζ (D i)) (ζ (D j)) := by
    intro D
    rw [hZ]; simp only
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      ← real_inner_self_eq_norm_sq, sum_inner]
    simp only [inner_sum]
  have hpairI : ∀ i j : Fin n, Integrable (fun D : Fin n → S =>
      inner (𝕜 := ℝ) (ζ (D i)) (ζ (D j))) μn := by
    intro i j
    refine Integrable.of_bound ((hζm.comp (measurable_pi_apply i)).inner
      (hζm.comp (measurable_pi_apply j))).aestronglyMeasurable (K * K) (ae_of_all _ fun D => ?_)
    rw [Real.norm_eq_abs]
    calc |inner (𝕜 := ℝ) (ζ (D i)) (ζ (D j))| ≤ ‖ζ (D i)‖ * ‖ζ (D j)‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ K * K := mul_le_mul (hζb _) (hζb _) (norm_nonneg _) hK
  have hdiag : ∀ i : Fin n, ∫ D, inner (𝕜 := ℝ) (ζ (D i)) (ζ (D i)) ∂μn ≤ V := by
    intro i
    have hg : Measurable fun s => ‖ζ s‖ ^ 2 := hζm.norm.pow_const 2
    calc ∫ D, inner (𝕜 := ℝ) (ζ (D i)) (ζ (D i)) ∂μn
        = ∫ D, (fun s => ‖ζ s‖ ^ 2) (D i) ∂μn := by
          simp_rw [real_inner_self_eq_norm_sq]
      _ = ∫ s, ‖ζ s‖ ^ 2 ∂(μn.map (fun D => D i)) := by
          rw [integral_map (measurable_pi_apply i).aemeasurable hg.aestronglyMeasurable]
      _ = ∫ s, ‖ζ s‖ ^ 2 ∂P := by
          rw [hμn, (measurePreserving_eval (fun _ : Fin n => P) i).map_eq]
      _ ≤ V := hV
  have hZ2 : ∫ D, Z D ^ 2 ∂μn ≤ V / n := by
    simp_rw [hZeq]
    rw [integral_const_mul, integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hpairI i j]
    have hrow : ∀ i : Fin n, ∫ D, ∑ j, inner (𝕜 := ℝ) (ζ (D i)) (ζ (D j)) ∂μn ≤ V := by
      intro i
      rw [integral_finsetSum _ fun j _ => hpairI i j]
      rw [Finset.sum_eq_single i (fun j _ hji =>
        cross_zero P n i j (Ne.symm hji) ζ hζm K hK hζb hζ0) (by simp)]
      exact hdiag i
    calc (1 / (n : ℝ)) ^ 2 * ∑ i, ∫ D, ∑ j, inner (𝕜 := ℝ) (ζ (D i)) (ζ (D j)) ∂μn
        ≤ (1 / (n : ℝ)) ^ 2 * ∑ _i : Fin n, V :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hrow i) (by positivity)
      _ = V / n := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have hm2 : mm ^ 2 ≤ V / n := by
    have hvar := ProbabilityTheory.variance_nonneg Z μn
    rw [variance_eq_sub (MemLp.of_bound hZm.aestronglyMeasurable K
      (ae_of_all _ fun D => by rw [Real.norm_eq_abs]; exact hZB D))] at hvar
    simp only [Pi.pow_apply] at hvar
    rw [hm]
    linarith
  have hmb : mm ≤ Real.sqrt (V / n) := (le_abs_self mm).trans (Real.abs_le_sqrt hm2)
  set cc : NNReal := ⟨Dd ^ 2 / (4 * n), by positivity⟩ with hcc
  have hccv : (cc : ℝ) = Dd ^ 2 / (4 * n) := rfl
  have hsub : HasSubgaussianMGF (fun D => Z D - mm) cc μn := by
    refine ⟨fun t => int_exp_of_bdd μn _ (hZm.sub measurable_const) (K + |mm|)
      (fun D => ?_) t, fun t => ?_⟩
    · show |Z D - mm| ≤ K + |mm|
      have := hZB D; have h2 := abs_add_le (Z D) (-mm)
      rw [abs_neg, ← sub_eq_add_neg] at h2; linarith
    · have := mcd_mgf P (Dd / n) K (by positivity) n Z hZm hZB hZd t
      unfold mgf
      rw [hccv]
      calc ∫ D, Real.exp (t * (Z D - mm)) ∂μn ≤ Real.exp (n * (Dd / n) ^ 2 / 8 * t ^ 2) := this
        _ = Real.exp (Dd ^ 2 / (4 * n) * t ^ 2 / 2) := by
          congr 1; field_simp; ring
  have htail := hsub.measure_ge_le hr
  rw [hccv] at htail
  refine le_trans (measureReal_mono (fun D hD => ?_)) htail
  show r ≤ Z D - mm
  have hD' : Real.sqrt (V / n) + r ≤ Z D := hD
  linarith

end Hilb

open Matrix

theorem norm_toLp_sq' {ι : Type} [Fintype ι] (w : ι → ℝ) :
    ‖(WithLp.toLp 2 w : EuclideanSpace ℝ ι)‖ ^ 2 = ∑ k, w k ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

theorem inner_toLp' {ι : Type} [Fintype ι] (u : EuclideanSpace ℝ ι) (w : ι → ℝ) :
    inner (𝕜 := ℝ) u (WithLp.toLp 2 w) = ∑ k, w k * u k := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct]

/-- Frobenius embedding of `z zᵀ - I`. -/
noncomputable def Yv {m : ℕ} (z : Fin m → ℝ) : EuclideanSpace ℝ (Fin m × Fin m) :=
  WithLp.toLp 2 (fun p => z p.1 * z p.2 - (1 : Matrix (Fin m) (Fin m) ℝ) p.1 p.2)

/-- Frobenius embedding of `x xᵀ`. -/
noncomputable def Xv {m : ℕ} (x : Fin m → ℝ) : EuclideanSpace ℝ (Fin m × Fin m) :=
  WithLp.toLp 2 (fun p => x p.1 * x p.2)

theorem dot_self_nonneg {m : ℕ} (z : Fin m → ℝ) : 0 ≤ z ⬝ᵥ z := by
  simp only [dotProduct]; exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem dot_sq {m : ℕ} (z w : Fin m → ℝ) :
    (z ⬝ᵥ w) ^ 2 = ∑ a, ∑ b, (z a * w a) * (z b * w b) := by
  rw [sq, dotProduct, Finset.sum_mul_sum]

theorem normY_sq {m : ℕ} (z : Fin m → ℝ) :
    ‖Yv z‖ ^ 2 = (z ⬝ᵥ z) ^ 2 - 2 * (z ⬝ᵥ z) + m := by
  rw [Yv, norm_toLp_sq', Fintype.sum_prod_type]
  have h : ∀ a b : Fin m, (z a * z b - (1 : Matrix (Fin m) (Fin m) ℝ) a b) ^ 2 =
      (z a * z a) * (z b * z b) - 2 * (if a = b then z a * z b else 0) +
        (if a = b then 1 else 0) := by
    intro a b
    rcases eq_or_ne a b with rfl | hab
    · rw [Matrix.one_apply_eq, if_pos rfl, if_pos rfl]; ring
    · rw [Matrix.one_apply_ne hab, if_neg hab, if_neg hab]; ring
  simp_rw [h]
  have hin : ∀ a : Fin m, ∑ b, ((z a * z a) * (z b * z b) - 2 * (if a = b then z a * z b else 0) +
      (if a = b then (1:ℝ) else 0)) = (z a * z a) * (z ⬝ᵥ z) - 2 * (z a * z a) + 1 := by
    intro a
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp [dotProduct]
  simp_rw [hin]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  simp [dotProduct, sq]

theorem normYdiff_sq {m : ℕ} (z w : Fin m → ℝ) :
    ‖Yv z - Yv w‖ ^ 2 = (z ⬝ᵥ z) ^ 2 + (w ⬝ᵥ w) ^ 2 - 2 * (z ⬝ᵥ w) ^ 2 := by
  have hsub : Yv z - Yv w = (WithLp.toLp 2 (fun p : Fin m × Fin m =>
      z p.1 * z p.2 - w p.1 * w p.2) : EuclideanSpace ℝ (Fin m × Fin m)) := by
    rw [Yv, Yv, ← WithLp.toLp_sub]
    congr 1
    funext p
    simp only [Pi.sub_apply]
    ring
  rw [hsub, norm_toLp_sq', Fintype.sum_prod_type, dot_sq, dot_sq, dot_sq, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem normX {m : ℕ} (x : Fin m → ℝ) : ‖Xv x‖ = x ⬝ᵥ x := by
  have h : ‖Xv x‖ ^ 2 = (x ⬝ᵥ x) ^ 2 := by
    rw [Xv, norm_toLp_sq', Fintype.sum_prod_type, dot_sq]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (dot_self_nonneg x)).1 h

theorem innerYX {m : ℕ} (z x : Fin m → ℝ) :
    inner (𝕜 := ℝ) (Yv z) (Xv x) = (x ⬝ᵥ z) ^ 2 - x ⬝ᵥ x := by
  rw [Xv, inner_toLp', Fintype.sum_prod_type]
  simp only [Yv, PiLp.toLp_apply]
  have h : ∀ a b : Fin m, x a * x b * (z a * z b - (1 : Matrix (Fin m) (Fin m) ℝ) a b) =
      (x a * z a) * (x b * z b) - (if a = b then x a * x b else 0) := by
    intro a b
    rcases eq_or_ne a b with rfl | hab
    · rw [Matrix.one_apply_eq, if_pos rfl]; ring
    · rw [Matrix.one_apply_ne hab, if_neg hab]; ring
  simp_rw [h]
  have hin : ∀ a : Fin m, ∑ b, ((x a * z a) * (x b * z b) - (if a = b then x a * x b else 0)) =
      (x a * z a) * (x ⬝ᵥ z) - x a * x a := by
    intro a
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq]
    simp [dotProduct]
  simp_rw [hin]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp [dotProduct, sq]

open scoped MatrixOrder in
theorem factor {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef) :
    ∃ B : Matrix (Fin m) (Fin m) ℝ, A = Bᵀ * B := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  exact ⟨B, by rw [hB, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]⟩

theorem quad_BtB {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ) (y : Fin m → ℝ) :
    MomentDRO.Conf.quadForm (Bᵀ * B) y = (B *ᵥ y) ⬝ᵥ (B *ᵥ y) := by
  unfold MomentDRO.Conf.quadForm
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem bsb {m : ℕ} (Sig B : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef)
    (hinv : Sig⁻¹ = Bᵀ * B) : B * Sig * Bᵀ = 1 := by
  have hdet : IsUnit Sig.det := (Matrix.isUnit_iff_isUnit_det Sig).mp hSig.isUnit
  have hBS : Bᵀ * (B * Sig) = 1 := by
    rw [← Matrix.mul_assoc, ← hinv, Matrix.nonsing_inv_mul _ hdet]
  exact mul_eq_one_comm.mp hBS

theorem quad_emp {m M : ℕ} (S : Fin M → (Fin m → ℝ)) (c z : Fin m → ℝ) :
    z ⬝ᵥ (MomentDRO.Conf.empCovAbout S c *ᵥ z) = (M : ℝ)⁻¹ * ∑ i, (z ⬝ᵥ (S i - c)) ^ 2 := by
  unfold MomentDRO.Conf.empCovAbout
  rw [Matrix.smul_mulVec, Matrix.sum_mulVec, dotProduct_smul, dotProduct_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul,
    dotProduct_comm (S i - c) z, sq]

theorem emp_symm {m M : ℕ} (S : Fin M → (Fin m → ℝ)) (c : Fin m → ℝ) (i j : Fin m) :
    MomentDRO.Conf.empCovAbout S c j i = MomentDRO.Conf.empCovAbout S c i j := by
  simp only [MomentDRO.Conf.empCovAbout, Matrix.smul_apply, Matrix.sum_apply,
    Matrix.vecMulVec_apply]
  congr 1
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

open MomentDRO.Conf in
theorem loewner_step {m M : ℕ} (Sig B : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef)
    (hinv : Sig⁻¹ = Bᵀ * B)
    (μ : Fin m → ℝ) (S : Fin M → (Fin m → ℝ)) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hfro : ∀ x : Fin m → ℝ,
      |(M : ℝ)⁻¹ * ∑ i, (x ⬝ᵥ (B *ᵥ (S i - μ))) ^ 2 - x ⬝ᵥ x| ≤ α * (x ⬝ᵥ x)) :
    LoewnerLE ((1 + α)⁻¹ • empCovAbout S μ) Sig ∧
      LoewnerLE Sig ((1 - α)⁻¹ • empCovAbout S μ) := by
  have hdet : IsUnit Sig.det := (Matrix.isUnit_iff_isUnit_det Sig).mp hSig.isUnit
  have hBSB := bsb Sig B hSig hinv
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin m) (Fin m) ℝ, C = Sig * Bᵀ := ⟨_, rfl⟩
  have hBC : B * C = 1 := by rw [hC, ← Matrix.mul_assoc]; exact hBSB
  have hCB : C * B = 1 := mul_eq_one_comm.mp hBC
  have hSigsym : ∀ i j, Sig j i = Sig i j := fun i j => by simpa using hSig.1.apply i j
  have hSigT : Sigᵀ = Sig := by ext i j; exact hSigsym i j
  have hCC : C * Cᵀ = Sig := by
    rw [hC, Matrix.transpose_mul, Matrix.transpose_transpose, hSigT, Matrix.mul_assoc,
      ← Matrix.mul_assoc Bᵀ, ← hinv, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
  have ha : ∀ z : Fin m → ℝ, z ⬝ᵥ (Sig *ᵥ z) = (z ᵥ* C) ⬝ᵥ (z ᵥ* C) := by
    intro z
    calc z ⬝ᵥ (Sig *ᵥ z) = z ⬝ᵥ ((C * Cᵀ) *ᵥ z) := by rw [hCC]
      _ = (z ᵥ* C) ⬝ᵥ (Cᵀ *ᵥ z) := by rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
      _ = (z ᵥ* C) ⬝ᵥ (z ᵥ* C) := by rw [Matrix.mulVec_transpose]
  have hb : ∀ (z v : Fin m → ℝ), z ⬝ᵥ v = (z ᵥ* C) ⬝ᵥ (B *ᵥ v) := by
    intro z v
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hCB, Matrix.one_mulVec]
  have hq : ∀ z : Fin m → ℝ, z ⬝ᵥ (empCovAbout S μ *ᵥ z) =
      (M : ℝ)⁻¹ * ∑ i, ((z ᵥ* C) ⬝ᵥ (B *ᵥ (S i - μ))) ^ 2 := by
    intro z
    rw [quad_emp]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [hb z (S i - μ)]
  have herm : ∀ c : ℝ, (Sig - c • empCovAbout S μ).IsHermitian := by
    intro c
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [star_trivial, Matrix.sub_apply, Matrix.smul_apply, hSigsym, emp_symm]
  refine ⟨?_, ?_⟩
  · show (Sig - (1 + α)⁻¹ • empCovAbout S μ).PosSemidef
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (herm _) fun z => ?_
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul, ha, hq]
    have h := hfro (z ᵥ* C)
    rw [abs_le] at h
    have h2 : (1 + α)⁻¹ * ((M : ℝ)⁻¹ * ∑ i, ((z ᵥ* C) ⬝ᵥ (B *ᵥ (S i - μ))) ^ 2) ≤
        (z ᵥ* C) ⬝ᵥ (z ᵥ* C) := by
      rw [inv_mul_le_iff₀ (by linarith)]; linarith
    linarith
  · show ((1 - α)⁻¹ • empCovAbout S μ - Sig).PosSemidef
    have hh : ((1 - α)⁻¹ • empCovAbout S μ - Sig).IsHermitian := by
      have := (herm (1 - α)⁻¹).neg
      rwa [neg_sub] at this
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh fun z => ?_
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul, ha, hq]
    have h := hfro (z ᵥ* C)
    rw [abs_le] at h
    have h2 : (z ᵥ* C) ⬝ᵥ (z ᵥ* C) ≤
        (1 - α)⁻¹ * ((M : ℝ)⁻¹ * ∑ i, ((z ᵥ* C) ⬝ᵥ (B *ᵥ (S i - μ))) ^ 2) := by
      rw [le_inv_mul_iff₀ (by linarith)]; linarith
    linarith

end PCe82

set_option maxHeartbeats 1000000 in
open MeasureTheory MomentDRO.Conf Matrix in
theorem solution {m M : ℕ} (P : Measure (Fin m → ℝ))
    (hP : HasSecondMoments P) (hcov : (covMat P).PosDef)
    (R : ℝ) (hA4 : Assumption4 P R) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hM : R ^ 4 * (Real.sqrt (1 - (m : ℝ) / R ^ 4) +
      Real.sqrt (Real.log (2 / δ))) ^ 2 < (M : ℝ)) :
    ENNReal.ofReal (1 - δ) ≤ sampleLaw P M
      {S | LoewnerLE ((1 + alphaC M m R (δ / 2))⁻¹ •
          empCovAbout S (meanVec P)) (covMat P) ∧
        LoewnerLE (covMat P) ((1 - alphaC M m R (δ / 2))⁻¹ •
          empCovAbout S (meanVec P))} := by
  have := hP.1
  simp only [sampleLaw]
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have h0 : ∀ X : Matrix (Fin 0) (Fin 0) ℝ, X.PosSemidef := fun X => by
      have : X = 0 := by ext i; exact i.elim0
      rw [this]; exact Matrix.PosSemidef.zero
    refine le_trans ?_ (measure_mono (s := Set.univ) ?_)
    · rw [measure_univ]; exact ENNReal.ofReal_le_one.2 (by linarith)
    · intro S _
      exact And.intro (h0 _) (h0 _)
  set μ := meanVec P with hμ
  set Sig := covMat P with hSig
  set α := alphaC M m R (δ / 2) with hαdef
  obtain ⟨B, hinv⟩ := PCe82.factor Sig⁻¹ hcov.inv.posSemidef
  have hBSB := PCe82.bsb Sig B hcov hinv
  have hqc : Continuous fun ξ : Fin m → ℝ => quadForm Sig⁻¹ (ξ - μ) := by
    unfold quadForm; simp only [dotProduct, Matrix.mulVec, Pi.sub_apply]; fun_prop
  obtain ⟨T, hT⟩ : ∃ T : (Fin m → ℝ) → (Fin m → ℝ),
      T = fun ξ => if quadForm Sig⁻¹ (ξ - μ) ≤ R ^ 2 then ξ else μ := ⟨_, rfl⟩
  have hTm : Measurable T := by
    rw [hT]
    exact Measurable.ite (measurableSet_le hqc.measurable measurable_const) measurable_id
      measurable_const
  have hTq : ∀ ξ, quadForm Sig⁻¹ (T ξ - μ) ≤ R ^ 2 := by
    intro ξ
    rw [hT]
    dsimp only
    split_ifs with h
    · exact h
    · simp only [sub_self, quadForm, zero_dotProduct]; positivity
  have hTae : ∀ᵐ ξ ∂P, T ξ = ξ := hA4.2.mono fun ξ h => by rw [hT]; exact if_pos h
  obtain ⟨ζ, hζ⟩ : ∃ ζ : (Fin m → ℝ) → (Fin m → ℝ), ζ = fun ξ => B *ᵥ (T ξ - μ) := ⟨_, rfl⟩
  have hζm : Measurable ζ := by
    have : Continuous fun y : Fin m → ℝ => B *ᵥ (y - μ) := by
      refine continuous_pi fun a => ?_
      simp only [Matrix.mulVec, dotProduct, Pi.sub_apply]; fun_prop
    rw [hζ]; exact this.measurable.comp hTm
  have hζaM : ∀ a, Measurable fun ξ => ζ ξ a := fun a => (measurable_pi_apply a).comp hζm
  have hζq : ∀ ξ, ζ ξ ⬝ᵥ ζ ξ ≤ R ^ 2 := by
    intro ξ; rw [hζ]; dsimp only; rw [← PCe82.quad_BtB, ← hinv]; exact hTq ξ
  have hζs0 : ∀ ξ, 0 ≤ ζ ξ ⬝ᵥ ζ ξ := fun ξ => PCe82.dot_self_nonneg _
  have hζa : ∀ ξ a, |ζ ξ a| ≤ R := by
    intro ξ a
    have h1 : ζ ξ a * ζ ξ a ≤ ζ ξ ⬝ᵥ ζ ξ :=
      Finset.single_le_sum (f := fun b => ζ ξ b * ζ ξ b) (fun b _ => mul_self_nonneg _)
        (Finset.mem_univ a)
    have := Real.abs_le_sqrt (x := ζ ξ a) (y := R ^ 2) (by rw [sq]; exact h1.trans (hζq ξ))
    rwa [Real.sqrt_sq hA4.1] at this
  have hprodI : ∀ a b, Integrable (fun ξ => ζ ξ a * ζ ξ b) P := fun a b =>
    PCe82.int_of_bdd P _ ((hζaM a).mul (hζaM b)) (R * R) (fun ξ => by
      rw [abs_mul]; exact mul_le_mul (hζa ξ a) (hζa ξ b) (abs_nonneg _) hA4.1)
  have hprodT : ∀ i j, Integrable (fun ξ => (T ξ i - μ i) * (T ξ j - μ j)) P := by
    intro i j
    have h1 : MemLp (fun ξ : Fin m → ℝ => ξ i - μ i) 2 P := (hP.2 i).sub (memLp_const _)
    have h2 : MemLp (fun ξ : Fin m → ℝ => ξ j - μ j) 2 P := (hP.2 j).sub (memLp_const _)
    exact (h1.integrable_mul h2).congr (hTae.mono fun ξ h => by simp [h])
  have hTT : ∀ i j, ∫ ξ, (T ξ i - μ i) * (T ξ j - μ j) ∂P = Sig i j := by
    intro i j
    have : Sig i j = ∫ ξ, (ξ i - μ i) * (ξ j - μ j) ∂P := rfl
    rw [this]
    exact integral_congr_ae (hTae.mono fun ξ h => by simp only [h])
  have hE : ∀ a b, ∫ ξ, ζ ξ a * ζ ξ b ∂P = (1 : Matrix (Fin m) (Fin m) ℝ) a b := by
    intro a b
    have hexp : ∀ ξ, ζ ξ a * ζ ξ b =
        ∑ i, ∑ j, (B a i * B b j) * ((T ξ i - μ i) * (T ξ j - μ j)) := by
      intro ξ; rw [hζ]; simp only [Matrix.mulVec, dotProduct, Pi.sub_apply]
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [integral_congr_ae (g := fun ξ => ∑ i, ∑ j, (B a i * B b j) *
      ((T ξ i - μ i) * (T ξ j - μ j))) (ae_of_all _ hexp)]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hprodT i j).const_mul _]
    have hrow : ∀ i, ∫ ξ, ∑ j, (B a i * B b j) * ((T ξ i - μ i) * (T ξ j - μ j)) ∂P =
        ∑ j, B a i * B b j * Sig i j := by
      intro i
      rw [integral_finsetSum _ fun j _ => (hprodT i j).const_mul _]
      exact Finset.sum_congr rfl fun j _ => by rw [integral_const_mul, hTT]
    rw [Finset.sum_congr rfl fun i _ => hrow i, ← hBSB]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have hsI : Integrable (fun ξ => ζ ξ ⬝ᵥ ζ ξ) P := by
    simp only [dotProduct]; exact integrable_finsetSum _ fun a _ => hprodI a a
  have hEs : ∫ ξ, ζ ξ ⬝ᵥ ζ ξ ∂P = m := by
    simp only [dotProduct]
    rw [integral_finsetSum _ fun a _ => hprodI a a]
    simp [hE]
  have hmR : (m : ℝ) ≤ R ^ 2 := by
    rw [← hEs]
    calc ∫ ξ, ζ ξ ⬝ᵥ ζ ξ ∂P ≤ ∫ _ξ, R ^ 2 ∂P := integral_mono hsI (integrable_const _) hζq
      _ = R ^ 2 := by simp
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
  have hR0 : R ≠ 0 := by
    intro h; rw [h] at hmR; norm_num at hmR; linarith
  have hRpos : 0 < R := lt_of_le_of_ne hA4.1 (Ne.symm hR0)
  -- the Frobenius-space vectors
  have hYm : Measurable fun ξ => PCe82.Yv (ζ ξ) := by
    simp only [PCe82.Yv]
    exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ fun p =>
      ((hζaM p.1).mul (hζaM p.2)).sub measurable_const)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = Real.sqrt (R ^ 4 + m) := ⟨_, rfl⟩
  have hYb : ∀ ξ, ‖PCe82.Yv (ζ ξ)‖ ≤ K := by
    intro ξ
    have h := PCe82.normY_sq (ζ ξ)
    have hs := hζq ξ; have hs0 := hζs0 ξ
    have h2 : ‖PCe82.Yv (ζ ξ)‖ ^ 2 ≤ R ^ 4 + m := by
      rw [h]; nlinarith
    have := Real.abs_le_sqrt h2
    rwa [abs_of_nonneg (norm_nonneg _), ← hK] at this
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = (R ^ 2) ^ 2 * (1 - (m : ℝ) / R ^ 4) := ⟨_, rfl⟩
  have hVeq : V = R ^ 4 - m := by rw [hV]; field_simp
  have hs2I : Integrable (fun ξ => (ζ ξ ⬝ᵥ ζ ξ) ^ 2) P := by
    refine PCe82.int_of_bdd P _ ?_ (R ^ 2 * R ^ 2) (fun ξ => ?_)
    · simp only [dotProduct]
      exact (Finset.measurable_sum _ fun a _ => (hζaM a).mul (hζaM a)).pow_const 2
    · rw [abs_of_nonneg (sq_nonneg _), sq]
      exact mul_le_mul (hζq ξ) (hζq ξ) (hζs0 ξ) (by positivity)
  have hYV : ∫ ξ, ‖PCe82.Yv (ζ ξ)‖ ^ 2 ∂P ≤ V := by
    rw [integral_congr_ae (g := fun ξ => (ζ ξ ⬝ᵥ ζ ξ) ^ 2 - 2 * (ζ ξ ⬝ᵥ ζ ξ) + m)
      (ae_of_all _ fun ξ => PCe82.normY_sq (ζ ξ))]
    rw [integral_add (by exact hs2I.sub (hsI.const_mul 2) :
      Integrable (fun ξ => (ζ ξ ⬝ᵥ ζ ξ) ^ 2 - 2 * (ζ ξ ⬝ᵥ ζ ξ)) P) (integrable_const _),
      integral_sub hs2I (hsI.const_mul 2), integral_const_mul, hEs, integral_const]
    have hle : ∫ ξ, (ζ ξ ⬝ᵥ ζ ξ) ^ 2 ∂P ≤ R ^ 4 := by
      calc ∫ ξ, (ζ ξ ⬝ᵥ ζ ξ) ^ 2 ∂P ≤ ∫ _ξ, R ^ 4 ∂P :=
            integral_mono hs2I (integrable_const _) (fun ξ => by
              have := pow_le_pow_left₀ (hζs0 ξ) (hζq ξ) 2
              calc (ζ ξ ⬝ᵥ ζ ξ) ^ 2 ≤ (R ^ 2) ^ 2 := this
                _ = R ^ 4 := by ring)
        _ = R ^ 4 := by simp
    simp only [probReal_univ, smul_eq_mul, one_mul]
    rw [hVeq]; linarith
  obtain ⟨Dd, hDd⟩ : ∃ Dd : ℝ, Dd = Real.sqrt (2 * R ^ 4) := ⟨_, rfl⟩
  have hYd : ∀ ξ ξ', ‖PCe82.Yv (ζ ξ) - PCe82.Yv (ζ ξ')‖ ≤ Dd := by
    intro ξ ξ'
    have h := PCe82.normYdiff_sq (ζ ξ) (ζ ξ')
    have h1 := pow_le_pow_left₀ (hζs0 ξ) (hζq ξ) 2
    have h2 := pow_le_pow_left₀ (hζs0 ξ') (hζq ξ') 2
    have h3 : ‖PCe82.Yv (ζ ξ) - PCe82.Yv (ζ ξ')‖ ^ 2 ≤ 2 * R ^ 4 := by
      rw [h]; nlinarith [sq_nonneg (ζ ξ ⬝ᵥ ζ ξ')]
    have := Real.abs_le_sqrt h3
    rwa [abs_of_nonneg (norm_nonneg _), ← hDd] at this
  have hY0 : ∀ u : EuclideanSpace ℝ (Fin m × Fin m),
      ∫ ξ, inner (𝕜 := ℝ) u (PCe82.Yv (ζ ξ)) ∂P = 0 := by
    intro u
    simp only [PCe82.Yv, PCe82.inner_toLp']
    rw [integral_finsetSum _ fun p _ => ((hprodI p.1 p.2).sub (integrable_const _)).mul_const _]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [integral_mul_const, integral_sub (hprodI _ _) (integrable_const _), hE, integral_const]
    simp
  -- constants
  have hMpos : (0 : ℝ) < M := by
    have : 0 ≤ R ^ 4 * (Real.sqrt (1 - (m : ℝ) / R ^ 4) + Real.sqrt (Real.log (2 / δ))) ^ 2 := by
      have : 0 ≤ R ^ 4 := by positivity
      positivity
    linarith
  have hMnat : 0 < M := by exact_mod_cast hMpos
  set L := Real.log (2 / δ) with hLdef
  have hL : 0 < L := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  set s1 := Real.sqrt (1 - (m : ℝ) / R ^ 4) with hs1
  have hsqM : Real.sqrt M ^ 2 = M := Real.sq_sqrt hMpos.le
  have hsqMpos : 0 < Real.sqrt M := Real.sqrt_pos.2 hMpos
  have hαeq : α = R ^ 2 / Real.sqrt M * (s1 + Real.sqrt L) := by
    rw [hαdef, alphaC, one_div_div]
  have hα0 : 0 ≤ α := by rw [hαeq]; positivity
  have hα1 : α < 1 := by
    have h2 : α ^ 2 < 1 := by
      rw [hαeq, mul_pow, div_pow, hsqM, div_mul_eq_mul_div, div_lt_one hMpos]
      calc (R ^ 2) ^ 2 * (s1 + Real.sqrt L) ^ 2 = R ^ 4 * (s1 + Real.sqrt L) ^ 2 := by ring
        _ < (M : ℝ) := hM
    nlinarith
  obtain ⟨Z, hZ⟩ : ∃ Z : (Fin M → (Fin m → ℝ)) → ℝ,
      Z = fun D => ‖(1 / (M : ℝ)) • ∑ i, PCe82.Yv (ζ (D i))‖ := ⟨_, rfl⟩
  have hZm : Measurable Z := by
    rw [hZ]
    exact ((Finset.measurable_sum _ fun i _ => hYm.comp (measurable_pi_apply i)).const_smul
      (1 / (M : ℝ))).norm
  have hgood : ∀ᵐ D ∂(Measure.pi fun _ : Fin M => P), ∀ i, T (D i) = D i := by
    rw [ae_all_iff]
    intro i
    exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin M => P) i).ae hTae
  have hsub : {D | Z D < α} ≤ᵐ[Measure.pi fun _ : Fin M => P]
      {S | LoewnerLE ((1 + α)⁻¹ • empCovAbout S μ) Sig ∧
        LoewnerLE Sig ((1 - α)⁻¹ • empCovAbout S μ)} := by
    filter_upwards [hgood] with D hD
    intro hZD
    change Z D < α at hZD
    have hζD : ∀ i, ζ (D i) = B *ᵥ (D i - μ) := by
      intro i; rw [hζ]; dsimp only; rw [hD i]
    refine PCe82.loewner_step Sig B hcov hinv μ D α hα0 hα1 fun x => ?_
    have hin : inner (𝕜 := ℝ) ((1 / (M : ℝ)) • ∑ i, PCe82.Yv (ζ (D i))) (PCe82.Xv x) =
        (M : ℝ)⁻¹ * ∑ i, (x ⬝ᵥ (B *ᵥ (D i - μ))) ^ 2 - x ⬝ᵥ x := by
      rw [real_inner_smul_left, sum_inner]
      simp_rw [PCe82.innerYX, hζD]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, one_div, mul_sub, ← mul_assoc, inv_mul_cancel₀ hMpos.ne', one_mul]
    have hcs := abs_real_inner_le_norm ((1 / (M : ℝ)) • ∑ i, PCe82.Yv (ζ (D i))) (PCe82.Xv x)
    rw [hin, PCe82.normX] at hcs
    have hZD' : ‖(1 / (M : ℝ)) • ∑ i, PCe82.Yv (ζ (D i))‖ ≤ α := by
      have : Z D = ‖(1 / (M : ℝ)) • ∑ i, PCe82.Yv (ζ (D i))‖ := by rw [hZ]
      rw [← this]; exact hZD.le
    exact hcs.trans (mul_le_mul_of_nonneg_right hZD' (PCe82.dot_self_nonneg x))
  have htail : (Measure.pi fun _ : Fin M => P) {D | α ≤ Z D} ≤ ENNReal.ofReal (δ / 2) := by
    set r := R ^ 2 / Real.sqrt M * Real.sqrt L with hr
    have hr0 : 0 ≤ r := by positivity
    have h1 := PCe82.conc2 P (fun ξ => PCe82.Yv (ζ ξ)) hYm K (by rw [hK]; positivity) hYb
      V hYV Dd (by rw [hDd]; positivity) hYd hY0 M hMnat r hr0
    have hsv : Real.sqrt (V / M) + r = α := by
      rw [hV, Real.sqrt_div' _ hMpos.le, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by positivity), hαeq, hr]
      ring
    have hsubset : {D | α ≤ Z D} ⊆
        {D | Real.sqrt (V / M) + r ≤ ‖(1 / (M : ℝ)) • ∑ i, PCe82.Yv (ζ (D i))‖} := by
      intro D hD
      have hD' : α ≤ Z D := hD
      rw [hZ] at hD'
      show Real.sqrt (V / M) + r ≤ ‖(1 / (M : ℝ)) • ∑ i, PCe82.Yv (ζ (D i))‖
      rw [hsv]; exact hD'
    have hexp : Real.exp (-r ^ 2 / (2 * (Dd ^ 2 / (4 * M)))) ≤ δ / 2 := by
      have hDd2 : Dd ^ 2 = 2 * R ^ 4 := by rw [hDd, Real.sq_sqrt (by positivity)]
      have : r ^ 2 / (2 * (Dd ^ 2 / (4 * M))) = L := by
        rw [hDd2, hr, mul_pow, div_pow, hsqM, Real.sq_sqrt hL.le]
        field_simp
        ring
      rw [neg_div, this, Real.exp_neg, hLdef, Real.exp_log (by positivity), inv_div]
    calc (Measure.pi fun _ : Fin M => P) {D | α ≤ Z D}
        ≤ (Measure.pi fun _ : Fin M => P)
            {D | Real.sqrt (V / M) + r ≤ ‖(1 / (M : ℝ)) • ∑ i, PCe82.Yv (ζ (D i))‖} :=
          measure_mono hsubset
      _ = ENNReal.ofReal ((Measure.pi fun _ : Fin M => P).real
            {D | Real.sqrt (V / M) + r ≤ ‖(1 / (M : ℝ)) • ∑ i, PCe82.Yv (ζ (D i))‖}) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (δ / 2) := ENNReal.ofReal_le_ofReal (h1.trans hexp)
  have hcompl : (Measure.pi fun _ : Fin M => P) {D | Z D < α} =
      1 - (Measure.pi fun _ : Fin M => P) {D | α ≤ Z D} := by
    have : {D | Z D < α} = {D | α ≤ Z D}ᶜ := by ext D; simp [not_le]
    rw [this, prob_compl_eq_one_sub (measurableSet_le measurable_const hZm)]
  calc ENNReal.ofReal (1 - δ) ≤ ENNReal.ofReal (1 - δ / 2) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ = 1 - ENNReal.ofReal (δ / 2) := by
        rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
    _ ≤ 1 - (Measure.pi fun _ : Fin M => P) {D | α ≤ Z D} := tsub_le_tsub_left htail _
    _ = (Measure.pi fun _ : Fin M => P) {D | Z D < α} := hcompl.symm
    _ ≤ _ := measure_mono_ae hsub
