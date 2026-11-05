-- Prove2me | solution 1 for MartOT.Product.curtain_target_least
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T05:25:54.496107+00:00
-- url     : https://prove2.me/submissions/26a3bdaa-4afc-4715-82e5-825abc5a9a6f

import Mathlib
import Definitions.Def_MartOT_Var_Setting

open MeasureTheory

namespace LC5Aux

/-- `ν^π_A = proj^y_# π|_{A×ℝ}`. -/
noncomputable def tgt (π : Measure (ℝ × ℝ)) (A : Set ℝ) : Measure ℝ :=
  (π.restrict (A ×ˢ Set.univ)).map Prod.snd

lemma integralE_of_nonneg {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    MartOT.Var.integralE μ f = ((∫⁻ x, ENNReal.ofReal (f x) ∂μ : ENNReal) : EReal) := by
  unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have h0 : ∀ x, (-(f x : EReal)).toENNReal = 0 := fun x =>
    EReal.toENNReal_of_nonpos (by rw [← EReal.coe_neg]; exact_mod_cast neg_nonpos.mpr (hf x))
  simp only [h0, lintegral_zero, EReal.real_coe_toENNReal, EReal.coe_ennreal_zero, sub_zero]

lemma integralE_eq {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) :
    MartOT.Var.integralE μ f = ((∫⁻ x, ENNReal.ofReal (f x) ∂μ : ENNReal) : EReal) -
      ((∫⁻ x, ENNReal.ofReal (-f x) ∂μ : ENNReal) : EReal) := by
  unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  simp only [← EReal.coe_neg, EReal.real_coe_toENNReal]

lemma tgt_apply (π : Measure (ℝ × ℝ)) (A : Set ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    tgt π A B = π (Prod.snd ⁻¹' B ∩ A ×ˢ Set.univ) := by
  unfold tgt
  rw [Measure.map_apply measurable_snd hB, Measure.restrict_apply (measurable_snd hB)]

lemma tgt_mono (π : Measure (ℝ × ℝ)) {A A' : Set ℝ} (h : A ⊆ A') : tgt π A ≤ tgt π A' := by
  unfold tgt
  exact Measure.map_mono (Measure.restrict_mono (Set.prod_mono h le_rfl) le_rfl) measurable_snd

lemma tgt_le_of_plan {μ ν : Measure ℝ} {π : Measure (ℝ × ℝ)} (h : MartOT.Var.IsPlan μ ν π)
    (A : Set ℝ) : tgt π A ≤ ν := by
  rw [← h.2]; unfold tgt
  exact Measure.map_mono Measure.restrict_le_self measurable_snd

lemma isFinite_of_plan {μ ν : Measure ℝ} [IsFiniteMeasure μ] {π : Measure (ℝ × ℝ)}
    (h : MartOT.Var.IsPlan μ ν π) : IsFiniteMeasure π := by
  refine ⟨?_⟩
  have : π Set.univ = μ Set.univ := by
    rw [← h.1, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
  rw [this]; exact measure_lt_top μ _

lemma inM_of_le {η ν : Measure ℝ} (h : η ≤ ν) (hν : MartOT.Var.InM ν) : MartOT.Var.InM η := by
  have := hν.1
  have : IsFiniteMeasure η := isFiniteMeasure_of_le ν h
  exact ⟨inferInstance, hν.2.mono_measure h⟩

lemma lintegral_tgt (π : Measure (ℝ × ℝ)) (A : Set ℝ) {g : ℝ → ENNReal} (hg : Measurable g) :
    ∫⁻ y, g y ∂(tgt π A) = ∫⁻ p in A ×ˢ Set.univ, g p.2 ∂π := by
  unfold tgt; rw [lintegral_map hg measurable_snd]

lemma lintegral_tgt_iUnion (π : Measure (ℝ × ℝ)) (u : ℕ → ℝ) (hu : Monotone u)
    {g : ℝ → ENNReal} (hg : Measurable g) :
    Monotone (fun n => ∫⁻ y, g y ∂(tgt π (Set.Iic (u n)))) ∧
    ∫⁻ y, g y ∂(tgt π (⋃ n, Set.Iic (u n))) = ⨆ n, ∫⁻ y, g y ∂(tgt π (Set.Iic (u n))) := by
  refine ⟨fun m n h => lintegral_mono' (tgt_mono π (Set.Iic_subset_Iic.mpr (hu h))) le_rfl, ?_⟩
  simp only [lintegral_tgt π _ hg]
  rw [Set.iUnion_prod_const]
  apply setLIntegral_iUnion_of_directed
  intro i j
  exact ⟨max i j, Set.prod_mono (Set.Iic_subset_Iic.mpr (hu (le_max_left i j))) le_rfl,
    Set.prod_mono (Set.Iic_subset_Iic.mpr (hu (le_max_right i j))) le_rfl⟩

lemma convex_lower_bound {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) :
    ∃ C K : ℝ, ∀ x, -φ x ≤ C + K * |x| := by
  refine ⟨|φ 0|, |φ 0 - φ (-1)| + |φ 1 - φ 0|, fun x => ?_⟩
  have h0 := neg_abs_le (φ 0)
  have ha1 := abs_nonneg (φ 0 - φ (-1))
  have ha2 := abs_nonneg (φ 1 - φ 0)
  have hx0 := abs_nonneg x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have h := hφ.secant_mono (a := 0) (x := x) (y := 1) trivial trivial trivial hx.ne
      (by norm_num) (by linarith)
    simp only [sub_zero, div_one] at h
    rw [div_le_iff_of_neg hx] at h
    have h1 : -(φ 1 - φ 0) * x ≤ |φ 1 - φ 0| * |x| := by
      rw [abs_of_neg hx, neg_mul, ← mul_neg]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (neg_pos.mpr hx).le
    nlinarith
  · subst hx; simp only [abs_zero, mul_zero, add_zero]; exact neg_le_abs _
  · have h := hφ.secant_mono (a := 0) (x := -1) (y := x) trivial trivial trivial (by norm_num)
      hx.ne' (by linarith)
    have e : (φ (-1) - φ 0) / (-1 - 0) = φ 0 - φ (-1) := by ring
    rw [e, sub_zero, le_div_iff₀ hx] at h
    have h1 : -(φ 0 - φ (-1)) * x ≤ |φ 0 - φ (-1)| * |x| := by
      rw [abs_of_pos hx]
      exact mul_le_mul_of_nonneg_right (by linarith [neg_abs_le (φ 0 - φ (-1))]) hx.le
    nlinarith

lemma lintegral_neg_ne_top {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) {η : Measure ℝ}
    (hη : MartOT.Var.InM η) : ∫⁻ x, ENNReal.ofReal (-φ x) ∂η ≠ ⊤ := by
  obtain ⟨C, K, hCK⟩ := convex_lower_bound hφ
  have := hη.1
  have hint : Integrable (fun x : ℝ => C + K * |x|) η :=
    (integrable_const C).add ((hη.2.abs).const_mul K)
  refine ne_top_of_le_ne_top hint.lintegral_lt_top.ne ?_
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hCK x)

lemma ereal_sub_le_iff (a b c d : ENNReal) (hb : b ≠ ⊤) (hd : d ≠ ⊤) :
    ((a : EReal) - b ≤ (c : EReal) - d) ↔ a + d ≤ c + b := by
  lift b to NNReal using hb
  lift d to NNReal using hd
  induction a using ENNReal.recTopCoe <;> induction c using ENNReal.recTopCoe
  · simp
  · rename_i c
    simp only [EReal.coe_nnreal_eq_coe_real, EReal.coe_ennreal_top]
    simp
    rw [← EReal.coe_sub]; exact EReal.coe_ne_top _
  · simp
  · rename_i a c
    rw [← ENNReal.coe_add, ← ENNReal.coe_add, ENNReal.coe_le_coe]
    simp only [EReal.coe_nnreal_eq_coe_real]
    rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff, ← NNReal.coe_le_coe,
      NNReal.coe_add, NNReal.coe_add]
    constructor <;> intro h <;> linarith


lemma ofReal_split (u v w : ℝ) (h : u + w ≤ v) :
    ENNReal.ofReal u + ENNReal.ofReal (-v) + ENNReal.ofReal w ≤
      ENNReal.ofReal v + ENNReal.ofReal (-u) + ENNReal.ofReal (-w) := by
  have e : ∀ r : ℝ, ENNReal.ofReal r = ENNReal.ofReal (max r 0) := by
    intro r; rcases le_total r 0 with hr | hr
    · rw [max_eq_right hr, ENNReal.ofReal_of_nonpos hr, ENNReal.ofReal_zero]
    · rw [max_eq_left hr]
  rw [e u, e (-v), e w, e v, e (-u), e (-w),
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ← ENNReal.ofReal_add (by positivity) (le_max_right _ _),
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ← ENNReal.ofReal_add (by positivity) (le_max_right _ _)]
  apply ENNReal.ofReal_le_ofReal
  rcases le_total u 0 with hu | hu <;> rcases le_total v 0 with hv | hv <;>
    rcases le_total w 0 with hw | hw <;>
    simp only [max_eq_left, max_eq_right, hu, hv, hw, neg_nonneg, neg_nonpos] <;> linarith

/-- Conditional Jensen for a martingale plan, restricted to `]-∞,s] × ℝ`. -/
lemma jensen_restrict {μ ν : Measure ℝ} (hμν : MartOT.Var.ConvexLE μ ν)
    (π : Measure (ℝ × ℝ)) (hπ : MartOT.Var.IsMartingalePlan μ ν π) (s : ℝ) :
    MartOT.Var.ConvexLE (μ.restrict (Set.Iic s)) (tgt π (Set.Iic s)) := by
  have : IsFiniteMeasure μ := hμν.1.1
  have hfπ : IsFiniteMeasure π := isFinite_of_plan hπ.1
  have hi1 : MartOT.Var.InM (μ.restrict (Set.Iic s)) := inM_of_le Measure.restrict_le_self hμν.1
  have hi2 : MartOT.Var.InM (tgt π (Set.Iic s)) := inM_of_le (tgt_le_of_plan hπ.1 _) hμν.2.1
  refine ⟨hi1, hi2, fun φ hφ => ?_⟩
  have hφc : Continuous φ := continuousOn_univ.mp (hφ.continuousOn isOpen_univ)
  have hm1 : Measurable (fun x => ENNReal.ofReal (φ x)) := hφc.measurable.ennreal_ofReal
  have hm2 : Measurable (fun x => ENNReal.ofReal (-φ x)) := hφc.measurable.neg.ennreal_ofReal
  rw [integralE_eq, integralE_eq,
    ereal_sub_le_iff _ _ _ _ (lintegral_neg_ne_top hφ hi1) (lintegral_neg_ne_top hφ hi2)]
  -- the subgradient
  set g : ℝ → ℝ := fun x => derivWithin φ (Set.Ioi x) x with hg
  have hgmono : Monotone g := by
    intro x y hxy
    have := hφ.monotoneOn_rightDeriv (by simp : x ∈ interior Set.univ)
      (by simp : y ∈ interior Set.univ) hxy
    exact this
  have hgm : Measurable g := hgmono.measurable
  have hsub : ∀ x y, φ x + g x * (y - x) ≤ φ y := by
    intro x y
    rcases lt_trichotomy x y with hxy | rfl | hxy
    · have h := hφ.rightDeriv_le_slope_of_mem_interior (by simp : x ∈ interior Set.univ)
        (Set.mem_univ y) hxy
      rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hxy)] at h
      show φ x + derivWithin φ (Set.Ioi x) x * (y - x) ≤ φ y
      linarith
    · simp
    · have h1 := hφ.slope_le_leftDeriv_of_mem_interior (Set.mem_univ y)
        (by simp : x ∈ interior Set.univ) hxy
      have h2 := hφ.leftDeriv_le_rightDeriv_of_mem_interior (by simp : x ∈ interior Set.univ)
      have h3 := le_trans h1 h2
      rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hxy)] at h3
      show φ x + derivWithin φ (Set.Ioi x) x * (y - x) ≤ φ y
      nlinarith
  -- truncation sets
  let E : ℕ → Set ℝ := fun M => {x | x ≤ s ∧ |g x| ≤ M}
  have hEm : ∀ M, MeasurableSet (E M) := fun M =>
    (measurableSet_le measurable_id measurable_const).inter
      (measurableSet_le hgm.abs measurable_const)
  let L : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (φ p.1) + ENNReal.ofReal (-φ p.2)
  let R : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (φ p.2) + ENNReal.ofReal (-φ p.1)
  have hLm : Measurable L := (hm1.comp measurable_fst).add (hm2.comp measurable_snd)
  have hRm : Measurable R := (hm1.comp measurable_snd).add (hm2.comp measurable_fst)
  have hstep : ∀ M : ℕ, ∫⁻ p in E M ×ˢ Set.univ, L p ∂π ≤ ∫⁻ p in E M ×ˢ Set.univ, R p ∂π := by
    intro M
    let ρ : ℝ → ℝ := (E M).indicator g
    have hρm : Measurable ρ := hgm.indicator (hEm M)
    have hρb : ∀ x, |ρ x| ≤ M := by
      intro x; simp only [ρ, Set.indicator]
      split_ifs with hx
      · exact hx.2
      · simp
    let h : ℝ × ℝ → ℝ := fun p => ρ p.1 * (p.2 - p.1)
    have hint : Integrable h π := by
      refine hπ.2.1.bdd_mul (c := M) (hρm.comp measurable_fst).aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall fun p => by
        simpa [Real.norm_eq_abs] using hρb p.1
    have hzero : ∫ p, h p ∂π = 0 := hπ.2.2 ρ hρm ⟨M, hρb⟩
    have hpn : ∫⁻ p, ENNReal.ofReal (h p) ∂π = ∫⁻ p, ENNReal.ofReal (-h p) ∂π := by
      rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint, sub_eq_zero] at hzero
      exact (ENNReal.toReal_eq_toReal_iff' hint.lintegral_lt_top.ne
        hint.neg.lintegral_lt_top.ne).mp hzero
    have hpt : ∫⁻ p, ENNReal.ofReal (h p) ∂π ≠ ⊤ := hint.lintegral_lt_top.ne
    have hhm : Measurable h := (hρm.comp measurable_fst).mul (measurable_snd.sub measurable_fst)
    have hpoint : ∀ p : ℝ × ℝ, (E M ×ˢ Set.univ).indicator L p + ENNReal.ofReal (h p) ≤
        (E M ×ˢ Set.univ).indicator R p + ENNReal.ofReal (-h p) := by
      intro p
      by_cases hp : p ∈ E M ×ˢ Set.univ
      · have hp1 : p.1 ∈ E M := hp.1
        have hρ : ρ p.1 = g p.1 := Set.indicator_of_mem hp1 g
        simp only [Set.indicator_of_mem hp, L, R, h, hρ]
        exact ofReal_split _ _ _ (hsub p.1 p.2)
      · have hp1 : p.1 ∉ E M := fun h1 => hp ⟨h1, Set.mem_univ _⟩
        have hρ : ρ p.1 = 0 := Set.indicator_of_notMem hp1 g
        simp [Set.indicator_of_notMem hp, h, hρ]
    have hint2 := lintegral_mono (μ := π) hpoint
    rw [lintegral_add_right _ hhm.ennreal_ofReal, lintegral_add_right _ (g := fun p => ENNReal.ofReal (-h p)) hhm.neg.ennreal_ofReal,
      ← hpn, lintegral_indicator ((hEm M).prod MeasurableSet.univ),
      lintegral_indicator ((hEm M).prod MeasurableSet.univ)] at hint2
    exact (ENNReal.add_le_add_iff_right hpt).mp hint2
  -- pass to the limit `M → ∞`
  have hU : (⋃ M : ℕ, E M ×ˢ (Set.univ : Set ℝ)) = Set.Iic s ×ˢ Set.univ := by
    ext ⟨x, y⟩
    simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_univ, and_true, Set.mem_Iic, E,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨M, h1, -⟩; exact h1
    · intro h1
      obtain ⟨M, hM⟩ := exists_nat_ge |g x|
      exact ⟨M, h1, hM⟩
  have hdir : Directed (· ⊆ ·) (fun M : ℕ => E M ×ˢ (Set.univ : Set ℝ)) := by
    intro i j
    refine ⟨max i j, Set.prod_mono (fun x hx => ⟨hx.1, le_trans hx.2 ?_⟩) le_rfl,
      Set.prod_mono (fun x hx => ⟨hx.1, le_trans hx.2 ?_⟩) le_rfl⟩
    · exact_mod_cast le_max_left i j
    · exact_mod_cast le_max_right i j
  have hlim : ∫⁻ p in Set.Iic s ×ˢ Set.univ, L p ∂π ≤ ∫⁻ p in Set.Iic s ×ˢ Set.univ, R p ∂π := by
    rw [← hU, setLIntegral_iUnion_of_directed _ hdir, setLIntegral_iUnion_of_directed _ hdir]
    exact iSup_mono hstep
  -- identify the four integrals
  have hfst : ∀ f : ℝ → ENNReal, Measurable f →
      ∫⁻ p in Set.Iic s ×ˢ Set.univ, f p.1 ∂π = ∫⁻ x, f x ∂(μ.restrict (Set.Iic s)) := by
    intro f hf
    have hmap : (π.restrict (Set.Iic s ×ˢ Set.univ)).map Prod.fst = μ.restrict (Set.Iic s) := by
      rw [← hπ.1.1, Measure.restrict_map measurable_fst measurableSet_Iic]
      congr 2
      ext ⟨x, y⟩; simp
    rw [← hmap, lintegral_map hf measurable_fst]
  have hsnd : ∀ f : ℝ → ENNReal, Measurable f →
      ∫⁻ p in Set.Iic s ×ˢ Set.univ, f p.2 ∂π = ∫⁻ y, f y ∂(tgt π (Set.Iic s)) := by
    intro f hf
    unfold tgt
    rw [lintegral_map hf measurable_snd]
  simp only [L, R] at hlim
  rw [lintegral_add_left (f := fun p : ℝ × ℝ => ENNReal.ofReal (φ p.1)) (hm1.comp measurable_fst),
    lintegral_add_left (f := fun p : ℝ × ℝ => ENNReal.ofReal (φ p.2)) (hm1.comp measurable_snd),
    hfst _ hm1, hfst _ hm2, hsnd _ hm1, hsnd _ hm2] at hlim
  exact hlim

end LC5Aux

open LC5Aux in
theorem solution (μ ν : Measure ℝ) (hμν : MartOT.Var.ConvexLE μ ν)
    (πlc π : Measure (ℝ × ℝ)) (hlc : MartOT.Var.IsLeftCurtain μ ν πlc) (hπ : MartOT.Var.IsMartingalePlan μ ν π)
    (s : ℝ) :
    MartOT.Var.targetUpTo π s ≤ ν ∧ MartOT.Var.ConvexLE (μ.restrict (Set.Iic s)) (MartOT.Var.targetUpTo π s) ∧
      MartOT.Var.ConvexLE (MartOT.Var.targetUpTo πlc s) (MartOT.Var.targetUpTo π s) := by
  have h1 : MartOT.Var.targetUpTo π s ≤ ν := tgt_le_of_plan hπ.1 (Set.Iic s)
  have h2 : MartOT.Var.ConvexLE (μ.restrict (Set.Iic s)) (MartOT.Var.targetUpTo π s) :=
    jensen_restrict hμν π hπ s
  exact ⟨h1, h2, (hlc.2 s).2.2.2 _ h1 h2⟩
