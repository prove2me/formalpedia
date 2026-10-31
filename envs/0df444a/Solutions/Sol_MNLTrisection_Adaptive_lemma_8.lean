-- Prove2me | solution 1 for MNLTrisection.Adaptive.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T17:15:35.298287+00:00
-- url     : https://prove2.me/submissions/ca4575f1-fa4b-4d6a-a52f-88dfb7aa1fa4

import Mathlib
import Definitions.Def_UnderstandingML_Framework
import Definitions.Def_MNLTrisection_Adaptive_Model

namespace MNLTriProb

open MeasureTheory ProbabilityTheory UnderstandingML

variable {Ω : Type*} [MeasurableSpace Ω]

theorem coord_ae (D : Measure Ω) [IsProbabilityMeasure D] (n : ℕ) (i : Fin n)
    {p : Ω → Prop} (hp : ∀ᵐ x ∂D, p x) : ∀ᵐ ω ∂(iidLaw D n), p (ω i) := by
  have hmp := measurePreserving_eval (fun _ : Fin n => D) i
  have h2 : ∀ᵐ x ∂(Measure.map (fun ω : Fin n → Ω => ω i) (iidLaw D n)), p x := by
    unfold iidLaw; rw [hmp.map_eq]; exact hp
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h2

theorem coord_integral (D : Measure Ω) [IsProbabilityMeasure D] (X : Ω → ℝ) (hX : Measurable X)
    (n : ℕ) (i : Fin n) : ∫ ω, X (ω i) ∂(iidLaw D n) = ∫ x, X x ∂D := by
  have hmp := measurePreserving_eval (fun _ : Fin n => D) i
  unfold iidLaw
  rw [← integral_map (measurable_pi_apply i).aemeasurable hX.aestronglyMeasurable, hmp.map_eq]

/-- One-sided Hoeffding inequality for a sub-sum of coordinates of an i.i.d. sample. -/
theorem hoeffding_upper (D : Measure Ω) [IsProbabilityMeasure D] (X : Ω → ℝ) (hX : Measurable X)
    {a b : ℝ} (hab : ∀ᵐ x ∂D, X x ∈ Set.Icc a b) (n : ℕ) (s : Finset (Fin n)) {ε : ℝ}
    (hε : 0 ≤ ε) :
    (iidLaw D n).real {ω | ε ≤ ∑ i ∈ s, (X (ω i) - ∫ x, X x ∂D)} ≤
      Real.exp (-(2 * ε ^ 2) / (s.card * (b - a) ^ 2)) := by
  haveI : IsProbabilityMeasure (iidLaw D n) := by unfold iidLaw; infer_instance
  have hind : iIndepFun (fun (i : Fin n) (ω : Fin n → Ω) => X (ω i) - ∫ x, X x ∂D)
      (iidLaw D n) := by
    have := iIndepFun_pi (μ := fun _ : Fin n => D) (X := fun _ x => X x - ∫ x, X x ∂D)
      (fun _ => (hX.sub_const _).aemeasurable)
    exact this
  have hsub : ∀ i ∈ s, HasSubgaussianMGF (fun ω : Fin n → Ω => X (ω i) - ∫ x, X x ∂D)
      ((‖b - a‖₊ / 2) ^ 2) (iidLaw D n) := by
    intro i _
    have h := hasSubgaussianMGF_of_mem_Icc (μ := iidLaw D n) (X := fun ω : Fin n → Ω => X (ω i))
      (a := a) (b := b) ((hX.comp (measurable_pi_apply i)).aemeasurable) (coord_ae D n i hab)
    rw [coord_integral D X hX n i] at h
    exact h
  have := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub hε
  refine this.trans (le_of_eq ?_)
  congr 1
  have hc : ((∑ i ∈ s, (‖b - a‖₊ / 2) ^ 2 : NNReal) : ℝ) = s.card * ((b - a) ^ 2 / 4) := by
    push_cast
    rw [Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [Real.norm_eq_abs, div_pow, sq_abs]
    ring
  rw [hc, show 2 * (↑s.card * ((b - a) ^ 2 / 4)) = (↑s.card * (b - a) ^ 2) / 2 by ring,
    div_div_eq_mul_div]
  ring

end MNLTriProb

namespace MNLTriMax

open MeasureTheory ProbabilityTheory UnderstandingML

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Prefix sums `∑_{i < k} (X(ω_i) - μ)` of a sample of length `L`. -/
noncomputable def psum (X : Ω → ℝ) (μ : ℝ) {L : ℕ} (k : ℕ) (ω : Fin L → Ω) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin L => (i : ℕ) < k), (X (ω i) - μ)

theorem psum_measurable (X : Ω → ℝ) (hX : Measurable X) (μ : ℝ) (L k : ℕ) :
    Measurable (psum X μ (L := L) k) := by
  unfold psum
  exact Finset.measurable_sum _ (fun i _ => (hX.comp (measurable_pi_apply i)).sub_const _)

/-- Partial sums over a sub-finset `U`, as a function of the restriction of the sample to `U`. -/
noncomputable def rsum (X : Ω → ℝ) (μ : ℝ) {L : ℕ} (U : Finset (Fin L)) (j : ℕ)
    (z : U → Ω) : ℝ :=
  ∑ i ∈ Finset.filter (fun i : U => ((i : Fin L) : ℕ) < j) Finset.univ, (X (z i) - μ)

theorem rsum_measurable (X : Ω → ℝ) (hX : Measurable X) (μ : ℝ) {L : ℕ} (U : Finset (Fin L))
    (j : ℕ) : Measurable (rsum X μ U j) := by
  unfold rsum
  exact Finset.measurable_sum _ (fun i _ => (hX.comp (measurable_pi_apply i)).sub_const _)

theorem sum_subtype_filter {L : ℕ} (U : Finset (Fin L)) (p : Fin L → Prop) [DecidablePred p]
    (f : Fin L → ℝ) :
    ∑ i ∈ Finset.filter (fun i : U => p (i : Fin L)) Finset.univ, f i =
      ∑ i ∈ U.filter p, f i := by
  rw [Finset.sum_filter, Finset.sum_filter]
  exact Finset.sum_coe_sort U (fun i => if p i then f i else 0)

theorem psum_eq_rsum (X : Ω → ℝ) (μ : ℝ) {L : ℕ} (k j : ℕ) (hjk : j ≤ k) (ω : Fin L → Ω) :
    psum X μ j ω = rsum X μ (Finset.univ.filter (fun i : Fin L => (i : ℕ) < k)) j
      (fun i => ω i) := by
  unfold psum rsum
  rw [sum_subtype_filter _ (fun i : Fin L => (i : ℕ) < j) (fun i => X (ω i) - μ),
    Finset.filter_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  omega

/-- **Maximal Hoeffding inequality** for prefix sums of an i.i.d. sample. -/
theorem max_hoeffding (D : Measure Ω) [IsProbabilityMeasure D] (X : Ω → ℝ) (hX : Measurable X)
    {a b : ℝ} (hab : ∀ᵐ x ∂D, X x ∈ Set.Icc a b) (L m : ℕ) {x lam : ℝ} (hlam : 0 < lam) :
    (iidLaw D L).real {ω | ∃ k ≤ m, x ≤ psum X (∫ y, X y ∂D) k ω} ≤
      Real.exp (-(lam * x)) *
        Real.exp ((((Finset.univ.filter (fun i : Fin L => (i : ℕ) < m)).card : ℝ) *
          ((b - a) ^ 2 / 4)) * lam ^ 2 / 2) := by
  classical
  set P := iidLaw D L with hP
  haveI : IsProbabilityMeasure P := by rw [hP]; unfold iidLaw; infer_instance
  set μ := ∫ y, X y ∂D with hμ
  set Y : Fin L → (Fin L → Ω) → ℝ := fun i ω => X (ω i) - μ with hY
  have hind : iIndepFun Y P := by
    have := iIndepFun_pi (μ := fun _ : Fin L => D) (X := fun _ x => X x - μ)
      (fun _ => (hX.sub_const _).aemeasurable)
    exact this
  have hcoord : iIndepFun (fun (i : Fin L) (ω : Fin L → Ω) => ω i) P := by
    have := iIndepFun_pi (μ := fun _ : Fin L => D) (X := fun _ (x : Ω) => x)
      (fun _ => aemeasurable_id)
    exact this
  have hsub : ∀ i, HasSubgaussianMGF (Y i) ((‖b - a‖₊ / 2) ^ 2) P := by
    intro i
    have h := hasSubgaussianMGF_of_mem_Icc (μ := P) (X := fun ω : Fin L → Ω => X (ω i))
      (a := a) (b := b) ((hX.comp (measurable_pi_apply i)).aemeasurable)
      (MNLTriProb.coord_ae D L i hab)
    rw [MNLTriProb.coord_integral D X hX L i] at h
    exact h
  have hsubS : ∀ s : Finset (Fin L), HasSubgaussianMGF (fun ω => ∑ i ∈ s, Y i ω)
      (∑ i ∈ s, (‖b - a‖₊ / 2) ^ 2) P :=
    fun s => HasSubgaussianMGF.sum_of_iIndepFun hind (fun i _ => hsub i)
  have hYint : ∀ i, ∫ ω, Y i ω ∂P = 0 := by
    intro i
    have hXi : Integrable (fun ω : Fin L → Ω => X (ω i)) P := by
      have := (hsub i).integrable.add (integrable_const μ)
      refine this.congr (ae_of_all _ (fun ω => ?_))
      simp [hY]
    simp only [hY]
    rw [integral_sub hXi (integrable_const _), MNLTriProb.coord_integral D X hX L i]
    simp [hμ]
  -- the events
  set S : ℕ → Finset (Fin L) := fun k => Finset.univ.filter (fun i : Fin L => (i : ℕ) < k)
    with hS
  have hpsumY : ∀ k ω, psum X μ k ω = ∑ i ∈ S k, Y i ω := fun k ω => rfl
  set A : ℕ → Set (Fin L → Ω) := fun k =>
    {ω | x ≤ psum X μ k ω ∧ ∀ j < k, psum X μ j ω < x} with hA
  have hAmeas : ∀ k, MeasurableSet (A k) := by
    intro k
    have h1 : MeasurableSet {ω : Fin L → Ω | x ≤ psum X μ k ω} :=
      measurableSet_le measurable_const (psum_measurable X hX μ L k)
    have h2 : MeasurableSet {ω : Fin L → Ω | ∀ j < k, psum X μ j ω < x} := by
      have : {ω : Fin L → Ω | ∀ j < k, psum X μ j ω < x} =
          ⋂ j, ⋂ (_ : j < k), {ω | psum X μ j ω < x} := by
        ext ω; simp
      rw [this]
      exact MeasurableSet.iInter (fun j => MeasurableSet.iInter
        (fun _ => measurableSet_lt (psum_measurable X hX μ L j) measurable_const))
    exact h1.inter h2
  have hcover : {ω | ∃ k ≤ m, x ≤ psum X μ k ω} ⊆ ⋃ k ∈ Finset.range (m + 1), A k := by
    intro ω hω
    have hex : ∃ k, k ≤ m ∧ x ≤ psum X μ k ω := hω
    let k0 := Nat.find hex
    have hk0 := Nat.find_spec hex
    simp only [Set.mem_iUnion, Finset.mem_range]
    refine ⟨k0, by omega, hk0.2, fun j hj => ?_⟩
    by_contra hcon
    push Not at hcon
    exact Nat.find_min hex hj ⟨by omega, hcon⟩
  set f : (Fin L → Ω) → ℝ := fun ω => Real.exp (lam * psum X μ m ω) with hf
  have hfint : Integrable f P := by
    have := (hsubS (S m)).integrable_exp_mul lam
    exact this
  -- key per-k bound
  have hkey : ∀ k ∈ Finset.range (m + 1),
      Real.exp (lam * x) * P.real (A k) ≤ ∫ ω, (A k).indicator f ω ∂P := by
    intro k hk
    have hkm : k ≤ m := by simpa [Nat.lt_succ_iff] using hk
    set U := S k
    set V := S m \ S k
    have hUV : Disjoint U V := Finset.disjoint_sdiff
    have hsplit : ∀ ω, psum X μ m ω = psum X μ k ω + ∑ i ∈ V, Y i ω := by
      intro ω
      rw [hpsumY, hpsumY, add_comm]
      exact (Finset.sum_sdiff (by
        intro i hi
        simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        omega)).symm
    set g : (Fin L → Ω) → ℝ := (A k).indicator (fun ω => Real.exp (lam * psum X μ k ω))
    set h : (Fin L → Ω) → ℝ := fun ω => Real.exp (lam * ∑ i ∈ V, Y i ω)
    have hgh : (A k).indicator f = fun ω => g ω * h ω := by
      funext ω
      simp only [g, h, f, Set.indicator_apply]
      split_ifs
      · rw [hsplit ω, mul_add, Real.exp_add]
      · simp
    -- g and h as functions of disjoint coordinate blocks
    set G : (U → Ω) → ℝ := fun z =>
      ({z | x ≤ rsum X μ U k z ∧ ∀ j < k, rsum X μ U j z < x} : Set (U → Ω)).indicator
        (fun z => Real.exp (lam * rsum X μ U k z)) z
    set H : (V → Ω) → ℝ := fun z => Real.exp (lam * ∑ i : V, (X (z i) - μ))
    have hGm : Measurable G := by
      apply Measurable.indicator
      · exact Real.measurable_exp.comp (measurable_const.mul (rsum_measurable X hX μ U k))
      · have h1 : MeasurableSet {z : U → Ω | x ≤ rsum X μ U k z} :=
          measurableSet_le measurable_const (rsum_measurable X hX μ U k)
        have h2 : MeasurableSet {z : U → Ω | ∀ j < k, rsum X μ U j z < x} := by
          have : {z : U → Ω | ∀ j < k, rsum X μ U j z < x} =
              ⋂ j, ⋂ (_ : j < k), {z | rsum X μ U j z < x} := by
            ext z; simp
          rw [this]
          exact MeasurableSet.iInter (fun j => MeasurableSet.iInter
            (fun _ => measurableSet_lt (rsum_measurable X hX μ U j) measurable_const))
        exact h1.inter h2
    have hHm : Measurable H := by
      apply Real.measurable_exp.comp
      apply measurable_const.mul
      exact Finset.measurable_sum _ (fun i _ => (hX.comp (measurable_pi_apply i)).sub_const _)
    have hgG : g = fun ω => G (fun i : U => ω i) := by
      funext ω
      simp only [g, G, Set.indicator_apply, Set.mem_setOf_eq, hA]
      have e1 : psum X μ k ω = rsum X μ U k (fun i : U => ω i) :=
        psum_eq_rsum X μ k k le_rfl ω
      have e2 : ∀ j < k, psum X μ j ω = rsum X μ U j (fun i : U => ω i) :=
        fun j hj => psum_eq_rsum X μ k j hj.le ω
      rw [e1]
      congr 1
      apply propext
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun j hj => (e2 j hj) ▸ h2 j hj⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun j hj => (e2 j hj).symm ▸ h2 j hj⟩
    have hhH : h = fun ω => H (fun i : V => ω i) := by
      funext ω
      simp only [h, H, hY]
      congr 2
      exact (Finset.sum_coe_sort V (fun i => X (ω i) - μ)).symm
    have hindep : IndepFun g h P := by
      rw [hgG, hhH]
      exact (hcoord.indepFun_finset U V hUV (fun i => measurable_pi_apply i)).comp hGm hHm
    have hgm : Measurable g := by rw [hgG]; exact hGm.comp (measurable_pi_lambda _
      (fun i => measurable_pi_apply _))
    have hhm : Measurable h := by rw [hhH]; exact hHm.comp (measurable_pi_lambda _
      (fun i => measurable_pi_apply _))
    have hmul : ∫ ω, g ω * h ω ∂P = (∫ ω, g ω ∂P) * ∫ ω, h ω ∂P :=
      hindep.integral_fun_mul_eq_mul_integral hgm.aestronglyMeasurable hhm.aestronglyMeasurable
    -- ∫ h ≥ 1
    have hZint : Integrable (fun ω => ∑ i ∈ V, Y i ω) P := (hsubS V).integrable
    have hZ0 : ∫ ω, ∑ i ∈ V, Y i ω ∂P = 0 := by
      rw [integral_finsetSum _ (fun i _ => (hsub i).integrable)]
      simp [hYint]
    have hh1 : 1 ≤ ∫ ω, h ω ∂P := by
      have hhint : Integrable h P := (hsubS V).integrable_exp_mul lam
      have hlin : Integrable (fun ω => 1 + lam * ∑ i ∈ V, Y i ω) P :=
        (integrable_const 1).add (hZint.const_mul lam)
      have := integral_mono hlin hhint (fun ω => by
        have := Real.add_one_le_exp (lam * ∑ i ∈ V, Y i ω)
        simp only [h]; linarith)
      rw [integral_add (integrable_const 1) (hZint.const_mul lam), integral_const_mul, hZ0]
        at this
      simpa using this
    -- ∫ g ≥ e^{λx} P(A k)
    have hgint : Integrable g P :=
      ((hsubS U).integrable_exp_mul lam).indicator (hAmeas k)
    have hg0 : 0 ≤ ∫ ω, g ω ∂P := integral_nonneg (fun ω => by
      simp only [g, Set.indicator_apply]; split_ifs <;> positivity)
    have hgA : Real.exp (lam * x) * P.real (A k) ≤ ∫ ω, g ω ∂P := by
      have hc : ∫ ω, (A k).indicator (fun _ => Real.exp (lam * x)) ω ∂P =
          P.real (A k) * Real.exp (lam * x) := by
        rw [integral_indicator_const _ (hAmeas k), smul_eq_mul]
      rw [mul_comm, ← hc]
      apply integral_mono ((integrable_const _).indicator (hAmeas k)) hgint
      intro ω
      simp only [g, Set.indicator_apply]
      split_ifs with hω
      · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω.1 hlam.le)
      · exact le_rfl
    calc Real.exp (lam * x) * P.real (A k) ≤ ∫ ω, g ω ∂P := hgA
      _ ≤ (∫ ω, g ω ∂P) * ∫ ω, h ω ∂P := le_mul_of_one_le_right hg0 hh1
      _ = ∫ ω, (A k).indicator f ω ∂P := by rw [← hmul, hgh]
  -- sum over k
  have hsumle : ∑ k ∈ Finset.range (m + 1), ∫ ω, (A k).indicator f ω ∂P ≤ ∫ ω, f ω ∂P := by
    rw [← integral_finsetSum _ (fun k _ => hfint.indicator (hAmeas k))]
    apply integral_mono (integrable_finsetSum _ (fun k _ => hfint.indicator (hAmeas k))) hfint
    intro ω
    simp only [Set.indicator_apply]
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.range (m + 1)).filter (fun k => ω ∈ A k)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro k1 hk1 k2 hk2
      simp only [Finset.mem_filter] at hk1 hk2
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact absurd (hk2.2.2 k1 hlt) (not_lt.mpr hk1.2.1)
      · exact absurd (hk1.2.2 k2 hlt) (not_lt.mpr hk2.2.1)
    have hf0 : 0 ≤ f ω := by simp only [f]; positivity
    have : (((Finset.range (m + 1)).filter (fun k => ω ∈ A k)).card : ℝ) ≤ 1 := by
      exact_mod_cast hcard
    nlinarith
  -- mgf bound
  have hmgf : ∫ ω, f ω ∂P ≤ Real.exp ((((S m).card : ℝ) * ((b - a) ^ 2 / 4)) * lam ^ 2 / 2) := by
    have := (hsubS (S m)).mgf_le lam
    unfold mgf at this
    refine this.trans (le_of_eq ?_)
    congr 1
    congr 1
    have hc : ((∑ i ∈ S m, (‖b - a‖₊ / 2) ^ 2 : NNReal) : ℝ) = (S m).card * ((b - a) ^ 2 / 4) := by
      push_cast
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [Real.norm_eq_abs, div_pow, sq_abs]
      ring
    rw [hc]
  -- assemble
  have hE : P.real {ω | ∃ k ≤ m, x ≤ psum X μ k ω} ≤
      ∑ k ∈ Finset.range (m + 1), P.real (A k) :=
    (measureReal_mono hcover (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le _ _)
  have hexp : 0 < Real.exp (lam * x) := Real.exp_pos _
  have h2 : Real.exp (lam * x) * ∑ k ∈ Finset.range (m + 1), P.real (A k) ≤ ∫ ω, f ω ∂P := by
    rw [Finset.mul_sum]
    exact (Finset.sum_le_sum hkey).trans hsumle
  rw [Real.exp_neg]
  rw [← div_eq_inv_mul, le_div_iff₀ hexp]
  calc P.real {ω | ∃ k ≤ m, x ≤ psum X μ k ω} * Real.exp (lam * x)
      ≤ (∑ k ∈ Finset.range (m + 1), P.real (A k)) * Real.exp (lam * x) :=
        mul_le_mul_of_nonneg_right hE hexp.le
    _ ≤ ∫ ω, f ω ∂P := by rw [mul_comm]; exact h2
    _ ≤ _ := hmgf

end MNLTriMax

namespace MNLTriL8

open MeasureTheory ProbabilityTheory UnderstandingML MNLTriMax

variable {Ω : Type*} [MeasurableSpace Ω]

theorem card_filter_lt (L ℓ : ℕ) (h : ℓ ≤ L) :
    (Finset.univ.filter (fun i : Fin L => (i : ℕ) < ℓ)).card = ℓ := by
  have himg : (Finset.univ.filter (fun i : Fin L => (i : ℕ) < ℓ)).image (fun i : Fin L => (i : ℕ)) =
      Finset.range ℓ := by
    ext n
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hn; exact ⟨⟨n, by omega⟩, hn, rfl⟩
  calc (Finset.univ.filter (fun i : Fin L => (i : ℕ) < ℓ)).card
      = ((Finset.univ.filter (fun i : Fin L => (i : ℕ) < ℓ)).image
          (fun i : Fin L => (i : ℕ))).card :=
        (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ = ℓ := by rw [himg, Finset.card_range]

theorem card_filter_le (L m : ℕ) :
    ((Finset.univ.filter (fun i : Fin L => (i : ℕ) < m)).card : ℝ) ≤ m := by
  have : (Finset.univ.filter (fun i : Fin L => (i : ℕ) < m)).card ≤ m := by
    calc _ ≤ ((Finset.univ.filter (fun i : Fin L => (i : ℕ) < m)).image
            (fun i : Fin L => (i : ℕ))).card := by
          rw [Finset.card_image_of_injective _ Fin.val_injective]
      _ ≤ (Finset.range m).card := by
          apply Finset.card_le_card
          intro n hn
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hn
          obtain ⟨i, hi, rfl⟩ := hn
          simpa using hi
      _ = m := Finset.card_range m
  exact_mod_cast this

theorem geom4 (n : ℕ) : ∑ j ∈ Finset.range n, (4 : ℝ) ^ j ≤ 4 ^ n / 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith

/-- Optimized maximal inequality: `P(∃ k ≤ m, x ≤ S_k) ≤ exp(-2x²/(m(b-a)²))`. -/
theorem max_hoeffding' (D : Measure Ω) [IsProbabilityMeasure D] (X : Ω → ℝ) (hX : Measurable X)
    {a b : ℝ} (hab : ∀ᵐ x ∂D, X x ∈ Set.Icc a b) (hab' : a < b) (L m : ℕ) (hm : 1 ≤ m)
    {x : ℝ} (hx : 0 < x) :
    (iidLaw D L).real {ω | ∃ k ≤ m, x ≤ psum X (∫ y, X y ∂D) k ω} ≤
      Real.exp (-(2 * x ^ 2 / (m * (b - a) ^ 2))) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set c := (b - a) ^ 2 / 4 with hc
  have hcpos : 0 < c := by rw [hc]; have := sub_pos.mpr hab'; positivity
  set lam := x / (m * c) with hlam
  have hlampos : 0 < lam := by rw [hlam]; positivity
  have h := max_hoeffding D X hX hab L m (x := x) hlampos
  rw [← hc] at h
  refine h.trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hcard := card_filter_le L m
  have h1 : ((Finset.univ.filter (fun i : Fin L => (i : ℕ) < m)).card : ℝ) * c * lam ^ 2 / 2 ≤
      m * c * lam ^ 2 / 2 := by
    have : 0 ≤ c * lam ^ 2 / 2 := by positivity
    nlinarith
  have h2 : -(lam * x) + m * c * lam ^ 2 / 2 = -(2 * x ^ 2 / (m * (b - a) ^ 2)) := by
    rw [hlam, hc]
    have : (b - a) ^ 2 ≠ 0 := by have := sub_pos.mpr hab'; positivity
    have : (m : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  linarith

end MNLTriL8

open MeasureTheory UnderstandingML MNLTriMax MNLTriL8 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (D : Measure Ω) [IsProbabilityMeasure D]
    (X : Ω → ℝ) (hX : Measurable X) {a b : ℝ} (hab : ∀ᵐ ω ∂D, a ≤ X ω ∧ X ω ≤ b)
    (L : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ENNReal.ofReal (1 - L * δ) ≤
      iidLaw D L {ω | ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ L →
        |(∑ i ∈ Finset.univ.filter (fun i : Fin L => (i : ℕ) < ℓ), X (ω i)) / ℓ - ∫ x, X x ∂D| ≤
          Real.sqrt (2 * (b - a) ^ 2 * Real.log (8 / (δ * ℓ)) / ℓ)} := by
  classical
  set P := iidLaw D L with hP
  haveI : IsProbabilityMeasure P := by rw [hP]; unfold iidLaw; infer_instance
  set μ := ∫ x, X x ∂D with hμ
  set G := {ω : Fin L → Ω | ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ L →
        |(∑ i ∈ Finset.univ.filter (fun i : Fin L => (i : ℕ) < ℓ), X (ω i)) / ℓ - μ| ≤
          Real.sqrt (2 * (b - a) ^ 2 * Real.log (8 / (δ * ℓ)) / ℓ)} with hG
  have habI : ∀ᵐ x ∂D, X x ∈ Set.Icc a b := hab.mono (fun x hx => hx)
  -- trivial case
  by_cases hLδ : 1 < (L : ℝ) * δ
  · rw [ENNReal.ofReal_of_nonpos (by linarith)]; exact zero_le
  push Not at hLδ
  -- it suffices to bound the complement
  suffices hc : P Gᶜ ≤ ENNReal.ofReal (L * δ) by
    have h1 : P Set.univ ≤ P G + P Gᶜ := by
      rw [← Set.union_compl_self G]; exact measure_union_le _ _
    rw [measure_univ] at h1
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
    exact tsub_le_iff_right.mpr (h1.trans (add_le_add le_rfl hc))
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · have : Gᶜ = ∅ := by
      ext ω
      simp only [Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not, hG,
        Set.mem_setOf_eq]
      intro ℓ h1 h2
      omega
    rw [this, measure_empty]; exact zero_le
  have hab_le : a ≤ b := by
    obtain ⟨x, hx⟩ := hab.exists
    linarith [hx.1, hx.2]
  rcases hab_le.eq_or_lt with heq | hlt
  · -- degenerate case: `X = a` almost surely
    subst heq
    have hXa : ∀ᵐ x ∂D, X x = a := hab.mono (fun x hx => le_antisymm hx.2 hx.1)
    have hμa : μ = a := by
      rw [hμ, integral_congr_ae hXa]; simp
    have hall : ∀ᵐ ω ∂P, ∀ i, X (ω i) = a := by
      rw [ae_all_iff]
      intro i
      exact MNLTriProb.coord_ae D L i hXa
    have hnull : P Gᶜ = 0 := by
      apply measure_mono_null _ (ae_iff.mp hall)
      intro ω hω
      simp only [Set.mem_setOf_eq]
      intro hcon
      apply hω
      simp only [hG, Set.mem_setOf_eq]
      intro ℓ hℓ1 hℓL
      have hsum : (∑ i ∈ Finset.univ.filter (fun i : Fin L => (i : ℕ) < ℓ), X (ω i)) = ℓ * a := by
        rw [Finset.sum_congr rfl (fun i _ => hcon i), Finset.sum_const, card_filter_lt L ℓ hℓL,
          nsmul_eq_mul]
      have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
      rw [hsum, hμa, mul_div_cancel_left₀ _ hℓpos.ne', sub_self, abs_zero]
      exact Real.sqrt_nonneg _
    rw [hnull]; exact zero_le
  · -- main case `a < b`
    set J := Nat.log 2 L
    let m : ℕ → ℕ := fun j => min (2 ^ (j + 1)) L
    let xj : ℕ → ℝ := fun j =>
      Real.sqrt (2 * (b - a) ^ 2 * (2 ^ j : ℝ) * Real.log (4 / (δ * 2 ^ j)))
    let Up : ℕ → Set (Fin L → Ω) := fun j => {ω | ∃ k ≤ m j, xj j ≤ psum X μ k ω}
    let Dn : ℕ → Set (Fin L → Ω) := fun j =>
      {ω | ∃ k ≤ m j, xj j ≤ psum (fun y => -X y) (∫ y, -X y ∂D) k ω}
    have hδL : ∀ ℓ : ℕ, ℓ ≤ L → δ * ℓ ≤ 1 := by
      intro ℓ hℓ
      have : (ℓ : ℝ) ≤ L := by exact_mod_cast hℓ
      nlinarith
    -- covering
    have hcover : Gᶜ ⊆ ⋃ j ∈ Finset.range (J + 1), (Up j ∪ Dn j) := by
      intro ω hω
      simp only [hG, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le] at hω
      obtain ⟨ℓ, hℓ1, hℓL, hdev⟩ := hω
      set j := Nat.log 2 ℓ with hj
      have hℓ0 : ℓ ≠ 0 := by omega
      have hjle : 2 ^ j ≤ ℓ := Nat.pow_log_le_self 2 hℓ0
      have hjlt : ℓ < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) ℓ
      have hjJ : j ≤ J := Nat.log_mono_right hℓL
      have hℓm : ℓ ≤ m j := le_min hjlt.le hℓL
      have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero hℓ0
      have hjR : (2 : ℝ) ^ j ≤ ℓ := by exact_mod_cast hjle
      have hjR2 : (ℓ : ℝ) ≤ 2 * 2 ^ j := by
        have : ℓ ≤ 2 * 2 ^ j := by rw [pow_succ] at hjlt; omega
        exact_mod_cast this
      have h2j : (0 : ℝ) < 2 ^ j := by positivity
      -- psum in terms of the sample mean
      have hps : psum X μ ℓ ω =
          (∑ i ∈ Finset.univ.filter (fun i : Fin L => (i : ℕ) < ℓ), X (ω i)) - ℓ * μ := by
        unfold psum
        rw [Finset.sum_sub_distrib, Finset.sum_const, card_filter_lt L ℓ hℓL, nsmul_eq_mul]
      set Ssum := (∑ i ∈ Finset.univ.filter (fun i : Fin L => (i : ℕ) < ℓ), X (ω i))
      have hdev' : ℓ * Real.sqrt (2 * (b - a) ^ 2 * Real.log (8 / (δ * ℓ)) / ℓ) <
          |psum X μ ℓ ω| := by
        rw [hps]
        have : Ssum - ℓ * μ = ℓ * (Ssum / ℓ - μ) := by field_simp
        rw [this, abs_mul, abs_of_pos hℓpos]
        exact mul_lt_mul_of_pos_left hdev hℓpos
      -- the block threshold is below the actual threshold
      have hlog1 : 0 ≤ Real.log (4 / (δ * 2 ^ j)) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ (by positivity)]
        have := hδL ℓ hℓL
        nlinarith
      have hlog2 : Real.log (4 / (δ * 2 ^ j)) ≤ Real.log (8 / (δ * ℓ)) := by
        apply Real.log_le_log (by positivity)
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have hxj : xj j ≤ ℓ * Real.sqrt (2 * (b - a) ^ 2 * Real.log (8 / (δ * ℓ)) / ℓ) := by
        have hnn : 0 ≤ 2 * (b - a) ^ 2 * Real.log (8 / (δ * ℓ)) / ℓ := by
          have : 0 ≤ Real.log (8 / (δ * ℓ)) := hlog1.trans hlog2
          positivity
        rw [Real.sqrt_le_iff]
        constructor
        · positivity
        · rw [mul_pow, Real.sq_sqrt hnn]
          have e : (ℓ : ℝ) ^ 2 * (2 * (b - a) ^ 2 * Real.log (8 / (δ * ℓ)) / ℓ) =
              2 * (b - a) ^ 2 * ℓ * Real.log (8 / (δ * ℓ)) := by
            field_simp
          rw [e]
          have hba : 0 ≤ 2 * (b - a) ^ 2 := by positivity
          have := mul_le_mul hjR hlog2 hlog1 hℓpos.le
          nlinarith
      have hbig : xj j ≤ |psum X μ ℓ ω| := hxj.trans hdev'.le
      simp only [Set.mem_iUnion, Finset.mem_range]
      refine ⟨j, by omega, ?_⟩
      rcases le_or_gt 0 (psum X μ ℓ ω) with hs | hs
      · left
        exact ⟨ℓ, hℓm, by rwa [abs_of_nonneg hs] at hbig⟩
      · right
        refine ⟨ℓ, hℓm, ?_⟩
        have hneg : psum (fun y => -X y) (∫ y, -X y ∂D) ℓ ω = -psum X μ ℓ ω := by
          unfold psum
          rw [integral_neg, ← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [hμ]; ring
        rw [hneg]
        rwa [abs_of_neg hs] at hbig
    -- probability bounds per block
    have hblock : ∀ j ∈ Finset.range (J + 1),
        P.real (Up j ∪ Dn j) ≤ 2 * (δ * 2 ^ j / 4) ^ 2 := by
      intro j hj
      have hjJ : j ≤ J := by simpa [Nat.lt_succ_iff] using hj
      have hL0 : 1 ≤ L := hLpos
      have h2jL : 2 ^ j ≤ L := by
        calc 2 ^ j ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) hjJ
          _ ≤ L := Nat.pow_log_le_self 2 (by omega)
      have hm1 : 1 ≤ m j := le_min (Nat.one_le_two_pow) hL0
      have hmR : ((m j : ℕ) : ℝ) ≤ 2 * 2 ^ j := by
        have : m j ≤ 2 ^ (j + 1) := min_le_left _ _
        rw [pow_succ] at this
        exact_mod_cast (show m j ≤ 2 * 2 ^ j by omega)
      have hmpos : (0 : ℝ) < m j := by exact_mod_cast hm1
      have h2j : (0 : ℝ) < 2 ^ j := by positivity
      have hδj : δ * 2 ^ j ≤ 1 := by
        have := hδL (2 ^ j) h2jL
        exact_mod_cast this
      have hlogpos : 0 < Real.log (4 / (δ * 2 ^ j)) := by
        apply Real.log_pos
        rw [lt_div_iff₀ (by positivity)]
        linarith
      have hba : 0 < b - a := sub_pos.mpr hlt
      have hQpos : 0 < 2 * (b - a) ^ 2 * (2 ^ j : ℝ) * Real.log (4 / (δ * 2 ^ j)) := by
        positivity
      have hxpos : 0 < xj j := Real.sqrt_pos.mpr hQpos
      have hxsq : xj j ^ 2 = 2 * (b - a) ^ 2 * (2 ^ j : ℝ) * Real.log (4 / (δ * 2 ^ j)) :=
        Real.sq_sqrt hQpos.le
      -- exponent bound
      have hexp : Real.exp (-(2 * xj j ^ 2 / ((m j : ℝ) * (b - a) ^ 2))) ≤ (δ * 2 ^ j / 4) ^ 2 := by
        have hge : 2 * Real.log (4 / (δ * 2 ^ j)) ≤ 2 * xj j ^ 2 / ((m j : ℝ) * (b - a) ^ 2) := by
          rw [le_div_iff₀ (by positivity), hxsq]
          have : 0 ≤ Real.log (4 / (δ * 2 ^ j)) := hlogpos.le
          nlinarith
        calc Real.exp (-(2 * xj j ^ 2 / ((m j : ℝ) * (b - a) ^ 2)))
            ≤ Real.exp (-(2 * Real.log (4 / (δ * 2 ^ j)))) := Real.exp_le_exp.mpr (by linarith)
          _ = (δ * 2 ^ j / 4) ^ 2 := by
            rw [← Real.log_rpow (by positivity), Real.exp_neg, Real.exp_log (by positivity)]
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            field_simp
      have hUp : P.real (Up j) ≤ (δ * 2 ^ j / 4) ^ 2 :=
        (max_hoeffding' D X hX habI hlt L (m j) hm1 hxpos).trans hexp
      have habN : ∀ᵐ x ∂D, -X x ∈ Set.Icc (-b) (-a) :=
        habI.mono (fun x hx => ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩)
      have hDn : P.real (Dn j) ≤ (δ * 2 ^ j / 4) ^ 2 := by
        have := max_hoeffding' D (fun y => -X y) hX.neg habN (by linarith) L (m j) hm1 hxpos
        refine this.trans (le_trans (le_of_eq ?_) hexp)
        congr 3
        ring
      calc P.real (Up j ∪ Dn j) ≤ P.real (Up j) + P.real (Dn j) := measureReal_union_le _ _
        _ ≤ _ := by linarith
    -- summing
    have hsum : P.real Gᶜ ≤ L * δ := by
      calc P.real Gᶜ ≤ P.real (⋃ j ∈ Finset.range (J + 1), (Up j ∪ Dn j)) :=
            measureReal_mono hcover (measure_ne_top _ _)
        _ ≤ ∑ j ∈ Finset.range (J + 1), P.real (Up j ∪ Dn j) :=
            measureReal_biUnion_finset_le _ _
        _ ≤ ∑ j ∈ Finset.range (J + 1), 2 * (δ * 2 ^ j / 4) ^ 2 := Finset.sum_le_sum hblock
        _ = δ ^ 2 / 8 * ∑ j ∈ Finset.range (J + 1), (4 : ℝ) ^ j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            rw [show (4 : ℝ) ^ j = (2 ^ j) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
            ring
        _ ≤ δ ^ 2 / 8 * (4 ^ (J + 1) / 3) :=
            mul_le_mul_of_nonneg_left (geom4 (J + 1)) (by positivity)
        _ ≤ L * δ := by
            have h4J : (4 : ℝ) ^ J ≤ (L : ℝ) ^ 2 := by
              have hJL : 2 ^ J ≤ L := Nat.pow_log_le_self 2 (by omega)
              have : ((2 : ℝ) ^ J) ≤ L := by exact_mod_cast hJL
              rw [show (4 : ℝ) ^ J = (2 ^ J) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
              exact pow_le_pow_left₀ (by positivity) this 2
            have h5 : δ ^ 2 * 4 ^ J ≤ δ ^ 2 * (L : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_left h4J (by positivity)
            have hLδ0 : 0 ≤ (L : ℝ) * δ := by positivity
            have h6 : ((L : ℝ) * δ) ^ 2 ≤ L * δ := by nlinarith
            calc δ ^ 2 / 8 * (4 ^ (J + 1) / 3) = (δ ^ 2 * 4 ^ J) / 6 := by
                  rw [pow_succ]; ring
              _ ≤ (δ ^ 2 * (L : ℝ) ^ 2) / 6 := by linarith
              _ = ((L : ℝ) * δ) ^ 2 / 6 := by ring
              _ ≤ L * δ := by linarith
    calc P Gᶜ = ENNReal.ofReal (P.real Gᶜ) := (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (L * δ) := ENNReal.ofReal_le_ofReal hsum
