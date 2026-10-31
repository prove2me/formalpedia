-- Prove2me | solution 1 for InventoryAnomaly.EW.lemma_16
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T09:17:05.557042+00:00
-- url     : https://prove2.me/submissions/d90f6fe5-fd53-4fb4-b020-758a0d78a349
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_InventoryAnomaly_EW_Model
import Theorems.Thm_InventoryAnomaly_EW_theorem_2
import Theorems.Thm_InventoryAnomaly_EW_lemma_14

open MeasureTheory ProbabilityTheory
open scoped NNReal Nat
open InventoryAnomaly.EW

open Classical in
lemma IA1_bind_mk_apply {α β : Type} (p : PMF α) (f : α → PMF β) (a : α) (b : β) :
    (p.bind fun x => (f x).map (Prod.mk x)) (a, b) = p a * f a b := by
  rw [PMF.bind_apply]
  have : ∀ x, ((f x).map (Prod.mk x)) (a, b) = if a = x then f a b else 0 := by
    intro x
    rw [PMF.map_apply]
    by_cases h : a = x
    · subst h
      rw [tsum_eq_single b]
      · simp
      · intro b' hb'; simp [Ne.symm hb']
    · simp [h]
  simp_rw [this, mul_ite, mul_zero]
  rw [tsum_eq_single a (fun x hx => by simp [Ne.symm hx])]; simp

lemma IA1_mix (p0 : ℝ≥0) (h : p0 ≤ 1) (src : Bool → PMF ℕ) :
    ((PMF.bernoulli p0 h).bind fun b => (src b).map (Prod.mk b)).toMeasure =
      (p0 : ENNReal) • ((src true).toMeasure.map (Prod.mk true)) +
        ((1 - p0 : ℝ≥0) : ENNReal) • ((src false).toMeasure.map (Prod.mk false)) := by
  rw [Measure.ext_iff_singleton]
  rintro ⟨b, k⟩
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), IA1_bind_mk_apply,
    PMF.bernoulli_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply measurable_prodMk_left (measurableSet_singleton _),
    Measure.map_apply measurable_prodMk_left (measurableSet_singleton _)]
  cases b
  · have h1 : Prod.mk true ⁻¹' {((false, k) : Bool × ℕ)} = ∅ := by ext; simp
    have h2 : Prod.mk false ⁻¹' {((false, k) : Bool × ℕ)} = {k} := by ext; simp
    rw [h1, h2, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp
  · have h1 : Prod.mk true ⁻¹' {((true, k) : Bool × ℕ)} = {k} := by ext; simp
    have h2 : Prod.mk false ⁻¹' {((true, k) : Bool × ℕ)} = ∅ := by ext; simp
    rw [h1, h2, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp

lemma IA1_int_mix (p0 : ℝ≥0) (h : p0 ≤ 1) (src : Bool → PMF ℕ) (G : Bool × ℕ → ℝ)
    (h1 : Integrable (fun k => G (true, k)) (src true).toMeasure)
    (h2 : Integrable (fun k => G (false, k)) (src false).toMeasure) :
    ∫ y, G y ∂((PMF.bernoulli p0 h).bind fun b => (src b).map (Prod.mk b)).toMeasure =
      (p0 : ℝ) * ∫ k, G (true, k) ∂(src true).toMeasure +
        (1 - (p0 : ℝ)) * ∫ k, G (false, k) ∂(src false).toMeasure := by
  rw [IA1_mix]
  have i1 : Integrable G ((src true).toMeasure.map (Prod.mk true)) :=
    (integrable_map_measure Measurable.of_discrete.aestronglyMeasurable
      measurable_prodMk_left.aemeasurable).2 h1
  have i2 : Integrable G ((src false).toMeasure.map (Prod.mk false)) :=
    (integrable_map_measure Measurable.of_discrete.aestronglyMeasurable
      measurable_prodMk_left.aemeasurable).2 h2
  rw [integral_add_measure (i1.smul_measure ENNReal.coe_ne_top)
      (i2.smul_measure ENNReal.coe_ne_top), integral_smul_measure, integral_smul_measure,
    integral_map measurable_prodMk_left.aemeasurable Measurable.of_discrete.aestronglyMeasurable,
    integral_map measurable_prodMk_left.aemeasurable Measurable.of_discrete.aestronglyMeasurable]
  have e1 : (((1 - p0 : ℝ≥0) : ENNReal)).toReal = 1 - (p0 : ℝ) := by
    rw [ENNReal.coe_toReal, NNReal.coe_sub h, NNReal.coe_one]
  rw [e1, ENNReal.coe_toReal, smul_eq_mul, smul_eq_mul]

/-- Law of the sales value of entry `(i,j)` given the anomaly indicator `b`. -/
noncomputable def IA1_src {d : ℕ} (I : Instance d) (ij : Fin I.n × Fin I.m) (b : Bool) : PMF ℕ :=
  if b then I.model.anom I.αstar (I.Mstar ij.1 ij.2).toNNReal
  else poissonPMF (I.Mstar ij.1 ij.2).toNNReal

/-- Joint law of (anomaly indicator, sales) of entry `(i,j)`. -/
noncomputable def IA1_D {d : ℕ} (I : Instance d) (ij : Fin I.n × Fin I.m) : PMF (Bool × ℕ) :=
  (PMF.bernoulli (min I.pAstar 1) (min_le_right _ _)).bind fun b => (IA1_src I ij b).map (Prod.mk b)

lemma IA1_entry {d : ℕ} (I : Instance d) (ij : Fin I.n × Fin I.m) :
    (I.entryPMF ij).toMeasure =
      (PMF.bernoulli (min I.pO 1) (min_le_right _ _)).toMeasure.prod (IA1_D I ij).toMeasure := by
  have hE : I.entryPMF ij = (PMF.bernoulli (min I.pO 1) (min_le_right _ _)).bind
      fun o => (IA1_D I ij).map (Prod.mk o) := by
    unfold Instance.entryPMF
    congr 1
    funext o
    simp only [IA1_D, PMF.map_bind, PMF.map_comp]
    rfl
  rw [Measure.ext_iff_singleton]
  rintro ⟨o, y⟩
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    ← Set.singleton_prod_singleton, Measure.prod_prod,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), hE, IA1_bind_mk_apply]

lemma IA1s_model_mono {d : ℕ} {I : Instance d} {cM cA Csp Csp' K L μ : ℝ}
    (hI : I.Model cM cA Csp K L μ) (hle : Csp' ≤ Csp) : I.Model cM cA Csp' K L μ := by
  have hn0 : 0 < I.n := by have := hI.two_le_m; have := hI.m_le_n; omega
  have hμ : 0 ≤ μ := by
    have h := hI.incoh_U ⟨0, hn0⟩
    have h0 : 0 ≤ ∑ k, I.U ⟨0, hn0⟩ k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    by_contra hneg'
    have hneg : μ < 0 := lt_of_not_ge hneg'
    have hr' : (0 : ℝ) < I.r := by exact_mod_cast hI.r_pos
    have hn' : (0 : ℝ) < I.n := by exact_mod_cast hn0
    have : μ * I.r / I.n < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg hr') hn'
    linarith
  refine { hI with sparsity := ?_ }
  have hX : 0 ≤ Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * I.κ hI.r_pos ^ 2 / Real.sqrt I.m := by
    have : 0 ≤ Real.log I.m := Real.log_natCast_nonneg _
    positivity
  have h := hI.sparsity
  calc Csp' * Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * I.κ hI.r_pos ^ 2 / Real.sqrt I.m
      = Csp' * (Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * I.κ hI.r_pos ^ 2 / Real.sqrt I.m) := by ring
    _ ≤ Csp * (Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * I.κ hI.r_pos ^ 2 / Real.sqrt I.m) :=
        mul_le_mul_of_nonneg_right hle hX
    _ = _ := by ring
    _ ≤ _ := h

lemma IA1s_spmax_mono {d : ℕ} {I : Instance d} {cM cA Csp Csp' K L μ : ℝ}
    (hI : I.Model cM cA Csp K L μ) (hS : I.SparsityMax hI.r_pos Csp μ L) (hle : Csp' ≤ Csp) :
    I.SparsityMax hI.r_pos Csp' μ L := by
  have hn0 : 0 < I.n := by have := hI.two_le_m; have := hI.m_le_n; omega
  have hm0 : 0 < I.m := by have := hI.two_le_m; omega
  have hL : 0 ≤ L := (abs_nonneg _).trans (hI.max_ub ⟨0, hn0⟩ ⟨0, hm0⟩)
  have hμ : 0 ≤ μ := by
    have h := hI.incoh_U ⟨0, hn0⟩
    have h0 : 0 ≤ ∑ k, I.U ⟨0, hn0⟩ k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    by_contra hneg'
    have hneg : μ < 0 := lt_of_not_ge hneg'
    have hr' : (0 : ℝ) < I.r := by exact_mod_cast hI.r_pos
    have hn' : (0 : ℝ) < I.n := by exact_mod_cast hn0
    have : μ * I.r / I.n < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg hr') hn'
    linarith
  intro i₀ j₀ hmax
  have h := hS i₀ j₀ hmax
  have hM0 : 0 ≤ I.Mstar i₀ j₀ := hI.nonneg i₀ j₀
  have hX : 0 ≤ Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * L * I.κ hI.r_pos ^ 2 /
      (I.Mstar i₀ j₀ * Real.sqrt I.m) := by
    have : 0 ≤ Real.log I.m := Real.log_natCast_nonneg _
    positivity
  calc Csp' * Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * L * I.κ hI.r_pos ^ 2 /
        (I.Mstar i₀ j₀ * Real.sqrt I.m)
      = Csp' * (Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * L * I.κ hI.r_pos ^ 2 /
        (I.Mstar i₀ j₀ * Real.sqrt I.m)) := by ring
    _ ≤ Csp * (Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * L * I.κ hI.r_pos ^ 2 /
        (I.Mstar i₀ j₀ * Real.sqrt I.m)) := mul_le_mul_of_nonneg_right hle hX
    _ = _ := by ring
    _ ≤ _ := h


lemma IA1s_mu_ge_one {d : ℕ} {I : Instance d} {cM cA Csp K L μ : ℝ}
    (hI : I.Model cM cA Csp K L μ) : 1 ≤ μ := by
  have hn0 : 0 < I.n := by have := hI.two_le_m; have := hI.m_le_n; omega
  have hcol : ∀ k, ∑ i, I.U i k ^ 2 = 1 := by
    intro k
    have h := congrFun (congrFun hI.U_orth k) k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    simpa [sq] using h
  have hsum : ∑ i, ∑ k, I.U i k ^ 2 = I.r := by
    rw [Finset.sum_comm]; simp [hcol]
  have hle : ∑ i, ∑ k, I.U i k ^ 2 ≤ ∑ _i : Fin I.n, μ * I.r / I.n :=
    Finset.sum_le_sum fun i _ => hI.incoh_U i
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
  have hn' : (0 : ℝ) < I.n := by exact_mod_cast hn0
  have hr' : (0 : ℝ) < I.r := by exact_mod_cast hI.r_pos
  rw [mul_div_cancel₀ _ hn'.ne'] at hle
  nlinarith

lemma IA1s_kappa_ge_one {d : ℕ} {I : Instance d} {cM cA Csp K L μ : ℝ}
    (hI : I.Model cM cA Csp K L μ) : 1 ≤ I.κ hI.r_pos := by
  unfold Instance.κ
  have h1 := hI.σ_pos ⟨I.r - 1, by have := hI.r_pos; omega⟩
  have h2 : I.σ ⟨I.r - 1, by have := hI.r_pos; omega⟩ ≤ I.σ ⟨0, hI.r_pos⟩ :=
    hI.σ_anti (Fin.mk_le_mk.2 (Nat.zero_le _))
  rw [one_le_div h1]; exact h2

lemma IA18_poisPmf_le_one (M : ℝ) (k : ℕ) : poisPmf M k ≤ 1 := by
  unfold poisPmf
  have h := hasSum_one_poissonMeasure M.toNNReal
  have := le_hasSum h k (fun j _ => by positivity)
  simpa [poissonPMFReal] using this

lemma IA18_poisPmf_nonneg (M : ℝ) (k : ℕ) : 0 ≤ poisPmf M k := by
  unfold poisPmf poissonPMFReal; positivity

lemma IA18_pmf_bounds {d : ℕ} (A : AnomModel d) (α : EuclideanSpace ℝ (Fin d)) (M : ℝ) (k : ℕ) :
    0 ≤ A.pmf α M k ∧ A.pmf α M k ≤ 1 := by
  unfold AnomModel.pmf
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using (A.anom α M.toNNReal).coe_le_one k)

lemma IA18_clamp01 (z : ℝ) : 0 ≤ clamp01 z ∧ clamp01 z ≤ 1 := by
  unfold clamp01
  exact ⟨le_max_right _ _, max_le (min_le_right _ _) zero_le_one⟩


lemma IA18_alpha_star {d : ℕ} (I : Instance d) : alphaOf I.θstar = I.αstar := by
  ext i; simp [alphaOf, Instance.θstar]

lemma IA18_pA_star {d : ℕ} (I : Instance d) : pAOf I.θstar = I.pAstar := by
  simp [pAOf, Instance.θstar]

lemma IA18_pois_le1 (j : ℕ) (t : ℝ) (ht : 0 ≤ t) : Real.exp (-t) * t ^ j / (j ! : ℝ) ≤ 1 := by
  have h := Real.pow_div_factorial_le_exp t ht j
  rw [mul_div_assoc]
  calc Real.exp (-t) * (t ^ j / j !) ≤ Real.exp (-t) * Real.exp t := by gcongr
    _ = 1 := by rw [← Real.exp_add]; simp

/-- The Poisson weights are `1`-Lipschitz in the mean on `[0, ∞)`. -/
lemma IA18_pois_lip_core (k : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) * x ^ k / (k ! : ℝ) - Real.exp (-y) * y ^ k / (k ! : ℝ)| ≤ |x - y| := by
  have hge0 : ∀ (j : ℕ) (t : ℝ), 0 ≤ t → 0 ≤ Real.exp (-t) * t ^ j / (j ! : ℝ) := by
    intro j t ht; positivity
  have key : ∀ f' : ℝ → ℝ, (∀ t, HasDerivAt (fun t => Real.exp (-t) * t ^ k / (k ! : ℝ)) (f' t) t) →
      (∀ t, 0 ≤ t → |f' t| ≤ 1) →
      |Real.exp (-x) * x ^ k / (k ! : ℝ) - Real.exp (-y) * y ^ k / (k ! : ℝ)| ≤ |x - y| := by
    intro f' hd hb
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun t => Real.exp (-t) * t ^ k / (k ! : ℝ)) (f' := f') (s := Set.Ici (0 : ℝ))
      (fun t _ => (hd t).hasDerivWithinAt)
      (fun t ht => by rw [Real.norm_eq_abs]; exact hb t ht) (convex_Ici 0) hy hx
    simpa [Real.norm_eq_abs] using this
  have hbase : ∀ t, HasDerivAt (fun t => Real.exp (-t) * t ^ k / (k ! : ℝ))
      ((Real.exp (-t) * -1 * t ^ k + Real.exp (-t) * ((k : ℝ) * t ^ (k - 1))) / (k ! : ℝ)) t := by
    intro t
    exact (((hasDerivAt_neg t).exp).mul (hasDerivAt_pow k t)).div_const _
  rcases k with _ | j
  · refine key (fun t => -Real.exp (-t)) (fun t => (hbase t).congr_deriv (by simp)) ?_
    intro t ht
    rw [abs_neg, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by linarith)
  · refine key (fun t => Real.exp (-t) * t ^ j / (j ! : ℝ) -
        Real.exp (-t) * t ^ (j + 1) / ((j + 1) ! : ℝ)) (fun t => (hbase t).congr_deriv ?_) ?_
    · have : (j ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
      simp only [Nat.add_sub_cancel, Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · intro t ht
      have a1 := IA18_pois_le1 j t ht
      have a2 := IA18_pois_le1 (j + 1) t ht
      have b1 := hge0 j t ht
      have b2 := hge0 (j + 1) t ht
      rw [abs_le]; constructor <;> linarith

lemma IA18_pois_lip (k : ℕ) (a b : ℝ) (hb : 0 ≤ b) : |poisPmf a k - poisPmf b k| ≤ |a - b| := by
  unfold poisPmf poissonPMFReal
  rw [Real.coe_toNNReal', Real.coe_toNNReal', max_eq_left hb]
  refine (IA18_pois_lip_core k (le_max_right a 0) hb).trans ?_
  rcases le_total a 0 with h | h
  · rw [max_eq_right h, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · rw [max_eq_left h]

lemma IA18_pmf_max {d : ℕ} (A : AnomModel d) (α : EuclideanSpace ℝ (Fin d)) (M : ℝ) (k : ℕ) :
    A.pmf α M k = A.pmf α (max M 0) k := by
  unfold AnomModel.pmf
  congr 3
  apply NNReal.eq
  rw [Real.coe_toNNReal', Real.coe_toNNReal', max_eq_left (le_max_right M 0)]


section transport
variable {d : ℕ}

/-- Two independent copies of every entry: the observation coin is read from the left copy,
the (anomaly, sales) pair from the right copy. -/
abbrev IA16_Ω2 (I : Instance d) := (Fin I.n × Fin I.m) ⊕ (Fin I.n × Fin I.m) → Entry

noncomputable def IA16_Q (I : Instance d) : Measure (IA16_Ω2 I) :=
  Measure.pi fun k => (I.entryPMF (Sum.elim id id k)).toMeasure

def IA16_ψ (I : Instance d) (ω : IA16_Ω2 I) : I.Sample :=
  fun ij => ((ω (Sum.inl ij)).1, (ω (Sum.inr ij)).2)

instance IA16_Q_prob (I : Instance d) : IsProbabilityMeasure (IA16_Q I) := by
  unfold IA16_Q; infer_instance

lemma IA16_entry_fst (I : Instance d) (ij : Fin I.n × Fin I.m) (o : Bool) :
    (I.entryPMF ij).toMeasure {e | e.1 = o} =
      (PMF.bernoulli (min I.pO 1) (min_le_right _ _)).toMeasure {o} := by
  rw [IA1_entry]
  have : {e : Entry | e.1 = o} = {o} ×ˢ (Set.univ : Set (Bool × ℕ)) := by ext e; simp
  rw [this, Measure.prod_prod, measure_univ, mul_one]

lemma IA16_entry_snd (I : Instance d) (ij : Fin I.n × Fin I.m) (y : Bool × ℕ) :
    (I.entryPMF ij).toMeasure {e | e.2 = y} = (IA1_D I ij).toMeasure {y} := by
  rw [IA1_entry]
  have : {e : Entry | e.2 = y} = (Set.univ : Set Bool) ×ˢ {y} := by ext e; simp
  rw [this, Measure.prod_prod, measure_univ, one_mul]

lemma IA16_entry_single (I : Instance d) (ij : Fin I.n × Fin I.m) (x : Entry) :
    (I.entryPMF ij).toMeasure {x} =
      (PMF.bernoulli (min I.pO 1) (min_le_right _ _)).toMeasure {x.1} *
        (IA1_D I ij).toMeasure {x.2} := by
  obtain ⟨o, y⟩ := x
  rw [IA1_entry, ← Set.singleton_prod_singleton, Measure.prod_prod]

lemma IA16_law_eq (I : Instance d) : Measure.map (IA16_ψ I) (IA16_Q I) = I.law := by
  rw [Measure.ext_iff_singleton]
  intro x
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)]
  have hpre : IA16_ψ I ⁻¹' {x} = Set.univ.pi (fun k : (Fin I.n × Fin I.m) ⊕ (Fin I.n × Fin I.m) =>
      Sum.elim (fun ij => {e : Entry | e.1 = (x ij).1})
        (fun ij => {e : Entry | e.2 = (x ij).2}) k) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ_pi]
    constructor
    · rintro rfl k
      cases k <;> simp [IA16_ψ]
    · intro h
      funext ij
      have h1 := h (Sum.inl ij)
      have h2 := h (Sum.inr ij)
      simp only [Sum.elim_inl, Sum.elim_inr, Set.mem_setOf_eq] at h1 h2
      simp only [IA16_ψ, h1, h2]
  rw [hpre, IA16_Q, Measure.pi_pi, Fintype.prod_sum_type]
  unfold Instance.law
  rw [Measure.pi_singleton, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ij _ => ?_
  simp only [Sum.elim_inl, Sum.elim_inr, id]
  rw [IA16_entry_fst, IA16_entry_snd, IA16_entry_single]

lemma IA16_real (I : Instance d) (S : Set I.Sample) :
    I.law.real S = (IA16_Q I).real (IA16_ψ I ⁻¹' S) := by
  rw [← IA16_law_eq, measureReal_def, measureReal_def,
    Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]

end transport

/-- Lemma 14 transported to the sampling law of an instance. -/
lemma IA16_conc : ∃ C : ℝ, 0 < C ∧ ∀ {d : ℕ} (I : Instance d) (τ : ℕ → ℝ),
    (∀ k, 0 ≤ τ k ∧ τ k ≤ 1) → 0 < I.n → 0 < I.m → (I.pO : ℝ) ≤ 1 →
    1 - 1 / ((I.n : ℝ) * I.m) ≤ I.law.real {x | |∑ ij, (if (x ij).1 then (1 : ℝ) else 0) *
        τ (x ij).2.2 - ∑ ij, (I.pO : ℝ) * ∫ e, τ e.2.2 ∂(I.entryPMF ij).toMeasure| ≤
      C * (Real.sqrt ((∑ ij, (I.pO : ℝ) * ∫ e, τ e.2.2 ∂(I.entryPMF ij).toMeasure) *
        Real.log (I.m * I.n)) + Real.log (I.m * I.n))} := by
  obtain ⟨C, hC, H⟩ := lemma_14
  refine ⟨C, hC, fun {d} I τ hτ hn hm hpO => ?_⟩
  set O : (Fin I.n × Fin I.m) → IA16_Ω2 I → ℝ := fun ij ω =>
    if (ω (Sum.inl ij)).1 then 1 else 0 with hOdef
  set T : (Fin I.n × Fin I.m) → IA16_Ω2 I → ℝ := fun ij ω => τ (ω (Sum.inr ij)).2.2 with hTdef
  set p : (Fin I.n × Fin I.m) → ℝ := fun ij => ∫ e, τ e.2.2 ∂(I.entryPMF ij).toMeasure with hp
  have hind : iIndepFun (fun k => Sum.elim O T k) (IA16_Q I) := by
    unfold IA16_Q
    have := iIndepFun_pi (μ := fun k => (I.entryPMF (Sum.elim id id k)).toMeasure)
      (X := fun k => Sum.elim (fun _ (e : Entry) => if e.1 then (1 : ℝ) else 0)
        (fun _ (e : Entry) => τ e.2.2) k)
      (fun k => Measurable.of_discrete.aemeasurable)
    convert this using 1
    funext k ω
    cases k <;> rfl
  have hO : ∀ ij ω, O ij ω = 0 ∨ O ij ω = 1 := by
    intro ij ω; simp only [hOdef]; split_ifs <;> simp
  have hOp : ∀ ij, (IA16_Q I).real {ω | O ij ω = 1} = I.pO := by
    intro ij
    have hset : {ω | O ij ω = 1} =
        Function.eval (Sum.inl ij) ⁻¹' {e : Entry | e.1 = true} := by
      ext ω
      simp only [hOdef, Set.mem_setOf_eq, Set.mem_preimage, Function.eval]
      split_ifs with h <;> simp [h]
    unfold IA16_Q
    rw [hset, measureReal_def, (measurePreserving_eval _ (Sum.inl ij)).measure_preimage
      MeasurableSet.of_discrete.nullMeasurableSet]
    simp only [Sum.elim_inl, id]
    rw [IA16_entry_fst, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.bernoulli_apply]
    have : min I.pO 1 = I.pO := min_eq_left (by exact_mod_cast hpO)
    simp [this]
  have hT : ∀ ij ω, 0 ≤ T ij ω ∧ T ij ω ≤ 1 := fun ij ω => hτ _
  have hTp : ∀ ij, ∫ ω, T ij ω ∂(IA16_Q I) = p ij := by
    intro ij
    simp only [hTdef, hp, IA16_Q]
    exact integral_comp_eval (X := fun _ : (Fin I.n × Fin I.m) ⊕ (Fin I.n × Fin I.m) => Entry)
      (μ := fun k => (I.entryPMF (Sum.elim id id k)).toMeasure)
      (i := Sum.inr ij) (f := fun e : Entry => τ e.2.2)
      Measurable.of_discrete.aestronglyMeasurable
  have key := H (IA16_Q I) (n := I.n) (m := I.m) I.pO O T p hn hm I.pO.2 hpO
    (fun _ => Measurable.of_discrete) (fun _ => Measurable.of_discrete) hind hO hOp hT hTp
  rw [IA16_real]
  exact key

lemma IA16_pmf_int_ind (P : PMF ℕ) (t : ℕ) :
    ∫ k, (if k ≤ t then (1 : ℝ) else 0) ∂P.toMeasure =
      ∑ k ∈ Finset.range (t + 1), (P k).toReal := by
  rw [PMF.integral_eq_tsum _ _ (Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun k => by split_ifs <;> simp))]
  rw [tsum_eq_sum (s := Finset.range (t + 1))]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have : k ≤ t := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    simp [this]
  · intro k hk
    have : ¬ k ≤ t := fun h => hk (Finset.mem_range.2 (Nat.lt_succ_of_le h))
    simp [this]

lemma IA16_mean_ind {d : ℕ} (I : Instance d) (hpA : (I.pAstar : ℝ) ≤ 1) (ij : Fin I.n × Fin I.m)
    (t : ℕ) :
    ∫ e, (if e.2.2 ≤ t then (1 : ℝ) else 0) ∂(I.entryPMF ij).toMeasure =
      (I.pAstar : ℝ) * I.model.cdf I.αstar (I.Mstar ij.1 ij.2) t +
        (1 - (I.pAstar : ℝ)) * poisCdf (I.Mstar ij.1 ij.2) t := by
  rw [IA1_entry, integral_fun_snd (fun y : Bool × ℕ => if y.2 ≤ t then (1 : ℝ) else 0)]
  simp only [probReal_univ, one_smul]
  unfold IA1_D
  rw [IA1_int_mix _ _ _ _ (Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun k => by simp only; split_ifs <;> simp))
    (Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun k => by simp only; split_ifs <;> simp))]
  have hmin : ((min I.pAstar 1 : ℝ≥0) : ℝ) = I.pAstar := by
    rw [min_eq_left (by exact_mod_cast hpA)]
  rw [hmin]
  simp only [IA1_src, if_true, Bool.false_eq_true, if_false]
  rw [IA16_pmf_int_ind, IA16_pmf_int_ind]
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold poisPmf
  rw [← poissonPMFReal_ofReal_eq_poissonPMF, ENNReal.toReal_ofReal poissonPMFReal_nonneg]

lemma IA16_mean_one {d : ℕ} (I : Instance d) (ij : Fin I.n × Fin I.m) :
    ∫ e, (fun _ : ℕ => (1 : ℝ)) (e : Entry).2.2 ∂(I.entryPMF ij).toMeasure = 1 := by
  simp

lemma IA16_gt_star {d : ℕ} (I : Instance d) (t : ℕ) :
    I.gt I.θstar I.Mstar t = (1 / (I.n * I.m : ℝ)) * ∑ ij : Fin I.n × Fin I.m,
      ((I.pAstar : ℝ) * I.model.cdf I.αstar (I.Mstar ij.1 ij.2) t +
        (1 - (I.pAstar : ℝ)) * poisCdf (I.Mstar ij.1 ij.2) t) := by
  unfold Instance.gt
  rw [IA18_alpha_star, IA18_pA_star, Fintype.sum_prod_type]

lemma IA16_card_omega {d : ℕ} (I : Instance d) (ω : I.Sample) :
    ((I.omega (I.obs ω)).card : ℝ) = ∑ ij, (if (ω ij).1 then (1 : ℝ) else 0) * 1 := by
  unfold Instance.omega
  rw [Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun ij _ => ?_
  cases h : (ω ij).1 <;> simp [Instance.obs, h]

lemma IA16_card_filter {d : ℕ} (I : Instance d) (ω : I.Sample) (t : ℕ) :
    ((((I.omega (I.obs ω)).filter fun ij => ((I.obs ω ij).getD 0) ≤ t).card : ℕ) : ℝ) =
      ∑ ij, (if (ω ij).1 then (1 : ℝ) else 0) * (if (ω ij).2.2 ≤ t then (1 : ℝ) else 0) := by
  unfold Instance.omega
  rw [Finset.filter_filter, Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun ij _ => ?_
  cases h : (ω ij).1 <;> by_cases h2 : (ω ij).2.2 ≤ t <;> simp [Instance.obs, h, h2]

lemma IA16_gt_eq {d : ℕ} (I : Instance d) (M : Matrix (Fin I.n) (Fin I.m) ℝ) (t : ℕ) :
    I.gt I.θstar M t = (1 / (I.n * I.m : ℝ)) * ∑ ij : Fin I.n × Fin I.m,
      ((I.pAstar : ℝ) * I.model.cdf I.αstar (M ij.1 ij.2) t +
        (1 - (I.pAstar : ℝ)) * poisCdf (M ij.1 ij.2) t) := by
  unfold Instance.gt
  rw [IA18_alpha_star, IA18_pA_star, Fintype.sum_prod_type]

lemma IA16_cdf_lip {d : ℕ} (I : Instance d) {cM cA Csp K L μ : ℝ}
    (hI : I.Model cM cA Csp K L μ) (hK : 0 ≤ K) (a b : ℝ) (hb : 0 ≤ b) (t : ℕ) :
    |I.model.cdf I.αstar a t - I.model.cdf I.αstar b t| ≤ (t + 1) * (K * |a - b|) := by
  unfold AnomModel.cdf
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hk : ∀ k ∈ Finset.range (t + 1),
      |I.model.pmf I.αstar a k - I.model.pmf I.αstar b k| ≤ K * |a - b| := by
    intro k _
    rw [IA18_pmf_max I.model I.αstar a k]
    have hsm := hI.smooth k (I.αstar, max a 0) ⟨hI.α_mem, Set.mem_Ici.2 (le_max_right _ _)⟩
      (I.αstar, b) ⟨hI.α_mem, Set.mem_Ici.2 hb⟩
    refine hsm.trans (mul_le_mul_of_nonneg_left ?_ hK)
    rw [Prod.dist_eq, dist_self, Real.dist_eq]
    refine max_le (abs_nonneg _) ?_
    rcases le_total a 0 with h | h
    · rw [max_eq_right h, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
    · rw [max_eq_left h]
  calc _ ≤ ∑ _k ∈ Finset.range (t + 1), K * |a - b| := Finset.sum_le_sum hk
    _ = _ := by simp

lemma IA16_poisCdf_lip (a b : ℝ) (hb : 0 ≤ b) (t : ℕ) :
    |poisCdf a t - poisCdf b t| ≤ (t + 1) * |a - b| := by
  unfold poisCdf
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _k ∈ Finset.range (t + 1), |a - b| :=
        Finset.sum_le_sum fun k _ => IA18_pois_lip k a b hb
    _ = _ := by simp

lemma IA16_partA {d : ℕ} (I : Instance d) {cM cA Csp K L μ : ℝ}
    (hI : I.Model cM cA Csp K L μ) (hK : 0 ≤ K) (M' : Matrix (Fin I.n) (Fin I.m) ℝ) (B : ℝ)
    (hB : ∀ i j, |M' i j - I.Mstar i j| ≤ B) (t : ℕ) (hpA1 : (I.pAstar : ℝ) ≤ 1) :
    |I.gt I.θstar M' t - I.gt I.θstar I.Mstar t| ≤ (t + 1) * ((K + 1) * B) := by
  have hn0 : 0 < I.n := by have := hI.two_le_m; have := hI.m_le_n; omega
  have hm0 : 0 < I.m := by have := hI.two_le_m; omega
  have hpA0 : (0 : ℝ) ≤ I.pAstar := I.pAstar.2
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB ⟨0, hn0⟩ ⟨0, hm0⟩)
  rw [IA16_gt_eq, IA16_gt_eq, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (by positivity)]
  have hentry : ∀ ij : Fin I.n × Fin I.m,
      |((I.pAstar : ℝ) * I.model.cdf I.αstar (M' ij.1 ij.2) t +
          (1 - (I.pAstar : ℝ)) * poisCdf (M' ij.1 ij.2) t) -
        ((I.pAstar : ℝ) * I.model.cdf I.αstar (I.Mstar ij.1 ij.2) t +
          (1 - (I.pAstar : ℝ)) * poisCdf (I.Mstar ij.1 ij.2) t)| ≤ (t + 1) * ((K + 1) * B) := by
    intro ij
    have h0 := hI.nonneg ij.1 ij.2
    have c1 := IA16_cdf_lip I hI hK (M' ij.1 ij.2) (I.Mstar ij.1 ij.2) h0 t
    have c2 := IA16_poisCdf_lip (M' ij.1 ij.2) (I.Mstar ij.1 ij.2) h0 t
    have hb := hB ij.1 ij.2
    have eq : ((I.pAstar : ℝ) * I.model.cdf I.αstar (M' ij.1 ij.2) t +
          (1 - (I.pAstar : ℝ)) * poisCdf (M' ij.1 ij.2) t) -
        ((I.pAstar : ℝ) * I.model.cdf I.αstar (I.Mstar ij.1 ij.2) t +
          (1 - (I.pAstar : ℝ)) * poisCdf (I.Mstar ij.1 ij.2) t) =
        (I.pAstar : ℝ) * (I.model.cdf I.αstar (M' ij.1 ij.2) t -
          I.model.cdf I.αstar (I.Mstar ij.1 ij.2) t) +
        (1 - (I.pAstar : ℝ)) * (poisCdf (M' ij.1 ij.2) t - poisCdf (I.Mstar ij.1 ij.2) t) := by
      ring
    rw [eq]
    have ht : (0 : ℝ) ≤ t + 1 := by positivity
    have e1 : (t + 1) * (K * |M' ij.1 ij.2 - I.Mstar ij.1 ij.2|) ≤ (t + 1) * (K * B) := by
      gcongr
    have e2 : (t + 1) * |M' ij.1 ij.2 - I.Mstar ij.1 ij.2| ≤ (t + 1) * B := by gcongr
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ (I.pAstar : ℝ) * ((t + 1) * (K * B)) + (1 - (I.pAstar : ℝ)) * ((t + 1) * B) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hpA0,
          abs_of_nonneg (show (0 : ℝ) ≤ 1 - I.pAstar by linarith)]
        exact add_le_add (mul_le_mul_of_nonneg_left (c1.trans e1) hpA0)
          (mul_le_mul_of_nonneg_left (c2.trans e2) (by linarith))
      _ ≤ (t + 1) * ((K + 1) * B) := by
        have : (I.pAstar : ℝ) * ((t + 1) * (K * B)) ≤ (t + 1) * (K * B) := by
          have : 0 ≤ (t + 1) * (K * B) := by positivity
          nlinarith
        have : (1 - (I.pAstar : ℝ)) * ((t + 1) * B) ≤ (t + 1) * B := by
          have : 0 ≤ (t + 1) * B := by positivity
          nlinarith
        nlinarith
  have hcard : (Finset.univ : Finset (Fin I.n × Fin I.m)).card = I.n * I.m := by
    simp
  calc 1 / (I.n * I.m : ℝ) * |∑ ij : Fin I.n × Fin I.m, _|
      ≤ 1 / (I.n * I.m : ℝ) * ∑ _ij : Fin I.n × Fin I.m, (t + 1) * ((K + 1) * B) := by
        gcongr
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ij _ => hentry ij)
    _ = (t + 1) * ((K + 1) * B) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        have : (0 : ℝ) < I.n * I.m := by positivity
        push_cast
        field_simp

lemma IA16_ratio (A N S E ℓ C14 : ℝ) (hE : 0 < E) (hℓ : 0 ≤ ℓ) (hS0 : 0 ≤ S) (hSE : S ≤ E)
    (hC : 0 < C14) (hK0 : (16 * C14 ^ 2 + 4 * C14 + 1) * ℓ ≤ E)
    (hA : |A - S| ≤ C14 * (Real.sqrt (S * ℓ) + ℓ))
    (hN : |N - E| ≤ C14 * (Real.sqrt (E * ℓ) + ℓ)) :
    |A / N - S / E| ≤ 8 * C14 * Real.sqrt (ℓ / E) := by
  set D0 := C14 * (Real.sqrt (E * ℓ) + ℓ) with hD0
  have hsq : Real.sqrt (E * ℓ) = E * Real.sqrt (ℓ / E) := by
    rw [show E * ℓ = E ^ 2 * (ℓ / E) by field_simp, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hE.le]
  have hle1 : ℓ / E ≤ 1 := by
    rw [div_le_one hE]; nlinarith [sq_nonneg C14]
  have hroot : ℓ / E ≤ Real.sqrt (ℓ / E) := by
    have h0 : 0 ≤ ℓ / E := by positivity
    calc ℓ / E = Real.sqrt (ℓ / E) * Real.sqrt (ℓ / E) := (Real.mul_self_sqrt h0).symm
      _ ≤ Real.sqrt (ℓ / E) * 1 := by
        gcongr
        rw [Real.sqrt_le_one]; exact hle1
      _ = _ := mul_one _
  have hsmall : Real.sqrt (ℓ / E) ≤ 1 / (4 * C14) := by
    rw [Real.sqrt_le_left (by positivity)]
    rw [div_le_iff₀ hE]
    have : (1 / (4 * C14)) ^ 2 * E ≥ ℓ := by
      rw [div_pow, one_pow, mul_pow, ge_iff_le, ← sub_nonneg]
      have h16 : (4 : ℝ) ^ 2 * C14 ^ 2 > 0 := by positivity
      have : 1 / (4 ^ 2 * C14 ^ 2) * E - ℓ = (E - 16 * C14 ^ 2 * ℓ) / (16 * C14 ^ 2) := by
        field_simp; ring
      rw [this]
      apply div_nonneg _ (by positivity)
      nlinarith [sq_nonneg C14]
    linarith
  have hD0E : D0 ≤ E / 2 := by
    rw [hD0, hsq]
    have h1 : C14 * (E * Real.sqrt (ℓ / E)) ≤ E / 4 := by
      calc C14 * (E * Real.sqrt (ℓ / E)) ≤ C14 * (E * (1 / (4 * C14))) := by gcongr
        _ = E / 4 := by field_simp
    have h2 : C14 * ℓ ≤ E / 4 := by nlinarith [sq_nonneg C14]
    nlinarith
  have hAS : |A - S| ≤ D0 := by
    refine hA.trans ?_
    rw [hD0]
    gcongr
  have hNpos : E / 2 ≤ N := by
    have := (abs_le.1 hN).1
    linarith
  have hN0 : 0 < N := by linarith
  have hSE1 : S / E ≤ 1 := (div_le_one hE).2 hSE
  have hSE0 : 0 ≤ S / E := by positivity
  have heq : A / N - S / E = ((A - S) + S / E * (E - N)) / N := by
    field_simp; ring
  rw [heq, abs_div, abs_of_pos hN0, div_le_iff₀ hN0]
  have hNE : |E - N| ≤ D0 := by rw [abs_sub_comm]; exact hN
  have hnum : |(A - S) + S / E * (E - N)| ≤ 2 * D0 := by
    calc _ ≤ |A - S| + |S / E * (E - N)| := abs_add_le _ _
      _ ≤ D0 + 1 * D0 := by
        rw [abs_mul, abs_of_nonneg hSE0]
        exact add_le_add hAS (mul_le_mul hSE1 hNE (abs_nonneg _) zero_le_one)
      _ = 2 * D0 := by ring
  have hD0' : D0 ≤ 2 * C14 * E * Real.sqrt (ℓ / E) := by
    rw [hD0, hsq]
    have : ℓ ≤ E * Real.sqrt (ℓ / E) := by
      have := mul_le_mul_of_nonneg_left hroot hE.le
      rwa [mul_div_cancel₀ _ hE.ne'] at this
    nlinarith
  have hsq0 : 0 ≤ Real.sqrt (ℓ / E) := Real.sqrt_nonneg _
  calc |(A - S) + S / E * (E - N)| ≤ 2 * D0 := hnum
    _ ≤ 2 * (2 * C14 * E * Real.sqrt (ℓ / E)) := by linarith
    _ = 8 * C14 * Real.sqrt (ℓ / E) * (E / 2) := by ring
    _ ≤ 8 * C14 * Real.sqrt (ℓ / E) * N := by gcongr

lemma IA16_X_ge (m : ℕ) (hm : 2 ≤ m) : (1 / 4 : ℝ) ≤ Real.log m ^ ((3 : ℝ) / 2) := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log m := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) hm2
    linarith
  have h1 : ((1 / 2 : ℝ)) ^ ((3 : ℝ) / 2) ≤ Real.log m ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow (by norm_num) hlog2 (by norm_num)
  have h2 : ((1 / 2 : ℝ)) ^ (2 : ℝ) ≤ ((1 / 2 : ℝ)) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
  have h3 : ((1 / 2 : ℝ)) ^ (2 : ℝ) = 1 / 4 := by rw [Real.rpow_two]; norm_num
  linarith

lemma IA16_pOm {d : ℕ} {I : Instance d} {cM cA Csp K L μ : ℝ}
    (hI : I.Model cM cA Csp K L μ) (hC : 0 ≤ Csp) : Csp ^ 2 / 16 ≤ (I.pO : ℝ) * I.m := by
  have hm0 : (0 : ℝ) < I.m := by have := hI.two_le_m; exact_mod_cast (by omega : 0 < I.m)
  have hX := IA16_X_ge I.m hI.two_le_m
  have hμ := IA1s_mu_ge_one hI
  have hκ := IA1s_kappa_ge_one hI
  have hr : (1 : ℝ) ≤ I.r := by exact_mod_cast hI.r_pos
  have hκ2 : 1 ≤ I.κ hI.r_pos ^ 2 := one_le_pow₀ hκ
  have hprod : 1 ≤ μ * I.r * I.κ hI.r_pos ^ 2 := by
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ μ * I.r * I.κ hI.r_pos ^ 2 := by gcongr
  have hs0 : 0 < Real.sqrt I.m := Real.sqrt_pos.2 hm0
  have hsp := hI.sparsity
  have h1 : Csp / 4 ≤ Csp * Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * I.κ hI.r_pos ^ 2 := by
    calc Csp / 4 = Csp * (1 / 4) * 1 := by ring
      _ ≤ Csp * Real.log I.m ^ ((3 : ℝ) / 2) * (μ * I.r * I.κ hI.r_pos ^ 2) := by gcongr
      _ = _ := by ring
  have h2 : Csp / 4 / Real.sqrt I.m ≤ Real.sqrt I.pO :=
    (div_le_div_of_nonneg_right h1 hs0.le).trans hsp
  have h3 : (Csp / 4 / Real.sqrt I.m) ^ 2 ≤ Real.sqrt I.pO ^ 2 := by
    have : 0 ≤ Csp / 4 / Real.sqrt I.m := by positivity
    gcongr
  rw [div_pow, div_pow, Real.sq_sqrt hm0.le, Real.sq_sqrt (NNReal.coe_nonneg I.pO)] at h3
  rw [div_le_iff₀ hm0] at h3
  nlinarith

lemma IA16_ell {d : ℕ} {I : Instance d} {cM cA Csp K L μ : ℝ}
    (hI : I.Model cM cA Csp K L μ) :
    Real.log (I.m * I.n) ≤ 2 * I.n ∧ Real.log (I.m * I.n) ≤ 3 * I.n * Real.log I.m := by
  have hm2 : (2 : ℝ) ≤ I.m := by exact_mod_cast hI.two_le_m
  have hmn : (I.m : ℝ) ≤ I.n := by exact_mod_cast hI.m_le_n
  have hm0 : (0 : ℝ) < I.m := by linarith
  have hn0 : (0 : ℝ) < I.n := by linarith
  have hlogm : (1 / 2 : ℝ) ≤ Real.log I.m := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ Real.log I.m := Real.log_le_log (by norm_num) hm2
    linarith
  have hlogn : Real.log I.n ≤ I.n - 1 := Real.log_le_sub_one_of_pos hn0
  have hlogmn : Real.log I.m ≤ Real.log I.n := Real.log_le_log hm0 hmn
  rw [Real.log_mul hm0.ne' hn0.ne']
  constructor
  · linarith
  · have h1 : Real.log I.m ≤ I.n * Real.log I.m := by
      have : (1 : ℝ) ≤ I.n := by linarith
      nlinarith
    have h2 : Real.log I.n ≤ 2 * I.n * Real.log I.m := by
      have : (I.n : ℝ) ≤ 2 * I.n * Real.log I.m := by nlinarith
      linarith
    linarith


lemma IA16_δlow {d : ℕ} {I : Instance d} {cM cA Csp K L μ : ℝ}
    (hI : I.Model cM cA Csp K L μ) (hcM : 0 < cM) (hLcM : cM ≤ L) :
    cM * Real.sqrt (Real.log I.m / (I.pO * I.m)) ≤ I.δ' hI.r_pos μ L := by
  unfold Instance.δ'
  have hμ := IA1s_mu_ge_one hI
  have hκ := IA1s_kappa_ge_one hI
  have hr : (1 : ℝ) ≤ I.r := by exact_mod_cast hI.r_pos
  have hκ4 : 1 ≤ I.κ hI.r_pos ^ 4 := one_le_pow₀ hκ
  have hprod : 1 ≤ I.κ hI.r_pos ^ 4 * μ * I.r := by
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ I.κ hI.r_pos ^ 4 * μ * I.r := by gcongr
  set y := Real.sqrt (Real.log I.m / (I.pO * I.m))
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hL : 0 ≤ L := by linarith
  calc cM * y ≤ L * y := mul_le_mul_of_nonneg_right hLcM hy
    _ = 1 * (L * y) := (one_mul _).symm
    _ ≤ (I.κ hI.r_pos ^ 4 * μ * I.r) * (L * y) := mul_le_mul_of_nonneg_right hprod (by positivity)
    _ = _ := by ring

lemma IA16_term {d : ℕ} (I : Instance d) {cM cA Csp K L μ : ℝ}
    (hI : I.Model cM cA Csp K L μ) (hcM : 0 < cM) (hcA : 0 < cA) (hK : 0 ≤ K) (hLcM : cM ≤ L)
    (hpA1 : (I.pAstar : ℝ) ≤ 1) (C2 C14 : ℝ) (hC2 : 0 < C2) (hC14 : 0 < C14)
    (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ) (ω : I.Sample)
    (t : ℕ) (htd : (t : ℝ) + 1 ≤ d + 1)
    (hBM : ∀ i j, |((I.model.e I.θstar)⁻¹ • I.Mhat svdr (I.obs ω)) i j - I.Mstar i j| ≤
        C2 * I.δ' hI.r_pos μ L / cA)
    (hpOpos : (0 : ℝ) < I.pO)
    (hℓ0 : 0 ≤ Real.log (I.m * I.n))
    (hK0ℓ : (16 * C14 ^ 2 + 4 * C14 + 1) * Real.log (I.m * I.n) ≤ I.pO * I.m * I.n)
    (hell2 : Real.log (I.m * I.n) ≤ 3 * I.n * Real.log I.m)
    (hAt : |∑ ij, (if (ω ij).1 then (1 : ℝ) else 0) * (if (ω ij).2.2 ≤ t then (1 : ℝ) else 0) -
        ∑ ij, (I.pO : ℝ) * ∫ e, (if (e : Entry).2.2 ≤ t then (1 : ℝ) else 0)
          ∂(I.entryPMF ij).toMeasure| ≤
      C14 * (Real.sqrt ((∑ ij, (I.pO : ℝ) * ∫ e, (if (e : Entry).2.2 ≤ t then (1 : ℝ) else 0)
          ∂(I.entryPMF ij).toMeasure) * Real.log (I.m * I.n)) + Real.log (I.m * I.n)))
    (hA1 : |∑ ij, (if (ω ij).1 then (1 : ℝ) else 0) * 1 - I.pO * I.m * I.n| ≤
      C14 * (Real.sqrt (I.pO * I.m * I.n * Real.log (I.m * I.n)) + Real.log (I.m * I.n))) :
    |I.gt I.θstar ((I.model.e I.θstar)⁻¹ • I.Mhat svdr (I.obs ω)) t -
        (((I.omega (I.obs ω)).filter fun ij => ((I.obs ω ij).getD 0) ≤ t).card : ℝ) /
          (I.omega (I.obs ω)).card| ≤
      (((d : ℝ) + 1) * (1 + 1 / cM) * C2 / cA + 8 * C14 * Real.sqrt 3 / cM ^ 2) *
        ((K + L) * I.δ' hI.r_pos μ L) := by
  have hm0' : (0 : ℝ) < I.m := by have := hI.two_le_m; exact_mod_cast (by omega : 0 < I.m)
  have hn0' : (0 : ℝ) < I.n := by
    have := hI.two_le_m; have := hI.m_le_n; exact_mod_cast (by omega : 0 < I.n)
  have hpart1 := IA16_partA I hI hK _ _ hBM t hpA1
  set E : ℝ := I.pO * I.m * I.n with hE
  have hEpos : 0 < E := by rw [hE]; positivity
  set ℓ := Real.log (I.m * I.n) with hℓ
  set S : ℝ := ∑ ij : Fin I.n × Fin I.m, (I.pO : ℝ) *
    ∫ e, (if (e : Entry).2.2 ≤ t then (1 : ℝ) else 0) ∂(I.entryPMF ij).toMeasure with hSdef
  have hp01 : ∀ ij : Fin I.n × Fin I.m,
      0 ≤ ∫ e, (if (e : Entry).2.2 ≤ t then (1 : ℝ) else 0) ∂(I.entryPMF ij).toMeasure ∧
      ∫ e, (if (e : Entry).2.2 ≤ t then (1 : ℝ) else 0) ∂(I.entryPMF ij).toMeasure ≤ 1 := by
    intro ij
    have hb : ∀ e : Entry, 0 ≤ (if e.2.2 ≤ t then (1 : ℝ) else 0) ∧
        (if e.2.2 ≤ t then (1 : ℝ) else 0) ≤ 1 := by
      intro e; split_ifs <;> norm_num
    constructor
    · exact integral_nonneg fun e => (hb e).1
    · calc _ ≤ ∫ _e, (1 : ℝ) ∂(I.entryPMF ij).toMeasure :=
            integral_mono (Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable 1
              (Filter.Eventually.of_forall fun e => by
                rw [Real.norm_eq_abs, abs_of_nonneg (hb e).1]; exact (hb e).2))
              (integrable_const _) (fun e => (hb e).2)
        _ = 1 := by simp
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun ij _ => mul_nonneg I.pO.2 (hp01 ij).1
  have hSE : S ≤ E := by
    have : S ≤ ∑ _ij : Fin I.n × Fin I.m, (I.pO : ℝ) * 1 :=
      Finset.sum_le_sum fun ij _ => mul_le_mul_of_nonneg_left (hp01 ij).2 I.pO.2
    refine this.trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul, hE]
    push_cast; ring
  have hA' : |(((I.omega (I.obs ω)).filter fun ij => ((I.obs ω ij).getD 0) ≤ t).card : ℝ) - S| ≤
      C14 * (Real.sqrt (S * ℓ) + ℓ) := by
    rw [IA16_card_filter]; exact hAt
  have hN' : |((I.omega (I.obs ω)).card : ℝ) - E| ≤ C14 * (Real.sqrt (E * ℓ) + ℓ) := by
    rw [IA16_card_omega]; exact hA1
  have hrat := IA16_ratio _ _ S E ℓ C14 hEpos hℓ0 hS0 hSE hC14 hK0ℓ hA' hN'
  have hgS : I.gt I.θstar I.Mstar t = S / E := by
    rw [IA16_gt_star, hSdef, hE]
    simp_rw [← IA16_mean_ind I hpA1 _ t]
    rw [← Finset.mul_sum]
    field_simp
  have hpart2 : |I.gt I.θstar I.Mstar t -
      (((I.omega (I.obs ω)).filter fun ij => ((I.obs ω ij).getD 0) ≤ t).card : ℝ) /
        (I.omega (I.obs ω)).card| ≤ 8 * C14 * Real.sqrt (ℓ / E) := by
    rw [abs_sub_comm, hgS]; exact hrat
  have hδ0 : 0 ≤ I.δ' hI.r_pos μ L := by
    unfold Instance.δ'
    have hμ := IA1s_mu_ge_one hI
    have hκ := IA1s_kappa_ge_one hI
    have : (0 : ℝ) ≤ I.r := Nat.cast_nonneg _
    have : 0 ≤ I.κ hI.r_pos := by linarith
    have : 0 ≤ μ := by linarith
    have : 0 ≤ L := by linarith
    positivity
  have hKL : cM ≤ K + L := by linarith
  have hb1 : (t + 1 : ℝ) * ((K + 1) * (C2 * I.δ' hI.r_pos μ L / cA)) ≤
      ((d : ℝ) + 1) * (1 + 1 / cM) * C2 / cA * ((K + L) * I.δ' hI.r_pos μ L) := by
    have hK1 : K + 1 ≤ (1 + 1 / cM) * (K + L) := by
      have : 1 ≤ (K + L) / cM := by rw [le_div_iff₀ hcM]; linarith
      have : (1 + 1 / cM) * (K + L) = (K + L) + (K + L) / cM := by ring
      linarith
    have hX0 : 0 ≤ C2 * I.δ' hI.r_pos μ L / cA := by positivity
    calc (t + 1 : ℝ) * ((K + 1) * (C2 * I.δ' hI.r_pos μ L / cA)) ≤
        ((d : ℝ) + 1) * (((1 + 1 / cM) * (K + L)) * (C2 * I.δ' hI.r_pos μ L / cA)) := by
          gcongr
      _ = _ := by ring
  have hlogm0 : 0 ≤ Real.log I.m := Real.log_natCast_nonneg _
  have hℓE : Real.sqrt (ℓ / E) ≤ Real.sqrt 3 * Real.sqrt (Real.log I.m / (I.pO * I.m)) := by
    rw [← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    rw [hE, div_le_iff₀ (by positivity)]
    calc ℓ ≤ 3 * I.n * Real.log I.m := hell2
      _ = 3 * (Real.log I.m / (I.pO * I.m)) * (I.pO * I.m * I.n) := by
        field_simp
  have hδlow := IA16_δlow hI hcM hLcM
  have hb2 : 8 * C14 * Real.sqrt (ℓ / E) ≤
      8 * C14 * Real.sqrt 3 / cM ^ 2 * ((K + L) * I.δ' hI.r_pos μ L) := by
    have h1 : Real.sqrt (Real.log I.m / (I.pO * I.m)) ≤
        (K + L) * I.δ' hI.r_pos μ L / cM ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have hs0 : 0 ≤ Real.sqrt (Real.log I.m / (I.pO * I.m)) := Real.sqrt_nonneg _
      calc Real.sqrt (Real.log I.m / (I.pO * I.m)) * cM ^ 2 =
          cM * (cM * Real.sqrt (Real.log I.m / (I.pO * I.m))) := by ring
        _ ≤ (K + L) * I.δ' hI.r_pos μ L :=
          mul_le_mul hKL hδlow (by positivity) (by linarith)
    calc 8 * C14 * Real.sqrt (ℓ / E) ≤
        8 * C14 * (Real.sqrt 3 * Real.sqrt (Real.log I.m / (I.pO * I.m))) := by gcongr
      _ ≤ 8 * C14 * (Real.sqrt 3 * ((K + L) * I.δ' hI.r_pos μ L / cM ^ 2)) := by gcongr
      _ = _ := by ring
  have hsplit : I.gt I.θstar ((I.model.e I.θstar)⁻¹ • I.Mhat svdr (I.obs ω)) t -
      (((I.omega (I.obs ω)).filter fun ij => ((I.obs ω ij).getD 0) ≤ t).card : ℝ) /
        (I.omega (I.obs ω)).card =
      (I.gt I.θstar ((I.model.e I.θstar)⁻¹ • I.Mhat svdr (I.obs ω)) t -
        I.gt I.θstar I.Mstar t) + (I.gt I.θstar I.Mstar t -
        (((I.omega (I.obs ω)).filter fun ij => ((I.obs ω ij).getD 0) ≤ t).card : ℝ) /
          (I.omega (I.obs ω)).card) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have : (((d : ℝ) + 1) * (1 + 1 / cM) * C2 / cA + 8 * C14 * Real.sqrt 3 / cM ^ 2) *
        ((K + L) * I.δ' hI.r_pos μ L) =
      ((d : ℝ) + 1) * (1 + 1 / cM) * C2 / cA * ((K + L) * I.δ' hI.r_pos μ L) +
        8 * C14 * Real.sqrt 3 / cM ^ 2 * ((K + L) * I.δ' hI.r_pos μ L) := by ring
  rw [this]
  linarith

theorem solution (d : ℕ) (cM cA : ℝ) (hcM : 0 < cM) (hcA : 0 < cA) (hcA1 : cA < 1) :
    ∃ Csp C C' : ℝ, 0 < Csp ∧ 0 < C ∧ 0 < C' ∧
      ∀ (I : Instance d) (K L μ : ℝ) (hI : I.Model cM cA Csp K L μ),
        I.SparsityMax hI.r_pos Csp μ L →
        ∀ (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ),
        IsBestRankApprox I.r svdr →
        1 - C' / (I.n * I.m) ≤ I.law.real {ω |
          I.hobj (d + 1) svdr (I.obs ω) I.θstar ≤ C * (K + L) ^ 2 * I.δ' hI.r_pos μ L ^ 2} := by
  classical
  obtain ⟨Cs2, C2, C2', h2s, h2C, h2C', H2⟩ := theorem_2 d cM cA hcM hcA hcA1
  obtain ⟨C14, hC14, H14⟩ := IA16_conc
  set K0 : ℝ := 16 * C14 ^ 2 + 4 * C14 + 1 with hK0
  set B0 : ℝ := ((d : ℝ) + 1) * (1 + 1 / cM) * C2 / cA + 8 * C14 * Real.sqrt 3 / cM ^ 2 with hB0
  have hB0pos : 0 < B0 := by positivity
  refine ⟨max Cs2 (32 * K0 + 1), ((d : ℝ) + 1) * B0 ^ 2, C2' + ((d : ℝ) + 2),
    lt_max_of_lt_left h2s, by positivity, by positivity, ?_⟩
  intro I K L μ hI hS svdr hsvd
  set Csp := max Cs2 (32 * K0 + 1) with hCsp
  have E2 := H2 I K L μ (IA1s_model_mono hI (le_max_left _ _))
    (IA1s_spmax_mono hI hS (le_max_left _ _)) svdr hsvd
  -- elementary facts
  have hm2 := hI.two_le_m
  have hmn := hI.m_le_n
  have hn0 : 0 < I.n := by omega
  have hm0 : 0 < I.m := by omega
  have hn0' : (0 : ℝ) < I.n := by exact_mod_cast hn0
  have hm0' : (0 : ℝ) < I.m := by exact_mod_cast hm0
  have hLcM : cM ≤ L := by
    obtain ⟨i, j, h⟩ := hI.max_lb
    exact h.trans ((le_abs_self _).trans (hI.max_ub i j))
  have hK : 0 ≤ K := by
    have := hI.smooth 0 (I.αstar, 0) ⟨hI.α_mem, Set.mem_Ici.2 le_rfl⟩ (I.αstar, 1)
      ⟨hI.α_mem, Set.mem_Ici.2 zero_le_one⟩
    have hd : dist ((I.αstar, (0 : ℝ))) (I.αstar, (1 : ℝ)) = 1 := by
      simp [Prod.dist_eq, Real.dist_eq]
    rw [hd, mul_one] at this
    exact (abs_nonneg _).trans this
  have hμ := IA1s_mu_ge_one hI
  have hκ := IA1s_kappa_ge_one hI
  have hr : (1 : ℝ) ≤ I.r := by exact_mod_cast hI.r_pos
  have hpO1 : (I.pO : ℝ) ≤ 1 := by exact_mod_cast hI.pO_le
  have hpA0 : (0 : ℝ) ≤ I.pAstar := I.pAstar.2
  have hpA1 : (I.pAstar : ℝ) ≤ 1 - cA := hI.pA_le
  have hCsp1 : 32 * K0 + 1 ≤ Csp := le_max_right _ _
  have hK00 : 0 < K0 := by positivity
  have hCsp0 : 0 ≤ Csp := by linarith
  have hpOm := IA16_pOm hI hCsp0
  have hCsq : 32 * K0 ≤ Csp ^ 2 / 16 * 16 := by nlinarith
  have hpOpos : (0 : ℝ) < I.pO := by
    by_contra h
    push_neg at h
    have : (I.pO : ℝ) * I.m ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hm0'.le
    nlinarith
  obtain ⟨hell1, hell2⟩ := IA16_ell hI
  set ℓ := Real.log (I.m * I.n) with hℓ
  have hℓ0 : 0 ≤ ℓ := by
    rw [hℓ]; apply Real.log_nonneg
    have hm1 : (1 : ℝ) ≤ I.m := by exact_mod_cast (by omega : 1 ≤ I.m)
    have hn1 : (1 : ℝ) ≤ I.n := by exact_mod_cast (by omega : 1 ≤ I.n)
    exact one_le_mul_of_one_le_of_one_le hm1 hn1
  -- e(θ*)
  have hestar : cA ≤ I.model.e I.θstar ∧ I.model.e I.θstar ≤ 1 := by
    obtain ⟨g0, g1⟩ := hI.g_mem (alphaOf I.θstar)
    unfold AnomModel.e
    rw [IA18_pA_star]
    constructor <;> nlinarith
  have hepos : 0 < I.model.e I.θstar := lt_of_lt_of_le hcA hestar.1
  have hδ0 : 0 ≤ I.δ' hI.r_pos μ L := by
    unfold Instance.δ'
    have : (0 : ℝ) ≤ I.r := by linarith
    have : 0 ≤ I.κ hI.r_pos := by linarith
    have : 0 ≤ μ := by linarith
    have : 0 ≤ L := by linarith
    positivity
  -- the events
  have hP : IsProbabilityMeasure I.law := by unfold Instance.law; infer_instance
  let τ : ℕ → ℕ → ℝ := fun t k => if k ≤ t then 1 else 0
  have hτ : ∀ t k, 0 ≤ τ t k ∧ τ t k ≤ 1 := by
    intro t k; simp only [τ]; split_ifs <;> norm_num
  set G2 := {ω | maxNorm (I.Mhat svdr (I.obs ω) - I.model.e I.θstar • I.Mstar)
      (C2 * I.δ' hI.r_pos μ L)} with hG2
  set At : ℕ → Set I.Sample := fun t => {x | |∑ ij, (if (x ij).1 then (1 : ℝ) else 0) *
        τ t (x ij).2.2 - ∑ ij, (I.pO : ℝ) * ∫ e, τ t e.2.2 ∂(I.entryPMF ij).toMeasure| ≤
      C14 * (Real.sqrt ((∑ ij, (I.pO : ℝ) * ∫ e, τ t e.2.2 ∂(I.entryPMF ij).toMeasure) *
        Real.log (I.m * I.n)) + Real.log (I.m * I.n))} with hAt
  set A1 := {x : I.Sample | |∑ ij, (if (x ij).1 then (1 : ℝ) else 0) *
        (fun _ : ℕ => (1 : ℝ)) (x ij).2.2 - ∑ ij, (I.pO : ℝ) *
          ∫ e, (fun _ : ℕ => (1 : ℝ)) (e : Entry).2.2 ∂(I.entryPMF ij).toMeasure| ≤
      C14 * (Real.sqrt ((∑ ij, (I.pO : ℝ) *
          ∫ e, (fun _ : ℕ => (1 : ℝ)) (e : Entry).2.2 ∂(I.entryPMF ij).toMeasure) *
        Real.log (I.m * I.n)) + Real.log (I.m * I.n))} with hA1
  have EAt : ∀ t, 1 - 1 / ((I.n : ℝ) * I.m) ≤ I.law.real (At t) := fun t =>
    H14 I (τ t) (hτ t) hn0 hm0 hpO1
  have EA1 : 1 - 1 / ((I.n : ℝ) * I.m) ≤ I.law.real A1 :=
    H14 I (fun _ => 1) (fun _ => ⟨zero_le_one, le_rfl⟩) hn0 hm0 hpO1
  set Bad := G2ᶜ ∪ (⋃ t ∈ Finset.range (d + 1), (At t)ᶜ) ∪ A1ᶜ with hBad
  have hcompl : ∀ S : Set I.Sample, I.law.real Sᶜ = 1 - I.law.real S := fun S => by
    rw [measureReal_compl MeasurableSet.of_discrete, probReal_univ]
  have hBadle : I.law.real Bad ≤ (C2' + ((d : ℝ) + 2)) / (I.n * I.m) := by
    have h1 := measureReal_union_le (μ := I.law) (G2ᶜ ∪ ⋃ t ∈ Finset.range (d + 1), (At t)ᶜ) A1ᶜ
    have h2 := measureReal_union_le (μ := I.law) G2ᶜ (⋃ t ∈ Finset.range (d + 1), (At t)ᶜ)
    have h3 := measureReal_biUnion_finset_le (μ := I.law) (Finset.range (d + 1))
      (fun t => (At t)ᶜ)
    have h4 : ∑ t ∈ Finset.range (d + 1), I.law.real (At t)ᶜ ≤
        ∑ _t ∈ Finset.range (d + 1), 1 / ((I.n : ℝ) * I.m) := by
      refine Finset.sum_le_sum fun t _ => ?_
      rw [hcompl]; linarith [EAt t]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h4
    have h5 : I.law.real G2ᶜ ≤ C2' / (I.n * I.m) := by rw [hcompl]; linarith
    have h6 : I.law.real A1ᶜ ≤ 1 / ((I.n : ℝ) * I.m) := by rw [hcompl]; linarith
    have : (C2' + ((d : ℝ) + 2)) / (I.n * I.m) =
        C2' / (I.n * I.m) + ((d + 1 : ℕ) : ℝ) * (1 / ((I.n : ℝ) * I.m)) +
          1 / ((I.n : ℝ) * I.m) := by
      push_cast; field_simp; ring
    rw [this]
    linarith
  -- deterministic part
  set Z := B0 * ((K + L) * I.δ' hI.r_pos μ L) with hZ
  have hsub : Badᶜ ⊆ {ω | I.hobj (d + 1) svdr (I.obs ω) I.θstar ≤
      ((d : ℝ) + 1) * B0 ^ 2 * (K + L) ^ 2 * I.δ' hI.r_pos μ L ^ 2} := by
    intro ω hω
    simp only [hBad, Set.compl_union, Set.compl_iUnion, compl_compl, Set.mem_inter_iff,
      Set.mem_iInter] at hω
    obtain ⟨⟨hG2ω, hAtω⟩, hA1ω⟩ := hω
    have hG2' : maxNorm (I.Mhat svdr (I.obs ω) - I.model.e I.θstar • I.Mstar)
        (C2 * I.δ' hI.r_pos μ L) := hG2ω
    have hBM : ∀ i j, |((I.model.e I.θstar)⁻¹ • I.Mhat svdr (I.obs ω)) i j - I.Mstar i j| ≤
        C2 * I.δ' hI.r_pos μ L / cA := by
      intro i j
      have h := hG2' i j
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h ⊢
      have heq : (I.model.e I.θstar)⁻¹ * I.Mhat svdr (I.obs ω) i j - I.Mstar i j =
          (I.Mhat svdr (I.obs ω) i j - I.model.e I.θstar * I.Mstar i j) / I.model.e I.θstar := by
        field_simp
      rw [heq, abs_div, abs_of_pos hepos]
      calc _ ≤ C2 * I.δ' hI.r_pos μ L / I.model.e I.θstar :=
            div_le_div_of_nonneg_right h hepos.le
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hcA hestar.1
    have hEval : ∑ ij : Fin I.n × Fin I.m, (I.pO : ℝ) *
        ∫ e, (fun _ : ℕ => (1 : ℝ)) (e : Entry).2.2 ∂(I.entryPMF ij).toMeasure =
          I.pO * I.m * I.n := by
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one, Finset.sum_const,
        Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    have hA1' : |∑ ij, (if (ω ij).1 then (1 : ℝ) else 0) * 1 - I.pO * I.m * I.n| ≤
        C14 * (Real.sqrt (I.pO * I.m * I.n * Real.log (I.m * I.n)) + Real.log (I.m * I.n)) := by
      have h : ω ∈ A1 := hA1ω
      rw [hA1, Set.mem_setOf_eq, hEval] at h
      exact h
    have hK0ℓ : (16 * C14 ^ 2 + 4 * C14 + 1) * Real.log (I.m * I.n) ≤ I.pO * I.m * I.n := by
      have h1 : 2 * K0 ≤ (I.pO : ℝ) * I.m := by linarith
      calc (16 * C14 ^ 2 + 4 * C14 + 1) * Real.log (I.m * I.n) = K0 * ℓ := by rw [hK0, hℓ]
        _ ≤ K0 * (2 * I.n) := by gcongr
        _ = 2 * K0 * I.n := by ring
        _ ≤ (I.pO : ℝ) * I.m * I.n := by gcongr
    have hterm : ∀ t ∈ Finset.range (d + 1),
        |I.gt I.θstar ((I.model.e I.θstar)⁻¹ • I.Mhat svdr (I.obs ω)) t -
          (((I.omega (I.obs ω)).filter fun ij => ((I.obs ω ij).getD 0) ≤ t).card : ℝ) /
            (I.omega (I.obs ω)).card| ≤ Z := by
      intro t ht
      have htd : (t : ℝ) + 1 ≤ d + 1 := by
        have := Finset.mem_range.1 ht
        exact_mod_cast (by omega : t + 1 ≤ d + 1)
      have hAt' : ω ∈ At t := hAtω t ht
      have := IA16_term I hI hcM hcA hK hLcM (by linarith) C2 C14 h2C hC14 svdr ω t htd hBM
        hpOpos hℓ0 hK0ℓ hell2 hAt' hA1'
      rw [hZ, hB0]; exact this
    have hZ0 : 0 ≤ Z := by
      rw [hZ]
      have : 0 ≤ K + L := by linarith
      positivity
    show I.hobj (d + 1) svdr (I.obs ω) I.θstar ≤ _
    unfold Instance.hobj
    calc _ ≤ ∑ _t ∈ Finset.range (d + 1), Z ^ 2 := by
          refine Finset.sum_le_sum fun t ht => ?_
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hterm t ht) 2
      _ = _ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hZ]
          push_cast; ring
  calc 1 - (C2' + ((d : ℝ) + 2)) / (I.n * I.m) ≤ 1 - I.law.real Bad := by linarith
    _ = I.law.real Badᶜ := (hcompl Bad).symm
    _ ≤ _ := measureReal_mono hsub
