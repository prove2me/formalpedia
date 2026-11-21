-- Prove2me | solution 1 for MasulloGRH.absolute_basis_shrinking_boundedly_complete
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T05:26:27.365126+00:00
-- url     : https://prove2.me/submissions/c2d0d6cf-b832-4bc0-b108-97aac0ae3e1a

import Definitions.Def_MasulloGRH_SchauderBases

set_option autoImplicit false

namespace Aux_absolute_basis_shrinking_boundedly_complete

open MasulloGRH Topology Filter Bornology

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

lemma bdd_of_cont {q : Seminorm ℂ E} (hq : Continuous q) {S : Set E}
    (hS : IsVonNBounded ℂ S) : ∃ R : ℝ, ∀ x ∈ S, q x ≤ R := by
  obtain ⟨a, ha⟩ := (hS (q.ball_mem_nhds hq one_pos)).eventually.exists
  refine ⟨‖a‖, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := ha hx
  rw [map_smul_eq_mul]
  have h1 : q y < 1 := by
    have := (Seminorm.mem_ball_zero q).1 hy
    exact this
  exact mul_le_of_le_one_right (norm_nonneg a) h1.le

lemma bdd_clm (g : StrongDual ℂ E) {S : Set E} (hS : IsVonNBounded ℂ S) :
    ∃ R : ℝ, ∀ x ∈ S, ‖g x‖ ≤ R := by
  have hc : Continuous ((normSeminorm ℂ ℂ).comp (g : E →ₗ[ℂ] ℂ)) := by
    have : ((normSeminorm ℂ ℂ).comp (g : E →ₗ[ℂ] ℂ) : E → ℝ) = fun x => ‖g x‖ := by
      funext x; rfl
    rw [this]
    exact continuous_norm.comp g.continuous
  obtain ⟨R, hR⟩ := bdd_of_cont hc hS
  exact ⟨R, fun x hx => hR x hx⟩

/-- evaluation at a point as an element of the bidual -/
noncomputable def evl [ContinuousSMul ℂ E] (y : E) : StrongDual ℂ (StrongDual ℂ E) :=
  ⟨{ toFun := fun g => g y, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
    continuous_eval_const y⟩

lemma evl_apply [ContinuousSMul ℂ E] (y : E) (g : StrongDual ℂ E) : evl y g = g y := rfl

lemma exists_cluster
    (hrefl : ∀ φ : StrongDual ℂ (StrongDual ℂ E), ∃! x : E, ∀ f : StrongDual ℂ E, φ f = f x)
    (w : ℕ → E) (hw : IsVonNBounded ℂ (Set.range w)) :
    ∃ v : E, ∀ g : StrongDual ℂ E, ∀ C : Set ℂ, IsClosed C →
      (∀ᶠ j in atTop, g (w j) ∈ C) → g v ∈ C := by
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  have hex : ∀ g : StrongDual ℂ E, ∃ c, Tendsto (fun j => g (w j)) (U : Filter ℕ) (𝓝 c) := by
    intro g
    obtain ⟨R, hR⟩ := bdd_clm g hw
    have hK : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall _ _
    obtain ⟨c, -, hc⟩ := hK.ultrafilter_le_nhds (U.map (fun j => g (w j))) (by
      rw [Ultrafilter.coe_map, Filter.le_principal_iff, Filter.mem_map]
      exact Filter.univ_mem' fun j => by
        show g (w j) ∈ Metric.closedBall (0 : ℂ) R
        rw [mem_closedBall_zero_iff]
        exact hR _ ⟨j, rfl⟩)
    exact ⟨c, hc⟩
  let L : StrongDual ℂ E → ℂ := fun g => limUnder (U : Filter ℕ) (fun j => g (w j))
  have hL : ∀ g, Tendsto (fun j => g (w j)) (U : Filter ℕ) (𝓝 (L g)) :=
    fun g => tendsto_nhds_limUnder (hex g)
  let Llin : StrongDual ℂ E →ₗ[ℂ] ℂ :=
    { toFun := L
      map_add' := fun g h => by
        refine tendsto_nhds_unique (hL (g + h)) ?_
        have := (hL g).add (hL h)
        exact this
      map_smul' := fun c g => by
        refine tendsto_nhds_unique (hL (c • g)) ?_
        have := (hL g).const_mul c
        exact this }
  have hcont0 : Tendsto Llin (𝓝 0) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hN : {g : StrongDual ℂ E | ∀ y ∈ Set.range w, g y ∈ Metric.closedBall (0 : ℂ) (ε / 2)}
        ∈ 𝓝 (0 : StrongDual ℂ E) :=
      (ContinuousLinearMap.hasBasis_nhds_zero).mem_of_mem
        (i := (Set.range w, Metric.closedBall (0 : ℂ) (ε / 2)))
        ⟨hw, Metric.closedBall_mem_nhds _ (half_pos hε)⟩
    filter_upwards [hN] with g hg
    have hmem : L g ∈ Metric.closedBall (0 : ℂ) (ε / 2) :=
      Metric.isClosed_closedBall.mem_of_tendsto (hL g)
        (Filter.Eventually.of_forall fun j => hg _ ⟨j, rfl⟩)
    rw [mem_closedBall_zero_iff] at hmem
    rw [dist_zero_right]
    show ‖L g‖ < ε
    linarith
  have hcont : Continuous Llin := by
    refine continuous_of_continuousAt_zero Llin ?_
    rw [ContinuousAt, map_zero]
    exact hcont0
  obtain ⟨v, hv, -⟩ := hrefl ⟨Llin, hcont⟩
  refine ⟨v, fun g C hC hev => ?_⟩
  have h1 : L g ∈ C := hC.mem_of_tendsto (hL g) (hU hev)
  have h2 : L g = g v := hv g
  rw [← h2]
  exact h1

section basis

variable {x : ℕ → E} {f : ℕ → StrongDual ℂ E}

lemma coeff_sum (hx : IsSchauderBasis x f) (l : ℕ) (s : Finset ℕ) (c : ℕ → ℂ) :
    f l (∑ m ∈ s, c m • x m) = if l ∈ s then c l else 0 := by
  rw [map_sum]
  simp only [map_smul, hx.biorthogonal, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

lemma eq_zero_of_coeffs [T2Space E] (hx : IsSchauderBasis x f) (v : E)
    (hv : ∀ m, f m v = 0) : v = 0 := by
  have h := hx.expansion v
  have h0 : (fun k => basicProjection x f k v) = fun _ => (0 : E) := by
    funext k
    unfold basicProjection
    simp only [hv, zero_smul, Finset.sum_const_zero]
  rw [h0] at h
  exact (tendsto_nhds_unique h tendsto_const_nhds)

lemma no_bad_seq [T2Space E]
    (hrefl : ∀ φ : StrongDual ℂ (StrongDual ℂ E), ∃! x : E, ∀ f : StrongDual ℂ E, φ f = f x)
    (hx : IsSchauderBasis x f) (φ : StrongDual ℂ E) (ε : ℝ) (hε : 0 < ε)
    (w : ℕ → E) (hw : IsVonNBounded ℂ (Set.range w))
    (hz : ∀ j, ∀ m ≤ j, f m (w j) = 0) (hφ : ∀ j, ε ≤ ‖φ (w j)‖) : False := by
  obtain ⟨v, hv⟩ := exists_cluster hrefl w hw
  have hcoef : ∀ m, f m v = 0 := by
    intro m
    have := hv (f m) {0} isClosed_singleton
      (Filter.eventually_atTop.2 ⟨m, fun j hj => hz j m hj⟩)
    exact this
  have hv0 : v = 0 := eq_zero_of_coeffs hx v hcoef
  have h2 : φ v ∈ {z : ℂ | ε ≤ ‖z‖} :=
    hv φ _ (isClosed_le continuous_const continuous_norm)
      (Filter.Eventually.of_forall fun j => hφ j)
  rw [hv0, map_zero] at h2
  have : ε ≤ ‖(0 : ℂ)‖ := h2
  rw [norm_zero] at this
  linarith

lemma phase_mul (z : ℂ) : (starRingEnd ℂ z / (‖z‖ : ℂ)) * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := by
      exact_mod_cast (norm_ne_zero_iff.2 hz)
    rw [div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    field_simp
    push_cast
    ring

lemma phase_norm (z : ℂ) : ‖starRingEnd ℂ z / (‖z‖ : ℂ)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_conj]
  by_cases hz : z = 0
  · simp [hz]
  · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn, div_self hn.ne']

lemma tail_small {ι : Type*} {p : SeminormFamily ℂ E ι} (hp : WithSeminorms p) [T2Space E]
    (hrefl : ∀ φ : StrongDual ℂ (StrongDual ℂ E), ∃! x : E, ∀ f : StrongDual ℂ E, φ f = f x)
    (hx : IsSchauderBasis x f) (habs : IsAbsoluteBasis x f) (φ : StrongDual ℂ E)
    {B : Set E} (hB : IsVonNBounded ℂ B) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ u ∈ B, ∀ N : ℕ, ∑ m ∈ Finset.Ioc K N, ‖φ (x m) * f m u‖ ≤ ε := by
  by_contra hcon
  push Not at hcon
  choose u hu N hN using hcon
  let c : ℕ → ℕ → ℂ := fun K m =>
    starRingEnd ℂ (φ (x m) * f m (u K)) / (‖φ (x m) * f m (u K)‖ : ℂ)
  let w : ℕ → E := fun K => ∑ m ∈ Finset.Ioc K (N K), (c K m * f m (u K)) • x m
  have hwz : ∀ j, ∀ l ≤ j, f l (w j) = 0 := by
    intro j l hl
    show f l (∑ m ∈ Finset.Ioc j (N j), (c j m * f m (u j)) • x m) = 0
    rw [coeff_sum hx]
    have : l ∉ Finset.Ioc j (N j) := by
      rw [Finset.mem_Ioc]; omega
    rw [if_neg this]
  have hwφ : ∀ j, ε ≤ ‖φ (w j)‖ := by
    intro j
    have hval : φ (w j) = ((∑ m ∈ Finset.Ioc j (N j), ‖φ (x m) * f m (u j)‖ : ℝ) : ℂ) := by
      show φ (∑ m ∈ Finset.Ioc j (N j), (c j m * f m (u j)) • x m) = _
      rw [map_sum]
      push_cast
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_smul, smul_eq_mul, ← phase_mul (φ (x m) * f m (u j))]
      show c j m * f m (u j) * φ (x m) = c j m * (φ (x m) * f m (u j))
      ring
    rw [hval, Complex.norm_real, Real.norm_eq_abs]
    have hpos : 0 ≤ ∑ m ∈ Finset.Ioc j (N j), ‖φ (x m) * f m (u j)‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    rw [abs_of_nonneg hpos]
    exact (hN j).le
  have hwb : IsVonNBounded ℂ (Set.range w) := by
    rw [hp.isVonNBounded_iff_seminorm_bounded]
    intro i
    obtain ⟨q', hq'c, hq'⟩ := habs (p i) (hp.continuous_seminorm i)
    obtain ⟨R, hR⟩ := bdd_of_cont hq'c hB
    refine ⟨max R 0 + 1, by positivity, ?_⟩
    rintro _ ⟨j, rfl⟩
    have h1 : p i (w j) ≤ ∑ m ∈ Finset.Ioc j (N j), p i ((c j m * f m (u j)) • x m) :=
      Finset.le_sum_of_subadditive (p i) (map_zero (p i)).le (map_add_le_add _) _ _
    have h2 : ∀ m, p i ((c j m * f m (u j)) • x m) ≤ p i (f m (u j) • x m) := by
      intro m
      rw [mul_smul, map_smul_eq_mul]
      exact mul_le_of_le_one_left (apply_nonneg _ _) (phase_norm _)
    have h3 : ∑ m ∈ Finset.Ioc j (N j), p i (f m (u j) • x m) ≤
        ∑' m, p i (f m (u j) • x m) :=
      Summable.sum_le_tsum _ (fun _ _ => apply_nonneg _ _) (hq' (u j)).1
    have h4 := (hq' (u j)).2
    have h5 := hR (u j) (hu j)
    have h6 := Finset.sum_le_sum fun m (_ : m ∈ Finset.Ioc j (N j)) => h2 m
    have h7 : p i (w j) ≤ R := by linarith
    have h8 : R ≤ max R 0 := le_max_left _ _
    linarith
  exact no_bad_seq hrefl hx φ ε hε w hwb hwz hwφ


lemma proj_apply (φ : StrongDual ℂ E) (k : ℕ) (u : E) :
    φ (basicProjection x f k u) = ∑ m ∈ Finset.range (k + 1), φ (x m) * f m u := by
  unfold basicProjection
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

lemma hasSum_dual {ι : Type*} {p : SeminormFamily ℂ E ι} (hp : WithSeminorms p) [T2Space E]
    (hrefl : ∀ φ : StrongDual ℂ (StrongDual ℂ E), ∃! x : E, ∀ f : StrongDual ℂ E, φ f = f x)
    (hx : IsSchauderBasis x f) (habs : IsAbsoluteBasis x f) (φ : StrongDual ℂ E) :
    HasSum (fun m => φ (x m) • f m) φ := by
  unfold HasSum
  rw [← tendsto_sub_nhds_zero_iff]
  refine (ContinuousLinearMap.hasBasis_nhds_zero).tendsto_right_iff.2 ?_
  rintro ⟨B, V⟩ ⟨hB, hV⟩
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
  obtain ⟨K, hK⟩ := tail_small hp hrefl hx habs φ hB (ε / 2) (half_pos hε)
  refine Filter.eventually_atTop.2 ⟨Finset.range (K + 1), fun s hs u hu => ?_⟩
  have hs' : Finset.range (K + 1) ⊆ s := hs
  apply hεV
  rw [Metric.mem_ball, dist_zero_right]
  set a : ℂ := ∑ m ∈ s, φ (x m) * f m u with ha
  have hval : ((∑ m ∈ s, φ (x m) • f m) - φ) u = a - φ u := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply]
    rfl
  rw [hval]
  have hlim : Tendsto (fun N => φ (basicProjection x f N u) - a) atTop (𝓝 (φ u - a)) :=
    ((φ.continuous.tendsto u).comp (hx.expansion u)).sub tendsto_const_nhds
  have hev : ∀ᶠ N in atTop, φ (basicProjection x f N u) - a ∈ Metric.closedBall (0 : ℂ) (ε / 2) := by
    refine Filter.eventually_atTop.2 ⟨s.sup id, fun N hN => ?_⟩
    rw [mem_closedBall_zero_iff, proj_apply]
    have hsub : s ⊆ Finset.range (N + 1) := by
      intro m hm
      have : m ≤ s.sup id := Finset.le_sup (f := id) hm
      rw [Finset.mem_range]; omega
    rw [ha, ← Finset.sum_sdiff hsub, add_sub_cancel_right]
    refine (norm_sum_le _ _).trans ?_
    refine le_trans ?_ (hK u hu N)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)
    intro m hm
    rw [Finset.mem_sdiff, Finset.mem_range] at hm
    rw [Finset.mem_Ioc]
    have : m ∉ Finset.range (K + 1) := fun h => hm.2 (hs' h)
    rw [Finset.mem_range] at this
    omega
  have hmem := Metric.isClosed_closedBall.mem_of_tendsto hlim hev
  rw [mem_closedBall_zero_iff] at hmem
  rw [norm_sub_rev]
  linarith

lemma barrel_bound [BarrelledSpace ℂ E] [ContinuousSMul ℂ E] {C : Set (StrongDual ℂ E)}
    (hC : IsVonNBounded ℂ C) :
    ∃ P : Seminorm ℂ E, Continuous P ∧ ∀ g ∈ C, ∀ v, ‖g v‖ ≤ P v := by
  let q : C → Seminorm ℂ E := fun g => (normSeminorm ℂ ℂ).comp ((g : StrongDual ℂ E) : E →ₗ[ℂ] ℂ)
  have hq : ∀ g v, q g v = ‖(g : StrongDual ℂ E) v‖ := fun _ _ => rfl
  have hqc : ∀ g, Continuous (q g) := by
    intro g
    have : (q g : E → ℝ) = fun v => ‖(g : StrongDual ℂ E) v‖ := funext (hq g)
    rw [this]
    exact continuous_norm.comp (g : StrongDual ℂ E).continuous
  have hbdd : BddAbove (Set.range q) := by
    rw [Seminorm.bddAbove_range_iff]
    intro v
    have hN : {g : StrongDual ℂ E | ∀ y ∈ ({v} : Set E), g y ∈ Metric.closedBall (0 : ℂ) 1}
        ∈ 𝓝 (0 : StrongDual ℂ E) :=
      (ContinuousLinearMap.hasBasis_nhds_zero).mem_of_mem
        (i := (({v} : Set E), Metric.closedBall (0 : ℂ) 1))
        ⟨isVonNBounded_singleton v, Metric.closedBall_mem_nhds _ one_pos⟩
    obtain ⟨a, ha⟩ := (hC hN).eventually.exists
    refine ⟨‖a‖, ?_⟩
    rintro _ ⟨g, rfl⟩
    obtain ⟨h, hh, hgh⟩ := ha g.2
    have h1 := hh v rfl
    rw [mem_closedBall_zero_iff] at h1
    show q g v ≤ ‖a‖
    rw [hq, ← hgh, ContinuousLinearMap.smul_apply, norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg a) h1
  refine ⟨⨆ g, q g, ?_, fun g hg v => ?_⟩
  · rw [Seminorm.coe_iSup_eq hbdd]
    exact Seminorm.continuous_iSup q hqc hbdd
  · have hle : q ⟨g, hg⟩ ≤ ⨆ g, q g := le_ciSup hbdd ⟨g, hg⟩
    exact (hq ⟨g, hg⟩ v).symm.le.trans (hle v)


lemma bc_primal [T2Space E]
    (hrefl : ∀ φ : StrongDual ℂ (StrongDual ℂ E), ∃! x : E, ∀ f : StrongDual ℂ E, φ f = f x)
    (hx : IsSchauderBasis x f) : IsBoundedlyCompleteBasis x := by
  intro α hbd
  obtain ⟨v, hv⟩ := exists_cluster hrefl (fun k => ∑ m ∈ Finset.range (k + 1), α m • x m) hbd
  have hcoef : ∀ m, f m v = α m := by
    intro m
    have := hv (f m) {α m} isClosed_singleton (Filter.eventually_atTop.2 ⟨m, fun k hk => by
      show f m (∑ l ∈ Finset.range (k + 1), α l • x l) ∈ ({α m} : Set ℂ)
      rw [coeff_sum hx, if_pos (Finset.mem_range.2 (by omega))]
      exact Set.mem_singleton _⟩)
    exact this
  refine ⟨v, ?_⟩
  have hfun : (fun k => ∑ m ∈ Finset.range (k + 1), α m • x m) =
      fun k => basicProjection x f k v := by
    funext k
    unfold basicProjection
    simp only [hcoef]
  rw [hfun]
  exact hx.expansion v

lemma bc_dual {ι : Type*} {p : SeminormFamily ℂ E ι} (hp : WithSeminorms p) [T2Space E]
    [BarrelledSpace ℂ E] [ContinuousSMul ℂ E] [IsTopologicalAddGroup E]
    (hrefl : ∀ φ : StrongDual ℂ (StrongDual ℂ E), ∃! x : E, ∀ f : StrongDual ℂ E, φ f = f x)
    (hx : IsSchauderBasis x f) (habs : IsAbsoluteBasis x f) : IsBoundedlyCompleteBasis f := by
  intro α hbd
  obtain ⟨P, hPc, hP⟩ := barrel_bound hbd
  have hΦapp : ∀ k v, (∑ m ∈ Finset.range (k + 1), α m • f m) v =
      ∑ m ∈ Finset.range (k + 1), α m * f m v := by
    intro k v
    rw [ContinuousLinearMap.sum_apply]
    rfl
  have hPb : ∀ k v, ‖(∑ m ∈ Finset.range (k + 1), α m • f m) v‖ ≤ P v :=
    fun k v => hP _ ⟨k, rfl⟩ v
  have hproj : ∀ N k, N ≤ k → ∀ v,
      (∑ m ∈ Finset.range (k + 1), α m • f m) (basicProjection x f N v) =
        (∑ m ∈ Finset.range (N + 1), α m • f m) v := by
    intro N k hNk v
    rw [hΦapp, hΦapp]
    unfold basicProjection
    simp only [coeff_sum hx, mul_ite, mul_zero]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2]
    intro m hm
    rw [Finset.mem_range] at hm ⊢
    omega
  have hPt : ∀ v, Tendsto (fun N => P (v - basicProjection x f N v)) atTop (𝓝 0) := by
    intro v
    have h1 : Tendsto (fun N => v - basicProjection x f N v) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := v)).sub (hx.expansion v)
      rw [sub_self] at this
      exact this
    have h2 := (hPc.tendsto 0).comp h1
    rw [map_zero] at h2
    exact h2
  have hcauchy : ∀ v, ∃ c, Tendsto (fun k => (∑ m ∈ Finset.range (k + 1), α m • f m) v)
      atTop (𝓝 c) := by
    intro v
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.2 fun ε hε => ?_)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((hPt v).eventually (Iio_mem_nhds hε))
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm, ← hproj N n hn v, ← map_sub]
    exact lt_of_le_of_lt (hPb n _) (hN N le_rfl)
  let ℓ : E → ℂ := fun v => limUnder atTop (fun k => (∑ m ∈ Finset.range (k + 1), α m • f m) v)
  have hℓ : ∀ v, Tendsto (fun k => (∑ m ∈ Finset.range (k + 1), α m • f m) v) atTop (𝓝 (ℓ v)) :=
    fun v => tendsto_nhds_limUnder (hcauchy v)
  let ℓlin : E →ₗ[ℂ] ℂ :=
    { toFun := ℓ
      map_add' := fun v w => by
        refine tendsto_nhds_unique (hℓ (v + w)) ?_
        have := (hℓ v).add (hℓ w)
        simp only [map_add]
        exact this
      map_smul' := fun c v => by
        refine tendsto_nhds_unique (hℓ (c • v)) ?_
        have := (hℓ v).const_mul c
        simp only [map_smul, smul_eq_mul]
        exact this }
  have hbound : ∀ v, ‖ℓ v‖ ≤ P v := fun v =>
    le_of_tendsto ((continuous_norm.tendsto _).comp (hℓ v))
      (Filter.Eventually.of_forall fun k => hPb k v)
  have hcont : Continuous ℓlin := by
    refine continuous_of_continuousAt_zero ℓlin ?_
    rw [ContinuousAt, map_zero]
    have h0 := hPc.tendsto 0
    rw [map_zero] at h0
    exact squeeze_zero_norm (fun v => hbound v) h0
  let φ : StrongDual ℂ E := ⟨ℓlin, hcont⟩
  have hφx : ∀ m, φ (x m) = α m := by
    intro m
    refine tendsto_nhds_unique (hℓ (x m)) (tendsto_atTop_of_eventually_const (i₀ := m) ?_)
    intro k hk
    rw [hΦapp]
    simp only [hx.biorthogonal, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.2 (by omega))]
  refine ⟨φ, ?_⟩
  have hfun : (fun k => ∑ m ∈ Finset.range (k + 1), α m • f m) =
      fun k => ∑ m ∈ Finset.range (k + 1), φ (x m) • f m := by
    funext k
    simp only [hφx]
  rw [hfun]
  exact ((hasSum_dual hp hrefl hx habs φ).tendsto_sum_nat).comp (Filter.tendsto_add_atTop_nat 1)

lemma bidual_part [T2Space E] [BarrelledSpace ℂ E] [ContinuousSMul ℂ E] [IsTopologicalAddGroup E]
    (hrefl : ∀ φ : StrongDual ℂ (StrongDual ℂ E), ∃! x : E, ∀ f : StrongDual ℂ E, φ f = f x)
    (hx : IsSchauderBasis x f) (ψ : StrongDual ℂ (StrongDual ℂ E)) :
    Filter.Tendsto
        (fun k => ∑ m ∈ Finset.range (k + 1), ψ (f m) •
          (Classical.epsilon fun e : StrongDual ℂ (StrongDual ℂ E) =>
            ∀ φ : StrongDual ℂ E, e φ = φ (x m)))
        Filter.atTop (nhds ψ) := by
  obtain ⟨u, hu, -⟩ := hrefl ψ
  have he : ∀ m (φ : StrongDual ℂ E),
      (Classical.epsilon fun e : StrongDual ℂ (StrongDual ℂ E) =>
        ∀ φ : StrongDual ℂ E, e φ = φ (x m)) φ = φ (x m) := fun m =>
    Classical.epsilon_spec (p := fun e : StrongDual ℂ (StrongDual ℂ E) =>
        ∀ φ : StrongDual ℂ E, e φ = φ (x m)) ⟨evl (x m), fun _ => rfl⟩
  have hfun : (fun k => ∑ m ∈ Finset.range (k + 1), ψ (f m) •
          (Classical.epsilon fun e : StrongDual ℂ (StrongDual ℂ E) =>
            ∀ φ : StrongDual ℂ E, e φ = φ (x m))) =
      fun k => evl (basicProjection x f k u) := by
    funext k
    refine ContinuousLinearMap.ext fun φ => ?_
    rw [evl_apply, proj_apply, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [ContinuousLinearMap.smul_apply, he, hu, smul_eq_mul, mul_comm]
  have hψ : ψ = evl u := ContinuousLinearMap.ext fun φ => hu φ
  rw [hfun, hψ, ← tendsto_sub_nhds_zero_iff]
  refine (ContinuousLinearMap.hasBasis_nhds_zero).tendsto_right_iff.2 ?_
  rintro ⟨C, V⟩ ⟨hC, hV⟩
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
  obtain ⟨P, hPc, hP⟩ := barrel_bound hC
  have h1 : Tendsto (fun k => basicProjection x f k u - u) atTop (𝓝 0) := by
    have := (hx.expansion u).sub (tendsto_const_nhds (x := u))
    rw [sub_self] at this
    exact this
  have h2 := (hPc.tendsto 0).comp h1
  rw [map_zero] at h2
  filter_upwards [h2.eventually (Iio_mem_nhds hε)] with k hk
  intro φ hφ
  apply hεV
  rw [Metric.mem_ball, dist_zero_right]
  have : (evl (basicProjection x f k u) - evl u) φ = φ (basicProjection x f k u - u) := by
    rw [ContinuousLinearMap.sub_apply, evl_apply, evl_apply, map_sub]
  rw [this]
  exact lt_of_le_of_lt (hP φ hφ _) hk

end basis
end Aux_absolute_basis_shrinking_boundedly_complete

open MasulloGRH

theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsHLCS E) (hc : IsCompleteTVS E) (hb : BarrelledSpace ℂ E) (hr : IsReflexive E)
    (x : ℕ → E) (f : ℕ → StrongDual ℂ E) (hx : IsSchauderBasis x f) (habs : IsAbsoluteBasis x f) :
    IsShrinkingBasis x f ∧ IsBoundedlyCompleteBasis x ∧
    (IsDualSchauderBasis x f ∧
      (∀ φ : StrongDual ℂ E, Summable (fun m => φ (x m) • f m)) ∧
      IsBoundedlyCompleteBasis f) ∧
    (IsNuclear E → ∀ ψ : StrongDual ℂ (StrongDual ℂ E),
      Filter.Tendsto
        (fun k => ∑ m ∈ Finset.range (k + 1), ψ (f m) •
          (Classical.epsilon fun e : StrongDual ℂ (StrongDual ℂ E) =>
            ∀ φ : StrongDual ℂ E, e φ = φ (x m)))
        Filter.atTop (nhds ψ)) := by
  obtain ⟨⟨ι, _, p, hp⟩, hT2⟩ := hE
  have := hp.topologicalAddGroup
  have := hp.continuousSMul
  have := hb
  have hrefl := hr.1
  have hdual : IsDualSchauderBasis x f :=
    ⟨hx.biorthogonal, fun φ =>
      ((Aux_absolute_basis_shrinking_boundedly_complete.hasSum_dual hp hrefl hx habs φ
        ).tendsto_sum_nat).comp (Filter.tendsto_add_atTop_nat 1)⟩
  refine ⟨hdual, Aux_absolute_basis_shrinking_boundedly_complete.bc_primal hrefl hx,
    ⟨hdual, fun φ => ⟨φ, Aux_absolute_basis_shrinking_boundedly_complete.hasSum_dual
      hp hrefl hx habs φ⟩,
      Aux_absolute_basis_shrinking_boundedly_complete.bc_dual hp hrefl hx habs⟩,
    fun _ ψ => Aux_absolute_basis_shrinking_boundedly_complete.bidual_part hrefl hx ψ⟩
