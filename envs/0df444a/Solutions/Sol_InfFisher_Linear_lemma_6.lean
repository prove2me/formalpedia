-- Prove2me | solution 1 for InfFisher.Linear.lemma_6
-- status  : ACCEPTED   (disprove)
-- author  : @queelius
-- created : 2026-10-18T06:20:08.042552+00:00
-- url     : https://prove2.me/submissions/f93b8ee7-87b2-4dfd-80dd-b4e755b8ef90

-- Counterexample to the full quantified continuum second welfare statement.
-- Research directed by Alexander Richard Towell (queelius); formalization by OpenAI Codex.
-- Source statement: Yuan Gao and Christian Kroer, arXiv:2010.03025v5, Lemma 6.
-- Platform formulation: mikedeng1. Mathlib provides the measure-theoretic foundations.
import Mathlib
import Definitions.Def_InfFisher_Linear_Setting
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory
open InfFisher.Linear
namespace FisherWelfare
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma pair_scale (f y : α → ℝ) (c : ℝ) :
    pair μ f (fun θ => c * y θ) = c * pair μ f y := by
  unfold pair
  rw [← integral_const_mul]
  congr 1
  funext θ
  ring

lemma pair_add {f x y : α → ℝ} (hf : Integrable f μ)
    (hx : MemLp x ⊤ μ) (hy : MemLp y ⊤ μ) :
    pair μ f (fun θ => x θ + y θ) = pair μ f x + pair μ f y := by
  unfold pair
  simp_rw [mul_add]
  exact integral_add ((memLp_one_iff_integrable.mpr hf).integrable_mul hx)
    ((memLp_one_iff_integrable.mpr hf).integrable_mul hy)

lemma bundle_scale {x : α → ℝ} (hx : IsBundle μ x) {c : ℝ} (hc : 0 ≤ c) :
    IsBundle μ (fun θ => c * x θ) := by
  refine ⟨hx.1.const_mul c, ?_⟩
  filter_upwards [hx.2] with θ hθ
  exact mul_nonneg hc hθ

lemma bundle_add {x y : α → ℝ} (hx : IsBundle μ x) (hy : IsBundle μ y) :
    IsBundle μ (fun θ => x θ + y θ) := by
  refine ⟨hx.1.add hy.1, ?_⟩
  filter_upwards [hx.2,hy.2] with θ hxθ hyθ
  exact add_nonneg hxθ hyθ

lemma positive_spending {n : ℕ} {v : Fin n → α → ℝ} {B : Fin n → ℝ}
    {p x : α → ℝ} {i : Fin n} (hp : IsPrice μ p)
    (hx : InDemand μ v B p i x) (hu : 0 < pair μ (v i) x) :
    0 < pair μ p x := by
  have hq : 0 ≤ pair μ p x := integral_nonneg_of_ae <| by
    filter_upwards [hp.2,hx.1.2] with θ hpθ hxθ
    exact mul_nonneg hpθ hxθ
  by_contra hn
  have hz : pair μ p x = 0 := le_antisymm (le_of_not_gt hn) hq
  have htwo := hx.2.2 (fun θ => 2*x θ) (bundle_scale hx.1 (by norm_num : (0:ℝ)≤2))
    (by rw [pair_scale,hz]; simpa [hz] using hx.2.1)
  rw [pair_scale] at htwo
  linarith

lemma demand_ratio {n : ℕ} {v : Fin n → α → ℝ} {B : Fin n → ℝ}
    {p x y : α → ℝ} {i : Fin n} (hp : IsPrice μ p)
    (hv : Integrable (v i) μ) (hx : InDemand μ v B p i x)
    (hu : 0 < pair μ (v i) x) (hy : IsBundle μ y) :
    pair μ p x * pair μ (v i) y ≤ pair μ p y * pair μ (v i) x := by
  let q := pair μ p x
  let c := pair μ p y
  have hq : 0 < q := positive_spending hp hx hu
  have hc : 0 ≤ c := integral_nonneg_of_ae <| by
    filter_upwards [hp.2,hy.2] with θ hpθ hyθ
    exact mul_nonneg hpθ hyθ
  have hqc : 0 < q+c := add_pos_of_pos_of_nonneg hq hc
  have hcost : pair μ p (fun θ => (q/(q+c))*(x θ+y θ)) = q := by
    rw [pair_scale,pair_add hp.1 hx.1.1 hy.1]
    exact div_mul_cancel₀ q (ne_of_gt hqc)
  have hopt := hx.2.2 (fun θ => (q/(q+c))*(x θ+y θ))
    (bundle_scale (bundle_add hx.1 hy) (div_nonneg hq.le hqc.le))
    (by rw [hcost]; exact hx.2.1)
  rw [pair_scale,pair_add hv hx.1.1 hy.1] at hopt
  have hmul := (div_le_iff₀ hqc).mp (show
    q*(pair μ (v i) x+pair μ (v i) y)/(q+c) ≤ pair μ (v i) x by
      simpa only [div_mul_eq_mul_div] using hopt)
  change q*pair μ (v i) y ≤ c*pair μ (v i) x
  nlinarith

end FisherWelfare
#print axioms FisherWelfare.positive_spending
#print axioms FisherWelfare.demand_ratio

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory
namespace FisherWelfare
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

lemma split_pareto (w : α → ℝ) (hw : Integrable w μ) (hw0 : ∀ θ, 0 ≤ w θ)
    (x : Fin 2 → α → ℝ) (hx : InfFisher.EG.IsAllocation μ x)
    (hx0 : ∀ θ, x 0 θ = if w θ = 0 then 1 else 0)
    (hx1 : ∀ θ, x 1 θ = if w θ = 0 then 0 else 1) :
    InfFisher.EG.IsParetoOptimal μ ![fun _ => 1, w] x := by
  refine ⟨hx, ?_⟩
  rintro ⟨y, hy, hge, i, hstrict⟩
  have hint (j : Fin 2) : Integrable (y j) μ :=
    ((hy.1 j).1.mono_exponent (by simp : (1:ENNReal) ≤ ⊤)).integrable le_rfl
  have hsum : ∀ᵐ θ ∂μ, y 0 θ + y 1 θ ≤ 1 := by
    simpa only [Fin.sum_univ_two] using hy.2
  have hy1 : ∀ᵐ θ ∂μ, y 1 θ ≤ 1 := by
    filter_upwards [hsum,(hy.1 0).2] with θ hθ h0
    change 0 ≤ y 0 θ at h0
    linarith
  have hxw : InfFisher.EG.pair μ w (x 1) = ∫ θ, w θ ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun θ => by by_cases h : w θ=0 <;> simp [hx1,h])
  have hwy : Integrable (fun θ => w θ*y 1 θ) μ :=
    (memLp_one_iff_integrable.mpr hw).integrable_mul (hy.1 1).1
  have hupper : InfFisher.EG.pair μ w (y 1) ≤ ∫ θ, w θ ∂μ := by
    apply integral_mono_ae hwy hw
    filter_upwards [hy1] with θ hθ
    exact mul_le_of_le_one_right (hw0 θ) hθ
  have heq : InfFisher.EG.pair μ w (y 1) = ∫ θ, w θ ∂μ := by
    apply le_antisymm hupper
    simpa [hxw] using hge 1
  have hdiff : Integrable (fun θ => w θ-w θ*y 1 θ) μ := hw.sub hwy
  have hdiff0 : 0 ≤ᵐ[μ] (fun θ => w θ-w θ*y 1 θ) := by
    filter_upwards [hy1] with θ hθ
    exact sub_nonneg.mpr (mul_le_of_le_one_right (hw0 θ) hθ)
  have hzero : (fun θ => w θ-w θ*y 1 θ) =ᵐ[μ] 0 := by
    apply (integral_eq_zero_iff_of_nonneg_ae hdiff0 hdiff).mp
    rw [integral_sub hw hwy]
    change (∫ θ, w θ ∂μ) - InfFisher.EG.pair μ w (y 1) = 0
    rw [heq,sub_self]
  have hle0 : y 0 ≤ᵐ[μ] x 0 := by
    filter_upwards [hsum,(hy.1 1).2,hzero] with θ hs hn hz
    change 0 ≤ y 1 θ at hn
    rw [hx0]
    split_ifs with h
    · linarith
    · have hpos := lt_of_le_of_ne (hw0 θ) (Ne.symm h)
      have hyone : y 1 θ = 1 := by
        change w θ-w θ*y 1 θ=0 at hz
        nlinarith
      linarith
  have hu0 : InfFisher.EG.pair μ (fun _ => 1) (y 0) ≤
      InfFisher.EG.pair μ (fun _ => 1) (x 0) := by
    simp only [InfFisher.EG.pair,one_mul]
    exact integral_mono_ae (hint 0)
      (((hx.1 0).1.mono_exponent (by simp : (1:ENNReal) ≤ ⊤)).integrable le_rfl) hle0
  fin_cases i
  · simpa using (not_lt_of_ge hu0 hstrict)
  · have : InfFisher.EG.pair μ w (x 1) < InfFisher.EG.pair μ w (y 1) := by simpa using hstrict
    rw [hxw,heq] at this
    exact lt_irrefl _ this

end FisherWelfare
namespace FisherWelfare
open InfFisher.Linear
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma pair_sub {f x y : α → ℝ} (hf : Integrable f μ)
    (hx : MemLp x ⊤ μ) (hy : MemLp y ⊤ μ) :
    pair μ f (fun θ => x θ-y θ) = pair μ f x-pair μ f y := by
  unfold pair
  simp_rw [mul_sub]
  exact integral_sub ((memLp_one_iff_integrable.mpr hf).integrable_mul hx)
    ((memLp_one_iff_integrable.mpr hf).integrable_mul hy)

lemma no_equilibrium_of_small_strips (w : α → ℝ) (hw : Integrable w μ)
    (h1 : Integrable (fun _ : α => (1:ℝ)) μ) (x : Fin 2 → α → ℝ)
    (hu0 : 0 < pair μ (fun _ => 1) (x 0)) (hu1 : 0 < pair μ w (x 1))
    (hstrips : ∀ ε : ℝ, 0 < ε → ∃ z : α → ℝ, IsBundle μ z ∧
      z ≤ᵐ[μ] x 1 ∧ 0 < pair μ (fun _ => 1) z ∧
      pair μ w z ≤ ε*pair μ (fun _ => 1) z) :
    ∀ B : Fin 2 → ℝ, ∀ p, ¬ IsME μ ![fun _ => 1,w] B x p := by
  intro B p he
  have hd0 : InDemand μ ![fun _ => 1,w] B p 0 (x 0) := he.2.2.1 0
  have hd1 : InDemand μ ![fun _ => 1,w] B p 1 (x 1) := he.2.2.1 1
  let q0 := pair μ p (x 0)
  let q1 := pair μ p (x 1)
  let u0 := pair μ (fun _ => 1) (x 0)
  let u1 := pair μ w (x 1)
  have hq0 : 0 < q0 := positive_spending he.1 hd0 hu0
  have hq1 : 0 < q1 := positive_spending he.1 hd1 hu1
  have hu0' : 0 < u0 := hu0
  have hu1' : 0 < u1 := hu1
  let ε := q0*u1/(2*u0*q1)
  have hε : 0 < ε := div_pos (mul_pos hq0 hu1') (by positivity)
  obtain ⟨z,hz,hzx,hzpos,hzw⟩ := hstrips ε hε
  have hrem : IsBundle μ (fun θ => x 1 θ-z θ) := by
    refine ⟨(he.2.1.1 1).1.sub hz.1, ?_⟩
    filter_upwards [hzx] with θ hθ
    exact sub_nonneg.mpr hθ
  have hleft : q0*pair μ (fun _ => 1) z ≤ pair μ p z*u0 := by
    exact demand_ratio he.1 h1 hd0 hu0 hz
  have hright : pair μ p z*u1 ≤ q1*pair μ w z := by
    have h := demand_ratio he.1 hw hd1 hu1 hrem
    dsimp only [Matrix.cons_val_one,Matrix.cons_val_zero] at h
    rw [pair_sub hw (he.2.1.1 1).1 hz.1,
      pair_sub he.1.1 (he.2.1.1 1).1 hz.1] at h
    change q1*(u1-pair μ w z) ≤ (q1-pair μ p z)*u1 at h
    nlinarith
  have hmul1 := mul_le_mul_of_nonneg_right hleft hu1'.le
  have hmul2 := mul_le_mul_of_nonneg_right hright hu0'.le
  have hmul3 := mul_le_mul_of_nonneg_left hzw (mul_nonneg hu0'.le hq1.le)
  have hbound : q0*u1 ≤ u0*q1*ε := by
    apply (mul_le_mul_iff_of_pos_right hzpos).mp
    nlinarith
  have hid : (u0*q1)*ε = q0*u1/2 := by
    dsimp [ε]
    field_simp
  rw [hid] at hbound
  nlinarith [mul_pos hq0 hu1']

end FisherWelfare
namespace FisherWelfare
open InfFisher.Linear
abbrev Item := EuclideanSpace ℝ (Fin 1)
def region : Set Item := Metric.closedBall 0 1
noncomputable def measure : Measure Item := volume.restrict region
lemma region_compact : IsCompact region := isCompact_closedBall 0 1
instance : IsFiniteMeasure measure :=
  isFiniteMeasure_restrict.mpr region_compact.measure_lt_top.ne
def val : Item → ℝ := fun θ => max (θ 0) 0
lemma val_cont : Continuous val := by unfold val; fun_prop
lemma val_int : Integrable val measure := val_cont.continuousOn.integrableOn_compact region_compact
lemma val_nonneg (θ : Item) : 0 ≤ val θ := le_max_right _ _
def zeroSet : Set Item := {θ | val θ = 0}
lemma zeroSet_measurable : MeasurableSet zeroSet := (isClosed_singleton.preimage val_cont).measurableSet
noncomputable def alloc : Fin 2 → Item → ℝ :=
  ![zeroSet.indicator (fun _ => 1), zeroSetᶜ.indicator (fun _ => 1)]
lemma alloc0 (θ : Item) : alloc 0 θ = if val θ=0 then 1 else 0 := by
  classical
  simp [alloc,Set.indicator,zeroSet]
lemma alloc1 (θ : Item) : alloc 1 θ = if val θ=0 then 0 else 1 := by
  classical
  by_cases h : val θ=0 <;> simp [alloc,zeroSet,h]
lemma alloc_feasible : InfFisher.EG.IsAllocation measure alloc := by
  constructor
  · intro i
    fin_cases i
    · refine ⟨(memLp_top_const (1:ℝ)).indicator zeroSet_measurable, Filter.Eventually.of_forall ?_⟩
      intro θ
      change 0 ≤ alloc 0 θ
      rw [alloc0]
      split_ifs <;> norm_num
    · refine ⟨(memLp_top_const (1:ℝ)).indicator zeroSet_measurable.compl, Filter.Eventually.of_forall ?_⟩
      intro θ
      change 0 ≤ alloc 1 θ
      rw [alloc1]
      split_ifs <;> norm_num
  · apply Filter.Eventually.of_forall
    intro θ
    simp only [Fin.sum_univ_two,alloc0,alloc1]
    split_ifs <;> norm_num
lemma alloc_pareto : InfFisher.EG.IsParetoOptimal measure ![fun _ => 1,val] alloc :=
  split_pareto val val_int val_nonneg alloc alloc_feasible alloc0 alloc1

lemma open_measure_pos {U : Set Item} (ho : IsOpen U) (hne : U.Nonempty)
    (hsub : U ⊆ region) : 0 < measure U := by
  rw [measure,Measure.restrict_apply ho.measurableSet,Set.inter_eq_left.mpr hsub]
  exact ho.measure_pos volume hne

def strip (ε : ℝ) : Set Item := {θ | ‖θ‖ < 1 ∧ 0 < θ 0 ∧ θ 0 < ε}
lemma strip_open (ε : ℝ) : IsOpen (strip ε) := by
  exact (isOpen_lt continuous_norm continuous_const).inter
    ((isOpen_lt continuous_const (by fun_prop : Continuous (fun θ : Item => θ 0))).inter
    (isOpen_lt (by fun_prop : Continuous (fun θ : Item => θ 0)) continuous_const))
lemma strip_nonempty {ε : ℝ} (hε : 0 < ε) : (strip ε).Nonempty := by
  let r := min (ε/2) (1/2)
  have hr : 0 < r := lt_min (by linarith) (by norm_num)
  have hr1 : r < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hre : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨EuclideanSpace.single 0 r, ?_⟩
  simpa [strip,PiLp.single_apply,PiLp.norm_single,Real.norm_eq_abs,abs_of_pos hr]
    using And.intro hr1 (And.intro hr hre)
lemma strip_subset (ε : ℝ) : strip ε ⊆ region := by
  intro θ hθ
  simpa [region,Metric.mem_closedBall,dist_zero_right] using hθ.1.le
lemma strip_pos {ε : ℝ} (hε : 0 < ε) : 0 < measure (strip ε) :=
  open_measure_pos (strip_open ε) (strip_nonempty hε) (strip_subset ε)

lemma val_pos_integral : 0 < ∫ θ, val θ ∂measure := by
  apply (integral_pos_iff_support_of_nonneg val_nonneg val_int).mpr
  apply lt_of_lt_of_le (strip_pos (by norm_num : (0:ℝ)<1))
  apply measure_mono
  intro θ hθ
  exact ne_of_gt (lt_of_lt_of_le hθ.2.1 (le_max_left _ _))

lemma alloc1_utility : pair measure val (alloc 1) = ∫ θ, val θ ∂measure := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun θ => by by_cases h : val θ=0 <;> simp [alloc1,h])

lemma alloc0_utility_pos : 0 < pair measure (fun _ => 1) (alloc 0) := by
  simp only [pair,one_mul]
  apply (integral_pos_iff_support_of_nonneg
    (fun θ => by rw [alloc0]; split_ifs <;> norm_num)
    ((alloc_feasible.1 0).1.integrable (by simp))).mpr
  let U : Set Item := {θ | ‖θ‖ < 1 ∧ θ 0 < 0}
  have ho : IsOpen U := (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt (by fun_prop : Continuous (fun θ : Item => θ 0)) continuous_const)
  have hn : U.Nonempty := by
    refine ⟨EuclideanSpace.single 0 (-1/2), ?_⟩
    norm_num [U,PiLp.single_apply,PiLp.norm_single,Real.norm_eq_abs]
  have hs : U ⊆ region := by
    intro θ hθ
    simpa [region,Metric.mem_closedBall,dist_zero_right] using hθ.1.le
  apply lt_of_lt_of_le (open_measure_pos ho hn hs)
  apply measure_mono
  intro θ hθ
  have hv : val θ=0 := max_eq_right hθ.2.le
  simp [Function.mem_support,alloc0,hv]

lemma small_strips (ε : ℝ) (hε : 0 < ε) :
    ∃ z : Item → ℝ, IsBundle measure z ∧ z ≤ᵐ[measure] alloc 1 ∧
      0 < pair measure (fun _ => 1) z ∧ pair measure val z ≤ ε*pair measure (fun _ => 1) z := by
  let z := (strip ε).indicator (fun _ => (1:ℝ))
  have hz : IsBundle measure z :=
    ⟨(memLp_top_const (1:ℝ)).indicator (strip_open ε).measurableSet,
      Filter.Eventually.of_forall (fun θ => Set.indicator_nonneg (fun _ _ => by norm_num) θ)⟩
  have hint : Integrable z measure := hz.1.integrable (by simp)
  refine ⟨z,hz,?_,?_,?_⟩
  · exact Filter.Eventually.of_forall (fun θ => by
      by_cases hθ : θ∈strip ε
      · have hv : val θ≠0 := ne_of_gt (lt_of_lt_of_le hθ.2.1 (le_max_left _ _))
        simp [z,hθ,alloc1,hv]
      · simp only [z,Set.indicator_of_notMem hθ,alloc1]
        split_ifs <;> norm_num)
  · simp only [pair,one_mul]
    apply (integral_pos_iff_support_of_nonneg_ae hz.2 hint).mpr
    simpa [z,Function.support] using strip_pos hε
  · rw [pair,pair,← integral_const_mul]
    apply integral_mono_ae ((memLp_one_iff_integrable.mpr val_int).integrable_mul hz.1)
      (by simpa only [one_mul] using hint.const_mul ε)
    exact Filter.Eventually.of_forall (fun θ => by
      by_cases hθ : θ∈strip ε
      · simp only [Pi.mul_apply,z,Set.indicator_of_mem hθ,mul_one]
        exact max_le hθ.2.2.le hε.le
      · simp [z,hθ,Pi.mul_apply])

lemma no_supporting_equilibrium (B : Fin 2 → ℝ) (p : Item → ℝ) :
    ¬ IsME measure ![fun _ => 1,val] B alloc p :=
  no_equilibrium_of_small_strips val val_int (integrable_const 1) alloc
    alloc0_utility_pos (by rw [alloc1_utility]; exact val_pos_integral) small_strips B p

end FisherWelfare
open MeasureTheory
theorem solution : ¬ (∀ {d n : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d))),
    IsCompact Θ → ∀ (v : Fin n → EuclideanSpace ℝ (Fin d) → ℝ),
    (∀ i, Integrable (v i) (volume.restrict Θ)) →
    (∀ i, 0 ≤ᵐ[volume.restrict Θ] v i) →
    (∀ i, 0 < ∫ θ in Θ, v i θ) →
    ∀ (x : Fin n → EuclideanSpace ℝ (Fin d) → ℝ),
    InfFisher.EG.IsParetoOptimal (volume.restrict Θ) v x →
    ∃ B : Fin n → ℝ, (∀ i, 0 ≤ B i) ∧
      ∃ p, InfFisher.Linear.IsME (volume.restrict Θ) v B x p) := by
  intro hall
  have hv : ∀ i : Fin 2, Integrable (![fun _ => 1,FisherWelfare.val] i) FisherWelfare.measure := by
    intro i
    fin_cases i
    · exact integrable_const 1
    · exact FisherWelfare.val_int
  have hv0 : ∀ i : Fin 2, 0 ≤ᵐ[FisherWelfare.measure] (![fun _ => 1,FisherWelfare.val] i) := by
    intro i
    fin_cases i
    · exact Filter.Eventually.of_forall (fun _ => by norm_num)
    · exact Filter.Eventually.of_forall FisherWelfare.val_nonneg
  have hvpos : ∀ i : Fin 2, 0 < ∫ θ, (![fun _ => 1,FisherWelfare.val] i) θ ∂FisherWelfare.measure := by
    intro i
    fin_cases i
    · change 0 < ∫ _ : FisherWelfare.Item, (1:ℝ) ∂FisherWelfare.measure
      apply (integral_pos_iff_support_of_nonneg (fun _ => by norm_num) (integrable_const 1)).mpr
      apply lt_of_lt_of_le (FisherWelfare.strip_pos (by norm_num : (0:ℝ)<1))
      apply measure_mono
      intro θ _
      simp [Function.mem_support]
    · exact FisherWelfare.val_pos_integral
  obtain ⟨B,_,p,hp⟩ := hall FisherWelfare.region FisherWelfare.region_compact
    ![fun _ => 1,FisherWelfare.val] hv hv0 hvpos FisherWelfare.alloc FisherWelfare.alloc_pareto
  exact FisherWelfare.no_supporting_equilibrium B p hp
