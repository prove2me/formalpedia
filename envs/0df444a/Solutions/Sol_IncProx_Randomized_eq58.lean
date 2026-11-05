-- Prove2me | solution 1 for IncProx.Randomized.eq58
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T00:02:36.501985+00:00
-- url     : https://prove2.me/submissions/9a464285-eb70-4ee2-a691-f4554a56e37f

import Mathlib
import Definitions.Def_IncProx_Randomized_Basic

open Filter Topology MeasureTheory ProbabilityTheory
open IncProx.Randomized

namespace IncProx2Inf

variable {n m : ℕ}

/-! ### Section A: deterministic one-step inequalities -/

lemma proj_inner {X : Set (Vec n)} (hX : Convex ℝ X) {u p : Vec n} (hp : IsProj X u p) :
    ∀ y ∈ X, inner ℝ (u - p) (y - p) ≤ 0 := by
  have : Nonempty X := ⟨⟨p, hp.1⟩⟩
  have : ‖u - p‖ = ⨅ w : X, ‖u - w‖ := by
    apply le_antisymm
    · exact le_ciInf (fun w => hp.2 w w.2)
    · exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ (⟨p, hp.1⟩ : X)
  exact (norm_eq_iInf_iff_real_inner_le_zero hX hp.1).1 this

/-- Prop. 1(b), strengthened: the proximal-type step `z` with `⟨x - a g - z, y - z⟩ ≤ 0`,
`g ∈ ∂f(z)`. -/
lemma prox_ineq {f : Vec n → ℝ} {x z g y : Vec n} {a : ℝ} (ha : 0 ≤ a) (hg : IsSubgrad f z g)
    (hw : inner ℝ (x - a • g - z) (y - z) ≤ 0) :
    ‖z - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 - ‖x - z‖ ^ 2 - 2 * a * (f z - f y) := by
  have hs := hg y
  have e : ‖x - y‖ ^ 2 = ‖x - z‖ ^ 2 + 2 * inner ℝ (x - z) (z - y) + ‖z - y‖ ^ 2 := by
    have : x - y = (x - z) + (z - y) := by abel
    rw [this, norm_add_sq_real]
  have e2 : inner ℝ (x - z) (z - y) =
      - inner ℝ (x - a • g - z) (y - z) - a * inner ℝ g (y - z) := by
    have h1 : x - z = (x - a • g - z) + a • g := by abel
    have h2 : z - y = -(y - z) := by abel
    rw [h1, h2, inner_add_left, real_inner_smul_left, inner_neg_right, inner_neg_right]
    ring
  have := mul_le_mul_of_nonneg_left hs ha
  nlinarith

lemma proj_dist {X : Set (Vec n)} (hX : Convex ℝ X) {u p y : Vec n} (hp : IsProj X u p)
    (hy : y ∈ X) : ‖p - y‖ ^ 2 ≤ ‖u - y‖ ^ 2 - ‖u - p‖ ^ 2 := by
  have hi := proj_inner hX hp y hy
  have e : ‖u - y‖ ^ 2 = ‖u - p‖ ^ 2 + 2 * inner ℝ (u - p) (p - y) + ‖p - y‖ ^ 2 := by
    have : u - y = (u - p) + (p - y) := by abel
    rw [this, norm_add_sq_real]
  have e2 : inner ℝ (u - p) (p - y) = - inner ℝ (u - p) (y - p) := by
    rw [← inner_neg_right]; congr 1; abel
  nlinarith

lemma grad_ineq {h : Vec n → ℝ} {z g y : Vec n} {a : ℝ} (hg : IsSubgrad h z g) (ha : 0 ≤ a) :
    ‖z - a • g - y‖ ^ 2 ≤ ‖z - y‖ ^ 2 - 2 * a * (h z - h y) + a ^ 2 * ‖g‖ ^ 2 := by
  have hs := hg y
  have e : ‖z - a • g - y‖ ^ 2 = ‖z - y‖ ^ 2 - 2 * inner ℝ (z - y) (a • g) + ‖a • g‖ ^ 2 := by
    have : z - a • g - y = (z - y) - a • g := by abel
    rw [this, norm_sub_sq_real]
  rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha] at e
  have e2 : inner ℝ (z - y) g = - inner ℝ g (y - z) := by
    rw [real_inner_comm, ← inner_neg_right]; congr 1; abel
  rw [e, e2]
  nlinarith [mul_le_mul_of_nonneg_left hs ha]

/-- Eq. (30) + (45)/(46) for iterations (19), (20) (per component). -/
lemma step_ineq_ab {P : Problem n m} (hP : P.Standing) {i : Fin m} {a c : ℝ} (ha : 0 ≤ a)
    {x z gH x' y : Vec n} (hy : y ∈ P.X)
    (hz : ‖z - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 - ‖x - z‖ ^ 2 - 2 * a * (P.f i z - P.f i y))
    (hgH : IsSubgrad (P.h i) z gH) (hx' : IsProj P.X (z - a • gH) x')
    (b1 : ‖gH‖ ≤ c) (b2 : P.f i x - P.f i z ≤ c * ‖x - z‖)
    (b3 : P.h i x - P.h i z ≤ c * ‖x - z‖) :
    ‖x' - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 - 2 * a * (P.Fi i x - P.Fi i y) + 5 * a ^ 2 * c ^ 2 := by
  have h1 := proj_dist hP.X_convex hx' hy
  have h2 := grad_ineq hgH ha (y := y)
  have hc2 : ‖gH‖ ^ 2 ≤ c ^ 2 := by
    have := norm_nonneg gH; nlinarith
  set d := ‖x - z‖
  have hd := norm_nonneg (x - z)
  have m1 := mul_le_mul_of_nonneg_left b2 ha
  have m2 := mul_le_mul_of_nonneg_left b3 ha
  have m3 := mul_le_mul_of_nonneg_left hc2 (sq_nonneg a)
  have hsq := sq_nonneg (d - 2 * a * c)
  have hnn := sq_nonneg ‖z - a • gH - x'‖
  unfold Problem.Fi
  nlinarith


/-- Eqs. (35)–(37) + (47)/(48) for iteration (21) (per component). -/
lemma step_ineq_c {P : Problem n m} (hP : P.Standing) {i : Fin m} {a c : ℝ} (ha : 0 ≤ a)
    {x z gF gH x' y : Vec n} (hy : y ∈ P.X)
    (hgH : IsSubgrad (P.h i) x gH) (hz : z = x - a • gH) (hgF : IsSubgrad (P.f i) x' gF)
    (hx' : IsProj P.X (z - a • gF) x')
    (b1 : ‖gF‖ ≤ c) (b2 : ‖gH‖ ≤ c) (b3 : P.f i x - P.f i x' ≤ c * ‖x - x'‖) :
    ‖x' - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 - 2 * a * (P.Fi i x - P.Fi i y) + 5 * a ^ 2 * c ^ 2 := by
  have hzi := grad_ineq hgH ha (y := y)
  rw [← hz] at hzi
  have hpi := prox_ineq ha hgF (proj_inner hP.X_convex hx' y hy)
  have hc : 0 ≤ c := le_trans (norm_nonneg _) b1
  have hxz : ‖x - z‖ ≤ a * c := by
    rw [hz, show x - (x - a • gH) = a • gH by abel, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left b2 ha
  have hxx' : ‖x - x'‖ ≤ a * c + ‖z - x'‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub x z x'
    linarith
  have hc2 : ‖gH‖ ^ 2 ≤ c ^ 2 := by
    have := norm_nonneg gH; nlinarith
  set e := ‖z - x'‖
  have he := norm_nonneg (z - x')
  have m1 : a * (P.f i x - P.f i x') ≤ a * (c * (a * c + e)) :=
    mul_le_mul_of_nonneg_left (le_trans b3 (mul_le_mul_of_nonneg_left hxx' hc)) ha
  have m3 := mul_le_mul_of_nonneg_left hc2 (sq_nonneg a)
  have hsq := sq_nonneg (e - a * c)
  have hac : 0 ≤ a ^ 2 * c ^ 2 := by positivity
  unfold Problem.Fi
  nlinarith

lemma step_a19 {P : Problem n m} (hP : P.Standing) {i : Fin m} {a c : ℝ} (ha : 0 ≤ a)
    {x z gF gH x' y : Vec n} (hy : y ∈ P.X) (hstep : Step P .a19 i a x z gF gH x')
    (b1 : ‖gH‖ ≤ c) (b2 : P.f i x - P.f i z ≤ c * ‖x - z‖)
    (b3 : P.h i x - P.h i z ≤ c * ‖x - z‖) :
    ‖x' - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 - 2 * a * (P.Fi i x - P.Fi i y) + 5 * a ^ 2 * c ^ 2 := by
  obtain ⟨hgF, hz, hgH, hx'⟩ := hstep
  exact step_ineq_ab hP ha hy (prox_ineq ha hgF (proj_inner hP.X_convex hz y hy)) hgH hx' b1 b2 b3


lemma step_a20 {P : Problem n m} (hP : P.Standing) {i : Fin m} {a c : ℝ} (ha : 0 ≤ a)
    {x z gF gH x' y : Vec n} (hy : y ∈ P.X) (hstep : Step P .a20 i a x z gF gH x')
    (b1 : ‖gH‖ ≤ c) (b2 : P.f i x - P.f i z ≤ c * ‖x - z‖)
    (b3 : P.h i x - P.h i z ≤ c * ‖x - z‖) :
    ‖x' - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 - 2 * a * (P.Fi i x - P.Fi i y) + 5 * a ^ 2 * c ^ 2 := by
  obtain ⟨hgF, hz, hgH, hx'⟩ := hstep
  have hw : inner ℝ (x - a • gF - z) (y - z) ≤ 0 := by
    rw [hz, sub_self, inner_zero_left]
  exact step_ineq_ab hP ha hy (prox_ineq ha hgF hw) hgH hx' b1 b2 b3

lemma step_a21 {P : Problem n m} (hP : P.Standing) {i : Fin m} {a c : ℝ} (ha : 0 ≤ a)
    {x z gF gH x' y : Vec n} (hy : y ∈ P.X) (hstep : Step P .a21 i a x z gF gH x')
    (b1 : ‖gF‖ ≤ c) (b2 : ‖gH‖ ≤ c) (b3 : P.f i x - P.f i x' ≤ c * ‖x - x'‖) :
    ‖x' - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 - 2 * a * (P.Fi i x - P.Fi i y) + 5 * a ^ 2 * c ^ 2 := by
  obtain ⟨hgH, hz, hgF, hx'⟩ := hstep
  exact step_ineq_c hP ha hy hgH hz hgF hx' b1 b2 b3

/-- Every next iterate lies in `X`. -/
lemma step_mem {P : Problem n m} {A : Alg} {i : Fin m} {a : ℝ} {x z gF gH x' : Vec n}
    (hstep : Step P A i a x z gF gH x') : x' ∈ P.X := by
  cases A
  · exact hstep.2.2.2.1
  · exact hstep.2.2.2.1
  · exact hstep.2.2.2.1


/-! ### Section B: measure-theoretic infrastructure -/

lemma Fi_cont {P : Problem n m} (hP : P.Standing) (i : Fin m) : Continuous (P.Fi i) := by
  have hf := (hP.f_convex i).continuousOn isOpen_univ
  have hh := (hP.h_convex i).continuousOn isOpen_univ
  rw [continuousOn_univ] at hf hh
  exact hf.add hh

lemma F_cont {P : Problem n m} (hP : P.Standing) : Continuous P.F := by
  unfold Problem.F
  exact continuous_finsetSum _ (fun i _ => Fi_cont hP i)

lemma Fi_lb {P : Problem n m} (hP : P.Standing) (R : ℝ) :
    ∃ B, ∀ i, ∀ v : Vec n, ‖v‖ ≤ R → B ≤ P.Fi i v := by
  have hg : Continuous (fun v => ∑ i, |P.Fi i v|) :=
    continuous_finsetSum _ (fun i _ => (Fi_cont hP i).abs)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Vec n) R).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨-C, fun i v hv => ?_⟩
  have h1 := hC v (by simpa using hv)
  have h2 : |P.Fi i v| ≤ ∑ j, |P.Fi j v| :=
    Finset.single_le_sum (f := fun j => |P.Fi j v|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _))] at h1
  have := neg_abs_le (P.Fi i v)
  linarith

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma meas_sel {E : Type*} [MeasurableSpace E] {g : Fin m → Ω → E} (hg : ∀ i, Measurable (g i))
    {w : Ω → Fin m} (hw : Measurable w) : Measurable (fun s => g (w s) s) := by
  have : Measurable (fun p : Ω × Fin m => g p.2 p.1) :=
    measurable_from_prod_countable_left (fun i => hg i)
  exact this.comp (measurable_id.prodMk hw)

lemma hist_mono (x z : ℕ → Ω → Vec n) {j k : ℕ} (h : j ≤ k) : hist x z j ≤ hist x z k := by
  unfold hist
  apply sup_le_sup
  · exact biSup_mono (fun i hi => by simp at hi ⊢; omega)
  · exact biSup_mono (fun i hi => by simp at hi ⊢; omega)

lemma x_meas_hist (x z : ℕ → Ω → Vec n) (k : ℕ) : Measurable[hist x z k] (x k) := by
  rw [measurable_iff_comap_le]
  unfold hist
  exact le_sup_of_le_left (le_iSup₂ (f := fun j (_ : j ∈ Finset.range (k + 1)) =>
    MeasurableSpace.comap (x j) inferInstance) k (by simp))

lemma hist_le {x : ℕ → Ω → Vec n} {ω : ℕ → Ω → Fin m} {zc : ℕ → Fin m → Ω → Vec n}
    (hx : ∀ k, Measurable (x k)) (hω : ∀ k, Measurable (ω k))
    (hzc : ∀ k i, Measurable[hist x (zOf ω zc) k] (zc k i)) :
    ∀ k, hist x (zOf ω zc) k ≤ mΩ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have key : ∀ j < k, Measurable (zOf ω zc j) := fun j hjk =>
      meas_sel (fun i => (hzc j i).mono (ih j hjk) le_rfl) (hω j)
    show (⨆ j ∈ Finset.range (k + 1), MeasurableSpace.comap (x j) inferInstance) ⊔
      (⨆ j ∈ Finset.range k, MeasurableSpace.comap (zOf ω zc j) inferInstance) ≤ mΩ
    refine sup_le (iSup₂_le fun j _ => (hx j).comap_le) (iSup₂_le fun j hj => ?_)
    exact (key j (by simpa using hj)).comap_le

/-- The filtration `F_k`. -/
def histF (x z : ℕ → Ω → Vec n) (hle : ∀ k, hist x z k ≤ mΩ) : Filtration ℕ mΩ where
  seq k := hist x z k
  mono' _ _ h := hist_mono x z h
  le' := hle

/-- Conditional expectation of the step with the uniformly sampled, independent component. -/
lemma condexp_select {Ω' : Type*} {G mΩ' : MeasurableSpace Ω'} (μ : Measure Ω')
    [IsProbabilityMeasure μ] [NeZero m] (hG : G ≤ mΩ') {w : Ω' → Fin m} (hw : Measurable w)
    (hunif : ∀ i, μ {s | w s = i} = (m : ENNReal)⁻¹)
    (hind : Indep (MeasurableSpace.comap w inferInstance) G μ)
    (g : Fin m → Ω' → ℝ) (hgm : ∀ i, StronglyMeasurable[G] (g i)) (hgi : ∀ i, Integrable (g i) μ) :
    μ[fun s => g (w s) s | G] =ᵐ[μ] fun s => (m : ℝ)⁻¹ * ∑ i, g i s := by
  set ind : Fin m → Ω' → ℝ := fun i => {s | w s = i}.indicator 1 with hind_def
  have hset : ∀ i, MeasurableSet {s | w s = i} := fun i => hw (measurableSet_singleton i)
  have hdecomp : (fun s => g (w s) s) = ∑ i, (ind i * g i) := by
    funext s
    simp only [Finset.sum_apply, Pi.mul_apply, hind_def, Set.indicator_apply, Set.mem_ofPred_eq,
      Pi.one_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]; simp
  have hindm : ∀ i, StronglyMeasurable[MeasurableSpace.comap w inferInstance] (ind i) := by
    intro i
    have : Measurable[MeasurableSpace.comap w inferInstance]
        ((fun j : Fin m => if j = i then (1 : ℝ) else 0) ∘ w) :=
      (measurable_of_finite _).comp (comap_measurable w)
    have heq : ind i = (fun j : Fin m => if j = i then (1 : ℝ) else 0) ∘ w := by
      funext s; simp [hind_def, Set.indicator_apply]
    rw [heq]; exact this.stronglyMeasurable
  have hindint : ∀ i, Integrable (ind i) μ := fun i =>
    (integrable_const (1 : ℝ)).indicator (hset i)
  have hprodint : ∀ i, Integrable (ind i * g i) μ := by
    intro i
    refine Integrable.mono' (hgi i).norm ((hindint i).aestronglyMeasurable.mul
      (hgi i).aestronglyMeasurable) (Eventually.of_forall fun s => ?_)
    simp only [Pi.mul_apply, hind_def, Set.indicator_apply, Pi.one_apply]
    split_ifs <;> simp
  have hle1 : MeasurableSpace.comap w inferInstance ≤ mΩ' := hw.comap_le
  have : SigmaFinite (μ.trim hG) := inferInstance
  have e1 : ∀ i, μ[ind i | G] =ᵐ[μ] fun _ => (m : ℝ)⁻¹ := by
    intro i
    refine (condExp_indep_eq hle1 hG (hindm i) hind).trans (Eventually.of_forall fun _ => ?_)
    simp only [hind_def]
    rw [integral_indicator_one (hset i), measureReal_def, hunif i]
    simp
  have e2 : ∀ i, μ[ind i * g i | G] =ᵐ[μ] fun s => (m : ℝ)⁻¹ * g i s := by
    intro i
    filter_upwards [condExp_mul_of_stronglyMeasurable_right (hgm i) (hprodint i) (hindint i),
      e1 i] with s h1 h2
    rw [h1, Pi.mul_apply, h2]
  rw [hdecomp]
  have e3 := condExp_finsetSum (s := Finset.univ) (fun i _ => hprodint i) G (μ := μ)
  have e4 : ∀ᵐ s ∂μ, ∀ i, μ[ind i * g i | G] s = (m : ℝ)⁻¹ * g i s := by
    rw [ae_all_iff]; exact e2
  filter_upwards [e3, e4] with s h3 h4
  rw [h3, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => h4 i)


section Run

variable {μ : Measure Ω} {P : Problem n m} {A : Alg} {α : ℕ → ℝ} {ω : ℕ → Ω → Fin m}
  {x : ℕ → Ω → Vec n} {zc gFc gHc xc : ℕ → Fin m → Ω → Vec n} {x₀ : Vec n} {c : ℝ}

theorem step_ae (hP : P.Standing) (hα : ∀ k, 0 < α k)
    (hR : RandHyp μ P A α ω x zc gFc gHc xc x₀ c) {y : Vec n} (hy : y ∈ P.X) (k : ℕ) :
    ∀ᵐ s ∂μ, ∀ i, ‖xc k i s - y‖ ^ 2 ≤
      ‖x k s - y‖ ^ 2 - 2 * α k * (P.Fi i (x k s) - P.Fi i y) + 5 * α k ^ 2 * c ^ 2 := by
  have ha := (hα k).le
  have hb := hR.bound
  cases A with
  | a19 =>
    have hb' : Assumption3b μ P x zc gFc gHc c := hb
    filter_upwards [hb' k] with s hs i
    obtain ⟨_, b2, b3, b4⟩ := hs i
    exact step_a19 hP ha hy ((hR.run k s).1 i) b2 b3 b4
  | a20 =>
    have hb' : Assumption3b μ P x zc gFc gHc c := hb
    filter_upwards [hb' k] with s hs i
    obtain ⟨_, b2, b3, b4⟩ := hs i
    exact step_a20 hP ha hy ((hR.run k s).1 i) b2 b3 b4
  | a21 =>
    have hb' : Assumption4b μ P x gFc gHc xc c := hb
    filter_upwards [hb' k] with s hs i
    obtain ⟨b1, b2, b3⟩ := hs i
    exact step_a21 hP ha hy ((hR.run k s).1 i) b1 b2 b3

theorem hR_hist_le (hR : RandHyp μ P A α ω x zc gFc gHc xc x₀ c) :
    ∀ k, hist x (zOf ω zc) k ≤ mΩ :=
  hist_le hR.x_meas (fun k => (hR.omega k).1) (fun k i => (hR.step_meas k i).1)

theorem xc_meas (hR : RandHyp μ P A α ω x zc gFc gHc xc x₀ c) (k : ℕ) (i : Fin m) :
    Measurable (xc k i) :=
  (hR.step_meas k i).2.2.2.mono (hR_hist_le hR k) le_rfl

theorem xc_bdd_of (hP : P.Standing) (hα : ∀ k, 0 < α k)
    (hR : RandHyp μ P A α ω x zc gFc gHc xc x₀ c) (k : ℕ) (R : ℝ)
    (hx : ∀ᵐ s ∂μ, ‖x k s‖ ≤ R) : ∃ R', ∀ᵐ s ∂μ, ∀ i, ‖xc k i s‖ ≤ R' := by
  obtain ⟨y0, hy0⟩ := hP.X_nonempty
  obtain ⟨B, hB⟩ := Fi_lb hP R
  set T := ∑ i, |P.Fi i y0|
  set Q := (R + ‖y0‖) ^ 2 + 2 * α k * (T - B) + 5 * α k ^ 2 * c ^ 2
  refine ⟨‖y0‖ + Q + 1, ?_⟩
  filter_upwards [hx, step_ae hP hα hR hy0 k] with s hs hst i
  have h1 := hst i
  have h2 : ‖x k s - y0‖ ^ 2 ≤ (R + ‖y0‖) ^ 2 := by
    have := norm_sub_le (x k s) y0
    exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
  have h3 := hB i (x k s) hs
  have h4 : P.Fi i y0 ≤ T := le_trans (le_abs_self _)
    (Finset.single_le_sum (f := fun j => |P.Fi j y0|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i))
  have ha := (hα k).le
  have h5 : ‖xc k i s - y0‖ ^ 2 ≤ Q := by
    have := mul_le_mul_of_nonneg_left (show P.Fi i y0 - P.Fi i (x k s) ≤ T - B by linarith)
      (show (0:ℝ) ≤ 2 * α k by linarith)
    simp only [Q]; nlinarith
  have h6 : ‖xc k i s - y0‖ ≤ ‖xc k i s - y0‖ ^ 2 + 1 := by
    nlinarith [sq_nonneg (‖xc k i s - y0‖ - 1)]
  have h7 := norm_le_norm_add_norm_sub' (xc k i s) y0
  have h8 : ‖xc k i s‖ ≤ ‖y0‖ + ‖xc k i s - y0‖ := by
    have := norm_sub_norm_le (xc k i s) y0; linarith
  linarith

theorem x_bdd (hP : P.Standing) (hα : ∀ k, 0 < α k)
    (hR : RandHyp μ P A α ω x zc gFc gHc xc x₀ c) :
    ∀ k, ∃ R, ∀ᵐ s ∂μ, ‖x k s‖ ≤ R := by
  intro k
  induction k with
  | zero =>
    refine ⟨‖x₀‖, Eventually.of_forall fun s => ?_⟩
    rw [hR.start]
  | succ k ih =>
    obtain ⟨R, hR0⟩ := ih
    obtain ⟨R', hR'⟩ := xc_bdd_of hP hα hR k R hR0
    refine ⟨R', ?_⟩
    filter_upwards [hR'] with s hs
    rw [(hR.run k s).2]
    exact hs _

theorem xc_bdd (hP : P.Standing) (hα : ∀ k, 0 < α k)
    (hR : RandHyp μ P A α ω x zc gFc gHc xc x₀ c) (k : ℕ) :
    ∃ R', ∀ᵐ s ∂μ, ∀ i, ‖xc k i s‖ ≤ R' := by
  obtain ⟨R, hR0⟩ := x_bdd hP hα hR k
  exact xc_bdd_of hP hα hR k R hR0

theorem int_of_bdd [IsFiniteMeasure μ] {u : Ω → Vec n} (hu : Measurable u) {R : ℝ}
    (hb : ∀ᵐ s ∂μ, ‖u s‖ ≤ R) (y : Vec n) : Integrable (fun s => ‖u s - y‖ ^ 2) μ := by
  refine Integrable.of_bound ((hu.sub_const y).norm.pow_const 2).aestronglyMeasurable
    ((R + ‖y‖) ^ 2) ?_
  filter_upwards [hb] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have := norm_sub_le (u s) y
  exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2

theorem int_x [IsFiniteMeasure μ] (hP : P.Standing) (hα : ∀ k, 0 < α k)
    (hR : RandHyp μ P A α ω x zc gFc gHc xc x₀ c) (k : ℕ) (y : Vec n) :
    Integrable (fun s => ‖x k s - y‖ ^ 2) μ := by
  obtain ⟨R, hb⟩ := x_bdd hP hα hR k
  exact int_of_bdd (hR.x_meas k) hb y

theorem int_xc [IsFiniteMeasure μ] (hP : P.Standing) (hα : ∀ k, 0 < α k)
    (hR : RandHyp μ P A α ω x zc gFc gHc xc x₀ c) (k : ℕ) (i : Fin m) (y : Vec n) :
    Integrable (fun s => ‖xc k i s - y‖ ^ 2) μ := by
  obtain ⟨R, hb⟩ := xc_bdd hP hα hR k
  exact int_of_bdd (xc_meas hR k i) (hb.mono fun s hs => hs i) y

/-- Eq. (50) with `α` replaced by `α_k`: for every `y ∈ X`,
`E{‖x_{k+1} − y‖² | F_k} ≤ ‖x_k − y‖² − (2α_k/m)(F(x_k) − F(y)) + 5α_k²c²`. -/
theorem eq50 [IsProbabilityMeasure μ] [NeZero m] (hP : P.Standing) (hα : ∀ k, 0 < α k)
    (hR : RandHyp μ P A α ω x zc gFc gHc xc x₀ c) {y : Vec n} (hy : y ∈ P.X) (k : ℕ) :
    μ[fun s => ‖x (k + 1) s - y‖ ^ 2 | hist x (zOf ω zc) k] ≤ᵐ[μ]
      fun s => ‖x k s - y‖ ^ 2 - 2 * α k / m * (P.F (x k s) - P.F y) + 5 * α k ^ 2 * c ^ 2 := by
  have hle := hR_hist_le hR k
  have hfun : (fun s => ‖x (k + 1) s - y‖ ^ 2) =
      fun s => (fun i s => ‖xc k i s - y‖ ^ 2) (ω k s) s := by
    funext s; rw [(hR.run k s).2]
  rw [hfun]
  have hgm : ∀ i, StronglyMeasurable[hist x (zOf ω zc) k] (fun s => ‖xc k i s - y‖ ^ 2) :=
    fun i => by
      have hcont : Continuous (fun v : Vec n => ‖v - y‖ ^ 2) := by fun_prop
      exact (hcont.measurable.comp (hR.step_meas k i).2.2.2).stronglyMeasurable
  have hc := condexp_select μ hle (hR.omega k).1 (hR.omega k).2.1 (hR.omega k).2.2
    (fun i s => ‖xc k i s - y‖ ^ 2) hgm (fun i => int_xc hP hα hR k i y)
  filter_upwards [hc, step_ae hP hα hR hy k] with s h1 h2
  rw [h1]
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h2 i)
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
    ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.card_univ, Fintype.card_fin] at hsum
  have hF : ∑ i, P.Fi i (x k s) = P.F (x k s) := rfl
  have hFy : ∑ i, P.Fi i y = P.F y := rfl
  rw [hF, hFy, nsmul_eq_mul, nsmul_eq_mul] at hsum
  have : (m : ℝ)⁻¹ * ∑ i, ‖xc k i s - y‖ ^ 2 ≤ (m : ℝ)⁻¹ * (↑m * ‖x k s - y‖ ^ 2 -
      2 * α k * (P.F (x k s) - P.F y) + ↑m * (5 * α k ^ 2 * c ^ 2)) :=
    mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hm.le)
  refine le_trans this (le_of_eq ?_)
  field_simp

end Run

end IncProx2Inf

open IncProx2Inf in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} [NeZero m]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Problem n m) (hP : P.Standing) (A : Alg)
    (α : ℕ → ℝ) (hαpos : ∀ k, 0 < α k) (ω : ℕ → Ω → Fin m) (x : ℕ → Ω → Vec n)
    (zc gFc gHc xc : ℕ → Fin m → Ω → Vec n) (x₀ : Vec n) (c : ℝ)
    (hR : RandHyp μ P A α ω x zc gFc gHc xc x₀ c)
    (xs : Vec n) (hxs : xs ∈ P.Xstar) (k : ℕ) :
    μ[fun s => ‖x (k + 1) s - xs‖ ^ 2 | hist x (zOf ω zc) k] ≤ᵐ[μ]
      fun s => ‖x k s - xs‖ ^ 2 - 2 * α k / m * (P.F (x k s) - P.F xs) + 5 * α k ^ 2 * c ^ 2 :=
  eq50 hP hαpos hR hxs.1 k
