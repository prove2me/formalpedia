-- Prove2me | solution 1 for IncProx.Randomized.proposition9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T00:08:30.867101+00:00
-- url     : https://prove2.me/submissions/62815346-1992-4dc6-a183-d606b98b2e30

import Mathlib
import Definitions.Def_IncProx_Randomized_Basic
import Theorems.Thm_IncProx_Randomized_proposition2
import Theorems.Thm_IncProx_Randomized_eq59

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

namespace IncProx2Inf

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {n m : ℕ}

lemma F_ge_of_mem {P : Problem n m} {v xs : Vec n} (hv : v ∈ P.X) (hxs : xs ∈ P.Xstar) :
    P.F xs ≤ P.F v := by
  have h1 : P.Fstar ≤ ((P.F v : ℝ) : EReal) := iInf₂_le v hv
  rw [← hxs.2] at h1
  exact_mod_cast h1

/-- Filtration `t ↦ F_{j+t}`. -/
def histFj (x z : ℕ → Ω → Vec n) (hle : ∀ k, hist x z k ≤ mΩ) (j : ℕ) : Filtration ℕ mΩ where
  seq t := hist x z (j + t)
  mono' a b h := hist_mono x z (by omega)
  le' t := hle (j + t)

section Run

variable {μ : Measure Ω} {P : Problem n m} {A : Alg} {α : ℕ → ℝ} {ω : ℕ → Ω → Fin m}
  {x : ℕ → Ω → Vec n} {zc gFc gHc xc : ℕ → Fin m → Ω → Vec n} {x₀ : Vec n} {c : ℝ}

theorem x_mem (hR : RandHyp μ P A α ω x zc gFc gHc xc x₀ c) (k : ℕ) (s : Ω) :
    x (k + 1) s ∈ P.X := by
  rw [(hR.run k s).2]; exact step_mem ((hR.run k s).1 _)

/-- The stopped-process argument of Prop. 7 / Prop. 9 (first part), started at time `j`. -/
theorem enter_after [IsProbabilityMeasure μ] [NeZero m] (hP : P.Standing)
    (hα : ∀ k, 0 < α k) (hR : RandHyp μ P A α ω x zc gFc gHc xc x₀ c)
    (hαsum : Tendsto (fun N => ∑ k ∈ Finset.range N, α k) atTop atTop)
    {y : Vec n} (hy : y ∈ P.X) {ε : ℝ} (hε : 0 < ε) (j : ℕ)
    (hsmall : ∀ k, j ≤ k → 5 * α k * c ^ 2 * m ≤ ε) :
    ∀ᵐ s ∂μ, ∃ k, j ≤ k ∧ P.F (x k s) < P.F y + ε := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  set z := zOf ω zc
  have hle := hR_hist_le hR
  set 𝓕 := histFj x z hle j with h𝓕
  set Gd : ℕ → Set Ω := fun t => {s | ∀ l ∈ Finset.range (t + 1), P.F y + ε ≤ P.F (x (j + l) s)}
    with hGd
  set I : ℕ → Ω → ℝ := fun t s => if s ∈ Gd t then 1 else 0 with hI
  set Y : ℕ → Ω → ℝ := fun t s => I t s * ‖x (j + t) s - y‖ ^ 2 with hY
  set Z : ℕ → Ω → ℝ := fun t s => I t s * (2 * α (j + t) / m * (P.F (x (j + t) s) - P.F y) -
    5 * α (j + t) ^ 2 * c ^ 2) with hZ
  set W : ℕ → Ω → ℝ := fun _ _ => 0 with hW
  have hI01 : ∀ t s, 0 ≤ I t s ∧ I t s ≤ 1 := by
    intro t s; simp only [hI]; split_ifs <;> norm_num
  have hxm : ∀ l t, l ≤ t → Measurable[𝓕 t] (x (j + l)) := fun l t hlt =>
    (x_meas_hist x z (j + l)).mono (hist_mono x z (by omega)) le_rfl
  have hGdm : ∀ t, MeasurableSet[𝓕 t] (Gd t) := by
    intro t
    have : Gd t = ⋂ l ∈ Finset.range (t + 1), {s | P.F y + ε ≤ P.F (x (j + l) s)} := by
      ext s; simp [hGd]
    rw [this]
    refine Finset.measurableSet_biInter _ (fun l hl => ?_)
    exact measurableSet_le measurable_const
      ((F_cont hP).measurable.comp (hxm l t (by simp at hl; omega)))
  have hIm : ∀ t, Measurable[𝓕 t] (I t) := fun t =>
    Measurable.ite (hGdm t) measurable_const measurable_const
  have hYad : Adapted 𝓕 Y := by
    intro t
    have hcont : Continuous (fun v : Vec n => ‖v - y‖ ^ 2) := by fun_prop
    exact (hIm t).mul (hcont.measurable.comp (hxm t t le_rfl))
  have hZad : Adapted 𝓕 Z := by
    intro t
    have hcont : Continuous (fun v : Vec n => 2 * α (j + t) / m * (P.F v - P.F y) -
        5 * α (j + t) ^ 2 * c ^ 2) :=
      (continuous_const.mul ((F_cont hP).sub continuous_const)).sub continuous_const
    exact (hIm t).mul (hcont.measurable.comp (hxm t t le_rfl))
  have hWad : Adapted 𝓕 W := fun t => measurable_const
  have hY0 : ∀ t s, 0 ≤ Y t s := fun t s => mul_nonneg (hI01 t s).1 (sq_nonneg _)
  -- progress lower bound when not yet stopped
  have hprog : ∀ t s, s ∈ Gd t → α (j + t) * ε / m ≤
      2 * α (j + t) / m * (P.F (x (j + t) s) - P.F y) - 5 * α (j + t) ^ 2 * c ^ 2 := by
    intro t s hs
    have h1 : P.F y + ε ≤ P.F (x (j + t) s) := hs t (by simp)
    have h2 := hsmall (j + t) (by omega)
    have ha := hα (j + t)
    have e1 : 2 * α (j + t) / m * (P.F (x (j + t) s) - P.F y) ≥ 2 * α (j + t) / m * ε :=
      mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (by linarith) hm.le)
    have e2 : 5 * α (j + t) ^ 2 * c ^ 2 ≤ α (j + t) * ε / m := by
      rw [le_div_iff₀ hm]; nlinarith
    have e3 : 2 * α (j + t) / m * ε = 2 * (α (j + t) * ε / m) := by ring
    linarith
  have hZ0 : ∀ t s, 0 ≤ Z t s := by
    intro t s
    simp only [hZ, hI]
    split_ifs with hs
    · have := hprog t s hs
      have : 0 ≤ α (j + t) * ε / m := div_nonneg (mul_nonneg (hα _).le hε.le) hm.le
      linarith
    · simp
  have hW0 : ∀ t s, 0 ≤ W t s := fun _ _ => le_rfl
  have hint : ∀ k, Integrable (fun s => ‖x k s - y‖ ^ 2) μ := fun k => int_x hP hα hR k y
  have hYint : ∀ t, Integrable (Y t) μ := by
    intro t
    refine Integrable.mono' (hint (j + t)) ((hIm t).mono (𝓕.le t) le_rfl |>.aestronglyMeasurable.mul
      (hint (j + t)).aestronglyMeasurable) (Eventually.of_forall fun s => ?_)
    simp only [hY, Real.norm_eq_abs]
    rw [abs_of_nonneg (hY0 t s)]
    have := hI01 t s
    nlinarith [sq_nonneg ‖x (j + t) s - y‖]
  have h2 : ∀ t, μ[Y (t + 1) | 𝓕 t] ≤ᵐ[μ] fun s => Y t s - Z t s + W t s := by
    intro t
    set g : Ω → ℝ := fun s => ‖x (j + t + 1) s - y‖ ^ 2 with hg
    have hIg : Integrable (I t * g) μ := by
      refine Integrable.mono' (hint (j + t + 1)) ((hIm t).mono (𝓕.le t) le_rfl
        |>.aestronglyMeasurable.mul (hint (j + t + 1)).aestronglyMeasurable)
        (Eventually.of_forall fun s => ?_)
      simp only [Pi.mul_apply, hg, Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg (hI01 t s).1 (sq_nonneg _))]
      have := hI01 t s
      nlinarith [sq_nonneg ‖x (j + t + 1) s - y‖]
    have hle1 : Y (t + 1) ≤ᵐ[μ] I t * g := by
      refine Eventually.of_forall fun s => ?_
      simp only [hY, Pi.mul_apply, hg, hI]
      rw [show j + (t + 1) = j + t + 1 by omega]
      have hsub : s ∈ Gd (t + 1) → s ∈ Gd t := fun hs l hl => hs l (by simp at hl ⊢; omega)
      by_cases h1 : s ∈ Gd (t + 1)
      · rw [if_pos h1, if_pos (hsub h1)]
      · rw [if_neg h1, zero_mul]
        exact mul_nonneg (by split_ifs <;> norm_num) (sq_nonneg _)
    have e1 := condExp_mono (m := 𝓕 t) (hYint (t + 1)) hIg hle1
    have e2 : μ[I t * g | 𝓕 t] =ᵐ[μ] I t * μ[g | 𝓕 t] :=
      condExp_mul_of_stronglyMeasurable_left (hIm t).stronglyMeasurable hIg (hint (j + t + 1))
    have e3 : μ[g | 𝓕 t] ≤ᵐ[μ] fun s => ‖x (j + t) s - y‖ ^ 2 -
        2 * α (j + t) / m * (P.F (x (j + t) s) - P.F y) + 5 * α (j + t) ^ 2 * c ^ 2 :=
      eq50 hP hα hR hy (j + t)
    filter_upwards [e1, e2, e3] with s h1 h2 h3
    refine le_trans h1 ?_
    rw [h2, Pi.mul_apply]
    have := mul_le_mul_of_nonneg_left h3 (hI01 t s).1
    simp only [hY, hZ, hW]
    linarith
  have h3 : ∀ᵐ s ∂μ, Summable fun t => W t s :=
    Eventually.of_forall fun s => by simp [hW]
  obtain ⟨hZs, -⟩ := IncProx.Randomized.proposition2 μ 𝓕 Y Z W hYad hZad hWad
    hY0 hZ0 hW0 hYint h2 h3
  filter_upwards [hZs] with s hs
  by_contra hcon
  push Not at hcon
  have hall : ∀ t, s ∈ Gd t := fun t l _ => hcon (j + l) (by omega)
  have hsumα : Summable fun t => α (j + t) * ε / m := by
    refine Summable.of_nonneg_of_le (fun t => div_nonneg (mul_nonneg (hα _).le hε.le) hm.le)
      (fun t => ?_) hs
    simp only [hZ, hI, if_pos (hall t), one_mul]
    exact hprog t s (hall t)
  have hsα : Summable fun t => α (t + j) := by
    have := hsumα.mul_left (m / ε)
    refine this.congr (fun t => ?_)
    rw [add_comm t j]; field_simp
  have hsα' : Summable α := (summable_nat_add_iff j).1 hsα
  exact not_tendsto_atTop_of_tendsto_nhds hsα'.hasSum.tendsto_sum_nat hαsum

theorem freq_lt [IsProbabilityMeasure μ] [NeZero m] (hP : P.Standing)
    (hα : ∀ k, 0 < α k) (hR : RandHyp μ P A α ω x zc gFc gHc xc x₀ c)
    (hα0 : Tendsto α atTop (𝓝 0))
    (hαsum : Tendsto (fun N => ∑ k ∈ Finset.range N, α k) atTop atTop)
    {y : Vec n} (hy : y ∈ P.X) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ s ∂μ, ∃ᶠ k in atTop, P.F (x k s) < P.F y + ε := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set K : ℝ := 5 * c ^ 2 * m + 1
  have hK : 0 < K := by positivity
  have hev : ∀ᶠ k in atTop, α k < ε / K := hα0 (gt_mem_nhds (div_pos hε hK))
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 hev
  have hsmall : ∀ k, k0 ≤ k → 5 * α k * c ^ 2 * m ≤ ε := by
    intro k hk
    have h1 := hk0 k hk
    have h2 := (hα k).le
    rw [lt_div_iff₀ hK] at h1
    have : 0 ≤ 5 * c ^ 2 * m := by positivity
    nlinarith
  have hall : ∀ᵐ s ∂μ, ∀ j : ℕ, ∃ k, max j k0 ≤ k ∧ P.F (x k s) < P.F y + ε := by
    rw [ae_all_iff]
    intro j
    exact enter_after hP hα hR hαsum hy hε (max j k0)
      (fun k hk => hsmall k (le_trans (le_max_right _ _) hk))
  filter_upwards [hall] with s hs
  rw [frequently_atTop]
  intro j
  obtain ⟨k, hk, hlt⟩ := hs j
  exact ⟨k, le_trans (le_max_left _ _) hk, hlt⟩

theorem part1 [IsProbabilityMeasure μ] [NeZero m] (hP : P.Standing)
    (hα : ∀ k, 0 < α k) (hR : RandHyp μ P A α ω x zc gFc gHc xc x₀ c)
    (hα0 : Tendsto α atTop (𝓝 0))
    (hαsum : Tendsto (fun N => ∑ k ∈ Finset.range N, α k) atTop atTop) :
    ∀ᵐ s ∂μ, liminf (fun k => ((P.F (x k s) : ℝ) : EReal)) atTop = P.Fstar := by
  have hq : ∀ q : ℚ, ∀ᵐ s ∂μ, P.Fstar < ((q : ℝ) : EReal) →
      liminf (fun k => ((P.F (x k s) : ℝ) : EReal)) atTop ≤ ((q : ℝ) : EReal) := by
    intro q
    by_cases hlt : P.Fstar < ((q : ℝ) : EReal)
    · obtain ⟨v, hv, hvq⟩ : ∃ v ∈ P.X, ((P.F v : ℝ) : EReal) < ((q : ℝ) : EReal) := by
        unfold Problem.Fstar at hlt
        rw [iInf_lt_iff] at hlt
        obtain ⟨v, hv⟩ := hlt
        rw [iInf_lt_iff] at hv
        obtain ⟨hvX, hv⟩ := hv
        exact ⟨v, hvX, hv⟩
      have hvq' : P.F v < q := EReal.coe_lt_coe_iff.1 hvq
      filter_upwards [freq_lt hP hα hR hα0 hαsum hv (sub_pos.2 hvq')] with s hs _
      refine liminf_le_of_frequently_le' (hs.mono fun k hk => ?_)
      have : P.F (x k s) ≤ q := by linarith
      exact_mod_cast this
    · exact Eventually.of_forall fun s h => absurd h hlt
  rw [← ae_all_iff] at hq
  filter_upwards [hq] with s hs
  apply le_antisymm
  · by_contra hcon
    push Not at hcon
    obtain ⟨q, h1, h2⟩ := EReal.lt_iff_exists_rat_btwn.1 hcon
    exact absurd (hs q h1) (not_le.2 h2)
  · refine le_liminf_of_le (h := ?_)
    rw [eventually_atTop]
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact iInf₂_le _ (x_mem hR k' s)

end Run

end IncProx2Inf

namespace IncProx2Inf

variable {n m : ℕ}

theorem part2_det {P : Problem n m} (hP : P.Standing) {u : ℕ → Vec n} {D : Set (Vec n)}
    (hDX : D ⊆ P.Xstar) (hcl : P.Xstar ⊆ closure D) {d0 : Vec n} (hd0 : d0 ∈ D)
    (hmem : ∀ k, u (k + 1) ∈ P.X)
    (hconv : ∀ d ∈ D, ∃ L, Tendsto (fun k => ‖u k - d‖) atTop (𝓝 L))
    (hlim : liminf (fun k => ((P.F (u k) : ℝ) : EReal)) atTop = P.Fstar) :
    ∃ xs ∈ P.Xstar, Tendsto u atTop (𝓝 xs) := by
  have hd0X := hDX hd0
  have hFs : P.Fstar = ((P.F d0 : ℝ) : EReal) := hd0X.2.symm
  obtain ⟨L0, hL0⟩ := hconv d0 hd0
  obtain ⟨B, hB⟩ := hL0.bddAbove_range
  have hball : ∀ k, u k ∈ Metric.closedBall d0 B := fun k => by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hB ⟨k, rfl⟩
  have hfreq : ∀ N : ℕ, ∃ᶠ k in atTop, P.F (u k) < P.F d0 + 1 / ((N : ℝ) + 1) := by
    intro N
    have hpos : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    have hlt : liminf (fun k => ((P.F (u k) : ℝ) : EReal)) atTop <
        ((P.F d0 + 1 / ((N : ℝ) + 1) : ℝ) : EReal) := by
      rw [hlim, hFs, EReal.coe_lt_coe_iff]; linarith
    exact (frequently_lt_of_liminf_lt (h := hlt)).mono fun k hk => EReal.coe_lt_coe_iff.1 hk
  obtain ⟨φ, hφ, hφP⟩ := extraction_forall_of_frequently hfreq
  obtain ⟨xb, -, ψ, hψ, hlimsub⟩ :=
    tendsto_subseq_of_bounded Metric.isBounded_closedBall (fun n => hball (φ n))
  have hsub_mono : StrictMono (φ ∘ ψ) := hφ.comp hψ
  have hxbX : xb ∈ P.X := by
    refine hP.X_closed.mem_of_tendsto hlimsub (eventually_atTop.2 ⟨1, fun k hk => ?_⟩)
    have h1 : 1 ≤ (φ ∘ ψ) k := le_trans hk (hsub_mono.id_le k)
    obtain ⟨k', hk'⟩ : ∃ k', (φ ∘ ψ) k = k' + 1 := ⟨(φ ∘ ψ) k - 1, by omega⟩
    show u ((φ ∘ ψ) k) ∈ P.X
    rw [hk']; exact hmem k'
  have hFle : P.F xb ≤ P.F d0 := by
    have h1 : Tendsto (fun k => P.F ((u ∘ φ ∘ ψ) k)) atTop (𝓝 (P.F xb)) :=
      ((F_cont hP).tendsto xb).comp hlimsub
    have h2 : Tendsto (fun k : ℕ => P.F d0 + 1 / ((k : ℝ) + 1)) atTop (𝓝 (P.F d0)) := by
      simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    refine le_of_tendsto_of_tendsto' h1 h2 (fun k => ?_)
    have h3 := hφP (ψ k)
    have hk : (k : ℝ) ≤ ψ k := by exact_mod_cast hψ.id_le k
    have h4 : 1 / ((ψ k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    simp only [Function.comp_apply]
    linarith
  have hxbS : xb ∈ P.Xstar := by
    refine ⟨hxbX, ?_⟩
    have := F_ge_of_mem hxbX hd0X
    rw [hFs]
    congr 1
    linarith
  refine ⟨xb, hxbS, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨d, hdD, hdist⟩ := Metric.mem_closure_iff.1 (hcl hxbS) (ε / 3) (by linarith)
  obtain ⟨Ld, hLd⟩ := hconv d hdD
  have hsubL : Tendsto (fun k => ‖(u ∘ φ ∘ ψ) k - d‖) atTop (𝓝 Ld) :=
    hLd.comp hsub_mono.tendsto_atTop
  have hsubL2 : Tendsto (fun k => ‖(u ∘ φ ∘ ψ) k - d‖) atTop (𝓝 ‖xb - d‖) :=
    (hlimsub.sub_const d).norm
  have hLeq : Ld = ‖xb - d‖ := tendsto_nhds_unique hsubL hsubL2
  have hLlt : Ld < 2 * ε / 3 := by
    rw [hLeq, ← dist_eq_norm]; linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hLd.eventually (gt_mem_nhds hLlt))
  refine ⟨N, fun k hk => ?_⟩
  have h1 := hN k hk
  rw [dist_eq_norm]
  have h2 := norm_sub_le_norm_sub_add_norm_sub (u k) d xb
  have h3 : ‖d - xb‖ < ε / 3 := by rw [← dist_eq_norm, dist_comm]; exact hdist
  linarith

end IncProx2Inf

open IncProx2Inf in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} [NeZero m]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Problem n m) (hP : P.Standing) (A : Alg)
    (α : ℕ → ℝ) (hαpos : ∀ k, 0 < α k) (ω : ℕ → Ω → Fin m) (x : ℕ → Ω → Vec n)
    (zc gFc gHc xc : ℕ → Fin m → Ω → Vec n) (x₀ : Vec n) (c : ℝ)
    (hR : RandHyp μ P A α ω x zc gFc gHc xc x₀ c)
    (hα0 : Tendsto α atTop (𝓝 0))
    (hαsum : Tendsto (fun N => ∑ k ∈ Finset.range N, α k) atTop atTop) :
    (∀ᵐ s ∂μ, liminf (fun k => ((P.F (x k s) : ℝ) : EReal)) atTop = P.Fstar) ∧
      (P.Xstar.Nonempty → Summable (fun k => α k ^ 2) →
        ∀ᵐ s ∂μ, ∃ xs ∈ P.Xstar, Tendsto (fun k => x k s) atTop (𝓝 xs)) := by
  refine ⟨part1 hP hαpos hR hα0 hαsum, fun hne hα2 => ?_⟩
  obtain ⟨D, hDX, hDc, hcl⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace P.Xstar).exists_countable_dense_subset
  obtain ⟨xs0, hxs0⟩ := hne
  obtain ⟨d0, hd0⟩ : D.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have := hcl hxs0
    rw [h, closure_empty] at this
    exact this
  have hall : ∀ᵐ s ∂μ, ∀ d ∈ D, Summable (fun k => 2 * α k / m * (P.F (x k s) - P.F d)) ∧
      ∃ L : ℝ, Tendsto (fun k => ‖x k s - d‖) atTop (𝓝 L) :=
    (ae_ball_iff hDc).2 (fun d hd => IncProx.Randomized.eq59 μ P hP A α hαpos ω x zc gFc gHc xc
      x₀ c hR hα2 d (hDX hd))
  filter_upwards [hall, part1 hP hαpos hR hα0 hαsum] with s hs hl
  exact part2_det hP hDX hcl hd0 (fun k => x_mem hR k s) (fun d hd => (hs d hd).2) hl
