-- Prove2me | solution 1 for NumStochOpt.Bounds.eq_2_55_2_56_simple_recourse_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T03:42:23.008588+00:00
-- url     : https://prove2.me/submissions/2c9ebe98-e7be-4fa2-942a-5d62be2a651b

import Definitions.Def_NumStochOpt_Bounds_EdmundsonMadansky
import Definitions.Def_NumStochOpt_Bounds_RecourseCost
import Definitions.Def_NumStochOpt_Bounds_SimpleRecourse
import Mathlib


set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory
open scoped BigOperators
open Classical
namespace NumStochOpt.Bounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma em_prob_sum (a b x : ℝ) (hab : a < b) :
    (∑ s : Bool, emProb a b x s) = 1 := by
  simp only [Fintype.sum_bool, emProb, Bool.false_eq_true, if_false, if_true]
  field_simp [sub_ne_zero.mpr hab.ne']
  ring

lemma em_prob_nonneg {a b x : ℝ} (hab : a < b) (hx : x ∈ Set.Icc a b) (s : Bool) :
    0 ≤ emProb a b x s := by
  cases s <;> simp only [emProb, Bool.false_eq_true, if_false, if_true]
  · exact div_nonneg (sub_nonneg.mpr hx.2) (sub_pos.mpr hab).le
  · exact div_nonneg (sub_nonneg.mpr hx.1) (sub_pos.mpr hab).le

lemma em_prob_mean (a b x : ℝ) (hab : a < b) :
    (∑ s : Bool, emProb a b x s * (if s then b else a)) = x := by
  simp only [Fintype.sum_bool, emProb, Bool.false_eq_true, if_false, if_true]
  field_simp [sub_ne_zero.mpr hab.ne']
  ring

lemma em_weight_sum (a b x : ι → ℝ) (hab : ∀ j, a j < b j) :
    (∑ v : ι → Bool, emVertexWeight a b x v) = 1 := by
  unfold emVertexWeight
  rw [← Fintype.prod_sum]
  simp only [em_prob_sum _ _ _ (hab _), Finset.prod_const_one]

lemma em_weight_eval (p : ι → Bool → ℝ) (hp : ∀ j, ∑ s : Bool, p j s = 1)
    (q : Bool → ℝ) (j : ι) :
    (∑ v : ι → Bool, (∏ k, p k (v k)) * q (v j)) = ∑ s : Bool, p j s * q s := by
  have hprod (v : ι → Bool) :
      (∏ k, p k (v k)) * q (v j) =
        ∏ k, if k = j then p k (v k) * q (v k) else p k (v k) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun k => p k (v k)) (Finset.mem_univ j),
      ← Finset.mul_prod_erase Finset.univ
        (fun k => if k = j then p k (v k) * q (v k) else p k (v k)) (Finset.mem_univ j)]
    have he : (∏ k ∈ Finset.univ.erase j,
        if k = j then p k (v k) * q (v k) else p k (v k)) =
        ∏ k ∈ Finset.univ.erase j, p k (v k) := by
      apply Finset.prod_congr rfl
      intro k hk
      simp [Finset.ne_of_mem_erase hk]
    rw [he]
    simp only [ite_true]
    ring
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun k (s : Bool) => if k = j then p k s * q s else p k s)]
  have hs : (fun k => ∑ s : Bool, if k = j then p k s * q s else p k s) =
      (fun k => if k = j then ∑ s : Bool, p k s * q s else 1) := by
    funext k
    by_cases hk : k = j
    · simp [hk]
    · simp only [if_neg hk]
      exact hp k
  rw [hs]
  simp

lemma em_weight_barycenter (a b x : ι → ℝ) (hab : ∀ j, a j < b j) :
    (∑ v : ι → Bool, emVertexWeight a b x v • boxVertex a b v) = x := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, boxVertex, emVertexWeight]
  rw [em_weight_eval (fun k s => emProb (a k) (b k) (x k) s)
    (fun k => em_prob_sum (a k) (b k) (x k) (hab k)) (fun s : Bool => if s then b j else a j) j]
  exact em_prob_mean (a j) (b j) (x j) (hab j)

lemma em_vertex_mem (a b : ι → ℝ) (hab : ∀ j, a j < b j) (v : ι → Bool) :
    boxVertex a b v ∈ Set.pi Set.univ (fun j => Set.Icc (a j) (b j)) := by
  intro j _
  cases hv : v j <;> simp [boxVertex, hv, (hab j).le]

lemma em_pointwise (a b : ι → ℝ) (hab : ∀ j, a j < b j)
    (φ : (ι → ℝ) → ℝ)
    (hφ : ConvexOn ℝ (Set.pi Set.univ fun j => Set.Icc (a j) (b j)) φ)
    (x : ι → ℝ) (hx : ∀ j, x j ∈ Set.Icc (a j) (b j)) :
    φ x ≤ emUpperBound a b x φ := by
  have key := hφ.map_sum_le (t := Finset.univ)
    (w := emVertexWeight a b x) (p := boxVertex a b)
    (fun v _ => Finset.prod_nonneg fun j _ => em_prob_nonneg (hab j) (hx j) (v j))
    (em_weight_sum a b x hab) (fun v _ => em_vertex_mem a b hab v)
  rw [em_weight_barycenter a b x hab] at key
  simpa only [smul_eq_mul, emUpperBound] using key

lemma em_upper_le_abs (a b x : ι → ℝ) (hab : ∀ j, a j < b j)
    (hx : ∀ j, x j ∈ Set.Icc (a j) (b j)) (φ : (ι → ℝ) → ℝ) :
    emUpperBound a b x φ ≤ ∑ v : ι → Bool, |φ (boxVertex a b v)| := by
  apply Finset.sum_le_sum
  intro v _
  have h0 : 0 ≤ emVertexWeight a b x v :=
    Finset.prod_nonneg fun j _ => em_prob_nonneg (hab j) (hx j) (v j)
  have h1 : emVertexWeight a b x v ≤ 1 := by
    rw [← em_weight_sum a b x hab]
    exact Finset.single_le_sum
      (fun u _ => Finset.prod_nonneg fun j _ => em_prob_nonneg (hab j) (hx j) (u j))
      (Finset.mem_univ v)
  calc
    emVertexWeight a b x v * φ (boxVertex a b v) ≤
        emVertexWeight a b x v * |φ (boxVertex a b v)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) h0
    _ ≤ |φ (boxVertex a b v)| := by
      simpa using mul_le_mul_of_nonneg_right h1 (abs_nonneg (φ (boxVertex a b v)))

lemma em_abs_bound (a b : ι → ℝ) (hab : ∀ j, a j < b j)
    (φ : (ι → ℝ) → ℝ)
    (hφ : ConvexOn ℝ (Set.pi Set.univ fun j => Set.Icc (a j) (b j)) φ)
    (x : ι → ℝ) (hx : ∀ j, x j ∈ Set.Icc (a j) (b j)) :
    |φ x| ≤ 2 * |φ (fun j => (a j + b j) / 2)| +
      2 * ∑ v : ι → Bool, |φ (boxVertex a b v)| := by
  let y : ι → ℝ := fun j => a j + b j - x j
  have hy : ∀ j, y j ∈ Set.Icc (a j) (b j) := by
    intro j; constructor <;> dsimp [y] <;> linarith [(hx j).1, (hx j).2]
  have hu := (em_pointwise a b hab φ hφ x hx).trans (em_upper_le_abs a b x hab hx φ)
  have hv := (em_pointwise a b hab φ hφ y hy).trans (em_upper_le_abs a b y hab hy φ)
  have hh := hφ.2 (fun j _ => hx j) (fun j _ => hy j)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)
  have hc : (1/2 : ℝ) • x + (1/2 : ℝ) • y = (fun j => (a j + b j) / 2) := by
    funext j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, y]; ring
  rw [hc] at hh
  simp only [smul_eq_mul] at hh
  rw [abs_le]
  have hs : 0 ≤ ∑ v : ι → Bool, |φ (boxVertex a b v)| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  constructor <;> nlinarith [neg_abs_le (φ (fun j => (a j + b j) / 2)),
    abs_nonneg (φ (fun j => (a j + b j) / 2))]

end NumStochOpt.Bounds


set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory
open scoped BigOperators
open Classical
namespace NumStochOpt.Bounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def emFace (a b : ι → ℝ) (v : ι → Option Bool) : Set (ι → ℝ) :=
  Set.pi Set.univ fun j => match v j with
    | none => Set.Ioo (a j) (b j)
    | some false => {a j}
    | some true => {b j}

def emFill (a b : ι → ℝ) (v : ι → Option Bool)
    (u : {j // v j = none} → ℝ) : ι → ℝ := fun j =>
  if h : v j = none then u ⟨j, h⟩ else if v j = some true then b j else a j

lemma em_fill_mem (a b : ι → ℝ) (hab : ∀ j, a j < b j) (v : ι → Option Bool)
    (u : {j // v j = none} → ℝ)
    (hu : u ∈ Set.pi Set.univ fun j : {j // v j = none} => Set.Icc (a j) (b j)) :
    emFill a b v u ∈ Set.pi Set.univ (fun j => Set.Icc (a j) (b j)) := by
  intro j _
  by_cases hj : v j = none
  · simpa [emFill, hj] using hu ⟨j, hj⟩ (Set.mem_univ _)
  · by_cases ht : v j = some true <;> simp [emFill, hj, ht, (hab j).le]

lemma em_fill_combo (a b : ι → ℝ) (v : ι → Option Bool)
    (u w : {j // v j = none} → ℝ) (r s : ℝ) (hrs : r + s = 1) :
    emFill a b v (r • u + s • w) = r • emFill a b v u + s • emFill a b v w := by
  funext j
  by_cases hj : v j = none
  · simp [emFill, hj]
  · by_cases ht : v j = some true <;>
      simp [emFill, hj, ht, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> rw [← add_mul, hrs, one_mul]

lemma em_face_measurable (a b : ι → ℝ) (v : ι → Option Bool) :
    MeasurableSet (emFace a b v) := by
  refine (measurableSet_pi Set.countable_univ).mpr (Or.inl ?_)
  intro j _
  cases hv : v j with
  | none => exact measurableSet_Ioo
  | some s => cases s <;> exact measurableSet_singleton _

lemma em_face_extension (a b : ι → ℝ) (hab : ∀ j, a j < b j)
    (φ : (ι → ℝ) → ℝ)
    (hφ : ConvexOn ℝ (Set.pi Set.univ fun j => Set.Icc (a j) (b j)) φ)
    (v : ι → Option Bool) :
    ∃ g : (ι → ℝ) → ℝ, Measurable g ∧ Set.EqOn g φ (emFace a b v) := by
  let D : Set ({j // v j = none} → ℝ) :=
    Set.pi Set.univ fun j => Set.Icc (a j) (b j)
  let U : Set ({j // v j = none} → ℝ) :=
    Set.pi Set.univ fun j => Set.Ioo (a j) (b j)
  let F : ({j // v j = none} → ℝ) → ℝ := fun u => φ (emFill a b v u)
  have hF : ConvexOn ℝ D F := by
    refine ⟨convex_pi (fun _ _ => convex_Icc _ _), ?_⟩
    intro u hu w hw r s hr hs hrs
    dsimp [F]
    rw [em_fill_combo a b v u w r s hrs]
    exact hφ.2 (em_fill_mem a b hab v u hu) (em_fill_mem a b hab v w hw) hr hs hrs
  have hDU : interior D = U := by
    dsimp [D, U]
    rw [interior_pi_set Set.finite_univ]
    simp only [interior_Icc]
  have hc : ContinuousOn F U := hDU ▸ hF.continuousOn_interior
  have hmU : MeasurableSet U :=
    (measurableSet_pi Set.countable_univ).mpr (Or.inl (fun _ _ => measurableSet_Ioo))
  let G : ({j // v j = none} → ℝ) → ℝ := U.piecewise F (fun _ => 0)
  have hG : Measurable G := hc.measurable_piecewise continuousOn_const hmU
  let proj : (ι → ℝ) → {j // v j = none} → ℝ := fun x j => x j
  have hp : Measurable proj := measurable_pi_lambda _ (fun j => measurable_pi_apply j.val)
  refine ⟨G ∘ proj, hG.comp hp, ?_⟩
  intro x hx
  have hpx : proj x ∈ U := by
    intro j _
    have hj := hx j (Set.mem_univ _)
    simpa only [emFace, j.property] using hj
  have hfill : emFill a b v (proj x) = x := by
    funext j
    have hj := hx j (Set.mem_univ _)
    cases hv : v j with
    | none => simp [emFill, hv, proj]
    | some s =>
      cases s <;> simp only [emFace, hv, Set.mem_singleton_iff] at hj <;>
        simp [emFill, hv, hj]
  simp [Function.comp_def, G, Set.piecewise, hpx, F, hfill]

/-- Every finite convex function on a finite box has a measurable extension from that box.
The proof includes all boundary faces and requires no continuity at their endpoints. -/
lemma em_box_measurable_extension (a b : ι → ℝ) (hab : ∀ j, a j < b j)
    (φ : (ι → ℝ) → ℝ)
    (hφ : ConvexOn ℝ (Set.pi Set.univ fun j => Set.Icc (a j) (b j)) φ) :
    ∃ g : (ι → ℝ) → ℝ, Measurable g ∧
      Set.EqOn g φ (Set.pi Set.univ fun j => Set.Icc (a j) (b j)) := by
  choose G hG hEq using em_face_extension a b hab φ hφ
  obtain ⟨g, hg, hge⟩ := exists_measurable_piecewise (emFace a b)
    (em_face_measurable a b) G hG (by
      intro v w _ x hx
      exact (hEq v hx.1).trans (hEq w hx.2).symm)
  refine ⟨g, hg, ?_⟩
  intro x hx
  have hcoord : ∀ j : ι, ∃ s : Option Bool,
      x j ∈ (match s with
        | none => Set.Ioo (a j) (b j)
        | some false => {a j}
        | some true => {b j}) := by
    intro j
    have hj := hx j (Set.mem_univ _)
    by_cases ha : x j = a j
    · exact ⟨some false, ha⟩
    · by_cases hb : x j = b j
      · exact ⟨some true, hb⟩
      · exact ⟨none, lt_of_le_of_ne hj.1 (Ne.symm ha), lt_of_le_of_ne hj.2 hb⟩
  choose v hv using hcoord
  have hface : x ∈ emFace a b v := fun j _ => hv j
  exact (hge v hface).trans (hEq v hface)

end NumStochOpt.Bounds


set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory
open scoped BigOperators
open Classical
namespace NumStochOpt.Bounds

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

lemma em_coordinate_integrable (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → ι → ℝ) (hmeas : ∀ j, AEMeasurable (fun ω => ξ ω j) P)
    (a b : ι → ℝ) (hsupp : ∀ᵐ ω ∂P, ∀ j, ξ ω j ∈ Set.Icc (a j) (b j)) (j : ι) :
    Integrable (fun ω => ξ ω j) P := by
  refine Integrable.of_bound (hmeas j).aestronglyMeasurable (|a j| + |b j|) ?_
  filter_upwards [hsupp] with ω hω
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [(hω j).1, (hω j).2, neg_abs_le (a j),
    le_abs_self (b j), abs_nonneg (a j), abs_nonneg (b j)]

lemma em_prob_integral (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX : Integrable X P) (a b : ℝ) (s : Bool) :
    (∫ ω, emProb a b (X ω) s ∂P) = emProb a b (∫ ω, X ω ∂P) s := by
  cases s <;> simp only [emProb, Bool.false_eq_true, if_false, if_true]
  · rw [integral_div, integral_sub (integrable_const _) hX, integral_const]
    simp
  · rw [integral_div, integral_sub hX (integrable_const _), integral_const]
    simp

lemma em_native_independent_bound (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → ι → ℝ) (hmeas : ∀ j, AEMeasurable (fun ω => ξ ω j) P)
    (hind : ProbabilityTheory.iIndepFun (fun j ω => ξ ω j) P)
    (a b : ι → ℝ) (hab : ∀ j, a j < b j)
    (hsupp : ∀ᵐ ω ∂P, ∀ j, ξ ω j ∈ Set.Icc (a j) (b j))
    (φ : (ι → ℝ) → ℝ)
    (hφ : ConvexOn ℝ (Set.pi Set.univ fun j => Set.Icc (a j) (b j)) φ) :
    ∫ ω, φ (ξ ω) ∂P ≤ emUpperBound a b (fun j => ∫ ω, ξ ω j ∂P) φ := by
  obtain ⟨g, hg, heq⟩ := em_box_measurable_extension a b hab φ hφ
  have hξ : AEMeasurable ξ P := by
    exact aemeasurable_pi_lambda _ hmeas
  have hφm : AEStronglyMeasurable (fun ω => φ (ξ ω)) P := by
    refine (hg.comp_aemeasurable hξ).aestronglyMeasurable.congr ?_
    filter_upwards [hsupp] with ω hω
    exact heq (fun j _ => hω j)
  have hφi : Integrable (fun ω => φ (ξ ω)) P := by
    refine Integrable.of_bound hφm
      (2 * |φ (fun j => (a j + b j) / 2)| +
        2 * ∑ v : ι → Bool, |φ (boxVertex a b v)|) ?_
    filter_upwards [hsupp] with ω hω
    rw [Real.norm_eq_abs]
    exact em_abs_bound a b hab φ hφ (ξ ω) hω
  have hpm (j : ι) (s : Bool) : Measurable (fun x : ℝ => emProb (a j) (b j) x s) := by
    cases s <;> simp only [emProb, Bool.false_eq_true, if_false, if_true] <;> fun_prop
  have hwi (v : ι → Bool) : Integrable (fun ω => emVertexWeight a b (ξ ω) v) P := by
    refine Integrable.of_bound ?_ 1 ?_
    · exact Finset.aestronglyMeasurable_fun_prod Finset.univ
        (fun j _ => ((hpm j (v j)).comp_aemeasurable (hmeas j)).aestronglyMeasurable)
    · filter_upwards [hsupp] with ω hω
      have h0 : 0 ≤ emVertexWeight a b (ξ ω) v :=
        Finset.prod_nonneg fun j _ => em_prob_nonneg (hab j) (hω j) (v j)
      have h1 : emVertexWeight a b (ξ ω) v ≤ 1 := by
        rw [← em_weight_sum a b (ξ ω) hab]
        exact Finset.single_le_sum
          (fun u _ => Finset.prod_nonneg fun j _ => em_prob_nonneg (hab j) (hω j) (u j))
          (Finset.mem_univ v)
      simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using h1
  have hui : Integrable (fun ω => emUpperBound a b (ξ ω) φ) P :=
    integrable_finsetSum Finset.univ (fun v _ => (hwi v).mul_const _)
  have hle := integral_mono_ae hφi hui (by
    filter_upwards [hsupp] with ω hω
    exact em_pointwise a b hab φ hφ (ξ ω) hω)
  have hwei (v : ι → Bool) :
      (∫ ω, emVertexWeight a b (ξ ω) v ∂P) =
        emVertexWeight a b (fun j => ∫ ω, ξ ω j ∂P) v := by
    unfold emVertexWeight
    rw [hind.integral_fun_prod_comp hmeas
      (fun j => (hpm j (v j)).aestronglyMeasurable)]
    apply Finset.prod_congr rfl
    intro j _
    exact em_prob_integral P (fun ω => ξ ω j)
      (em_coordinate_integrable P ξ hmeas a b hsupp j) (a j) (b j) (v j)
  have hue : (∫ ω, emUpperBound a b (ξ ω) φ ∂P) =
      emUpperBound a b (fun j => ∫ ω, ξ ω j ∂P) φ := by
    unfold emUpperBound
    rw [integral_finsetSum _ (fun v _ => (hwi v).mul_const _)]
    apply Finset.sum_congr rfl
    intro v _
    rw [integral_mul_const, hwei]
  rwa [hue] at hle

end NumStochOpt.Bounds



set_option autoImplicit false

namespace NumStochOpt.Bounds.P2c67119f

open Matrix

lemma W_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι ⊕ ι → ℝ) (j : ι) :
    (simpleRecourseMatrix ι *ᵥ y) j = y (Sum.inl j) - y (Sum.inr j) := by
  simp [simpleRecourseMatrix, Matrix.fromCols_mulVec, Matrix.neg_mulVec, sub_eq_add_neg]

lemma q_dot {ι : Type*} [Fintype ι] (qp qm : ι → ℝ) (y : ι ⊕ ι → ℝ) :
    Sum.elim qp qm ⬝ᵥ y = ∑ j, (qp j * y (Sum.inl j) + qm j * y (Sum.inr j)) := by
  simp [dotProduct, Fintype.sum_sum_type, Finset.sum_add_distrib]

lemma one_row (qp qm χ h a b : ℝ) (hq : 0 ≤ qp + qm) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a - b = h - χ) : simpleRecourseCost qp qm χ h ≤ qp * a + qm * b := by
  unfold simpleRecourseCost
  split_ifs with hc
  · have : a = (h - χ) + b := by linarith
    subst this
    nlinarith [mul_nonneg hq hb]
  · have : b = a - (h - χ) := by linarith
    subst this
    nlinarith [mul_nonneg hq ha]

lemma one_row_eq (qp qm χ h : ℝ) :
    simpleRecourseCost qp qm χ h = qp * max (h - χ) 0 + qm * max (-(h - χ)) 0 := by
  unfold simpleRecourseCost
  split_ifs with hc
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring

end NumStochOpt.Bounds.P2c67119f

open Matrix in
theorem NumStochOpt.Bounds.em_reused_separable {ι ν : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ν] (qp qm : ι → ℝ) (hq : ∀ j, 0 ≤ qp j + qm j) (T : Matrix ι ν ℝ) (h : ι → ℝ)
    (x : ν → ℝ) :
    NumStochOpt.Bounds.recourseCost (NumStochOpt.Bounds.simpleRecourseMatrix ι) (Sum.elim qp qm) h T x =
      ((∑ j, NumStochOpt.Bounds.simpleRecourseCost (qp j) (qm j) ((T *ᵥ x) j) (h j) : ℝ) : EReal) := by
  open NumStochOpt.Bounds NumStochOpt.Bounds.P2c67119f in
  unfold recourseCost
  apply le_antisymm
  · let y : ι ⊕ ι → ℝ := Sum.elim (fun j => max (h j - (T *ᵥ x) j) 0)
      (fun j => max (-(h j - (T *ᵥ x) j)) 0)
    have hy : y ∈ {y : ι ⊕ ι → ℝ | 0 ≤ y ∧ simpleRecourseMatrix ι *ᵥ y = h - T *ᵥ x} := by
      refine ⟨?_, ?_⟩
      · intro k
        cases k with
        | inl j => simp [y]
        | inr j => simp [y]
      · funext j
        rw [W_mulVec]
        simp only [y, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply]
        rcases le_total 0 (h j - (T *ᵥ x) j) with hc | hc
        · rw [max_eq_left hc, max_eq_right (by linarith)]; ring
        · rw [max_eq_right hc, max_eq_left (by linarith)]; ring
    refine (iInf₂_le y hy).trans (le_of_eq ?_)
    congr 1
    rw [q_dot]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [one_row_eq]
    rfl
  · refine le_iInf₂ fun y hy => ?_
    obtain ⟨hy0, hyW⟩ := hy
    rw [EReal.coe_le_coe_iff, q_dot]
    refine Finset.sum_le_sum fun j _ => ?_
    have hj := congrFun hyW j
    rw [W_mulVec] at hj
    exact one_row _ _ _ _ _ _ (hq j) (hy0 _) (hy0 _) (by simpa using hj)



set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Matrix
open scoped BigOperators
open Classical
namespace NumStochOpt.Bounds

lemma em_simple_max (qp qm χ h : ℝ) (hq : 0 ≤ qp + qm) :
    simpleRecourseCost qp qm χ h = max (qp * (h - χ)) (qm * (χ - h)) := by
  unfold simpleRecourseCost
  split_ifs with hc
  · rw [max_eq_left]
    nlinarith [mul_nonneg hq (sub_nonneg.mpr hc)]
  · rw [max_eq_right]
    nlinarith [mul_nonneg hq (sub_nonneg.mpr (not_le.mp hc).le)]

lemma em_simple_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : Ω → ℝ) (hH : Integrable H P)
    (qp qm χ : ℝ) (hq : 0 ≤ qp + qm) :
    Integrable (fun ω => simpleRecourseCost qp qm χ (H ω)) P := by
  simp_rw [em_simple_max qp qm χ _ hq]
  exact ((hH.sub (integrable_const χ)).const_mul qp).sup
    (((integrable_const χ).sub hH).const_mul qm)

lemma em_simple_jensen {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : Ω → ℝ) (hH : Integrable H P)
    (qp qm χ : ℝ) (hq : 0 ≤ qp + qm) :
    simpleRecourseCost qp qm χ (∫ ω, H ω ∂P) ≤
      ∫ ω, simpleRecourseCost qp qm χ (H ω) ∂P := by
  rw [em_simple_max qp qm χ _ hq]
  have hi := em_simple_integrable P H hH qp qm χ hq
  have hl := integral_mono_ae ((hH.sub (integrable_const χ)).const_mul qp) hi
    (Filter.Eventually.of_forall (fun ω => by
      change qp * (H ω - χ) ≤ simpleRecourseCost qp qm χ (H ω)
      rw [em_simple_max qp qm χ _ hq]; exact le_max_left _ _))
  have hr := integral_mono_ae (((integrable_const χ).sub hH).const_mul qm) hi
    (Filter.Eventually.of_forall (fun ω => by
      change qm * (χ - H ω) ≤ simpleRecourseCost qp qm χ (H ω)
      rw [em_simple_max qp qm χ _ hq]; exact le_max_right _ _))
  change (∫ ω, qp * (H ω - χ) ∂P) ≤ _ at hl
  change (∫ ω, qm * (χ - H ω) ∂P) ≤ _ at hr
  rw [integral_const_mul, integral_sub hH (integrable_const χ), integral_const] at hl
  rw [integral_const_mul, integral_sub (integrable_const χ) hH, integral_const] at hr
  simp only [probReal_univ, one_smul] at hl hr
  exact max_le hl hr

lemma em_simple_expected {Ω ι ν : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] [Fintype ν]
    (P : Measure Ω) [IsProbabilityMeasure P] (qp qm : ι → ℝ)
    (hq : ∀ j, 0 ≤ qp j + qm j) (h : Ω → ι → ℝ)
    (hh : ∀ j, Integrable (fun ω => h ω j) P) (T : Matrix ι ν ℝ) (x : ν → ℝ) :
    expectedRecourse P (simpleRecourseMatrix ι) (fun _ => Sum.elim qp qm) h
      (fun _ => T) x = ∑ j, ∫ ω, simpleRecourseCost (qp j) (qm j) ((T *ᵥ x) j) (h ω j) ∂P := by
  unfold expectedRecourse
  simp_rw [em_reused_separable qp qm hq T, EReal.toReal_coe]
  exact integral_finsetSum _ (fun j _ => em_simple_integrable P _ (hh j) _ _ _ (hq j))

end NumStochOpt.Bounds


set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Matrix
open scoped BigOperators
open Classical
namespace NumStochOpt.Bounds

lemma em_native_sandwich {Ω ι ρ ν : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] [Fintype ρ] [Fintype ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Matrix ρ ν ℝ) (bvec : ρ → ℝ) (c : ν → ℝ) (T : Matrix ι ν ℝ)
    (qp qm : ι → ℝ) (hq : ∀ j, 0 ≤ qp j + qm j)
    (h : Ω → ι → ℝ) (hmeas : ∀ j, Measurable fun ω => h ω j)
    (a b : ι → ℝ) (hab : ∀ j, a j ≤ b j) (hsupp : ∀ᵐ ω ∂P, ∀ j, h ω j ∈ Set.Icc (a j) (b j))
    (xt : ν → ℝ) (ypt ymt : ι → ℝ)
    (hfeas : A *ᵥ xt = bvec ∧ T *ᵥ xt + ypt - ymt = (fun j => ∫ ω, h ω j ∂P) ∧
      0 ≤ xt ∧ 0 ≤ ypt ∧ 0 ≤ ymt)
    (hopt : ∀ (x : ν → ℝ) (yp ym : ι → ℝ), A *ᵥ x = bvec →
      T *ᵥ x + yp - ym = (fun j => ∫ ω, h ω j ∂P) → 0 ≤ x → 0 ≤ yp → 0 ≤ ym →
      c ⬝ᵥ xt + qp ⬝ᵥ ypt + qm ⬝ᵥ ymt ≤ c ⬝ᵥ x + qp ⬝ᵥ yp + qm ⬝ᵥ ym) :
    (∀ j, simpleRecourseCost (qp j) (qm j) ((T *ᵥ xt) j) (∫ ω, h ω j ∂P) ≤
        ∫ ω, simpleRecourseCost (qp j) (qm j) ((T *ᵥ xt) j) (h ω j) ∂P) ∧
      c ⬝ᵥ xt + ∑ j, simpleRecourseCost (qp j) (qm j) ((T *ᵥ xt) j) (∫ ω, h ω j ∂P) ≤
        sInf ((fun x => c ⬝ᵥ x + expectedRecourse P (simpleRecourseMatrix ι)
            (fun _ => Sum.elim qp qm) h (fun _ => T) x) '' {x | A *ᵥ x = bvec ∧ 0 ≤ x}) ∧
      sInf ((fun x => c ⬝ᵥ x + expectedRecourse P (simpleRecourseMatrix ι)
            (fun _ => Sum.elim qp qm) h (fun _ => T) x) '' {x | A *ᵥ x = bvec ∧ 0 ≤ x}) ≤
        c ⬝ᵥ xt + ∑ j, ∫ ω, simpleRecourseCost (qp j) (qm j) ((T *ᵥ xt) j) (h ω j) ∂P := by
  have hh (j : ι) : Integrable (fun ω => h ω j) P :=
    em_coordinate_integrable P h (fun j => (hmeas j).aemeasurable) a b hsupp j
  have hjensen (x : ν → ℝ) (j : ι) := em_simple_jensen P _ (hh j) (qp j) (qm j) ((T *ᵥ x) j) (hq j)
  let B : ℝ := c ⬝ᵥ xt + ∑ j, simpleRecourseCost (qp j) (qm j) ((T *ᵥ xt) j) (∫ ω, h ω j ∂P)
  let F : (ν → ℝ) → ℝ := fun x => c ⬝ᵥ x + expectedRecourse P (simpleRecourseMatrix ι)
    (fun _ => Sum.elim qp qm) h (fun _ => T) x
  let X : Set (ν → ℝ) := {x | A *ᵥ x = bvec ∧ 0 ≤ x}
  have hxt : xt ∈ X := ⟨hfeas.1, hfeas.2.2.1⟩
  have hb (x : ν → ℝ) (hx : x ∈ X) : B ≤ F x := by
    let yp : ι → ℝ := fun j => max ((∫ ω, h ω j ∂P) - (T *ᵥ x) j) 0
    let ym : ι → ℝ := fun j => max (-((∫ ω, h ω j ∂P) - (T *ᵥ x) j)) 0
    have hyp : 0 ≤ yp := fun j => le_max_right _ _
    have hym : 0 ≤ ym := fun j => le_max_right _ _
    have hy : T *ᵥ x + yp - ym = (fun j => ∫ ω, h ω j ∂P) := by
      funext j
      dsimp [yp, ym]
      rcases le_total 0 ((∫ ω, h ω j ∂P) - (T *ᵥ x) j) with hd | hd
      · rw [max_eq_left hd, max_eq_right (by linarith)]
        ring
      · rw [max_eq_right hd, max_eq_left (by linarith)]
        ring
    have ho := hopt x yp ym hx.1 hy hx.2 hyp hym
    have ht : B ≤ c ⬝ᵥ xt + qp ⬝ᵥ ypt + qm ⬝ᵥ ymt := by
      dsimp [B]
      simp only [dotProduct]
      rw [add_assoc, ← Finset.sum_add_distrib]
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro j _
      have he := congrFun hfeas.2.1 j
      exact P2c67119f.one_row _ _ _ _ _ _ (hq j) (hfeas.2.2.2.1 j)
        (hfeas.2.2.2.2 j) (by
          change (T *ᵥ xt) j + ypt j - ymt j = _ at he
          linarith)
    have hcost : qp ⬝ᵥ yp + qm ⬝ᵥ ym =
        ∑ j, simpleRecourseCost (qp j) (qm j) ((T *ᵥ x) j) (∫ ω, h ω j ∂P) := by
      rw [dotProduct, dotProduct, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      exact (P2c67119f.one_row_eq _ _ _ _).symm
    calc
      B ≤ c ⬝ᵥ xt + qp ⬝ᵥ ypt + qm ⬝ᵥ ymt := ht
      _ ≤ c ⬝ᵥ x + qp ⬝ᵥ yp + qm ⬝ᵥ ym := ho
      _ = c ⬝ᵥ x + ∑ j, simpleRecourseCost (qp j) (qm j) ((T *ᵥ x) j) (∫ ω, h ω j ∂P) := by
        rw [add_assoc, hcost]
      _ ≤ F x := by
        dsimp [F]
        rw [em_simple_expected P qp qm hq h hh T x]
        exact add_le_add_right (Finset.sum_le_sum (fun j _ => hjensen x j)) _
  refine ⟨hjensen xt, ?_, ?_⟩
  · exact le_csInf (Set.Nonempty.image _ ⟨xt, hxt⟩) (by
      rintro y ⟨x, hx, rfl⟩
      exact hb x hx)
  · have hbelow : BddBelow (F '' X) := ⟨B, by rintro y ⟨x, hx, rfl⟩; exact hb x hx⟩
    have hi := csInf_le hbelow (Set.mem_image_of_mem F hxt)
    simpa only [F, em_simple_expected P qp qm hq h hh T xt] using hi

end NumStochOpt.Bounds


open MeasureTheory Matrix NumStochOpt.Bounds in

/-- Eqs. (2.55)–(2.56), p. 55: simple recourse `W = [I, −I]`, deterministic `q = [q⁺, q⁻]` with
`q⁺_j + q⁻_j ≥ 0` and `T`, random right-hand side `h(ω)` in the box `×_j [a_j, b_j]`. If
`(x̃, ỹ⁺, ỹ⁻)` solves the one-block problem (2.53) with `h¹ = E h(ω)` and `χ̃ = T x̃`, then
`Q_j(χ̃_j, h¹_j) ≤ E Q_j(χ̃_j, h_j(ω))` for every `j`, and
`cᵀx̃ + Σ_j Q_j(χ̃_j, h¹_j) ≤ min_{Ax=b, x≥0} [cᵀx + E Q(Tx, h(ω))] ≤ cᵀx̃ + Σ_j E Q_j(χ̃_j, h_j(ω))`. -/
theorem solution {Ω ι ρ ν : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] [Fintype ρ] [Fintype ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Matrix ρ ν ℝ) (bvec : ρ → ℝ) (c : ν → ℝ) (T : Matrix ι ν ℝ)
    (qp qm : ι → ℝ) (hq : ∀ j, 0 ≤ qp j + qm j)
    (h : Ω → ι → ℝ) (hmeas : ∀ j, Measurable fun ω => h ω j)
    (a b : ι → ℝ) (hab : ∀ j, a j ≤ b j) (hsupp : ∀ᵐ ω ∂P, ∀ j, h ω j ∈ Set.Icc (a j) (b j))
    (xt : ν → ℝ) (ypt ymt : ι → ℝ)
    (hfeas : A *ᵥ xt = bvec ∧ T *ᵥ xt + ypt - ymt = (fun j => ∫ ω, h ω j ∂P) ∧
      0 ≤ xt ∧ 0 ≤ ypt ∧ 0 ≤ ymt)
    (hopt : ∀ (x : ν → ℝ) (yp ym : ι → ℝ), A *ᵥ x = bvec →
      T *ᵥ x + yp - ym = (fun j => ∫ ω, h ω j ∂P) → 0 ≤ x → 0 ≤ yp → 0 ≤ ym →
      c ⬝ᵥ xt + qp ⬝ᵥ ypt + qm ⬝ᵥ ymt ≤ c ⬝ᵥ x + qp ⬝ᵥ yp + qm ⬝ᵥ ym) :
    (∀ j, simpleRecourseCost (qp j) (qm j) ((T *ᵥ xt) j) (∫ ω, h ω j ∂P) ≤
        ∫ ω, simpleRecourseCost (qp j) (qm j) ((T *ᵥ xt) j) (h ω j) ∂P) ∧
      c ⬝ᵥ xt + ∑ j, simpleRecourseCost (qp j) (qm j) ((T *ᵥ xt) j) (∫ ω, h ω j ∂P) ≤
        sInf ((fun x => c ⬝ᵥ x + expectedRecourse P (simpleRecourseMatrix ι)
            (fun _ => Sum.elim qp qm) h (fun _ => T) x) '' {x | A *ᵥ x = bvec ∧ 0 ≤ x}) ∧
      sInf ((fun x => c ⬝ᵥ x + expectedRecourse P (simpleRecourseMatrix ι)
            (fun _ => Sum.elim qp qm) h (fun _ => T) x) '' {x | A *ᵥ x = bvec ∧ 0 ≤ x}) ≤
        c ⬝ᵥ xt + ∑ j, ∫ ω, simpleRecourseCost (qp j) (qm j) ((T *ᵥ xt) j) (h ω j) ∂P := by
  exact em_native_sandwich P A bvec c T qp qm hq h hmeas a b hab hsupp xt ypt ymt hfeas hopt


#print axioms solution
