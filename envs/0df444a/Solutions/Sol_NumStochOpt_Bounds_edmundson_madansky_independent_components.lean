-- Prove2me | solution 1 for NumStochOpt.Bounds.edmundson_madansky_independent_components
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T03:31:35.252439+00:00
-- url     : https://prove2.me/submissions/a7855a9d-6edc-4c34-8b9b-0f90e069eb8c

import Mathlib
import Definitions.Def_NumStochOpt_Bounds_EdmundsonMadansky

open MeasureTheory


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


open MeasureTheory NumStochOpt.Bounds in

/-- The Edmundson–Madansky bound for independent components, p. 46 (with (2.32)–(2.33)). Let
`ξ = (ξ_j)_{j ∈ ι}` have independent components, `ξ_j ∈ [a_j, b_j]` almost surely with
`a_j < b_j`, and means `ξ⁰_j = E ξ_j`. If `φ` is convex on the box `Ξ = ×_j [a_j, b_j]`, then
`E φ(ξ) ≤ Σ_v (∏_j p_j(v_j)) φ(v)`, the sum over the vertices `v` of `Ξ`, where `p_j(a_j) =
(b_j − ξ⁰_j)/(b_j − a_j)` and `p_j(b_j) = (ξ⁰_j − a_j)/(b_j − a_j)`. -/
theorem solution {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] (P : Measure Ω) [IsProbabilityMeasure P] (ξ : Ω → ι → ℝ)
    (hmeas : ∀ j, AEMeasurable (fun ω => ξ ω j) P)
    (hind : ProbabilityTheory.iIndepFun (fun j ω => ξ ω j) P)
    (a b : ι → ℝ) (hab : ∀ j, a j < b j)
    (hsupp : ∀ᵐ ω ∂P, ∀ j, ξ ω j ∈ Set.Icc (a j) (b j))
    (φ : (ι → ℝ) → ℝ) (hφ : ConvexOn ℝ (Set.pi Set.univ fun j => Set.Icc (a j) (b j)) φ) :
    ∫ ω, φ (ξ ω) ∂P ≤ emUpperBound a b (fun j => ∫ ω, ξ ω j ∂P) φ := by
  exact em_native_independent_bound P ξ hmeas hind a b hab hsupp φ hφ


#print axioms solution
