-- Prove2me | solution 1 for OAI.BoxTransport.Routing.balanced_box_routing
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T13:53:46.925977+00:00
-- url     : https://prove2.me/submissions/0b270566-fb08-4fc0-ba62-fbffb8be32f2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BoxTransport/Routing.lean:L172-L182
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.BoxTransport.Routing.balanced_box_routing.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_BoxTransport_Routing_balanced_box_routing) verbatim and is proved by it.
import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow
import Definitions.Def_OAI_Analysis_BoxTransport_Motion
import Definitions.Def_OAI_Analysis_BoxTransport_Computation
import Definitions.Def_OAI_Analysis_BoxTransport_Expressions
import Definitions.Def_OAI_Analysis_BoxTransport_Routing
import Theorems.Thm_OAI_BoxTransport_Routing_Computation_effective_of_expressions
import Theorems.Thm_OAI_BoxTransport_Routing_balancedScale_le
import Theorems.Thm_OAI_BoxTransport_Routing_coordinateRank_strict
import Theorems.Thm_OAI_BoxTransport_Routing_exists_rational_padding
import Theorems.Thm_OAI_BoxTransport_Routing_realBox_disjoint_iff
import Theorems.Thm_OAI_BoxTransport_Routing_stationaryMotionField_realizes

-- ---- from OAI.Analysis.BoxTransport.Geometry ----
namespace OAI

/-! Quantitative box separation, affine images and positive diagonal shape estimates. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

namespace BoxTransport.Routing
theorem realBox_disjoint_of_gap {c d h k : Space}
    (hgap : ∃ j, h j + k j < |c j - d j|) :
    Disjoint (realBox c h) (realBox d k) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨j, hj⟩ := hgap
  have hle : |c j - d j| ≤ h j + k j := calc
    |c j - d j| = |(c j - x j) + (x j - d j)| := by congr 1; ring
    _ ≤ |c j - x j| + |x j - d j| := abs_add_le _ _
    _ = |x j - c j| + |x j - d j| := by rw [abs_sub_comm (c j) (x j)]
    _ ≤ h j + k j := add_le_add (hx j) (hy j)
  exact (not_lt_of_ge hle) hj

theorem padded_boxes_disjoint_of_clearance {c d h k : Space} {R η : ℝ}
    (hR : 0 < R) (hη : η < R / 8)
    (hh : ∀ j, h j ≤ R) (hk : ∀ j, k j ≤ R)
    (hclear : ∃ j, 4 * R ≤ |c j - d j|) :
    Disjoint (realBox c (fun j => h j + 2 * η))
      (realBox d (fun j => k j + 2 * η)) := by
  obtain ⟨j, hj⟩ := hclear
  apply realBox_disjoint_of_gap
  refine ⟨j, ?_⟩
  have := hh j
  have := hk j
  linarith

end BoxTransport.Routing

end

end OAI

-- ---- from OAI.Analysis.BoxTransport.Motion ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Separated five-stage motions and explicit affine time-one delivery. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

namespace BoxTransport.Routing
theorem centerKey_injective {n : ℕ} (f : Fin n → ℚ) : Function.Injective (centerKey f) := by
  intro i j hij
  have hp := toLex.injective hij
  exact Fin.ext (congrArg Prod.snd hp)

theorem centerKey_coordinate_le {n : ℕ} {f : Fin n → ℚ} {i j : Fin n}
    (hij : centerKey f i < centerKey f j) : f i ≤ f j :=
  Prod.Lex.monotone_fst _ _ hij.le

theorem spreadCenter_gap {n : ℕ} (a : Fin n → RationalSpace) {D θ : ℝ}
    (hD : 0 ≤ D) (hθ : 0 ≤ θ) (i j : Fin n) (k : Fin 3) :
    |(a i k : ℝ) - (a j k : ℝ)| ≤ |spreadCenter a D θ i k - spreadCenter a D θ j k| := by
  by_cases hk : k = 0
  · subst k
    wlog hij : centerKey (fun q => a q 0) i ≤ centerKey (fun q => a q 0) j generalizing i j
    · simpa only [abs_sub_comm] using this j i (le_of_not_ge hij)
    rcases hij.eq_or_lt with he | hij
    · have heij := centerKey_injective (fun q => a q 0) he
      subst j
      simp
    have hr : coordinateRank (fun q => a q 0) i ≤ coordinateRank (fun q => a q 0) j :=
      (coordinateRank_strict hij).le
    have hc : (a i 0 : ℝ) ≤ (a j 0 : ℝ) := by exact_mod_cast centerKey_coordinate_le hij
    have hr' : (coordinateRank (fun q => a q 0) i : ℝ) ≤
        (coordinateRank (fun q => a q 0) j : ℝ) := by exact_mod_cast hr
    have hm := mul_le_mul_of_nonneg_left hr' (mul_nonneg hθ hD)
    simp only [spreadCenter, ite_true]
    rw [abs_of_nonpos (sub_nonpos.mpr hc), abs_of_nonpos (by linarith)]
    linarith
  · simp only [spreadCenter, ite_eq_right hk]
    exact le_rfl

theorem spreadCenter_separated {n : ℕ} (a : Fin n → RationalSpace) {D : ℝ}
    (hD : 0 ≤ D) {i j : Fin n} (hij : i ≠ j) :
    D ≤ |spreadCenter a D 1 i 0 - spreadCenter a D 1 j 0| := by
  wlog hkey : centerKey (fun q => a q 0) i < centerKey (fun q => a q 0) j generalizing i j
  · have hne : centerKey (fun q => a q 0) i ≠ centerKey (fun q => a q 0) j :=
      (centerKey_injective (fun q => a q 0)).ne hij
    simpa only [abs_sub_comm] using this hij.symm (lt_of_le_of_ne (le_of_not_gt hkey) hne.symm)
  have hr : coordinateRank (fun q => a q 0) i + 1 ≤ coordinateRank (fun q => a q 0) j :=
    coordinateRank_strict hkey
  have hr' : (coordinateRank (fun q => a q 0) i : ℝ) + 1 ≤
      (coordinateRank (fun q => a q 0) j : ℝ) := by exact_mod_cast hr
  have hc : (a i 0 : ℝ) ≤ (a j 0 : ℝ) := by exact_mod_cast centerKey_coordinate_le hkey
  simp only [spreadCenter, ite_true, one_mul]
  have ha := neg_le_abs ((a i 0 : ℝ) + D * coordinateRank (fun q => a q 0) i -
    ((a j 0 : ℝ) + D * coordinateRank (fun q => a q 0) j))
  nlinarith

theorem spreadCenter_disjoint {n : ℕ} (a : Fin n → RationalSpace) (r : Fin n → Space)
    {D θ : ℝ} (hD : 0 ≤ D) (hθ : 0 ≤ θ) (hr : ∀ i k, 0 ≤ r i k)
    (hsep : Pairwise fun i j => Disjoint (realBox (realPoint (a i)) (r i))
      (realBox (realPoint (a j)) (r j))) :
    Pairwise fun i j => Disjoint (realBox (spreadCenter a D θ i) (r i))
      (realBox (spreadCenter a D θ j) (r j)) := by
  intro i j hij
  obtain ⟨k, hk⟩ := (realBox_disjoint_iff (hr i) (hr j)).mp (hsep hij)
  apply realBox_disjoint_of_gap
  exact ⟨k, hk.trans_le (spreadCenter_gap a hD hθ i j k)⟩

theorem stageSwitch_zero {j : Fin 5} {t : ℝ} (h : 10 * t - 5 / 2 ≤ (j : ℝ)) :
    stageSwitch j t = 0 :=
  Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr h)

theorem stageSwitch_one {j : Fin 5} {t : ℝ} (h : (j : ℝ) + 1 ≤ 10 * t - 5 / 2) :
    stageSwitch j t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem stageSwitch_before (j : Fin 5) {t : ℝ} (h : t ≤ 1 / 4) : stageSwitch j t = 0 := by
  apply stageSwitch_zero
  have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
  linarith

theorem stageSwitch_after (j : Fin 5) {t : ℝ} (h : 3 / 4 ≤ t) : stageSwitch j t = 1 := by
  apply stageSwitch_one
  have hj : (j : ℝ) ≤ 4 := by exact_mod_cast Nat.le_of_lt_succ j.isLt
  linarith

theorem stageSwitch_cases (t : ℝ) :
    (stageSwitch 1 t = 0 ∧ stageSwitch 2 t = 0 ∧ stageSwitch 3 t = 0 ∧ stageSwitch 4 t = 0) ∨
    (stageSwitch 0 t = 1 ∧ stageSwitch 2 t = 0 ∧ stageSwitch 3 t = 0 ∧ stageSwitch 4 t = 0) ∨
    (stageSwitch 0 t = 1 ∧ stageSwitch 1 t = 1 ∧ stageSwitch 3 t = 0 ∧ stageSwitch 4 t = 0) ∨
    (stageSwitch 0 t = 1 ∧ stageSwitch 1 t = 1 ∧ stageSwitch 2 t = 1 ∧ stageSwitch 4 t = 0) ∨
    (stageSwitch 0 t = 1 ∧ stageSwitch 1 t = 1 ∧ stageSwitch 2 t = 1 ∧ stageSwitch 3 t = 1) := by
  by_cases h₁ : 10 * t - 5 / 2 ≤ 1
  · exact Or.inl ⟨stageSwitch_zero (by simpa using h₁), stageSwitch_zero (by norm_num; linarith),
      stageSwitch_zero (by norm_num; linarith), stageSwitch_zero (by norm_num; linarith)⟩
  right
  by_cases h₂ : 10 * t - 5 / 2 ≤ 2
  · exact Or.inl ⟨stageSwitch_one (by norm_num; linarith), stageSwitch_zero (by simpa using h₂),
      stageSwitch_zero (by norm_num; linarith), stageSwitch_zero (by norm_num; linarith)⟩
  right
  by_cases h₃ : 10 * t - 5 / 2 ≤ 3
  · exact Or.inl ⟨stageSwitch_one (by norm_num; linarith), stageSwitch_one (by norm_num; linarith),
      stageSwitch_zero (by simpa using h₃), stageSwitch_zero (by norm_num; linarith)⟩
  right
  by_cases h₄ : 10 * t - 5 / 2 ≤ 4
  · exact Or.inl ⟨stageSwitch_one (by norm_num; linarith), stageSwitch_one (by norm_num; linarith),
      stageSwitch_one (by norm_num; linarith), stageSwitch_zero (by simpa using h₄)⟩
  right
  exact ⟨stageSwitch_one (by norm_num; linarith), stageSwitch_one (by norm_num; linarith),
    stageSwitch_one (by norm_num; linarith), stageSwitch_one (by norm_num; linarith)⟩

theorem contDiff_routeCenters {n : ℕ} (a b : Fin n → RationalSpace) (D : ℝ) (i : Fin n) :
    ContDiff ℝ ∞ (routeCenters a b D i) := by
  have hs := contDiff_stageSwitch
  apply contDiff_pi.mpr
  intro j
  fin_cases j <;> dsimp [routeCenters, routeCenterParameters] <;> fun_prop

theorem routeCenter_stage₀ {n : ℕ} (a b : Fin n → RationalSpace) (D : ℝ)
    {u : Fin 5 → ℝ} (h₁ : u 1 = 0) (h₂ : u 2 = 0) (h₃ : u 3 = 0) (h₄ : u 4 = 0)
    (i : Fin n) : routeCenterParameters a b D u i = spreadCenter a D (u 0) i := by
  ext j
  fin_cases j <;> simp [routeCenterParameters, spreadCenter, h₁, h₂, h₃, h₄]

theorem routeCenter_stage₁ {n : ℕ} (a b : Fin n → RationalSpace) (D : ℝ)
    {u : Fin 5 → ℝ} (h₀ : u 0 = 1) (h₂ : u 2 = 0) (_h₃ : u 3 = 0) (h₄ : u 4 = 0)
    (i : Fin n) : routeCenterParameters a b D u i 0 = spreadCenter a D 1 i 0 := by
  simp [routeCenterParameters, spreadCenter, h₀, h₂, h₄]

theorem routeCenter_stage₂ {n : ℕ} (a b : Fin n → RationalSpace) (D : ℝ)
    {u : Fin 5 → ℝ} (_h₀ : u 0 = 1) (h₁ : u 1 = 1) (h₃ : u 3 = 0) (_h₄ : u 4 = 0)
    (i : Fin n) : routeCenterParameters a b D u i 2 = D * (i : ℝ) := by
  simp [routeCenterParameters, h₁, h₃]

theorem routeCenter_stage₃ {n : ℕ} (a b : Fin n → RationalSpace) (D : ℝ)
    {u : Fin 5 → ℝ} (h₀ : u 0 = 1) (_h₁ : u 1 = 1) (h₂ : u 2 = 1) (h₄ : u 4 = 0)
    (i : Fin n) : routeCenterParameters a b D u i 0 = spreadCenter b D 1 i 0 := by
  simp [routeCenterParameters, spreadCenter, h₀, h₂, h₄]

theorem routeCenter_stage₄ {n : ℕ} (a b : Fin n → RationalSpace) (D : ℝ)
    {u : Fin 5 → ℝ} (h₀ : u 0 = 1) (h₁ : u 1 = 1) (h₂ : u 2 = 1) (h₃ : u 3 = 1)
    (i : Fin n) : routeCenterParameters a b D u i = spreadCenter b D (1 - u 4) i := by
  ext j
  fin_cases j <;> simp [routeCenterParameters, spreadCenter, h₀, h₁, h₂, h₃]
  ring

theorem routeCenters_before {n : ℕ} (a b : Fin n → RationalSpace) (D : ℝ)
    (i : Fin n) {t : ℝ} (ht : t ≤ 1 / 4) : routeCenters a b D i t = realPoint (a i) := by
  rw [routeCenters, routeCenter_stage₀ a b D
    (stageSwitch_before 1 ht) (stageSwitch_before 2 ht) (stageSwitch_before 3 ht)
    (stageSwitch_before 4 ht), stageSwitch_before 0 ht, spreadCenter_zero]

theorem routeCenters_after {n : ℕ} (a b : Fin n → RationalSpace) (D : ℝ)
    (i : Fin n) {t : ℝ} (ht : 3 / 4 ≤ t) : routeCenters a b D i t = realPoint (b i) := by
  rw [routeCenters, routeCenter_stage₄ a b D
    (stageSwitch_after 0 ht) (stageSwitch_after 1 ht) (stageSwitch_after 2 ht)
    (stageSwitch_after 3 ht), stageSwitch_after 4 ht, sub_self, spreadCenter_zero]

theorem private_layers_separated {n : ℕ} {D : ℝ} (hD : 0 ≤ D) {i j : Fin n} (hij : i ≠ j) :
    D ≤ |D * (i : ℝ) - D * (j : ℝ)| := by
  wlog hlt : i < j generalizing i j
  · simpa only [abs_sub_comm] using this hij.symm (lt_of_le_of_ne (le_of_not_gt hlt) hij.symm)
  have hstep : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hlt
  have ha := neg_le_abs (D * (i : ℝ) - D * (j : ℝ))
  nlinarith

theorem balancedScale_one (s : Space) (hdet : ∏ j : Fin 3, s j = 1) :
    balancedScale s 1 = s := by
  have hd : s 0 * s 1 * s 2 = 1 := by simpa [Fin.prod_univ_three] using hdet
  ext j
  fin_cases j
  · simp [balancedScale]
  · simp [balancedScale]
  · simpa [balancedScale] using inv_eq_of_mul_eq_one_right hd

theorem balancedScale_det (s : Space) (hs : ∀ j, 0 < s j)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) : ∏ j : Fin 3, balancedScale s u j = 1 := by
  simp only [Fin.prod_univ_three, balancedScale, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  exact mul_inv_cancel₀ (mul_ne_zero (ne_of_gt (linearBlend_pos (hs 0) hu))
    (ne_of_gt (linearBlend_pos (hs 1) hu)))

theorem scaleRatio_mul_width {n : ℕ} {h k : Fin n → RationalSpace}
    (hh : ∀ i j, 0 < h i j) (i : Fin n) (j : Fin 3) :
    scaleRatio h k i j * (h i j : ℝ) = (k i j : ℝ) := by
  unfold scaleRatio
  exact_mod_cast div_mul_cancel₀ (k i j) (ne_of_gt (hh i j))

theorem routeScales_det {n : ℕ} {h k : Fin n → RationalSpace}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (_hvol : ∀ i, ∏ j : Fin 3, k i j / h i j = 1) (i : Fin n) (t : ℝ) :
    ∏ j : Fin 3, routeScales h k i t j = 1 :=
  balancedScale_det _ (scaleRatio_pos hh hk i) (stageSwitch_mem 2 t)

theorem scaleRatio_det {n : ℕ} {h k : Fin n → RationalSpace}
    (hvol : ∀ i, ∏ j : Fin 3, k i j / h i j = 1) (i : Fin n) :
    ∏ j : Fin 3, scaleRatio h k i j = 1 := by
  unfold scaleRatio
  exact_mod_cast hvol i

theorem routeScales_le {n : ℕ} {h k : Fin n → RationalSpace}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (hvol : ∀ i, ∏ j : Fin 3, k i j / h i j = 1)
    {M : ℝ} (hM : 1 ≤ M) (hsM : ∀ i j, scaleRatio h k i j ≤ M)
    (i : Fin n) (t : ℝ) (j : Fin 3) : routeScales h k i t j ≤ M :=
  (balancedScale_le _ (scaleRatio_pos hh hk i) (scaleRatio_det hvol i) (stageSwitch_mem 2 t) j).trans
    (max_le hM (hsM i j))

theorem routeScales_before {n : ℕ} (h k : Fin n → RationalSpace)
    (i : Fin n) {t : ℝ} (ht : t ≤ 1 / 4) : routeScales h k i t = 1 := by
  simp [routeScales, stageSwitch_before 2 ht]

theorem routeScales_after {n : ℕ} (h k : Fin n → RationalSpace)
    (hvol : ∀ i, ∏ j : Fin 3, k i j / h i j = 1)
    (i : Fin n) {t : ℝ} (ht : 3 / 4 ≤ t) : routeScales h k i t = scaleRatio h k i := by
  simp only [routeScales, stageSwitch_after 2 ht, balancedScale_one _ (scaleRatio_det hvol i)]

theorem routeScales_width_le {n : ℕ} {h k : Fin n → RationalSpace}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (hvol : ∀ i, ∏ j : Fin 3, k i j / h i j = 1)
    {R : ℝ} (hhR : ∀ i j, (h i j : ℝ) ≤ R) (hkR : ∀ i j, (k i j : ℝ) ≤ R)
    (i : Fin n) (t : ℝ) (j : Fin 3) : routeScales h k i t j * (h i j : ℝ) ≤ R := by
  have hh' : 0 ≤ (h i j : ℝ) := by exact_mod_cast (hh i j).le
  have hs := balancedScale_le _ (scaleRatio_pos hh hk i) (scaleRatio_det hvol i) (stageSwitch_mem 2 t) j
  apply (mul_le_mul_of_nonneg_right hs hh').trans
  rw [max_mul_of_nonneg _ _ hh', one_mul, scaleRatio_mul_width hh]
  exact max_le (hhR i j) (hkR i j)

theorem boxDataBound_ge_one {n : ℕ} (h k : Fin n → RationalSpace) : 1 ≤ boxDataBound h k := by
  unfold boxDataBound
  have hn : 0 ≤ ∑ i : Fin n, ∑ j : Fin 3, (|h i j| + |k i j| + |k i j / h i j| + 1) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
  linarith

theorem boxDataBound_bounds {n : ℕ} (h k : Fin n → RationalSpace) (i : Fin n) (j : Fin 3) :
    h i j ≤ boxDataBound h k ∧ k i j ≤ boxDataBound h k ∧ k i j / h i j ≤ boxDataBound h k := by
  have h₁ : |h i j| + |k i j| + |k i j / h i j| + 1 ≤
      ∑ l : Fin 3, (|h i l| + |k i l| + |k i l / h i l| + 1) :=
    Finset.single_le_sum (f := fun l : Fin 3 => |h i l| + |k i l| + |k i l / h i l| + 1)
      (fun _ _ => by positivity) (Finset.mem_univ j)
  have h₂ : (∑ l : Fin 3, (|h i l| + |k i l| + |k i l / h i l| + 1)) ≤
      ∑ s : Fin n, ∑ l : Fin 3, (|h s l| + |k s l| + |k s l / h s l| + 1) :=
    Finset.single_le_sum (f := fun s : Fin n => ∑ l : Fin 3,
      (|h s l| + |k s l| + |k s l / h s l| + 1))
      (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity)) (Finset.mem_univ i)
  have hs := h₁.trans h₂
  have hha := le_abs_self (h i j)
  have hka := le_abs_self (k i j)
  have hsa := le_abs_self (k i j / h i j)
  have hhn := abs_nonneg (h i j)
  have hkn := abs_nonneg (k i j)
  have hsn := abs_nonneg (k i j / h i j)
  unfold boxDataBound
  constructor
  · linarith
  constructor <;> linarith

theorem route_padded_disjoint {n : ℕ} {a b h k : Fin n → RationalSpace}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (hvol : ∀ i, ∏ j : Fin 3, k i j / h i j = 1)
    {R η : ℝ} (hR : 0 < R) (hη : 0 < η) (hηR : η < R / 8)
    (hhR : ∀ i j, (h i j : ℝ) ≤ R) (hkR : ∀ i j, (k i j : ℝ) ≤ R)
    (ha : Pairwise fun i j =>
      Disjoint (realBox (realPoint (a i)) (fun l => (h i l : ℝ) + 2 * η))
        (realBox (realPoint (a j)) (fun l => (h j l : ℝ) + 2 * η)))
    (hb : Pairwise fun i j =>
      Disjoint (realBox (realPoint (b i)) (fun l => (k i l : ℝ) + 2 * η))
        (realBox (realPoint (b j)) (fun l => (k j l : ℝ) + 2 * η))) (t : ℝ) :
    Pairwise fun i j =>
      Disjoint
        (realBox (routeCenters a b (30 * R) i t)
          (fun l => routeScales h k i t l * (h i l : ℝ) + 2 * η))
        (realBox (routeCenters a b (30 * R) j t)
          (fun l => routeScales h k j t l * (h j l : ℝ) + 2 * η)) := by
  have hD : 0 ≤ 30 * R := by positivity
  have h4 : 4 * R ≤ 30 * R := by linarith
  have hwidth (i : Fin n) (j : Fin 3) := routeScales_width_le hh hk hvol hhR hkR i t j
  rcases stageSwitch_cases t with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₀, h₂, h₃, h₄⟩ |
    ⟨h₀, h₁, h₃, h₄⟩ | ⟨h₀, h₁, h₂, h₄⟩ | ⟨h₀, h₁, h₂, h₃⟩
  · have hp : ∀ i j, 0 ≤ (h i j : ℝ) + 2 * η := by
      intro i j
      have hhi : (0 : ℝ) < (h i j : ℝ) := by exact_mod_cast hh i j
      linarith
    have hs := spreadCenter_disjoint a (fun i j => (h i j : ℝ) + 2 * η) hD
      (stageSwitch_mem 0 t).1 hp ha
    simpa only [routeCenters, routeCenter_stage₀ a b (30 * R) (u := fun j => stageSwitch j t) h₁ h₂ h₃ h₄,
      routeScales, h₂, balancedScale_zero, Pi.one_apply, one_mul] using hs
  · intro i j hij
    apply padded_boxes_disjoint_of_clearance hR hηR (hwidth i) (hwidth j)
    refine ⟨0, h4.trans ?_⟩
    simpa only [routeCenters, routeCenter_stage₁ a b (30 * R) (u := fun j => stageSwitch j t) h₀ h₂ h₃ h₄] using
      spreadCenter_separated a hD hij
  · intro i j hij
    apply padded_boxes_disjoint_of_clearance hR hηR (hwidth i) (hwidth j)
    refine ⟨2, h4.trans ?_⟩
    simpa only [routeCenters, routeCenter_stage₂ a b (30 * R) (u := fun j => stageSwitch j t) h₀ h₁ h₃ h₄] using
      private_layers_separated hD hij
  · intro i j hij
    apply padded_boxes_disjoint_of_clearance hR hηR (hwidth i) (hwidth j)
    refine ⟨0, h4.trans ?_⟩
    simpa only [routeCenters, routeCenter_stage₃ a b (30 * R) (u := fun j => stageSwitch j t) h₀ h₁ h₂ h₄] using
      spreadCenter_separated b hD hij
  · have hp : ∀ i j, 0 ≤ (k i j : ℝ) + 2 * η := by
      intro i j
      have hki : (0 : ℝ) < (k i j : ℝ) := by exact_mod_cast hk i j
      linarith
    have hs := spreadCenter_disjoint b (fun i j => (k i j : ℝ) + 2 * η) hD
      (by have := (stageSwitch_mem 4 t).2; linarith : 0 ≤ 1 - stageSwitch 4 t) hp hb
    simpa only [routeCenters, routeCenter_stage₄ a b (30 * R) (u := fun j => stageSwitch j t) h₀ h₁ h₂ h₃,
      routeScales, h₂, balancedScale_one _ (scaleRatio_det hvol _), scaleRatio_mul_width hh] using hs

theorem routedField_realizes {n : ℕ} (a b h k : Fin n → RationalSpace)
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (hvol : ∀ i, ∏ j : Fin 3, k i j / h i j = 1)
    {η : ℚ} (hη : 0 < η) (hηR : η < boxDataBound h k / 8)
    (ha : Pairwise fun i j =>
      Disjoint (realBox (realPoint (a i)) (fun l => (h i l : ℝ) + 2 * η))
        (realBox (realPoint (a j)) (fun l => (h j l : ℝ) + 2 * η)))
    (hb : Pairwise fun i j =>
      Disjoint (realBox (realPoint (b i)) (fun l => (k i l : ℝ) + 2 * η))
        (realBox (realPoint (b j)) (fun l => (k j l : ℝ) + 2 * η))) :
    ContDiff ℝ ∞ (routedField a b h k η) ∧ HasCompactSupport (routedField a b h k η) ∧
    (∀ t x, spatialDivergence (routedField a b h k η) t x = 0) ∧
    (∀ (t : ℝ) x, t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) → routedField a b h k η (t, x) = 0) ∧
    ∃ Φ, IsGlobalFlow (routedField a b h k η) Φ ∧ Delivers a b h k Φ := by
  let R : ℝ := boxDataBound h k
  have hR₁ : 1 ≤ R := by dsimp [R]; exact_mod_cast boxDataBound_ge_one h k
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR₁
  have hη' : (0 : ℝ) < η := by exact_mod_cast hη
  have hηR' : (η : ℝ) < R / 8 := by dsimp [R]; exact_mod_cast hηR
  have hbound (i : Fin n) (j : Fin 3) :
      (h i j : ℝ) ≤ R ∧ (k i j : ℝ) ≤ R ∧ scaleRatio h k i j ≤ R := by
    dsimp [R, scaleRatio]
    exact_mod_cast boxDataBound_bounds h k i j
  have hstart (i : Fin n) (t : ℝ) (ht : t ≤ (1 / 4 : ℝ)) :
      routeCenters a b (30 * R) i t = realPoint (a i) ∧ routeScales h k i t = 1 :=
    ⟨routeCenters_before a b (30 * R) i ht, routeScales_before h k i ht⟩
  have hend (i : Fin n) (t : ℝ) (ht : (3 / 4 : ℝ) ≤ t) :
      routeCenters a b (30 * R) i t = routeCenters a b (30 * R) i 1 ∧
      routeScales h k i t = routeScales h k i 1 := by
    rw [routeCenters_after a b (30 * R) i ht, routeCenters_after a b (30 * R) i (t := 1) (by norm_num),
      routeScales_after h k hvol i ht, routeScales_after h k hvol i (t := 1) (by norm_num)]
    exact ⟨rfl, rfl⟩
  have hsep := route_padded_disjoint hh hk hvol hR hη' hηR'
    (fun i j => (hbound i j).1) (fun i j => (hbound i j).2.1) ha hb
  obtain ⟨hsm, hcp, hdiv, htime, Φ, hΦ, hn⟩ :=
    stationaryMotionField_realizes (fun i => realPoint (a i)) (fun i => realPoint (h i))
      hη' hR (contDiff_routeCenters a b (30 * R)) (contDiff_routeScales hh hk)
      hstart hend (routeScales_det hh hk hvol) (routeScales_pos hh hk)
      (routeScales_le hh hk hvol hR₁ (fun i j => (hbound i j).2.2)) hsep
  refine ⟨hsm, hcp, hdiv, htime, Φ, hΦ, ?_⟩
  intro i
  obtain ⟨O, hO, hbO, hmap⟩ := hn i
  refine ⟨O, hO, hbO, ?_⟩
  intro x hx
  rw [hmap x hx 1]
  ext j
  simp only [affineTrajectory, routeCenters_after a b (30 * R) i (t := 1) (by norm_num),
    routeScales_after h k hvol i (t := 1) (by norm_num), scaleRatio, realPoint, prescribedAffine]

theorem exists_routedField_realization
    (n : ℕ) (a b h k : Fin n → RationalSpace)
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (ha : Pairwise fun i j => Disjoint (solidBox (a i) (h i)) (solidBox (a j) (h j)))
    (hb : Pairwise fun i j => Disjoint (solidBox (b i) (k i)) (solidBox (b j) (k j)))
    (hvol : ∀ i, ∏ j : Fin 3, k i j / h i j = 1) :
    ∃ η : ℚ, 0 < η ∧
      ContDiff ℝ ∞ (routedField a b h k η) ∧ HasCompactSupport (routedField a b h k η) ∧
      (∀ t x, spatialDivergence (routedField a b h k η) t x = 0) ∧
      (∀ (t : ℝ) x, t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) → routedField a b h k η (t, x) = 0) ∧
      ∃ Φ, IsGlobalFlow (routedField a b h k η) Φ ∧ Delivers a b h k Φ := by
  have hR : 0 < boxDataBound h k := lt_of_lt_of_le zero_lt_one (boxDataBound_ge_one h k)
  obtain ⟨η, hη, hηR, hap, hbp⟩ := exists_rational_padding a b h k
    (fun i j => (hh i j).le) (fun i j => (hk i j).le) ha hb (boxDataBound h k) hR
  exact ⟨η, hη, routedField_realizes a b h k hh hk hvol hη hηR hap hbp⟩
end BoxTransport.Routing

end

end OAI

-- ---- from OAI.Analysis.BoxTransport.Routing ----
namespace OAI

/-! Effective realization of every balanced finite box instruction. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

open scoped BigOperators ContDiff
namespace BoxTransport.Routing.Computation

theorem representable_routedField {n : ℕ} (a b h k : Fin n → RationalSpace)
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j) (η : ℚ) (j : Fin 3) :
    Representable (fun p => routedField a b h k η p j) := by
  have hc (i : Fin n) (j : Fin 3) : Representable (fun p : SpaceTime =>
      routeCenters a b (30 * (boxDataBound h k : ℝ)) i p.1 j) := by
    simpa only [Rat.cast_mul, Rat.cast_ofNat] using representable_routeCenters a b (30 * boxDataBound h k) i j
  apply representable_spatialCurl
  apply representable_familyPotential
  · exact hc
  · intro i j
    exact representable_curve_deriv (contDiff_routeCenters a b _ i) (hc i) j
  · exact representable_diagonalLogVelocity hh hk
  · intro i j
    exact (representable_routeScales hh hk i j).mul (Representable.rational (h i j))

theorem effective_routedField {n : ℕ} (a b h k : Fin n → RationalSpace)
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j) (η : ℚ)
    (hs : ContDiff ℝ ∞ (routedField a b h k η)) (hc : HasCompactSupport (routedField a b h k η)) :
    Effective (routedField a b h k η) := by
  choose es he hv using representable_routedField a b h k hh hk η
  exact effective_of_expressions hs hc es he (fun p j => congrFun (hv j) p)

end BoxTransport.Routing.Computation

namespace BoxTransport.Routing

theorem balanced_box_routing
    (n : ℕ) (a b h k : Fin n → RationalSpace)
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (ha : Pairwise fun i j => Disjoint (solidBox (a i) (h i)) (solidBox (a j) (h j)))
    (hb : Pairwise fun i j => Disjoint (solidBox (b i) (k i)) (solidBox (b j) (k j)))
    (hvol : ∀ i, ∏ j : Fin 3, k i j / h i j = 1) :
    ∃ U : Field, ∃ Φ : ℝ → Space → Space,
      AdmissibleField U ∧ IsGlobalFlow U Φ ∧ Delivers a b h k Φ := by
  obtain ⟨η, _, hs, hc, hdiv, ht, Φ, hΦ, hdel⟩ := exists_routedField_realization n a b h k hh hk ha hb hvol
  exact ⟨routedField a b h k η, Φ, ⟨hs, hc, Computation.effective_routedField a b h k hh hk η hs hc,
    hdiv, ht⟩, hΦ, hdel⟩

end BoxTransport.Routing

end

end OAI

-- ---- mission target ----
open OAI OAI.BoxTransport OAI.BoxTransport.Routing
open scoped BigOperators ContDiff
open scoped Topology

theorem solution
    (n : ℕ) (a b h k : Fin n → RationalSpace)
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (ha : Pairwise fun i j => Disjoint (solidBox (a i) (h i)) (solidBox (a j) (h j)))
    (hb : Pairwise fun i j => Disjoint (solidBox (b i) (k i)) (solidBox (b j) (k j)))
    (hvol : ∀ i, ∏ j : Fin 3, k i j / h i j = 1) :
    ∃ U : Field, ∃ Φ : ℝ → Space → Space,
      AdmissibleField U ∧ IsGlobalFlow U Φ ∧ Delivers a b h k Φ := by
  first
    | exact OAI.BoxTransport.Routing.balanced_box_routing n a b h k hh hk ha hb hvol
    | exact OAI.BoxTransport.Routing.balanced_box_routing
    | (apply OAI.BoxTransport.Routing.balanced_box_routing <;> assumption)
    | (intros; apply OAI.BoxTransport.Routing.balanced_box_routing <;> assumption)
