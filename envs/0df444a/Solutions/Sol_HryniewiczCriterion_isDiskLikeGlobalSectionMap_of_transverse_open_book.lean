-- Prove2me | solution 1 for HryniewiczCriterion.isDiskLikeGlobalSectionMap_of_transverse_open_book
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T15:32:31.13121+00:00
-- url     : https://prove2.me/submissions/107e07d1-5ab2-4729-8a96-3b4ddad0c295
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking
import Theorems.Thm_HryniewiczCriterion_exists_page_parameter_along_trajectory
import Theorems.Thm_HryniewiczCriterion_tendsto_infDist_binding_of_bounded_page_parameter
import Theorems.Thm_HryniewiczCriterion_not_tendsto_binding_of_tendsto_page_parameter
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Floor

open HryniewiczCriterion
open scoped ContDiff
open Filter Topology Complex

/-!
# Glue for `isDiskLikeGlobalSectionMap_of_transverse_open_book`

Along a trajectory off the binding the page parameter `Θ` is continuous and strictly monotone
(child A). If `Θ` moved by less than `1` on a half-line it would converge, the trajectory would
converge to the binding (child B1), and that is excluded (child B2). So `Θ` moves by at least `1`
on every half-line and, by the intermediate value theorem, takes a value in `θ + ℤ`, where the
page is `page θ` again (integer periodicity).
-/


noncomputable section

namespace HryniewiczCriterion

lemma rpg_cp_surj (w : Plane) (hw : w 0 ^ 2 + w 1 ^ 2 = 1) : ∃ s, circlePoint s = w := by
  set z : ℂ := (w 0 : ℂ) + (w 1 : ℂ) * I
  have hzre : z.re = w 0 := by simp [z]
  have hzim : z.im = w 1 := by simp [z]
  have hzn : ‖z‖ = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [normSq_apply, hzre, hzim] at h
    nlinarith [norm_nonneg z]
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hzn; norm_num at hzn
  refine ⟨arg z / (2 * Real.pi), ?_⟩
  have h2 : 2 * Real.pi * (arg z / (2 * Real.pi)) = arg z := by field_simp
  ext i; fin_cases i
  · simp only [circlePoint, h2]
    simp [Complex.cos_arg hz0, hzn, hzre]
  · simp only [circlePoint, h2]
    simp [Complex.sin_arg, hzn, hzim]

lemma rpg_cp_mem (s : ℝ) : circlePoint s ∈ unitCircle := by
  show circlePoint s 0 ^ 2 + circlePoint s 1 ^ 2 = 1
  simp [circlePoint, Real.cos_sq_add_sin_sq]

lemma rpg_page_int (page : ℝ → Plane → R4) (hper : ∀ θ u, page (θ + 1) u = page θ u)
    (θ : ℝ) (n : ℤ) : page (θ + n) = page θ := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    funext u
    calc page (θ + ((k + 1 : ℤ) : ℝ)) u = page (θ + (k : ℝ) + 1) u := by
          congr 1; push_cast; ring
      _ = page (θ + (k : ℝ)) u := hper _ u
      _ = page θ u := by simpa using congrFun ih u
  | pred k ih =>
    funext u
    calc page (θ + ((-(k : ℤ) - 1 : ℤ) : ℝ)) u = page (θ + (-(k : ℝ) - 1)) u := by
          congr 1; push_cast; ring
      _ = page (θ + (-(k : ℝ) - 1) + 1) u := (hper _ u).symm
      _ = page (θ + ((-(k : ℤ) : ℤ) : ℝ)) u := by congr 1; push_cast; ring
      _ = page θ u := congrFun ih u

lemma rpg_hit (Θ : ℝ → ℝ) (hΘ : Continuous Θ) (θ a t₁ : ℝ) (h1 : 1 ≤ |Θ t₁ - Θ a|) :
    ∃ s ∈ Set.uIcc a t₁, s ≠ a ∧ ∃ n : ℤ, Θ s = θ + n := by
  have key : ∃ n : ℤ, θ + n ∈ Set.uIcc (Θ a) (Θ t₁) ∧ θ + n ≠ Θ a := by
    rcases le_abs'.1 h1 with h | h
    · refine ⟨⌈Θ a - θ⌉ - 1, ?_, ?_⟩
      · rw [Set.mem_uIcc]; right; push_cast
        constructor <;> linarith [Int.le_ceil (Θ a - θ), Int.ceil_lt_add_one (Θ a - θ)]
      · push_cast; intro h'; linarith [Int.ceil_lt_add_one (Θ a - θ)]
    · refine ⟨⌊Θ a - θ⌋ + 1, ?_, ?_⟩
      · rw [Set.mem_uIcc]; left; push_cast
        constructor <;> linarith [Int.floor_le (Θ a - θ), Int.lt_floor_add_one (Θ a - θ)]
      · push_cast; intro h'; linarith [Int.lt_floor_add_one (Θ a - θ)]
  obtain ⟨n, hc, hne⟩ := key
  obtain ⟨s, hs, hΘs⟩ := intermediate_value_uIcc hΘ.continuousOn hc
  exact ⟨s, hs, fun h => hne (by rw [← hΘs, h]), n, hΘs⟩

lemma rpg_conv_top (Θ : ℝ → ℝ) (hmono : StrictMono Θ ∨ StrictAnti Θ) (a : ℝ)
    (hb : ∀ t, a < t → |Θ t - Θ a| < 1) : ∃ θs, Tendsto Θ atTop (𝓝 θs) := by
  rcases hmono with hm | hm
  · refine ⟨_, tendsto_atTop_ciSup hm.monotone ⟨Θ a + 1, ?_⟩⟩
    rintro _ ⟨t, rfl⟩
    rcases lt_or_ge a t with h | h
    · linarith [(abs_lt.1 (hb t h)).2]
    · linarith [hm.monotone h]
  · refine ⟨_, tendsto_atTop_ciInf hm.antitone ⟨Θ a - 1, ?_⟩⟩
    rintro _ ⟨t, rfl⟩
    rcases lt_or_ge a t with h | h
    · linarith [(abs_lt.1 (hb t h)).1]
    · linarith [hm.antitone h]

lemma rpg_conv_bot (Θ : ℝ → ℝ) (hmono : StrictMono Θ ∨ StrictAnti Θ) (a : ℝ)
    (hb : ∀ t, t < a → |Θ t - Θ a| < 1) : ∃ θs, Tendsto Θ atBot (𝓝 θs) := by
  rcases hmono with hm | hm
  · refine ⟨_, tendsto_atBot_ciInf hm.monotone ⟨Θ a - 1, ?_⟩⟩
    rintro _ ⟨t, rfl⟩
    rcases lt_or_ge t a with h | h
    · linarith [(abs_lt.1 (hb t h)).1]
    · linarith [hm.monotone h]
  · refine ⟨_, tendsto_atBot_ciSup hm.antitone ⟨Θ a + 1, ?_⟩⟩
    rintro _ ⟨t, rfl⟩
    rcases lt_or_ge t a with h | h
    · linarith [(abs_lt.1 (hb t h)).2]
    · linarith [hm.antitone h]

lemma rpg_bdd (Θ : ℝ → ℝ) (a : ℝ) (S : Set ℝ) (hS : ∀ t ∈ S, t ≠ a → |Θ t - Θ a| < 1) :
    Bornology.IsBounded (Θ '' S) := by
  refine (Metric.isBounded_Icc (Θ a - 1) (Θ a + 1)).subset ?_
  rintro _ ⟨t, ht, rfl⟩
  by_cases h : t = a
  · subst h; constructor <;> linarith
  · have := abs_lt.1 (hS t ht h); constructor <;> linarith [this.1, this.2]

theorem rpg_main (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H) (P : PeriodicOrbit H)
    (hcz : ∀ Y : ℝ → (R4 →L[ℝ] R4), IsLinearizedFlow H P.x Y →
      3 ≤ czIndexOfPath (linearizedXiPath H P Y))
    (page : ℝ → Plane → R4)
    (hob : ContDiff ℝ ∞ (fun z : ℝ × Plane => page z.1 z.2) ∧
      (∀ θ u, page (θ + 1) u = page θ u) ∧
      (∀ θ, IsSmoothDiskEmbedding (page θ)) ∧
      (∀ θ, page θ '' closedUnitDisk ⊆ energySurface H) ∧
      (∀ θ t, page θ (circlePoint t) = P.x (P.T * t)) ∧
      (∀ θ, ∀ u ∈ openUnitDisk,
        hamiltonianVectorField H (page θ u) ∉ Set.range (fderiv ℝ (page θ) u)) ∧
      (∀ y ∈ energySurface H, y ∉ P.image →
        ∃! z : ℝ × Plane, z.1 ∈ Set.Ico (0 : ℝ) 1 ∧ z.2 ∈ openUnitDisk ∧ page z.1 z.2 = y) ∧
      (∀ θ : ℝ, ∀ u ∈ openUnitDisk,
        Function.Injective (fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) (θ, u)))) :
    ∀ θ : ℝ, IsDiskLikeGlobalSectionMap H P (page θ) := by
  have hob' := hob
  obtain ⟨_, hper, hemb, hSu, hbd, htr, _, _⟩ := hob'
  intro θ
  refine ⟨hemb θ, hSu θ, ?_, htr θ, ?_⟩
  · ext x; constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨s, rfl⟩ := rpg_cp_surj w hw
      rw [hbd]; exact ⟨_, rfl⟩
    · rintro ⟨t, rfl⟩
      refine ⟨circlePoint (t / P.T), rpg_cp_mem _, ?_⟩
      rw [hbd, mul_div_cancel₀ _ P.T_pos.ne']
  · intro y hy hy0 a
    obtain ⟨Θ, u, hΘ, hmono, hyu⟩ :=
      exists_page_parameter_along_trajectory H hS P page hob y hy hy0
    obtain ⟨hB1t, hB1b⟩ :=
      tendsto_infDist_binding_of_bounded_page_parameter H hS P page hob y hy Θ u hΘ hmono hyu
    have hB2 := fun θs =>
      not_tendsto_binding_of_tendsto_page_parameter H hS P hcz page hob y hy Θ u hyu θs
    have hmem : ∀ s, (∃ n : ℤ, Θ s = θ + n) → y s ∈ page θ '' closedUnitDisk := by
      rintro s ⟨n, hn⟩
      refine ⟨u s, show (u s) 0 ^ 2 + (u s) 1 ^ 2 ≤ 1 from le_of_lt (hyu s).1, ?_⟩
      rw [← (hyu s).2, hn, rpg_page_int page hper θ n]
    constructor
    · have hpos : ∃ t₁, a < t₁ ∧ 1 ≤ |Θ t₁ - Θ a| := by
        by_contra hcon
        push_neg at hcon
        have hbdd : Bornology.IsBounded (Θ '' Set.Ici a) :=
          rpg_bdd Θ a _ fun t ht hta => hcon t (lt_of_le_of_ne (Set.mem_Ici.1 ht) (Ne.symm hta))
        obtain ⟨θs, hθs⟩ := rpg_conv_top Θ hmono a hcon
        exact (hB2 θs).1 ⟨hθs, hB1t a hbdd⟩
      obtain ⟨t₁, hat, h1⟩ := hpos
      obtain ⟨s, hs, hsa, hn⟩ := rpg_hit Θ hΘ θ a t₁ h1
      rw [Set.uIcc_of_le hat.le] at hs
      exact ⟨s, lt_of_le_of_ne hs.1 (Ne.symm hsa), hmem s hn⟩
    · have hneg : ∃ t₁, t₁ < a ∧ 1 ≤ |Θ t₁ - Θ a| := by
        by_contra hcon
        push_neg at hcon
        have hbdd : Bornology.IsBounded (Θ '' Set.Iic a) :=
          rpg_bdd Θ a _ fun t ht hta => hcon t (lt_of_le_of_ne (Set.mem_Iic.1 ht) hta)
        obtain ⟨θs, hθs⟩ := rpg_conv_bot Θ hmono a hcon
        exact (hB2 θs).2 ⟨hθs, hB1b a hbdd⟩
      obtain ⟨t₁, hta, h1⟩ := hneg
      obtain ⟨s, hs, hsa, hn⟩ := rpg_hit Θ hΘ θ a t₁ h1
      rw [Set.uIcc_of_ge hta.le] at hs
      exact ⟨s, lt_of_le_of_ne hs.2 hsa, hmem s hn⟩

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H) (P : PeriodicOrbit H)
    (hcz : ∀ Y : ℝ → (R4 →L[ℝ] R4), IsLinearizedFlow H P.x Y →
      3 ≤ czIndexOfPath (linearizedXiPath H P Y))
    (page : ℝ → Plane → R4)
    (hob : ContDiff ℝ ∞ (fun z : ℝ × Plane => page z.1 z.2) ∧
      (∀ θ u, page (θ + 1) u = page θ u) ∧
      (∀ θ, IsSmoothDiskEmbedding (page θ)) ∧
      (∀ θ, page θ '' closedUnitDisk ⊆ energySurface H) ∧
      (∀ θ t, page θ (circlePoint t) = P.x (P.T * t)) ∧
      (∀ θ, ∀ u ∈ openUnitDisk,
        hamiltonianVectorField H (page θ u) ∉ Set.range (fderiv ℝ (page θ) u)) ∧
      (∀ y ∈ energySurface H, y ∉ P.image →
        ∃! z : ℝ × Plane, z.1 ∈ Set.Ico (0 : ℝ) 1 ∧ z.2 ∈ openUnitDisk ∧ page z.1 z.2 = y) ∧
      (∀ θ : ℝ, ∀ u ∈ openUnitDisk,
        Function.Injective (fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) (θ, u)))) :
    ∀ θ : ℝ, IsDiskLikeGlobalSectionMap H P (page θ) :=
  rpg_main H hS P hcz page hob
