-- Prove2me | solution 1 for HarmonicRanking.Main.Supplement.lemma_B_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T20:24:00.763797+00:00
-- url     : https://prove2.me/submissions/dc867d92-5640-425b-9330-ecaea0beccf9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HarmonicRanking_Main_Supplement_PriceLP
import Theorems.Thm_HarmonicRanking_Main_Supplement_lemma_B_4

set_option autoImplicit false
noncomputable section

namespace HarmonicRanking.Main.Supplement


def tableOf {m : ℕ} (h : Interval m → ℝ) : Fin m → Fin m → ℝ := fun ℓ r =>
  if hlr : ℓ < r then (1 + h ⟨(ℓ, r), hlr⟩) / 2
  else if hrl : r < ℓ then (1 - h ⟨(r, ℓ), hrl⟩) / 2 else 1 / 2

lemma tableOf_lt {m : ℕ} (h : Interval m → ℝ) {ℓ r : Fin m} (hlr : ℓ < r) :
    tableOf h ℓ r = (1 + h ⟨(ℓ, r), hlr⟩) / 2 := by
  simp [tableOf, hlr]

lemma tableOf_gt {m : ℕ} (h : Interval m → ℝ) {ℓ r : Fin m} (hlr : r < ℓ) :
    tableOf h ℓ r = (1 - h ⟨(r, ℓ), hlr⟩) / 2 := by
  simp [tableOf, hlr, not_lt.2 hlr.le]

lemma tableOf_eq {m : ℕ} (h : Interval m → ℝ) (ℓ : Fin m) :
    tableOf h ℓ ℓ = 1 / 2 := by
  simp [tableOf]

lemma tableOf_D {m : ℕ} (h : Interval m → ℝ) : InD (tableOf h) := by
  intro ℓ r
  rcases lt_trichotomy ℓ r with hlr | hlr | hlr
  · rw [tableOf_lt h hlr, tableOf_gt h hlr]; ring
  · subst hlr; rw [tableOf_eq]; norm_num
  · rw [tableOf_lt h hlr, tableOf_gt h hlr]; ring

lemma mono_of_anti {m : ℕ} (F : Fin m → Fin m → ℝ) (hD : InD F)
    (ha : ∀ r, Antitone (fun ℓ => F ℓ r)) : ∀ ℓ, Monotone (F ℓ) := by
  intro ℓ r r' hr
  have h1 := ha ℓ hr
  have h2 := hD ℓ r
  have h3 := hD ℓ r'
  have h4 := hD r ℓ
  have h5 := hD r' ℓ
  simp only at h1
  linarith

lemma tableOf_anti {m : ℕ} (h : Interval m → ℝ) (hh : InOrderPolytope h) (r : Fin m) :
    Antitone (fun ℓ => tableOf h ℓ r) := by
  intro a b hab
  simp only
  have hm := hh.2
  have hb := hh.1
  rcases lt_trichotomy b r with h2 | h2 | h2
  · have h1 : a < r := lt_of_le_of_lt hab h2
    rw [tableOf_lt h h1, tableOf_lt h h2]
    have := hm ⟨(b, r), h2⟩ ⟨(a, r), h1⟩ ⟨hab, le_rfl⟩
    linarith
  · subst h2
    rcases lt_or_eq_of_le hab with h1 | h1
    · rw [tableOf_lt h h1, tableOf_eq]
      have := (hb ⟨(a, b), h1⟩).1
      linarith
    · subst h1; exact le_rfl
  · rw [tableOf_gt h h2]
    rcases lt_trichotomy a r with h1 | h1 | h1
    · rw [tableOf_lt h h1]
      have := (hb ⟨(r, b), h2⟩).1
      have := (hb ⟨(a, r), h1⟩).1
      linarith
    · subst h1; rw [tableOf_eq]
      have := (hb ⟨(a, b), h2⟩).1
      linarith
    · rw [tableOf_gt h h1]
      have := hm ⟨(r, a), h1⟩ ⟨(r, b), h2⟩ ⟨le_rfl, hab⟩
      linarith

lemma tableOf_InA {m : ℕ} (h : Interval m → ℝ) (hh : InOrderPolytope h) : InA (tableOf h) := by
  have hD := tableOf_D h
  have hb := hh.1
  refine ⟨hD, ?_, tableOf_anti h hh, mono_of_anti _ hD (tableOf_anti h hh)⟩
  intro ℓ r
  rcases lt_trichotomy ℓ r with h1 | h1 | h1
  · rw [tableOf_lt h h1]
    have := hb ⟨(ℓ, r), h1⟩
    constructor <;> linarith [this.1, this.2]
  · subst h1; rw [tableOf_eq]; constructor <;> norm_num
  · rw [tableOf_gt h h1]
    have := hb ⟨(r, ℓ), h1⟩
    constructor <;> linarith [this.1, this.2]

lemma intervalCoords_tableOf {m : ℕ} (h : Interval m → ℝ) :
    intervalCoords (tableOf h) = h := by
  funext I
  obtain ⟨⟨a, b⟩, hab⟩ := I
  simp only [intervalCoords]
  rw [tableOf_lt h hab]; ring

lemma intervalCoords_mem {m : ℕ} {F : Fin m → Fin m → ℝ} (hF : InA F) :
    InOrderPolytope (intervalCoords F) := by
  obtain ⟨hD, hb, ha, hmo⟩ := hF
  have diag : ∀ ℓ, F ℓ ℓ = 1 / 2 := fun ℓ => by have := hD ℓ ℓ; linarith
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨a, b⟩, hab⟩
    simp only [intervalCoords]
    have h1 : F b b ≤ F a b := ha b hab.le
    have := (hb a b).2
    rw [diag] at h1
    constructor <;> linarith
  · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨c, d⟩, hcd⟩ ⟨h1, h2⟩
    simp only [intervalCoords] at *
    have e1 : F a b ≤ F c b := ha b h1
    have e2 : F c b ≤ F c d := hmo c h2
    linarith

theorem part1 (m : ℕ) : Set.BijOn (intervalCoords (m := m)) {F | InA F} {h | InOrderPolytope h} := by
  refine ⟨fun F hF => intervalCoords_mem hF, ?_, ?_⟩
  · intro F hF G hG hFG
    have hD := hF.1
    have hD' := hG.1
    funext ℓ r
    rcases lt_trichotomy ℓ r with h1 | h1 | h1
    · have := congrFun hFG ⟨(ℓ, r), h1⟩
      simp only [intervalCoords] at this
      linarith
    · subst h1
      have := hD ℓ ℓ; have := hD' ℓ ℓ; linarith
    · have := congrFun hFG ⟨(r, ℓ), h1⟩
      simp only [intervalCoords] at this
      have := hD ℓ r; have := hD' ℓ r; linarith
  · intro h hh
    exact ⟨tableOf h, tableOf_InA h hh, intervalCoords_tableOf h⟩



lemma sum_interval {m : ℕ} (φ : Interval m → ℝ) :
    ∑ I, φ I = ∑ ℓ : Fin m, ∑ r : Fin m, if hlr : ℓ < r then φ ⟨(ℓ, r), hlr⟩ else 0 := by
  have e1 : ∑ I, φ I = ∑ x : Interval m,
      (if hq : (x : Fin m × Fin m).1 < (x : Fin m × Fin m).2 then φ ⟨x, hq⟩ else 0) :=
    Finset.sum_congr rfl fun I _ => by rw [dif_pos I.2]
  have := Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset (Fin m × Fin m)))
    (p := fun q => q.1 < q.2)
    (f := fun q => if hq : q.1 < q.2 then φ ⟨q, hq⟩ else 0)
  rw [Finset.subtype_univ, Finset.sum_filter] at this
  rw [e1, this, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun r _ => ?_
  by_cases hlr : ℓ < r <;> simp [hlr]

lemma sigma_ge {m : ℕ} (δ : Interval m → ℝ) (U : Finset (Interval m)) (hU : IsUpClosed U) :
    ∑ I ∈ U, δ I ≤ sigma δ := by
  classical
  unfold sigma
  convert Finset.le_sup' (fun U : Finset (Interval m) => ∑ I ∈ U, δ I)
    (Finset.mem_filter.2 ⟨Finset.mem_univ U, hU⟩)

lemma sigma_attained {m : ℕ} (δ : Interval m → ℝ) :
    ∃ U : Finset (Interval m), IsUpClosed U ∧ sigma δ = ∑ I ∈ U, δ I := by
  classical
  unfold sigma
  obtain ⟨U, hU, he⟩ := Finset.exists_mem_eq_sup' (⟨∅, by simp [IsUpClosed]⟩ :
    ((Finset.univ : Finset (Finset (Interval m))).filter IsUpClosed).Nonempty)
    (fun U : Finset (Interval m) => ∑ I ∈ U, δ I)
  exact ⟨U, (Finset.mem_filter.1 hU).2, by convert he⟩

lemma integral_ind (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    ∫ t in (0:ℝ)..1, (Set.Iic c).indicator (fun _ => (1:ℝ)) t = c := by
  rw [intervalIntegral.integral_of_le zero_le_one, MeasureTheory.integral_indicator measurableSet_Iic,
    MeasureTheory.setIntegral_const]
  rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.restrict_apply measurableSet_Iic]
  have : Set.Iic c ∩ Set.Ioc (0:ℝ) 1 = Set.Ioc 0 c := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
    constructor
    · rintro ⟨a, b, _⟩; exact ⟨b, a⟩
    · rintro ⟨a, b⟩; exact ⟨b, a, by linarith⟩
  rw [this]; simp [h0]

lemma layer_cake {m : ℕ} (h δ : Interval m → ℝ) (hh : InOrderPolytope h) :
    ∑ I, h I * δ I ≤ sigma δ := by
  classical
  have hint : ∀ I : Interval m, IntervalIntegrable
      (fun t : ℝ => δ I * (Set.Iic (h I)).indicator (fun _ => (1:ℝ)) t) MeasureTheory.volume 0 1 := by
    intro I
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    refine MeasureTheory.Integrable.const_mul ?_ _
    exact (MeasureTheory.integrableOn_const (by simp)).indicator measurableSet_Iic
  have key : ∑ I, h I * δ I = ∫ t in (0:ℝ)..1, ∑ I, δ I * (Set.Iic (h I)).indicator (fun _ => (1:ℝ)) t := by
    rw [intervalIntegral.integral_finsetSum (fun I _ => hint I)]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_ind _ (hh.1 I).1 (hh.1 I).2]; ring
  rw [key]
  have hle : ∀ t : ℝ, ∑ I, δ I * (Set.Iic (h I)).indicator (fun _ => (1:ℝ)) t ≤ sigma δ := by
    intro t
    have hU : IsUpClosed (Finset.univ.filter fun I => t ≤ h I) := by
      intro I J hI hIJ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hI ⊢
      exact hI.trans (hh.2 I J hIJ)
    refine le_trans (le_of_eq ?_) (sigma_ge δ _ hU)
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun I _ => ?_
    by_cases ht : t ≤ h I <;> simp [Set.indicator, ht]
  calc _ ≤ ∫ t in (0:ℝ)..1, sigma δ := by
        refine intervalIntegral.integral_mono_on zero_le_one ?_ (by simp) (fun t _ => hle t)
        have := IntervalIntegrable.sum Finset.univ (fun I _ => hint I)
        have e : (∑ i, fun t : ℝ => δ i * (Set.Iic (h i)).indicator (fun _ => (1:ℝ)) t) =
            fun t => ∑ I, δ I * (Set.Iic (h I)).indicator (fun _ => (1:ℝ)) t := by
          funext t; simp [Finset.sum_apply]
        rwa [e] at this
    _ = sigma δ := by simp


lemma sum_h_delta {m : ℕ} (F : Fin m → Fin m → ℝ) (hD : InD F) (M : Fin m → Fin m → ℝ) :
    ∑ ℓ : Fin m, ∑ r : Fin m, (2 * F ℓ r - 1) * M ℓ r =
      ∑ I : Interval m, intervalCoords F I * (M I.1.1 I.1.2 - M I.1.2 I.1.1) := by
  rw [sum_interval]
  set hh : Fin m → Fin m → ℝ := fun ℓ r => if hlr : ℓ < r then intervalCoords F ⟨(ℓ, r), hlr⟩ else 0
    with hhdef
  have e1 : ∀ ℓ r : Fin m, 2 * F ℓ r - 1 = hh ℓ r - hh r ℓ := by
    intro ℓ r
    rcases lt_trichotomy ℓ r with h1 | h1 | h1
    · have : ¬ r < ℓ := not_lt.2 h1.le
      simp only [hhdef, h1, this, dif_pos, dif_neg, not_false_eq_true, intervalCoords]; ring
    · subst h1; have := hD ℓ ℓ; simp only [hhdef, lt_irrefl, dif_neg, not_false_eq_true]; linarith
    · have hn : ¬ ℓ < r := not_lt.2 h1.le
      have h2 := hD ℓ r
      have h3 := hD r ℓ
      simp only [hhdef, h1, hn, dif_pos, dif_neg, not_false_eq_true, intervalCoords]
      linarith
  have e2 : ∀ ℓ r : Fin m, (if hlr : ℓ < r then intervalCoords F ⟨(ℓ, r), hlr⟩ * (M ℓ r - M r ℓ) else 0)
      = hh ℓ r * M ℓ r - hh ℓ r * M r ℓ := by
    intro ℓ r
    by_cases hlr : ℓ < r <;> simp [hhdef, hlr]; ring
  simp only [e1, e2, sub_mul, Finset.sum_sub_distrib]
  have : ∑ ℓ : Fin m, ∑ r : Fin m, hh r ℓ * M ℓ r = ∑ ℓ : Fin m, ∑ r : Fin m, hh ℓ r * M r ℓ :=
    Finset.sum_comm
  rw [this]

lemma priced_eq {m : ℕ} (hm : 1 ≤ m) (F : Fin m → Fin m → ℝ) (hD : InD F)
    (x : Fin m → Fin m → Fin m → ℝ) :
    pricedObjective F x = ((∑ ℓ, ∑ r, aggM x ℓ r) + ∑ I, intervalCoords F I * imbalance x I) /
      (m : ℝ) ^ 2 := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have := sum_h_delta F hD (aggM x)
  have e : ∑ I : Interval m, intervalCoords F I * imbalance x I =
      ∑ I : Interval m, intervalCoords F I * (aggM x I.1.1 I.1.2 - aggM x I.1.2 I.1.1) := rfl
  rw [e, ← this]
  have e3 : ∑ ℓ : Fin m, ∑ r : Fin m, ∑ p : Fin m, F ℓ r * x ℓ r p =
      ∑ ℓ : Fin m, ∑ r : Fin m, F ℓ r * rowMass x ℓ r := by
    simp [rowMass, Finset.mul_sum]
  unfold pricedObjective
  rw [e3]
  have e4 : (∑ ℓ : Fin m, ∑ r : Fin m, aggM x ℓ r) + ∑ ℓ : Fin m, ∑ r : Fin m, (2 * F ℓ r - 1) * aggM x ℓ r
      = ∑ ℓ : Fin m, ∑ r : Fin m, 2 * (m:ℝ) * (F ℓ r * rowMass x ℓ r) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    unfold aggM; ring
  rw [e4]
  simp only [← Finset.mul_sum]
  field_simp

lemma cumY_smul_add {m : ℕ} (a b : ℝ) (x y : Fin m → Fin m → Fin m → ℝ) (ℓ r p : Fin m) :
    cumY (a • x + b • y) ℓ r p = a * cumY x ℓ r p + b * cumY y ℓ r p := by
  simp only [cumY, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  split_ifs <;> ring

lemma cumY_continuous {m : ℕ} (ℓ r p : Fin m) :
    Continuous (fun x : Fin m → Fin m → Fin m → ℝ => cumY x ℓ r p) := by
  unfold cumY
  refine continuous_finset_sum _ fun h _ => ?_
  split_ifs
  · exact (continuous_apply p).comp ((continuous_apply r).comp (continuous_apply h))
  · exact continuous_const

lemma convex_Ccap (m : ℕ) : Convex ℝ {x : Fin m → Fin m → Fin m → ℝ | InCcap x} := by
  intro x hx y hy a b ha hb hab
  obtain ⟨⟨hx0, hx50, hx51, hx52, hx53⟩, hxc⟩ := hx
  obtain ⟨⟨hy0, hy50, hy51, hy52, hy53⟩, hyc⟩ := hy
  have key : ∀ c : ℝ, a * c + b * c = c := fun c => by rw [← add_mul, hab, one_mul]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro ℓ r p
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hx0 ℓ r p, hy0 ℓ r p, mul_nonneg ha (hx0 ℓ r p), mul_nonneg hb (hy0 ℓ r p)]
  · intro ℓ r p
    rw [cumY_smul_add, cumY_smul_add]
    nlinarith [mul_le_mul_of_nonneg_left (hx50 ℓ r p) ha, mul_le_mul_of_nonneg_left (hy50 ℓ r p) hb,
      key (1 / (m:ℝ))]
  · intro ℓ r p hℓ hp
    rw [cumY_smul_add, cumY_smul_add]
    nlinarith [mul_le_mul_of_nonneg_left (hx51 ℓ r p hℓ hp) ha,
      mul_le_mul_of_nonneg_left (hy51 ℓ r p hℓ hp) hb]
  · intro ℓ r p hℓ hlt
    rw [cumY_smul_add, cumY_smul_add, hx52 ℓ r p hℓ hlt, hy52 ℓ r p hℓ hlt]
  · intro ℓ r p hℓ hp
    rw [cumY_smul_add, cumY_smul_add]
    nlinarith [mul_le_mul_of_nonneg_left (hx53 ℓ r p hℓ hp) ha,
      mul_le_mul_of_nonneg_left (hy53 ℓ r p hℓ hp) hb]
  · intro ℓ r p
    rw [cumY_smul_add]
    have := hxc ℓ r p
    have := hyc ℓ r p
    constructor
    · nlinarith [mul_nonneg ha (hxc ℓ r p).1, mul_nonneg hb (hyc ℓ r p).1]
    · nlinarith [mul_le_mul_of_nonneg_left (hxc ℓ r p).2 ha,
        mul_le_mul_of_nonneg_left (hyc ℓ r p).2 hb, key (1 / (m:ℝ))]

lemma Ccap_nonempty {m : ℕ} (hm : 1 ≤ m) : ∃ x : Fin m → Fin m → Fin m → ℝ, InCcap x := by
  have hm0 : 0 < m := hm
  let x : Fin m → Fin m → Fin m → ℝ := fun ℓ _ _ => if ℓ.val = 0 then 1 / (m:ℝ) else 0
  have hy : ∀ ℓ r p : Fin m, cumY x ℓ r p = 1 / (m:ℝ) := by
    intro ℓ r p
    simp only [cumY, x]
    rw [Finset.sum_eq_single (⟨0, hm0⟩ : Fin m)]
    · simp [Fin.le_def]
    · intro b _ hb
      have : b.val ≠ 0 := fun h => hb (Fin.ext h)
      simp [this]
    · simp
  have hpos : (0:ℝ) ≤ 1 / (m:ℝ) := by positivity
  refine ⟨x, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro ℓ r p; simp only [x]; split_ifs <;> simp [hpos]
  · intro ℓ r p; rw [hy, hy]
    have : (0:ℝ) ≤ 1 / (m:ℝ) := hpos
    linarith
  · intro ℓ r p _ _; rw [hy, hy]
  · intro ℓ r p _ _; rw [hy, hy]
  · intro ℓ r p _ _; rw [hy, hy]
  · intro ℓ r p; rw [hy]; exact ⟨hpos, le_rfl⟩

lemma Ccap_compact (m : ℕ) : IsCompact {x : Fin m → Fin m → Fin m → ℝ | InCcap x} := by
  have hcl : IsClosed {x : Fin m → Fin m → Fin m → ℝ | InCcap x} := by
    have hc := fun ℓ r p => cumY_continuous (m := m) ℓ r p
    have e : {x : Fin m → Fin m → Fin m → ℝ | InCcap x} =
        (⋂ ℓ, ⋂ r, ⋂ p, {x | 0 ≤ x ℓ r p}) ∩ (⋂ ℓ, ⋂ r, ⋂ p, {x | 1 / (m:ℝ) ≤ cumY x ℓ r ℓ + cumY x r ℓ p}) ∩
        (⋂ ℓ, ⋂ r, ⋂ p, ⋂ (hℓ : ℓ.val + 1 < m), ⋂ (_ : p.val ≤ ℓ.val),
          {x | cumY x ℓ r p ≤ cumY x ⟨ℓ.val + 1, hℓ⟩ r ⟨p.val + 1, by omega⟩}) ∩
        (⋂ ℓ, ⋂ r, ⋂ p, ⋂ (hℓ : ℓ.val + 1 < m), ⋂ (_ : ℓ < p),
          {x | cumY x ℓ r p = cumY x ℓ r ⟨ℓ.val + 1, hℓ⟩}) ∩
        (⋂ ℓ, ⋂ r, ⋂ p, ⋂ (hℓ : ℓ.val + 1 < m), ⋂ (_ : p ≤ ℓ),
          {x | cumY x ℓ r ⟨ℓ.val + 1, hℓ⟩ ≤ cumY x ⟨ℓ.val + 1, hℓ⟩ r p}) ∩
        (⋂ ℓ, ⋂ r, ⋂ p, {x | 0 ≤ cumY x ℓ r p ∧ cumY x ℓ r p ≤ 1 / (m:ℝ)}) := by
      ext x
      simp only [InCcap, InC, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
      tauto
    rw [e]
    refine IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_) ?_) ?_
    · exact isClosed_iInter fun ℓ => isClosed_iInter fun r => isClosed_iInter fun p =>
        isClosed_le continuous_const ((continuous_apply p).comp ((continuous_apply r).comp (continuous_apply ℓ)))
    · exact isClosed_iInter fun ℓ => isClosed_iInter fun r => isClosed_iInter fun p =>
        isClosed_le continuous_const ((hc ℓ r ℓ).add (hc r ℓ p))
    · exact isClosed_iInter fun ℓ => isClosed_iInter fun r => isClosed_iInter fun p =>
        isClosed_iInter fun hℓ => isClosed_iInter fun _ => isClosed_le (hc _ _ _) (hc _ _ _)
    · exact isClosed_iInter fun ℓ => isClosed_iInter fun r => isClosed_iInter fun p =>
        isClosed_iInter fun hℓ => isClosed_iInter fun _ => isClosed_eq (hc _ _ _) (hc _ _ _)
    · exact isClosed_iInter fun ℓ => isClosed_iInter fun r => isClosed_iInter fun p =>
        isClosed_iInter fun hℓ => isClosed_iInter fun _ => isClosed_le (hc _ _ _) (hc _ _ _)
    · exact isClosed_iInter fun ℓ => isClosed_iInter fun r => isClosed_iInter fun p =>
        (isClosed_le continuous_const (hc ℓ r p)).inter (isClosed_le (hc ℓ r p) continuous_const)
  refine (isCompact_univ_pi (fun ℓ => isCompact_univ_pi (fun r => isCompact_univ_pi
    (fun p => (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) (1 / (m:ℝ))))))) |>.of_isClosed_subset hcl ?_)
  intro x hx
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  intro ℓ r p
  have h0 := hx.1.1
  have hc := hx.2 ℓ r p
  refine ⟨h0 ℓ r p, le_trans ?_ hc.2⟩
  unfold cumY
  calc x ℓ r p = ∑ h : Fin m, if h = ℓ then x h r p else 0 := by simp
    _ ≤ _ := Finset.sum_le_sum fun h _ => by
      by_cases hl : h = ℓ
      · simp [hl]
      · by_cases hle : h ≤ ℓ <;> simp [hl, hle, h0]



lemma aggM_smul_add {m : ℕ} (a b : ℝ) (x y : Fin m → Fin m → Fin m → ℝ) (ℓ r : Fin m) :
    aggM (a • x + b • y) ℓ r = a * aggM x ℓ r + b * aggM y ℓ r := by
  simp only [aggM, rowMass, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

def uvec {m : ℕ} (x : Fin m → Fin m → Fin m → ℝ) (U : Finset (Interval m)) : ℝ :=
  ((∑ ℓ, ∑ r, aggM x ℓ r) + ∑ I ∈ U, imbalance x I) / (m : ℝ) ^ 2

lemma uvec_smul_add {m : ℕ} (a b : ℝ) (x y : Fin m → Fin m → Fin m → ℝ) (U : Finset (Interval m)) :
    uvec (a • x + b • y) U = a * uvec x U + b * uvec y U := by
  have e : ∀ I, imbalance (a • x + b • y) I = a * imbalance x I + b * imbalance y I := by
    intro I; simp only [imbalance, aggM_smul_add]; ring
  simp only [uvec, e, aggM_smul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

lemma minimaxObjective_eq_uvec {m : ℕ} (x : Fin m → Fin m → Fin m → ℝ) :
    ∃ U : Finset (Interval m), IsUpClosed U ∧ minimaxObjective x = uvec x U := by
  obtain ⟨U, hU, he⟩ := sigma_attained (imbalance x)
  exact ⟨U, hU, by simp only [minimaxObjective, uvec, he]⟩

lemma uvec_le_minimax {m : ℕ} (x : Fin m → Fin m → Fin m → ℝ) (U : Finset (Interval m))
    (hU : IsUpClosed U) : uvec x U ≤ minimaxObjective x := by
  unfold uvec minimaxObjective
  have := sigma_ge (imbalance x) U hU
  gcongr

lemma minimax_sep {m : ℕ} (hm : 1 ≤ m) (w : ℝ)
    (hw : ∀ x ∈ {x : Fin m → Fin m → Fin m → ℝ | InCcap x}, w ≤ minimaxObjective x) :
    ∃ h : Interval m → ℝ, InOrderPolytope h ∧
      ∀ x ∈ {x : Fin m → Fin m → Fin m → ℝ | InCcap x},
        w ≤ ((∑ ℓ, ∑ r, aggM x ℓ r) + ∑ I, h I * imbalance x I) / (m : ℝ) ^ 2 := by
  classical
  let ι := {U : Finset (Interval m) // IsUpClosed U}
  let u : (Fin m → Fin m → Fin m → ℝ) → (ι → ℝ) := fun x U => uvec x U.1
  let T : Set (ι → ℝ) := {z | ∃ x ∈ {x : Fin m → Fin m → Fin m → ℝ | InCcap x}, ∀ U, u x U ≤ z U}
  let O : Set (ι → ℝ) := {z | ∀ U, z U < w}
  have hTc : Convex ℝ T := by
    rintro z ⟨x, hx, hxz⟩ z' ⟨y, hy, hyz⟩ a b ha hb hab
    refine ⟨a • x + b • y, convex_Ccap m hx hy ha hb hab, fun U => ?_⟩
    simp only [u, uvec_smul_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := hxz U
    have h2 := hyz U
    simp only [u] at h1 h2
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
  have hOo : IsOpen O := by
    have : O = ⋂ U : ι, (fun z : ι → ℝ => z U) ⁻¹' Set.Iio w := by
      ext z; simp [O]
    rw [this]
    exact isOpen_iInter_of_finite fun U => isOpen_Iio.preimage (continuous_apply U)
  have hOc : Convex ℝ O := by
    intro z hz z' hz' a b ha hb hab U
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := hz U
    have h2 := hz' U
    rcases ha.eq_or_lt with h | h
    · subst h
      have : b = 1 := by linarith
      subst this; simpa using h2
    · have k1 := mul_lt_mul_of_pos_left h1 h
      have k2 := mul_le_mul_of_nonneg_left h2.le hb
      have k3 : a * w + b * w = w := by rw [← add_mul, hab, one_mul]
      linarith
  have hdisj : Disjoint O T := by
    rw [Set.disjoint_left]
    rintro z hz ⟨x, hx, hxz⟩
    obtain ⟨U, hU, he⟩ := minimaxObjective_eq_uvec x
    have := hw x hx
    have h1 := hxz ⟨U, hU⟩
    have h2 := hz ⟨U, hU⟩
    simp only [u] at h1
    linarith
  obtain ⟨f, s, hfO, hfT⟩ := geometric_hahn_banach_open hOc hOo hTc hdisj
  obtain ⟨x0, hx0⟩ := Ccap_nonempty hm
  let lam : ι → ℝ := fun U => f (fun j => if U = j then 1 else 0)
  have hf : ∀ z : ι → ℝ, f z = ∑ U, lam U * z U := by
    intro z
    have := LinearMap.pi_apply_eq_sum_univ (f : (ι → ℝ) →ₗ[ℝ] ℝ) z
    simpa [lam, mul_comm] using this
  have hz0 : u x0 ∈ T := ⟨x0, hx0, fun U => le_rfl⟩
  have hs0 : s ≤ f (u x0) := hfT _ hz0
  have hlam : ∀ U, 0 ≤ lam U := by
    intro U0
    by_contra hneg
    push_neg at hneg
    set t : ℝ := (f (u x0) - s + 1) / (-lam U0) with ht
    have ht0 : 0 ≤ t := by
      rw [ht]; apply div_nonneg <;> linarith
    have hmem : (u x0 + t • (fun j => if U0 = j then (1:ℝ) else 0)) ∈ T := by
      refine ⟨x0, hx0, fun U => ?_⟩
      by_cases h : U0 = U <;> simp [h, ht0]
    have h1 := hfT _ hmem
    rw [map_add, map_smul, smul_eq_mul] at h1
    have h2 : t * lam U0 = -(f (u x0) - s + 1) := by
      have hne : -lam U0 ≠ 0 := by linarith
      have := div_mul_cancel₀ (f (u x0) - s + 1) hne
      rw [ht]; linarith
    have : lam U0 = f (fun j => if U0 = j then 1 else 0) := rfl
    linarith
  have hLam : 0 < ∑ U, lam U := by
    by_contra hnp
    push_neg at hnp
    have hz : ∀ U, lam U = 0 := fun U =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun U _ => hlam U)).1
        (le_antisymm hnp (Finset.sum_nonneg fun U _ => hlam U)) U (Finset.mem_univ U)
    have f0 : ∀ z, f z = 0 := fun z => by rw [hf]; simp [hz]
    have h1 := hfO (fun _ => w - 1) (fun U => by simp)
    rw [f0] at h1
    have h2 := hs0
    rw [f0] at h2
    linarith
  set Λ : ℝ := ∑ U, lam U with hΛ
  have hΛw : Λ * w ≤ s := by
    by_contra hlt
    push_neg at hlt
    have hε : 0 < (Λ * w - s) / (2 * Λ) := div_pos (by linarith) (by linarith)
    have h1 := hfO (fun _ => w - (Λ * w - s) / (2 * Λ)) (fun U => by simp only; linarith)
    rw [hf, ← Finset.sum_mul] at h1
    have h2 : Λ * ((Λ * w - s) / (2 * Λ)) = (Λ * w - s) / 2 := by field_simp
    nlinarith
  have hbound : ∀ x ∈ {x : Fin m → Fin m → Fin m → ℝ | InCcap x},
      Λ * w ≤ ∑ U, lam U * u x U := by
    intro x hx
    have := hfT _ (⟨x, hx, fun U => le_rfl⟩ : u x ∈ T)
    rw [hf] at this
    linarith
  have hμ0 : ∀ U, 0 ≤ lam U / Λ := fun U => div_nonneg (hlam U) hLam.le
  have hμ1 : ∑ U, lam U / Λ = 1 := by rw [← Finset.sum_div, div_self hLam.ne']
  have hind : ∀ (U : ι) (I : Interval m), (0:ℝ) ≤ (if I ∈ U.1 then 1 else 0) ∧
      (if I ∈ U.1 then (1:ℝ) else 0) ≤ 1 := by
    intro U I; by_cases h : I ∈ U.1 <;> simp [h]
  refine ⟨fun I => ∑ U : ι, (lam U / Λ) * (if I ∈ U.1 then 1 else 0), ⟨fun I => ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact Finset.sum_nonneg fun U _ => mul_nonneg (hμ0 U) (hind U I).1
  · calc _ ≤ ∑ U : ι, lam U / Λ * 1 :=
          Finset.sum_le_sum fun U _ => mul_le_mul_of_nonneg_left (hind U I).2 (hμ0 U)
      _ = 1 := by simp [hμ1]
  · intro I J hIJ
    refine Finset.sum_le_sum fun U _ => mul_le_mul_of_nonneg_left ?_ (hμ0 U)
    by_cases h : I ∈ U.1
    · simp [h, U.2 I J h hIJ]
    · simp only [h, if_false]; exact (hind U J).1
  · intro x hx
    have key : ((∑ ℓ, ∑ r, aggM x ℓ r) + ∑ I, (∑ U : ι, (lam U / Λ) * (if I ∈ U.1 then (1:ℝ) else 0)) *
        imbalance x I) / (m : ℝ) ^ 2 = ∑ U : ι, (lam U / Λ) * u x U := by
      have e1 : ∑ I, (∑ U : ι, (lam U / Λ) * (if I ∈ U.1 then (1:ℝ) else 0)) * imbalance x I =
          ∑ U : ι, (lam U / Λ) * ∑ I ∈ U.1, imbalance x I := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun U _ => ?_
        rw [Finset.mul_sum]
        calc _ = ∑ I, if I ∈ U.1 then lam U / Λ * imbalance x I else 0 :=
              Finset.sum_congr rfl fun I _ => by by_cases h : I ∈ U.1 <;> simp [h]
          _ = _ := by rw [Finset.sum_ite_mem, Finset.univ_inter]
      rw [e1]
      simp only [u, uvec]
      have e2 : ∑ U : ι, lam U / Λ * (((∑ ℓ, ∑ r, aggM x ℓ r) + ∑ I ∈ U.1, imbalance x I) / (m : ℝ) ^ 2) =
          (∑ U : ι, (lam U / Λ * (∑ ℓ, ∑ r, aggM x ℓ r) + lam U / Λ * ∑ I ∈ U.1, imbalance x I)) /
            (m : ℝ) ^ 2 := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun U _ => by ring
      rw [e2, Finset.sum_add_distrib, ← Finset.sum_mul, hμ1]
      ring
    rw [key]
    have : Λ * w ≤ Λ * ∑ U : ι, (lam U / Λ) * u x U := by
      calc Λ * w ≤ ∑ U, lam U * u x U := hbound x hx
        _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun U _ => ?_
          field_simp
    exact le_of_mul_le_mul_left this hLam


lemma Phi_cont (m : ℕ) : Continuous (fun x : Fin m → Fin m → Fin m → ℝ => minimaxObjective x) := by
  classical
  have hagg : ∀ ℓ r : Fin m, Continuous (fun x : Fin m → Fin m → Fin m → ℝ => aggM x ℓ r) := by
    intro ℓ r
    unfold aggM rowMass
    refine continuous_const.mul (continuous_finsetSum _ fun p _ => ?_)
    exact (continuous_apply p).comp ((continuous_apply r).comp (continuous_apply ℓ))
  have himb : ∀ I : Interval m, Continuous (fun x : Fin m → Fin m → Fin m → ℝ => imbalance x I) :=
    fun I => (hagg _ _).sub (hagg _ _)
  have hsig : Continuous (fun x : Fin m → Fin m → Fin m → ℝ => sigma (imbalance x)) := by
    unfold sigma
    refine continuous_iff_continuousAt.2 fun x => ?_
    refine ContinuousAt.finset_sup'_apply _ fun U _ => ?_
    exact (continuous_finsetSum _ fun I _ => himb I).continuousAt
  unfold minimaxObjective
  exact ((continuous_finsetSum _ fun ℓ _ => continuous_finsetSum _ fun r _ => hagg ℓ r).add hsig).div_const _

lemma priced_le_Phi {m : ℕ} (hm : 1 ≤ m) {F : Fin m → Fin m → ℝ} (hF : InA F)
    (x : Fin m → Fin m → Fin m → ℝ) : pricedObjective F x ≤ minimaxObjective x := by
  rw [priced_eq hm F hF.1 x]
  have := layer_cake (intervalCoords F) (imbalance x) (intervalCoords_mem hF)
  unfold minimaxObjective
  gcongr

theorem lemma_B_5 (m : ℕ) (hm : 1 ≤ m) :
    Set.BijOn (intervalCoords (m := m)) {F | InA F} {h | InOrderPolytope h} ∧
    ∃ v : ℝ, IsGreatest (Rm '' {F : Fin m → Fin m → ℝ | InA F}) (v : EReal) ∧
      IsLeast (minimaxObjective '' {x : Fin m → Fin m → Fin m → ℝ | InCcap x}) v := by
  refine ⟨part1 m, ?_⟩
  have hB4 := (lemma_B_4 m hm).2.2
  obtain ⟨xs, hxs, hmin⟩ := (Ccap_compact m).exists_isMinOn (Ccap_nonempty hm)
    (Phi_cont m).continuousOn
  have hmin' : ∀ x ∈ {x : Fin m → Fin m → Fin m → ℝ | InCcap x},
      minimaxObjective xs ≤ minimaxObjective x := fun x hx => hmin hx
  obtain ⟨h, hh, hbd⟩ := minimax_sep hm _ hmin'
  have hF0 := tableOf_InA h hh
  have hcoord := intervalCoords_tableOf h
  have hRle : ∀ F : Fin m → Fin m → ℝ, InA F → Rm F ≤ ((minimaxObjective xs : ℝ) : EReal) := by
    intro F hF
    have hnn : ∀ ℓ r, 0 ≤ F ℓ r := fun ℓ r => (hF.2.1 ℓ r).1
    rw [← hB4 F hnn]
    refine le_trans (iInf₂_le xs hxs) ?_
    exact EReal.coe_le_coe_iff.2 (priced_le_Phi hm hF xs)
  refine ⟨minimaxObjective xs, ⟨⟨tableOf h, hF0, ?_⟩, ?_⟩, ⟨⟨xs, hxs, rfl⟩, ?_⟩⟩
  · refine le_antisymm (hRle _ hF0) ?_
    rw [← hB4 _ (fun ℓ r => (hF0.2.1 ℓ r).1)]
    refine le_iInf₂ fun x hx => EReal.coe_le_coe_iff.2 ?_
    rw [priced_eq hm _ hF0.1, hcoord]
    exact hbd x hx
  · rintro _ ⟨F, hF, rfl⟩
    exact hRle F hF
  · rintro _ ⟨x, hx, rfl⟩
    exact hmin' x hx

end HarmonicRanking.Main.Supplement

theorem solution (m : ℕ) (hm : 1 ≤ m) :
    Set.BijOn (HarmonicRanking.Main.Supplement.intervalCoords (m := m))
      {F | HarmonicRanking.Main.Supplement.InA F} {h | HarmonicRanking.Main.Supplement.InOrderPolytope h} ∧
    ∃ v : ℝ, IsGreatest (HarmonicRanking.Main.Supplement.Rm '' {F : Fin m → Fin m → ℝ | HarmonicRanking.Main.Supplement.InA F}) (v : EReal) ∧
      IsLeast (HarmonicRanking.Main.Supplement.minimaxObjective '' {x : Fin m → Fin m → Fin m → ℝ | HarmonicRanking.Main.Supplement.InCcap x}) v :=
  HarmonicRanking.Main.Supplement.lemma_B_5 m hm
