-- Prove2me | solution 1 for JMMS.exists_isMinimal_subshift_mulEquiv_IETOn_and_complexity_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T15:31:47.413887+00:00
-- url     : https://prove2.me/submissions/87d3b98c-3428-4169-a61f-2441f300c2af

import Mathlib
import Definitions.Def_CantorSystems
import Theorems.Thm_JMMS_mem_IET_iff

section

open CantorSystems IntervalExchange
open Filter Topology Set

namespace JMMS
namespace IETP511

/-! ## Positions on the circle -/

/-- The position of `z` in `[0, 1)`. -/
noncomputable def fr (z : UnitAddCircle) : ℝ := (AddCircle.equivIco (1:ℝ) 0 z : ℝ)

lemma fr_coe (x : ℝ) : fr (x : UnitAddCircle) = Int.fract x := by
  rw [fr, AddCircle.equivIco]; simp [toIcoMod_zero_one]

lemma coe_fr (z : UnitAddCircle) : ((fr z : ℝ) : UnitAddCircle) = z := AddCircle.coe_equivIco

lemma fr_nonneg (z : UnitAddCircle) : 0 ≤ fr z := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  have := fr_coe x
  simp only [QuotientAddGroup.mk] at this ⊢
  rw [this]; exact Int.fract_nonneg _

lemma fr_lt_one (z : UnitAddCircle) : fr z < 1 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  have := fr_coe x
  simp only [QuotientAddGroup.mk] at this ⊢
  rw [this]; exact Int.fract_lt_one _

lemma fr_coe_of {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) : fr (x : UnitAddCircle) = x := by
  rw [fr_coe, Int.fract_eq_self.2 ⟨h0, h1⟩]

lemma fr_zero : fr 0 = 0 := by
  have := fr_coe_of (x := 0) le_rfl one_pos
  simpa using this

lemma fr_eq_zero_iff (z : UnitAddCircle) : fr z = 0 ↔ z = 0 := by
  constructor
  · intro h; rw [← coe_fr z, h]; simp
  · rintro rfl; exact fr_zero

lemma fr_add_coe (z : UnitAddCircle) (t : ℝ) (h0 : 0 ≤ fr z + t) (h1 : fr z + t < 1) :
    fr (z + t) = fr z + t := by
  have : z + (t : UnitAddCircle) = ((fr z + t : ℝ) : UnitAddCircle) := by
    rw [AddCircle.coe_add, coe_fr]
  rw [this, fr_coe_of h0 h1]

lemma fr_add (z w : UnitAddCircle) : fr (z + w) = Int.fract (fr z + fr w) := by
  have : z + w = ((fr z + fr w : ℝ) : UnitAddCircle) := by
    rw [AddCircle.coe_add, coe_fr, coe_fr]
  rw [this, fr_coe]

lemma fr_neg_of_ne {z : UnitAddCircle} (hz : z ≠ 0) : fr (-z) = 1 - fr z := by
  have h0 : fr z ≠ 0 := fun h => hz ((fr_eq_zero_iff z).1 h)
  have hpos : 0 < fr z := lt_of_le_of_ne (fr_nonneg z) (Ne.symm h0)
  have : -z = ((1 - fr z : ℝ) : UnitAddCircle) := by
    rw [AddCircle.coe_sub, coe_fr]
    have : ((1:ℝ) : UnitAddCircle) = 0 := AddCircle.coe_period (1:ℝ)
    rw [this, zero_sub]
  rw [this, fr_coe_of (by linarith [fr_lt_one z]) (by linarith)]

lemma contMk : Continuous (fun t : ℝ => (t : UnitAddCircle)) := continuous_quotient_mk'

lemma nhds_circle (z : UnitAddCircle) :
    𝓝 z = Filter.map (fun t : ℝ => z + (t : UnitAddCircle)) (𝓝 0) := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [QuotientAddGroup.nhds_eq]
  have : 𝓝 a = Filter.map (fun t : ℝ => a + t) (𝓝 0) := by
    have h := (Homeomorph.addLeft a).map_nhds_eq 0
    simp only [Homeomorph.coe_addLeft, add_zero] at h
    exact h.symm
  rw [this, Filter.map_map]
  rfl

lemma coe_ne_zero_of {t : ℝ} (h0 : 0 < |t|) (h1 : |t| < 1) : (t : UnitAddCircle) ≠ 0 := by
  intro h
  have := fr_coe t
  rw [h, fr_zero] at this
  have h2 := (Int.fract_eq_zero_iff (a := t)).not
  rcases abs_cases t with ⟨ht, _⟩ | ⟨ht, _⟩
  · rw [ht] at h0 h1
    have : Int.fract t = t := Int.fract_eq_self.2 ⟨h0.le, h1⟩
    linarith
  · rw [ht] at h0 h1
    have : Int.fract t = t + 1 := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩
    linarith

/-! ## Arcs -/

/-- `arc l true z`: `z ∈ [0, l)`; `arc l false z`: `z ∈ (0, l]`. -/
def arc (l : ℝ) (b : Bool) (z : UnitAddCircle) : Prop :=
  if b then fr z < l else z ≠ 0 ∧ fr z ≤ l

lemma arc_le {l : ℝ} {b : Bool} {z : UnitAddCircle} (h : arc l b z) : fr z ≤ l := by
  cases b
  · exact h.2
  · exact le_of_lt h

lemma arc_of_pos {l : ℝ} (b : Bool) {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < l) (hl : l < 1) :
    arc l b (ρ : UnitAddCircle) := by
  have hf : fr (ρ : UnitAddCircle) = ρ := fr_coe_of h0.le (by linarith)
  cases b
  · refine ⟨fun h => ?_, by rw [hf]; exact h1.le⟩
    rw [← fr_eq_zero_iff, hf] at h; linarith
  · show fr _ < l; rw [hf]; exact h1

lemma not_arc_of {l : ℝ} (b : Bool) {z : UnitAddCircle} (h : l < fr z) : ¬ arc l b z :=
  fun h' => absurd (arc_le h') (not_le.2 h)

lemma arc_true_zero {l : ℝ} (hl : 0 < l) : arc l true 0 := by
  show fr 0 < l; rw [fr_zero]; exact hl

lemma not_arc_false_zero {l : ℝ} : ¬ arc l false 0 := fun h => h.1 rfl

lemma arc_pos {l : ℝ} (hl1 : l < 1) (w : UnitAddCircle) (b : Bool) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, (arc l b (w + t) ↔ arc l true w) := by
  set r := fr w with hr
  have h0 := fr_nonneg w
  have h1 := fr_lt_one w
  have key : ∀ t : ℝ, 0 < t → t < 1 - r → fr (w + t) = r + t ∧ w + (t : UnitAddCircle) ≠ 0 := by
    intro t ht0 ht1
    have e := fr_add_coe w t (by linarith) (by linarith)
    refine ⟨e, fun h => ?_⟩
    rw [h, fr_zero] at e; linarith
  by_cases hrl : r < l
  · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < min (1 - r) (l - r) by
      simp only [lt_min_iff]; constructor <;> linarith)] with t ⟨ht0, ht1⟩
    have hm1 := min_le_left (1 - r) (l - r)
    have hm2 := min_le_right (1 - r) (l - r)
    obtain ⟨e, hne⟩ := key t ht0 (by linarith)
    have : arc l true w := hrl
    simp only [this, iff_true]
    cases b
    · exact ⟨hne, by rw [e]; linarith⟩
    · show fr _ < l; rw [e]; linarith
  · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 - r by linarith)] with t ⟨ht0, ht1⟩
    obtain ⟨e, -⟩ := key t ht0 ht1
    have : ¬ arc l true w := hrl
    simp only [this, iff_false]
    exact not_arc_of b (by rw [e]; push Not at hrl; linarith)

lemma arc_neg {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (w : UnitAddCircle) (b : Bool) :
    ∀ᶠ t : ℝ in 𝓝[<] 0, (arc l b (w + t) ↔ arc l false w) := by
  classical
  set r : ℝ := if w = 0 then 1 else fr w with hr
  have hr0 : 0 < r := by
    rw [hr]; split_ifs with h
    · exact one_pos
    · exact lt_of_le_of_ne (fr_nonneg w) (fun e => h ((fr_eq_zero_iff w).1 e.symm))
  have hr1 : r ≤ 1 := by
    rw [hr]; split_ifs
    · exact le_rfl
    · exact (fr_lt_one w).le
  have hwr : w = (r : UnitAddCircle) := by
    rw [hr]; split_ifs with h
    · rw [h]; exact (AddCircle.coe_period (1:ℝ)).symm
    · exact (coe_fr w).symm
  have harc : arc l false w ↔ r ≤ l := by
    rw [hr]; split_ifs with h
    · simp only [arc, h]; constructor
      · intro h'; exact absurd rfl h'.1
      · intro h'; linarith
    · simp only [arc, Bool.false_eq_true, if_false]
      exact ⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩
  have key : ∀ t : ℝ, -r < t → t < 0 → fr (w + t) = r + t ∧ w + (t : UnitAddCircle) ≠ 0 := by
    intro t ht0 ht1
    have e : fr (w + t) = r + t := by
      rw [hwr, ← AddCircle.coe_add, fr_coe_of (by linarith) (by linarith)]
    refine ⟨e, fun h => ?_⟩
    rw [h, fr_zero] at e; linarith
  by_cases hrl : r ≤ l
  · filter_upwards [Ioo_mem_nhdsLT (show -r < (0:ℝ) by linarith)] with t ⟨ht0, ht1⟩
    obtain ⟨e, hne⟩ := key t ht0 ht1
    simp only [harc.2 hrl, iff_true]
    cases b
    · exact ⟨hne, by rw [e]; linarith⟩
    · show fr _ < l; rw [e]; linarith
  · push Not at hrl
    filter_upwards [Ioo_mem_nhdsLT (show l - r < (0:ℝ) by linarith)] with t ⟨ht0, ht1⟩
    obtain ⟨e, -⟩ := key t (by linarith) ht1
    have : ¬ arc l false w := fun h => absurd (harc.1 h) (not_le.2 hrl)
    simp only [this, iff_false]
    exact not_arc_of b (by rw [e]; linarith)

/-! ## The hypotheses and the coding -/

/-- The standing hypotheses. -/
structure Hyp (Λ : AddSubgroup UnitAddCircle) (σ : Finset UnitAddCircle) (l : ℝ) : Prop where
  l0 : 0 < l
  l1 : l < 1 / 2
  lΛ : (l : UnitAddCircle) ∈ Λ
  den : ∀ (c : UnitAddCircle) (α β : ℝ), α < β → ∃ ρ ∈ Ioo α β, c + (ρ : UnitAddCircle) ∈ Λ
  ne : σ.Nonempty

/-- The alphabet size. -/
noncomputable abbrev K (σ : Finset UnitAddCircle) : ℕ := Fintype.card (σ → Bool)

/-- Encoding of letters. -/
noncomputable def enc (σ : Finset UnitAddCircle) : (σ → Bool) ≃ Fin (K σ) := Fintype.equivFin _

/-- The letter of a point. -/
noncomputable def letter (σ : Finset UnitAddCircle) (l : ℝ) (b : Bool) (z : UnitAddCircle) :
    σ → Bool := fun s => by classical exact decide (arc l b (z - s))

/-- The right (`b = true`) and left (`b = false`) codings. -/
noncomputable def code (Λ : AddSubgroup UnitAddCircle) (σ : Finset UnitAddCircle) (l : ℝ)
    (b : Bool) (y : UnitAddCircle) : Λ → Fin (K σ) :=
  fun δ => enc σ (letter σ l b (y + δ))

variable {Λ : AddSubgroup UnitAddCircle} {σ : Finset UnitAddCircle} {l : ℝ}

lemma letter_eq_iff {b b' : Bool} {z z' : UnitAddCircle} :
    letter σ l b z = letter σ l b' z' ↔ ∀ s ∈ σ, (arc l b (z - s) ↔ arc l b' (z' - s)) := by
  classical
  constructor
  · intro h s hs
    have := congrFun h ⟨s, hs⟩
    simp only [letter, decide_eq_decide] at this
    exact this
  · intro h
    funext s
    simp only [letter, decide_eq_decide]
    exact h s s.2

lemma code_eq_iff {b b' : Bool} {y y' : UnitAddCircle} {δ : Λ} :
    code Λ σ l b y δ = code Λ σ l b' y' δ ↔
      ∀ s ∈ σ, (arc l b (y + δ - s) ↔ arc l b' (y' + δ - s)) := by
  rw [code, code, (enc σ).apply_eq_iff_eq, letter_eq_iff]

lemma shift_code (b : Bool) (y : UnitAddCircle) (γ : Λ) :
    shift γ (code Λ σ l b y) = code Λ σ l b (y + γ) := by
  funext δ
  simp only [shift_apply, code, AddSubgroup.coe_add]
  congr 2
  abel

/-- The density of `Λ`. -/
lemma dense_of_infinite (Λ : AddSubgroup UnitAddCircle) (hΛ : (Λ : Set UnitAddCircle).Infinite) :
    ∀ (c : UnitAddCircle) (α β : ℝ), α < β → ∃ ρ ∈ Ioo α β, c + (ρ : UnitAddCircle) ∈ Λ := by
  have hd : Dense (Λ : Set UnitAddCircle) := by
    rw [AddCircle.dense_addSubgroup_iff_ne_zmultiples]
    rintro a ha rfl
    have : IsOfFinAddOrder a := by
      by_contra h; exact ha (addOrderOf_eq_zero_iff.2 h)
    exact hΛ (finite_zmultiples.2 this)
  intro c α β hαβ
  have hU : IsOpen ((fun ρ : ℝ => c + (ρ : UnitAddCircle)) '' Ioo α β) := by
    have h1 : IsOpenMap (fun ρ : ℝ => (ρ : UnitAddCircle)) := QuotientAddGroup.isOpenMap_coe
    have h2 : IsOpenMap (fun z : UnitAddCircle => c + z) := (Homeomorph.addLeft c).isOpenMap
    exact (h2.comp h1) _ isOpen_Ioo
  obtain ⟨_, ⟨ρ, hρ, rfl⟩, hmem⟩ := hd.inter_open_nonempty _ hU
    ⟨_, ⟨(α + β) / 2, ⟨by linarith, by linarith⟩, rfl⟩⟩
  exact ⟨ρ, hρ, hmem⟩


/-! ## Separation -/

lemma code_true_eq_false (H : Hyp Λ σ l) {y : UnitAddCircle} (hy : y ∉ cosetsOf Λ σ) :
    code Λ σ l true y = code Λ σ l false y := by
  funext δ
  rw [code_eq_iff]
  intro s hs
  set z := y + (δ : UnitAddCircle) - s with hz
  have hz0 : z ≠ 0 := by
    intro h
    apply hy
    refine ⟨s, hs, ?_⟩
    have : y - s = z - δ := by rw [hz]; abel
    rw [this, h, zero_sub]
    exact Λ.neg_mem δ.2
  by_cases hl : fr z = l
  · exfalso
    apply hy
    refine ⟨s, hs, ?_⟩
    have h1 : z = (l : UnitAddCircle) := by rw [← hl, coe_fr]
    have : y - s = z - δ := by rw [hz]; abel
    rw [this, h1]
    exact Λ.sub_mem H.lΛ δ.2
  · simp only [arc, if_true, Bool.false_eq_true, if_false]
    constructor
    · intro h; exact ⟨hz0, h.le⟩
    · rintro ⟨-, h⟩; exact lt_of_le_of_ne h hl

lemma code_true_ne_false (H : Hyp Λ σ l) {y : UnitAddCircle} (hy : y ∈ cosetsOf Λ σ) :
    code Λ σ l true y ≠ code Λ σ l false y := by
  obtain ⟨s, hs, hys⟩ := hy
  intro h
  have hδ : s - y ∈ Λ := by
    have := Λ.neg_mem hys; rwa [neg_sub] at this
  have := (code_eq_iff.1 (congrFun h ⟨s - y, hδ⟩)) s hs
  have e : y + ((⟨s - y, hδ⟩ : Λ) : UnitAddCircle) - s = 0 := by simp
  rw [e] at this
  exact not_arc_false_zero (this.1 (arc_true_zero H.l0))

lemma sep_aux (H : Hyp Λ σ l) {y y' : UnitAddCircle} (hd : l < fr (y' - y)) (b b' : Bool) :
    code Λ σ l b y ≠ code Λ σ l b' y' := by
  obtain ⟨s₀, hs₀⟩ := H.ne
  have hd1 := fr_lt_one (y' - y)
  obtain ⟨ρ, ⟨hρ0, hρ1⟩, hρΛ⟩ := H.den (s₀ - y) 0 (min l (1 - fr (y' - y)))
    (lt_min H.l0 (by linarith))
  have hρl := lt_of_lt_of_le hρ1 (min_le_left _ _)
  have hρd := lt_of_lt_of_le hρ1 (min_le_right _ _)
  intro h
  have := (code_eq_iff.1 (congrFun h ⟨_, hρΛ⟩)) s₀ hs₀
  have e1 : y + ((⟨_, hρΛ⟩ : Λ) : UnitAddCircle) - s₀ = (ρ : UnitAddCircle) := by
    simp only; abel
  have e2 : y' + ((⟨_, hρΛ⟩ : Λ) : UnitAddCircle) - s₀ = (y' - y) + (ρ : UnitAddCircle) := by
    simp only; abel
  rw [e1, e2] at this
  have ha := this.1 (arc_of_pos b hρ0 hρl (by linarith [H.l1]))
  have hf := fr_add_coe (y' - y) ρ (by linarith [fr_nonneg (y' - y)]) (by linarith)
  exact not_arc_of b' (by rw [hf]; linarith) ha

lemma sep (H : Hyp Λ σ l) {y y' : UnitAddCircle} {b b' : Bool}
    (h : code Λ σ l b y = code Λ σ l b' y') : y = y' := by
  by_contra hne
  have hd0 : y' - y ≠ 0 := fun e => hne (sub_eq_zero.1 e).symm
  by_cases hd : l < fr (y' - y)
  · exact sep_aux H hd b b' h
  · push Not at hd
    have e : y - y' = -(y' - y) := by abel
    have hd' : l < fr (y - y') := by
      rw [e, fr_neg_of_ne hd0]; linarith [H.l1]
    exact sep_aux H hd' b' b h.symm

/-! ## One-sided limits -/

lemma tendsto_pos (H : Hyp Λ σ l) (y : UnitAddCircle) (b : Bool) :
    Tendsto (fun t : ℝ => code Λ σ l b (y + t)) (𝓝[>] 0) (𝓝 (code Λ σ l true y)) := by
  rw [tendsto_pi_nhds]
  intro δ
  rw [nhds_discrete, tendsto_pure]
  have : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ s ∈ σ,
      (arc l b (y + t + δ - s) ↔ arc l true (y + δ - s)) := by
    rw [Filter.eventually_all_finset]
    intro s hs
    filter_upwards [arc_pos (by linarith [H.l1]) (y + δ - s) b] with t ht
    have e : y + (t : UnitAddCircle) + δ - s = (y + δ - s) + t := by abel
    rw [e]; exact ht
  filter_upwards [this] with t ht
  exact code_eq_iff.2 ht

lemma tendsto_neg (H : Hyp Λ σ l) (y : UnitAddCircle) (b : Bool) :
    Tendsto (fun t : ℝ => code Λ σ l b (y + t)) (𝓝[<] 0) (𝓝 (code Λ σ l false y)) := by
  rw [tendsto_pi_nhds]
  intro δ
  rw [nhds_discrete, tendsto_pure]
  have : ∀ᶠ t : ℝ in 𝓝[<] 0, ∀ s ∈ σ,
      (arc l b (y + t + δ - s) ↔ arc l false (y + δ - s)) := by
    rw [Filter.eventually_all_finset]
    intro s hs
    filter_upwards [arc_neg H.l0 (by linarith [H.l1]) (y + δ - s) b] with t ht
    have e : y + (t : UnitAddCircle) + δ - s = (y + δ - s) + t := by abel
    rw [e]; exact ht
  filter_upwards [this] with t ht
  exact code_eq_iff.2 ht

/-- The carrier of the subshift. -/
def Scar (Λ : AddSubgroup UnitAddCircle) (σ : Finset UnitAddCircle) (l : ℝ) :
    Set (Λ → Fin (K σ)) :=
  closure (range (code Λ σ l true))

lemma code_mem (H : Hyp Λ σ l) (b : Bool) (y : UnitAddCircle) : code Λ σ l b y ∈ Scar Λ σ l := by
  cases b
  · refine mem_closure_of_tendsto (tendsto_neg H y true) ?_
    exact Filter.Eventually.of_forall fun t => ⟨_, rfl⟩
  · exact subset_closure ⟨y, rfl⟩

lemma nhds_zero_eq : 𝓝 (0:ℝ) = (𝓝[<] 0 ⊔ 𝓝[>] 0) ⊔ pure 0 := by
  rw [nhdsLT_sup_nhdsGT, nhdsNE_sup_pure]

lemma eq_code_of_mem (H : Hyp Λ σ l) {x : Λ → Fin (K σ)} (hx : x ∈ Scar Λ σ l) :
    ∃ y b, x = code Λ σ l b y := by
  set F := comap (code Λ σ l true) (𝓝 x) with hF
  have hne : F.NeBot := by
    rw [comap_neBot_iff]
    intro t ht
    obtain ⟨_, hz, ⟨y, rfl⟩⟩ := mem_closure_iff_nhds.1 hx t ht
    exact ⟨y, hz⟩
  obtain ⟨y, hy⟩ := exists_clusterPt_of_compactSpace F
  have hy' : (𝓝 y ⊓ F).NeBot := hy
  rw [nhds_circle, nhds_zero_eq, Filter.map_sup, Filter.map_sup, inf_sup_right, inf_sup_right,
    sup_neBot, sup_neBot] at hy'
  have key : ∀ (G : Filter UnitAddCircle) (c : Λ → Fin (K σ)), (G ⊓ F).NeBot →
      Tendsto (code Λ σ l true) G (𝓝 c) → x = c := by
    intro G c hG hT
    exact tendsto_nhds_unique (tendsto_comap.mono_left inf_le_right) (hT.mono_left inf_le_left)
  rcases hy' with (h | h) | h
  · exact ⟨y, false, key _ _ h (tendsto_map'_iff.2 (tendsto_neg H y true))⟩
  · exact ⟨y, true, key _ _ h (tendsto_map'_iff.2 (tendsto_pos H y true))⟩
  · refine ⟨y, true, key _ _ h ?_⟩
    rw [Filter.map_pure]
    simpa using (tendsto_pure_nhds (code Λ σ l true) y)

/-! ## Neighbourhoods of codes -/

lemma isOpen_coord (δ : Λ) (c : Fin (K σ)) : IsOpen {x : Λ → Fin (K σ) | x δ = c} := by
  have := (isOpen_discrete ({c} : Set (Fin (K σ)))).preimage
    (continuous_apply (A := fun _ : Λ => Fin (K σ)) δ)
  exact this

/-- The basic neighbourhood lemma: codes near `code b y` are codes of points near `y`, on the
correct side of `y` when `y ∈ Σ + Λ`. -/
lemma nbhd (H : Hyp Λ σ l) (y : UnitAddCircle) (b : Bool) {η : ℝ} (hη : 0 < η) :
    ∃ V ∈ 𝓝 (code Λ σ l b y), ∀ (w : UnitAddCircle) (b' : Bool), code Λ σ l b' w ∈ V →
      ∃ t : ℝ, |t| < η ∧ w = y + t ∧
        (y ∈ cosetsOf Λ σ → (b = true → 0 ≤ t ∧ (t = 0 → b' = true)) ∧
          (b = false → t ≤ 0 ∧ (t = 0 → b' = false))) := by
  obtain ⟨s₀, hs₀⟩ := H.ne
  have hl0 := H.l0
  have hl1 := H.l1
  set η' := min η l with hη'
  have hη'0 : 0 < η' := lt_min hη hl0
  have hη'η : η' ≤ η := min_le_left _ _
  have hη'l : η' ≤ l := min_le_right _ _
  obtain ⟨ρA, ⟨hA0, hA1⟩, hAΛ⟩ := H.den (s₀ - y) 0 η' hη'0
  obtain ⟨ρB, ⟨hB0, hB1⟩, hBΛ⟩ := H.den (s₀ - y) (l - η') l (by linarith)
  set δA : Λ := ⟨_, hAΛ⟩
  set δB : Λ := ⟨_, hBΛ⟩
  -- the two basic constraints
  have core : ∀ (w : UnitAddCircle) (b' : Bool), code Λ σ l b' w δA = code Λ σ l b y δA →
      code Λ σ l b' w δB = code Λ σ l b y δB →
      fr (w - y) < η' ∨ 1 - η' < fr (w - y) := by
    intro w b' hA hB
    have eA : ∀ v : UnitAddCircle, v + (δA : UnitAddCircle) - s₀ = (v - y) + (ρA : UnitAddCircle) := by
      intro v; simp only [δA]; abel
    have eB : ∀ v : UnitAddCircle, v + (δB : UnitAddCircle) - s₀ = (v - y) + (ρB : UnitAddCircle) := by
      intro v; simp only [δB]; abel
    have hA' := (code_eq_iff.1 hA) s₀ hs₀
    have hB' := (code_eq_iff.1 hB) s₀ hs₀
    rw [eA, eA, sub_self, zero_add] at hA'
    rw [eB, eB, sub_self, zero_add] at hB'
    have aA := arc_le (hA'.2 (arc_of_pos b hA0 (by linarith) (by linarith)))
    have aB := arc_le (hB'.2 (arc_of_pos b (by linarith) hB1 (by linarith)))
    set τ := fr (w - y)
    have hτ0 := fr_nonneg (w - y)
    have hτ1 := fr_lt_one (w - y)
    rw [fr_add, fr_coe_of hA0.le (by linarith)] at aA
    rw [fr_add, fr_coe_of (by linarith) (by linarith)] at aB
    by_cases hc : τ + ρA < 1
    · rw [Int.fract_eq_self.2 ⟨by linarith, hc⟩] at aA
      rw [Int.fract_eq_self.2 ⟨by linarith, by linarith⟩] at aB
      left; linarith
    · right; linarith
  have hw : ∀ w : UnitAddCircle, w = y + ((fr (w - y) : ℝ) : UnitAddCircle) := by
    intro w; rw [coe_fr]; abel
  have hw' : ∀ w : UnitAddCircle, w = y + ((fr (w - y) - 1 : ℝ) : UnitAddCircle) := by
    intro w
    rw [AddCircle.coe_sub, coe_fr, AddCircle.coe_period (1:ℝ)]; abel
  set V0 : Set (Λ → Fin (K σ)) :=
    {x | x δA = code Λ σ l b y δA} ∩ {x | x δB = code Λ σ l b y δB} with hV0
  have hV0o : IsOpen V0 := (isOpen_coord _ _).inter (isOpen_coord _ _)
  have hV0m : code Λ σ l b y ∈ V0 := ⟨rfl, rfl⟩
  by_cases hy : y ∈ cosetsOf Λ σ
  · obtain ⟨s₁, hs₁, hys⟩ := hy
    have hδC : s₁ - y ∈ Λ := by have := Λ.neg_mem hys; rwa [neg_sub] at this
    set δC : Λ := ⟨_, hδC⟩
    refine ⟨V0 ∩ {x | x δC = code Λ σ l b y δC},
      (hV0o.inter (isOpen_coord _ _)).mem_nhds ⟨hV0m, rfl⟩, ?_⟩
    rintro w b' ⟨⟨hA, hB⟩, hC⟩
    have hC' := (code_eq_iff.1 hC) s₁ hs₁
    have eC : ∀ v : UnitAddCircle, v + (δC : UnitAddCircle) - s₁ = v - y := by
      intro v; simp only [δC]; abel
    rw [eC, eC, sub_self] at hC'
    rcases core w b' hA hB with h | h
    · refine ⟨fr (w - y), ?_, hw w, fun _ => ⟨?_, ?_⟩⟩
      · rw [abs_of_nonneg (fr_nonneg _)]; linarith
      · rintro rfl
        refine ⟨fr_nonneg _, fun h0 => ?_⟩
        rw [fr_eq_zero_iff] at h0
        rw [h0] at hC'
        cases b'
        · exact absurd (hC'.2 (arc_true_zero hl0)) not_arc_false_zero
        · rfl
      · rintro rfl
        by_cases h0 : fr (w - y) = 0
        · refine ⟨h0.le, fun _ => ?_⟩
          rw [fr_eq_zero_iff] at h0
          rw [h0] at hC'
          cases b'
          · rfl
          · exact absurd (hC'.1 (arc_true_zero hl0)) not_arc_false_zero
        · exfalso
          have hpos : 0 < fr (w - y) := lt_of_le_of_ne (fr_nonneg _) (Ne.symm h0)
          have := arc_of_pos (l := l) b' hpos (by linarith) (by linarith)
          rw [coe_fr] at this
          exact not_arc_false_zero (hC'.1 this)
    · refine ⟨fr (w - y) - 1, ?_, hw' w, fun _ => ⟨?_, ?_⟩⟩
      · rw [abs_of_neg (by linarith [fr_lt_one (w - y)])]; linarith
      · rintro rfl
        exfalso
        have := arc_le (hC'.2 (arc_true_zero hl0))
        linarith
      · rintro rfl
        refine ⟨by linarith [fr_lt_one (w - y)], fun h0 => ?_⟩
        exfalso; linarith [fr_lt_one (w - y)]
  · refine ⟨V0, hV0o.mem_nhds hV0m, ?_⟩
    rintro w b' ⟨hA, hB⟩
    rcases core w b' hA hB with h | h
    · refine ⟨fr (w - y), ?_, hw w, fun h' => absurd h' hy⟩
      rw [abs_of_nonneg (fr_nonneg _)]; linarith
    · refine ⟨fr (w - y) - 1, ?_, hw' w, fun h' => absurd h' hy⟩
      rw [abs_of_neg (by linarith [fr_lt_one (w - y)])]; linarith

/-! ## The subshift -/

lemma isSubshift (_H : Hyp Λ σ l) : IsSubshift (Scar Λ σ l) := by
  refine ⟨isClosed_closure, fun γ x hx => ?_⟩
  have hc : Continuous (shift (A := Fin (K σ)) γ) :=
    continuous_pi fun δ => continuous_apply _
  have hm : MapsTo (shift γ) (range (code Λ σ l true)) (range (code Λ σ l true)) := by
    rintro _ ⟨y, rfl⟩; exact ⟨y + γ, (shift_code true y γ).symm⟩
  exact map_mem_closure hc hx hm

/-- The subshift. -/
def Sub (H : Hyp Λ σ l) : Subshift Λ (Fin (K σ)) := ⟨Scar Λ σ l, isSubshift H⟩

/-- The points of the subshift. -/
noncomputable def pt (H : Hyp Λ σ l) (b : Bool) (y : UnitAddCircle) : Sub H := ⟨code Λ σ l b y, code_mem H b y⟩

@[simp] lemma coe_pt (H : Hyp Λ σ l) (b : Bool) (y : UnitAddCircle) :
    ((pt H b y : Sub H) : Λ → Fin (K σ)) = code Λ σ l b y := rfl

lemma vadd_pt (H : Hyp Λ σ l) (b : Bool) (y : UnitAddCircle) (γ : Λ) :
    γ +ᵥ pt H b y = pt H b (y + γ) := by
  apply Subtype.ext
  rw [Subshift.coe_vadd]
  exact shift_code b y γ

lemma exists_pt (H : Hyp Λ σ l) (x : Sub H) : ∃ y b, x = pt H b y := by
  obtain ⟨y, b, h⟩ := eq_code_of_mem H x.2
  exact ⟨y, b, Subtype.ext h⟩

lemma pt_inj (H : Hyp Λ σ l) {b b' : Bool} {y y' : UnitAddCircle} (h : pt H b y = pt H b' y') :
    y = y' := sep H (congrArg Subtype.val h)

lemma pt_true_eq_false (H : Hyp Λ σ l) {y : UnitAddCircle} (hy : y ∉ cosetsOf Λ σ) :
    pt H true y = pt H false y := Subtype.ext (code_true_eq_false H hy)

lemma pt_true_ne_false (H : Hyp Λ σ l) {y : UnitAddCircle} (hy : y ∈ cosetsOf Λ σ) :
    pt H true y ≠ pt H false y := fun h => code_true_ne_false H hy (congrArg Subtype.val h)

lemma tendsto_pt_pos (H : Hyp Λ σ l) (y : UnitAddCircle) (b : Bool) :
    Tendsto (fun t : ℝ => pt H b (y + t)) (𝓝[>] 0) (𝓝 (pt H true y)) :=
  tendsto_subtype_rng.2 (tendsto_pos H y b)

lemma tendsto_pt_neg (H : Hyp Λ σ l) (y : UnitAddCircle) (b : Bool) :
    Tendsto (fun t : ℝ => pt H b (y + t)) (𝓝[<] 0) (𝓝 (pt H false y)) :=
  tendsto_subtype_rng.2 (tendsto_neg H y b)

lemma nhdsGE_zero_eq : 𝓝[≥] (0:ℝ) = pure 0 ⊔ 𝓝[>] 0 := by
  rw [← Set.Ioi_insert, nhdsWithin_insert]

lemma tendsto_pt_ge (H : Hyp Λ σ l) (y : UnitAddCircle) :
    Tendsto (fun t : ℝ => pt H true (y + t)) (𝓝[≥] 0) (𝓝 (pt H true y)) := by
  rw [nhdsGE_zero_eq, tendsto_sup]
  refine ⟨?_, tendsto_pt_pos H y true⟩
  rw [tendsto_pure_left]
  intro U hU
  simpa using mem_of_mem_nhds hU

lemma nbhdS (H : Hyp Λ σ l) (y : UnitAddCircle) (b : Bool) {η : ℝ} (hη : 0 < η) :
    ∃ V ∈ 𝓝 (pt H b y), ∀ (w : UnitAddCircle) (b' : Bool), pt H b' w ∈ V →
      ∃ t : ℝ, |t| < η ∧ w = y + t ∧
        (y ∈ cosetsOf Λ σ → (b = true → 0 ≤ t ∧ (t = 0 → b' = true)) ∧
          (b = false → t ≤ 0 ∧ (t = 0 → b' = false))) := by
  obtain ⟨V, hV, hVp⟩ := nbhd H y b hη
  exact ⟨Subtype.val ⁻¹' V, continuous_subtype_val.continuousAt.preimage_mem_nhds hV,
    fun w b' hw => hVp w b' hw⟩

/-- The projection to the circle. -/
noncomputable def proj (H : Hyp Λ σ l) (x : Sub H) : UnitAddCircle :=
  Classical.choose (exists_pt H x)

lemma proj_spec (H : Hyp Λ σ l) (x : Sub H) : ∃ b, x = pt H b (proj H x) :=
  Classical.choose_spec (exists_pt H x)

@[simp] lemma proj_pt (H : Hyp Λ σ l) (b : Bool) (y : UnitAddCircle) : proj H (pt H b y) = y := by
  obtain ⟨b', h⟩ := proj_spec H (pt H b y)
  exact (pt_inj H h).symm

lemma continuous_proj (H : Hyp Λ σ l) : Continuous (proj H) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨b, hx⟩ := proj_spec H x
  set y := proj H x
  rw [ContinuousAt, nhds_circle y, ((Metric.nhds_basis_ball (x := (0:ℝ))).map _).tendsto_right_iff]
  intro ε hε
  rw [hx]
  obtain ⟨V, hV, hVp⟩ := nbhdS H y b hε
  filter_upwards [hV] with x' hx'
  obtain ⟨w, b', rfl⟩ := exists_pt H x'
  obtain ⟨t, ht, rfl, -⟩ := hVp w b' hx'
  refine ⟨t, ?_, by rw [proj_pt]⟩
  simpa [Real.dist_eq] using ht

lemma surjective_proj (H : Hyp Λ σ l) : Function.Surjective (proj H) :=
  fun y => ⟨pt H true y, proj_pt H true y⟩

lemma compactSpace_Sub (H : Hyp Λ σ l) : CompactSpace (Sub H) :=
  isCompact_iff_compactSpace.1 ((Sub H).isSubshift.1.isCompact)

lemma isMinimal_Sub (H : Hyp Λ σ l) : AddAction.IsMinimal Λ (Sub H) := by
  constructor
  intro x x'
  obtain ⟨y, b, rfl⟩ := exists_pt H x
  obtain ⟨y', b', rfl⟩ := exists_pt H x'
  have hmem : ∀ t : ℝ, y' + (t : UnitAddCircle) - y ∈ Λ →
      pt H b (y' + t) ∈ AddAction.orbit Λ (pt H b y) := by
    intro t ht
    refine ⟨⟨_, ht⟩, ?_⟩
    show (⟨_, ht⟩ : Λ) +ᵥ pt H b y = _
    rw [vadd_pt]
    congr 1
    simp
  cases b'
  · set L := 𝓝[<] (0:ℝ) ⊓ 𝓟 {t : ℝ | y' + (t : UnitAddCircle) - y ∈ Λ}
    have hL : L.NeBot := by
      rw [← frequently_iff_neBot, (nhdsLT_basis (0:ℝ)).frequently_iff]
      intro ε hε
      obtain ⟨ρ, hρ, hρΛ⟩ := H.den (y' - y) ε 0 hε
      exact ⟨ρ, hρ, by rw [show y' + (ρ : UnitAddCircle) - y = y' - y + ρ by abel]; exact hρΛ⟩
    have hT : Tendsto (fun t : ℝ => pt H b (y' + t)) L (𝓝 _) :=
      (tendsto_pt_neg H y' b).mono_left inf_le_left
    have := hL
    refine mem_closure_of_tendsto hT ?_
    filter_upwards [mem_inf_of_right (mem_principal_self _)] with t ht
    exact hmem t ht
  · set L := 𝓝[>] (0:ℝ) ⊓ 𝓟 {t : ℝ | y' + (t : UnitAddCircle) - y ∈ Λ}
    have hL : L.NeBot := by
      rw [← frequently_iff_neBot, (nhdsGT_basis (0:ℝ)).frequently_iff]
      intro ε hε
      obtain ⟨ρ, hρ, hρΛ⟩ := H.den (y' - y) 0 ε hε
      exact ⟨ρ, hρ, by rw [show y' + (ρ : UnitAddCircle) - y = y' - y + ρ by abel]; exact hρΛ⟩
    have hT : Tendsto (fun t : ℝ => pt H b (y' + t)) L (𝓝 _) :=
      (tendsto_pt_pos H y' b).mono_left inf_le_left
    have := hL
    refine mem_closure_of_tendsto hT ?_
    filter_upwards [mem_inf_of_right (mem_principal_self _)] with t ht
    exact hmem t ht

lemma isCantorSpace_Sub (H : Hyp Λ σ l) [Countable Λ] : IsCantorSpace (Sub H) := by
  have hm : TopologicalSpace.MetrizableSpace (Scar Λ σ l) := inferInstance
  have ht : TotallyDisconnectedSpace (Scar Λ σ l) := inferInstance
  refine ⟨⟨pt H true 0⟩, compactSpace_Sub H, hm, ht, ?_⟩
  intro x hx
  obtain ⟨y, b, rfl⟩ := exists_pt H x
  cases b
  · have h1 : ∀ᶠ t : ℝ in _, pt H false (y + t) ∈ ({pt H false y} : Set (Sub H)) :=
      (tendsto_pt_neg H y false).eventually_mem (hx.mem_nhds rfl)
    have h2 : ∀ᶠ t : ℝ in 𝓝[<] 0, t ∈ Ioo (-1:ℝ) 0 := Ioo_mem_nhdsLT (by norm_num)
    obtain ⟨t, ht1, ⟨ht2, ht3⟩⟩ := (h1.and h2).exists
    have e := pt_inj H (Set.mem_singleton_iff.1 ht1)
    have : (t : UnitAddCircle) = 0 := by
      have := congrArg (fun z => z - y) e; simpa using this
    exact coe_ne_zero_of (by rw [abs_pos]; linarith) (by rw [abs_lt]; constructor <;> linarith) this
  · have h1 : ∀ᶠ t : ℝ in _, pt H true (y + t) ∈ ({pt H true y} : Set (Sub H)) :=
      (tendsto_pt_pos H y true).eventually_mem (hx.mem_nhds rfl)
    have h2 : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioo (0:ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
    obtain ⟨t, ht1, ⟨ht2, ht3⟩⟩ := (h1.and h2).exists
    have e := pt_inj H (Set.mem_singleton_iff.1 ht1)
    have : (t : UnitAddCircle) = 0 := by
      have := congrArg (fun z => z - y) e; simpa using this
    exact coe_ne_zero_of (by rw [abs_pos]; linarith) (by rw [abs_lt]; constructor <;> linarith) this

/-! ## The topological full group acts on the circle -/

lemma vadd_continuous (H : Hyp Λ σ l) (γ : Λ) : Continuous (fun y : Sub H => γ +ᵥ y) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun δ => (continuous_apply (δ + γ)).comp continuous_subtype_val

lemma free (H : Hyp Λ σ l) {γ γ' : Λ} {x : Sub H} (h : γ +ᵥ x = γ' +ᵥ x) : γ = γ' := by
  obtain ⟨y, b, rfl⟩ := exists_pt H x
  rw [vadd_pt, vadd_pt] at h
  exact Subtype.ext (add_left_cancel (pt_inj H h))

lemma exists_ang (H : Hyp Λ σ l) (g : topologicalFullGroup Λ (Sub H)) (x : Sub H) :
    ∃ γ : Λ, (g : Sub H ≃ₜ Sub H) x = γ +ᵥ x := by
  obtain ⟨U, hU, γ, hγ⟩ := g.2 x
  exact ⟨γ, hγ x (mem_of_mem_nhds hU)⟩

/-- The local translation amount of an element of the full group. -/
noncomputable def ang (H : Hyp Λ σ l) (g : topologicalFullGroup Λ (Sub H)) (x : Sub H) : Λ :=
  Classical.choose (exists_ang H g x)

lemma ang_spec (H : Hyp Λ σ l) (g : topologicalFullGroup Λ (Sub H)) (x : Sub H) :
    (g : Sub H ≃ₜ Sub H) x = ang H g x +ᵥ x :=
  Classical.choose_spec (exists_ang H g x)

lemma ang_eventually (H : Hyp Λ σ l) (g : topologicalFullGroup Λ (Sub H)) (x : Sub H) :
    ∀ᶠ x' in 𝓝 x, ang H g x' = ang H g x := by
  obtain ⟨U, hU, γ, hγ⟩ := g.2 x
  have hx : ang H g x = γ := free H ((ang_spec H g x).symm.trans (hγ x (mem_of_mem_nhds hU)))
  filter_upwards [hU] with x' hx'
  rw [hx]; exact free H ((ang_spec H g x').symm.trans (hγ x' hx'))

lemma isLocallyConstant_ang (H : Hyp Λ σ l) (g : topologicalFullGroup Λ (Sub H)) :
    IsLocallyConstant (ang H g) :=
  (IsLocallyConstant.iff_eventually_eq _).2 (ang_eventually H g)

lemma ang_mul (H : Hyp Λ σ l) (g g' : topologicalFullGroup Λ (Sub H)) (x : Sub H) :
    ang H (g * g') x = ang H g ((g' : Sub H ≃ₜ Sub H) x) + ang H g' x := by
  apply free H (x := x)
  rw [← ang_spec, add_vadd, ← ang_spec, ← ang_spec]
  rfl

lemma ang_one (H : Hyp Λ σ l) (x : Sub H) : ang H 1 x = 0 := by
  apply free H (x := x)
  rw [← ang_spec, zero_vadd]
  rfl

/-- The circle map of an element of the full group. -/
noncomputable def ψf (H : Hyp Λ σ l) (g : topologicalFullGroup Λ (Sub H)) (z : UnitAddCircle) :
    UnitAddCircle :=
  z + (ang H g (pt H true z) : UnitAddCircle)

lemma g_pt (H : Hyp Λ σ l) (g : topologicalFullGroup Λ (Sub H)) (z : UnitAddCircle) :
    (g : Sub H ≃ₜ Sub H) (pt H true z) = pt H true (ψf H g z) := by
  rw [ang_spec, vadd_pt]; rfl

lemma ψf_mul (H : Hyp Λ σ l) (g g' : topologicalFullGroup Λ (Sub H)) (z : UnitAddCircle) :
    ψf H (g * g') z = ψf H g (ψf H g' z) := by
  simp only [ψf]
  rw [ang_mul, g_pt]
  simp only [ψf, AddSubgroup.coe_add]
  abel

lemma ψf_one (H : Hyp Λ σ l) (z : UnitAddCircle) : ψf H 1 z = z := by
  simp [ψf, ang_one]

/-- The homomorphism to permutations of the circle. -/
noncomputable def ψ (H : Hyp Λ σ l) : topologicalFullGroup Λ (Sub H) →* Equiv.Perm UnitAddCircle where
  toFun g :=
    { toFun := ψf H g
      invFun := ψf H g⁻¹
      left_inv := fun z => by rw [← ψf_mul, inv_mul_cancel, ψf_one]
      right_inv := fun z => by rw [← ψf_mul, mul_inv_cancel, ψf_one] }
  map_one' := by ext z; exact ψf_one H z
  map_mul' g g' := by ext z; exact ψf_mul H g g' z

lemma ψ_apply (H : Hyp Λ σ l) (g : topologicalFullGroup Λ (Sub H)) (z : UnitAddCircle) :
    ψ H g z = ψf H g z := rfl

lemma ψf_contAt (H : Hyp Λ σ l) (g : topologicalFullGroup Λ (Sub H)) (z : UnitAddCircle)
    (h : ang H g (pt H true z) = ang H g (pt H false z)) : ContinuousAt (ψf H g) z := by
  have hR := (tendsto_pt_pos H z true).eventually (ang_eventually H g (pt H true z))
  have hL := (tendsto_pt_neg H z true).eventually (ang_eventually H g (pt H false z))
  set a : UnitAddCircle := (ang H g (pt H true z) : UnitAddCircle)
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ψf H g (z + t) = z + t + a := by
    rw [nhds_zero_eq, eventually_sup, eventually_sup]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · filter_upwards [hL] with t ht; simp only [ψf, a]; rw [ht, h]
    · filter_upwards [hR] with t ht; simp only [ψf, a]; rw [ht]
    · rw [eventually_pure]; simp [ψf, a]
  rw [ContinuousAt, nhds_circle, tendsto_map'_iff]
  have hc : Continuous (fun t : ℝ => z + (t : UnitAddCircle) + a) :=
    (continuous_const.add contMk).add continuous_const
  have e : ψf H g z = z + ((0:ℝ) : UnitAddCircle) + a := by simp [ψf, a]
  rw [e]
  exact (hc.tendsto 0).congr' (hev.mono fun t ht => ht.symm)

lemma ψf_contAt_of_not_mem (H : Hyp Λ σ l) (g : topologicalFullGroup Λ (Sub H))
    {z : UnitAddCircle} (hz : z ∉ cosetsOf Λ σ) : ContinuousAt (ψf H g) z :=
  ψf_contAt H g z (by rw [pt_true_eq_false H hz])

lemma ψf_punctured (H : Hyp Λ σ l) (g : topologicalFullGroup Λ (Sub H)) (z : UnitAddCircle) :
    ∀ᶠ t : ℝ in 𝓝[≠] 0, ContinuousAt (ψf H g) (z + t) := by
  rw [← nhdsLT_sup_nhdsGT, eventually_sup]
  constructor
  · have h1 := (tendsto_pt_neg H z true).eventually (ang_eventually H g (pt H false z))
    have h2 := (tendsto_pt_neg H z false).eventually (ang_eventually H g (pt H false z))
    filter_upwards [h1, h2] with t h1 h2
    exact ψf_contAt H g _ (h1.trans h2.symm)
  · have h1 := (tendsto_pt_pos H z true).eventually (ang_eventually H g (pt H true z))
    have h2 := (tendsto_pt_pos H z false).eventually (ang_eventually H g (pt H true z))
    filter_upwards [h1, h2] with t h1 h2
    exact ψf_contAt H g _ (h1.trans h2.symm)

lemma finite_of_punctured (D : Set UnitAddCircle)
    (h : ∀ z, ∀ᶠ t : ℝ in 𝓝[≠] 0, z + (t : UnitAddCircle) ∉ D) : D.Finite := by
  have hU : ∀ z ∈ (univ : Set UnitAddCircle), {w | w ∈ D → w = z} ∈ 𝓝 z := by
    intro z _
    rw [nhds_circle, Filter.mem_map, ← nhdsNE_sup_pure, Filter.mem_sup]
    refine ⟨?_, ?_⟩
    · filter_upwards [h z] with t ht
      intro hd; exact absurd hd ht
    · simp
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover _ hU
  refine t.finite_toSet.subset ?_
  intro w hw
  obtain ⟨z, hz, hwz⟩ := mem_iUnion₂.1 (ht (mem_univ w))
  rw [hwz hw]; exact hz

lemma ψ_mem (H : Hyp Λ σ l) (g : topologicalFullGroup Λ (Sub H)) : ψ H g ∈ IETOn Λ σ := by
  have hang : (angles (ψf H g)).Finite := by
    have := compactSpace_Sub H
    refine (((isLocallyConstant_ang H g).range_finite).image
      (fun a : Λ => (a : UnitAddCircle))).subset ?_
    rintro _ ⟨z, rfl⟩
    exact ⟨_, ⟨pt H true z, rfl⟩, by simp [ψf]⟩
  have hie : IsIntervalExchange (ψ H g) := by
    refine ⟨?_, hang, ?_⟩
    · intro z
      have hev : ∀ᶠ t : ℝ in 𝓝[≥] 0, ψ H g (z + t) = ψ H g z + t := by
        filter_upwards [(tendsto_pt_ge H z).eventually (ang_eventually H g (pt H true z))]
          with t ht
        simp only [ψ_apply, ψf]; rw [ht]; abel
      have hc : ContinuousWithinAt (fun t : ℝ => ψ H g z + (t : UnitAddCircle)) (Ici 0) 0 :=
        (continuous_const.add contMk).continuousWithinAt
      exact hc.congr_of_eventuallyEq hev (by simp)
    · exact finite_of_punctured _ (fun z => (ψf_punctured H g z).mono fun t ht hd => hd ht)
  refine ⟨⟨(JMMS.mem_IET_iff _).2 hie, fun z => ?_⟩, fun z hz => ⟨ψf_contAt_of_not_mem H g hz, ?_⟩⟩
  · show ψf H g z - z ∈ Λ
    simp [ψf]
  · have : ((ψ H g)⁻¹ : Equiv.Perm UnitAddCircle) = ψ H g⁻¹ := (map_inv _ _).symm
    rw [this]; exact ψf_contAt_of_not_mem H g⁻¹ hz

lemma dense_pt (H : Hyp Λ σ l) : Dense (range (pt H true)) := by
  intro x
  obtain ⟨y, b, rfl⟩ := exists_pt H x
  cases b
  · exact mem_closure_of_tendsto (tendsto_pt_neg H y true)
      (Filter.Eventually.of_forall fun t => ⟨_, rfl⟩)
  · exact subset_closure ⟨y, rfl⟩

lemma ψ_injective (H : Hyp Λ σ l) : Function.Injective (ψ H) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : ∀ z, ang H g (pt H true z) = 0 := by
    intro z
    have := congrArg (fun p : Equiv.Perm UnitAddCircle => p z) hg
    simp only [ψ_apply, ψf, Equiv.Perm.coe_one, id_eq, add_eq_left] at this
    exact Subtype.ext this
  have := Continuous.ext_on (dense_pt H) (g : Sub H ≃ₜ Sub H).continuous continuous_id
    (by rintro _ ⟨z, rfl⟩; rw [ang_spec, h1, zero_vadd]; rfl)
  apply Subtype.ext
  apply Homeomorph.ext
  intro x
  exact congrFun this x

/-! ## Surjectivity: interval exchanges act on the subshift -/

lemma eventually_eq_of_finite {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [T1Space β]
    {f : α → β} {s : Set α} {a : α} {S : Set β} (hS : S.Finite) (hf : ∀ t, f t ∈ S)
    (hc : ContinuousWithinAt f s a) : ∀ᶠ t in 𝓝[s] a, f t = f a := by
  have hopen : IsOpen (S \ {f a})ᶜ := ((hS.subset Set.sdiff_subset).isClosed).isOpen_compl
  have hmem : f a ∈ (S \ {f a})ᶜ := by simp
  filter_upwards [hc (hopen.mem_nhds hmem)] with t ht
  by_contra hne
  exact ht ⟨hf t, hne⟩

lemma eventually_of_continuousAt {g : UnitAddCircle → UnitAddCircle} (ha : (angles g).Finite)
    {x : UnitAddCircle} (hc : ContinuousAt g x) : ∀ᶠ z in 𝓝 x, g z - z = g x - x := by
  have := eventually_eq_of_finite (s := Set.univ) ha (fun t => ⟨t, rfl⟩)
    ((hc.sub continuousAt_id).continuousWithinAt)
  simpa [nhdsWithin_univ] using this

lemma locTrans_of {g : UnitAddCircle → UnitAddCircle} (hr : IsRightContinuous g)
    (ha : (angles g).Finite) (x : UnitAddCircle) :
    ∀ᶠ t : ℝ in 𝓝[Set.Ici (0:ℝ)] (0:ℝ), g (x + (t : UnitAddCircle)) = g x + t := by
  have hc : ContinuousWithinAt
      (fun t : ℝ => g (x + (t : UnitAddCircle)) - (x + (t : UnitAddCircle))) (Set.Ici 0) 0 :=
    (hr x).sub ((continuous_const.add contMk).continuousWithinAt)
  filter_upwards [eventually_eq_of_finite ha (fun t => ⟨x + t, rfl⟩) hc] with t ht
  simp only [QuotientAddGroup.mk_zero, add_zero] at ht
  rw [← sub_add_cancel (g (x + t)) (x + t), ht]
  abel

variable {f : Equiv.Perm UnitAddCircle}

lemma perm_inv_apply (f : Equiv.Perm UnitAddCircle) (x : UnitAddCircle) : f⁻¹ (f x) = x := by
  simp

lemma ie_of (hf : f ∈ IETOn Λ σ) : IsIntervalExchange f := (JMMS.mem_IET_iff f).1 hf.1.1

lemma angmem_of (hf : f ∈ IETOn Λ σ) (z : UnitAddCircle) : f z - z ∈ Λ := hf.1.2 z

lemma right_trans (hf : f ∈ IETOn Λ σ) (y : UnitAddCircle) :
    ∀ᶠ t : ℝ in 𝓝[≥] 0, f (y + t) = y + t + (f y - y) := by
  filter_upwards [locTrans_of (ie_of hf).1 (ie_of hf).2.1 y] with t ht
  rw [ht]; abel

lemma left_exists (hf : f ∈ IETOn Λ σ) (y : UnitAddCircle) :
    ∃ α : UnitAddCircle, ∀ᶠ t : ℝ in 𝓝[<] 0, f (y + t) = y + t + α := by
  have hI := ie_of hf
  have hcont : Continuous (fun t : ℝ => y + (t : UnitAddCircle)) := continuous_const.add contMk
  have h1 : ∀ᶠ t : ℝ in 𝓝[<] 0, ContinuousAt f (y + t) := by
    have : ∀ d ∈ {x | ¬ ContinuousAt f x}, ∀ᶠ t : ℝ in 𝓝[<] 0, y + (t : UnitAddCircle) ≠ d := by
      intro d _
      by_cases hd : d = y
      · subst hd
        filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 0 by norm_num)] with t ⟨h1, h2⟩ h
        have : (t : UnitAddCircle) = 0 := by
          have := congrArg (fun z => z - d) h; simpa using this
        exact coe_ne_zero_of (t := t) (by rw [abs_pos]; linarith)
          (by rw [abs_lt]; constructor <;> linarith) this
      · exact nhdsWithin_le_nhds (hcont.continuousAt.eventually_ne (by simpa using Ne.symm hd))
    filter_upwards [(Filter.eventually_all_finite hI.2.2).2 this] with t ht
    by_contra hc
    exact ht _ hc rfl
  obtain ⟨c, hc, hcs⟩ := (nhdsLT_basis (0:ℝ)).eventually_iff.1 h1
  set A : ℝ → UnitAddCircle := fun t => f (y + t) - (y + t) with hA
  have hAc : ContinuousOn A (Ioo c 0) := by
    intro t ht
    exact ((ContinuousAt.comp (f := fun t : ℝ => y + (t : UnitAddCircle)) (hcs ht)
      hcont.continuousAt).sub hcont.continuousAt).continuousWithinAt
  have hAm : MapsTo A (Ioo c 0) (angles f) := fun t _ => ⟨y + t, rfl⟩
  refine ⟨A (c / 2), ?_⟩
  filter_upwards [Ioo_mem_nhdsLT hc] with t ht
  have e : A t = A (c / 2) := isPreconnected_Ioo.constant_of_mapsTo hI.2.1.isDiscrete hAc hAm
    (x := t) (y := c / 2) ht ⟨by linarith, by linarith⟩
  rw [← e]; simp only [hA]; abel

/-- The left angle of `f` at `y`. -/
noncomputable def leftAng (hf : f ∈ IETOn Λ σ) (y : UnitAddCircle) : UnitAddCircle :=
  Classical.choose (left_exists hf y)

lemma leftAng_spec (hf : f ∈ IETOn Λ σ) (y : UnitAddCircle) :
    ∀ᶠ t : ℝ in 𝓝[<] 0, f (y + t) = y + t + leftAng hf y :=
  Classical.choose_spec (left_exists hf y)

lemma leftAng_unique (hf : f ∈ IETOn Λ σ) (y : UnitAddCircle) {α : UnitAddCircle}
    (h : ∀ᶠ t : ℝ in 𝓝[<] 0, f (y + t) = y + t + α) : leftAng hf y = α := by
  obtain ⟨t, h1, h2⟩ := (h.and (leftAng_spec hf y)).exists
  rw [h1] at h2; exact (add_left_cancel h2).symm

lemma leftAng_mem (hf : f ∈ IETOn Λ σ) (y : UnitAddCircle) : leftAng hf y ∈ Λ := by
  obtain ⟨t, ht⟩ := (leftAng_spec hf y).exists
  have := angmem_of hf (y + t)
  rw [ht] at this
  simpa using this

lemma leftAng_eq_of_cont (hf : f ∈ IETOn Λ σ) {y : UnitAddCircle} (hc : ContinuousAt f y) :
    leftAng hf y = f y - y := by
  apply leftAng_unique
  have := eventually_of_continuousAt (ie_of hf).2.1 hc
  rw [nhds_circle, eventually_map] at this
  filter_upwards [nhdsWithin_le_nhds this] with t ht
  rw [← ht]; abel

lemma evR (hf : f ∈ IETOn Λ σ) (y : UnitAddCircle) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, f (y + t) - (y + t) = f y - y ∧ leftAng hf (y + t) = f y - y := by
  obtain ⟨c, hc, hcs⟩ := (nhdsGE_basis (0:ℝ)).eventually_iff.1 (right_trans hf y)
  filter_upwards [Ioo_mem_nhdsGT hc] with t ⟨ht0, ht1⟩
  refine ⟨?_, ?_⟩
  · rw [hcs ⟨ht0.le, ht1⟩]; abel
  · apply leftAng_unique
    filter_upwards [Ioo_mem_nhdsLT (show -t < 0 by linarith)] with t' ⟨h1, h2⟩
    have := hcs (x := t + t') ⟨by linarith, by linarith⟩
    rw [AddCircle.coe_add, ← add_assoc] at this
    rw [this]

lemma evL (hf : f ∈ IETOn Λ σ) (y : UnitAddCircle) :
    ∀ᶠ t : ℝ in 𝓝[<] 0, f (y + t) - (y + t) = leftAng hf y ∧
      leftAng hf (y + t) = leftAng hf y := by
  obtain ⟨c, hc, hcs⟩ := (nhdsLT_basis (0:ℝ)).eventually_iff.1 (leftAng_spec hf y)
  filter_upwards [Ioo_mem_nhdsLT hc] with t ⟨ht0, ht1⟩
  refine ⟨?_, ?_⟩
  · rw [hcs ⟨ht0, ht1⟩]; abel
  · apply leftAng_unique
    filter_upwards [Ioo_mem_nhdsLT (show c - t < 0 by linarith)] with t' ⟨h1, h2⟩
    have := hcs (x := t + t') ⟨by linarith, by linarith⟩
    rw [AddCircle.coe_add, ← add_assoc] at this
    rw [this]

open Classical in
/-- The translation amount of the lift of `f` at a point of the subshift. -/
noncomputable def θ (H : Hyp Λ σ l) (hf : f ∈ IETOn Λ σ) (x : Sub H) : Λ :=
  if x = pt H true (proj H x) then ⟨f (proj H x) - proj H x, angmem_of hf _⟩
  else ⟨leftAng hf (proj H x), leftAng_mem hf _⟩

open Classical in
lemma θ_eq (H : Hyp Λ σ l) (hf : f ∈ IETOn Λ σ) (x : Sub H) :
    (θ H hf x : UnitAddCircle) =
      if x = pt H true (proj H x) then f (proj H x) - proj H x else leftAng hf (proj H x) := by
  unfold θ
  split_ifs <;> rfl

open Classical in
lemma θ_pt (H : Hyp Λ σ l) (hf : f ∈ IETOn Λ σ) (b : Bool) (y : UnitAddCircle) :
    (θ H hf (pt H b y) : UnitAddCircle) = if b then f y - y else leftAng hf y := by
  rw [θ_eq, proj_pt]
  by_cases h : pt H b y = pt H true y
  · rw [if_pos h]
    cases b
    · have hy : y ∉ cosetsOf Λ σ := fun hy => pt_true_ne_false H hy h.symm
      simp only [Bool.false_eq_true, if_false]
      exact (leftAng_eq_of_cont hf (hf.2 y hy).1).symm
    · simp
  · rw [if_neg h]
    cases b
    · simp
    · exact absurd rfl h

lemma θ_eventually (H : Hyp Λ σ l) (hf : f ∈ IETOn Λ σ) (x₀ : Sub H) :
    ∀ᶠ x in 𝓝 x₀, θ H hf x = θ H hf x₀ := by
  obtain ⟨y, b, rfl⟩ := exists_pt H x₀
  have hRL : y ∉ cosetsOf Λ σ → leftAng hf y = f y - y :=
    fun hy => leftAng_eq_of_cont hf (hf.2 y hy).1
  obtain ⟨c1, hc1, hR⟩ := (nhdsGT_basis (0:ℝ)).eventually_iff.1 (evR hf y)
  obtain ⟨c2, hc2, hL⟩ := (nhdsLT_basis (0:ℝ)).eventually_iff.1 (evL hf y)
  obtain ⟨V, hV, hVp⟩ := nbhdS H y b (η := min c1 (-c2)) (lt_min hc1 (by linarith))
  filter_upwards [hV] with x hx
  obtain ⟨w, b', rfl⟩ := exists_pt H x
  obtain ⟨t, ht, rfl, hside⟩ := hVp w b' hx
  apply Subtype.ext
  rw [θ_pt, θ_pt]
  have hm1 := min_le_left c1 (-c2)
  have hm2 := min_le_right c1 (-c2)
  obtain ⟨ht1, ht2⟩ := abs_lt.1 ht
  rcases lt_trichotomy t 0 with hneg | rfl | hpos
  · obtain ⟨h1, h2⟩ := hL ⟨by linarith, hneg⟩
    have lhs : (if b' then f (y + t) - (y + t) else leftAng hf (y + t)) = leftAng hf y := by
      cases b' <;> simp [h1, h2]
    rw [lhs]
    by_cases hy : y ∈ cosetsOf Λ σ
    · cases b
      · simp
      · exact absurd ((hside hy).1 rfl).1 (not_le.2 hneg)
    · cases b <;> simp [hRL hy]
  · simp only [QuotientAddGroup.mk_zero, add_zero]
    by_cases hy : y ∈ cosetsOf Λ σ
    · cases b
      · have := ((hside hy).2 rfl).2 rfl
        subst this; rfl
      · have := ((hside hy).1 rfl).2 rfl
        subst this; rfl
    · cases b <;> cases b' <;> simp [hRL hy]
  · obtain ⟨h1, h2⟩ := hR ⟨hpos, by linarith⟩
    have lhs : (if b' then f (y + t) - (y + t) else leftAng hf (y + t)) = f y - y := by
      cases b' <;> simp [h1, h2]
    rw [lhs]
    by_cases hy : y ∈ cosetsOf Λ σ
    · cases b
      · exact absurd ((hside hy).2 rfl).1 (not_le.2 hpos)
      · simp
    · cases b <;> simp [hRL hy]

/-- The lift of `f` to the subshift. -/
noncomputable def Gfun (H : Hyp Λ σ l) (hf : f ∈ IETOn Λ σ) (x : Sub H) : Sub H := θ H hf x +ᵥ x

lemma Gfun_pt_true (H : Hyp Λ σ l) (hf : f ∈ IETOn Λ σ) (y : UnitAddCircle) :
    Gfun H hf (pt H true y) = pt H true (f y) := by
  rw [Gfun, vadd_pt]
  congr 1
  have := θ_pt H hf true y
  simp only [if_true] at this
  rw [this]; abel

lemma Gfun_pt_false (H : Hyp Λ σ l) (hf : f ∈ IETOn Λ σ) (y : UnitAddCircle) :
    Gfun H hf (pt H false y) = pt H false (y + leftAng hf y) := by
  rw [Gfun, vadd_pt]
  congr 1
  have := θ_pt H hf false y
  simp only [Bool.false_eq_true, if_false] at this
  rw [this]

lemma Gfun_continuous (H : Hyp Λ σ l) (hf : f ∈ IETOn Λ σ) : Continuous (Gfun H hf) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hc := (vadd_continuous H (θ H hf x)).continuousAt (x := x)
  refine hc.congr ?_
  filter_upwards [θ_eventually H hf x] with x' hx'
  simp [Gfun, hx']

lemma leftAng_inv (hf : f ∈ IETOn Λ σ) (y : UnitAddCircle) :
    leftAng ((IETOn Λ σ).inv_mem hf) (y + leftAng hf y) = -leftAng hf y := by
  apply leftAng_unique
  filter_upwards [leftAng_spec hf y] with t ht
  rw [show y + leftAng hf y + (t : UnitAddCircle) = y + t + leftAng hf y by abel, ← ht,
    perm_inv_apply, ht]
  abel

lemma Gfun_inv_left (H : Hyp Λ σ l) (hf : f ∈ IETOn Λ σ) (x : Sub H) :
    Gfun H ((IETOn Λ σ).inv_mem hf) (Gfun H hf x) = x := by
  obtain ⟨y, b, rfl⟩ := exists_pt H x
  cases b
  · rw [Gfun_pt_false, Gfun_pt_false, leftAng_inv]
    congr 1; abel
  · rw [Gfun_pt_true, Gfun_pt_true, perm_inv_apply]

lemma Gfun_eq (H : Hyp Λ σ l) {f f' : Equiv.Perm UnitAddCircle} (hf : f ∈ IETOn Λ σ)
    (hf' : f' ∈ IETOn Λ σ) (h : f = f') : Gfun H hf = Gfun H hf' := by
  subst h; rfl

/-- The lift of `f` as a homeomorphism. -/
noncomputable def Gf (H : Hyp Λ σ l) (hf : f ∈ IETOn Λ σ) : Sub H ≃ₜ Sub H where
  toFun := Gfun H hf
  invFun := Gfun H ((IETOn Λ σ).inv_mem hf)
  left_inv := Gfun_inv_left H hf
  right_inv x := by
    have := Gfun_inv_left H ((IETOn Λ σ).inv_mem hf) x
    rwa [Gfun_eq H _ hf (inv_inv f)] at this
  continuous_toFun := Gfun_continuous H hf
  continuous_invFun := Gfun_continuous H _

lemma Gf_mem (H : Hyp Λ σ l) (hf : f ∈ IETOn Λ σ) : Gf H hf ∈ topologicalFullGroup Λ (Sub H) := by
  intro x
  refine ⟨_, θ_eventually H hf x, θ H hf x, fun x' hx' => ?_⟩
  show θ H hf x' +ᵥ x' = _
  rw [show θ H hf x' = θ H hf x from hx']

lemma ψ_Gf (H : Hyp Λ σ l) (hf : f ∈ IETOn Λ σ) : ψ H ⟨Gf H hf, Gf_mem H hf⟩ = f := by
  ext z
  rw [ψ_apply, ψf]
  have : ang H ⟨Gf H hf, Gf_mem H hf⟩ (pt H true z) = θ H hf (pt H true z) :=
    free H ((ang_spec _ _ _).symm.trans rfl)
  rw [this, θ_pt]; simp

/-- The isomorphism `[[Λ]] ≃* IET(Λ; Σ)`. -/
noncomputable def π (H : Hyp Λ σ l) : topologicalFullGroup Λ (Sub H) ≃* IETOn Λ σ :=
  MulEquiv.ofBijective ((ψ H).codRestrict (IETOn Λ σ) (ψ_mem H))
    ⟨fun _ _ h => ψ_injective H (congrArg Subtype.val h),
     fun ⟨_, hf⟩ => ⟨⟨Gf H hf, Gf_mem H hf⟩, Subtype.ext (ψ_Gf H hf)⟩⟩

lemma π_apply (H : Hyp Λ σ l) (g : topologicalFullGroup Λ (Sub H)) :
    ((π H g : IETOn Λ σ) : Equiv.Perm UnitAddCircle) = ψ H g := rfl

lemma semiconj (H : Hyp Λ σ l) (g : topologicalFullGroup Λ (Sub H)) (x : Sub H)
    (hx : proj H x ∉ cosetsOf Λ σ) :
    proj H ((g : Sub H ≃ₜ Sub H) x) = ((π H g : IETOn Λ σ) : Equiv.Perm UnitAddCircle) (proj H x) := by
  obtain ⟨b, hb⟩ := proj_spec H x
  set y := proj H x with hy
  have hx' : x = pt H true y := by
    cases b
    · rw [hb]; exact (pt_true_eq_false H hx).symm
    · exact hb
  rw [π_apply, ψ_apply]
  conv_lhs => rw [hx']
  rw [g_pt, proj_pt]

/-! ## Complexity (Lemma 5.13) -/

lemma window (H : Hyp Λ σ l) {m : ℕ} (p : Sub H → Fin m) (hp : Continuous p) :
    ∃ W : Finset Λ, ∀ x x' : Sub H,
      (∀ δ ∈ W, (x : Λ → Fin (K σ)) δ = (x' : Λ → Fin (K σ)) δ) → p x = p x' := by
  classical
  have := compactSpace_Sub H
  have hx : ∀ x : Sub H, ∃ W : Finset Λ, ∀ x' : Sub H,
      (∀ δ ∈ W, (x' : Λ → Fin (K σ)) δ = (x : Λ → Fin (K σ)) δ) → p x' = p x := by
    intro x
    have hU : p ⁻¹' {p x} ∈ 𝓝 x :=
      hp.continuousAt.preimage_mem_nhds ((isOpen_discrete _).mem_nhds rfl)
    rw [nhds_subtype, Filter.mem_comap, nhds_pi] at hU
    obtain ⟨t, ht, hts⟩ := hU
    rw [Filter.mem_pi] at ht
    obtain ⟨I, hI, u, hu, hIu⟩ := ht
    refine ⟨hI.toFinset, fun x' hx' => ?_⟩
    have h1 : (x' : Λ → Fin (K σ)) ∈ t := hIu (fun i hi => by
      rw [hx' i (hI.mem_toFinset.2 hi)]; exact mem_of_mem_nhds (hu i))
    exact hts h1
  choose Wx hWx using hx
  set U : Sub H → Set (Sub H) := fun x =>
    {x' | ∀ δ ∈ Wx x, (x' : Λ → Fin (K σ)) δ = (x : Λ → Fin (K σ)) δ} with hUdef
  have hUo : ∀ x, IsOpen (U x) := by
    intro x
    have : U x = ⋂ δ ∈ Wx x,
        {x' : Sub H | (x' : Λ → Fin (K σ)) δ = (x : Λ → Fin (K σ)) δ} := by
      ext x'; simp [hUdef]
    rw [this]
    exact isOpen_biInter_finset fun δ _ => (isOpen_coord δ _).preimage continuous_subtype_val
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover U hUo
    (fun x _ => mem_iUnion.2 ⟨x, fun δ _ => rfl⟩)
  refine ⟨T.biUnion Wx, fun x x' hxx' => ?_⟩
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 (hT (mem_univ x))
  have hx'z : x' ∈ U z := fun δ hδ =>
    (hxx' δ (Finset.mem_biUnion.2 ⟨z, hz, hδ⟩)).symm.trans (hxz δ hδ)
  rw [hWx z x hxz, hWx z x' hx'z]

lemma ball_bound (Λ : AddSubgroup UnitAddCircle) [AddGroup.FG Λ] (d : ℕ)
    (hd : rationalRank Λ = d) (T : Finset Λ) :
    ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∃ B : Finset Λ, wordBall (T : Set Λ) n ⊆ B ∧
      B.card ≤ C * n ^ d := by
  classical
  obtain ⟨r, ι, _, q, hq, e, ⟨φ⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod Λ
  have : ∀ i, NeZero (q i ^ e i) := fun i => ⟨pow_ne_zero _ (hq i).ne_zero⟩
  set Tor := DirectSum ι fun i => ZMod (q i ^ e i)
  have hTf : Finite Tor := Finite.of_injective (fun x : Tor => (fun i => x i)) DFunLike.coe_injective
  have : Fintype Tor := Fintype.ofFinite Tor
  let emb : (Fin r → ℤ) →+ Λ :=
    { toFun := fun v => φ.symm (Finsupp.equivFunOnFinite.symm v, 0)
      map_zero' := by
        rw [show Finsupp.equivFunOnFinite.symm (0 : Fin r → ℤ) = 0 from
          (Equiv.symm_apply_eq _).2 Finsupp.coe_zero.symm]
        simp
      map_add' := fun v w => by
        rw [← map_add]; congr 1; ext i <;> simp }
  have hemb : Function.Injective emb := by
    intro v w h
    have h1 := congrArg Prod.fst (φ.symm.injective h)
    exact Finsupp.equivFunOnFinite.symm.injective h1
  have hr : r ≤ d := by
    have : (r : ℕ∞) ≤ rationalRank Λ :=
      le_iSup₂_of_le (f := fun (d : ℕ) (_ : ∃ f : (Fin d → ℤ) →+ Λ, Function.Injective f) =>
        (d : ℕ∞)) r ⟨emb, hemb⟩ le_rfl
    rw [hd] at this; exact_mod_cast this
  set crd : Λ → Fin r → ℤ := fun a i => (φ a).1 i with hcrd
  have crd_add : ∀ a b i, crd (a + b) i = crd a i + crd b i := by intro a b i; simp [crd]
  have crd_neg : ∀ a i, crd (-a) i = -crd a i := by intro a i; simp [crd]
  set M : ℕ := ∑ t ∈ T, ∑ i, (crd t i).natAbs with hMdef
  have hM : ∀ a, (a ∈ T ∨ -a ∈ T) → ∀ i, (crd a i).natAbs ≤ M := by
    intro a ha i
    have key : ∀ t ∈ T, (crd t i).natAbs ≤ M := fun t ht =>
      (Finset.single_le_sum (f := fun j => (crd t j).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)).trans
        (Finset.single_le_sum (f := fun t => ∑ j, (crd t j).natAbs) (fun _ _ => Nat.zero_le _) ht)
    rcases ha with ha | ha
    · exact key a ha
    · have := key _ ha; rwa [crd_neg, Int.natAbs_neg] at this
  have hlist : ∀ L : List Λ, (∀ a ∈ L, a ∈ T ∨ -a ∈ T) → ∀ i,
      (crd L.sum i).natAbs ≤ L.length * M := by
    intro L
    induction L with
    | nil => intro _ i; simp [crd]
    | cons a L ih =>
      intro hL i
      rw [List.sum_cons, crd_add, List.length_cons]
      have h1 := hM a (hL a List.mem_cons_self) i
      have h2 := ih (fun b hb => hL b (List.mem_cons_of_mem _ hb)) i
      calc (crd a i + crd L.sum i).natAbs ≤ (crd a i).natAbs + (crd L.sum i).natAbs :=
            Int.natAbs_add_le _ _
        _ ≤ M + L.length * M := Nat.add_le_add h1 h2
        _ = (L.length + 1) * M := by ring
  refine ⟨(2 * M + 1) ^ r * Fintype.card Tor, fun n hn => ?_⟩
  set N : ℕ := n * M with hN
  set box : Finset (Fin r → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N
  refine ⟨(box ×ˢ (Finset.univ : Finset Tor)).image
    (fun p => φ.symm (Finsupp.equivFunOnFinite.symm p.1, p.2)), ?_, ?_⟩
  · rintro γ ⟨L, hLn, hL, rfl⟩
    refine Finset.mem_image.2 ⟨(crd L.sum, (φ L.sum).2),
      Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩, ?_⟩
    · rw [Fintype.mem_piFinset]; intro i
      have h1 := (hlist L hL i).trans (Nat.mul_le_mul_right M hLn)
      have h2 : |crd L.sum i| ≤ (N : ℤ) := by
        rw [← Int.natCast_natAbs]; exact_mod_cast h1
      exact Finset.mem_Icc.2 (abs_le.1 h2)
    · simp [crd]
  · have hc : (Finset.Icc (-(N : ℤ)) N).card = 2 * N + 1 := by rw [Int.card_Icc]; omega
    calc ((box ×ˢ (Finset.univ : Finset Tor)).image _).card
        ≤ (box ×ˢ (Finset.univ : Finset Tor)).card := Finset.card_image_le
      _ = (2 * N + 1) ^ r * Fintype.card Tor := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_piFinset, hc]
        simp
      _ ≤ ((2 * M + 1) * n) ^ r * Fintype.card Tor := by
        apply Nat.mul_le_mul_right
        apply Nat.pow_le_pow_left
        rw [hN]; nlinarith
      _ = (2 * M + 1) ^ r * Fintype.card Tor * n ^ r := by rw [mul_pow]; ring
      _ ≤ (2 * M + 1) ^ r * Fintype.card Tor * n ^ d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn hr)

lemma same_arc {y q u : UnitAddCircle} (hu : fr (y - q) ≤ fr (y - u))
    (hu' : fr (y - q) ≤ fr (y - (u + l))) : (fr (y - u) < l ↔ fr (q - u) < l) := by
  set r := fr (y - q)
  set A := fr (q - u)
  have hr0 := fr_nonneg (y - q)
  have hr1 := fr_lt_one (y - q)
  have hA0 := fr_nonneg (q - u)
  have hA1 := fr_lt_one (q - u)
  have e0 : fr (y - u) = Int.fract (r + A) := by
    have : y - u = (y - q) + (q - u) := by abel
    rw [this, fr_add]
  have e1 : fr (y - u) = r + A := by
    rw [e0]
    by_cases h : r + A < 1
    · exact Int.fract_eq_self.2 ⟨by linarith, h⟩
    · exfalso
      have : Int.fract (r + A) = r + A - 1 := by
        rw [Int.fract_eq_iff]; exact ⟨by linarith, by linarith, 1, by push_cast; ring⟩
      rw [e0, this] at hu; linarith
  have e2 : fr (y - (u + l)) = Int.fract (r + A - l) := by
    have : y - (u + (l : UnitAddCircle)) = ((fr (y - u) - l : ℝ) : UnitAddCircle) := by
      rw [AddCircle.coe_sub, coe_fr]; abel
    rw [this, fr_coe, e1]
  constructor
  · intro h; rw [e1] at h; linarith
  · intro h
    rw [e1]
    by_contra h'
    push Not at h'
    rw [e2, Int.fract_eq_self.2 ⟨by linarith, by linarith⟩] at hu'
    linarith

lemma ncard_range_le {α β γ : Type*} (f : α → β) (g : α → γ)
    (h : ∀ a a', g a = g a' → f a = f a') (hg : (range g).Finite) :
    (range f).ncard ≤ (range g).ncard := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [Set.range_eq_empty]
  · set Φ := fun c => f (Function.invFun g c)
    have hsub : range f ⊆ Φ '' range g := by
      rintro _ ⟨a, rfl⟩
      exact ⟨g a, ⟨a, rfl⟩, h _ _ (Function.invFun_eq ⟨a, rfl⟩)⟩
    exact (Set.ncard_le_ncard hsub (hg.image _)).trans (Set.ncard_image_le hg)

lemma count_codes (H : Hyp Λ σ l) (F : Finset Λ) :
    (range (fun y : UnitAddCircle => fun δ : F => code Λ σ l true y δ)).ncard ≤
      2 * σ.card * F.card + 1 := by
  classical
  set R := fun y : UnitAddCircle => fun δ : F => code Λ σ l true y δ with hR
  set Q : Finset UnitAddCircle :=
    (σ ×ˢ F).image (fun p => p.1 - (p.2 : UnitAddCircle)) ∪
      (σ ×ˢ F).image (fun p => p.1 - (p.2 : UnitAddCircle) + l) with hQdef
  have hQc : Q.card ≤ 2 * σ.card * F.card := by
    calc Q.card ≤ _ + _ := Finset.card_union_le _ _
      _ ≤ (σ ×ˢ F).card + (σ ×ˢ F).card := add_le_add Finset.card_image_le Finset.card_image_le
      _ = 2 * σ.card * F.card := by rw [Finset.card_product]; ring
  rcases Q.eq_empty_or_nonempty with hQ | hQ
  · have hF : F = ∅ := by
      by_contra hF
      obtain ⟨δ, hδ⟩ := Finset.nonempty_iff_ne_empty.2 hF
      obtain ⟨s, hs⟩ := H.ne
      have : s - (δ : UnitAddCircle) ∈ Q := Finset.mem_union_left _
        (Finset.mem_image.2 ⟨(s, δ), Finset.mem_product.2 ⟨hs, hδ⟩, rfl⟩)
      rw [hQ] at this; simp at this
    have : Subsingleton (F → Fin (K σ)) :=
      ⟨fun f g => funext fun δ => absurd δ.2 (Finset.eq_empty_iff_forall_notMem.1 hF _)⟩
    exact (Set.ncard_le_one_of_subsingleton _).trans (Nat.le_add_left _ _)
  · have hsub : range R ⊆ R '' (Q : Set UnitAddCircle) := by
      rintro _ ⟨y, rfl⟩
      obtain ⟨q, hq, hmin⟩ := Q.exists_min_image (fun q => fr (y - q)) hQ
      refine ⟨q, hq, ?_⟩
      funext δ
      apply code_eq_iff.2
      intro s hs
      set u := s - (δ : UnitAddCircle) with hu
      have huQ : u ∈ Q := Finset.mem_union_left _
        (Finset.mem_image.2 ⟨(s, δ), Finset.mem_product.2 ⟨hs, δ.2⟩, rfl⟩)
      have huQ' : u + l ∈ Q := Finset.mem_union_right _
        (Finset.mem_image.2 ⟨(s, δ), Finset.mem_product.2 ⟨hs, δ.2⟩, rfl⟩)
      have e : ∀ v : UnitAddCircle, v + (δ : UnitAddCircle) - s = v - u := by
        intro v; rw [hu]; abel
      rw [e, e]
      show fr _ < l ↔ fr _ < l
      exact (same_arc (hmin u huQ) (hmin _ huQ')).symm
    calc (range R).ncard ≤ (R '' (Q : Set UnitAddCircle)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (Q : Set UnitAddCircle).ncard := Set.ncard_image_le Q.finite_toSet
      _ = Q.card := Set.ncard_coe_finset Q
      _ ≤ _ := by omega

lemma complexity_bound (H : Hyp Λ σ l) [AddGroup.FG Λ] (d : ℕ) (hd : rationalRank Λ = d)
    (T : Finset Λ) {m : ℕ} (p : Sub H → Fin m) (hp : IsClopenPartition p) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (complexity (T : Set Λ) p n : ℝ) ≤ C * (n : ℝ) ^ d := by
  classical
  have hpc : Continuous p := by
    rw [continuous_discrete_rng]; intro i; exact (hp i).isOpen
  obtain ⟨W, hW⟩ := window H p hpc
  obtain ⟨C, hC⟩ := ball_bound Λ d hd T
  refine ⟨2 * σ.card * W.card * C + 1, by positivity, fun n hn => ?_⟩
  obtain ⟨B, hB, hBc⟩ := hC n hn
  set F : Finset Λ := (W ×ˢ B).image (fun q => q.1 - q.2) with hFdef
  set Pat := fun x : Sub H => fun γ : wordBall (T : Set Λ) n => p (-(γ : Λ) +ᵥ x) with hPat
  set Rs := fun x : Sub H => fun δ : F => (x : Λ → Fin (K σ)) δ with hRs
  set R := fun y : UnitAddCircle => fun δ : F => code Λ σ l true y δ with hR
  have h1 : (range Pat).ncard ≤ (range Rs).ncard := by
    refine ncard_range_le Pat Rs (fun x x' hxx' => funext fun γ => ?_) (Set.toFinite _)
    apply hW
    intro δ hδ
    have hmem : δ - (γ : Λ) ∈ F :=
      Finset.mem_image.2 ⟨(δ, γ), Finset.mem_product.2 ⟨hδ, hB γ.2⟩, rfl⟩
    have := congrFun hxx' ⟨_, hmem⟩
    simp only [hRs] at this
    rw [Subshift.coe_vadd, Subshift.coe_vadd, shift_apply, shift_apply, ← sub_eq_add_neg]
    exact this
  have h2 : (range Rs).ncard ≤ (range R).ncard := by
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro _ ⟨x, rfl⟩
    have hc : Continuous Rs :=
      continuous_pi fun δ => (continuous_apply (δ : Λ)).comp continuous_subtype_val
    have hO : IsOpen (Rs ⁻¹' {Rs x}) := (isOpen_discrete _).preimage hc
    obtain ⟨_, hy, ⟨y, rfl⟩⟩ := (dense_pt H).inter_open_nonempty _ hO ⟨x, rfl⟩
    exact ⟨y, hy⟩
  have h3 := count_codes H F
  have hF : F.card ≤ W.card * B.card := by
    calc F.card ≤ (W ×ˢ B).card := Finset.card_image_le
      _ = W.card * B.card := Finset.card_product _ _
  have hN : (range Pat).ncard ≤ 2 * σ.card * W.card * C * n ^ d + 1 := by
    calc (range Pat).ncard ≤ 2 * σ.card * F.card + 1 := h1.trans (h2.trans h3)
      _ ≤ 2 * σ.card * (W.card * (C * n ^ d)) + 1 := by
        gcongr; exact hF.trans (Nat.mul_le_mul_left _ hBc)
      _ = 2 * σ.card * W.card * C * n ^ d + 1 := by ring
  have hcx : complexity (T : Set Λ) p n = (range Pat).ncard := Nat.card_coe_set_eq _
  rw [hcx]
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hn)
  have : ((range Pat).ncard : ℝ) ≤ 2 * σ.card * W.card * C * (n : ℝ) ^ d + 1 := by
    exact_mod_cast hN
  nlinarith

/-! ## Assembly -/

/-- An infinite subgroup of the circle contains `l` with `0 < l < 1/2`. -/
lemma exists_small (Λ : AddSubgroup UnitAddCircle) (hΛ : (Λ : Set UnitAddCircle).Infinite) :
    ∃ l : ℝ, 0 < l ∧ l < 1 / 2 ∧ (l : UnitAddCircle) ∈ Λ := by
  obtain ⟨μ, hμ, hμn⟩ :=
    (hΛ.sdiff (Set.toFinite ({0, ((1 / 2 : ℝ) : UnitAddCircle)} : Set UnitAddCircle))).nonempty
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hμn
  set m : ℝ := (AddCircle.equivIco 1 0 μ : ℝ) with hm
  have hmμ : (m : UnitAddCircle) = μ := AddCircle.coe_equivIco
  have hmI := (AddCircle.equivIco 1 0 μ).2
  rw [← hm] at hmI
  simp only [Set.mem_Ico, zero_add] at hmI
  have hm0 : m ≠ 0 := by rintro h; apply hμn.1; rw [← hmμ, h]; simp
  have hm2 : m ≠ 1 / 2 := by rintro h; apply hμn.2; rw [← hmμ, h]
  rcases lt_or_gt_of_ne hm2 with h | h
  · exact ⟨m, lt_of_le_of_ne hmI.1 (Ne.symm hm0), h, hmμ ▸ hμ⟩
  · refine ⟨1 - m, by linarith, by linarith, ?_⟩
    rw [AddCircle.coe_sub, AddCircle.coe_period, zero_sub, hmμ]
    exact Λ.neg_mem hμ

lemma countable_of_fg (Λ : AddSubgroup UnitAddCircle) [AddGroup.FG Λ] : Countable Λ := by
  obtain ⟨r, ι, _, q, hq, e, ⟨φ⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod Λ
  have : ∀ i, NeZero (q i ^ e i) := fun i => ⟨pow_ne_zero _ (hq i).ne_zero⟩
  have hTf : Finite (DirectSum ι fun i => ZMod (q i ^ e i)) :=
    Finite.of_injective (fun x : DirectSum ι fun i => ZMod (q i ^ e i) => (fun i => x i))
      DFunLike.coe_injective
  exact φ.injective.countable

end IETP511

open IETP511 in
theorem chk_exists_isMinimal_subshift_mulEquiv_IETOn_and_complexity_le
    (Λ : AddSubgroup UnitAddCircle) (hΛ : (Λ : Set UnitAddCircle).Infinite) (hfg : Λ.FG)
    (σ : Finset UnitAddCircle) (hσ : σ.Nonempty) :
    ∃ k : ℕ, ∃ S : Subshift Λ (Fin k), IsCantorSpace S ∧ AddAction.IsMinimal Λ S ∧
      (∃ π : topologicalFullGroup Λ S ≃* IETOn Λ σ, ∃ h : S → UnitAddCircle,
        Continuous h ∧ Function.Surjective h ∧
        ∀ (g : topologicalFullGroup Λ S) (x : S), h x ∉ cosetsOf Λ σ →
          h ((g : S ≃ₜ S) x) = (π g : Equiv.Perm UnitAddCircle) (h x)) ∧
      ∀ d : ℕ, rationalRank Λ = d →
        ∀ T : Finset Λ, AddSubgroup.closure (T : Set Λ) = ⊤ →
        ∀ (m : ℕ) (p : S → Fin m), IsClopenPartition p → IsSeparatingPartition Λ p →
          ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (complexity (T : Set Λ) p n : ℝ) ≤ C * (n : ℝ) ^ d := by
  obtain ⟨l, hl0, hl1, hlΛ⟩ := exists_small Λ hΛ
  have H : Hyp Λ σ l := ⟨hl0, hl1, hlΛ, dense_of_infinite Λ hΛ, hσ⟩
  have : AddGroup.FG Λ := (AddGroup.fg_iff_addSubgroup_fg Λ).2 hfg
  have : Countable Λ := countable_of_fg Λ
  refine ⟨K σ, Sub H, isCantorSpace_Sub H, isMinimal_Sub H,
    ⟨π H, proj H, continuous_proj H, surjective_proj H, fun g x hx => semiconj H g x hx⟩, ?_⟩
  intro d hd T _ m p hp _
  exact complexity_bound H d hd T p hp

end JMMS

end

open CantorSystems IntervalExchange
theorem solution
    (Λ : AddSubgroup UnitAddCircle) (hΛ : (Λ : Set UnitAddCircle).Infinite) (hfg : Λ.FG)
    (σ : Finset UnitAddCircle) (hσ : σ.Nonempty) :
    ∃ k : ℕ, ∃ S : Subshift Λ (Fin k), IsCantorSpace S ∧ AddAction.IsMinimal Λ S ∧
      (∃ π : topologicalFullGroup Λ S ≃* IETOn Λ σ, ∃ h : S → UnitAddCircle,
        Continuous h ∧ Function.Surjective h ∧
        ∀ (g : topologicalFullGroup Λ S) (x : S), h x ∉ cosetsOf Λ σ →
          h ((g : S ≃ₜ S) x) = (π g : Equiv.Perm UnitAddCircle) (h x)) ∧
      ∀ d : ℕ, rationalRank Λ = d →
        ∀ T : Finset Λ, AddSubgroup.closure (T : Set Λ) = ⊤ →
        ∀ (m : ℕ) (p : S → Fin m), IsClopenPartition p → IsSeparatingPartition Λ p →
          ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (complexity (T : Set Λ) p n : ℝ) ≤ C * (n : ℝ) ^ d :=
  JMMS.chk_exists_isMinimal_subshift_mulEquiv_IETOn_and_complexity_le Λ hΛ hfg σ hσ
