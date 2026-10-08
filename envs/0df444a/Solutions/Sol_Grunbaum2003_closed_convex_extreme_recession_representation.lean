-- Prove2me | solution 1 for Grunbaum2003.closed_convex_extreme_recession_representation
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T17:20:45.685983+00:00
-- url     : https://prove2.me/submissions/2601a388-ee5b-4920-88d9-8ab776ecc1e6

import Definitions.Def_auto_GRUM02ER_1c2100_Grunbaum2003_RecessionDefinitions
import Mathlib

set_option autoImplicit false
open scoped Pointwise

namespace Grunbaum2003
namespace RecessionRep

variable {d : ℕ} {K : Set (Fin d → ℝ)}

/-- If `x ∈ K`, `x + a • w ∈ K` and `0 ≤ t ≤ a`, then `x + t • w ∈ K` (`K` convex). -/
lemma ray_mem (hK : Convex ℝ K) {x w : Fin d → ℝ} {a t : ℝ} (hx : x ∈ K)
    (hy : x + a • w ∈ K) (ha : 0 < a) (ht0 : 0 ≤ t) (hta : t ≤ a) : x + t • w ∈ K := by
  have h := hK.add_smul_sub_mem hx hy (t := t / a) ⟨div_nonneg ht0 ha.le, (div_le_one ha).2 hta⟩
  have e : x + (t / a) • (x + a • w - x) = x + t • w := by
    rw [add_sub_cancel_left, smul_smul, div_mul_cancel₀ t ha.ne']
  rwa [e] at h

/-! ### The characteristic cone -/

lemma cc_zero : (0 : Fin d → ℝ) ∈ characteristicCone K := by
  intro x hx t _
  simpa using hx

lemma cc_add {u v : Fin d → ℝ} (hu : u ∈ characteristicCone K) (hv : v ∈ characteristicCone K) :
    u + v ∈ characteristicCone K := by
  intro x hx t ht
  have h := hv _ (hu x hx t ht) t ht
  convert h using 1
  module

lemma cc_smul {u : Fin d → ℝ} (hu : u ∈ characteristicCone K) {c : ℝ} (hc : 0 ≤ c) :
    c • u ∈ characteristicCone K := by
  intro x hx t ht
  have h := hu x hx (t * c) (mul_nonneg ht hc)
  convert h using 2
  rw [mul_smul]

lemma cc_convex : Convex ℝ (characteristicCone K) := by
  intro u hu v hv a b ha hb _
  exact cc_add (cc_smul hu ha) (cc_smul hv hb)

/-- For a closed convex set, a ray inside the set from one point gives a recession direction. -/
lemma mem_cc_of_ray (hK : Convex ℝ K) (hc : IsClosed K) {x u : Fin d → ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → x + t • u ∈ K) : u ∈ characteristicCone K := by
  intro z hz s hs
  have hlim : Filter.Tendsto (fun t : ℝ => z + s • u + (s / t) • (x - z)) Filter.atTop
      (nhds (z + s • u + (0 : ℝ) • (x - z))) := by
    refine tendsto_const_nhds.add (Filter.Tendsto.smul_const ?_ _)
    exact tendsto_const_nhds.div_atTop Filter.tendsto_id
  rw [zero_smul, add_zero] at hlim
  refine hc.mem_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_ge_atTop (max s 1)] with t ht
  have ht1 : 1 ≤ t := le_trans (le_max_right _ _) ht
  have hts : s ≤ t := le_trans (le_max_left _ _) ht
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht1
  have key : s / t * t = s := div_mul_cancel₀ s ht0.ne'
  have hcomb := hK hz (h t ht0.le) (a := 1 - s / t) (b := s / t)
    (sub_nonneg.2 ((div_le_one ht0).2 hts)) (div_nonneg hs ht0.le) (by ring)
  convert hcomb using 1
  rw [smul_add, smul_smul, key]
  module

/-! ### The subspace of two-sided free directions at a point -/

/-- Directions `w` along which `x` is an interior point of the segment `K ∩ (x + ℝ w)`. -/
def freeDir (K : Set (Fin d → ℝ)) (hK : Convex ℝ K) (x : Fin d → ℝ) (hx : x ∈ K) :
    Submodule ℝ (Fin d → ℝ) where
  carrier := {w | ∃ ε : ℝ, 0 < ε ∧ x + ε • w ∈ K ∧ x - ε • w ∈ K}
  zero_mem' := ⟨1, one_pos, by simpa using hx, by simpa using hx⟩
  add_mem' := by
    rintro w₁ w₂ ⟨ε₁, hε₁, h₁, h₁'⟩ ⟨ε₂, hε₂, h₂, h₂'⟩
    set m := min ε₁ ε₂ with hm
    have hm0 : 0 < m := lt_min hε₁ hε₂
    have hm1 : m ≤ ε₁ := min_le_left _ _
    have hm2 : m ≤ ε₂ := min_le_right _ _
    refine ⟨m / 2, by positivity, ?_, ?_⟩
    · have a1 := ray_mem hK hx h₁ hε₁ hm0.le hm1
      have a2 := ray_mem hK hx h₂ hε₂ hm0.le hm2
      have := hK a1 a2 (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
      convert this using 1
      module
    · have a1 := ray_mem hK hx (w := -w₁) (by simpa [sub_eq_add_neg] using h₁') hε₁ hm0.le hm1
      have a2 := ray_mem hK hx (w := -w₂) (by simpa [sub_eq_add_neg] using h₂') hε₂ hm0.le hm2
      have := hK a1 a2 (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
      convert this using 1
      module
  smul_mem' := by
    rintro c w ⟨ε, hε, h, h'⟩
    rcases lt_trichotomy c 0 with hc | hc | hc
    · have e : ε / -c * c = -ε := by rw [div_neg, neg_mul, div_mul_cancel₀ _ hc.ne]
      refine ⟨ε / (-c), div_pos hε (neg_pos.2 hc), ?_, ?_⟩
      · convert h' using 1
        rw [smul_smul, e]
        module
      · convert h using 1
        rw [smul_smul, e]
        module
    · subst hc
      exact ⟨1, one_pos, by simpa using hx, by simpa using hx⟩
    · have e : ε / c * c = ε := div_mul_cancel₀ _ hc.ne'
      refine ⟨ε / c, div_pos hε hc, ?_, ?_⟩
      · convert h using 1
        rw [smul_smul, e]
      · convert h' using 1
        rw [smul_smul, e]

lemma mem_freeDir {hK : Convex ℝ K} {x : Fin d → ℝ} {hx : x ∈ K} {w : Fin d → ℝ} :
    w ∈ freeDir K hK x hx ↔ ∃ ε : ℝ, 0 < ε ∧ x + ε • w ∈ K ∧ x - ε • w ∈ K := Iff.rfl

/-- A non-extreme point of a convex set has a nonzero free direction. -/
lemma exists_freeDir_of_not_extreme (hK : Convex ℝ K) {x : Fin d → ℝ} (hx : x ∈ K)
    (hne : x ∉ K.extremePoints ℝ) : ∃ v ∈ freeDir K hK x hx, v ≠ 0 := by
  rw [mem_extremePoints] at hne
  push Not at hne
  obtain ⟨x₁, hx₁, x₂, hx₂, hseg, hne'⟩ := hne hx
  obtain ⟨a, b, ha, hb, hab, hxe⟩ := hseg
  have hne12 : x₁ ≠ x₂ := by
    intro h
    subst h
    have : a • x₁ + b • x₁ = x₁ := by rw [← add_smul, hab, one_smul]
    rw [this] at hxe
    exact (hne' hxe) hxe
  refine ⟨x₁ - x₂, ⟨min a b, lt_min ha hb, ?_, ?_⟩, sub_ne_zero.2 hne12⟩
  · have := hK hx₁ hx₂ (a := a + min a b) (b := b - min a b)
      (by have := le_min ha.le hb.le; linarith)
      (by have := min_le_right a b; linarith) (by linarith)
    convert this using 1
    rw [← hxe]
    module
  · have := hK hx₁ hx₂ (a := a - min a b) (b := b + min a b)
      (by have := min_le_left a b; linarith)
      (by have := le_min ha.le hb.le; linarith) (by linarith)
    convert this using 1
    rw [← hxe]
    module

/-- If `x` lies strictly between `p ∈ K` and `y ∈ K` then the free directions at `y`
are free directions at `x`. -/
lemma freeDir_le (hK : Convex ℝ K) {x y p : Fin d → ℝ} (hx : x ∈ K) (hy : y ∈ K) (hp : p ∈ K)
    {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (hxe : x = (1 - l) • p + l • y) :
    freeDir K hK y hy ≤ freeDir K hK x hx := by
  rintro w ⟨ε, hε, h1, h2⟩
  refine ⟨l * ε, by positivity, ?_, ?_⟩
  · have := hK hp h1 (a := 1 - l) (b := l) (by linarith) hl0.le (by ring)
    convert this using 1
    rw [hxe]
    module
  · have := hK hp h2 (a := 1 - l) (b := l) (by linarith) hl0.le (by ring)
    convert this using 1
    rw [hxe]
    module

/-- Moving from `x` in a free direction `v` to the far end `x + t₀ v` of the chord
strictly decreases the free subspace. -/
lemma freeDir_lt_endpoint (hK : Convex ℝ K) {x v : Fin d → ℝ} {t₀ : ℝ} (hx : x ∈ K)
    (hv : v ∈ freeDir K hK x hx) (ht₀ : 0 < t₀) (hy : x + t₀ • v ∈ K)
    (hblock : ∀ t : ℝ, t₀ < t → x + t • v ∉ K) :
    freeDir K hK (x + t₀ • v) hy < freeDir K hK x hx := by
  obtain ⟨ε₀, hε₀, -, hp⟩ := id hv
  have hs : 0 < ε₀ + t₀ := by linarith
  have hl0 : 0 < ε₀ / (ε₀ + t₀) := div_pos hε₀ hs
  have hl1 : ε₀ / (ε₀ + t₀) < 1 := (div_lt_one hs).2 (by linarith)
  have hle : freeDir K hK (x + t₀ • v) hy ≤ freeDir K hK x hx := by
    refine freeDir_le hK hx hy hp hl0 hl1 ?_
    have h1 : (1 - ε₀ / (ε₀ + t₀)) * ε₀ = ε₀ / (ε₀ + t₀) * t₀ := by field_simp; ring
    match_scalars
    · field_simp; ring
    · field_simp; ring
  refine (SetLike.lt_iff_le_and_exists).2 ⟨hle, v, ?_, ?_⟩
  · exact hv
  · rintro ⟨ε, hε, h1, -⟩
    refine hblock (t₀ + ε) (by linarith) ?_
    convert h1 using 1
    module


/-- Along a free direction either the chord has a far endpoint, or the ray stays in `K`. -/
lemma ray_dichotomy (hK : Convex ℝ K) (hc : IsClosed K) {x v : Fin d → ℝ} (hx : x ∈ K)
    (hv : v ∈ freeDir K hK x hx) :
    (∃ t₀ : ℝ, 0 < t₀ ∧ x + t₀ • v ∈ K ∧ ∀ t : ℝ, t₀ < t → x + t • v ∉ K) ∨
      (∀ t : ℝ, 0 ≤ t → x + t • v ∈ K) := by
  obtain ⟨ε, hε, hε1, -⟩ := hv
  set S : Set ℝ := Set.Ici 0 ∩ (fun t : ℝ => x + t • v) ⁻¹' K with hS
  have hSc : IsClosed S :=
    isClosed_Ici.inter (hc.preimage (continuous_const.add (continuous_id.smul continuous_const)))
  have hεS : ε ∈ S := ⟨hε.le, hε1⟩
  by_cases hb : BddAbove S
  · left
    have hmem : sSup S ∈ S := hSc.csSup_mem ⟨ε, hεS⟩ hb
    refine ⟨sSup S, lt_of_lt_of_le hε (le_csSup hb hεS), hmem.2, ?_⟩
    intro t ht hmt
    have : t ∈ S := ⟨le_trans (le_of_lt (lt_of_lt_of_le hε (le_csSup hb hεS))) ht.le, hmt⟩
    exact absurd (le_csSup hb this) (not_le.2 ht)
  · right
    intro t ht
    obtain ⟨s, hs, hts⟩ := not_bddAbove_iff.1 hb t
    exact ray_mem hK hx hs.2 (lt_of_le_of_lt ht hts) ht hts.le

theorem sub_rep (hK : Convex ℝ K) (hc : IsClosed K) (hline : IsLineFree K) :
    ∀ n : ℕ, ∀ (x : Fin d → ℝ) (hx : x ∈ K), Module.finrank ℝ (freeDir K hK x hx) = n →
      x ∈ characteristicCone K + convexHull ℝ (K.extremePoints ℝ) := by
  set A : Set (Fin d → ℝ) := characteristicCone K + convexHull ℝ (K.extremePoints ℝ) with hA
  have hAconv : Convex ℝ A := cc_convex.add (convex_convexHull ℝ _)
  have hAadd : ∀ {u a : Fin d → ℝ}, u ∈ characteristicCone K → a ∈ A → u + a ∈ A := by
    rintro u a hu ⟨c, hcc, h, hh, rfl⟩
    exact ⟨u + c, cc_add hu hcc, h, hh, add_assoc _ _ _⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx hn
    have IH : ∀ y (hy : y ∈ K), Module.finrank ℝ (freeDir K hK y hy) <
        Module.finrank ℝ (freeDir K hK x hx) → y ∈ A := fun y hy hlt =>
      ih _ (hn ▸ hlt) y hy rfl
    by_cases hext : x ∈ K.extremePoints ℝ
    · exact ⟨0, cc_zero, x, subset_convexHull ℝ _ hext, zero_add x⟩
    obtain ⟨v, hv, hv0⟩ := exists_freeDir_of_not_extreme hK hx hext
    have hv' : -v ∈ freeDir K hK x hx := Submodule.neg_mem _ hv
    rcases ray_dichotomy hK hc hx hv with ⟨t₁, ht₁, hy₁, hb₁⟩ | hfree₁ <;>
      rcases ray_dichotomy hK hc hx hv' with ⟨t₂, ht₂, hy₂, hb₂⟩ | hfree₂
    · -- both ends of the chord exist
      have i1 := IH _ hy₁ (Submodule.finrank_lt_finrank_of_lt
        (freeDir_lt_endpoint hK hx hv ht₁ hy₁ hb₁))
      have i2 := IH _ hy₂ (Submodule.finrank_lt_finrank_of_lt
        (freeDir_lt_endpoint hK hx hv' ht₂ hy₂ hb₂))
      have hs : 0 < t₁ + t₂ := by linarith
      have := hAconv i1 i2 (a := t₂ / (t₁ + t₂)) (b := t₁ / (t₁ + t₂))
        (div_nonneg ht₂.le hs.le) (div_nonneg ht₁.le hs.le) (by field_simp; ring)
      convert this using 1
      match_scalars
      · field_simp; ring
      · field_simp; ring
    · -- chord ends at `x + t₁ v`; the opposite ray stays in `K`
      have hcc : -v ∈ characteristicCone K := mem_cc_of_ray hK hc hfree₂
      have i1 := IH _ hy₁ (Submodule.finrank_lt_finrank_of_lt
        (freeDir_lt_endpoint hK hx hv ht₁ hy₁ hb₁))
      have := hAadd (cc_smul hcc ht₁.le) i1
      convert this using 1
      module
    · -- chord ends at `x - t₂ v`; the ray in direction `v` stays in `K`
      have hcc : v ∈ characteristicCone K := mem_cc_of_ray hK hc hfree₁
      have i2 := IH _ hy₂ (Submodule.finrank_lt_finrank_of_lt
        (freeDir_lt_endpoint hK hx hv' ht₂ hy₂ hb₂))
      have := hAadd (cc_smul hcc ht₂.le) i2
      convert this using 1
      module
    · -- a full line through `x` would lie in `K`
      exfalso
      refine hline ⟨x, v, hv0, fun t => ?_⟩
      rcases le_total 0 t with ht | ht
      · exact hfree₁ t ht
      · have := hfree₂ (-t) (by linarith)
        convert this using 1
        module

theorem representation (hK : Convex ℝ K) (hc : IsClosed K) (hline : IsLineFree K) :
    K = characteristicCone K + convexHull ℝ (K.extremePoints ℝ) := by
  refine Set.Subset.antisymm (fun x hx => sub_rep hK hc hline _ x hx rfl) ?_
  rintro _ ⟨u, hu, h, hh, rfl⟩
  have hhK : h ∈ K := convexHull_min extremePoints_subset hK hh
  show u + h ∈ K
  rw [add_comm]
  simpa using hu h hhK 1 zero_le_one

end RecessionRep
end Grunbaum2003

open Grunbaum2003 in
theorem solution {d : ℕ}
    (K : Set (Fin d → ℝ)) (hline : IsLineFree K)
    (hclosed : IsClosed K) (hconvex : Convex ℝ K) :
    K = characteristicCone K + convexHull ℝ (K.extremePoints ℝ) :=
  RecessionRep.representation hconvex hclosed hline
