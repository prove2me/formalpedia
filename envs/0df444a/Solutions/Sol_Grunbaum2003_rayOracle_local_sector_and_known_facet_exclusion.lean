-- Prove2me | solution 1 for Grunbaum2003.rayOracle_local_sector_and_known_facet_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T18:41:33.114059+00:00
-- url     : https://prove2.me/submissions/5ecb3fe6-bd01-4975-b28e-2b98a8a460fa

import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_IsDPolytope
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators

noncomputable section

namespace Grunbaum2003

theorem nonneg_smul_frontier_mem_iff {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {b : Fin d → ℝ} (hb : b ∈ frontier P) {s : ℝ} (hs : 0 ≤ s) :
    s • b ∈ P ↔ s ≤ 1 := by
  constructor
  · intro hsb
    by_contra hle
    have hsone : 1 < s := lt_of_not_ge hle
    have hspos : 0 < s := zero_lt_one.trans hsone
    have hinv : s⁻¹ < 1 := by
      rw [inv_eq_one_div, div_lt_iff₀ hspos]
      simpa only [one_mul] using hsone
    have hi := hconv.combo_interior_self_mem_interior hzero hsb
      (sub_pos.mpr hinv) (inv_nonneg.mpr hspos.le) (sub_add_cancel 1 s⁻¹)
    have hbint : b ∈ interior P := by
      simpa only [smul_zero, zero_add, smul_smul, inv_mul_cancel₀ hspos.ne', one_smul]
        using hi
    exact hb.2 hbint
  · intro hsone
    have hi := hconv (interior_subset hzero) (hclosed.frontier_subset hb)
      (sub_nonneg.mpr hsone) hs (sub_add_cancel 1 s)
    simpa only [smul_zero, zero_add] using hi

theorem frontier_eq_of_pos_smul {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {b c : Fin d → ℝ} (hb : b ∈ frontier P) (hc : c ∈ frontier P)
    {s : ℝ} (hs : 0 < s) (hcb : c = s • b) : c = b := by
  have hsle : s ≤ 1 := (nonneg_smul_frontier_mem_iff hconv hclosed hzero hb hs.le).mp
    (hcb ▸ hclosed.frontier_subset hc)
  have hsge : 1 ≤ s := by
    by_contra h
    have hslt : s < 1 := lt_of_not_ge h
    have hi := hconv.combo_interior_self_mem_interior hzero (hclosed.frontier_subset hb)
      (sub_pos.mpr hslt) hs.le (sub_add_cancel 1 s)
    have hcint : c ∈ interior P := by
      rw [hcb]
      simpa only [smul_zero, zero_add] using hi
    exact hc.2 hcint
  rw [hcb, le_antisymm hsle hsge, one_smul]

theorem rayOracle_eq_at_nonzero {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle₁ oracle₂ : (Fin d → ℝ) → (Fin d → ℝ)}
    (h₁ : IsPolytopeRayOracle P oracle₁) (h₂ : IsPolytopeRayOracle P oracle₂)
    {x : Fin d → ℝ} (hx : x ≠ 0) : oracle₁ x = oracle₂ x := by
  obtain ⟨hb, t, ht, hbt⟩ := h₁ x hx
  obtain ⟨hc, u, hu, hcu⟩ := h₂ x hx
  apply frontier_eq_of_pos_smul hconv hclosed hzero hc hb (div_pos ht hu)
  rw [hbt, hcu, smul_smul, div_mul_cancel₀ t hu.ne']

theorem rayOracle_mem_iff_coordinate_ratio {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (x : Fin d → ℝ) (j : Fin d) (hxj : x j ≠ 0) :
    x ∈ P ↔ 1 ≤ oracle x j / x j := by
  have hx : x ≠ 0 := by
    intro h
    exact hxj (congrFun h j)
  obtain ⟨hb, t, ht, hbt⟩ := horacle x hx
  have hxscale : x = t⁻¹ • oracle x := by
    rw [hbt, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  have hratio : oracle x j / x j = t := by
    rw [hbt]
    change (t * x j) / x j = t
    exact mul_div_cancel_right₀ t hxj
  rw [hratio, hxscale, nonneg_smul_frontier_mem_iff hconv hclosed hzero hb
    (inv_nonneg.mpr ht.le)]
  rw [inv_eq_one_div, div_le_iff₀ ht]
  simp only [one_mul]

theorem rayOracle_eq_self_iff_frontier {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    {x : Fin d → ℝ} (hx : x ≠ 0) :
    oracle x = x ↔ x ∈ frontier P := by
  constructor
  · intro heq
    exact heq ▸ (horacle x hx).1
  · intro hxfront
    obtain ⟨hb, t, ht, hbt⟩ := horacle x hx
    exact frontier_eq_of_pos_smul hconv hclosed hzero hxfront hb ht hbt

end Grunbaum2003

namespace Grunbaum2003

theorem rayOracle_outer_vertex_fixed_iff {d : ℕ} (hd : 0 < d)
    {P Q : Set (Fin d → ℝ)} (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P) (hPQ : P ⊆ Q)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    {x : Fin d → ℝ} (hx : x ∈ Q.extremePoints ℝ) :
    x ≠ 0 ∧ (oracle x = x ↔ x ∈ P.extremePoints ℝ) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hzeroQ : (0 : Fin d → ℝ) ∈ interior Q := interior_mono hPQ hzero
  have hxne : x ≠ 0 := by
    intro heq
    have hzext : (0 : Fin d → ℝ) ∈ Q.extremePoints ℝ := heq ▸ hx
    exact Set.disjoint_left.mp (disjoint_interior_extremePoints Q) hzeroQ hzext
  refine ⟨hxne, ?_⟩
  constructor
  · intro hfixed
    have hxP : x ∈ P := hclosed.frontier_subset
      ((rayOracle_eq_self_iff_frontier hconv hclosed hzero horacle hxne).mp hfixed)
    exact isExtreme_singleton.mp
      ((isExtreme_singleton.mpr hx).mono hPQ (Set.singleton_subset_iff.mpr hxP))
  · intro hxP
    have hxNot : x ∉ interior P := by
      intro hi
      exact Set.disjoint_left.mp (disjoint_interior_extremePoints P) hi hxP
    have hxFront : x ∈ frontier P :=
      (mem_frontier_iff_notMem_interior (extremePoints_subset hxP)).mpr hxNot
    exact (rayOracle_eq_self_iff_frontier hconv hclosed hzero horacle hxne).mpr hxFront

end Grunbaum2003

namespace Grunbaum2003

theorem perturb_frontier_ne_zero_of_negative_mem {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) (hsa : s < a)
    (hminus : (-a) • u ∈ P) : p + s • u ≠ 0 := by
  intro hz
  have hc : 0 ≤ s / a := div_nonneg hs ha.le
  have hc1 : s / a < 1 := (div_lt_one ha).mpr hsa
  have hi := hconv.combo_interior_self_mem_interior hzero hminus
    (sub_pos.mpr hc1) hc (sub_add_cancel 1 (s / a))
  have heq : (s / a) • ((-a) • u) = p := by
    ext j
    have hj := congrFun hz j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj ⊢
    field_simp
    nlinarith only [hj]
  have hpint : p ∈ interior P := by
    simpa only [smul_zero, zero_add, heq] using hi
  exact hp.2 hpint

theorem rayOracle_perturb_scale_upper {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) (hsa : s < a)
    (hminus : (-a) • u ∈ P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    ∃ t : ℝ, 0 < t ∧ oracle (p + s • u) = t • (p + s • u) ∧
      t * (a - s) ≤ a := by
  have hr := perturb_frontier_ne_zero_of_negative_mem hconv hclosed hzero hp ha hs hsa hminus
  obtain ⟨hq, t, ht, heq⟩ := horacle (p + s • u) hr
  refine ⟨t, ht, heq, ?_⟩
  have hden : 0 < a + t * s := add_pos_of_pos_of_nonneg ha (mul_nonneg ht.le hs)
  have hc : 0 ≤ a / (a + t * s) := div_nonneg ha.le hden.le
  have hc1 : a / (a + t * s) ≤ 1 := (div_le_one hden).mpr (by linarith [mul_nonneg ht.le hs])
  have hcombo := hconv (hclosed.frontier_subset hq) hminus hc
    (sub_nonneg.mpr hc1) (add_sub_cancel (a / (a + t * s)) 1)
  have hceq : (a / (a + t * s)) • oracle (p + s • u) +
      (1 - a / (a + t * s)) • ((-a) • u) =
      (t * a / (a + t * s)) • p := by
    rw [heq]
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    <;> ring
  rw [hceq] at hcombo
  have hscaleNonneg : 0 ≤ t * a / (a + t * s) :=
    div_nonneg (mul_nonneg ht.le ha.le) hden.le
  have hscaleLe := (nonneg_smul_frontier_mem_iff hconv hclosed hzero hp hscaleNonneg).mp hcombo
  have hnum : t * a ≤ a + t * s := (div_le_one hden).mp hscaleLe
  nlinarith only [hnum]

theorem facet_local_step_bounds {a δ M : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M) :
    let ε := a * δ / (2 * (1 + a * M + δ))
    0 < ε ∧ ε < a ∧ ε * (1 + a * M) < a * δ := by
  have haM : 0 ≤ a * M := mul_nonneg ha.le hM
  have hD : 0 < 2 * (1 + a * M + δ) := by linarith
  dsimp only
  refine ⟨div_pos (mul_pos ha hδ) hD, ?_, ?_⟩
  · apply (div_lt_iff₀ hD).mpr
    have hh : δ < 2 * (1 + a * M + δ) := by linarith
    exact mul_lt_mul_of_pos_left hh ha
  · rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hD).mpr
    have hh : 1 + a * M < 2 * (1 + a * M + δ) := by linarith
    exact mul_lt_mul_of_pos_left hh (mul_pos ha hδ)

theorem rayOracle_perturb_avoids_halfspace_boundary {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a δ M s : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hminus : (-a) • u ∈ P)
    (ℓ : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hpSlack : ℓ p ≤ 1 - δ) (huBound : ℓ u ≤ M)
    (hs : 0 ≤ s) (hsε : s ≤ a * δ / (2 * (1 + a * M + δ)))
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    p + s • u ≠ 0 ∧ ℓ (oracle (p + s • u)) < 1 := by
  obtain ⟨hεpos, hεa, hεgap⟩ := facet_local_step_bounds ha hδ hM
  have hsa : s < a := hsε.trans_lt hεa
  have hr := perturb_frontier_ne_zero_of_negative_mem hconv hclosed hzero hp ha hs hsa hminus
  refine ⟨hr, ?_⟩
  obtain ⟨t, ht, heq, hupper⟩ :=
    rayOracle_perturb_scale_upper hconv hclosed hzero hp ha hs hsa hminus horacle
  have hgap : s * (1 + a * M) < a * δ :=
    (mul_le_mul_of_nonneg_right hsε (by positivity)).trans_lt hεgap
  have hbase : a * (1 - δ + s * M) < a - s := by
    nlinarith only [hgap]
  have hℓ : ℓ p + s * ℓ u ≤ 1 - δ + s * M :=
    add_le_add hpSlack (mul_le_mul_of_nonneg_left huBound hs)
  have hℓa : a * (ℓ p + s * ℓ u) < a - s :=
    (mul_le_mul_of_nonneg_left hℓ ha.le).trans_lt hbase
  have hscaled : a * (t * (ℓ p + s * ℓ u)) < a := by
    calc
      a * (t * (ℓ p + s * ℓ u)) = t * (a * (ℓ p + s * ℓ u)) := by ring
      _ < t * (a - s) := mul_lt_mul_of_pos_left hℓa ht
      _ ≤ a := hupper
  rw [heq, map_smul, map_add, map_smul]
  change t * (ℓ p + s * ℓ u) < 1
  nlinarith only [ha, hscaled]

theorem rayOracle_perturb_avoids_known_facets {d : ℕ} {ι : Type*}
    {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a δ M s : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hminus : (-a) • u ∈ P) (hplus : a • u ∈ P)
    (L : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hpSlack : ∀ j, L j p ≤ 1 - δ) (huBound : ∀ j, |L j u| ≤ M)
    (hsε : |s| ≤ a * δ / (2 * (1 + a * M + δ)))
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    p + s • u ≠ 0 ∧ ∀ j, L j (oracle (p + s • u)) < 1 := by
  have hsa : |s| < a := hsε.trans_lt (facet_local_step_bounds ha hδ hM).2.1
  by_cases hs : 0 ≤ s
  · have hsε' : s ≤ a * δ / (2 * (1 + a * M + δ)) :=
      (le_abs_self s).trans hsε
    refine ⟨perturb_frontier_ne_zero_of_negative_mem hconv hclosed hzero hp ha hs
      ((le_abs_self s).trans_lt hsa) hminus, ?_⟩
    intro j
    exact (rayOracle_perturb_avoids_halfspace_boundary hconv hclosed hzero hp
      ha hδ hM hminus (L j) (hpSlack j) ((le_abs_self _).trans (huBound j))
      hs hsε' horacle).2
  · have hs' : 0 ≤ -s := by linarith
    have hsε' : -s ≤ a * δ / (2 * (1 + a * M + δ)) :=
      (neg_le_abs s).trans hsε
    have hsa' : -s < a := (neg_le_abs s).trans_lt hsa
    have hminus' : (-a) • (-u) ∈ P := by
      simpa only [smul_neg, neg_smul, neg_neg] using hplus
    have heq : p + (-s) • (-u) = p + s • u := by
      simp only [smul_neg, neg_smul, neg_neg]
    refine ⟨heq ▸ perturb_frontier_ne_zero_of_negative_mem hconv hclosed hzero hp
      ha hs' hsa' hminus', ?_⟩
    intro j
    have huBound' : L j (-u) ≤ M := by
      rw [map_neg]
      exact (neg_le_abs _).trans (huBound j)
    have h := (rayOracle_perturb_avoids_halfspace_boundary hconv hclosed hzero hp
      ha hδ hM hminus' (L j) (hpSlack j) huBound' hs' hsε' horacle).2
    simpa only [heq] using h

end Grunbaum2003

namespace Grunbaum2003

theorem rayOracle_pos_smul_eq {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    {x : Fin d → ℝ} (hx : x ≠ 0) {c : ℝ} (hc : 0 < c) :
    oracle (c • x) = oracle x := by
  have hcx : c • x ≠ 0 := smul_ne_zero hc.ne' hx
  obtain ⟨hq, t, ht, hqt⟩ := horacle (c • x) hcx
  obtain ⟨hp, s, hs, hps⟩ := horacle x hx
  apply frontier_eq_of_pos_smul hconv hclosed hzero hp hq (div_pos (mul_pos ht hc) hs)
  rw [hqt, hps, smul_smul, smul_smul, div_mul_cancel₀ _ hs.ne']

theorem facet_local_step_lt_half {a δ M : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M) :
    a * δ / (2 * (1 + a * M + δ)) < a / 2 := by
  have hden : 0 < 2 * (1 + a * M + δ) := by positivity
  apply (div_lt_iff₀ hden).mpr
  have hm : 0 ≤ a * M := mul_nonneg ha.le hM
  have hh : δ < 1 + a * M + δ := by linarith
  have hk := mul_lt_mul_of_pos_left hh ha
  nlinarith only [hk]

theorem scaled_planar_first_two_queries_avoid_known_facets {d : ℕ} {ι : Type*}
    {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a δ M : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hminus : (-a) • u ∈ P) (hplus : a • u ∈ P)
    (L : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hpSlack : ∀ j, L j p ≤ 1 - δ) (huBound : ∀ j, |L j u| ≤ M)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    let ε := a * δ / (2 * (1 + a * M + δ))
    p - ε • u ≠ 0 ∧
    ∃ τ : ℝ, 0 < τ ∧ τ < 2 ∧
      oracle (p - ε • u) = τ • (p - ε • u) ∧
      (∀ j, L j (oracle (p - ε • u)) < 1) ∧
      let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
      r₂ ≠ 0 ∧ (∀ j, L j (oracle r₂) < 1) := by
  dsimp only
  let ε := a * δ / (2 * (1 + a * M + δ))
  have hε : 0 < ε := (facet_local_step_bounds ha hδ hM).1
  have hεhalf : ε < a / 2 := facet_local_step_lt_half ha hδ hM
  have hfirst := rayOracle_perturb_avoids_known_facets hconv hclosed hzero hp
    ha hδ hM hminus hplus L hpSlack huBound
    (s := -ε) (by rw [abs_neg, abs_of_pos hε]) horacle
  have heq₁ : p + (-ε) • u = p - ε • u := by simp only [neg_smul, sub_eq_add_neg]
  rw [heq₁] at hfirst
  refine ⟨hfirst.1, ?_⟩
  obtain ⟨hq, τ, hτ, hreply⟩ := horacle (p - ε • u) hfirst.1
  have hminus' : (-a) • (-u) ∈ P := by simpa only [smul_neg, neg_smul, neg_neg] using hplus
  have hεa : ε < a := (facet_local_step_bounds ha hδ hM).2.1
  obtain ⟨t, ht, hteq, hupper⟩ := rayOracle_perturb_scale_upper hconv hclosed hzero hp
    ha hε.le hεa hminus' horacle
  have heq₂ : p + ε • (-u) = p - ε • u := by simp only [smul_neg, sub_eq_add_neg]
  rw [heq₂] at hteq
  have htτ : t = τ := by
    apply (smul_left_injective ℝ hfirst.1)
    exact hteq.symm.trans hreply
  rw [htτ] at hupper
  have hτtwo : τ < 2 := by
    have hm := mul_lt_mul_of_pos_left hεhalf hτ
    nlinarith only [hupper, hm, ha]
  refine ⟨τ, hτ, hτtwo, hreply, hfirst.2, ?_⟩
  let s₂ := τ * ε / 2
  have hs₂ : 0 ≤ s₂ := by dsimp [s₂]; positivity
  have hs₂ε : s₂ ≤ ε := by
    dsimp only [s₂]
    have hm := mul_lt_mul_of_pos_right hτtwo hε
    linarith
  have hsafe := rayOracle_perturb_avoids_known_facets hconv hclosed hzero hp
    ha hδ hM hminus hplus L hpSlack huBound
    (s := s₂) (by rw [abs_of_nonneg hs₂]; exact hs₂ε) horacle
  have hc : 0 < 2 / (1 + τ) := by positivity
  have hr₂ : (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p =
      (2 / (1 + τ)) • (p + s₂ • u) := by
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    dsimp only [s₂]
    ring
  rw [hr₂]
  refine ⟨smul_ne_zero hc.ne' hsafe.1, ?_⟩
  rw [rayOracle_pos_smul_eq hconv hclosed hzero horacle hsafe.1 hc]
  exact hsafe.2

end Grunbaum2003

namespace Grunbaum2003

theorem rayOracle_local_cone_avoids_known_facets {d : ℕ} {ι : Type*}
    {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a δ M α β : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hminus : (-a) • u ∈ P) (hplus : a • u ∈ P)
    (L : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hpSlack : ∀ j, L j p ≤ 1 - δ) (huBound : ∀ j, |L j u| ≤ M)
    (hα : 0 < α) (hβ : |β| ≤ α * (a * δ / (2 * (1 + a * M + δ))))
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    α • p + β • u ≠ 0 ∧ ∀ j, L j (oracle (α • p + β • u)) < 1 := by
  have hs : |β / α| ≤ a * δ / (2 * (1 + a * M + δ)) := by
    rw [abs_div, abs_of_pos hα]
    apply (div_le_iff₀ hα).mpr
    simpa only [mul_comm] using hβ
  have hsafe := rayOracle_perturb_avoids_known_facets hconv hclosed hzero hp
    ha hδ hM hminus hplus L hpSlack huBound hs horacle
  have heq : α • p + β • u = α • (p + (β / α) • u) := by
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    <;> ring
  rw [heq]
  refine ⟨smul_ne_zero hα.ne' hsafe.1, ?_⟩
  rw [rayOracle_pos_smul_eq hconv hclosed hzero horacle hsafe.1 hα]
  exact hsafe.2

theorem local_cone_convex_coefficients {α β γ η ε θ : ℝ}
    (hα : 0 < α) (hγ : 0 < γ)
    (hβ : |β| ≤ α * ε) (hη : |η| ≤ γ * ε)
    (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    0 < (1 - θ) * α + θ * γ ∧
      |(1 - θ) * β + θ * η| ≤ ((1 - θ) * α + θ * γ) * ε := by
  have hcomp : 0 ≤ 1 - θ := sub_nonneg.mpr hθone
  constructor
  · by_cases hz : θ = 0
    · simpa only [hz, sub_zero, one_mul, zero_mul, add_zero] using hα
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hcomp hα.le)
        (mul_pos (lt_of_le_of_ne hθ (Ne.symm hz)) hγ)
  · calc
      |(1 - θ) * β + θ * η| ≤ |(1 - θ) * β| + |θ * η| := abs_add_le _ _
      _ = (1 - θ) * |β| + θ * |η| := by
        rw [abs_mul, abs_of_nonneg hcomp, abs_mul, abs_of_nonneg hθ]
      _ ≤ (1 - θ) * (α * ε) + θ * (γ * ε) :=
        add_le_add (mul_le_mul_of_nonneg_left hβ hcomp)
          (mul_le_mul_of_nonneg_left hη hθ)
      _ = ((1 - θ) * α + θ * γ) * ε := by ring

theorem rayOracle_safe_reference_segment {d : ℕ} {ι : Type*}
    {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a δ M α β γ η θ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hminus : (-a) • u ∈ P) (hplus : a • u ∈ P)
    (L : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hpSlack : ∀ j, L j p ≤ 1 - δ) (huBound : ∀ j, |L j u| ≤ M)
    (hα : 0 < α) (hγ : 0 < γ)
    (hβ : |β| ≤ α * (a * δ / (2 * (1 + a * M + δ))))
    (hη : |η| ≤ γ * (a * δ / (2 * (1 + a * M + δ))))
    (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    let r := (1 - θ) • (α • p + β • u) + θ • (γ • p + η • u)
    r ≠ 0 ∧ ∀ j, L j (oracle r) < 1 := by
  obtain ⟨hpos, hbound⟩ := local_cone_convex_coefficients hα hγ hβ hη hθ hθone
  have hsafe := rayOracle_local_cone_avoids_known_facets hconv hclosed hzero hp
    ha hδ hM hminus hplus L hpSlack huBound hpos hbound horacle
  have heq : (1 - θ) • (α • p + β • u) + θ • (γ • p + η • u) =
      ((1 - θ) * α + θ * γ) • p + ((1 - θ) * β + θ * η) • u := by
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simpa only [heq] using hsafe

end Grunbaum2003

namespace Grunbaum2003.RayPlanar

theorem known_slack_product_bounds {k : ℕ} (s : Fin k → ℝ) (hs : ∀ j, 0 < s j) :
    let δ := ∏ j, s j / (1 + s j)
    0 < δ ∧ ∀ j, δ ≤ s j := by
  have hden : ∀ j, 0 < 1 + s j := fun j => by linarith only [hs j]
  have hfactor : ∀ j, 0 < s j / (1 + s j) := fun j => div_pos (hs j) (hden j)
  have hfactorOne : ∀ j, s j / (1 + s j) ≤ 1 := by
    intro j
    apply (div_le_one (hden j)).mpr
    linarith
  have hfactorSlack : ∀ j, s j / (1 + s j) ≤ s j := by
    intro j
    apply (div_le_iff₀ (hden j)).mpr
    nlinarith only [sq_nonneg (s j)]
  dsimp only
  refine ⟨Finset.prod_pos (fun j _ => hfactor j), ?_⟩
  intro j
  have hrest : (∏ i ∈ Finset.univ.erase j, s i / (1 + s i)) ≤ 1 :=
    Finset.prod_le_one (fun i _ => (hfactor i).le) (fun i _ => hfactorOne i)
  rw [← Finset.mul_prod_erase Finset.univ (fun i => s i / (1 + s i)) (Finset.mem_univ j)]
  exact (mul_le_mul_of_nonneg_left hrest (hfactor j).le).trans (by simpa only [mul_one] using hfactorSlack j)

theorem known_direction_square_sum_bounds {k : ℕ} (v : Fin k → ℝ) :
    0 ≤ 1 + ∑ j, (v j) ^ 2 ∧ ∀ j, |v j| ≤ 1 + ∑ i, (v i) ^ 2 := by
  have hsum : 0 ≤ ∑ j, (v j) ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg (v j))
  refine ⟨by linarith only [hsum], ?_⟩
  intro j
  have hsingle : (v j) ^ 2 ≤ ∑ i, (v i) ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (v i)) (Finset.mem_univ j)
  have habs : |v j| ≤ 1 + (v j) ^ 2 := by
    apply abs_le.mpr
    constructor
    · nlinarith only [sq_nonneg (v j + 1 / 2)]
    · nlinarith only [sq_nonneg (v j - 1 / 2)]
  linarith only [habs, hsingle]

theorem known_facet_field_parameters {d k : ℕ}
    (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ) (p u : Fin d → ℝ)
    (hstrict : ∀ j, L j p < 1) :
    let δ := ∏ j, (1 - L j p) / (1 + (1 - L j p))
    let M := 1 + ∑ j, (L j u) ^ 2
    0 < δ ∧ 0 ≤ M ∧ (∀ j, L j p ≤ 1 - δ) ∧ (∀ j, |L j u| ≤ M) := by
  obtain ⟨hδ, hδbound⟩ := known_slack_product_bounds (fun j => 1 - L j p)
    (fun j => sub_pos.mpr (hstrict j))
  obtain ⟨hM, hMbound⟩ := known_direction_square_sum_bounds (fun j => L j u)
  refine ⟨hδ, hM, ?_, hMbound⟩
  intro j
  have hj := hδbound j
  linarith only [hj]

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

theorem rayOracle_scale_lt_one_of_not_mem {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    {x : Fin d → ℝ} (hx : x ≠ 0) (hxP : x ∉ P) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ oracle x = t • x := by
  obtain ⟨hq, t, ht, heq⟩ := horacle x hx
  refine ⟨t, ht, ?_, heq⟩
  by_contra hn
  have htge : 1 ≤ t := le_of_not_gt hn
  have hsnonneg : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.le
  have hsle : t⁻¹ ≤ 1 := by
    rw [inv_eq_one_div, div_le_one ht]
    exact htge
  have hscaled := (nonneg_smul_frontier_mem_iff hconv hclosed hzero hq hsnonneg).mpr hsle
  have hxmem : x ∈ P := by
    simpa only [heq, smul_smul, inv_mul_cancel₀ ht.ne', one_smul] using hscaled
  exact hxP hxmem

theorem outer_vertex_probe_known_facets_strict {d k : ℕ} (hd : 0 < d)
    {P Q : Set (Fin d → ℝ)} (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P) (hPQ : P ⊆ Q)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    {x : Fin d → ℝ} (hx : x ∈ Q.extremePoints ℝ) (hnonfixed : oracle x ≠ x)
    (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ) (hxBound : ∀ j, L j x ≤ 1) :
    x ≠ 0 ∧ (∀ j, L j (oracle x) < 1) := by
  obtain ⟨hxne, hfixed⟩ := rayOracle_outer_vertex_fixed_iff hd hconv hclosed hzero hPQ horacle hx
  have hxNotP : x ∉ P := by
    intro hxP
    apply hnonfixed
    apply hfixed.mpr
    exact isExtreme_singleton.mp
      ((isExtreme_singleton.mpr hx).mono hPQ (Set.singleton_subset_iff.mpr hxP))
  obtain ⟨t, ht, htone, heq⟩ := rayOracle_scale_lt_one_of_not_mem hconv hclosed hzero horacle hxne hxNotP
  refine ⟨hxne, ?_⟩
  intro j
  rw [heq, map_smul]
  change t * L j x < 1
  exact (mul_le_mul_of_nonneg_left (hxBound j) ht.le).trans_lt (by simpa only [mul_one] using htone)

theorem rayOracle_known_nonpositive_direction_strict {d k : ℕ}
    {P : Set (Fin d → ℝ)}
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    {x : Fin d → ℝ} (hx : x ≠ 0) (hdir : ∀ j, L j x ≤ 0) :
    ∀ j, L j (oracle x) < 1 := by
  obtain ⟨_, t, ht, heq⟩ := horacle x hx
  intro j
  rw [heq, map_smul]
  change t * L j x < 1
  have hle : t * L j x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le (hdir j)
  linarith only [hle]

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

theorem convex_secant_zero_progress {h : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ h) (hzero : h 0 = 0)
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) (hhx : 0 < h x) :
    0 < h y - h x ∧
      0 ≤ (x * h y - y * h x) / (h y - h x) ∧
      (x * h y - y * h x) / (h y - h x) < x := by
  have hcross := hconv.secant_mono_aux1 (Set.mem_univ 0) (Set.mem_univ y) hx hxy
  simp only [sub_zero, hzero, mul_zero, zero_add] at hcross
  have hprod : 0 < (y - x) * h x := mul_pos (sub_pos.mpr hxy) hhx
  have hden : 0 < h y - h x := by
    by_contra hn
    have hle : h y ≤ h x := by linarith
    have hmul := mul_le_mul_of_nonneg_left hle hx.le
    nlinarith only [hcross, hprod, hmul]
  refine ⟨hden, div_nonneg (by linarith only [hcross]) hden.le, ?_⟩
  apply (div_lt_iff₀ hden).mpr
  nlinarith only [hprod]

theorem secant_zero_of_common_affine_piece {h : ℝ → ℝ} {x y a b : ℝ}
    (hden : h y - h x ≠ 0)
    (hx : h x = a * x + b) (hy : h y = a * y + b) :
    a * ((x * h y - y * h x) / (h y - h x)) + b = 0 := by
  have hz : ((x * h y - y * h x) / (h y - h x)) * (h y - h x) =
      x * h y - y * h x := div_mul_cancel₀ _ hden
  have hp : (a * ((x * h y - y * h x) / (h y - h x)) + b) *
      (h y - h x) = 0 := by
    calc
      _ = a * (((x * h y - y * h x) / (h y - h x)) * (h y - h x)) +
          b * (h y - h x) := by ring
      _ = a * (x * h y - y * h x) + b * (h y - h x) := by rw [hz]
      _ = 0 := by rw [hx, hy]; ring
  exact (mul_eq_zero.mp hp).resolve_right hden

theorem convex_affine_piece_active_between {h : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ h) {a b x z y : ℝ}
    (hmajor : ∀ t, a * t + b ≤ h t)
    (hx : h x = a * x + b) (hy : h y = a * y + b)
    (hxz : x ≤ z) (hzy : z ≤ y) : h z = a * z + b := by
  rcases eq_or_lt_of_le hxz with rfl | hxz
  · exact hx
  rcases eq_or_lt_of_le hzy with rfl | hzy
  · exact hy
  apply le_antisymm ?_ (hmajor z)
  have hk := hconv.secant_mono_aux1 (Set.mem_univ x) (Set.mem_univ y) hxz hzy
  rw [hx, hy] at hk
  by_contra hn
  have hp : 0 < (y - x) * (h z - (a * z + b)) :=
    mul_pos (sub_pos.mpr (hxz.trans hzy)) (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith only [hk, hp]

theorem third_secant_response_leaves_common_piece {h : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ h) (hzero : h 0 = 0)
    {x y a b : ℝ} (hx : 0 < x) (hxy : x < y) (hhx : 0 < h x)
    (hax : h x = a * x + b) (hay : h y = a * y + b)
    (hnext : 0 < h ((x * h y - y * h x) / (h y - h x))) :
    h ((x * h y - y * h x) / (h y - h x)) ≠
      a * ((x * h y - y * h x) / (h y - h x)) + b := by
  have hden := (convex_secant_zero_progress hconv hzero hx hxy hhx).1
  have hz := secant_zero_of_common_affine_piece hden.ne' hax hay
  rw [hz]
  exact ne_of_gt hnext

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

def finiteAffineEnvelope {m : ℕ} (hm : 0 < m) (a b : Fin m → ℝ) (x : ℝ) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun j => a j * x + b j)

lemma finiteAffineEnvelope_major {m : ℕ} (hm : 0 < m) (a b : Fin m → ℝ)
    (j : Fin m) (x : ℝ) : a j * x + b j ≤ finiteAffineEnvelope hm a b x :=
  Finset.le_sup' (fun k => a k * x + b k) (Finset.mem_univ j)

lemma finiteAffineEnvelope_attained {m : ℕ} (hm : 0 < m) (a b : Fin m → ℝ)
    (x : ℝ) : ∃ j, finiteAffineEnvelope hm a b x = a j * x + b j := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Fin m))) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    (fun j => a j * x + b j)
  exact ⟨j, hj⟩

lemma finiteAffineEnvelope_convex {m : ℕ} (hm : 0 < m) (a b : Fin m → ℝ) :
    ConvexOn ℝ Set.univ (finiteAffineEnvelope hm a b) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ α β hα hβ hab
  simp only [smul_eq_mul]
  apply Finset.sup'_le
  intro j _
  have hx := finiteAffineEnvelope_major hm a b j x
  have hy := finiteAffineEnvelope_major hm a b j y
  calc
    a j * (α * x + β * y) + b j =
        α * (a j * x + b j) + β * (a j * y + b j) := by
      linear_combination -b j * hab
    _ ≤ α * finiteAffineEnvelope hm a b x + β * finiteAffineEnvelope hm a b y :=
      add_le_add (mul_le_mul_of_nonneg_left hx hα) (mul_le_mul_of_nonneg_left hy hβ)

theorem frontier_finite_halfspaces_active {d m : ℕ}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    {q : Fin d → ℝ} (hq : q ∈ frontier P) :
    (∀ j, L j q ≤ 1) ∧ ∃ j, L j q = 1 := by
  have hclosed : IsClosed P := by
    rw [hP, Set.ofPred_forall]
    exact isClosed_iInter (fun j => isClosed_le (L j).continuous continuous_const)
  have hle : ∀ j, L j q ≤ 1 := by
    have hmem := hclosed.frontier_subset hq
    rwa [hP] at hmem
  refine ⟨hle, ?_⟩
  by_contra hn
  have hlt : ∀ j, L j q < 1 := by
    intro j
    exact lt_of_le_of_ne (hle j) (by intro heq; exact hn ⟨j, heq⟩)
  have hopen : IsOpen {x : Fin d → ℝ | ∀ j, L j x < 1} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun j => isOpen_lt (L j).continuous continuous_const)
  have hsub : {x : Fin d → ℝ | ∀ j, L j x < 1} ⊆ P := by
    intro x hx
    rw [hP]
    exact fun j => (hx j).le
  exact hq.2 (interior_maximal hsub hopen hlt)

theorem rayOracle_halfspace_envelope_eq {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p u : Fin d → ℝ) (x : ℝ) (hr : p + x • u ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ oracle (p + x • u) = t • (p + x • u) ∧
      finiteAffineEnvelope hm (fun j => L j u) (fun j => L j p - 1) x = 1 / t - 1 := by
  obtain ⟨hq, t, ht, heq⟩ := horacle (p + x • u) hr
  obtain ⟨hineq, j, hj⟩ := frontier_finite_halfspaces_active L hP hq
  refine ⟨t, ht, heq, le_antisymm ?_ ?_⟩
  · apply Finset.sup'_le
    intro k _
    have hk := hineq k
    rw [heq, map_smul, map_add, map_smul] at hk
    change t * (L k p + x * L k u) ≤ 1 at hk
    have hdiv : L k p + x * L k u ≤ 1 / t := (le_div_iff₀ ht).mpr (by nlinarith only [hk])
    linarith only [hdiv]
  · have hj' := hj
    rw [heq, map_smul, map_add, map_smul] at hj'
    change t * (L j p + x * L j u) = 1 at hj'
    have hdiv : L j p + x * L j u = 1 / t := (eq_div_iff ht.ne').mpr (by nlinarith only [hj'])
    have hmajor := finiteAffineEnvelope_major hm (fun k => L k u) (fun k => L k p - 1) j x
    linarith only [hdiv, hmajor]

theorem halfspace_envelope_zero_at_boundary {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    (p u : Fin d → ℝ) (hp : p ∈ frontier P) :
    finiteAffineEnvelope hm (fun j => L j u) (fun j => L j p - 1) 0 = 0 := by
  obtain ⟨hle, j, hj⟩ := frontier_finite_halfspaces_active L hP hp
  apply le_antisymm
  · apply Finset.sup'_le
    intro k _
    dsimp only
    simp only [mul_zero, zero_add]
    linarith only [hle k]
  · have h := finiteAffineEnvelope_major hm (fun k => L k u) (fun k => L k p - 1) j 0
    simpa only [mul_zero, zero_add, hj, sub_self] using h

theorem convex_gap_nonneg_positive_of_negative_zero {h : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ h) (hzero : h 0 = 0)
    {z x : ℝ} (hz : z < 0) (hzval : h z = 0) (hx : 0 ≤ x) : 0 ≤ h x := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simpa only [hzero] using (le_refl (0 : ℝ))
  have hk := hconv.secant_mono_aux1 (Set.mem_univ z) (Set.mem_univ x) hz hx
  rw [hzero, hzval] at hk
  simp only [mul_zero, add_zero, zero_add, zero_sub] at hk
  by_contra hn
  have hp : 0 < (-z) * (-h x) := mul_pos (neg_pos.mpr hz) (neg_pos.mpr (lt_of_not_ge hn))
  nlinarith only [hk, hp]

theorem rayOracle_active_halfspace_envelope {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p u : Fin d → ℝ) (x : ℝ) (hr : p + x • u ≠ 0)
    (j : Fin m) (hj : L j (oracle (p + x • u)) = 1) :
    finiteAffineEnvelope hm (fun k => L k u) (fun k => L k p - 1) x =
      L j u * x + (L j p - 1) := by
  obtain ⟨t, ht, heq, henv⟩ := rayOracle_halfspace_envelope_eq hm L hP horacle p u x hr
  rw [heq, map_smul, map_add, map_smul] at hj
  change t * (L j p + x * L j u) = 1 at hj
  have hdiv : L j p + x * L j u = 1 / t := (eq_div_iff ht.ne').mpr (by nlinarith only [hj])
  linarith only [henv, hdiv]

theorem rayOracle_common_halfspace_opposite_sides_incident {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p u : Fin d → ℝ) (hp : p ∈ frontier P)
    {x y : ℝ} (hx : x < 0) (hy : 0 < y)
    (hrx : p + x • u ≠ 0) (hry : p + y • u ≠ 0)
    (j : Fin m)
    (hjx : L j (oracle (p + x • u)) = 1)
    (hjy : L j (oracle (p + y • u)) = 1) : L j p = 1 := by
  have hax := rayOracle_active_halfspace_envelope hm L hP horacle p u x hrx j hjx
  have hay := rayOracle_active_halfspace_envelope hm L hP horacle p u y hry j hjy
  have hconv := finiteAffineEnvelope_convex hm (fun k => L k u) (fun k => L k p - 1)
  have hmajor := finiteAffineEnvelope_major hm (fun k => L k u) (fun k => L k p - 1) j
  have hact := convex_affine_piece_active_between hconv hmajor hax hay hx.le hy.le
  rw [halfspace_envelope_zero_at_boundary hm L hP p u hp] at hact
  simp only [mul_zero, zero_add] at hact
  linarith only [hact]

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

private theorem envelope_zero_at_frontier {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    (p u : Fin d → ℝ) (x : ℝ) (hp : p + x • u ∈ frontier P) :
    finiteAffineEnvelope hm (fun j => L j u) (fun j => L j p - 1) x = 0 := by
  obtain ⟨hle, j, hj⟩ := frontier_finite_halfspaces_active L hP hp
  apply le_antisymm
  · apply Finset.sup'_le
    intro k _
    have hk := hle k
    rw [map_add, map_smul] at hk
    change L k p + x * L k u ≤ 1 at hk
    linarith only [hk]
  · have hj' := hj
    rw [map_add, map_smul] at hj'
    change L j p + x * L j u = 1 at hj'
    have hmajor := finiteAffineEnvelope_major hm (fun k => L k u) (fun k => L k p - 1) j x
    linarith only [hmajor, hj']

theorem first_reference_chord_data {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p u : Fin d → ℝ) (hp : p ∈ frontier P)
    {ε τ : ℝ} (hτ : 0 < τ) (hr : p - ε • u ≠ 0)
    (hreply : oracle (p - ε • u) = τ • (p - ε • u)) :
    let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
    let B := r₂ - p
    let H := finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1)
    H 0 = 0 ∧ H (-(1 + τ)) = 0 ∧ (∀ x : ℝ, 0 ≤ x → 0 ≤ H x) ∧
      oracle (p - ε • u) = p + (-(1 + τ)) • B ∧
      (1 / 2 : ℝ) • (p + r₂) = p + (1 / 2 : ℝ) • B := by
  dsimp only
  let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
  let B := r₂ - p
  have hden : 1 + τ ≠ 0 := ne_of_gt (by linarith)
  have hanchor : p + (-(1 + τ)) • B = τ • (p - ε • u) := by
    ext j
    dsimp [B, r₂]
    field_simp
    <;> ring
  have hp₁ : p + (-(1 + τ)) • B ∈ frontier P := by
    rw [hanchor, ← hreply]
    exact (horacle (p - ε • u) hr).1
  have hzero := halfspace_envelope_zero_at_boundary hm L hP p B hp
  have hnegative := envelope_zero_at_frontier hm L hP p B (-(1 + τ)) hp₁
  refine ⟨hzero, hnegative, ?_, hreply.trans hanchor.symm, ?_⟩
  · intro x hx
    exact convex_gap_nonneg_positive_of_negative_zero
      (finiteAffineEnvelope_convex hm _ _) hzero (by linarith) hnegative hx
  · ext j
    dsimp [B]
    ring

theorem first_reference_segment_avoids_known_facets {d : ℕ} {ι : Type*}
    {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a δ M τ x : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hminus : (-a) • u ∈ P) (hplus : a • u ∈ P)
    (L : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hpSlack : ∀ j, L j p ≤ 1 - δ) (huBound : ∀ j, |L j u| ≤ M)
    (hτ : 0 < τ) (hτtwo : τ ≤ 2) (hx : 0 ≤ x) (hxone : x ≤ 1)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    let ε := a * δ / (2 * (1 + a * M + δ))
    let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
    let r := p + x • (r₂ - p)
    r ≠ 0 ∧ ∀ j, L j (oracle r) < 1 := by
  dsimp only
  let ε := a * δ / (2 * (1 + a * M + δ))
  have hε : 0 < ε := (facet_local_step_bounds ha hδ hM).1
  have hden : 0 < 1 + τ := by linarith
  have hc : 0 < 2 / (1 + τ) := div_pos (by norm_num) hden
  have hβ : |(0 : ℝ)| ≤ 1 * ε := by simpa only [abs_zero, one_mul] using hε.le
  have hη : |τ * ε / (1 + τ)| ≤ (2 / (1 + τ)) * ε := by
    rw [abs_of_nonneg (div_nonneg (mul_nonneg hτ.le hε.le) hden.le)]
    have hm := mul_le_mul_of_nonneg_right hτtwo (div_nonneg hε.le hden.le)
    calc
      τ * ε / (1 + τ) = τ * (ε / (1 + τ)) := by ring
      _ ≤ 2 * (ε / (1 + τ)) := hm
      _ = (2 / (1 + τ)) * ε := by ring
  have hsafe := rayOracle_safe_reference_segment hconv hclosed hzero hp
    ha hδ hM hminus hplus L hpSlack huBound (by norm_num : (0 : ℝ) < 1)
    hc hβ hη hx hxone horacle
  have heq : p + x • ((τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p - p) =
      (1 - x) • ((1 : ℝ) • p + (0 : ℝ) • u) +
        x • ((2 / (1 + τ)) • p + (τ * ε / (1 + τ)) • u) := by
    ext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [← heq] at hsafe
  exact hsafe

end Grunbaum2003.RayPlanar

namespace Grunbaum2003

theorem rayOracle_local_sector_and_known_facet_exclusion :
    (∀ {d : ℕ} (hd : 0 < d) {P Q : Set (Fin d → ℝ)},
      Convex ℝ P → IsClosed P → (0 : Fin d → ℝ) ∈ interior P → P ⊆ Q →
      ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
      ∀ {x : Fin d → ℝ}, x ∈ Q.extremePoints ℝ →
        x ≠ 0 ∧ (oracle x = x ↔ x ∈ P.extremePoints ℝ)) ∧
    (∀ {d k : ℕ} (hd : 0 < d) {P Q : Set (Fin d → ℝ)},
      Convex ℝ P → IsClosed P → (0 : Fin d → ℝ) ∈ interior P → P ⊆ Q →
      ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
      ∀ {x : Fin d → ℝ}, x ∈ Q.extremePoints ℝ → oracle x ≠ x →
      ∀ (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ), (∀ j, L j x ≤ 1) →
        x ≠ 0 ∧ (∀ j, L j (oracle x) < 1)) ∧
    (∀ {d k : ℕ} {P : Set (Fin d → ℝ)} {oracle : (Fin d → ℝ) → (Fin d → ℝ)},
      IsPolytopeRayOracle P oracle →
      ∀ (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ) {x : Fin d → ℝ},
        x ≠ 0 → (∀ j, L j x ≤ 0) → ∀ j, L j (oracle x) < 1) ∧
    (∀ {d k : ℕ} (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ) (p u : Fin d → ℝ),
      (∀ j, L j p < 1) →
      let δ := ∏ j, (1 - L j p) / (1 + (1 - L j p))
      let M := 1 + ∑ j, (L j u) ^ 2
      0 < δ ∧ 0 ≤ M ∧ (∀ j, L j p ≤ 1 - δ) ∧ (∀ j, |L j u| ≤ M)) ∧
    (∀ {d : ℕ} {ι : Type*} {P : Set (Fin d → ℝ)},
      Convex ℝ P → IsClosed P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ {p u : Fin d → ℝ}, p ∈ frontier P →
      ∀ {a δ M : ℝ}, 0 < a → 0 < δ → 0 ≤ M →
      (-a) • u ∈ P → a • u ∈ P →
      ∀ (L : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ),
      (∀ j, L j p ≤ 1 - δ) → (∀ j, |L j u| ≤ M) →
      ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
      let ε := a * δ / (2 * (1 + a * M + δ))
      (p - ε • u ≠ 0 ∧
        ∃ τ : ℝ, 0 < τ ∧ τ < 2 ∧
          oracle (p - ε • u) = τ • (p - ε • u) ∧
          (∀ j, L j (oracle (p - ε • u)) < 1) ∧
          let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
          r₂ ≠ 0 ∧ (∀ j, L j (oracle r₂) < 1) ∧
          ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
            p + x • (r₂ - p) ≠ 0 ∧ ∀ j, L j (oracle (p + x • (r₂ - p))) < 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d hd P Q hconv hclosed hzero hPQ oracle horacle x hx
    exact rayOracle_outer_vertex_fixed_iff hd hconv hclosed hzero hPQ horacle hx
  · intro d k hd P Q hconv hclosed hzero hPQ oracle horacle x hx hnonfixed L hxBound
    exact RayPlanar.outer_vertex_probe_known_facets_strict hd hconv hclosed hzero hPQ horacle hx hnonfixed L hxBound
  · intro d k P oracle horacle L x hx hdir
    exact RayPlanar.rayOracle_known_nonpositive_direction_strict horacle L hx hdir
  · intro d k L p u hstrict
    exact RayPlanar.known_facet_field_parameters L p u hstrict
  · intro d ι P hconv hclosed hzero p u hp a δ M ha hδ hM hminus hplus L hpSlack huBound oracle horacle
    obtain ⟨hfirstNe, τ, hτ, hτtwo, hreply, hfirstSlack, hr₂Ne, hr₂Slack⟩ :=
      scaled_planar_first_two_queries_avoid_known_facets hconv hclosed hzero hp ha hδ hM hminus hplus L hpSlack huBound horacle
    refine ⟨hfirstNe, τ, hτ, hτtwo, hreply, hfirstSlack, hr₂Ne, hr₂Slack, ?_⟩
    intro x hx0 hx1
    exact RayPlanar.first_reference_segment_avoids_known_facets hconv hclosed hzero hp ha hδ hM hminus hplus L hpSlack huBound hτ hτtwo.le hx0 hx1 horacle

end Grunbaum2003
end

theorem solution :
    (∀ {d : ℕ} (hd : 0 < d) {P Q : Set (Fin d → ℝ)},
      Convex ℝ P → IsClosed P → (0 : Fin d → ℝ) ∈ interior P → P ⊆ Q →
      ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, Grunbaum2003.IsPolytopeRayOracle P oracle →
      ∀ {x : Fin d → ℝ}, x ∈ Q.extremePoints ℝ →
        x ≠ 0 ∧ (oracle x = x ↔ x ∈ P.extremePoints ℝ)) ∧
    (∀ {d k : ℕ} (hd : 0 < d) {P Q : Set (Fin d → ℝ)},
      Convex ℝ P → IsClosed P → (0 : Fin d → ℝ) ∈ interior P → P ⊆ Q →
      ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, Grunbaum2003.IsPolytopeRayOracle P oracle →
      ∀ {x : Fin d → ℝ}, x ∈ Q.extremePoints ℝ → oracle x ≠ x →
      ∀ (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ), (∀ j, L j x ≤ 1) →
        x ≠ 0 ∧ (∀ j, L j (oracle x) < 1)) ∧
    (∀ {d k : ℕ} {P : Set (Fin d → ℝ)} {oracle : (Fin d → ℝ) → (Fin d → ℝ)},
      Grunbaum2003.IsPolytopeRayOracle P oracle →
      ∀ (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ) {x : Fin d → ℝ},
        x ≠ 0 → (∀ j, L j x ≤ 0) → ∀ j, L j (oracle x) < 1) ∧
    (∀ {d k : ℕ} (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ) (p u : Fin d → ℝ),
      (∀ j, L j p < 1) →
      let δ := ∏ j, (1 - L j p) / (1 + (1 - L j p))
      let M := 1 + ∑ j, (L j u) ^ 2
      0 < δ ∧ 0 ≤ M ∧ (∀ j, L j p ≤ 1 - δ) ∧ (∀ j, |L j u| ≤ M)) ∧
    (∀ {d : ℕ} {ι : Type*} {P : Set (Fin d → ℝ)},
      Convex ℝ P → IsClosed P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ {p u : Fin d → ℝ}, p ∈ frontier P →
      ∀ {a δ M : ℝ}, 0 < a → 0 < δ → 0 ≤ M →
      (-a) • u ∈ P → a • u ∈ P →
      ∀ (L : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ),
      (∀ j, L j p ≤ 1 - δ) → (∀ j, |L j u| ≤ M) →
      ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, Grunbaum2003.IsPolytopeRayOracle P oracle →
      let ε := a * δ / (2 * (1 + a * M + δ))
      (p - ε • u ≠ 0 ∧
        ∃ τ : ℝ, 0 < τ ∧ τ < 2 ∧
          oracle (p - ε • u) = τ • (p - ε • u) ∧
          (∀ j, L j (oracle (p - ε • u)) < 1) ∧
          let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
          r₂ ≠ 0 ∧ (∀ j, L j (oracle r₂) < 1) ∧
          ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
            p + x • (r₂ - p) ≠ 0 ∧ ∀ j, L j (oracle (p + x • (r₂ - p))) < 1)) :=
  Grunbaum2003.rayOracle_local_sector_and_known_facet_exclusion
