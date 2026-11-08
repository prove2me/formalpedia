-- Prove2me | solution 1 for Grunbaum2003.rayFrame_boundary_extension_axes_and_cramer_normal
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T18:41:33.992203+00:00
-- url     : https://prove2.me/submissions/064a5a5a-f39d-49d5-a3b5-e79beb4d58ec

import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_IsDPolytope
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
open scoped BigOperators Matrix

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

namespace Grunbaum2003.RaySection

theorem frontier_of_normalized_support {n : ℕ} {Q : Set (Fin n → ℝ)}
    (F : (Fin n → ℝ) →L[ℝ] ℝ) {q : Fin n → ℝ}
    (hq : q ∈ Q) (hFq : F q = 1) (hbound : ∀ x ∈ Q, F x ≤ 1) :
    q ∈ frontier Q := by
  refine ⟨subset_closure hq, ?_⟩
  intro hqint
  have hsurj : Function.Surjective F := by
    intro s
    refine ⟨s • q, ?_⟩
    rw [map_smul, hFq]
    exact mul_one s
  have hopen : IsOpen (F '' interior Q) := F.isOpenMap hsurj _ isOpen_interior
  have hsub : F '' interior Q ⊆ Set.Iic (1 : ℝ) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hbound x (interior_subset hx)
  have hmem : (1 : ℝ) ∈ interior (Set.Iic (1 : ℝ)) :=
    interior_maximal hsub hopen ⟨q, hqint, hFq⟩
  simpa only [interior_Iic, Set.mem_Iio, lt_self_iff_false] using hmem

theorem induced_rayOracle_of_leftInverse {d n m : ℕ}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (f : (Fin n → ℝ) →L[ℝ] (Fin d → ℝ))
    (g : (Fin d → ℝ) →L[ℝ] (Fin n → ℝ))
    (hgf : Function.LeftInverse g f) :
    IsPolytopeRayOracle (f ⁻¹' P) (fun r => g (oracle (f r))) ∧
      (∀ r, r ≠ 0 → f (g (oracle (f r))) = oracle (f r)) := by
  have hf : Function.Injective f := hgf.injective
  have hrnonzero : ∀ r : Fin n → ℝ, r ≠ 0 → f r ≠ 0 := by
    intro r hr hz
    apply hr
    exact hf (by simpa only [map_zero] using hz)
  have hreply : ∀ r : Fin n → ℝ, r ≠ 0 →
      ∃ t : ℝ, 0 < t ∧ oracle (f r) = t • f r ∧ g (oracle (f r)) = t • r := by
    intro r hr
    obtain ⟨_, t, ht, heq⟩ := horacle (f r) (hrnonzero r hr)
    refine ⟨t, ht, heq, ?_⟩
    rw [heq, map_smul, hgf r]
  constructor
  · intro r hr
    obtain ⟨t, ht, heq, hcoord⟩ := hreply r hr
    obtain ⟨hle, j, hj⟩ := RayPlanar.frontier_finite_halfspaces_active L hP
      (horacle (f r) (hrnonzero r hr)).1
    have hrecover : f (g (oracle (f r))) = oracle (f r) := by
      rw [hcoord, map_smul, ← heq]
    refine ⟨?_, t, ht, hcoord⟩
    apply frontier_of_normalized_support ((L j).comp f)
    · change f (g (oracle (f r))) ∈ P
      rw [hrecover, hP]
      exact hle
    · change L j (f (g (oracle (f r)))) = 1
      rw [hrecover]
      exact hj
    · intro x hx
      change L j (f x) ≤ 1
      have hmem : f x ∈ P := hx
      rw [hP] at hmem
      exact hmem j
  · intro r hr
    obtain ⟨t, _, heq, hcoord⟩ := hreply r hr
    rw [hcoord, map_smul, ← heq]

end Grunbaum2003.RaySection

namespace Grunbaum2003.RayFrame

theorem active_contains_positive_frame {d n : ℕ}
    (l : (Fin d → ℝ) →L[ℝ] ℝ) (v : Fin n → Fin d → ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (p : Fin d → ℝ) (hp : p = ∑ i, w i • v i)
    (hbound : ∀ i, l (v i) ≤ 1) (hactive : l p = 1) :
    ∀ i, l (v i) = 1 := by
  have hsumL : ∑ i, w i * l (v i) = 1 := by
    simpa only [hp, map_sum, map_smul, smul_eq_mul] using hactive
  have hsumgap : ∑ i, w i * (1 - l (v i)) = 0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hsum, hsumL, sub_self]
  have hnonneg : ∀ i ∈ Finset.univ, 0 ≤ w i * (1 - l (v i)) :=
    fun i _ => mul_nonneg (hw i).le (sub_nonneg.mpr (hbound i))
  intro i
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsumgap i (Finset.mem_univ i)
  have hgap : 1 - l (v i) = 0 := (mul_eq_zero.mp hz).resolve_left (hw i).ne'
  linarith only [hgap]

theorem transverse_reply_outside_span {d : ℕ} (W : Submodule ℝ (Fin d → ℝ))
    {P : Set (Fin d → ℝ)} {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    {p u : Fin d → ℝ} (hp : p ∈ W) (hu : u ∉ W)
    (a b : ℝ) (hb : b ≠ 0) :
    oracle (a • p + b • u) ∈ frontier P ∧ oracle (a • p + b • u) ∉ W := by
  have hdir : a • p + b • u ∉ W := by
    intro hmem
    have hsub := W.sub_mem hmem (W.smul_mem a hp)
    have hbu : b • u ∈ W := by simpa only [add_sub_cancel_left] using hsub
    exact hu ((W.smul_mem_iff hb).mp hbu)
  have hne : a • p + b • u ≠ 0 := by
    intro hz
    apply hdir
    rw [hz]
    exact W.zero_mem
  obtain ⟨hfront, t, ht, heq⟩ := horacle (a • p + b • u) hne
  refine ⟨hfront, ?_⟩
  intro hmem
  rw [heq] at hmem
  exact hdir ((W.smul_mem_iff ht.ne').mp hmem)

theorem common_support_midpoint {d m : ℕ}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    (p q : Fin d → ℝ) (hp : p ∈ P) (hq : q ∈ P)
    (j : Fin m) (hjp : L j p = 1) (hjq : L j q = 1) :
    (1 / 2 : ℝ) • (p + q) ∈ frontier P ∧
      ∀ k : Fin m, L k p < 1 → L k q < 1 → L k ((1 / 2 : ℝ) • (p + q)) < 1 := by
  have hpRows : ∀ k, L k p ≤ 1 := by rwa [hP] at hp
  have hqRows : ∀ k, L k q ≤ 1 := by rwa [hP] at hq
  have hmid : (1 / 2 : ℝ) • (p + q) ∈ P := by
    rw [hP]
    intro k
    rw [map_smul, map_add]
    change (1 / 2 : ℝ) * (L k p + L k q) ≤ 1
    linarith only [hpRows k, hqRows k]
  have hactive : L j ((1 / 2 : ℝ) • (p + q)) = 1 := by
    rw [map_smul, map_add, hjp, hjq]
    norm_num
  refine ⟨RaySection.frontier_of_normalized_support (L j) hmid hactive
    (fun x hx => (by rw [hP] at hx; exact hx j)), ?_⟩
  intro k hkp hkq
  rw [map_smul, map_add]
  change (1 / 2 : ℝ) * (L k p + L k q) < 1
  linarith only [hkp, hkq]

theorem extend_positive_boundary_frame {d n m : ℕ}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    (v : Fin n → Fin d → ℝ) (hv : LinearIndependent ℝ v)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hV : ∀ i, v i ∈ P)
    (p q : Fin d → ℝ) (hp : p ∈ P) (hq : q ∈ P)
    (hpcombo : p = ∑ i, w i • v i)
    (hqspan : q ∉ Submodule.span ℝ (Set.range v))
    (j : Fin m) (hjp : L j p = 1) (hjq : L j q = 1) :
    let V : Fin (n + 1) → Fin d → ℝ := Fin.cons q v
    let W : Fin (n + 1) → ℝ := Fin.cons (1 / 2 : ℝ) (fun i => w i / 2)
    let p' := (1 / 2 : ℝ) • (p + q)
    LinearIndependent ℝ V ∧ (∀ i, 0 < W i) ∧ (∑ i, W i = 1) ∧
      p' = ∑ i, W i • V i ∧ (∀ i, V i ∈ P) ∧ p' ∈ frontier P ∧
      (∀ k : Fin m, L k p' = 1 → ∀ i, L k (V i) = 1) := by
  dsimp only
  let V : Fin (n + 1) → Fin d → ℝ := Fin.cons q v
  let W : Fin (n + 1) → ℝ := Fin.cons (1 / 2 : ℝ) (fun i => w i / 2)
  let p' := (1 / 2 : ℝ) • (p + q)
  have hWpos : ∀ i, 0 < W i := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · change 0 < (1 / 2 : ℝ)
      norm_num
    · change 0 < w k / 2
      exact div_pos (hw k) (by norm_num)
  have hWsum : ∑ i, W i = 1 := by
    change ∑ i, (Fin.cons (1 / 2 : ℝ) (fun k => w k / 2)) i = 1
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, div_eq_mul_inv]
    rw [← Finset.sum_mul, hsum]
    norm_num
  have hhalf : ∑ i, (w i / 2) • v i = (1 / 2 : ℝ) • p := by
    rw [hpcombo, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul]
    congr 1
    ring
  have hcombo : p' = ∑ i, W i • V i := by
    change (1 / 2 : ℝ) • (p + q) =
      ∑ i : Fin (n + 1), (Fin.cons (1 / 2 : ℝ) (fun k => w k / 2) : Fin (n + 1) → ℝ) i •
        (Fin.cons q v : Fin (n + 1) → Fin d → ℝ) i
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hhalf, smul_add]
    exact add_comm _ _
  have hVP : ∀ i, V i ∈ P := by
    intro i
    exact Fin.cases hq (fun k => hV k) i
  have hfront : p' ∈ frontier P := (common_support_midpoint L hP p q hp hq j hjp hjq).1
  refine ⟨hv.finCons hqspan, hWpos, hWsum, hcombo, hVP, hfront, ?_⟩
  intro k hk
  apply active_contains_positive_frame (L k) V W hWpos hWsum p' hcombo
  · intro i
    have hmem := hVP i
    rw [hP] at hmem
    exact hmem k
  · exact hk

end Grunbaum2003.RayFrame

namespace Grunbaum2003.RayFrame

def coordinateAxis {d : ℕ} (i : Fin d) : Fin d → ℝ := Pi.single i 1

theorem sum_coordinate_axes {d : ℕ} (p : Fin d → ℝ) :
    ∑ i, p i • coordinateAxis i = p := by
  calc
    ∑ i, p i • coordinateAxis i = ∑ i, Pi.single i (p i) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [coordinateAxis, smul_eq_mul, mul_one] using
        (Pi.single_smul' i (p i) (1 : ℝ)).symm
    _ = p := LinearMap.sum_single_apply (fun _ : Fin d => ℝ) p

theorem exists_coordinate_axis_outside_frame {d n : ℕ}
    (v : Fin n → Fin d → ℝ) (hv : LinearIndependent ℝ v) (hn : n < d) :
    ∃ i : Fin d, coordinateAxis i ∉ Submodule.span ℝ (Set.range v) := by
  classical
  let W := Submodule.span ℝ (Set.range v)
  have hdim : Module.finrank ℝ W = n := by
    simpa only [W, Fintype.card_fin] using finrank_span_eq_card hv
  by_contra hnone
  have haxes : ∀ i : Fin d, coordinateAxis i ∈ W := by
    intro i
    by_contra hi
    exact hnone ⟨i, hi⟩
  have hall : ∀ p : Fin d → ℝ, p ∈ W := by
    intro p
    rw [← sum_coordinate_axes p]
    exact W.sum_mem (fun i _ => W.smul_mem (p i) (haxes i))
  have htop : W = ⊤ := by
    apply le_antisymm le_top
    intro p _
    exact hall p
  rw [htop, finrank_top, Module.finrank_fin_fun] at hdim
  omega

theorem exists_off_axis_pivot {d : ℕ} (W : Submodule ℝ (Fin d → ℝ))
    (p : Fin d → ℝ) (hp : p ∈ W) (hpne : p ≠ 0) (i : Fin d)
    (hi : coordinateAxis i ∉ W) : ∃ j : Fin d, j ≠ i ∧ p j ≠ 0 := by
  classical
  by_contra hnone
  have hzero : ∀ j : Fin d, j ≠ i → p j = 0 := by
    intro j hji
    by_contra hpj
    exact hnone ⟨j, hji, hpj⟩
  have heq : p = p i • coordinateAxis i := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [coordinateAxis]
    · simp [coordinateAxis, hzero j hji, hji, Ne.symm hji]
  have hpi : p i ≠ 0 := by
    intro hz
    apply hpne
    rw [heq, hz, zero_smul]
  rw [heq] at hp
  exact hi ((W.smul_mem_iff hpi).mp hp)

end Grunbaum2003.RayFrame

namespace Grunbaum2003.RayFrame

def frameCramerCoefficients {d : ℕ} (v : Matrix (Fin d) (Fin d) ℝ) : Fin d → ℝ :=
  v.det⁻¹ • Matrix.cramer v (fun _ => 1)

theorem frameCramerCoefficients_apply {d : ℕ} (v : Matrix (Fin d) (Fin d) ℝ) (k : Fin d) :
    frameCramerCoefficients v k = (v.updateCol k (fun _ => 1)).det / v.det := by
  simp only [frameCramerCoefficients, Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply,
    div_eq_mul_inv]
  ring

def frameNormalLinear {d : ℕ} (v : Matrix (Fin d) (Fin d) ℝ) : (Fin d → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ k, frameCramerCoefficients v k * x k
  map_add' x y := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    change (∑ k, frameCramerCoefficients v k * (a * x k)) =
      a * ∑ k, frameCramerCoefficients v k * x k
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring

def frameNormal {d : ℕ} (v : Matrix (Fin d) (Fin d) ℝ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  (frameNormalLinear v).toContinuousLinearMap

theorem frame_det_ne_zero {d : ℕ} (v : Matrix (Fin d) (Fin d) ℝ)
    (hv : LinearIndependent ℝ v) : v.det ≠ 0 :=
  Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.Nonsingular.of_linearIndependent_row hv)

theorem frameCramer_equations {d : ℕ} (v : Matrix (Fin d) (Fin d) ℝ)
    (hv : LinearIndependent ℝ v) : v *ᵥ frameCramerCoefficients v = (fun _ => 1) := by
  rw [frameCramerCoefficients, Matrix.mulVec_smul, Matrix.mulVec_cramer,
    smul_smul, inv_mul_cancel₀ (frame_det_ne_zero v hv), one_smul]

theorem frameNormal_on_frame {d : ℕ} (v : Matrix (Fin d) (Fin d) ℝ)
    (hv : LinearIndependent ℝ v) (i : Fin d) : frameNormal v (v i) = 1 := by
  have hi := congrFun (frameCramer_equations v hv) i
  change (∑ k, v i k * frameCramerCoefficients v k) = 1 at hi
  change (∑ k, frameCramerCoefficients v k * v i k) = 1
  simpa only [mul_comm] using hi

theorem frameNormal_eq_of_values {d : ℕ} (v : Matrix (Fin d) (Fin d) ℝ)
    (hv : LinearIndependent ℝ v) (l : (Fin d → ℝ) →L[ℝ] ℝ)
    (hl : ∀ i, l (v i) = 1) : frameNormal v = l := by
  have hspan : Submodule.span ℝ (Set.range v) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa only [Fintype.card_fin, Module.finrank_fin_fun] using finrank_span_eq_card hv
  apply ContinuousLinearMap.coe_injective
  apply LinearMap.ext_on_range hspan
  intro i
  exact (frameNormal_on_frame v hv i).trans (hl i).symm

theorem frameNormal_eq_original_active_row {d m : ℕ}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    (v : Matrix (Fin d) (Fin d) ℝ) (hv : LinearIndependent ℝ v)
    (w : Fin d → ℝ) (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hV : ∀ i, v i ∈ P)
    (p : Fin d → ℝ) (hp : p ∈ frontier P) (hpcombo : p = ∑ i, w i • v i) :
    ∃ j : Fin m, frameNormal v = L j ∧ L j p = 1 := by
  obtain ⟨_, j, hj⟩ := RayPlanar.frontier_finite_halfspaces_active L hP hp
  have hvalues : ∀ i, L j (v i) = 1 := by
    apply active_contains_positive_frame (L j) v w hw hsum p hpcombo
    · intro i
      have hi := hV i
      rw [hP] at hi
      exact hi j
    · exact hj
  exact ⟨j, frameNormal_eq_of_values v hv (L j) hvalues, hj⟩

end Grunbaum2003.RayFrame

namespace Grunbaum2003

theorem rayFrame_boundary_extension_axes_and_cramer_normal :
    ∃ (coordinateAxis : ∀ {d : ℕ}, Fin d → Fin d → ℝ)
      (frameCramerCoefficients : ∀ {d : ℕ}, Matrix (Fin d) (Fin d) ℝ → Fin d → ℝ)
      (frameNormal : ∀ {d : ℕ}, Matrix (Fin d) (Fin d) ℝ → (Fin d → ℝ) →L[ℝ] ℝ),
      (∀ (d : ℕ) (i : Fin d), coordinateAxis i = Pi.single i 1) ∧
      (∀ (d : ℕ) (v : Matrix (Fin d) (Fin d) ℝ) (k : Fin d),
        frameCramerCoefficients v k = (v.updateCol k (fun _ => 1)).det / v.det) ∧
      (∀ (d : ℕ) (v : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ),
        frameNormal v x = ∑ k, frameCramerCoefficients v k * x k) ∧
      (∀ {d n m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {P : Set (Fin d → ℝ)},
        P = {x | ∀ j, L j x ≤ 1} →
        ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
        ∀ (f : (Fin n → ℝ) →L[ℝ] (Fin d → ℝ)) (g : (Fin d → ℝ) →L[ℝ] (Fin n → ℝ)),
          Function.LeftInverse g f →
          IsPolytopeRayOracle (f ⁻¹' P) (fun r => g (oracle (f r))) ∧
            (∀ r, r ≠ 0 → f (g (oracle (f r))) = oracle (f r))) ∧
      (∀ {d n : ℕ} (v : Fin n → Fin d → ℝ),
        LinearIndependent ℝ v → n < d →
        ∃ i : Fin d, coordinateAxis i ∉ Submodule.span ℝ (Set.range v)) ∧
      (∀ {d : ℕ} (W : Submodule ℝ (Fin d → ℝ)) (p : Fin d → ℝ),
        p ∈ W → p ≠ 0 → ∀ (i : Fin d), coordinateAxis i ∉ W →
        ∃ j : Fin d, j ≠ i ∧ p j ≠ 0) ∧
      (∀ {d n m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {P : Set (Fin d → ℝ)},
        P = {x | ∀ j, L j x ≤ 1} →
        ∀ (v : Fin n → Fin d → ℝ), LinearIndependent ℝ v →
        ∀ (w : Fin n → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
        (∀ i, v i ∈ P) →
        ∀ (p q : Fin d → ℝ), p ∈ P → q ∈ P →
        p = ∑ i, w i • v i →
        q ∉ Submodule.span ℝ (Set.range v) →
        ∀ (j : Fin m), L j p = 1 → L j q = 1 →
        let V : Fin (n + 1) → Fin d → ℝ := Fin.cons q v
        let W : Fin (n + 1) → ℝ := Fin.cons (1 / 2 : ℝ) (fun i => w i / 2)
        let p' := (1 / 2 : ℝ) • (p + q)
        LinearIndependent ℝ V ∧ (∀ i, 0 < W i) ∧ (∑ i, W i = 1) ∧
          p' = ∑ i, W i • V i ∧ (∀ i, V i ∈ P) ∧ p' ∈ frontier P ∧
          (∀ k : Fin m, L k p' = 1 → ∀ i, L k (V i) = 1)) ∧
      (∀ {d m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {P : Set (Fin d → ℝ)},
        P = {x | ∀ j, L j x ≤ 1} →
        ∀ (v : Matrix (Fin d) (Fin d) ℝ), LinearIndependent ℝ v →
        ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
        (∀ i, v i ∈ P) →
        ∀ (p : Fin d → ℝ), p ∈ frontier P → p = ∑ i, w i • v i →
        v.det ≠ 0 ∧ ∃ j : Fin m, frameNormal v = L j ∧ L j p = 1) := by
  refine ⟨@RayFrame.coordinateAxis, @RayFrame.frameCramerCoefficients, @RayFrame.frameNormal,
    fun _ _ => rfl,
    fun d v k => RayFrame.frameCramerCoefficients_apply v k,
    fun _ _ _ => rfl,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro d n m L P hP oracle horacle f g hgf
    exact RaySection.induced_rayOracle_of_leftInverse L hP horacle f g hgf
  · intro d n v hv hn
    exact RayFrame.exists_coordinate_axis_outside_frame v hv hn
  · intro d W p hp hpne i hi
    exact RayFrame.exists_off_axis_pivot W p hp hpne i hi
  · intro d n m L P hP v hv w hw hsum hV p q hp hq hpcombo hqspan j hjp hjq
    exact RayFrame.extend_positive_boundary_frame L hP v hv w hw hsum hV p q hp hq hpcombo hqspan j hjp hjq
  · intro d m L P hP v hv w hw hsum hV p hp hpcombo
    exact ⟨RayFrame.frame_det_ne_zero v hv,
      RayFrame.frameNormal_eq_original_active_row L hP v hv w hw hsum hV p hp hpcombo⟩

end Grunbaum2003
end

theorem solution :
    ∃ (coordinateAxis : ∀ {d : ℕ}, Fin d → Fin d → ℝ)
      (frameCramerCoefficients : ∀ {d : ℕ}, Matrix (Fin d) (Fin d) ℝ → Fin d → ℝ)
      (frameNormal : ∀ {d : ℕ}, Matrix (Fin d) (Fin d) ℝ → (Fin d → ℝ) →L[ℝ] ℝ),
      (∀ (d : ℕ) (i : Fin d), coordinateAxis i = Pi.single i 1) ∧
      (∀ (d : ℕ) (v : Matrix (Fin d) (Fin d) ℝ) (k : Fin d),
        frameCramerCoefficients v k = (v.updateCol k (fun _ => 1)).det / v.det) ∧
      (∀ (d : ℕ) (v : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ),
        frameNormal v x = ∑ k, frameCramerCoefficients v k * x k) ∧
      (∀ {d n m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {P : Set (Fin d → ℝ)},
        P = {x | ∀ j, L j x ≤ 1} →
        ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, Grunbaum2003.IsPolytopeRayOracle P oracle →
        ∀ (f : (Fin n → ℝ) →L[ℝ] (Fin d → ℝ)) (g : (Fin d → ℝ) →L[ℝ] (Fin n → ℝ)),
          Function.LeftInverse g f →
          Grunbaum2003.IsPolytopeRayOracle (f ⁻¹' P) (fun r => g (oracle (f r))) ∧
            (∀ r, r ≠ 0 → f (g (oracle (f r))) = oracle (f r))) ∧
      (∀ {d n : ℕ} (v : Fin n → Fin d → ℝ),
        LinearIndependent ℝ v → n < d →
        ∃ i : Fin d, coordinateAxis i ∉ Submodule.span ℝ (Set.range v)) ∧
      (∀ {d : ℕ} (W : Submodule ℝ (Fin d → ℝ)) (p : Fin d → ℝ),
        p ∈ W → p ≠ 0 → ∀ (i : Fin d), coordinateAxis i ∉ W →
        ∃ j : Fin d, j ≠ i ∧ p j ≠ 0) ∧
      (∀ {d n m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {P : Set (Fin d → ℝ)},
        P = {x | ∀ j, L j x ≤ 1} →
        ∀ (v : Fin n → Fin d → ℝ), LinearIndependent ℝ v →
        ∀ (w : Fin n → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
        (∀ i, v i ∈ P) →
        ∀ (p q : Fin d → ℝ), p ∈ P → q ∈ P →
        p = ∑ i, w i • v i →
        q ∉ Submodule.span ℝ (Set.range v) →
        ∀ (j : Fin m), L j p = 1 → L j q = 1 →
        let V : Fin (n + 1) → Fin d → ℝ := Fin.cons q v
        let W : Fin (n + 1) → ℝ := Fin.cons (1 / 2 : ℝ) (fun i => w i / 2)
        let p' := (1 / 2 : ℝ) • (p + q)
        LinearIndependent ℝ V ∧ (∀ i, 0 < W i) ∧ (∑ i, W i = 1) ∧
          p' = ∑ i, W i • V i ∧ (∀ i, V i ∈ P) ∧ p' ∈ frontier P ∧
          (∀ k : Fin m, L k p' = 1 → ∀ i, L k (V i) = 1)) ∧
      (∀ {d m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {P : Set (Fin d → ℝ)},
        P = {x | ∀ j, L j x ≤ 1} →
        ∀ (v : Matrix (Fin d) (Fin d) ℝ), LinearIndependent ℝ v →
        ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
        (∀ i, v i ∈ P) →
        ∀ (p : Fin d → ℝ), p ∈ frontier P → p = ∑ i, w i • v i →
        v.det ≠ 0 ∧ ∃ j : Fin m, frameNormal v = L j ∧ L j p = 1) :=
  Grunbaum2003.rayFrame_boundary_extension_axes_and_cramer_normal
