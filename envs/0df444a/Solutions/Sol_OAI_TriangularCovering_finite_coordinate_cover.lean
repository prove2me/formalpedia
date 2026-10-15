-- Prove2me | solution 1 for OAI.TriangularCovering.finite_coordinate_cover
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T19:13:41.271251+00:00
-- url     : https://prove2.me/submissions/1082e715-084e-4447-ab28-a454bfbe2d1d

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/CoordinateCover.lean:L447-L466
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularCovering.finite_coordinate_cover. Inline helpers are the
-- source spans of proof-only lemmas this proof needs; the node is hoisted out of its namespace
-- as a top-level `theorem solution` with the namespace re-opened.
import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover
import Theorems.Thm_OAI_TriangularCovering_alpha_error
import Theorems.Thm_OAI_TriangularCovering_coeff_bounds
import Theorems.Thm_OAI_TriangularCovering_d_le_max_endpoints
import Theorems.Thm_OAI_TriangularCovering_first_crossing
import Theorems.Thm_OAI_TriangularCovering_mesh_abs_le
import Theorems.Thm_OAI_TriangularCovering_radial_exclusion

-- ---- inline helpers from OAI.Geometry.TriangularCovering.CoordinateCover ----
namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

theorem beta_error {a b q : ℝ} (ha : a ≤ q) (hb : q ≤ b) :
    |beta a b - q / 2| ≤ (b - a) / 4 := by
  rw [abs_le]
  dsimp [beta]
  constructor <;> linarith

theorem angular_sector {N : ℕ} (hN : 0 < N) {r z ℓ : ℝ} (hz : |z| ≤ r) :
    ∃ j : ℕ, j < N ∧
      Sector (mesh N j) (mesh N (j + 1))
        (r - ℓ * beta (mesh N j) (mesh N (j + 1)))
        (z - ℓ * alpha (mesh N j) (mesh N (j + 1))) := by
  let f : ℕ → ℝ := fun i => mesh N i * r + ℓ * (1 - mesh N i ^ 2) / 4
  have hf0 : f 0 = -r := by simp [f]
  have hfN : f N = r := by simp [f, mesh_last hN]
  obtain ⟨j, hj, hlo, hhi⟩ := first_crossing hN f z
    (by rw [hf0]; exact (abs_le.mp hz).1)
    (by rw [hfN]; exact (abs_le.mp hz).2)
  let a := mesh N j
  let b := mesh N (j + 1)
  have he0 : f j = a * (r - ℓ * beta a b) + ℓ * alpha a b := by
    change a * r + ℓ * (1 - a ^ 2) / 4 = _
    dsimp [alpha, beta]; ring
  have he1 : f (j + 1) = b * (r - ℓ * beta a b) + ℓ * alpha a b := by
    change b * r + ℓ * (1 - b ^ 2) / 4 = _
    dsimp [alpha, beta]; ring
  rw [he0] at hlo
  rw [he1] at hhi
  have hlo' : a * (r - ℓ * beta a b) ≤ z - ℓ * alpha a b := by linarith only [hlo]
  have hhi' : z - ℓ * alpha a b ≤ b * (r - ℓ * beta a b) := by linarith only [hhi]
  have hdiff : 0 < b - a := by
    change 0 < mesh N (j + 1) - mesh N j
    rw [mesh_succ]
    exact step_pos hN
  refine ⟨j, hj, ?_, hlo', hhi'⟩
  have hmul : 0 ≤ (b - a) * (r - ℓ * beta a b) := by nlinarith only [hlo', hhi']
  exact nonneg_of_mul_nonneg_right hmul hdiff

theorem cutoff_pos {ε a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) : 0 < cutoff ε a b := by
  have h := (coeff_bounds ha hb).2.2.2.1
  have hM : 0 ≤ cutoffCoeff a b := by unfold η at h; linarith only [h]
  dsimp [cutoff]
  nlinarith only [mul_nonneg (sq_nonneg ε) hM]

theorem angle_in_interval {a b r z : ℝ} (hr : 0 < r) (hz : Sector a b r z) :
    a ≤ z / r ∧ z / r ≤ b := by
  exact ⟨(le_div_iff₀ hr).mpr hz.2.1, (div_le_iff₀ hr).mpr hz.2.2⟩

theorem abs_le_of_interval {a b q : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hqa : a ≤ q) (hqb : q ≤ b) : |q| ≤ 1 :=
  abs_le.mpr ⟨(abs_le.mp ha).1.trans hqa, hqb.trans (abs_le.mp hb).2⟩

theorem selected_cuts {ε Δ a b c e x y r s : ℝ}
    (he0 : 0 < ε) (he1 : ε ≤ η / 2) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ ε ^ 2)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc : |c| ≤ 1) (he : |e| ≤ 1)
    (hab : b - a = Δ) (hce : e - c = Δ) (hxy : |x| + |y| ≤ 1)
    (hrs : r + s = 1 - ε * x * beta a b + ε * y * beta c e)
    (hqsec : Sector a b r (y - ε * x * alpha a b))
    (hpsec : Sector c e s (x + ε * y * alpha c e)) :
    r ≤ cutoff ε a b ∨ s ≤ cutoff ε c e := by
  by_contra! hbad
  have hr : 0 < r := lt_trans (cutoff_pos ha hb) hbad.1
  have hs : 0 < s := lt_trans (cutoff_pos hc he) hbad.2
  let q := (y - ε * x * alpha a b) / r
  let p := (x + ε * y * alpha c e) / s
  have hqI : a ≤ q ∧ q ≤ b := angle_in_interval hr hqsec
  have hpI : c ≤ p ∧ p ≤ e := angle_in_interval hs hpsec
  have hq : |q| ≤ 1 := abs_le_of_interval ha hb hqI.1 hqI.2
  have hp : |p| ≤ 1 := abs_le_of_interval hc he hpI.1 hpI.2
  have h1 := coeff_bounds ha hb
  have h2 := coeff_bounds hc he
  have hβ : |beta a b - q / 2| ≤ Δ / 4 := by simpa [hab] using beta_error hqI.1 hqI.2
  have hγ : |beta c e - p / 2| ≤ Δ / 4 := by simpa [hce] using beta_error hpI.1 hpI.2
  have hea : |alpha a b - (1 + q ^ 2) / 4| ≤ Δ / 2 := by
    simpa [hab] using alpha_error ha hq hqI.1 hqI.2
  have heb : |alpha c e - (1 + p ^ 2) / 4| ≤ Δ / 2 := by
    simpa [hce] using alpha_error hc hp hpI.1 hpI.2
  have hM : η + d q ≤ cutoffCoeff a b := by
    exact add_le_add_right (d_le_max_endpoints hqI.1 hqI.2) η
  have hN : η + d p ≤ cutoffCoeff c e := by
    exact add_le_add_right (d_le_max_endpoints hpI.1 hpI.2) η
  have hMN : cutoffCoeff a b + cutoffCoeff c e ≤ 1 / 4 + 2 * η := by
    linarith only [h1.2.2.2.2, h2.2.2.2.2]
  have hy : y = r * q + ε * x * alpha a b := by
    dsimp [q]
    field_simp
    ring
  have hx : x = s * p - ε * y * alpha c e := by
    dsimp [p]
    field_simp
    ring
  have hcut := radial_exclusion he0 he1 hΔ0 hΔ1 hxy hq hp
    h1.1 h1.2.1 h2.1 h2.2.1 h1.2.2.1 h2.2.2.1 hβ hγ hea heb hM hN hMN hrs hy hx
  exact hcut.elim (not_le.mpr hbad.1) (not_le.mpr hbad.2)

end TriangularCovering

namespace TriangularCovering

end TriangularCovering

end

end OAI

-- ---- hoisted node ----
open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem solution {N : ℕ} {ε x y t : ℝ}
    (hN : 0 < N) (he0 : 0 < ε) (he1 : ε ≤ η / 2) (hmesh : step N ≤ ε ^ 2)
    (hx : |x| ≤ 1 - t) (hy : |y| ≤ t) :
    (∃ j : ℕ, j < N ∧ LowerHit N j ε x y t) ∨
    (∃ j : ℕ, j < N ∧ UpperHit N j ε x y t) := by
  obtain ⟨j, hj, hjs⟩ := angular_sector hN (ℓ := ε * x) hy
  obtain ⟨k, hk, hks⟩ := angular_sector hN (ℓ := -(ε * y)) hx
  have hks' : Sector (mesh N k) (mesh N (k + 1))
      (1 - t + ε * y * beta (mesh N k) (mesh N (k + 1)))
      (x + ε * y * alpha (mesh N k) (mesh N (k + 1))) := by
    simpa only [neg_mul, sub_neg_eq_add] using hks
  have hcuts := selected_cuts he0 he1 (step_pos hN).le hmesh
    (mesh_abs_le hN hj.le) (mesh_abs_le hN hj) (mesh_abs_le hN hk.le) (mesh_abs_le hN hk)
    (mesh_succ N j) (mesh_succ N k) (by linarith only [hx, hy])
    (show (t - ε * x * beta (mesh N j) (mesh N (j + 1))) +
        (1 - t + ε * y * beta (mesh N k) (mesh N (k + 1))) =
      1 - ε * x * beta (mesh N j) (mesh N (j + 1)) +
        ε * y * beta (mesh N k) (mesh N (k + 1)) by ring) hjs hks'
  exact hcuts.elim (fun h => Or.inl ⟨j, hj, hjs, h⟩) (fun h => Or.inr ⟨k, hk, hks', h⟩)
