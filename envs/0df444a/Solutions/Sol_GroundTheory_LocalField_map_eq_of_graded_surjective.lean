-- Prove2me | solution 1 for GroundTheory.LocalField.map_eq_of_graded_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:31.682795+00:00
-- url     : https://prove2.me/submissions/dc83cdd4-405c-483c-b9b4-17a3f64857fd

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Filter Topology Uniformity
variable {G H : Type*} [Group G] [Group H]
namespace GroundTheory.LocalField
theorem _root_.solution {F : ℕ → Subgroup G} {E : ℕ → Subgroup H}
    (hF : Antitone F) (hE : Antitone E) (hG : FiltrationComplete F)
    (hH : FiltrationSeparated E) (f : G →* H) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (k : ℕ) (hmap : ∀ n, k ≤ n → ∀ g ∈ F n, f g ∈ E (φ n))
    (hgr : ∀ n, k ≤ n → ∀ h ∈ E (φ n), ∃ g ∈ F n, h / f g ∈ E (φ (n + 1))) :
    (F k).map f = E (φ k) := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact hmap k le_rfl g hg
  intro h hh
  rw [Subgroup.mem_map]
  have hs : ∀ (n : ℕ) (a : H), ∃ g : G,
      k ≤ n → a ∈ E (φ n) → g ∈ F n ∧ a / f g ∈ E (φ (n + 1)) := by
    intro n a
    by_cases hc : k ≤ n ∧ a ∈ E (φ n)
    · obtain ⟨g, hg1, hg2⟩ := hgr n hc.1 a hc.2
      exact ⟨g, fun _ _ => ⟨hg1, hg2⟩⟩
    · exact ⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose s hs using hs

  obtain ⟨r, hr0, hrs⟩ : ∃ r : ℕ → H, r 0 = h ∧ ∀ j, r (j + 1) = r j / f (s (k + j) (r j)) :=
    ⟨fun j => Nat.rec h (fun j rj => rj / f (s (k + j) rj)) j, rfl, fun _ => rfl⟩
  have hrE : ∀ j, r j ∈ E (φ (k + j)) := by
    intro j
    induction j with
    | zero => simpa [hr0] using hh
    | succ j ih =>
      rw [hrs, ← add_assoc]
      exact (hs (k + j) (r j) (Nat.le_add_right k j) ih).2

  obtain ⟨D, hD⟩ : ∃ D : ℕ → G, ∀ j, D j = s (k + j) (r j) := ⟨_, fun _ => rfl⟩
  have hDF : ∀ j, D j ∈ F (k + j) := fun j => by
    rw [hD]
    exact (hs (k + j) (r j) (Nat.le_add_right k j) (hrE j)).1
  have hrs' : ∀ j, r (j + 1) = r j / f (D j) := fun j => by rw [hrs, hD]

  obtain ⟨x, hx0, hxs⟩ : ∃ x : ℕ → G, x 0 = D 0 ∧ ∀ j, x (j + 1) = D (j + 1) * x j :=
    ⟨fun j => Nat.rec (D 0) (fun j xj => D (j + 1) * xj) j, rfl, fun _ => rfl⟩
  have hxr : ∀ j, h / f (x j) = r (j + 1) := by
    intro j
    induction j with
    | zero => rw [hx0, hrs', hr0]
    | succ j ih =>
      rw [hxs, hrs' (j + 1), ← ih, map_mul]
      simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc]
  have hxF : ∀ m d, x (m + d) / x m ∈ F (k + m + 1) := by
    intro m d
    induction d with
    | zero => simp
    | succ d ih =>
      have e : x (m + (d + 1)) / x m = D (m + d + 1) * (x (m + d) / x m) := by
        rw [← add_assoc, hxs, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
      rw [e]
      exact (F _).mul_mem (hF (by omega) (hDF (m + d + 1))) ih
  have hC : FiltrationCauchy F x := by
    intro N
    refine ⟨N, fun m hm n hn => ?_⟩
    rcases le_total m n with hmn | hnm
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
      exact hF (by omega) (hxF m d)
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
      have e := (F _).inv_mem (hxF n d)
      rw [inv_div] at e
      exact hF (by omega) e
  have hxk : ∀ j, x j ∈ F k := by
    intro j
    induction j with
    | zero => rw [hx0]; simpa using hDF 0
    | succ j ih => rw [hxs]; exact (F k).mul_mem (hF (by omega) (hDF (j + 1))) ih
  obtain ⟨y, hy⟩ := hG x hC
  obtain ⟨M0, hM0⟩ := hy k
  have hyk : y ∈ F k := by
    have e : (x M0 / y)⁻¹ * x M0 = y := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
    rw [← e]
    exact (F k).mul_mem ((F k).inv_mem (hM0 M0 le_rfl)) (hxk M0)
  refine ⟨y, hyk, ?_⟩
  have h1 : h / f y = 1 := by
    apply hH
    intro m
    obtain ⟨N0, hN0⟩ := Filter.tendsto_atTop_atTop.mp hφ m
    obtain ⟨M, hM⟩ := hy (max N0 k)
    have e : h / f y = r (max M N0 + 1) * f (x (max M N0) / y) := by
      rw [← hxr (max M N0), map_div]
      simp only [div_eq_mul_inv, mul_assoc, inv_mul_cancel_left]
    rw [e]
    refine (E m).mul_mem ?_ ?_
    · exact hE (hN0 _ (by omega)) (hrE (max M N0 + 1))
    · exact hE (hN0 _ (le_max_left _ _))
        (hmap _ (le_max_right _ _) _ (hM (max M N0) (le_max_left _ _)))
  exact (div_eq_one.mp h1).symm
end GroundTheory.LocalField
