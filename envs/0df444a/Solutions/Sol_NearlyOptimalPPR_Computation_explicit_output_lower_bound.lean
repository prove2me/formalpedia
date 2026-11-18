-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.explicit_output_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T02:17:22.638186+00:00
-- url     : https://prove2.me/submissions/a341e902-62af-4a74-afe0-174d80a3d378

import Definitions.Def_NearlyOptimalPPR_Computation_machine
import Theorems.Thm_NearlyOptimalPPR_Computation_residual_error

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

local instance star_adjacency (L : ℕ) : DecidableRel (star L).Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧ (u.val = 0 ∨ v.val = 0)))

lemma star_neighbors_center (L : ℕ) :
    (star L).neighborFinset (⟨0, Nat.zero_lt_succ L⟩ : Fin (L+1)) =
      Finset.univ.erase ⟨0, Nat.zero_lt_succ L⟩ := by
  ext v
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase, mem_univ, and_true]
  change ((⟨0, Nat.zero_lt_succ L⟩ : Fin (L+1)) ≠ v ∧ (0 = 0 ∨ v.val = 0)) ↔ _
  simp only [true_or, and_true, ne_comm]

lemma star_neighbors_leaf (L : ℕ) (v : Fin (L+1)) (hv : v.val ≠ 0) :
    (star L).neighborFinset v = {⟨0, Nat.zero_lt_succ L⟩} := by
  ext u
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
  change (v ≠ u ∧ (v.val = 0 ∨ u.val = 0)) ↔ u = ⟨0, Nat.zero_lt_succ L⟩
  constructor
  · intro h
    apply Fin.ext
    exact h.2.resolve_left hv
  · intro h
    subst u
    exact ⟨fun h => hv (congrArg Fin.val h), Or.inr rfl⟩

lemma star_degree_center (L : ℕ) :
    (star L).degree (⟨0, Nat.zero_lt_succ L⟩ : Fin (L+1)) = L := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, star_neighbors_center]
  simp

lemma star_degree_leaf (L : ℕ) (v : Fin (L+1)) (hv : v.val ≠ 0) :
    (star L).degree v = 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, star_neighbors_leaf L v hv]
  simp

lemma star_lap_apply (L : ℕ) (α : ℝ) (z : Fin (L+1) → ℝ) (v : Fin (L+1)) :
    (LocalPush.Lα (star L) α *ᵥ z) v =
      LocalPush.deg (star L) v * z v - (1-α) * ∑ u ∈ (star L).neighborFinset v, z u := by
  classical
  simp [LocalPush.Lα, LocalPush.degM, LocalPush.adjM, sub_mulVec,
    smul_mulVec, SimpleGraph.adjMatrix_mulVec_apply, mulVec_diagonal]

lemma green_zero {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) : green G α 0 = 0 := by
  classical
  ext v
  simp [green, extendPositive, show (fun _ : PositiveVertices G => (0 : ℝ)) = 0 from rfl]

lemma star_ppr (L : ℕ) (hL : 1 ≤ L) (α : ℝ) (hα : 0 < α ∧ α < 1) :
    ∀ v : Fin (L+1), ppr (star L) α ⟨0, Nat.zero_lt_succ L⟩ v =
      if v.val = 0 then 1 / (2-α) else ((1-α)/(2-α)) / (L : ℝ) := by
  classical
  let s : Fin (L+1) := ⟨0, Nat.zero_lt_succ L⟩
  let z : Fin (L+1) → ℝ := fun v =>
    if v.val = 0 then 1 / (α * (L : ℝ) * (2-α))
    else (1-α) / (α * (L : ℝ) * (2-α))
  have hα0 := hα.1
  have hα1 := hα.2
  have hLr : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have h2 : 0 < 2-α := by linarith [hα.2]
  have hz : ∀ v, 0 ≤ z v := by
    intro v
    dsimp [z]
    have hnon : 0 < 1-α := by linarith [hα.2]
    split <;> positivity
  have hr : residual (star L) α s z = 0 := by
    ext v
    simp only [residual, Pi.sub_apply, Pi.zero_apply]
    rw [star_lap_apply]
    by_cases hv : v.val = 0
    · have hvs : v = s := by apply Fin.ext; exact hv
      subst v
      have he : (star L).neighborFinset s = Finset.univ.erase s := star_neighbors_center L
      have hsum : ∑ u ∈ (star L).neighborFinset s, z u =
          (L : ℝ) * ((1-α)/(α * (L : ℝ) * (2-α))) := by
        rw [he]
        have heq : ∀ u ∈ Finset.univ.erase s,
            z u = (1-α)/(α * (L : ℝ) * (2-α)) := by
          intro u hu
          have hu' : u.val ≠ 0 := fun he => (Finset.mem_erase.mp hu).1 (Fin.ext he)
          simp only [z, if_neg hu']
        rw [Finset.sum_congr rfl heq]
        simp
      rw [hsum]
      simp only [LocalPush.deg, s, star_degree_center, z, ite_true, LocalPush.e, Pi.single_eq_same]
      field_simp [hα0.ne', hLr.ne', h2.ne']
      <;> ring
    · have he : (star L).neighborFinset v = {s} := star_neighbors_leaf L v hv
      rw [he]
      simp only [Finset.sum_singleton, LocalPush.deg, star_degree_leaf L v hv]
      have hvs : v ≠ s := fun he => hv (congrArg Fin.val he)
      simp only [z, hv, ite_false, s, ite_true, LocalPush.e, Pi.single_apply, hvs]
      field_simp [hα0.ne', hLr.ne', h2.ne']
      <;> ring
  have hs : 0 < (star L).degree s := by rw [show s = ⟨0, Nat.zero_lt_succ L⟩ from rfl, star_degree_center]; omega
  have hid := (residual_error (star L) s α 1 hα ⟨by norm_num, by norm_num⟩ hs z hz).1
  rw [hr, green_zero] at hid
  have heq : ppr (star L) α s = potentialOutput (star L) α z := by
    have hh : potentialOutput (star L) α 0 = 0 := by ext v; simp [potentialOutput]
    rw [hh] at hid
    exact sub_eq_zero.mp hid
  intro v
  rw [show (⟨0, Nat.zero_lt_succ L⟩ : Fin (L+1)) = s from rfl, heq]
  by_cases hv : v.val = 0
  · have hvs : v = s := Fin.ext hv
    subst v
    simp only [potentialOutput, LocalPush.deg, s, star_degree_center, z, ite_true]
    field_simp [hα0.ne', hLr.ne', h2.ne']
  · simp only [potentialOutput, LocalPush.deg, star_degree_leaf L v hv, Nat.cast_one,
      z, hv, ite_false, mul_one]
    field_simp [hα0.ne', hLr.ne', h2.ne']
    <;> ring

lemma nonzero_output_label {n : ℕ} (o : SparseOutput) (v : Fin n)
    (hn : outputVector o v ≠ 0) : (v.val : ℤ) ∈ o.map Prod.fst := by
  induction o with
  | nil => simp [outputVector] at hn
  | cons a o ih =>
    by_cases ha : a.1 = (v.val : ℤ)
    · simp [ha]
    · have ho : outputVector o v ≠ 0 := by
        simpa [outputVector, ha] using hn
      simp [ih ho]

lemma output_leaf_count (L : ℕ) (o : SparseOutput)
    (ho : ∀ v : Fin (L+1), v.val ≠ 0 → outputVector o v ≠ 0) : L ≤ o.length := by
  classical
  let leaves : Finset (Fin (L+1)) := Finset.univ.erase ⟨0, Nat.zero_lt_succ L⟩
  let labels : Finset ℤ := (o.map Prod.fst).toFinset
  have hsub : leaves.image (fun v => (v.val : ℤ)) ⊆ labels := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    have hv0 : v.val ≠ 0 := fun h =>
      (Finset.mem_erase.mp hv).1 (Fin.ext h)
    exact List.mem_toFinset.mpr (nonzero_output_label o v (ho v hv0))
  have hinj : Function.Injective (fun v : Fin (L+1) => (v.val : ℤ)) := by
    intro u v h
    apply Fin.ext
    exact Int.natCast_inj.mp h
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at hcard
  have hleaves : leaves.card = L := by simp [leaves]
  rw [hleaves] at hcard
  have hl := List.toFinset_card_le (o.map Prod.fst)
  simp only [List.length_map] at hl
  exact hcard.trans hl

theorem explicit_output_lower_bound_proved : explicitOutputLowerBound := by
  classical
  intro α hα0 hα1
  dsimp only
  let β := (1-α)/(2-α)
  have h2 : 0 < 2-α := by linarith
  have hb : 0 < β := div_pos (sub_pos.mpr hα1) h2
  intro ε hε hεb
  let L := ⌊β/(2*ε)⌋₊
  have hx0 : 0 ≤ β/(2*ε) := le_of_lt (div_pos hb (by positivity))
  have hx2 : (2 : ℝ) ≤ β/(2*ε) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*ε)).mpr
    change ε ≤ β / 4 at hεb
    linarith
  have hL : 1 ≤ L := by
    apply (Nat.le_floor_iff hx0).mpr
    norm_num
    linarith
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hfloor := Nat.sub_one_lt_floor (β/(2*ε))
  have hlow : β/(4*ε) ≤ (L : ℝ) := by
    have he : β/(4*ε) = (β/(2*ε))/2 := by field_simp; norm_num
    rw [he]
    dsimp [L]
    linarith
  have hup : (L : ℝ) ≤ β/(2*ε) := Nat.floor_le hx0
  have hp : 2*ε ≤ β/(L : ℝ) := by
    apply (le_div_iff₀ hLpos).mpr
    have hh := (le_div_iff₀ (by positivity : 0 < 2*ε)).mp hup
    nlinarith
  refine ⟨hL, hlow, ?_, ?_⟩
  · convert! star_ppr L hL α ⟨hα0,hα1⟩ using 1 <;> congr!
  · intro o ho
    have ho' : ACL (star L) α ε ⟨0, Nat.zero_lt_succ L⟩ (outputVector o) := by
      convert! ho using 1 <;> congr!
    have hleaf : ∀ v : Fin (L+1), v.val ≠ 0 → ε ≤ outputVector o v := by
      intro v hv
      have hvacl := ho' v
      rw [star_ppr L hL α ⟨hα0,hα1⟩ v] at hvacl
      simp only [hv, ite_false] at hvacl
      rw [show LocalPush.deg (star L) v = 1 by simp [LocalPush.deg, star_degree_leaf L v hv], mul_one] at hvacl
      have hh := (abs_le.mp hvacl).1
      change -ε ≤ outputVector o v - β/(L : ℝ) at hh
      linarith
    refine ⟨hleaf, ?_⟩
    have hc : L ≤ o.length := output_leaf_count L o (fun v hv =>
      ne_of_gt (lt_of_lt_of_le hε (hleaf v hv)))
    exact hlow.trans (by exact_mod_cast hc)

end
end NearlyOptimalPPR.Computation

open NearlyOptimalPPR.Computation
theorem solution : explicitOutputLowerBound := explicit_output_lower_bound_proved
