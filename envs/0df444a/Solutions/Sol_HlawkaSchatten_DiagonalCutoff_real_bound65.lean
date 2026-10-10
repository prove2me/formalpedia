-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff.real_bound65
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-10T06:24:07.979548+00:00
-- url     : https://prove2.me/submissions/2ee8f5d7-315a-4fe8-865a-d3d8a8076e54

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_CyclicWitness
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_OrbitAveraging
import Definitions.Def_HlawkaSchatten_GapComparison
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclic_denominator_pos
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_real_bound_of_fin_three
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff_real_bound66
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff_scalar_window65
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff_local_failure65
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff_convex_box65
import Mathlib
set_option autoImplicit false

namespace HlawkaCodex65Geometry
open HlawkaSchatten.DiagonalConstruction
noncomputable abbrev entryMin : ℝ := 4851/6500
noncomputable abbrev entryMax : ℝ := 273/250
abbrev codexEntryBox : Set Triple := {X | ∀ j i,
  if j = i then -entryMax ≤ X j i ∧ X j i ≤ -entryMin
  else entryMin ≤ X j i ∧ X j i ≤ entryMax}
end HlawkaCodex65Geometry

namespace HlawkaCodex65Curvature
open HlawkaSchatten.DiagonalConstruction
abbrev codexEntryBox : Set Triple := HlawkaCodex65Geometry.codexEntryBox
theorem convex_codexEntryBox : Convex ℝ codexEntryBox := by
  intro X hX Y hY a b ha hb hab j i
  have hx := hX j i
  have hy := hY j i
  have hw (l u : ℝ) (hx : l ≤ X j i ∧ X j i ≤ u) (hy : l ≤ Y j i ∧ Y j i ≤ u) :
      l ≤ (a • X+b • Y) j i ∧ (a • X+b • Y) j i ≤ u := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hlo := add_le_add (mul_le_mul_of_nonneg_left hx.1 ha) (mul_le_mul_of_nonneg_left hy.1 hb)
    have hhi := add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
    rw [← add_mul, hab, one_mul] at hlo hhi
    exact ⟨hlo,hhi⟩
  by_cases he : j = i
  · simp only [if_pos he] at hx hy ⊢
    exact hw _ _ hx hy
  · simp only [if_neg he] at hx hy ⊢
    exact hw _ _ hx hy
end HlawkaCodex65Curvature

namespace HlawkaCodex65Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

theorem hlawkaDeficit_eq (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x y z =
      K * pairGapSum (lpNorm p) x y z - tripleGap (lpNorm p) x y z := by
  unfold hlawkaDeficit pairGapSum pairGap tripleGap
  ring

theorem hlawkaDeficit_smul {p : ℝ} (hp : 0 < p) (K c : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K (c • x) (c • y) (c • z) = |c| * hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← smul_add, lpNorm_smul hp]
  ring
end HlawkaCodex65Localization

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace HlawkaCodex65Integration
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaCodex65Curvature (codexEntryBox convex_codexEntryBox)
open HlawkaCodex65Localization (hlawkaDeficit_eq hlawkaDeficit_smul lpNorm_comp_equiv)

theorem continuous_cyclicA {p : ℝ} (hp : 0 < p) : Continuous (cyclicA p) := by
  exact ((Real.continuous_rpow_const hp.le).add continuous_const).rpow_const
    (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))

theorem continuous_cyclicB {p : ℝ} (hp : 0 < p) : Continuous (cyclicB p) := by
  apply Continuous.rpow_const _ (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))
  exact (continuous_const.mul
    ((continuous_const.sub continuous_id).abs.rpow_const
      (fun _ ↦ Or.inr hp.le))).add continuous_const

theorem continuousOn_cyclicRatio {p : ℝ} (hp : 1 < p) :
    ContinuousOn (cyclicRatio p) (Set.Ici 0) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  apply ContinuousOn.div
  · exact ((continuous_const.mul (continuous_cyclicA hp0)).sub
      (continuous_const.mul (continuous_const.sub continuous_id).abs)).continuousOn
  · exact ((continuous_const.mul (continuous_cyclicA hp0)).sub
      (continuous_const.mul (continuous_cyclicB hp0))).continuousOn
  · intro t ht
    exact (cyclic_denominator_pos hp ht).ne'

theorem lpNorm_const {p : ℝ} (hp : 0 < p) {ι : Type*} [Fintype ι] (x : ℝ) :
    lpNorm p (fun _ : ι ↦ x) = (Fintype.card ι : ℝ) ^ (1 / p) * |x| := by
  unfold lpNorm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.norm_eq_abs]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _),
    ← Real.rpow_mul (abs_nonneg x), mul_one_div_cancel hp.ne', Real.rpow_one]

theorem lpNorm_cyclicX {p t : ℝ} (ht : 0 ≤ t) :
    lpNorm p (cyclicX t) = cyclicA p t := by
  simp [lpNorm, cyclicX, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring

theorem lpNorm_cyclicY {p t : ℝ} (ht : 0 ≤ t) :
    lpNorm p (cyclicY t) = cyclicA p t := by
  simp [lpNorm, cyclicY, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring

theorem lpNorm_cyclicZ {p t : ℝ} (ht : 0 ≤ t) :
    lpNorm p (cyclicZ t) = cyclicA p t := by
  simp [lpNorm, cyclicZ, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring

theorem lpNorm_cyclicXY {p t : ℝ} (ht : 0 ≤ t) :
    lpNorm p (cyclicX t + cyclicY t) = cyclicB p t := by
  simp [lpNorm, cyclicX, cyclicY, cyclicB, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring

theorem lpNorm_cyclicXZ {p t : ℝ} (ht : 0 ≤ t) :
    lpNorm p (cyclicX t + cyclicZ t) = cyclicB p t := by
  simp [lpNorm, cyclicX, cyclicZ, cyclicB, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring

theorem lpNorm_cyclicYZ {p t : ℝ} (ht : 0 ≤ t) :
    lpNorm p (cyclicY t + cyclicZ t) = cyclicB p t := by
  simp [lpNorm, cyclicY, cyclicZ, cyclicB, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring

theorem cyclic_tripleGap {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    tripleGap (lpNorm p) (cyclicX t) (cyclicY t) (cyclicZ t) =
      3 * cyclicA p t - (3 : ℝ) ^ (1 / p) * |2 - t| := by
  have hsum : cyclicX t + cyclicY t + cyclicZ t = fun _ : Fin 3 ↦ 2 - t := by
    ext i
    fin_cases i <;> simp [cyclicX, cyclicY, cyclicZ] <;> ring
  rw [tripleGap, lpNorm_cyclicX ht, lpNorm_cyclicY ht, lpNorm_cyclicZ ht, hsum,
    lpNorm_const hp, Fintype.card_fin]
  ring

theorem cyclic_pairGapSum {p t : ℝ} (ht : 0 ≤ t) :
    pairGapSum (lpNorm p) (cyclicX t) (cyclicY t) (cyclicZ t) =
      6 * cyclicA p t - 3 * cyclicB p t := by
  simp only [pairGapSum, pairGap, lpNorm_cyclicX ht, lpNorm_cyclicY ht,
    lpNorm_cyclicZ ht, lpNorm_cyclicXY ht, lpNorm_cyclicXZ ht, lpNorm_cyclicYZ ht]
  ring

theorem cyclicRatio_le_constant {p t : ℝ} (hp : 1 < p)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : cyclicRatio p t ≤ cyclicConstant p := by
  have hc := (continuousOn_cyclicRatio hp).mono
    (show Set.Icc (1 / 2 : ℝ) 2 ⊆ Set.Ici 0 from fun s hs ↦ by
      simp only [Set.mem_Ici]; linarith [hs.1])
  exact le_csSup (isCompact_Icc.image_of_continuousOn hc).bddAbove
    (Set.mem_image_of_mem (cyclicRatio p) ht)

theorem one_le_cyclicConstant {p : ℝ} (hp : 1 < p) : 1 ≤ cyclicConstant p := by
  have htwo : cyclicRatio p 2 = 1 := by
    have hB : cyclicB p 2 = cyclicA p 2 := by
      norm_num [cyclicA, cyclicB, add_comm]
    rw [cyclicRatio, hB]
    norm_num only [sub_self, abs_zero, mul_zero, sub_zero]
    have hden : 6 * cyclicA p 2 - 3 * cyclicA p 2 = 3 * cyclicA p 2 := by ring
    rw [hden, div_self (by
      have : 0 < cyclicA p 2 := by
        unfold cyclicA
        exact Real.rpow_pos_of_pos (by positivity) _
      positivity)]
  rw [← htwo]
  exact cyclicRatio_le_constant hp (by norm_num)
theorem conjugate_mem_codexEntryBox (e : Equiv.Perm (Fin 3)) {X : Triple} (hX : X ∈ codexEntryBox) :
    conjugate e X ∈ codexEntryBox := by
  intro j i
  simpa [conjugate, e.injective.eq_iff] using hX (e j) (e i)

private def permutations : Fin 6 → Equiv.Perm (Fin 3) :=
  ![Equiv.refl _, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
    (Equiv.swap 0 1).trans (Equiv.swap 1 2), (Equiv.swap 1 2).trans (Equiv.swap 0 1)]


private theorem tripleDeficit_conjugate_six (p K : ℝ) (X : Triple) (k : Fin 6) :
    tripleDeficit p K (conjugate (permutations k) X) = tripleDeficit p K X := by
  have he (e : Equiv.Perm (Fin 3)) :
      tripleDeficit p K (conjugate e X) = hlawkaDeficit p K (X (e 0)) (X (e 1)) (X (e 2)) := by
    have hsum (u v : Fin 3 → ℝ) : u ∘ e + v ∘ e = (u + v) ∘ e := rfl
    change hlawkaDeficit p K (X (e 0) ∘ e) (X (e 1) ∘ e) (X (e 2) ∘ e) = _
    simp only [hlawkaDeficit, hsum, lpNorm_comp_equiv]
  rw [he]
  fin_cases k <;> simp [permutations, tripleDeficit, hlawkaDeficit, Equiv.swap_apply_def,
    add_comm, add_left_comm, add_assoc]


theorem orbitAverage_apply (X : Triple) (j i : Fin 3) :
    orbitAverage X j i = if i = j then averageDiagonal X else averageOffDiagonal X := by
  fin_cases j <;> fin_cases i <;>
    norm_num [orbitAverage, permutations, conjugate, Fin.sum_univ_succ, Equiv.swap_apply_def,
      averageDiagonal, averageOffDiagonal, Fin.ext_iff] <;> ring!


theorem orbitAverage_mem_codexEntryBox {X : Triple} (hX : X ∈ codexEntryBox) : orbitAverage X ∈ codexEntryBox := by
  apply convex_codexEntryBox.sum_mem (t := Finset.univ)
  · intros; norm_num
  · norm_num
  · intro k _
    exact conjugate_mem_codexEntryBox _ hX


theorem tripleDeficit_orbitAverage_le {p K : ℝ}
    (hc : ConvexOn ℝ codexEntryBox (tripleDeficit p K)) {X : Triple} (hX : X ∈ codexEntryBox) :
    tripleDeficit p K (orbitAverage X) ≤ tripleDeficit p K X := by
  have h := hc.map_sum_le (t := Finset.univ) (w := fun _ : Fin 6 ↦ (1 / 6 : ℝ))
    (p := fun k ↦ conjugate (permutations k) X) (by intros; norm_num) (by norm_num)
    (fun _ _ ↦ conjugate_mem_codexEntryBox _ hX)
  change tripleDeficit p K (orbitAverage X) ≤ _ at h
  simp only [tripleDeficit_conjugate_six, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, nsmul_eq_mul] at h
  norm_num at h
  linarith


theorem average_parameter_bounds {X : Triple} (hX : X ∈ codexEntryBox) :
    0 < averageOffDiagonal X ∧ -averageDiagonal X / averageOffDiagonal X ∈ Set.Icc (1 / 2) 2 := by
  have hbar := orbitAverage_mem_codexEntryBox hX
  have hd := hbar 0 0
  have ho := hbar 0 1
  rw [orbitAverage_apply] at hd ho
  norm_num [HlawkaCodex65Geometry.entryMin,HlawkaCodex65Geometry.entryMax] at hd ho
  have hop : 0 < averageOffDiagonal X := by linarith
  exact ⟨hop, (le_div_iff₀ hop).mpr (by linarith), (div_le_iff₀ hop).mpr (by linarith)⟩


theorem orbitAverage_eq_cyclic (X : Triple) (ho : averageOffDiagonal X ≠ 0) :
    orbitAverage X = ![averageOffDiagonal X • cyclicX (-averageDiagonal X / averageOffDiagonal X),
      averageOffDiagonal X • cyclicY (-averageDiagonal X / averageOffDiagonal X),
      averageOffDiagonal X • cyclicZ (-averageDiagonal X / averageOffDiagonal X)] := by
  ext j i
  rw [orbitAverage_apply]
  fin_cases j <;> fin_cases i <;> norm_num [cyclicX, cyclicY, cyclicZ] <;> field_simp


theorem tripleDeficit_orbitAverage_nonneg {p : ℝ} (hp : 1 < p) {X : Triple} (hX : X ∈ codexEntryBox) :
    0 ≤ tripleDeficit p (cyclicConstant p) (orbitAverage X) := by
  obtain ⟨ho, ht⟩ := average_parameter_bounds hX
  let t := -averageDiagonal X / averageOffDiagonal X
  have ht0 : 0 ≤ t := by dsimp [t]; linarith [ht.1]
  have hratio := cyclicRatio_le_constant hp ht
  have hD := cyclic_denominator_pos hp ht0
  rw [cyclicRatio, div_le_iff₀ hD] at hratio
  have hcyclic : 0 ≤ hlawkaDeficit p (cyclicConstant p) (cyclicX t) (cyclicY t) (cyclicZ t) := by
    rw [hlawkaDeficit_eq, cyclic_tripleGap (zero_lt_one.trans hp) ht0, cyclic_pairGapSum ht0]
    exact sub_nonneg.mpr hratio
  rw [orbitAverage_eq_cyclic X ho.ne']
  change 0 ≤ hlawkaDeficit p (cyclicConstant p) (averageOffDiagonal X • cyclicX t)
    (averageOffDiagonal X • cyclicY t) (averageOffDiagonal X • cyclicZ t)
  rw [hlawkaDeficit_smul (zero_lt_one.trans hp)]
  exact mul_nonneg (abs_nonneg _) hcyclic


theorem tripleDeficit_nonneg_of_convex {p : ℝ} (hp : 1 < p)
    (hc : ConvexOn ℝ codexEntryBox (tripleDeficit p (cyclicConstant p)))
    {X : Triple} (hX : X ∈ codexEntryBox) : 0 ≤ tripleDeficit p (cyclicConstant p) X :=
  (tripleDeficit_orbitAverage_nonneg hp hX).trans (tripleDeficit_orbitAverage_le hc hX)


/-- Localization and convexity suffice for the real three-coordinate bound. -/
theorem real_bound_of_box_convex {p : ℝ} (hp : 1 < p)
    (hlocal : ∀ x y z : Fin 3 → ℝ,
      hlawkaDeficit p (cyclicConstant p) x y z < 0 →
        ∃ X ∈ codexEntryBox, tripleDeficit p (cyclicConstant p) X < 0)
    (hc : ConvexOn ℝ codexEntryBox (tripleDeficit p (cyclicConstant p))) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  intro x y z
  by_contra hn
  have hf : hlawkaDeficit p (cyclicConstant p) x y z < 0 := by
    rw [hlawkaDeficit_eq]
    linarith
  obtain ⟨X, hX, hneg⟩ := hlocal x y z hf
  exact (not_lt_of_ge (tripleDeficit_nonneg_of_convex hp hc hX)) hneg


end HlawkaCodex65Integration

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution : ∀ p : ℝ, 65 ≤ p → ∀ n : ℕ,
    HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ) (cyclicConstant p) := by
  intro p hp n
  by_cases h66 : 66 ≤ p
  · exact HlawkaSchatten.DiagonalCutoff.real_bound66 p h66 n
  have hscalar := HlawkaSchatten.DiagonalCutoff.scalar_window65 p hp (by linarith)
  have hK : 1 / 2 ≤ cyclicConstant p := by
    have h := HlawkaCodex65Integration.one_le_cyclicConstant (p := p) (by linarith)
    linarith
  have hlocal : ∀ x y z : Fin 3 → ℝ,
      hlawkaDeficit p (cyclicConstant p) x y z < 0 →
        ∃ X ∈ HlawkaCodex65Curvature.codexEntryBox,
          tripleDeficit p (cyclicConstant p) X < 0 :=
    HlawkaSchatten.DiagonalCutoff.local_failure65 p hp hscalar.1 hscalar.2.1
  have hc : ConvexOn ℝ HlawkaCodex65Curvature.codexEntryBox
      (tripleDeficit p (cyclicConstant p)) :=
    HlawkaSchatten.DiagonalCutoff.convex_box65 p (cyclicConstant p) hp hscalar.1.le
      (by linarith [hscalar.2.2])
  exact real_bound_of_fin_three (by linarith) hK
    (HlawkaCodex65Integration.real_bound_of_box_convex (by linarith) hlocal hc)
#print axioms solution
