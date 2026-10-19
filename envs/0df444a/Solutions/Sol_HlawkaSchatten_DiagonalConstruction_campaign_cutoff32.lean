-- Prove2me | solution 1 for HlawkaSchatten.DiagonalConstruction.campaign_cutoff32
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T14:21:19.144234+00:00
-- url     : https://prove2.me/submissions/2d248eb1-4938-4dee-8392-df24d2c70f2f

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ComplexTransfer
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_CyclicWitness
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_OrbitAveraging
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclicConstant_le_of_complex_constant
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclic_denominator_pos
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_real_bound_of_fin_three
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff32_coarse32
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff32_contract32
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff32_convex_box32
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff32_scalar_window32
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff32_slab_envelopes32
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff_cutoff50

/- Cutoff 32 for the sharp diagonal Hlawka constant: reduction to the scalar window, the slab envelope bounds,
the coarse orientation, the residual-budget localization and convexity on the cutoff-32 box (separate
platform theorems). Builds on Ezzeri Esa's Apache-2.0 Hlawka-Schatten construction and the accepted cutoff-62
and cutoff-50 developments on Prove2Me. -/

namespace HlawkaSchatten.DiagonalCutoff32
open HlawkaSchatten.DiagonalConstruction
theorem slabRadius_pos (p : ℝ) : 0 < slabRadius p := by
  unfold slabRadius; split_ifs <;> norm_num
theorem slabRadius_le (p : ℝ) : slabRadius p ≤ 386/1000 := by
  unfold slabRadius; split_ifs <;> norm_num
end HlawkaSchatten.DiagonalCutoff32


open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

namespace HlawkaCut32

/-- Real coordinate vectors embed isometrically into complex ones. -/
theorem lpNorm_ofReal {n : ℕ} (p : ℝ) (x : Fin n → ℝ) :
    lpNorm p (fun i => (x i : ℂ)) = lpNorm p x := by
  unfold lpNorm
  simp [Complex.norm_real]

/-- A complex coordinate Hlawka constant is also a real one. -/
theorem real_of_complex {n : ℕ} {p C : ℝ}
    (h : HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ) C := by
  intro x y z
  have hc := h (fun i => (x i : ℂ)) (fun i => (y i : ℂ)) (fun i => (z i : ℂ))
  have e1 : (fun i => (x i : ℂ)) + (fun i => (y i : ℂ)) = fun i => ((x + y) i : ℂ) := by
    funext i; simp
  have e2 : (fun i => (x i : ℂ)) + (fun i => (z i : ℂ)) = fun i => ((x + z) i : ℂ) := by
    funext i; simp
  have e3 : (fun i => (y i : ℂ)) + (fun i => (z i : ℂ)) = fun i => ((y + z) i : ℂ) := by
    funext i; simp
  have e4 : (fun i => (x i : ℂ)) + (fun i => (y i : ℂ)) + (fun i => (z i : ℂ)) =
      fun i => ((x + y + z) i : ℂ) := by
    funext i; simp
  unfold tripleGap pairGapSum pairGap at hc ⊢
  rw [e4, e1, e2, e3] at hc
  simpa only [lpNorm_ofReal] using hc

/-- For p ≥ 50 the real bound follows from the accepted complex cutoff-50 theorem. -/
theorem real_bound_ge50 : ∀ p : ℝ, 50 ≤ p → ∀ n : ℕ,
    HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ) (cyclicConstant p) := by
  intro p hp n
  exact real_of_complex ((HlawkaSchatten.DiagonalCutoff.cutoff50 p hp).1 n)

end HlawkaCut32

set_option autoImplicit false

namespace HlawkaCert32Geometry
open HlawkaSchatten.DiagonalConstruction
noncomputable abbrev diagMin : ℝ := 625/1000
noncomputable abbrev diagMax : ℝ := 1065/1000
noncomputable abbrev offMin : ℝ := 849/1000
noncomputable abbrev offMax : ℝ := 1121/1000
abbrev certEntryBox : Set Triple := {X | ∀ j i,
  if j = i then -diagMax ≤ X j i ∧ X j i ≤ -diagMin
  else offMin ≤ X j i ∧ X j i ≤ offMax}
end HlawkaCert32Geometry

namespace HlawkaCert32Curvature
open HlawkaSchatten.DiagonalConstruction
abbrev certEntryBox : Set Triple := HlawkaCert32Geometry.certEntryBox
theorem convex_certEntryBox : Convex ℝ certEntryBox := by
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
end HlawkaCert32Curvature

namespace HlawkaCert32Localization
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
end HlawkaCert32Localization

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace HlawkaCert32Integration
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaCert32Curvature (certEntryBox convex_certEntryBox)
open HlawkaCert32Localization (hlawkaDeficit_eq hlawkaDeficit_smul lpNorm_comp_equiv)

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
theorem conjugate_mem_certEntryBox (e : Equiv.Perm (Fin 3)) {X : Triple} (hX : X ∈ certEntryBox) :
    conjugate e X ∈ certEntryBox := by
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


theorem orbitAverage_mem_certEntryBox {X : Triple} (hX : X ∈ certEntryBox) : orbitAverage X ∈ certEntryBox := by
  apply convex_certEntryBox.sum_mem (t := Finset.univ)
  · intros; norm_num
  · norm_num
  · intro k _
    exact conjugate_mem_certEntryBox _ hX


theorem tripleDeficit_orbitAverage_le {p K : ℝ}
    (hc : ConvexOn ℝ certEntryBox (tripleDeficit p K)) {X : Triple} (hX : X ∈ certEntryBox) :
    tripleDeficit p K (orbitAverage X) ≤ tripleDeficit p K X := by
  have h := hc.map_sum_le (t := Finset.univ) (w := fun _ : Fin 6 ↦ (1 / 6 : ℝ))
    (p := fun k ↦ conjugate (permutations k) X) (by intros; norm_num) (by norm_num)
    (fun _ _ ↦ conjugate_mem_certEntryBox _ hX)
  change tripleDeficit p K (orbitAverage X) ≤ _ at h
  simp only [tripleDeficit_conjugate_six, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, nsmul_eq_mul] at h
  norm_num at h
  linarith


theorem average_parameter_bounds {X : Triple} (hX : X ∈ certEntryBox) :
    0 < averageOffDiagonal X ∧ -averageDiagonal X / averageOffDiagonal X ∈ Set.Icc (1 / 2) 2 := by
  have hbar := orbitAverage_mem_certEntryBox hX
  have hd := hbar 0 0
  have ho := hbar 0 1
  rw [orbitAverage_apply] at hd ho
  norm_num [HlawkaCert32Geometry.diagMin,HlawkaCert32Geometry.diagMax,HlawkaCert32Geometry.offMin,HlawkaCert32Geometry.offMax] at hd ho
  have hop : 0 < averageOffDiagonal X := by linarith
  exact ⟨hop, (le_div_iff₀ hop).mpr (by linarith), (div_le_iff₀ hop).mpr (by linarith)⟩


theorem orbitAverage_eq_cyclic (X : Triple) (ho : averageOffDiagonal X ≠ 0) :
    orbitAverage X = ![averageOffDiagonal X • cyclicX (-averageDiagonal X / averageOffDiagonal X),
      averageOffDiagonal X • cyclicY (-averageDiagonal X / averageOffDiagonal X),
      averageOffDiagonal X • cyclicZ (-averageDiagonal X / averageOffDiagonal X)] := by
  ext j i
  rw [orbitAverage_apply]
  fin_cases j <;> fin_cases i <;> norm_num [cyclicX, cyclicY, cyclicZ] <;> field_simp


theorem tripleDeficit_orbitAverage_nonneg {p : ℝ} (hp : 1 < p) {X : Triple} (hX : X ∈ certEntryBox) :
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
    (hc : ConvexOn ℝ certEntryBox (tripleDeficit p (cyclicConstant p)))
    {X : Triple} (hX : X ∈ certEntryBox) : 0 ≤ tripleDeficit p (cyclicConstant p) X :=
  (tripleDeficit_orbitAverage_nonneg hp hX).trans (tripleDeficit_orbitAverage_le hc hX)


/-- Localization and convexity suffice for the real three-coordinate bound. -/
theorem real_bound_of_box_convex {p : ℝ} (hp : 1 < p)
    (hlocal : ∀ x y z : Fin 3 → ℝ,
      hlawkaDeficit p (cyclicConstant p) x y z < 0 →
        ∃ X ∈ certEntryBox, tripleDeficit p (cyclicConstant p) X < 0)
    (hc : ConvexOn ℝ certEntryBox (tripleDeficit p (cyclicConstant p))) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  intro x y z
  by_contra hn
  have hf : hlawkaDeficit p (cyclicConstant p) x y z < 0 := by
    rw [hlawkaDeficit_eq]
    linarith
  obtain ⟨X, hX, hneg⟩ := hlocal x y z hf
  exact (not_lt_of_ge (tripleDeficit_nonneg_of_convex hp hc hX)) hneg


end HlawkaCert32Integration

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem HlawkaCut32.real_bound32 : ∀ p : ℝ, 32 ≤ p → ∀ n : ℕ,
    HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ) (cyclicConstant p) := by
  intro p hp n
  by_cases h50 : 50 ≤ p
  · exact HlawkaCut32.real_bound_ge50 p h50 n
  have hp50 : p ≤ 50 := by linarith
  have hscalar := HlawkaSchatten.DiagonalCutoff32.scalar_window32 p hp hp50
  have henv := HlawkaSchatten.DiagonalCutoff32.slab_envelopes32 p hp hp50
  have hK : 1 / 2 ≤ cyclicConstant p := by
    have h := HlawkaCert32Integration.one_le_cyclicConstant (p := p) (by linarith)
    linarith
  have hlocal : ∀ x y z : Fin 3 → ℝ,
      hlawkaDeficit p (cyclicConstant p) x y z < 0 →
        ∃ X ∈ HlawkaCert32Curvature.certEntryBox,
          tripleDeficit p (cyclicConstant p) X < 0 := by
    intro x y z hf
    obtain ⟨X, hB0, hS, hT, hG, hneg⟩ := HlawkaSchatten.DiagonalCutoff32.coarse32 p hp hp50 hscalar.1
      (HlawkaSchatten.DiagonalCutoff32.slabRadius p) (HlawkaSchatten.DiagonalCutoff32.slabRadius_pos p)
      (HlawkaSchatten.DiagonalCutoff32.slabRadius_le p) henv x y z hf
    exact ⟨X, HlawkaSchatten.DiagonalCutoff32.contract32 p hp hp50 X hB0 hS hT hG, hneg⟩
  have hc : ConvexOn ℝ HlawkaCert32Curvature.certEntryBox
      (tripleDeficit p (cyclicConstant p)) :=
    HlawkaSchatten.DiagonalCutoff32.convex_box32 p (cyclicConstant p) hp hp50 hscalar.1.le hscalar.2.2
  exact real_bound_of_fin_three (by linarith) hK
    (HlawkaCert32Integration.real_bound_of_box_convex (by linarith) hlocal hc)



set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace HlawkaCertComplex80Transfer
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction MeasureTheory

section NormLaws
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]


theorem lpNorm_const {p : ℝ} (hp : 0 < p) (x : E) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (fun _ : ι ↦ x) = (Fintype.card ι : ℝ) ^ (1 / p) * ‖x‖ := by
  unfold _root_.HlawkaSchatten.DiagonalConstruction.lpNorm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg x), mul_one_div_cancel hp.ne', Real.rpow_one]


theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (c • x) = |c| * _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p x := by
  unfold _root_.HlawkaSchatten.DiagonalConstruction.lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]


theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold HlawkaSchatten.DiagonalConstruction.lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

end NormLaws


theorem cyclicA_pos {p t : ℝ} (ht : 0 ≤ t) : 0 < cyclicA p t := by
  unfold cyclicA
  exact Real.rpow_pos_of_pos (by positivity) _


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


theorem cyclicRatio_le_constant {p t : ℝ} (hp : 1 < p)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : cyclicRatio p t ≤ cyclicConstant p := by
  have hc := (continuousOn_cyclicRatio hp).mono
    (show Set.Icc (1 / 2 : ℝ) 2 ⊆ Set.Ici 0 from fun s hs ↦ by
      simp only [Set.mem_Ici]; linarith [hs.1])
  exact le_csSup (isCompact_Icc.image_of_continuousOn hc).bddAbove
    (Set.mem_image_of_mem (cyclicRatio p) ht)


theorem cyclicRatio_two (p : ℝ) : cyclicRatio p 2 = 1 := by
  have hA : 0 < cyclicA p 2 := cyclicA_pos (by norm_num)
  have hB : cyclicB p 2 = cyclicA p 2 := by
    norm_num [cyclicA, cyclicB, add_comm]
  rw [cyclicRatio, hB]
  norm_num only [sub_self, abs_zero, mul_zero, sub_zero]
  have hden : 6 * cyclicA p 2 - 3 * cyclicA p 2 = 3 * cyclicA p 2 := by ring
  rw [hden, div_self (by positivity)]


theorem one_le_cyclicConstant {p : ℝ} (hp : 1 < p) : 1 ≤ cyclicConstant p := by
  rw [← cyclicRatio_two p]
  exact cyclicRatio_le_constant hp (by norm_num)


theorem lpNorm_cyclicX {p t : ℝ} (ht : 0 ≤ t) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicX t) = cyclicA p t := by
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicX, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring


theorem lpNorm_cyclicY {p t : ℝ} (ht : 0 ≤ t) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicY t) = cyclicA p t := by
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicY, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring


theorem lpNorm_cyclicZ {p t : ℝ} (ht : 0 ≤ t) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicZ t) = cyclicA p t := by
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicZ, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring


theorem lpNorm_cyclicXY (p t : ℝ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicX t + cyclicY t) = cyclicB p t := by
  have he : cyclicX t + cyclicY t = ![1 - t, 1 - t, 2] := by
    ext i
    fin_cases i <;> simp [cyclicX, cyclicY] <;> ring
  rw [he]
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicB, Fin.sum_univ_three]
  congr 1
  ring


theorem lpNorm_cyclicXZ (p t : ℝ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicX t + cyclicZ t) = cyclicB p t := by
  have he : cyclicX t + cyclicZ t = ![1 - t, 2, 1 - t] := by
    ext i
    fin_cases i <;> simp [cyclicX, cyclicZ] <;> ring
  rw [he]
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicB, Fin.sum_univ_three]
  congr 1
  ring


theorem lpNorm_cyclicYZ (p t : ℝ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicY t + cyclicZ t) = cyclicB p t := by
  have he : cyclicY t + cyclicZ t = ![2, 1 - t, 1 - t] := by
    ext i
    fin_cases i <;> simp [cyclicY, cyclicZ] <;> ring
  rw [he]
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicB, Fin.sum_univ_three]
  congr 1
  ring


theorem lpNorm_cyclicXYZ {p : ℝ} (hp : 0 < p) (t : ℝ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicX t + cyclicY t + cyclicZ t) =
      (3 : ℝ) ^ (1 / p) * |2 - t| := by
  have he : cyclicX t + cyclicY t + cyclicZ t = fun _ ↦ 2 - t := by
    ext i
    fin_cases i <;> simp [cyclicX, cyclicY, cyclicZ] <;> ring
  rw [he, lpNorm_const hp]
  simp


theorem cyclic_tripleGap {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    tripleGap (_root_.HlawkaSchatten.DiagonalConstruction.lpNorm p) (cyclicX t) (cyclicY t) (cyclicZ t) =
      3 * cyclicA p t - (3 : ℝ) ^ (1 / p) * |2 - t| := by
  rw [tripleGap, lpNorm_cyclicX ht, lpNorm_cyclicY ht, lpNorm_cyclicZ ht,
    lpNorm_cyclicXYZ hp]
  ring


theorem cyclic_pairGapSum {p t : ℝ} (ht : 0 ≤ t) :
    pairGapSum (_root_.HlawkaSchatten.DiagonalConstruction.lpNorm p) (cyclicX t) (cyclicY t) (cyclicZ t) =
      6 * cyclicA p t - 3 * cyclicB p t := by
  simp only [pairGapSum, pairGap, lpNorm_cyclicX ht, lpNorm_cyclicY ht,
    lpNorm_cyclicZ ht, lpNorm_cyclicXY, lpNorm_cyclicXZ, lpNorm_cyclicYZ]
  ring

section Deficit
variable {ι : Type*} [Fintype ι]


theorem hlawkaDeficit_eq (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x y z =
      K * pairGapSum (_root_.HlawkaSchatten.DiagonalConstruction.lpNorm p) x y z - tripleGap (_root_.HlawkaSchatten.DiagonalConstruction.lpNorm p) x y z := by
  unfold hlawkaDeficit pairGapSum pairGap tripleGap
  ring


theorem hlawkaDeficit_smul {p : ℝ} (hp : 0 < p) (K c : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K (c • x) (c • y) (c • z) = |c| * hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← smul_add, lpNorm_smul hp]
  ring

end Deficit


section CircleTransfer

instance circleMeasure_isProbability : IsProbabilityMeasure circleMeasure :=
  ⟨by simpa only [TopologicalSpace.PositiveCompacts.coe_top] using
    (Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts Circle)))⟩


theorem continuous_circle_projection_power {p : ℝ} (hp : 0 < p) (z : ℂ) :
    Continuous (fun u : Circle ↦ |((u : ℂ) * z).re| ^ p) := by
  exact ((Complex.continuous_re.comp (continuous_subtype_val.mul continuous_const)).abs).rpow_const
    (fun _ ↦ Or.inr hp.le)


theorem circleMoment_pos {p : ℝ} (hp : 0 < p) : 0 < circleMoment p := by
  have hc : Continuous (fun u : Circle ↦ |(u : ℂ).re| ^ p) := by
    simpa only [mul_one] using continuous_circle_projection_power hp 1
  exact integral_pos_of_integrable_nonneg_nonzero hc
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (fun u ↦ Real.rpow_nonneg (abs_nonneg _) _) (x := (1 : Circle)) (by simp)


theorem integral_circle_projection_power {p : ℝ} (hp : 0 < p) (z : ℂ) :
    (∫ u : Circle, |((u : ℂ) * z).re| ^ p ∂circleMeasure) = circleMoment p * ‖z‖ ^ p := by
  by_cases hz : z = 0
  · simp [hz, hp.ne']
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let v : Circle := ⟨z / (‖z‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z), div_self hn])⟩
  have hv : (v : ℂ) * (‖z‖ : ℂ) = z := div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hn)
  have hre (u : Circle) : ((u : ℂ) * z).re = ‖z‖ * ((v * u : Circle) : ℂ).re := by
    calc
      _ = (((v : ℂ) * (u : ℂ)) * (‖z‖ : ℂ)).re := by
        congr 1
        conv_lhs => rw [← hv]
        ring
      _ = _ := by simp only [Circle.coe_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]; ring
  simp_rw [hre, abs_mul, abs_of_nonneg (norm_nonneg z),
    Real.mul_rpow (norm_nonneg z) (abs_nonneg _)]
  rw [integral_const_mul]
  have hrot : (∫ a : Circle, |((v * a : Circle) : ℂ).re| ^ p ∂circleMeasure) = circleMoment p :=
    integral_mul_left_eq_self (μ := circleMeasure) (fun a : Circle ↦ |(a : ℂ).re| ^ p) v
  change ‖z‖ ^ p * (∫ a : Circle, |((v * a : Circle) : ℂ).re| ^ p ∂circleMeasure) = _
  rw [hrot]
  exact mul_comm _ _

variable {ι : Type*} [Fintype ι]


theorem continuous_projectionPower {p : ℝ} (hp : 0 < p) (z : ι → ℂ) :
    Continuous (projectionPower p z) :=
  continuous_finsetSum _ fun i _ ↦ continuous_circle_projection_power hp (z i)


theorem integral_projectionPower {p : ℝ} (hp : 0 < p) (z : ι → ℂ) :
    (∫ u : Circle, projectionPower p z u ∂circleMeasure) = circleMoment p * ∑ i, ‖z i‖ ^ p := by
  unfold projectionPower
  rw [integral_finsetSum Finset.univ (fun i _ ↦
    (continuous_circle_projection_power hp (z i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  simp only [integral_circle_projection_power hp, Finset.mul_sum]

variable {κ : Type*} [Fintype κ]

omit [Fintype ι] [Fintype κ] in

theorem finiteProjection_add (p : ℝ) (w : κ → ℝ) (u : κ → Circle) (z v : ι → ℂ) :
    finiteProjection p w u (z + v) = finiteProjection p w u z + finiteProjection p w u v := by
  ext k
  simp [finiteProjection, mul_add, Complex.add_re]


theorem lpNorm_finiteProjection {p : ℝ} (hp : 0 < p) (w : κ → ℝ) (u : κ → Circle)
    (hw : ∀ k, 0 ≤ w k) (z : ι → ℂ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (finiteProjection p w u z) = (∑ k, w k * projectionPower p z (u k)) ^ (1 / p) := by
  unfold _root_.HlawkaSchatten.DiagonalConstruction.lpNorm
  congr 1
  simp only [finiteProjection, Fintype.sum_prod_type, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (hw _) _)]
  simp_rw [Real.mul_rpow (Real.rpow_nonneg (hw _) _) (abs_nonneg _),
    ← Real.rpow_mul (hw _), one_div_mul_cancel hp.ne', Real.rpow_one]
  simp only [projectionPower, Finset.mul_sum]


theorem continuous_powerDeficit {p : ℝ} (hp : 0 < p) (K : ℝ) : Continuous (powerDeficit p K) := by
  have hc (i : Fin 7) : Continuous (fun a : Fin 7 → ℝ ↦ (a i) ^ (1 / p)) :=
    (continuous_apply i).rpow_const (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))
  exact ((continuous_const.mul (((hc 0).add (hc 1)).add (hc 2))).add (hc 6)).sub
    (continuous_const.mul (((hc 3).add (hc 4)).add (hc 5)))


theorem continuous_sevenProjections {p : ℝ} (hp : 0 < p) (x y z : ι → ℂ) :
    Continuous (sevenProjections p x y z) :=
  continuous_pi fun k ↦ continuous_projectionPower hp (sevenVectors x y z k)


theorem powerDeficit_nonneg_on_projection_hull {p : ℝ} (hp : 1 < p)
    (hreal : HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p)) (x y z : ι → ℂ) :
    convexHull ℝ (Set.range (sevenProjections p x y z)) ⊆
      {a | 0 ≤ powerDeficit p (cyclicConstant p) a} := by
  classical
  intro a ha
  have hp0 : 0 < p := by linarith
  obtain ⟨κ, _, w, points, hw, _, hpoints, hsum⟩ := mem_convexHull_iff_exists_fintype.mp ha
  choose u hu using hpoints
  have hsum' : ∑ k, w k • sevenProjections p x y z (u k) = a := by
    simpa only [hu] using hsum
  let R : (ι → ℂ) → κ × ι → ℝ := finiteProjection p w u
  have hadd (v v' : ι → ℂ) : R (v + v') = R v + R v' := finiteProjection_add p w u v v'
  have hn (k : Fin 7) : lpNorm p (R (sevenVectors x y z k)) = (a k) ^ (1 / p) := by
    rw [lpNorm_finiteProjection hp0 w u hw]
    congr 1
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sevenProjections] using
      congrFun hsum' k
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  have h3 := hn 3
  have h4 := hn 4
  have h5 := hn 5
  have h6 := hn 6
  change lpNorm p (R x) = (a 0) ^ (1 / p) at h0
  change lpNorm p (R y) = (a 1) ^ (1 / p) at h1
  change lpNorm p (R z) = (a 2) ^ (1 / p) at h2
  change lpNorm p (R (x + y)) = (a 3) ^ (1 / p) at h3
  change lpNorm p (R (x + z)) = (a 4) ^ (1 / p) at h4
  change lpNorm p (R (y + z)) = (a 5) ^ (1 / p) at h5
  change lpNorm p (R (x + y + z)) = (a 6) ^ (1 / p) at h6
  have h := real_bound_of_fin_three hp (by linarith [one_le_cyclicConstant hp]) hreal (R x) (R y) (R z)
  simp only [tripleGap, pairGapSum, pairGap, ← hadd] at h
  change 0 ≤ powerDeficit p (cyclicConstant p) a
  unfold powerDeficit
  rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6]
  nlinarith


/-- The sharp constant passes from real coordinates to complex coordinates. -/
theorem complex_hlawka_bound {p : ℝ} (hp : 1 < p)
    (hreal : HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p)) :
    HasHlawkaConstant (lpNorm p : (ι → ℂ) → ℝ) (cyclicConstant p) := by
  intro x y z
  have hp0 : 0 < p := by linarith
  let F := sevenProjections p x y z
  let m : Fin 7 → ℝ := ∫ u : Circle, F u ∂circleMeasure
  have hcont : Continuous F := continuous_sevenProjections hp0 x y z
  have hfi : Integrable F circleMeasure :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm : m ∈ closure (convexHull ℝ (Set.range F)) := by
    apply (convex_convexHull ℝ (Set.range F)).closure.integral_mem isClosed_closure _ hfi
    exact Filter.Eventually.of_forall fun u ↦
      subset_closure (subset_convexHull ℝ (Set.range F) (Set.mem_range_self u))
  have hclosed : IsClosed {a | 0 ≤ powerDeficit p (cyclicConstant p) a} :=
    isClosed_le continuous_const (continuous_powerDeficit hp0 _)
  have hnon : 0 ≤ powerDeficit p (cyclicConstant p) m :=
    (closure_minimal (powerDeficit_nonneg_on_projection_hull hp hreal x y z) hclosed) hm
  have hcoord (k : Fin 7) : m k = circleMoment p * ∑ i, ‖sevenVectors x y z k i‖ ^ p := by
    calc
      _ = ∫ u : Circle, F u k ∂circleMeasure :=
        ((ContinuousLinearMap.proj k : (Fin 7 → ℝ) →L[ℝ] ℝ).integral_comp_comm hfi).symm
      _ = _ := integral_projectionPower hp0 (sevenVectors x y z k)
  let c := circleMoment p ^ (1 / p)
  have hc : 0 < c := Real.rpow_pos_of_pos (circleMoment_pos hp0) _
  have hroot (k : Fin 7) : (m k) ^ (1 / p) = c * lpNorm p (sevenVectors x y z k) := by
    rw [hcoord, Real.mul_rpow (circleMoment_pos hp0).le
      (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
    rfl
  simp only [powerDeficit, hroot] at hnon
  change 0 ≤ (2 * cyclicConstant p - 1) *
      (c * lpNorm p x + c * lpNorm p y + c * lpNorm p z) + c * lpNorm p (x + y + z) -
    cyclicConstant p * (c * lpNorm p (x + y) + c * lpNorm p (x + z) + c * lpNorm p (y + z)) at hnon
  have hscaled : 0 ≤ c * (cyclicConstant p * pairGapSum (lpNorm p) x y z -
      tripleGap (lpNorm p) x y z) := by
    convert hnon using 1
    unfold pairGapSum pairGap tripleGap
    ring
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hc).mp hscaled)

end CircleTransfer


/-- A real bound in dimension three gives uniform complex sharpness,
including the empty coordinate dimension. -/
theorem isLeast_of_real_bound {p : ℝ} (hp : 1 < p)
    (hreal : HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p)) :
    IsLeast {C : ℝ | ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C} (cyclicConstant p) := by
  constructor
  · intro n
    exact complex_hlawka_bound hp hreal
  · intro C hC
    exact cyclicConstant_le_of_complex_constant hp (n := 3) (by rfl) (hC 3)

end HlawkaCertComplex80Transfer



set_option autoImplicit false
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution : ∀ p : ℝ, 32 ≤ p →
    IsLeast {C : ℝ | ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C} (cyclicConstant p) := by
  intro p hp
  exact HlawkaCertComplex80Transfer.isLeast_of_real_bound (by linarith)
    (HlawkaCut32.real_bound32 p hp 3)

