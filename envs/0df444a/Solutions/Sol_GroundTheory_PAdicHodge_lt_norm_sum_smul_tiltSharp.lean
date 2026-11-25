-- Prove2me | solution 1 for GroundTheory.PAdicHodge.lt_norm_sum_smul_tiltSharp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:29:28.844122+00:00
-- url     : https://prove2.me/submissions/fc6576f9-0f99-47da-b0d7-de3c32034fd0

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_OrthoBasis
import Definitions.Def_GroundTheory_PAdicHodge_UntiltIndep
import Theorems.Thm_GroundTheory_PAdicHodge_norm_natCast_algebra
import Theorems.Thm_GroundTheory_PAdicHodge_norm_eq_of_norm_sub_lt
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_mk_untilt_eq
import Theorems.Thm_GroundTheory_PAdicHodge_norm_untilt_sum_sub_le
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution {ι : Type*} [Fintype ι] {w : ι → C♭} {t r ρ : ℝ}
    (hw : ∀ (c : ι → K♭) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖)
    (hw1 : ∀ i, ‖w i‖ ≤ 1) (hwr : ∀ i, r < ‖w i‖) (ht : 0 < t) (hr : 0 ≤ r) (hρ : 0 < ρ)
    (hp : ‖(p : K)‖ ≤ t * r * ρ) {l : ι → K} (hl1 : ∀ i, ‖l i‖ ≤ 1) {j : ι} (hj : ρ < ‖l j‖) :
    t * r * ρ < ‖∑ i, l i • tiltSharp C p (w i)‖ := by
  classical
  have hwj0 : 0 < ‖w j‖ := hr.trans_lt (hwr j)

  have ht1 : t ≤ 1 := by
    have e : ∑ j', (Pi.single j (1 : K♭) : ι → K♭) j' • w j' = w j := by
      rw [Finset.sum_eq_single j (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul])
        (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, one_smul]
    have := hw (Pi.single j 1) j
    rw [e, Pi.single_eq_same, one_smul] at this
    exact le_of_mul_le_mul_right (by linarith) hwj0
  have hr1 : r < 1 := (hwr j).trans_le (hw1 j)
  have htr : t * r ≤ 1 := by nlinarith
  have hpρ : ‖(p : K)‖ ≤ ρ := hp.trans (by nlinarith)
  have hpl : ‖(p : K)‖ < ‖l j‖ := hpρ.trans_lt hj

  have hA : ∀ i, ∃ a : 𝒪K♭, ‖((a.untilt : normInteger K) : K) - l i‖ ≤ ‖(p : K)‖ := fun i => by
    obtain ⟨a, ha⟩ := exists_mk_untilt_eq (p := p)
      (⟨l i, mem_normInteger.2 (hl1 i)⟩ : normInteger K)
    exact ⟨a, mk_eq_mk_iff_norm_sub_le.1 ha⟩
  choose a ha using hA
  choose b hb using fun i => (norm_le_one_iff_exists_algebraMap (K := C) (p := p)).1 (hw1 i)
  set φ := preTiltMap p (algebraMap K C) (norm_algebraMap' C) with hφ
  set d : ι → 𝒪C♭ := fun i => φ (a i) * b i with hd
  have hdw : ∀ i, algebraMap 𝒪C♭ C♭ (d i) = algebraMap 𝒪K♭ K♭ (a i) • w i := by
    intro i
    rw [Algebra.smul_def, algebraMap_tilt_eq, tiltMap_algebraMap, ← hb i, ← map_mul]
  have hsharp : ∀ i, tiltSharp C p (w i) = ((b i).untilt : C) := by
    intro i; rw [← hb i, tiltSharp_algebraMap]
  have hdu : ∀ i, ((d i).untilt : C) = algebraMap K C ((a i).untilt : K) * tiltSharp C p (w i) := by
    intro i
    rw [hd, untilt_mul, Subring.coe_mul, coe_untilt_preTiltMap, hsharp]
  set A : C := ((∑ i, d i).untilt : C) with hA

  have hAn : ‖A‖ = ‖∑ i, algebraMap 𝒪K♭ K♭ (a i) • w i‖ := by
    rw [hA, ← tiltSharp_algebraMap, norm_tiltSharp, map_sum]
    simp only [hdw]
  have hsw : ∀ i, ‖tiltSharp C p (w i)‖ ≤ 1 := fun i => by rw [norm_tiltSharp]; exact hw1 i

  have haj : ‖algebraMap 𝒪K♭ K♭ (a j)‖ = ‖l j‖ := by
    rw [norm_algebraMap_preTilt, preTilt_norm_def]
    exact norm_eq_of_norm_sub_lt ((ha j).trans_lt hpl)
  have hAbig : t * r * ρ < ‖A‖ := by
    rw [hAn]
    refine lt_of_lt_of_le ?_ (hw _ j)
    rw [norm_smul, haj]
    have : ρ * r < ‖l j‖ * ‖w j‖ :=
      mul_lt_mul'' hj (hwr j) hρ.le hr
    nlinarith

  have hS : ‖∑ i, ((d i).untilt : C) - A‖ ≤ ‖(p : K)‖ := by
    rw [norm_sub_rev, hA, ← norm_natCast_algebra (C := C)]
    exact norm_untilt_sum_sub_le Finset.univ d
  have hT : ‖∑ i, l i • tiltSharp C p (w i) - ∑ i, ((d i).untilt : C)‖ ≤ ‖(p : K)‖ := by
    rw [← Finset.sum_sub_distrib]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [hdu, Algebra.smul_def, ← sub_mul, ← map_sub, norm_mul, norm_algebraMap', norm_sub_rev]
    calc ‖((a i).untilt : K) - l i‖ * ‖tiltSharp C p (w i)‖ ≤ ‖(p : K)‖ * 1 := by
          gcongr
          · exact ha i
          · exact hsw i
      _ = _ := mul_one _
  have hE : ‖∑ i, l i • tiltSharp C p (w i) - A‖ ≤ ‖(p : K)‖ := by
    have e : ∑ i, l i • tiltSharp C p (w i) - A =
        (∑ i, l i • tiltSharp C p (w i) - ∑ i, ((d i).untilt : C)) +
          (∑ i, ((d i).untilt : C) - A) := by abel
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hT hS)
  rw [norm_eq_of_norm_sub_lt (hE.trans_lt (hp.trans_lt hAbig))]
  exact hAbig
end GroundTheory.PAdicHodge
