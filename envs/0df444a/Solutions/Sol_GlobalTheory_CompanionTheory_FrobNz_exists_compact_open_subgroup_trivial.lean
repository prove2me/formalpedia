-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrobNz.exists_compact_open_subgroup_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:33:21.17723+00:00
-- url     : https://prove2.me/submissions/aebea564-fd5b-4012-b708-98c2be77623f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSchwartzBruhatCharacterIntegralOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob Topology
namespace GlobalTheory.CompanionTheory.FrobNz
private theorem three_halves_norm_sub_one_le_norm_sq_sub_one (u : ℂ) (hu : ‖u - 1‖ < 1/2) :
    3/2 * ‖u - 1‖ ≤ ‖u ^ 2 - 1‖ := by
  have h1 : u ^ 2 - 1 = (u - 1) * (u + 1) := by ring
  have h4 : ‖(2:ℂ)‖ ≤ ‖u + 1‖ + ‖u - 1‖ := by
    calc ‖(2:ℂ)‖ = ‖(u + 1) - (u - 1)‖ := by congr 1; ring
      _ ≤ ‖u + 1‖ + ‖u - 1‖ := norm_sub_le _ _
  have h5 : ‖(2:ℂ)‖ = 2 := by simp
  have h2 : (3:ℝ)/2 ≤ ‖u + 1‖ := by linarith
  rw [h1, norm_mul]
  nlinarith [norm_nonneg (u - 1), mul_le_mul_of_nonneg_left h2 (norm_nonneg (u - 1))]
private theorem eq_one_of_forall_norm_pow_two_pow_sub_one_lt' (w : ℂ) (hw : ∀ n : ℕ, ‖w ^ (2 ^ n) - 1‖ < 1/2) :
    w = 1 := by
  have key : ∀ n : ℕ, (3/2 : ℝ) ^ n * ‖w - 1‖ ≤ ‖w ^ (2 ^ n) - 1‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : w ^ (2 ^ (n + 1)) = (w ^ (2 ^ n)) ^ 2 := by rw [pow_succ, pow_mul]
      rw [e]
      have h3 := three_halves_norm_sub_one_le_norm_sq_sub_one (w ^ (2 ^ n)) (hw n)
      calc (3/2 : ℝ) ^ (n + 1) * ‖w - 1‖ = 3/2 * ((3/2) ^ n * ‖w - 1‖) := by ring
        _ ≤ 3/2 * ‖w ^ (2 ^ n) - 1‖ := by linarith
        _ ≤ ‖(w ^ (2 ^ n)) ^ 2 - 1‖ := h3
  by_contra hne
  have hd : 0 < ‖w - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1/2 / ‖w - 1‖) (by norm_num : (1:ℝ) < 3/2)
  have h1 := key n
  have h2 := hw n
  rw [div_lt_iff₀ hd] at hn
  linarith
end GlobalTheory.CompanionTheory.FrobNz
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrobNz
namespace GlobalTheory.CompanionTheory.FrobNz
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (χ : G →* ℂˣ) (hχ : Continuous (fun g => (χ g : ℂ))) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ ∀ k ∈ K, χ k = 1 := by
  let V : Set G := {g | ‖(χ g : ℂ) - 1‖ < 1/2}
  have hVo : IsOpen V := isOpen_lt ((hχ.sub continuous_const).norm) continuous_const
  have h1V : (1 : G) ∈ V := by
    show ‖((χ 1 : ℂˣ) : ℂ) - 1‖ < 1/2
    simp
  obtain ⟨N, hNc, hN1⟩ := exists_compact_mem_nhds (1 : G)
  have hW : interior N ∩ V ∈ 𝓝 (1 : G) :=
    Filter.inter_mem (interior_mem_nhds.mpr hN1) (hVo.mem_nhds h1V)
  obtain ⟨s, hs, h1s, hsW⟩ := (loc_compact_Haus_tot_disc_of_zero_dim (H := G)).mem_nhds_iff.mp hW
  have hsclo : IsClopen s := hs
  have hsc : IsCompact s :=
    hNc.of_isClosed_subset hsclo.isClosed
      (hsW.trans (Set.inter_subset_left.trans interior_subset))
  obtain ⟨W, hW1, hWs⟩ := compact_open_separated_mul_right hsc hsclo.isOpen subset_rfl
  let H : Subgroup G :=
    { carrier := {g | ∀ x ∈ s, x * g ∈ s ∧ x * g⁻¹ ∈ s}
      mul_mem' := by
        intro a b ha hb
        change ∀ x ∈ s, x * a ∈ s ∧ x * a⁻¹ ∈ s at ha
        change ∀ x ∈ s, x * b ∈ s ∧ x * b⁻¹ ∈ s at hb
        change ∀ x ∈ s, x * (a * b) ∈ s ∧ x * (a * b)⁻¹ ∈ s
        intro x hx
        refine ⟨?_, ?_⟩
        · rw [← mul_assoc]; exact (hb _ (ha x hx).1).1
        · rw [mul_inv_rev, ← mul_assoc]; exact (ha _ (hb x hx).2).2
      one_mem' := by
        change ∀ x ∈ s, x * 1 ∈ s ∧ x * 1⁻¹ ∈ s
        intro x hx
        simp [hx]
      inv_mem' := by
        intro a ha
        change ∀ x ∈ s, x * a ∈ s ∧ x * a⁻¹ ∈ s at ha
        change ∀ x ∈ s, x * a⁻¹ ∈ s ∧ x * a⁻¹⁻¹ ∈ s
        intro x hx
        rw [inv_inv]
        exact ⟨(ha x hx).2, (ha x hx).1⟩ }
  have hHn : (H : Set G) ∈ 𝓝 (1 : G) := by
    have hWW : W ∩ W⁻¹ ∈ 𝓝 (1 : G) := Filter.inter_mem hW1 (inv_mem_nhds_one G hW1)
    refine Filter.mem_of_superset hWW ?_
    rintro g ⟨hg, hg'⟩
    show ∀ x ∈ s, x * g ∈ s ∧ x * g⁻¹ ∈ s
    intro x hx
    exact ⟨hWs (Set.mul_mem_mul hx hg), hWs (Set.mul_mem_mul hx (Set.mem_inv.mp hg'))⟩
  have hHo : IsOpen (H : Set G) := Subgroup.isOpen_of_mem_nhds H hHn
  have hHs : (H : Set G) ⊆ s := by
    intro g hg
    have hg' : ∀ x ∈ s, x * g ∈ s ∧ x * g⁻¹ ∈ s := hg
    simpa using (hg' 1 h1s).1
  have hHc : IsCompact (H : Set G) :=
    hsc.of_isClosed_subset (Subgroup.isClosed_of_isOpen H hHo) hHs
  refine ⟨⟨H, hHo⟩, hHc, ?_⟩
  intro k hk
  have hkH : k ∈ H := hk
  apply Units.ext
  rw [Units.val_one]
  apply eq_one_of_forall_norm_pow_two_pow_sub_one_lt'
  intro n
  have hmem : k ^ (2 ^ n) ∈ H := H.pow_mem hkH _
  have hV : k ^ (2 ^ n) ∈ V := (hsW (hHs hmem)).2
  have hV' : ‖((χ (k ^ (2 ^ n)) : ℂˣ) : ℂ) - 1‖ < 1/2 := hV
  simpa [map_pow, Units.val_pow_eq_pow_val] using hV'
end GlobalTheory.CompanionTheory.FrobNz
