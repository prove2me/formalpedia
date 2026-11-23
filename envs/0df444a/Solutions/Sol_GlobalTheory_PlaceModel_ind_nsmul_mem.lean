-- Prove2me | solution 1 for GlobalTheory.PlaceModel.ind_nsmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:34.079927+00:00
-- url     : https://prove2.me/submissions/7169cd31-ce1c-41a6-afb5-e45822a3af1c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Theorems.Thm_GlobalTheory_PlaceModel_IsBichar_nsmul
import Theorems.Thm_GlobalTheory_PlaceModel_wave_zero
import Theorems.Thm_GlobalTheory_PlaceModel_modul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PlaceModel
variable {G : Type} [AddCommGroup G]
variable {χ : G → G → ℂ} {X Y L L' : AddSubgroup G}
namespace GlobalTheory.PlaceModel
theorem _root_.solution (h : IsBichar χ) (hL : L ≤ X) (hL' : L' ≤ Y) (hLL' : ∀ u ∈ L, ∀ y ∈ L', χ u y = 1)
    (hX : ∀ x ∈ X, (∀ y ∈ L', χ x y = 1) → x ∈ L) {k : ℕ}
    (dX : ∀ x ∈ X, ∃ x' ∈ X, k • x' = x) (dY : ∀ y ∈ Y, ∃ y' ∈ Y, k • y' = y)
    (R : Set G) (hR : R.Finite) (hfin : ∀ t ∈ L, ∃ r ∈ R, ∃ u ∈ L, t = r + k • u) :
    ind (L.map (nsmulAddMonoidHom k)) ∈ waveSpan χ X Y L := by
  classical
  set K := L.map (nsmulAddMonoidHom k) with hK
  have memK : ∀ t, t ∈ K ↔ ∃ u ∈ L, k • u = t := by
    intro t
    simp [hK, AddSubgroup.mem_map]

  have hsep : ∀ t ∈ L, t ∉ K → ∃ y ∈ Y, k • y ∈ L' ∧ χ t y ≠ 1 := by
    intro t ht htK
    by_contra hcon
    push Not at hcon
    obtain ⟨x', hx', hkx⟩ := dX t (hL ht)
    apply htK
    rw [memK]
    refine ⟨x', hX x' hx' fun y' hy' => ?_, hkx⟩
    obtain ⟨y, hy, hky⟩ := dY y' (hL' hy')
    rw [← hky, ← h.nsmul, hkx]
    exact hcon y hy (by rw [hky]; exact hy')
  have hRf : (R ∩ {r | r ∈ L ∧ r ∉ K}).Finite := hR.subset Set.inter_subset_left
  let F := hRf.toFinset
  have hmemF : ∀ r, r ∈ F ↔ r ∈ R ∧ r ∈ L ∧ r ∉ K := by
    intro r
    simp [F]
  choose! yr hyrY hyrL' hyr using fun r (hr : r ∈ F) =>
    hsep r ((hmemF r).mp hr).2.1 ((hmemF r).mp hr).2.2

  have hstep : ∀ Φ ∈ waveSpan χ X Y L, ∀ y ∈ Y, ∀ α β : ℂ,
      (fun t => Φ t * (α * χ t y + β)) ∈ waveSpan χ X Y L := by
    intro Φ hΦ y hy α β
    have e : (fun t => Φ t * (α * χ t y + β)) = α • (fun t => χ t y * Φ t) + β • Φ := by
      funext t
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact add_mem (Submodule.smul_mem _ _ (modul_mem h hΦ hy)) (Submodule.smul_mem _ _ hΦ)
  have hind0 : ind L ∈ waveSpan χ X Y L := by
    rw [← wave_zero (χ := χ) (L := L) h]
    exact Submodule.subset_span ⟨0, X.zero_mem, 0, Y.zero_mem, rfl⟩
  have hprod : ∀ S : Finset G, S ⊆ F → (fun t => ind L t *
      ∏ r ∈ S, (χ t (yr r) - χ r (yr r)) / (1 - χ r (yr r))) ∈ waveSpan χ X Y L := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro _
      simpa using hind0
    · intro r S hrS ih hsub
      have hrF := hsub (Finset.mem_insert_self r S)
      have h1 := hstep _ (ih fun z hz => hsub (Finset.mem_insert_of_mem hz)) (yr r) (hyrY r hrF)
        (1 - χ r (yr r))⁻¹ (-(χ r (yr r)) * (1 - χ r (yr r))⁻¹)
      convert h1 using 1
      funext t
      rw [Finset.prod_insert hrS]
      ring
  convert hprod F (subset_refl _) using 1
  funext t
  by_cases htL : t ∈ L
  · obtain ⟨r0, hr0, u, hu, rfl⟩ := hfin t htL
    have hshift : ∀ r ∈ F, χ (r0 + k • u) (yr r) = χ r0 (yr r) := fun r hr => by
      rw [h.left, h.nsmul, hLL' u hu _ (hyrL' r hr), mul_one]
    rw [show ind L (r0 + k • u) = 1 by simp [ind, htL], one_mul]
    by_cases hK0 : r0 + k • u ∈ K
    · rw [show ind K (r0 + k • u) = 1 by simp [ind, hK0]]
      symm
      refine Finset.prod_eq_one fun r hr => ?_
      obtain ⟨w, hw, hkw⟩ := (memK _).mp hK0
      rw [← hkw, h.nsmul, hLL' w hw _ (hyrL' r hr), div_self (sub_ne_zero.mpr (hyr r hr).symm)]
    · rw [show ind K (r0 + k • u) = 0 by simp [ind, hK0]]
      symm
      have hr0L : r0 ∈ L := by
        have h2 := L.sub_mem htL (L.nsmul_mem hu k)
        simpa using h2
      have hr0K : r0 ∉ K := fun hm => hK0 (K.add_mem hm ((memK _).mpr ⟨u, hu, rfl⟩))
      have hr0F : r0 ∈ F := (hmemF r0).mpr ⟨hr0, hr0L, hr0K⟩
      refine Finset.prod_eq_zero hr0F ?_
      rw [hshift r0 hr0F, sub_self, zero_div]
  · have htK : t ∉ K := fun hm => htL (by
      obtain ⟨w, hw, hkw⟩ := (memK _).mp hm
      rw [← hkw]
      exact L.nsmul_mem hw k)
    simp [ind, htL, htK]
end GlobalTheory.PlaceModel
