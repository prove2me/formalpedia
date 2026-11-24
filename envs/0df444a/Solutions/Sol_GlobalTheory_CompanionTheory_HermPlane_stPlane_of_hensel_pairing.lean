-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermPlane.stPlane_of_hensel_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:13:14.500601+00:00
-- url     : https://prove2.me/submissions/fd2af340-dfc6-4977-9f06-7116dd43ee81

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PlaneOfHenselAndPairing
import Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_exists_uniformiser
import Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_lat_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_lat_commens
import Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_herm_smul_left
import Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_exists_pair
import Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_plane_of_pair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermPlane
namespace GlobalTheory.CompanionTheory.HermPlane
theorem _root_.solution : StHensel → StPairing → StPlane := by
  intro hH hP L _ _ _ _ s hs δ hδ V _ _ _ h hh hiso Λ M hΛ hM
  obtain ⟨p, hp0, hp1, hpm⟩ := exists_uniformiser (L := L)
  have key : ∀ Λ M : AddSubgroup V, IsMax h Λ → IsMax h M → ∀ r : ℕ, (∀ x ∈ M, p ^ r • x ∈ Λ) →
      (∀ k < r, ∃ z ∈ M, p ^ k • z ∉ Λ) → (∀ y ∈ Λ, p ^ r • y ∈ M) →
      ∃ (e f : V) (u : L), u ≠ 0 ∧ h e e = 0 ∧ h f f = 0 ∧ h e f = δ ∧
        e ∈ Λ ∧ f ∈ Λ ∧ u • e ∈ M ∧ (s u)⁻¹ • f ∈ M := by
    intro Λ M hΛ hM r hr hmin hrM
    obtain ⟨e, y, heΛ, hyΛ, he, hey, heM⟩ :=
      exists_pair hH hP hs hδ hh hiso hΛ hM hp0 hp1 hpm hr hmin hrM
    exact plane_of_pair hs hδ hh hΛ hM hp0 hp1 hrM heΛ hyΛ he hey heM
  classical
  have c1 := lat_commens hΛ.1 hM.1 hp0 hp1
  have c2 := lat_commens hM.1 hΛ.1 hp0 hp1
  have hmin1 : ∀ k < Nat.find c1, ∃ z ∈ M, p ^ k • z ∉ Λ := fun k hk => by
    have := Nat.find_min c1 hk
    push_neg at this
    exact this
  have hmin2 : ∀ k < Nat.find c2, ∃ z ∈ Λ, p ^ k • z ∉ M := fun k hk => by
    have := Nat.find_min c2 hk
    push_neg at this
    exact this
  have up : ∀ (A : AddSubgroup V), IsLat L A → ∀ (B : AddSubgroup V) {a b : ℕ}, a ≤ b →
      (∀ y ∈ B, p ^ a • y ∈ A) → ∀ y ∈ B, p ^ b • y ∈ A := by
    intro A hA B a b hab hy y hyB
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add, mul_comm, mul_smul]
    refine lat_smul hA ?_ (hy y hyB)
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hp1.le
  rcases le_total (Nat.find c2) (Nat.find c1) with hle | hle
  · exact key Λ M hΛ hM _ (Nat.find_spec c1) hmin1 (up M hM.1 Λ hle (Nat.find_spec c2))
  · obtain ⟨e, f, u, hu, he, hf, hef, heM, hfM, heΛ, hfΛ⟩ :=
      key M Λ hM hΛ _ (Nat.find_spec c2) hmin2 (up Λ hΛ.1 M hle (Nat.find_spec c1))
    have hsu : s u ≠ 0 := (map_ne_zero s).2 hu
    refine ⟨u • e, (s u)⁻¹ • f, u⁻¹, inv_ne_zero hu, ?_, ?_, ?_, heΛ, hfΛ, ?_, ?_⟩
    · rw [herm_smul_left hh, hh.2.1, he]; simp
    · rw [herm_smul_left hh, hh.2.1, hf]; simp
    · rw [herm_smul_left hh, hh.2.1, hef, ← mul_assoc, mul_inv_cancel₀ hsu, one_mul]
    · rwa [smul_smul, inv_mul_cancel₀ hu, one_smul]
    · rwa [map_inv₀, inv_inv, smul_smul, mul_inv_cancel₀ hsu, one_smul]
end GlobalTheory.CompanionTheory.HermPlane
