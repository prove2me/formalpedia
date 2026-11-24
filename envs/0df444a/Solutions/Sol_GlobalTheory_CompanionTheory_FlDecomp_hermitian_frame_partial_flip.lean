-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlDecomp.hermitian_frame_partial_flip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:31:28.0239+00:00
-- url     : https://prove2.me/submissions/e2f72e74-ffdb-4741-a82a-b483b6b069a4

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorus
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_h_fe
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_flip_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FlDecomp
open CompanionTheory.Rg.FlB
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
variable {s : L →+* L} {δ : L} {h : V → V → L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}
namespace GlobalTheory.CompanionTheory.FlDecomp
theorem _root_.solution (hs : IsInv s) (hδ : δ ≠ 0) (hh : IsHerm s h) (hF : IsFrame h δ e f W)
    (F : Fin l → Prop) [DecidablePred F] :
    IsFrame h δ (fun i => if F i then f i else e i) (fun i => if F i then (δ / s δ) • e i else f i) W := by
  have hsδ : s δ ≠ 0 := (map_ne_zero s).2 hδ
  set c := δ / s δ with hc
  have hc0 : c ≠ 0 := div_ne_zero hδ hsδ
  have hl1 : ∀ (a : L) x y, h (a • x) y = s a * h x y := fun a x y => by
    rw [hh.2.2.1 y (a • x), hh.2.1, map_mul, ← hh.2.2.1 y x]
  have hr1 : ∀ (a : L) x y, h x (a • y) = a * h x y := hh.2.1
  have hne : ∀ {i j}, F i → ¬ F j → i ≠ j := fun hi hj hij => hj (hij ▸ hi)
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_, fun w hw i => ?_, hF.2.2.2.2.1, fun x => ?_⟩
  · by_cases h1 : F i <;> by_cases h2 : F j <;> simp only [h1, h2, if_true, if_false]
    · exact hF.2.1 i j
    · rw [h_fe hh hF, if_neg (hne h1 h2)]
    · rw [hF.2.2.1, if_neg (fun hij : i = j => h1 (hij ▸ h2))]
    · exact hF.1 i j
  · by_cases h1 : F i <;> by_cases h2 : F j <;> simp only [h1, h2, if_true, if_false]
    · rw [hl1, hr1, hF.1]
      simp
    · rw [hl1, hF.2.2.1, if_neg (hne h1 h2)]
      simp
    · rw [hr1, h_fe hh hF, if_neg (fun hij : i = j => h1 (hij ▸ h2))]
      simp
    · exact hF.2.1 i j
  · by_cases h1 : F i <;> by_cases h2 : F j <;> simp only [h1, h2, if_true, if_false]
    · rw [hr1, h_fe hh hF]
      by_cases hij : i = j
      · simp [hij, hc, hsδ]
      · simp [hij]
    · rw [hF.2.1, if_neg (hne h1 h2)]
    · rw [hr1, hF.1, if_neg (fun hij : i = j => h1 (hij ▸ h2))]
      simp
    · exact hF.2.2.1 i j
  · have := hF.2.2.2.1 w hw i
    by_cases h1 : F i <;> simp only [h1, if_true, if_false]
    · rw [hl1, this.1, this.2]
      simp
    · exact this
  · obtain ⟨a, b, w, hw, rfl⟩ := hF.2.2.2.2.2 x
    refine ⟨fun i => if F i then b i else a i, fun i => if F i then c⁻¹ * a i else b i, w, hw, ?_⟩
    rw [flip_sum]
    congr 2
    · refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h1 : F i
      · simp [h1, hc0]
      · simp [h1]
    · refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h1 : F i <;> simp [h1]
end GlobalTheory.CompanionTheory.FlDecomp
