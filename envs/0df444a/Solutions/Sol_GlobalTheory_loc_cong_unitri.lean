-- Prove2me | solution 1 for GlobalTheory.loc_cong_unitri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:59:54.663092+00:00
-- url     : https://prove2.me/submissions/dfdec0dd-3d54-44d9-9a90-1a0c5edf77fd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermFamiliesCongrModUnitriangular
import Theorems.Thm_GlobalTheory_SlocCong_exists_unitri
import Theorems.Thm_GlobalTheory_SlocCong_flag_of_mem_N
import Theorems.Thm_GlobalTheory_SlocCong_coords_of_flag
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open Formalism.MainNotions.S
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) {r : ℕ} (P : LocNG.FPair H r) (d : LocNG.Datum P) (τ : Loc.Term V M r) (sg : Loc.SplitG M.L), M.split = some sg → LocNG.IsTermOver P d τ → ∀ (y x : Fin (r + 1) → V) (B B' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → B a b = 0) → (∀ a b, b < a → B' a b = 0) → (∀ a, B' a a = B a a) → (∀ a, B a a ∈ M.L.O ∧ ∃ t ∈ M.L.O, t * B a a = 1) → (∀ b, y b = ∑ a, B a b • P.A.f a) → (∀ b, x b = ∑ a, B' a b • P.B.f a) → (∀ a, y a ∈ τ.abelian₂) → (∀ b, x b ∈ τ.abelian₂) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ a b, ξ a b ∈ M.L.O) ∧ (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, x b - ∑ a, ξ a b • y a ∈ H.smulLat (algebraMap F E (sg.q : F)) τ.abelian₂ := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r P d τ sg hsg hτ y x B B' hB hB' hd hu hy hx hyL hxL
  obtain ⟨-, -, ⟨n, hn, hf, hL⟩, ⟨n', hn', hf', hL'⟩, hadm⟩ := hτ
  have hyL' : ∀ b, n⁻¹ (y b) ∈ P.A.LamStd d.L := by
    intro b
    have := hyL b
    rw [hL] at this
    obtain ⟨u, hu, hu'⟩ := Submodule.mem_map.1 this
    have : n⁻¹ (y b) = u := by
      rw [← hu']; simp
    rw [this]; exact hu
  have hxL' : ∀ b, n'⁻¹ (x b) ∈ P.B.LamStd d.L' := by
    intro b
    have := hxL b
    rw [hL'] at this
    obtain ⟨u, hu, hu'⟩ := Submodule.mem_map.1 this
    have : n'⁻¹ (x b) = u := by
      rw [← hu']; simp
    rw [this]; exact hu
  obtain ⟨W, hWt, hWd, hWO, hWy⟩ := SlocCong.coords_of_flag P.A d.L n⁻¹
    (SlocCong.flag_of_mem_N P.A n⁻¹ (inv_mem hn)) y B hB (fun a => (hu a).1) hy hyL'
  obtain ⟨W', hWt', hWd', hWO', hWx⟩ := SlocCong.coords_of_flag P.B d.L' n'⁻¹
    (SlocCong.flag_of_mem_N P.B n'⁻¹ (inv_mem hn')) x B' hB' (fun a => hd a ▸ (hu a).1) hx hxL'
  have hy2 : ∀ a, y a = ∑ c, W c a • τ.f c := by
    intro a
    have := congrArg n (hWy a)
    simp only [map_sum, map_smul] at this
    rw [hf]
    simpa using this
  have hx2 : ∀ b, x b = ∑ c, W' c b • τ.f' c := by
    intro b
    have := congrArg n' (hWx b)
    simp only [map_sum, map_smul] at this
    rw [hf']
    simpa using this
  let WO : Matrix (Fin (r + 1)) (Fin (r + 1)) M.L.O := Matrix.of fun a b => ⟨W a b, hWO a b⟩
  let WO' : Matrix (Fin (r + 1)) (Fin (r + 1)) M.L.O := Matrix.of fun a b => ⟨W' a b, hWO' a b⟩
  have hunit : ∀ a, IsUnit (WO a a) := by
    intro a
    obtain ⟨t, ht, ht1⟩ := (hu a).2
    refine isUnit_iff_exists_inv.2 ⟨⟨t, ht⟩, ?_⟩
    apply Subtype.ext
    simp [WO, hWd, mul_comm, ht1]
  obtain ⟨ξO, hξt, hξd, hξ⟩ := SlocCong.exists_unitri WO WO'
    (fun a b h => Subtype.ext (by simp [WO, hWt a b h]))
    (fun a b h => Subtype.ext (by simp [WO', hWt' a b h]))
    (fun a => Subtype.ext (by simp [WO, WO', hWd, hWd', hd]))
    hunit
  have hWξ : ∀ c b, W' c b = ∑ a, W c a * (ξO a b : E) := by
    intro c b
    have := congrArg (fun m => ((m c b : M.L.O) : E)) hξ
    simp [Matrix.mul_apply, WO, WO'] at this
    exact this.symm
  refine ⟨fun a b => (ξO a b : E), fun a b => (ξO a b).2, fun a b h => by simp [hξt a b h],
    fun a => by simp [hξd a], fun b => ?_⟩
  have hadm' := (hadm sg hsg).1
  have key : x b - ∑ a, (ξO a b : E) • y a = ∑ c, W' c b • (τ.f' c - τ.f c) := by
    simp only [hy2, Finset.smul_sum, smul_smul, smul_sub, Finset.sum_sub_distrib, hx2 b]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hWξ c b, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm]
  rw [key]
  refine Submodule.sum_mem _ fun c _ => ?_
  have := Submodule.smul_mem _ (⟨W' c b, hWO' c b⟩ : M.L.O) (hadm' c)
  exact this
end GlobalTheory
