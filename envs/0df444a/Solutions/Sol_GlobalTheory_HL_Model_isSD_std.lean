-- Prove2me | solution 1 for GlobalTheory.HL.Model.isSD_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:44:20.278871+00:00
-- url     : https://prove2.me/submissions/ed8ab05b-3087-4312-ba3d-11216e757230

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_HermitianLattices
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
namespace GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
private theorem cj_mem_O_of_mem_O' (L : LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at hx ⊢
  exact hx.map (L.cj.toAlgHom.restrictScalars 𝒪[F])
private theorem mem_stdLat_iff_forall_mem_O (L : LocE F E) (n : ℕ) (y : Fin n → E) :
    y ∈ stdLat L n ↔ ∀ i, y i ∈ L.O := by
  unfold stdLat
  constructor
  · intro hy i
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    | zero => simp
    | add x z _ _ hx hz => exact L.O.add_mem hx hz
    | smul a x _ hx => exact L.O.mul_mem a.2 hx
  · intro h
    have hy : y = ∑ i, (⟨y i, h i⟩ : L.O) • (Pi.single i 1 : Fin n → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def]
    rw [hy]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end GlobalTheory.HL.Model
end
end

set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.Model
theorem _root_.solution (L : LocE F E) (n : ℕ) : IsSD L (1 : Matrix (Fin n) (Fin n) E) (stdLat L n) := by
  refine ⟨⟨Submodule.fg_span (Set.finite_range _), ?_⟩, fun y => ?_⟩
  · rw [eq_top_iff]
    intro v _
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun i _ => ?_
    have e : Pi.single i (v i) = v i • (Pi.single i 1 : Fin n → E) := by
      ext j
      by_cases h : j = i <;> simp [h]
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact (mem_stdLat_iff_forall_mem_O L n _).mpr fun j => by by_cases h : j = i <;> simp [h]
  · rw [mem_stdLat_iff_forall_mem_O]
    constructor
    · intro hy i
      have h1 := hy (Pi.single i 1) ((mem_stdLat_iff_forall_mem_O L n _).mpr fun j => by
        by_cases h : j = i <;> simp [h])
      have h2 : hf L 1 (Pi.single i 1) y = L.cj (y i) := by
        simp [hf, Pi.single_apply, Matrix.one_apply]
      rw [h2] at h1
      simpa [L.cj_cj] using cj_mem_O_of_mem_O' L h1
    · intro hy x hx
      rw [mem_stdLat_iff_forall_mem_O] at hx
      unfold hf
      refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_
      refine L.O.mul_mem (L.O.mul_mem (hx i) ?_) (cj_mem_O_of_mem_O' L (hy j))
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
end GlobalTheory.HL.Model
