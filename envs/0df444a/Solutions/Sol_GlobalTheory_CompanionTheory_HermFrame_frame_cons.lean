-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermFrame.frame_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:55:08.978798+00:00
-- url     : https://prove2.me/submissions/67e25ce8-338c-4134-b646-bbbf78965997

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FrameOfAnisotropicPlaneSplitting
import Theorems.Thm_GlobalTheory_CompanionTheory_HermFrame_herm_symm_zero

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermFrame
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}
namespace GlobalTheory.CompanionTheory.HermFrame
theorem _root_.solution (hh : IsHerm s h) {δ : L} {e f : V} {U : Submodule L V}
    (hU : ∀ x, x ∈ U ↔ h e x = 0 ∧ h f x = 0) (hee : h e e = 0) (hff : h f f = 0) (hef : h e f = δ)
    (hdec : ∀ x, ∃ (a b : L), ∃ w ∈ U, x = a • e + b • f + w) {l : ℕ} {e' f' : Fin l → U}
    {W' : Submodule L U} (hfr : IsFrame (fun x y : U => h x y) δ e' f' W') :
    IsFrame h δ (Fin.cons e fun i => (e' i : V) : Fin (l + 1) → V)
      (Fin.cons f fun i => (f' i : V) : Fin (l + 1) → V) (W'.map U.subtype) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hfr
  have heU : ∀ x ∈ U, h e x = 0 := fun x hx => ((hU x).1 hx).1
  have hfU : ∀ x ∈ U, h f x = 0 := fun x hx => ((hU x).1 hx).2
  have heU' : ∀ x ∈ U, h x e = 0 := fun x hx => herm_symm_zero hh (heU x hx)
  have hfU' : ∀ x ∈ U, h x f = 0 := fun x hx => herm_symm_zero hh (hfU x hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simpa using hee
      | succ j => simpa using heU _ (e' j).2
    | succ i =>
      induction j using Fin.cases with
      | zero => simpa using heU' _ (e' i).2
      | succ j => simpa using a1 i j
  · intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simpa using hff
      | succ j => simpa using hfU _ (f' j).2
    | succ i =>
      induction j using Fin.cases with
      | zero => simpa using hfU' _ (f' i).2
      | succ j => simpa using a2 i j
  · intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simpa using hef
      | succ j =>
        simpa [Ne.symm (Fin.succ_ne_zero j)] using heU _ (f' j).2
    | succ i =>
      induction j using Fin.cases with
      | zero => simpa [Fin.succ_ne_zero i] using hfU' _ (e' i).2
      | succ j => simpa using a3 i j
  · intro w hw i
    obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.1 hw
    induction i using Fin.cases with
    | zero => simpa using And.intro (heU _ w'.2) (hfU _ w'.2)
    | succ i => simpa using a4 w' hw' i
  · intro w hw h0
    obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.1 hw
    have : w' = 0 := a5 w' hw' h0
    simp [this]
  · intro x
    obtain ⟨a, b, w, hw, rfl⟩ := hdec x
    obtain ⟨a', b', w', hw', hEq⟩ := a6 ⟨w, hw⟩
    refine ⟨Fin.cons a a', Fin.cons b b', U.subtype w', Submodule.mem_map_of_mem hw', ?_⟩
    have hw2 : w = ∑ i, a' i • (e' i : V) + ∑ i, b' i • (f' i : V) + (w' : V) := by
      have := congrArg Subtype.val hEq
      simpa using this
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Submodule.subtype_apply]
    rw [hw2]
    abel
end GlobalTheory.CompanionTheory.HermFrame
