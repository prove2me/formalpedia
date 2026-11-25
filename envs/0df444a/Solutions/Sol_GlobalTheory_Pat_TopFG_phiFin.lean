-- Prove2me | solution 1 for GlobalTheory.Pat.TopFG.phiFin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:05:30.899983+00:00
-- url     : https://prove2.me/submissions/0ce5c654-3003-42c3-ab01-513d07ee935a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Polynomial IsLocalRing
noncomputable section
open IsLocalRing
open GlobalTheory GlobalTheory.Pat
namespace GlobalTheory.Pat
namespace TopFG
theorem _root_.solution (l : ℕ) [NeZero l] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (h : TopFG G) : PhiFin l G := by
  intro H hH
  obtain ⟨S, hS⟩ := h
  set D := Subgroup.closure (S : Set G) with hD
  have hDd : Dense (D : Set G) := by
    rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, hS]; rfl
  haveI : Group.FG D := (Group.fg_iff_subgroup_fg D).2 ⟨S, rfl⟩
  haveI : Finite (G ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI : (H.subgroupOf D).FiniteIndex := inferInstance
  haveI : Group.FG (H.subgroupOf D) := Subgroup.fg_of_index_ne_zero _
  obtain ⟨T, hT⟩ := Group.fg_def.1 ‹Group.FG (H.subgroupOf D)›
  let ι : H.subgroupOf D →* H :=
    (D.subtype.comp (H.subgroupOf D).subtype).codRestrict H (fun x => x.2)
  refine Set.Finite.of_finite_image (f := fun f => fun t : T => f (ι t)) (Set.toFinite _) ?_
  intro f hf g hg e
  have e1 : f.comp ι = g.comp ι :=
    MonoidHom.eq_of_eqOn_dense hT (fun t ht => congrFun e ⟨t, ht⟩)
  ext x
  have hU : IsOpen (Subtype.val '' ((fun y : H => x⁻¹ * y) ⁻¹' ((f.ker : Set H) ∩ (g.ker : Set H)))) :=
    hH.isOpenMap_subtype_val _ ((IsOpen.inter (show IsOpen (f.ker : Set H) from hf) (show IsOpen (g.ker : Set H) from hg)).preimage (by fun_prop))
  obtain ⟨d, ⟨y, ⟨hy1, hy2⟩, rfl⟩, hd⟩ := hDd.inter_open_nonempty _ hU ⟨x, x, by simp, rfl⟩
  have e2 : f y = g y := DFunLike.congr_fun e1 ⟨⟨y, hd⟩, y.2⟩
  simp only [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hy1 hy2
  rw [hy1, hy2, e2]
end TopFG
end GlobalTheory.Pat
