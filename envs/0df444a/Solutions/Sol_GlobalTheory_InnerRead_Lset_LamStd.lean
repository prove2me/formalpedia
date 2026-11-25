-- Prove2me | solution 1 for GlobalTheory.InnerRead.Lset_LamStd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:29:16.923728+00:00
-- url     : https://prove2.me/submissions/e22fb13b-2dee-4afb-a1a6-55f72603c9d9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NonGenericDatumLatticeEqPerpQuotientImageTerm
import Theorems.Thm_GlobalTheory_InnerRead_mkW_eq
import Theorems.Thm_GlobalTheory_InnerRead_prF_e
import Theorems.Thm_GlobalTheory_InnerRead_prF_es
import Theorems.Thm_GlobalTheory_InnerRead_prF_perp
import Theorems.Thm_GlobalTheory_InnerRead_prF_add
import Theorems.Thm_GlobalTheory_InnerRead_prF_smul
import Theorems.Thm_GlobalTheory_InnerRead_prF_of
import Theorems.Thm_GlobalTheory_InnerRead_sub_prF_mem
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
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
noncomputable section
open GlobalTheory GlobalTheory.InnerRead
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {H} {r : ℕ} (Fr : FrameD H r)
namespace GlobalTheory.InnerRead
theorem _root_.solution (L : Submodule M.L.O (H.Wb Fr.f)) :
    H.Lset (Fr.LamStd L) Fr.f = (L : Set (H.Wb Fr.f)) := by
  ext w
  constructor
  · rintro ⟨x, hxΛ, rfl⟩
    have hQ : ∀ v ∈ Fr.LamStd L, H.mkW Fr.f ⟨Fr.prF v, prF_perp Fr v⟩ ∈ L := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨-, -, w, hw, hwL⟩ := hv
        have e : (⟨Fr.prF v, prF_perp Fr v⟩ : ↥(H.perp (H.X Fr.f))) = w := Subtype.ext hw.symm
        rw [e]; exact hwL
      | zero =>
        have e : (⟨Fr.prF 0, prF_perp Fr 0⟩ : ↥(H.perp (H.X Fr.f))) = 0 :=
          Subtype.ext (by simpa using prF_smul Fr 0 0)
        rw [e, map_zero]; exact L.zero_mem
      | add x y _ _ hx hy =>
        have e : (⟨Fr.prF (x + y), prF_perp Fr _⟩ : ↥(H.perp (H.X Fr.f))) =
            ⟨Fr.prF x, prF_perp Fr x⟩ + ⟨Fr.prF y, prF_perp Fr y⟩ := Subtype.ext (prF_add Fr x y)
        rw [e, map_add]; exact L.add_mem hx hy
      | smul c x _ hx =>
        have e : (⟨Fr.prF (c • x), prF_perp Fr _⟩ : ↥(H.perp (H.X Fr.f))) =
            (c : E) • ⟨Fr.prF x, prF_perp Fr x⟩ := Subtype.ext (prF_smul Fr (c : E) x)
        rw [e, map_smul]
        exact L.smul_mem c hx
    have := hQ x hxΛ
    rwa [mkW_eq H ⟨Fr.prF x, prF_perp Fr x⟩ x (by
      have := (H.X Fr.f).neg_mem (sub_prF_mem Fr x x.2); simpa using this)] at this
  · intro hw
    obtain ⟨x0, rfl⟩ := Submodule.mkQ_surjective _ w
    refine ⟨⟨Fr.prF x0, prF_perp Fr x0⟩, ?_, ?_⟩
    · have hp : Fr.prF (Fr.prF x0) = Fr.prF x0 := prF_of Fr _ (prF_es Fr x0) (prF_e Fr x0)
      refine Submodule.subset_span ⟨fun a => ?_, fun a => ?_, ⟨Fr.prF x0, prF_perp Fr x0⟩, hp.symm, ?_⟩
      · change H.h (Fr.prF x0) (Fr.es a) ∈ _; rw [prF_es]; exact zero_mem _
      · change H.h (Fr.prF x0) (Fr.e a) ∈ _; rw [prF_e]; exact zero_mem _
      · rw [mkW_eq H ⟨Fr.prF x0, prF_perp Fr x0⟩ x0 (by
          have := (H.X Fr.f).neg_mem (sub_prF_mem Fr x0 x0.2); simpa using this)]
        exact hw
    · have := (H.X Fr.f).neg_mem (sub_prF_mem Fr x0 x0.2)
      show H.mkW Fr.f _ = H.mkW Fr.f x0
      exact mkW_eq H _ _ (by simpa using this)
end GlobalTheory.InnerRead
