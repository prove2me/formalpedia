-- Prove2me | solution 1 for GlobalTheory.InnerRead.Lset_img
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:47:54.07613+00:00
-- url     : https://prove2.me/submissions/8d5f9d4d-604e-4769-9752-7673f7368202

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NonGenericDatumLatticeEqPerpQuotientImageTerm
import Theorems.Thm_GlobalTheory_InnerRead_mkW_eq
import Theorems.Thm_GlobalTheory_InnerRead_good_perp
import Theorems.Thm_GlobalTheory_InnerRead_good_inv
import Theorems.Thm_GlobalTheory_InnerRead_X_le_perp
import Theorems.Thm_GlobalTheory_InnerRead_good_of_mem_N
import Theorems.Thm_GlobalTheory_InnerRead_mem_img

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
noncomputable section
open GlobalTheory GlobalTheory.InnerRead
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {H} {r : ℕ} (Fr : FrameD H r)
namespace GlobalTheory.InnerRead
theorem _root_.solution {u : V ≃ₗ[E] V} (hu : u ∈ Fr.N) (Λ : Submodule M.L.O V) :
    H.Lset (img u Λ) Fr.f = H.Lset Λ Fr.f := by
  have hX := X_le_perp Fr
  have g1 := good_of_mem_N Fr hu
  have g2 := good_inv H hX g1
  ext w
  constructor
  · rintro ⟨x, hxΛ, rfl⟩
    obtain ⟨y, hy, hyx⟩ := (mem_img u Λ x).1 hxΛ
    have hyp : y ∈ H.perp (H.X Fr.f) := by
      have := good_perp H hX g2 (x : V) x.2
      rw [← hyx] at this
      change u.symm (u y) ∈ _ at this
      rwa [LinearEquiv.symm_apply_apply] at this
    refine ⟨⟨y, hyp⟩, hy, (mkW_eq H _ _ ?_).symm⟩
    change (x : V) - y ∈ _
    rw [← hyx]
    exact g1.2 y hyp
  · rintro ⟨y, hyΛ, rfl⟩
    exact ⟨⟨u y, good_perp H hX g1 y y.2⟩, (mem_img u Λ _).2 ⟨y, hyΛ, rfl⟩,
      mkW_eq H _ _ (g1.2 y y.2)⟩
end GlobalTheory.InnerRead
