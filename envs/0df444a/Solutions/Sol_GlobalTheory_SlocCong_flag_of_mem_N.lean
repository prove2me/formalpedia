-- Prove2me | solution 1 for GlobalTheory.SlocCong.flag_of_mem_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:47:46.166869+00:00
-- url     : https://prove2.me/submissions/3215f48a-c159-422d-b34a-5dbe19c94746

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermFamiliesCongrModUnitriangular
import Theorems.Thm_GlobalTheory_SlocCong_stab_of_flag
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
open GlobalTheory GlobalTheory.SlocCong
namespace GlobalTheory.SlocCong
theorem _root_.solution {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V]
    [Module E V] {H : Loc.HermSp M V} {r : ℕ} (Fr : LocNG.FrameD H r) (g : V ≃ₗ[E] V) (hg : g ∈ Fr.N)
    (a : Fin (r + 1)) : g (Fr.f a) - Fr.f a ∈ Submodule.span E (Fr.f '' {c | c < a}) := by
  classical
  have fmem : ∀ c a : Fin (r + 1), c < a → Fr.f c ∈ Submodule.span E (Fr.f '' {c | c < a}) :=
    fun c a h => Submodule.subset_span ⟨c, h, rfl⟩
  have Smono : ∀ a b : Fin (r + 1), a ≤ b →
      Submodule.span E (Fr.f '' {c | c < a}) ≤ Submodule.span E (Fr.f '' {c | c < b}) :=
    fun a b h => Submodule.span_mono (Set.image_mono fun c (hc : c < a) => (show c < b from lt_of_lt_of_le hc h))
  let Q : (V ≃ₗ[E] V) → Prop := fun g => ∀ a, g (Fr.f a) - Fr.f a ∈ Submodule.span E (Fr.f '' {c | c < a})
  suffices hQ : Q g from hQ a
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨-, hflag, hperp⟩ := hg
    intro a
    rcases Fin.eq_castSucc_or_eq_last a with ⟨i, rfl⟩ | rfl
    · have hv : Fr.f i.castSucc ∈ Fr.Fj (i.val + 1) :=
        Submodule.subset_span ⟨i, by simp, rfl⟩
      have := hflag (i.val + 1) (by omega) _ hv
      simp only [Nat.add_sub_cancel] at this
      refine (Submodule.span_le.2 ?_) this
      rintro _ ⟨b, hb, rfl⟩
      exact fmem b.castSucc i.castSucc (Fin.castSucc_lt_castSucc_iff.2 (Fin.lt_def.2 hb))
    · have hz : Fr.f (Fin.last r) ∈ H.perp (H.X Fr.f) := by
        intro x hx
        have h0 : H.h x (Fr.f (Fin.last r)) = 0 := by
          induction hx using Submodule.span_induction with
          | mem x hx =>
            obtain ⟨b, rfl⟩ := hx
            exact Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last b))
          | zero => exact H.h_zero_left _
          | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
          | smul c x _ hx => rw [H.h_smul_left, hx, mul_zero]
        rw [H.h_herm, h0, map_zero]
      have := hperp _ hz
      refine (Submodule.span_le.2 ?_) this
      rintro _ ⟨b, rfl⟩
      exact fmem b.castSucc (Fin.last r) (Fin.castSucc_lt_last b)
  | one => intro a; simp
  | mul g h _ _ hg hh =>
    intro a
    have := Submodule.add_mem _
      (stab_of_flag Fr.f (g : V →ₗ[E] V) hg a _ (hh a)) (hg a)
    convert this using 1
    simp only [LinearEquiv.coe_coe, map_sub, LinearEquiv.mul_apply]
    abel
  | inv g _ hg =>
    intro a
    induction a using WellFoundedLT.induction with
    | _ a ih =>
      have hst : ∀ v ∈ Submodule.span E (Fr.f '' {c | c < a}),
          g⁻¹ v ∈ Submodule.span E (Fr.f '' {c | c < a}) := by
        intro v hv
        have : Submodule.span E (Fr.f '' {c | c < a}) ≤
            (Submodule.span E (Fr.f '' {c | c < a})).comap (g⁻¹ : V ≃ₗ[E] V).toLinearMap := by
          rw [Submodule.span_le]
          rintro _ ⟨c, hc, rfl⟩
          have := Submodule.add_mem _ (Smono c a (le_of_lt hc) (ih c hc)) (fmem c a hc)
          simpa using this
        exact this hv
      have := Submodule.neg_mem _ (hst _ (hg a))
      convert this using 1
      simp [map_sub]
end GlobalTheory.SlocCong
