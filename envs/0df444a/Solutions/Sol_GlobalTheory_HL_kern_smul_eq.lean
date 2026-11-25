-- Prove2me | solution 1 for GlobalTheory.HL.kern_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:00:05.527771+00:00
-- url     : https://prove2.me/submissions/f0859f4b-f9fd-428c-8a47-864f2cefe6c5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralTransportAndChangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameMovesKernelCommonStabilizerSmulEq
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameAct_inTh_iff
import Theorems.Thm_GlobalTheory_FrameAct_mem_smul_iff
import Theorems.Thm_GlobalTheory_FrameAct_spanTo_iff
import Theorems.Thm_GlobalTheory_FrameAct_stabiliser_acts_on_terms
import Theorems.Thm_GlobalTheory_IdxInt_Transport_cint_map_and_change
import Theorems.Thm_P2M_GlobalTheory_FrameAct_spanTo_iff__721488b8eec6
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.KernInv
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
end GlobalTheory.HL.KernInv
namespace GlobalTheory.HL
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma form_apply_apply_of_mem_St {h : S.GLV}
    (hh : h ∈ S.St) (x y : S.V) :
    S.h (h x) (h y) = S.h x y := by
  unfold _root_.GlobalTheory.HL.Frames.St at hh
  have hN := (Subgroup.mem_inf.mp hh).1
  unfold _root_.GlobalTheory.HL.Frames.N _root_.GlobalTheory.HL.Frames.Nof at hN
  have hI := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hN).1).1
  unfold _root_.GlobalTheory.HL.isomG at hI
  unfold _root_.GlobalTheory.HL.Frames.h
  exact hI x y
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma addSubgroup_eq_map_of_apply_mem_iff {M : Type} [AddCommGroup M] (e : M ≃+ M)
    (A B : AddSubgroup M) (hAB : ∀ w, e w ∈ B ↔ w ∈ A) : B = A.map e.toAddMonoidHom := by
  ext w
  constructor
  · intro hw
    exact ⟨e.symm w, (hAB _).mp (by simpa using hw), by simp⟩
  · rintro ⟨w, hw, rfl⟩
    exact (hAB w).mpr hw
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma mem_refB_iff (J : ℕ) (Λ : Submodule L.O S.V) (a b : S.V) :
    (a, b) ∈ S.refB J Λ ↔ a ∈ S.spanTo S.f J ∧ b ∈ S.spanTo S.f' J ∧
      ∃ y ∈ Λ, a + b = (algebraMap F E) S.th • y := by
  unfold _root_.GlobalTheory.HL.Frames.refB
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_prod, AddSubgroup.mem_comap, AddSubgroup.mem_map,
    Submodule.mem_toAddSubgroup, and_assoc]
  exact Iff.rfl.and (Iff.rfl.and (exists_congr fun _ => Iff.rfl.and eq_comm))
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma apply_mem_sup_iff_of_apply_mem_iff (h : S.GLV) (A B : Submodule E S.V)
    (hA : ∀ v, h v ∈ A ↔ v ∈ A) (hB : ∀ v, h v ∈ B ↔ v ∈ B) (v : S.V) :
    h v ∈ A ⊔ B ↔ v ∈ A ⊔ B := by
  simp only [Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, hyz⟩
    refine ⟨h.symm y, (hA _).mp (by simpa using hy), h.symm z, (hB _).mp (by simpa using hz), ?_⟩
    rw [← map_add, hyz, LinearEquiv.symm_apply_apply]
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact ⟨h y, (hA y).mpr hy, h z, (hB z).mpr hz, (map_add h y z).symm⟩
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma apply_mem_perp_Ysp_iff_of_mem_St {h : S.GLV}
    (hh : h ∈ S.St) (J : ℕ) (u : S.V) :
    h u ∈ _root_.GlobalTheory.HL.perp L S.Hm (S.Ysp J) ↔
      u ∈ _root_.GlobalTheory.HL.perp L S.Hm (S.Ysp J) := by
  have hform : ∀ x y, _root_.GlobalTheory.HL.hf L S.Hm (h x) (h y) =
      _root_.GlobalTheory.HL.hf L S.Hm x y := form_apply_apply_of_mem_St S hh
  have hY : ∀ v, h v ∈ S.Ysp J ↔ v ∈ S.Ysp J := by
    unfold _root_.GlobalTheory.HL.Frames.Ysp
    exact apply_mem_sup_iff_of_apply_mem_iff S h _ _
      (_root_.GlobalTheory.FrameAct.spanTo_iff S h hh J)
      (_root_.GlobalTheory.FrameAct.spanTo_iff' S h hh J)
  unfold _root_.GlobalTheory.HL.perp
  show (∀ y ∈ S.Ysp J, _ = 0) ↔ (∀ y ∈ S.Ysp J, _ = 0)
  constructor
  · intro H y hy
    rw [← hform]
    exact H _ ((hY y).mpr hy)
  · intro H y hy
    have hyy : h (h.symm y) = y := h.apply_symm_apply y
    rw [← hyy, hform]
    exact H _ ((hY _).mp (hyy.symm ▸ hy))
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma coe_smul_submodule_eq_iff_of_apply_mem_iff (h : S.GLV) (Λ₁ : Submodule L.O S.V) (P Q : Set S.V)
    (hPQ : ∀ v, h v ∈ Q ↔ v ∈ P) :
    ((h • Λ₁ : Submodule L.O S.V) : Set S.V) = Q ↔ (Λ₁ : Set S.V) = P := by
  simp only [Set.ext_iff, SetLike.mem_coe]
  rw [h.surjective.forall]
  simp only [_root_.GlobalTheory.FrameAct.mem_smul_iff, hPQ]
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma eich_apply_apply_of_mem_St {h : S.GLV}
    (hh : h ∈ S.St) (a b v : S.V) (c : E) :
    _root_.GlobalTheory.HL.eich L S.Hm (h a) (h b) c (h v) = h (_root_.GlobalTheory.HL.eich L S.Hm a b c v) := by
  have hform : ∀ x y, _root_.GlobalTheory.HL.hf L S.Hm (h x) (h y) =
      _root_.GlobalTheory.HL.hf L S.Hm x y := form_apply_apply_of_mem_St S hh
  unfold _root_.GlobalTheory.HL.eich
  rw [hform, hform]
  simp only [map_add, map_sub, map_smul]
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma apply_mem_moved_smul_iff_of_mem_St {h : S.GLV}
    (hh : h ∈ S.St) (Λ : Submodule L.O S.V) (a b v : S.V) (c : E) :
    h v ∈ S.moved (h • Λ) (h a) (h b) c ↔ v ∈ S.moved Λ a b c := by
  unfold _root_.GlobalTheory.HL.Frames.moved
  show _root_.GlobalTheory.HL.eich L S.Hm (h a) (h b) c (h v) ∈ h • Λ ↔
    _root_.GlobalTheory.HL.eich L S.Hm a b c v ∈ Λ
  rw [eich_apply_apply_of_mem_St S hh, _root_.GlobalTheory.FrameAct.mem_smul_iff]
end GlobalTheory.HL
end
end

set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k)
namespace GlobalTheory.HL
namespace _root_.GlobalTheory.HL
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ (β J βJ : ℕ) (Λ₁ : Submodule L.O S.V), ∀ h ∈ S.St, S.kern β J βJ d (h • Λ) (h • Λ₁) = S.kern β J βJ d Λ Λ₁ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT β J βJ Λ₁ h hh
  have hform := form_apply_apply_of_mem_St S hh
  have hmove := (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d Λ hT h hh).2.2.2.2.2.2.2.2.2.2
  have hA : S.refA J (h • Λ) =
      (S.refA J Λ).map (_root_.GlobalTheory.HL.KernInv.mvEquiv S h).toAddMonoidHom := by
    refine addSubgroup_eq_map_of_apply_mem_iff _ _ _ ?_
    rintro ⟨⟨a, b⟩, u, t⟩
    unfold _root_.GlobalTheory.HL.Frames.refA
    simp only [AddSubgroup.mem_prod]
    change (h a, h b) ∈ S.refB J (h • Λ) ∧ h u ∈ S.refU J (h • Λ) ∧ t ∈ S.refT ↔
      (a, b) ∈ S.refB J Λ ∧ u ∈ S.refU J Λ ∧ t ∈ S.refT
    rw [mem_refB_iff, mem_refB_iff, ← map_add,
      _root_.GlobalTheory.FrameAct.spanTo_iff S h hh,
      _root_.GlobalTheory.FrameAct.spanTo_iff' S h hh]
    have hth := _root_.GlobalTheory.FrameAct.inTh_iff S h Λ (a + b)
    unfold _root_.GlobalTheory.HL.Frames.InTh at hth
    rw [hth]
    unfold _root_.GlobalTheory.HL.Frames.refU
    simp only [AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup,
      _root_.GlobalTheory.FrameAct.mem_smul_iff, apply_mem_perp_Ysp_iff_of_mem_St S hh]
  have hP : ∀ w, _root_.GlobalTheory.IdxInt.ind (S.MvTo J d (h • Λ) (h • Λ₁))
      (_root_.GlobalTheory.HL.KernInv.mvEquiv S h w) = _root_.GlobalTheory.IdxInt.ind (S.MvTo J d Λ Λ₁) w := by
    rintro ⟨⟨a, b⟩, u, t⟩
    have hs : S.sOf ((h a, h b), (h u, t)) = S.sOf ((a, b), (u, t)) := by
      unfold _root_.GlobalTheory.HL.Frames.sOf
      simp only [hform]
    have hiff : S.MvTo J d (h • Λ) (h • Λ₁) ((h a, h b), (h u, t)) ↔
        S.MvTo J d Λ Λ₁ ((a, b), (u, t)) := by
      unfold _root_.GlobalTheory.HL.Frames.MvTo _root_.GlobalTheory.HL.Frames.Mv
      change S.IsMove J d (h • Λ) (h a) (h b) (h u) (S.sOf ((h a, h b), (h u, t))) ∧
          ((h • Λ₁ : Submodule L.O S.V) : Set S.V) =
            S.moved (h • Λ) (h a) (h u) (S.sOf ((h a, h b), (h u, t))) ↔
        S.IsMove J d Λ a b u (S.sOf ((a, b), (u, t))) ∧
          (Λ₁ : Set S.V) = S.moved Λ a u (S.sOf ((a, b), (u, t)))
      rw [hs]
      exact and_congr (hmove J a b u _).symm
        (coe_smul_submodule_eq_iff_of_apply_mem_iff S h Λ₁ _ _ fun v => apply_mem_moved_smul_iff_of_mem_St S hh Λ a u v _)
    unfold _root_.GlobalTheory.IdxInt.ind
    exact if_congr hiff rfl rfl
  unfold _root_.GlobalTheory.HL.Frames.kern
  rw [hA, (_root_.GlobalTheory.IdxInt.Transport.cint_map_and_change.1 _ _ _).2]
  simp only [hP]
end _root_.GlobalTheory.HL
end GlobalTheory.HL
