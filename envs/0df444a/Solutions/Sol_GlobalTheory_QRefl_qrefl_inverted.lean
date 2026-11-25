-- Prove2me | solution 1 for GlobalTheory.QRefl.qrefl_inverted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:44:26.902104+00:00
-- url     : https://prove2.me/submissions/8b785b27-ddfd-4947-ac84-1b871d8ed22d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_QuasiReflectionStabilizesLattice
import Theorems.Thm_GlobalTheory_QRefl_hf_smul_left
import Theorems.Thm_GlobalTheory_QRefl_hf_smul_right
import Theorems.Thm_GlobalTheory_QRefl_hf_zero_right
import Theorems.Thm_GlobalTheory_QRefl_hf_sum_left
import Theorems.Thm_GlobalTheory_QRefl_hf_sum_right
import Theorems.Thm_GlobalTheory_QRefl_cj_hf
import Theorems.Thm_GlobalTheory_QRefl_cj_mem_O
import Theorems.Thm_GlobalTheory_QRefl_of_involution
import Theorems.Thm_GlobalTheory_QRefl_exists_involution
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HermOrthBasis_cj_hf
import Theorems.Thm_GlobalTheory_HermOrthBasis_hf_smul_left
import Theorems.Thm_GlobalTheory_HermOrthBasis_hf_smul_right
import Theorems.Thm_GlobalTheory_HermOrthBasis_hf_sum_left
import Theorems.Thm_GlobalTheory_HermOrthBasis_orth_basis_perp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.QRefl
namespace GlobalTheory.QRefl
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → ∀ a ∈ perp L Hm (Submodule.span E (Set.range x)), ∀ g, IsQRefl L Hm a g → ∃ Λ : Submodule L.O (Fin n → E), IsLat L Λ ∧ ∃ α : ((Fin n → E) ≃ₗ[E] (Fin n → E)) ≃* ((Fin n → E) ≃ₗ[E] (Fin n → E)), (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ).map α.toMonoidHom = fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ ∧ α g = g⁻¹ := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH m x hx a ha g hg
  let Γ : Matrix (Fin m) (Fin m) E := (gramT L Hm x).transpose
  have hΓ : IsHermND L Γ := by
    refine ⟨?_, by rwa [Matrix.det_transpose]⟩
    funext i j
    exact cj_hf L Hm hH.1 _ _
  let φ : (Fin m → E) →ₗ[E] (Fin n → E) := Fintype.linearCombination E x
  have hφ : ∀ s t, hf L Hm (φ s) (φ t) = hf L Γ s t := fun s t => by
    simp only [φ, Fintype.linearCombination_apply, hf_sum_left, hf_sum_right, hf_smul_left,
      hf_smul_right, Finset.mul_sum]
    conv_rhs => unfold hf
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Γ, gramT, Matrix.transpose_apply, Matrix.of_apply]
    ring
  obtain ⟨-, -, w, hw1, hw2, hw3⟩ := GlobalTheory.HermOrthBasis.orth_basis_perp L Γ hΓ 0 Fin.elim0 (by simp)
  have hw : Submodule.span E (Set.range w) = ⊤ := by
    rw [hw1, eq_top_iff]
    intro v _ y hy
    rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at hy
    rw [hy, hf_zero_right]
  let u : Fin (m - 0) → Fin n → E := fun i => φ (w i)
  have hu : Submodule.span E (Set.range u) = Submodule.span E (Set.range x) := by
    rw [show u = φ ∘ w from rfl, Set.range_comp, ← Submodule.map_span, hw, Submodule.map_top,
      Fintype.range_linearCombination]
  have hau : ∀ i, hf L Hm a (u i) = 0 := fun i =>
    ha _ (hu ▸ Submodule.subset_span ⟨i, rfl⟩)
  let z : Fin (m - 0 + 1) → Fin n → E := Fin.cons a u
  have hz1 : ∀ i, IsUnit (hf L Hm (z i) (z i)) := fun i => by
    refine Fin.cases hg.1 (fun k => ?_) i
    show IsUnit (hf L Hm (φ _) (φ _))
    rw [hφ]; exact hw2 k
  have hz2 : ∀ i j, i ≠ j → hf L Hm (z i) (z j) = 0 := fun i j => by
    refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) j <;> intro hij
    · exact absurd rfl hij
    · exact hau l
    · show hf L Hm (u k) a = 0
      rw [← cj_hf L Hm hH.1, hau, map_zero]
    · show hf L Hm (φ _) (φ _) = 0
      rw [hφ]; exact hw3 k l fun e => hij (by rw [e])
  have hz : IsUnit (gramT L Hm z).det := by
    have : gramT L Hm z = Matrix.diagonal fun i => hf L Hm (z i) (z i) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [gramT]
      · rw [Matrix.diagonal_apply_ne _ hij]; exact hz2 j i (Ne.symm hij)
    rw [this, Matrix.det_diagonal]
    exact IsUnit.prod_univ_iff.2 hz1
  obtain ⟨-, hcompl, r, hr1, hr2, hr3⟩ := GlobalTheory.HermOrthBasis.orth_basis_perp L Hm hH _ z hz
  have hrz : ∀ i j, hf L Hm (r i) (z j) = 0 := fun i j => by
    have : r i ∈ perp L Hm (Submodule.span E (Set.range z)) :=
      hr1 ▸ Submodule.subset_span ⟨i, rfl⟩
    exact this _ (Submodule.subset_span ⟨j, rfl⟩)
  have hb : Submodule.span E (Set.range (Sum.elim z r)) = ⊤ := by
    rw [Set.Sum.elim_range, Submodule.span_union, hr1]
    exact hcompl.sup_eq_top
  obtain ⟨c, hs, hc, hf', hbi⟩ := exists_involution L Hm hH.1 (Sum.elim z r) hb
    (by rintro (i | i); exacts [hz1 i, hr2 i])
    (by
      rintro (i | i) (j | j) hij
      · exact hz2 i j fun e => hij (by rw [e])
      · show hf L Hm (z i) (r j) = 0
        rw [← cj_hf L Hm hH.1, hrz, map_zero]
      · exact hrz i j
      · exact hr3 i j fun e => hij (by rw [e]))
  refine ⟨Submodule.span L.O (Set.range (Sum.elim z r)),
    ⟨Submodule.fg_span (Set.finite_range _), ?_⟩, ?_⟩
  · rw [eq_top_iff, ← hb]
    exact Submodule.span_mono Submodule.subset_span
  refine of_involution L Hm hH.1 c hs hc hf' _ ?_ _ ?_ a (hbi (Sum.inl 0)) g hg
  · rw [← hu]
    intro v hv
    induction hv using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨i, rfl⟩ := h
      have : c (u i) = u i := hbi (Sum.inl i.succ)
      rw [this]; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add x y _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | smul t x _ h => rw [hs]; exact Submodule.smul_mem _ _ h
  · intro v hv
    induction hv using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨i, rfl⟩ := h
      rw [hbi]; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add x y _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | smul t x _ h =>
      have : c (t • x) = (⟨L.cj t, cj_mem_O L t.2⟩ : L.O) • c x := hs t x
      rw [this]; exact Submodule.smul_mem _ _ h
end GlobalTheory.QRefl
