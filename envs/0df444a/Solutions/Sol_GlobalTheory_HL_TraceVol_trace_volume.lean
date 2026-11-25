-- Prove2me | solution 1 for GlobalTheory.HL.TraceVol.trace_volume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:50:56.158807+00:00
-- url     : https://prove2.me/submissions/1b367bdd-0257-4f9a-a3be-8610e846bf39

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameUnipotentUnitriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexSpanLatticeMatrixDetNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeTraceInitialSpanVolumeEq
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_CardQuotientPow_main
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_HL_FrameIndex_relIndex_span_matrix
import Theorems.Thm_GlobalTheory_HL_FrameTri_sub_mem
import Theorems.Thm_GlobalTheory_HL_TermBasic_sub_mem
import Theorems.Thm_GlobalTheory_HL_TermBasic_term_basic
import Theorems.Thm_GlobalTheory_HL_frame_unipotent_unitriangular
import Theorems.Thm_GlobalTheory_QuotientCardinality_main
import Theorems.Thm_GlobalTheory_UnramVal_vE_zpow_mul_unit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.TraceVol
section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}
end
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private theorem unitriangular_sum_castLE_eq {E V : Type} [CommRing E] [AddCommGroup V] [Module E V]
    {m J : ℕ} (hJ : J ≤ m) (b : Fin m → V) (s : Fin m → Fin m → E)
    (hs : ∀ i j, j < i → s i j = 0) (j : Fin J) :
    ∑ i, s i (Fin.castLE hJ j) • b i =
      ∑ i : Fin J, s (Fin.castLE hJ i) (Fin.castLE hJ j) • b (Fin.castLE hJ i) := by
  rw [show (∑ i : Fin J, s (Fin.castLE hJ i) (Fin.castLE hJ j) • b (Fin.castLE hJ i)) =
      ∑ i ∈ Finset.univ.map (Fin.castLEEmb hJ), s i (Fin.castLE hJ j) • b i from
    by rw [Finset.sum_map]; rfl]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
  have hiJ : ¬ (i : ℕ) < J := fun h => hi (Finset.mem_map.2 ⟨⟨i, h⟩, Finset.mem_univ _, rfl⟩)
  rw [hs i _ (by rw [Fin.lt_def]; simp; omega), zero_smul]
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private theorem span_image_frameScaledDifferenceFamily_eq_lemma_3 {E V : Type} [CommRing E] [AddCommGroup V]
    [Module E V] (O : Subring E) {m J : ℕ} (hJ : J ≤ m) (f f' : Fin m → V)
    (s s' : Matrix (Fin m) (Fin m) E) (hs : ∀ i j, j < i → s i j = 0)
    (hs' : ∀ i j, j < i → s' i j = 0) (θ : E) :
    Submodule.span O (_root_.GlobalTheory.HL.TraceVol.dfam θ (fun j => ∑ i, s i j • f i)
        (fun j => ∑ i, s' i j • f' i) ''
        {a | Sum.elim (fun i : Fin m => (i : ℕ)) (fun i : Fin m => (i : ℕ)) a < J}) =
      Submodule.span O (Set.range fun j => ∑ i, Matrix.fromBlocks (s.submatrix (Fin.castLE hJ) (Fin.castLE hJ))
        (-(θ • s.submatrix (Fin.castLE hJ) (Fin.castLE hJ))) 0
        (θ • s'.submatrix (Fin.castLE hJ) (Fin.castLE hJ)) i j •
          Sum.elim (fun i => f (Fin.castLE hJ i)) (fun i => f' (Fin.castLE hJ i)) i) := by
  have hpt : ∀ a : Fin J ⊕ Fin J, (∑ i, Matrix.fromBlocks (s.submatrix (Fin.castLE hJ) (Fin.castLE hJ))
        (-(θ • s.submatrix (Fin.castLE hJ) (Fin.castLE hJ))) 0
        (θ • s'.submatrix (Fin.castLE hJ) (Fin.castLE hJ)) i a •
          Sum.elim (fun i => f (Fin.castLE hJ i)) (fun i => f' (Fin.castLE hJ i)) i) =
      _root_.GlobalTheory.HL.TraceVol.dfam θ (fun j => ∑ i, s i j • f i) (fun j => ∑ i, s' i j • f' i)
        (Sum.map (Fin.castLE hJ) (Fin.castLE hJ) a) := by
    intro a
    rcases a with j | j
    · rw [Fintype.sum_sum_type]
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.submatrix_apply,
        Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, zero_smul, Finset.sum_const_zero, add_zero,
        _root_.GlobalTheory.HL.TraceVol.dfam, Sum.map_inl]
      rw [unitriangular_sum_castLE_eq hJ f s hs j]
    · rw [Fintype.sum_sum_type]
      simp only [Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.submatrix_apply,
        Sum.elim_inl, Sum.elim_inr, _root_.GlobalTheory.HL.TraceVol.dfam, Sum.map_inr]
      rw [unitriangular_sum_castLE_eq hJ f s hs j, unitriangular_sum_castLE_eq hJ f' s' hs' j]
      simp only [Matrix.neg_apply, Matrix.smul_apply, Matrix.submatrix_apply, neg_smul, smul_sub,
        Finset.smul_sum, smul_smul, smul_eq_mul, Finset.sum_neg_distrib]
      abel
  have hset : _root_.GlobalTheory.HL.TraceVol.dfam θ (fun j => ∑ i, s i j • f i)
        (fun j => ∑ i, s' i j • f' i) ''
        {a | Sum.elim (fun i : Fin m => (i : ℕ)) (fun i : Fin m => (i : ℕ)) a < J} =
      Set.range fun a : Fin J ⊕ Fin J => _root_.GlobalTheory.HL.TraceVol.dfam θ (fun j => ∑ i, s i j • f i)
        (fun j => ∑ i, s' i j • f' i) (Sum.map (Fin.castLE hJ) (Fin.castLE hJ) a) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      rcases a with i | i
      · exact ⟨Sum.inl ⟨i, ha⟩, rfl⟩
      · exact ⟨Sum.inr ⟨i, ha⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      rcases a with i | i
      · exact ⟨Sum.inl (Fin.castLE hJ i), by simp, rfl⟩
      · exact ⟨Sum.inr (Fin.castLE hJ i), by simp, rfl⟩
  rw [hset]
  congr 2
  funext a
  exact (hpt a).symm
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private theorem dfam_mem_lower_span {E V : Type} [CommRing E] [AddCommGroup V]
    [Module E V] {m : ℕ} (f f' g g' : Fin m → V) (t : E)
    (hg : ∀ j, g j - f j ∈ Submodule.span E (f '' {i | i < j}))
    (hg' : ∀ j, g' j - f' j ∈ Submodule.span E (f' '' {i | i < j})) (J : ℕ) (a : Fin m ⊕ Fin m)
    (ha : Sum.elim (fun i : Fin m => (i : ℕ)) (fun i : Fin m => (i : ℕ)) a < J) :
    _root_.GlobalTheory.HL.TraceVol.dfam t g g' a ∈
      Submodule.span E (f '' {i | (i : ℕ) < J}) ⊔ Submodule.span E (f' '' {i | (i : ℕ) < J}) := by
  have hf : ∀ j : Fin m, (j : ℕ) < J → g j ∈ Submodule.span E (f '' {i | (i : ℕ) < J}) := by
    intro j hj
    have h1 : f j ∈ Submodule.span E (f '' {i | (i : ℕ) < J}) :=
      Submodule.subset_span ⟨j, hj, rfl⟩
    have h2 : g j - f j ∈ Submodule.span E (f '' {i | (i : ℕ) < J}) :=
      Submodule.span_mono (Set.image_mono fun i (hi : i < j) => lt_trans (Fin.lt_def.1 hi) hj) (hg j)
    simpa using Submodule.add_mem _ h2 h1
  have hf' : ∀ j : Fin m, (j : ℕ) < J → g' j ∈ Submodule.span E (f' '' {i | (i : ℕ) < J}) := by
    intro j hj
    have h1 : f' j ∈ Submodule.span E (f' '' {i | (i : ℕ) < J}) :=
      Submodule.subset_span ⟨j, hj, rfl⟩
    have h2 : g' j - f' j ∈ Submodule.span E (f' '' {i | (i : ℕ) < J}) :=
      Submodule.span_mono (Set.image_mono fun i (hi : i < j) => lt_trans (Fin.lt_def.1 hi) hj) (hg' j)
    simpa using Submodule.add_mem _ h2 h1
  rcases a with j | j
  · exact Submodule.mem_sup_left (hf j ha)
  · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.mem_sup_right (hf' j ha))
      (Submodule.mem_sup_left (hf j ha)))
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private theorem coeff_eq_zero_of_mem_span_lower_indices {E V : Type} [CommRing E] [AddCommGroup V] [Module E V]
    {m : ℕ} (f f' : Fin m → V) (hB : LinearIndependent E (Sum.elim f f')) (J : Fin m) (α β : E)
    (h : α • f J + β • f' J ∈ Submodule.span E (f '' {i | i < J}) ⊔ Submodule.span E (f' '' {i | i < J})) :
    α = 0 ∧ β = 0 := by
  have hsup : Submodule.span E (f '' {i | i < J}) ⊔ Submodule.span E (f' '' {i | i < J}) =
      Submodule.span E (Sum.elim f f' '' (Sum.inl '' {i | i < J} ∪ Sum.inr '' {i | i < J})) := by
    rw [Set.image_union, Submodule.span_union, Set.image_image, Set.image_image]
    rfl
  have hpair : α • f J + β • f' J ∈
      Submodule.span E (Sum.elim f f' '' {Sum.inl J, Sum.inr J}) := by
    rw [Set.image_pair]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hdisj := hB.disjoint_span_image (s := {Sum.inl J, Sum.inr J})
    (t := Sum.inl '' {i | i < J} ∪ Sum.inr '' {i | i < J}) (by
      rw [Set.disjoint_left]
      intro a ha hb
      rcases ha with rfl | rfl <;> rcases hb with ⟨i, hi, h⟩ | ⟨i, hi, h⟩ <;>
        simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Set.mem_setOf_eq] at h hi <;>
        subst h <;> exact lt_irrefl _ hi)
  rw [hsup] at h
  have h0 : α • f J + β • f' J = 0 := (Submodule.disjoint_def.1 hdisj) _ hpair h
  have hli := hB.comp (fun b : Bool => if b then Sum.inl J else Sum.inr J) (by
    intro a b hab; cases a <;> cases b <;> simp_all)
  rw [Fintype.linearIndependent_iff] at hli
  have := hli (fun b => if b then α else β) (by simpa [add_comm] using h0)
  exact ⟨this true, this false⟩
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private theorem mem_span_dfam_inf_iff {E V : Type} [CommRing E]
    [AddCommGroup V] [Module E V] (O : Subring E) {m : ℕ} (f f' g g' : Fin m → V)
    (hB : LinearIndependent E (Sum.elim f f')) (t : E) (ht : IsUnit t)
    (hg : ∀ j, g j - f j ∈ Submodule.span E (f '' {i | i < j}))
    (hg' : ∀ j, g' j - f' j ∈ Submodule.span E (f' '' {i | i < j})) (J : ℕ) (x : V) :
    (x ∈ Submodule.span O (Set.range (_root_.GlobalTheory.HL.TraceVol.dfam t g g')) ∧
      x ∈ Submodule.span E (f '' {i | (i : ℕ) < J}) ⊔ Submodule.span E (f' '' {i | (i : ℕ) < J})) ↔
      x ∈ Submodule.span O (_root_.GlobalTheory.HL.TraceVol.dfam t g g' ''
        {a | Sum.elim (fun i : Fin m => (i : ℕ)) (fun i : Fin m => (i : ℕ)) a < J}) := by
  have hle : ∀ J : ℕ, Submodule.span O (_root_.GlobalTheory.HL.TraceVol.dfam t g g' ''
      {a | Sum.elim (fun i : Fin m => (i : ℕ)) (fun i : Fin m => (i : ℕ)) a < J}) ≤
      (Submodule.span E (f '' {i | (i : ℕ) < J}) ⊔
        Submodule.span E (f' '' {i | (i : ℕ) < J})).restrictScalars O := by
    intro J
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    exact dfam_mem_lower_span f f' g g' t hg hg' J a ha
  refine ⟨fun ⟨hx, hY⟩ => ?_, fun hx => ⟨Submodule.span_mono (Set.image_subset_range _ _) hx, hle J hx⟩⟩
  suffices H : ∀ d J, m ≤ J + d → ∀ x, x ∈ Submodule.span O (Set.range (_root_.GlobalTheory.HL.TraceVol.dfam t g g')) →
      x ∈ Submodule.span E (f '' {i | (i : ℕ) < J}) ⊔ Submodule.span E (f' '' {i | (i : ℕ) < J}) →
      x ∈ Submodule.span O (_root_.GlobalTheory.HL.TraceVol.dfam t g g' ''
        {a | Sum.elim (fun i : Fin m => (i : ℕ)) (fun i : Fin m => (i : ℕ)) a < J}) from
    H m J (by omega) x hx hY
  intro d
  induction d with
  | zero =>
    intro J hJ x hx _
    have huniv : {a : Fin m ⊕ Fin m | Sum.elim (fun i : Fin m => (i : ℕ)) (fun i : Fin m => (i : ℕ)) a < J} =
        Set.univ := Set.eq_univ_of_forall fun a => by
      rcases a with i | i <;> exact lt_of_lt_of_le i.isLt (by omega)
    rwa [huniv, Set.image_univ]
  | succ d ih =>
    intro J hJ x hx hY
    by_cases hJm : m ≤ J + d
    · exact ih J hJm x hx hY
    have hJlt : J < m := by omega
    set j0 : Fin m := ⟨J, hJlt⟩ with hj0
    have hYmono : Submodule.span E (f '' {i | (i : ℕ) < J}) ⊔ Submodule.span E (f' '' {i | (i : ℕ) < J}) ≤
        Submodule.span E (f '' {i | (i : ℕ) < J + 1}) ⊔ Submodule.span E (f' '' {i | (i : ℕ) < J + 1}) :=
      sup_le_sup (Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < J) => by
        show (i : ℕ) < J + 1; omega))
        (Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < J) => by
        show (i : ℕ) < J + 1; omega))
    have hx1 := ih (J + 1) (by omega) x hx (hYmono hY)
    have hset : _root_.GlobalTheory.HL.TraceVol.dfam t g g' ''
        {a | Sum.elim (fun i : Fin m => (i : ℕ)) (fun i : Fin m => (i : ℕ)) a < J + 1} =
        {_root_.GlobalTheory.HL.TraceVol.dfam t g g' (Sum.inl j0), _root_.GlobalTheory.HL.TraceVol.dfam t g g' (Sum.inr j0)} ∪
        _root_.GlobalTheory.HL.TraceVol.dfam t g g' ''
          {a | Sum.elim (fun i : Fin m => (i : ℕ)) (fun i : Fin m => (i : ℕ)) a < J} := by
      rw [← Set.image_pair, ← Set.image_union]
      congr 1
      ext a
      rcases a with i | i <;>
        simp only [Set.mem_setOf_eq, Sum.elim_inl, Sum.elim_inr, Set.mem_union, Set.mem_insert_iff,
          Set.mem_singleton_iff, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_or, or_false,
          Fin.ext_iff, hj0] <;> omega
    rw [hset, Submodule.span_union, Submodule.mem_sup] at hx1
    obtain ⟨z, hz, y, hy, rfl⟩ := hx1
    rw [Submodule.mem_span_pair] at hz
    obtain ⟨a, b, rfl⟩ := hz
    have hyY := hle J hy
    have hzY : a • _root_.GlobalTheory.HL.TraceVol.dfam t g g' (Sum.inl j0) +
        b • _root_.GlobalTheory.HL.TraceVol.dfam t g g' (Sum.inr j0) ∈
        Submodule.span E (f '' {i | (i : ℕ) < J}) ⊔ Submodule.span E (f' '' {i | (i : ℕ) < J}) := by
      have := Submodule.sub_mem _ hY hyY
      simpa using this
    have hsets : ∀ h : Fin m → V, h '' {i | i < j0} = h '' {i | (i : ℕ) < J} := fun h => by
      congr 1
    have hrest : ((a : E) - b * t) • (g j0 - f j0) + ((b : E) * t) • (g' j0 - f' j0) ∈
        Submodule.span E (f '' {i | (i : ℕ) < J}) ⊔ Submodule.span E (f' '' {i | (i : ℕ) < J}) :=
      Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ (by rw [← hsets]; exact hg j0)))
        (Submodule.mem_sup_right (Submodule.smul_mem _ _ (by rw [← hsets]; exact hg' j0)))
    have hmain : ((a : E) - b * t) • f j0 + ((b : E) * t) • f' j0 ∈
        Submodule.span (E) (f '' {i | i < j0}) ⊔ Submodule.span E (f' '' {i | i < j0}) := by
      rw [hsets, hsets]
      have := Submodule.sub_mem _ hzY hrest
      convert this using 1
      simp only [_root_.GlobalTheory.HL.TraceVol.dfam, Sum.elim_inl, Sum.elim_inr, Subring.smul_def, smul_sub,
        sub_smul, smul_smul]
      module
    obtain ⟨h1, h2⟩ := coeff_eq_zero_of_mem_span_lower_indices f f' hB j0 _ _ hmain
    have hb : b = 0 := Subtype.ext (by simpa using (ht.mul_left_eq_zero).1 h2)
    have ha : a = 0 := Subtype.ext (by simpa [hb] using h1)
    simpa [ha, hb] using hy
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private theorem unitriangular_sum_sub_mem_span_lower {E V : Type} [CommRing E] [AddCommGroup V] [Module E V]
    {m : ℕ} (b : Fin m → V) (s : Fin m → Fin m → E)
    (hs : (∀ i j, j < i → s i j = 0) ∧ ∀ i, s i i = 1) (j : Fin m) :
    ∑ i, s i j • b i - b j ∈ Submodule.span E (b '' {i | i < j}) := by
  have key : ∀ i, s i j • b i = (if i < j then s i j • b i else 0) + (if i = j then b i else 0) := by
    intro i
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.ne]
    · simp [hs.2]
    · simp [hs.1 i j h, not_lt.2 h.le, h.ne']
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, add_sub_cancel_right]
  refine Submodule.sum_mem _ fun i _ => ?_
  split_ifs with h
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, h, rfl⟩)
  · exact Submodule.zero_mem _
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private theorem termFrameLattice_inf_initialSpan_eq_lemma {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k)
    (d : S.Datum) (Λ : Submodule L.O S.V) (hT : S.IsTerm d Λ) (J : ℕ)
    (hJ : J ≤ r + 1) :
    ∃ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      ((∀ i j, j < i → s i j = 0) ∧ ∀ i, s i i = 1) ∧
      ((∀ i j, j < i → s' i j = 0) ∧ ∀ i, s' i i = 1) ∧
      S.M d Λ ⊓ (S.spanTo S.f J ⊔
          S.spanTo S.f' J).restrictScalars L.O =
        Submodule.span L.O (Set.range fun j => ∑ i, Matrix.fromBlocks (s.submatrix (Fin.castLE hJ) (Fin.castLE hJ))
          (-(algebraMap F E S.th⁻¹ • s.submatrix (Fin.castLE hJ) (Fin.castLE hJ))) 0
          (algebraMap F E S.th⁻¹ • s'.submatrix (Fin.castLE hJ) (Fin.castLE hJ)) i j •
            Sum.elim (fun i => S.f (Fin.castLE hJ i)) (fun i => S.f' (Fin.castLE hJ i)) i) := by
  obtain ⟨-, hW, -⟩ := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  unfold _root_.GlobalTheory.HL.Frames.IsTermW at hW
  obtain ⟨-, -, hp, hq, -⟩ := hW
  obtain ⟨hB, -, -, -, -, hth, -⟩ := _root_.GlobalTheory.FrameBasic.main L r k S
  obtain ⟨-, hN⟩ := _root_.GlobalTheory.HL.frame_unipotent_unitriangular L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨-, hN'⟩ := _root_.GlobalTheory.HL.frame_unipotent_unitriangular L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩)
  obtain ⟨⟨s, hs, hsf⟩, -⟩ := hN _ hp
  obtain ⟨⟨s', hs', hsf'⟩, -⟩ := hN' _ hq
  refine ⟨s, s', hs, hs', ?_⟩
  have hθ : IsUnit (algebraMap F E S.th⁻¹) := (isUnit_iff_ne_zero.2 (inv_ne_zero hth)).map _
  have hM : S.M d Λ = Submodule.span L.O (Set.range
      (_root_.GlobalTheory.HL.TraceVol.dfam (algebraMap F E S.th⁻¹)
        (fun j => ∑ i, s i j • S.f i) (fun j => ∑ i, s' i j • S.f' i))) := by
    unfold _root_.GlobalTheory.HL.Frames.M _root_.GlobalTheory.HL.Frames.Mof
      _root_.GlobalTheory.HL.Frames.fr _root_.GlobalTheory.HL.Frames.fr' _root_.GlobalTheory.HL.TraceVol.dfam
    rw [Set.Sum.elim_range]
    congr 3
    · funext j; exact hsf j
    · funext j; rw [hsf j, hsf' j]
  rw [← span_image_frameScaledDifferenceFamily_eq_lemma_3 L.O hJ S.f S.f' s s' hs.1 hs'.1]
  ext x
  rw [Submodule.mem_inf, hM, Submodule.restrictScalars_mem]
  exact mem_span_dfam_inf_iff L.O S.f S.f' _ _ hB _ hθ
    (unitriangular_sum_sub_mem_span_lower S.f s hs) (unitriangular_sum_sub_mem_span_lower S.f' s' hs') J x
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private theorem det_fromBlocks_unitriangular_eq_pow {E : Type} [CommRing E] {m : ℕ} (θ : E)
    (s s' : Matrix (Fin m) (Fin m) E)
    (hs : (∀ i j, j < i → s i j = 0) ∧ ∀ i, s i i = 1)
    (hs' : (∀ i j, j < i → s' i j = 0) ∧ ∀ i, s' i i = 1) :
    (Matrix.fromBlocks s (-(θ • s)) 0 (θ • s')).det = θ ^ m := by
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_of_upperTriangular (fun i j h => hs.1 i j h),
    Matrix.det_of_upperTriangular (fun i j h => hs'.1 i j h)]
  simp [hs.2, hs'.2]
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private theorem linearIndependent_comb_of_isUnit_det {E V ι : Type} [CommRing E] [AddCommGroup V] [Module E V]
    [Fintype ι] [DecidableEq ι] (b : ι → V) (hb : LinearIndependent E b) (M : Matrix ι ι E)
    (hM : IsUnit M.det) : LinearIndependent E (fun j => ∑ i, M i j • b i) := by
  rw [Fintype.linearIndependent_iff] at hb ⊢
  intro c hc
  have h1 : ∀ i, M.mulVec c i = 0 := by
    refine hb _ ?_
    rw [← hc]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  have h2 : M.mulVec c = 0 := funext h1
  have : c = M⁻¹.mulVec (M.mulVec c) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hM, Matrix.one_mulVec]
  intro i
  rw [this, h2, Matrix.mulVec_zero]
  rfl
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private theorem sum_smul_sum_smul_eq_sum_mul_smul' {E V ι : Type} [CommRing E] [AddCommGroup V] [Module E V] [Fintype ι]
    (b : ι → V) (M N : Matrix ι ι E) (j : ι) :
    ∑ i, N i j • ∑ l, M l i • b l = ∑ l, (M * N) l j • b l := by
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private theorem relIndex_symm_of_blockFrameMatrix_lemma_2 {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) (ϖ : (ValuativeRel.valuation F).integer)
    (hϖ : Irreducible ϖ) {N m : ℕ} (B : Fin m ⊕ Fin m → (Fin N → E))
    (hB : LinearIndependent E B) (θ : E) (hθ : IsUnit θ) (s s' u u' : Matrix (Fin m) (Fin m) E)
    (hs : (∀ i j, j < i → s i j = 0) ∧ ∀ i, s i i = 1)
    (hs' : (∀ i j, j < i → s' i j = 0) ∧ ∀ i, s' i i = 1)
    (hu : (∀ i j, j < i → u i j = 0) ∧ ∀ i, u i i = 1)
    (hu' : (∀ i j, j < i → u' i j = 0) ∧ ∀ i, u' i i = 1) :
    (Submodule.span L.O (Set.range fun j => ∑ i, Matrix.fromBlocks s (-(θ • s)) 0 (θ • s') i j • B i)).toAddSubgroup.relIndex
        (Submodule.span L.O (Set.range fun j => ∑ i, Matrix.fromBlocks u (-(θ • u)) 0 (θ • u') i j • B i)).toAddSubgroup =
      (Submodule.span L.O (Set.range fun j => ∑ i, Matrix.fromBlocks u (-(θ • u)) 0 (θ • u') i j • B i)).toAddSubgroup.relIndex
        (Submodule.span L.O (Set.range fun j => ∑ i, Matrix.fromBlocks s (-(θ • s)) 0 (θ • s') i j • B i)).toAddSubgroup ∧
    (Submodule.span L.O (Set.range fun j => ∑ i, Matrix.fromBlocks s (-(θ • s)) 0 (θ • s') i j • B i)).toAddSubgroup.relIndex
        (Submodule.span L.O (Set.range fun j => ∑ i, Matrix.fromBlocks u (-(θ • u)) 0 (θ • u') i j • B i)).toAddSubgroup ≠ 0 := by
  set T1 := Matrix.fromBlocks s (-(θ • s)) 0 (θ • s') with hT1
  set T2 := Matrix.fromBlocks u (-(θ • u)) 0 (θ • u') with hT2
  have hd1 : T1.det = θ ^ m := det_fromBlocks_unitriangular_eq_pow θ s s' hs hs'
  have hd2 : T2.det = θ ^ m := det_fromBlocks_unitriangular_eq_pow θ u u' hu hu'
  have hU1 : IsUnit T1.det := hd1 ▸ hθ.pow m
  let e : Fin (m + m) ≃ Fin m ⊕ Fin m := finSumFinEquiv.symm
  let A := T1⁻¹ * T2
  have hA : T1 * A = T2 := by rw [← mul_assoc, Matrix.mul_nonsing_inv T1 hU1, one_mul]
  have hdetA : A.det = 1 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, hd1, hd2]
    exact Ring.inverse_mul_cancel _ (hθ.pow m)
  let b : Fin (m + m) → (Fin N → E) := fun j => ∑ i, T1 i (e j) • B i
  have hb : LinearIndependent E b :=
    (linearIndependent_comb_of_isUnit_det B hB T1 hU1).comp e e.injective
  let A' : Matrix (Fin (m + m)) (Fin (m + m)) E := Matrix.reindex e.symm e.symm A
  have hdetA' : A'.det = 1 := by rw [Matrix.det_reindex_self, hdetA]
  have hrange1 : Set.range b = Set.range fun j => ∑ i, T1 i j • B i := by
    have : b = (fun j => ∑ i, T1 i j • B i) ∘ e := rfl
    rw [this, Set.range_comp, e.range_eq_univ, Set.image_univ]
  have hrange2 : (Set.range fun j => ∑ i, A' i j • b i) = Set.range fun j => ∑ i, T2 i j • B i := by
    have : (fun j => ∑ i, A' i j • b i) = (fun j => ∑ i, T2 i j • B i) ∘ e := by
      funext j
      simp only [Function.comp_apply, A', b, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_symm]
      rw [Equiv.sum_comp e (fun i => A i (e j) • ∑ l, T1 l i • B l), sum_smul_sum_smul_eq_sum_mul_smul', hA]
    rw [this, Set.range_comp, e.range_eq_univ, Set.image_univ]
  have hcj : A'.det * L.cj A'.det = algebraMap F E 1 := by simp [hdetA']
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.HL.FrameIndex.relIndex_span_matrix L ϖ hϖ b hb A' 1 one_ne_zero hcj
    (Submodule.span L.O (Set.range b)) (Submodule.span L.O (Set.range fun j => ∑ i, A' i j • b i))
    rfl rfl
  rw [hrange1, hrange2] at h1 h2 h3
  have hv : _root_.GlobalTheory.HL.vE L ϖ (algebraMap F E 1) = 0 := by
    simpa using _root_.GlobalTheory.UnramVal.vE_zpow_mul_unit L hϖ 0 1
  rw [hv, zpow_zero, one_mul] at h3
  exact ⟨by exact_mod_cast h3.symm, h2⟩
end GlobalTheory.HL.TraceVol
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TraceVol
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.TraceVol
namespace _root_.GlobalTheory.HL.TraceVol
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ d' Λ', S.IsTerm d' Λ' → ∀ (J : ℕ) (Yy : Submodule L.O S.V), J ≤ r + 1 → Yy = (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O → (S.M d Λ ⊓ Yy).toAddSubgroup.relIndex (S.M d' Λ' ⊓ Yy).toAddSubgroup = (S.M d' Λ' ⊓ Yy).toAddSubgroup.relIndex (S.M d Λ ⊓ Yy).toAddSubgroup ∧ (S.M d Λ ⊓ Yy).toAddSubgroup.relIndex (S.M d' Λ' ⊓ Yy).toAddSubgroup ≠ 0 := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT d' Λ' hT' J Yy hJ hYy
  subst hYy
  obtain ⟨s, s', hs, hs', h1⟩ := termFrameLattice_inf_initialSpan_eq_lemma L r k S d Λ hT J hJ
  obtain ⟨u, u', hu, hu', h2⟩ := termFrameLattice_inf_initialSpan_eq_lemma L r k S d' Λ' hT' J hJ
  obtain ⟨hB, -, -, -, -, hth, -⟩ := _root_.GlobalTheory.FrameBasic.main L r k S
  have hθ : IsUnit (algebraMap F E S.th⁻¹) := (isUnit_iff_ne_zero.2 (inv_ne_zero hth)).map _
  have hBJ : LinearIndependent E (Sum.elim (fun i : Fin J => S.f (Fin.castLE hJ i))
      (fun i => S.f' (Fin.castLE hJ i))) := by
    have := hB.comp (Sum.map (Fin.castLE hJ) (Fin.castLE hJ))
      (Sum.map_injective.2 ⟨Fin.castLE_injective hJ, Fin.castLE_injective hJ⟩)
    rwa [Sum.elim_comp_map] at this
  have htri : ∀ t : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      ((∀ i j, j < i → t i j = 0) ∧ ∀ i, t i i = 1) →
      ((∀ i j, j < i → t.submatrix (Fin.castLE hJ) (Fin.castLE hJ) i j = 0) ∧
        ∀ i, t.submatrix (Fin.castLE hJ) (Fin.castLE hJ) i i = 1) := fun t ht =>
    ⟨fun i j hij => ht.1 _ _ ((Fin.castLE_lt_castLE_iff hJ).2 hij), fun i => ht.2 _⟩
  rw [h1, h2]
  exact relIndex_symm_of_blockFrameMatrix_lemma_2 L S.ϖ S.ϖ_irr _ hBJ _ hθ _ _ _ _
    (htri s hs) (htri s' hs') (htri u hu) (htri u' hu')
end _root_.GlobalTheory.HL.TraceVol
end GlobalTheory.HL.TraceVol
