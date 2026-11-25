-- Prove2me | solution 1 for GlobalTheory.HL.LevelRep.level_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:00:43.383633+00:00
-- url     : https://prove2.me/submissions/f13e315f-e05a-4543-ad37-9d8a16617a5f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermLevelZeroAndBoundedRepresentatives
import Theorems.Thm_GlobalTheory_HL_LevelRep_spanTo_mono
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_HL_StdLat_exists_coef
import Theorems.Thm_GlobalTheory_HL_TermBasic_self_mem
import Theorems.Thm_GlobalTheory_HL_TermBasic_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_TermBasic_sub_mem
import Theorems.Thm_GlobalTheory_HL_TermBasic_term_basic
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.LevelRep
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable {S} {g g' : Fin (r + 1) → S.V}
end GlobalTheory.HL.LevelRep
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable {S} {g g' : Fin (r + 1) → S.V} in
private lemma mem_spanTo_of_triangular_of_lt {h : Fin (r + 1) → S.V}
    (hsub : ∀ i : Fin (r + 1), h i - g i ∈ S.spanTo g i)
    {i : Fin (r + 1)} {j : ℕ} (hij : (i : ℕ) < j) : h i ∈ S.spanTo g j := by
  have := Submodule.add_mem _ (_root_.GlobalTheory.HL.TermBasic.self_mem S g hij)
    (_root_.GlobalTheory.HL.TermBasic.spanTo_mono S g hij.le (hsub i))
  simpa using this
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable {S} {g g' : Fin (r + 1) → S.V} in
private lemma spanTo_le_span_image_of_triangular {h : Fin (r + 1) → S.V}
    (hsub : ∀ i : Fin (r + 1), h i - g i ∈ S.spanTo g i) (j : ℕ) :
    S.spanTo g j ≤ Submodule.span E (h '' {i | (i : ℕ) < j}) := by
  induction j with
  | zero =>
    unfold _root_.GlobalTheory.HL.Frames.spanTo
    simp
  | succ j ih =>
    rw [show S.spanTo g (j + 1) = Submodule.span E (g '' {i | (i : ℕ) < j + 1}) from rfl,
      Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have hmono : Submodule.span E (h '' {i | (i : ℕ) < j}) ≤
        Submodule.span E (h '' {i | (i : ℕ) < j + 1}) :=
      Submodule.span_mono (Set.image_mono fun x hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢; omega)
    simp only [Set.mem_setOf_eq] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · exact hmono (ih (_root_.GlobalTheory.HL.TermBasic.self_mem S g hi))
    · have h1 : h i ∈ Submodule.span E (h '' {i | (i : ℕ) < j + 1}) :=
        Submodule.subset_span ⟨i, (show (i : ℕ) < j + 1 by omega), rfl⟩
      have h2' := hsub i
      rw [hi] at h2'
      have h2 := hmono (ih h2')
      have := Submodule.sub_mem _ h1 h2
      simpa using this
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable {S} {g g' : Fin (r + 1) → S.V} in
private lemma levelRep_good_add_add_smul (hθ : S.th ≠ 0) {j : ℕ} {u u' m : S.V}
    (hu : u ∈ Submodule.span E (g '' {i | (i : ℕ) < j}))
    (hu' : u' ∈ Submodule.span E (g' '' {i | (i : ℕ) < j}))
    (hm : m ∈ Submodule.span L.O (Set.range g ∪
      Set.range fun b => algebraMap F E S.th⁻¹ • (g' b - g b))) :
    _root_.GlobalTheory.HL.LevelRep.Good S g g' j (u + u' + algebraMap F E S.th • m) := by
  have ht : algebraMap F E S.th * algebraMap F E S.th⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hθ, map_one]
  obtain ⟨c, hc0, rfl⟩ := _root_.GlobalTheory.HL.StdLat.exists_coef g _ hu
  obtain ⟨c', hc0', rfl⟩ := _root_.GlobalTheory.HL.StdLat.exists_coef g' _ hu'
  rw [Submodule.span_union, Submodule.mem_sup] at hm
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := hm
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hm₁
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hm₂
  refine ⟨fun i => c i + algebraMap F E S.th * a i - b i, fun i => c' i + b i, ?_, ?_⟩
  · have key : ∀ i, c i • g i + c' i • g' i + algebraMap F E S.th •
        ((a i : E) • g i + (b i : E) • (algebraMap F E S.th⁻¹ • (g' i - g i))) =
        (c i + algebraMap F E S.th * a i - b i) • g i + (c' i + b i) • g' i := by
      intro i
      match_scalars <;> first | ring1 | linear_combination (b i : E) * ht | linear_combination (-(b i : E)) * ht
    simp only [Subring.smul_def]
    calc _ = ∑ i, (c i • g i + c' i • g' i + algebraMap F E S.th •
          ((a i : E) • g i + (b i : E) • (algebraMap F E S.th⁻¹ • (g' i - g i)))) := by
          simp only [Finset.sum_add_distrib, Finset.smul_sum, smul_add]
      _ = _ := by rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib]
  · intro i hi
    have hci : c i = 0 := hc0 i (by simp only [Set.mem_setOf_eq, not_lt]; exact hi)
    have hci' : c' i = 0 := hc0' i (by simp only [Set.mem_setOf_eq, not_lt]; exact hi)
    refine ⟨by simpa [hci'] using (b i).2, a i, (a i).2, ?_⟩
    simp only [hci, hci']
    ring
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable {S} {g g' : Fin (r + 1) → S.V} in
private lemma levelRep_good_mono {j j' : ℕ} {b : S.V}
    (h : _root_.GlobalTheory.HL.LevelRep.Good S g g' j b) (hj : j ≤ j') :
    _root_.GlobalTheory.HL.LevelRep.Good S g g' j' b := by
  obtain ⟨al, al', hb, hal⟩ := h
  exact ⟨al, al', hb, fun i hi => hal i (hj.trans hi)⟩
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable {S} {g g' : Fin (r + 1) → S.V} in
private lemma lev_le_iff_levelRep_good {b : S.V}
    (h : ∃ j₀, _root_.GlobalTheory.HL.LevelRep.Good S g g' j₀ b) (j : ℕ) :
    S.lev g g' b ≤ j ↔ _root_.GlobalTheory.HL.LevelRep.Good S g g' j b := by
  have hset : S.lev g g' b =
      sInf {j | _root_.GlobalTheory.HL.LevelRep.Good S g g' j b} := rfl
  rw [hset]
  constructor
  · intro hj
    exact levelRep_good_mono (Nat.sInf_mem h) hj
  · intro hj
    exact Nat.sInf_le hj
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable {S} {g g' : Fin (r + 1) → S.V} in
private lemma exists_decomp_of_levelRep_good (hθ : S.th ≠ 0) {j : ℕ} {v : S.V}
    (h : _root_.GlobalTheory.HL.LevelRep.Good S g g' j v) :
    ∃ u ∈ Submodule.span E (g '' {i | (i : ℕ) < j}),
      ∃ u' ∈ Submodule.span E (g' '' {i | (i : ℕ) < j}),
        ∃ m ∈ Submodule.span L.O (Set.range g ∪
          Set.range fun b => algebraMap F E S.th⁻¹ • (g' b - g b)),
          v = u + u' + algebraMap F E S.th • m := by
  have ht : algebraMap F E S.th * algebraMap F E S.th⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hθ, map_one]
  obtain ⟨al, al', rfl, hal⟩ := h
  refine ⟨∑ i : Fin (r + 1), (if (i : ℕ) < j then al i else 0) • g i, ?_,
    ∑ i : Fin (r + 1), (if (i : ℕ) < j then al' i else 0) • g' i, ?_,
    ∑ i : Fin (r + 1), (if (i : ℕ) < j then 0 else
      algebraMap F E S.th⁻¹ • (al i • g i + al' i • g' i)), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun i _ => ?_
    split_ifs with hi
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · rw [zero_smul]; exact Submodule.zero_mem _
  · refine Submodule.sum_mem _ fun i _ => ?_
    split_ifs with hi
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · rw [zero_smul]; exact Submodule.zero_mem _
  · refine Submodule.sum_mem _ fun i _ => ?_
    split_ifs with hi
    · exact Submodule.zero_mem _
    · obtain ⟨hb, c, hc, hsum⟩ := hal i (not_lt.1 hi)
      have hal_eq : al i = algebraMap F E S.th * c - al' i := by
        linear_combination hsum
      have hrw : algebraMap F E S.th⁻¹ • (al i • g i + al' i • g' i) =
          (⟨c, hc⟩ : L.O) • g i + (⟨al' i, hb⟩ : L.O) •
            (algebraMap F E S.th⁻¹ • (g' i - g i)) := by
        rw [Subring.smul_def, Subring.smul_def, hal_eq]
        match_scalars <;> first | ring1 | linear_combination c * ht | linear_combination (-c) * ht
      rw [hrw]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨i, rfl⟩)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨i, rfl⟩)))
  · simp only [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs
    · simp
    · simp only [zero_smul, zero_add, smul_smul, ht, one_smul]
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable {S} {g g' : Fin (r + 1) → S.V} in
private lemma eq_and_eq_of_sum_elim_linearIndependent (hli : LinearIndependent E (Sum.elim g g'))
    {a a' b b' : Fin (r + 1) → E}
    (h : ∑ i, a i • g i + ∑ i, a' i • g' i = ∑ i, b i • g i + ∑ i, b' i • g' i) :
    a = b ∧ a' = b' := by
  have h0 := Fintype.linearIndependent_iff.1 hli (Sum.elim (a - b) (a' - b')) (by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    rw [sub_add_sub_comm, h, sub_self])
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · have := h0 (Sum.inl i)
    simpa [sub_eq_zero] using this
  · have := h0 (Sum.inr i)
    simpa [sub_eq_zero] using this
end
end

set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
namespace _root_.GlobalTheory.HL.LevelRep
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → (∀ y ∈ S.sat Λ, S.levC d Λ y = 0 ↔ y ∈ S.M d Λ) ∧ (∀ y ∈ S.sat Λ, ∀ j, S.levC d Λ y ≤ j ↔ ∃ y₁ ∈ (S.spanTo S.f j ⊔ S.spanTo S.f' j), y - y₁ ∈ S.M d Λ) ∧ (∀ y ∈ S.sat Λ, ∀ m ∈ S.M d Λ, S.levC d Λ (y + m) = S.levC d Λ y) ∧ ∀ (al al' : Fin (r + 1) → E) (j : ℕ), S.lev (S.fr d Λ) (S.fr' d Λ) (∑ i, al i • S.fr d Λ i + ∑ i, al' i • S.fr' d Λ i) ≤ j ↔ ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (al i) (al' i) := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT
  obtain ⟨-, hW, hMsat, -, -, hli, -⟩ := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, -, -, -, hθ, -⟩ := _root_.GlobalTheory.FrameBasic.main L r k S
  obtain ⟨-, -, hp, hq, -⟩ := hW
  have hsub : ∀ i : Fin (r + 1), S.fr d Λ i - S.f i ∈
      S.spanTo S.f i := fun i =>
    _root_.GlobalTheory.HL.TermBasic.sub_mem (S := S) (g := S.f)
      (fun a j => (S.gram a j.castSucc).trans
        (if_neg fun h => (Fin.castSucc_lt_last j).ne h.2)) hp i
  have hsub' : ∀ i : Fin (r + 1), S.fr' d Λ i - S.f' i ∈
      S.spanTo S.f' i := fun i =>
    _root_.GlobalTheory.HL.TermBasic.sub_mem (S := S) (g := S.f')
      (fun a j => (S.gram' a j.castSucc).trans
        (if_neg fun h => (Fin.castSucc_lt_last j).ne h.2)) hq i
  have hti : algebraMap F E S.th⁻¹ * algebraMap F E S.th = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hθ, map_one]
  have hspan : ∀ j, Submodule.span E (S.fr d Λ '' {i | (i : ℕ) < j}) ≤
      S.spanTo S.f j := fun j =>
    Submodule.span_le.2 (by rintro _ ⟨i, hi, rfl⟩; exact mem_spanTo_of_triangular_of_lt hsub hi)
  have hspan' : ∀ j, Submodule.span E (S.fr' d Λ '' {i | (i : ℕ) < j}) ≤
      S.spanTo S.f' j := fun j =>
    Submodule.span_le.2 (by rintro _ ⟨i, hi, rfl⟩; exact mem_spanTo_of_triangular_of_lt hsub' hi)
  have hbound := spanTo_le_span_image_of_triangular hsub
  have hbound' := spanTo_le_span_image_of_triangular hsub'
  have hlev : ∀ y ∈ S.sat Λ, ∀ j, S.levC d Λ y ≤ j ↔
      ∃ y₁ ∈ (S.spanTo S.f j ⊔ S.spanTo S.f' j),
        y - y₁ ∈ S.M d Λ := by
    intro y hy j
    have hex : ∃ j₀, _root_.GlobalTheory.HL.LevelRep.Good S (S.fr d Λ)
        (S.fr' d Λ) j₀ (algebraMap F E S.th • y) := by
      refine ⟨r + 1, ?_⟩
      have hy2 : y ∈ Λ ∧ y ∈ S.spanTo S.f (r + 1) ⊔
          S.spanTo S.f' (r + 1) := hy
      obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.1 hy2.2
      have := levelRep_good_add_add_smul hθ
        (Submodule.smul_mem _ (algebraMap F E S.th) (hbound (r + 1) hu))
        (Submodule.smul_mem _ (algebraMap F E S.th) (hbound' (r + 1) hu'))
        (Submodule.zero_mem _)
      simpa [smul_add] using this
    show S.lev _ _ (algebraMap F E S.th • y) ≤ j ↔ _
    rw [lev_le_iff_levelRep_good hex]
    constructor
    · intro h
      obtain ⟨u, hu, u', hu', m, hm, hv⟩ := exists_decomp_of_levelRep_good hθ h
      refine ⟨algebraMap F E S.th⁻¹ • (u + u'), ?_, ?_⟩
      · exact Submodule.smul_mem _ _ (Submodule.add_mem_sup (hspan j hu) (hspan' j hu'))
      · have hym : y - algebraMap F E S.th⁻¹ • (u + u') = m := by
          have h2 : y = algebraMap F E S.th⁻¹ • (algebraMap F E S.th • y) := by
            rw [smul_smul, hti, one_smul]
          rw [h2, hv, smul_add, smul_smul, hti, one_smul]
          abel
        rw [hym]
        exact hm
    · rintro ⟨y₁, hy₁, hm⟩
      obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.1 hy₁
      have := levelRep_good_add_add_smul hθ
        (Submodule.smul_mem _ (algebraMap F E S.th) (hbound j hu))
        (Submodule.smul_mem _ (algebraMap F E S.th) (hbound' j hu')) hm
      have heq : algebraMap F E S.th • u + algebraMap F E S.th • u' +
          algebraMap F E S.th • (y - (u + u')) = algebraMap F E S.th • y := by
        rw [← smul_add, ← smul_add]
        congr 1
        abel
      rwa [heq] at this
  refine ⟨fun y hy => ?_, hlev, fun y hy m hm => ?_, fun al al' j => ?_⟩
  · rw [← Nat.le_zero, hlev y hy 0]
    have h0 : S.spanTo S.f 0 = ⊥ := by
      unfold _root_.GlobalTheory.HL.Frames.spanTo
      simp
    have h0' : S.spanTo S.f' 0 = ⊥ := by
      unfold _root_.GlobalTheory.HL.Frames.spanTo
      simp
    rw [h0, h0', bot_sup_eq]
    simp
  · have hy' : y + m ∈ S.sat Λ := Submodule.add_mem _ hy (hMsat hm)
    apply le_antisymm
    · rw [hlev _ hy']
      obtain ⟨y₁, hy₁, hym⟩ := (hlev y hy _).1 le_rfl
      refine ⟨y₁, hy₁, ?_⟩
      convert Submodule.add_mem _ hym hm using 1
      abel
    · rw [hlev _ hy]
      obtain ⟨y₁, hy₁, hym⟩ := (hlev _ hy' _).1 le_rfl
      refine ⟨y₁, hy₁, ?_⟩
      convert Submodule.sub_mem _ hym hm using 1
      abel
  · have hv : _root_.GlobalTheory.HL.LevelRep.Good S (S.fr d Λ) (S.fr' d Λ)
        (r + 1) (∑ i, al i • S.fr d Λ i + ∑ i, al' i • S.fr' d Λ i) :=
      ⟨al, al', rfl, fun i hi => absurd hi (not_le.2 i.isLt)⟩
    rw [lev_le_iff_levelRep_good ⟨r + 1, hv⟩]
    constructor
    · rintro ⟨bl, bl', hb, hbl⟩
      obtain ⟨rfl, rfl⟩ := eq_and_eq_of_sum_elim_linearIndependent hli hb
      exact hbl
    · intro h
      exact ⟨al, al', rfl, h⟩
end _root_.GlobalTheory.HL.LevelRep
