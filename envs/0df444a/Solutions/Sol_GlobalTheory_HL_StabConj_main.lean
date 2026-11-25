-- Prove2me | solution 1 for GlobalTheory.HL.StabConj.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:45:46.531817+00:00
-- url     : https://prove2.me/submissions/a75abe3b-07eb-4226-8f1c-b37f13e8319f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLatticeStabilizerNormalisingSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeStabilizerInfLeConjNormalisingSubgroup
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_HL_BlockStab_exists_monomial
import Theorems.Thm_GlobalTheory_HL_BlockStab_inv_facts
import Theorems.Thm_GlobalTheory_HL_BlockStab_stabiliser_blockDiag
import Theorems.Thm_GlobalTheory_HL_FrameOnto_unipotent_onto
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_main
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_span_le
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_uni_mul
import Theorems.Thm_GlobalTheory_HL_FrameStab_stab_eq
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
namespace GlobalTheory.HL.StabConj
section Blocks
variable {E : Type} [CommRing E]
end Blocks
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {E : Type} [CommRing E] in
private lemma rep_apply_sum_smul_eq_sum_mul_smul {n m : ℕ} {f : Fin m → Fin n → E}
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} {A : Matrix (Fin m) (Fin m) E}
    (hg : _root_.GlobalTheory.HL.StabConj.Rep f g A) (B : Matrix (Fin m) (Fin m) E) (j : Fin m) :
    g (∑ i, B i j • f i) = ∑ i, (A * B) i j • f i := by
  simp only [map_sum, map_smul, hg _, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm]
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {E : Type} [CommRing E] in
private lemma rep_inv_of_mul_eq_one {n m : ℕ} {f : Fin m → Fin n → E}
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} {A B : Matrix (Fin m) (Fin m) E}
    (hg : _root_.GlobalTheory.HL.StabConj.Rep f g A) (hAB : A * B = 1) :
    _root_.GlobalTheory.HL.StabConj.Rep f g⁻¹ B := by
  intro j
  have h := rep_apply_sum_smul_eq_sum_mul_smul hg B j
  have h1 : ∑ i, (1 : Matrix (Fin m) (Fin m) E) i j • f i = f j := by
    simp [Matrix.one_apply]
  rw [hAB, h1] at h
  rw [← h]
  exact g.symm_apply_apply _
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {E : Type} [CommRing E] in
private lemma matrix_eq_of_linearIndependent_sum_smul_eq {n m : ℕ} {f : Fin m → Fin n → E}
    (hf : LinearIndependent E f) {A B : Matrix (Fin m) (Fin m) E}
    (h : ∀ j, ∑ i, A i j • f i = ∑ i, B i j • f i) : A = B := by
  ext i j
  have := Fintype.linearIndependent_iff.mp hf (fun l => A l j - B l j)
    (by simp only [sub_smul, Finset.sum_sub_distrib, h j, sub_self])
  exact sub_eq_zero.mp (this i)
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
private lemma smul_span_le_of_rep_entries_mem (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n m : ℕ} {f : Fin m → Fin n → E}
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} {A : Matrix (Fin m) (Fin m) E}
    (hg : _root_.GlobalTheory.HL.StabConj.Rep f g A) (hA : ∀ i j, A i j ∈ L.O) :
    g • Submodule.span L.O (Set.range f) ≤ Submodule.span L.O (Set.range f) := by
  rw [Submodule.smul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  show g (f j) ∈ Submodule.span L.O (Set.range f)
  rw [hg j]
  refine Submodule.sum_mem _ fun i _ => ?_
  have : A i j • f i = (⟨A i j, hA i j⟩ : L.O) • f i := rfl
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end GlobalTheory.HL.StabConj
end
end

set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StabConj
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.StabConj
namespace _root_.GlobalTheory.HL.StabConj
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ)
    (S : _root_.GlobalTheory.HL.Frames L r k), ∀ n ∈ S.N,
    ∃ h ∈ S.St, S.St ⊓
      _root_.GlobalTheory.HL.stabL L (Submodule.span L.O (Set.range fun b => n (S.f b))) ≤
        MulAut.conj h • S.K0 ∧
      ∃ u : Matrix (Fin (r + 1)) (Fin (r + 1)) E, _root_.GlobalTheory.HL.IsUni u ∧
        (∀ i j : Fin (r + 1), _root_.Formalism.MainNotions.S.Loc.sameBlock S.w.blocks i j = true → u i j ∈ L.O) ∧
        ∀ j, h⁻¹ (n (S.f j)) = ∑ i, u i j • S.f i := by
  intro F _ _ _ _ _ E _ _ _ L r k S n hn

  obtain ⟨σ, β, τ, hβ⟩ :=
    _root_.GlobalTheory.HL.BlockStab.exists_monomial S.w.blocks
  rw [S.w.size] at hβ
  have hsame : ∀ i j : Fin (r + 1),
      _root_.Formalism.MainNotions.S.Loc.sameBlock S.w.blocks i j = true ↔ β i = β j :=
    fun i j => ((hβ i i.isLt).2.2.2 j j.isLt).1
  have hmono : ∀ i j : Fin (r + 1), i ≤ j → β i ≤ β j :=
    fun i j hij => ((hβ i i.isLt).2.2.2 j j.isLt).2.1 hij
  have hfalse : ∀ i j : Fin (r + 1), β i ≠ β j →
      _root_.Formalism.MainNotions.S.Loc.sameBlock S.w.blocks i j = false :=
    fun i j hij => Bool.eq_false_iff.mpr fun ht => hij ((hsame i j).1 ht)
  have hoff : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) E, _root_.GlobalTheory.HL.IsUni M →
      (∀ i j : Fin (r + 1), β i < β j → M i j = 0) →
      ∀ i j : Fin (r + 1), β i ≠ β j → M i j = 0 := by
    intro M hM hlt i j hij
    rcases lt_or_gt_of_ne hij with h1 | h1
    · exact hlt i j h1
    · exact hM.1 i j (lt_of_not_ge fun hle => absurd (hmono i j hle) (not_le.mpr h1))
  have hlower : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) E, _root_.GlobalTheory.HL.IsUni M →
      ∀ i j : Fin (r + 1), β j < β i → M i j = 0 := by
    intro M hM i j hij
    exact hM.1 i j (lt_of_not_ge fun hle => absurd (hmono i j hle) (not_le.mpr hij))

  obtain ⟨s, hsU, hns⟩ := (_root_.GlobalTheory.HL.FrameOnto.unipotent_onto L r k S).1 n hn
  have hsU' : _root_.GlobalTheory.HL.IsUni s := hsU
  obtain ⟨sb, hsb⟩ : ∃ sb, sb = _root_.GlobalTheory.HL.StabConj.bd S.w s := ⟨_, rfl⟩
  have hsbU : _root_.GlobalTheory.HL.IsUni sb := by
    unfold _root_.GlobalTheory.HL.IsUni
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · rw [hsb]
      simp only [_root_.GlobalTheory.HL.StabConj.bd]
      split_ifs
      · exact hsU'.1 i j hji
      · rfl
    · rw [hsb]
      simp only [_root_.GlobalTheory.HL.StabConj.bd, (hsame i i).2 rfl, if_true]
      exact hsU'.2 i
  have hsb0 : ∀ i j : Fin (r + 1),
      _root_.Formalism.MainNotions.S.Loc.sameBlock S.w.blocks i j = false → sb i j = 0 := by
    intro i j hij
    rw [hsb]
    simp [_root_.GlobalTheory.HL.StabConj.bd, hij]

  obtain ⟨s', hs'U, hs'⟩ := (_root_.GlobalTheory.HL.BlockStab.stabiliser_blockDiag L r k S).2 sb hsbU hsb0
  obtain ⟨h, hhSt, hhf, -⟩ :=
    ((_root_.GlobalTheory.HL.FrameStab.stab_eq L r k S).2 sb s' hsbU hs'U).mp hs'
  have hhR : _root_.GlobalTheory.HL.StabConj.Rep S.f h sb := hhf
  obtain ⟨B, hsbB, hBsb, hBU, -, hBβ⟩ := _root_.GlobalTheory.HL.BlockStab.inv_facts sb hsbU
  have hBoff : ∀ i j : Fin (r + 1), β i ≠ β j → B i j = 0 :=
    hoff B hBU (hBβ (fun i => β i) fun i j hij => hsb0 i j (hfalse i j hij.ne))
  have hu : _root_.GlobalTheory.HL.IsUni (B * s) := _root_.GlobalTheory.HL.FrameStabLat.uni_mul hBU hsU'
  have hublk : ∀ i j : Fin (r + 1), β i = β j →
      (B * s) i j = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) i j := by
    intro i j hij
    rw [← hBsb, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hil : β i = β l
    · rw [hsb]
      simp only [_root_.GlobalTheory.HL.StabConj.bd, (hsame l j).2 (hil.symm.trans hij), if_true]
    · rw [hBoff i l hil, zero_mul, zero_mul]
  have hnu : _root_.GlobalTheory.HL.StabConj.Rep S.f (h⁻¹ * n) (B * s) := by
    intro j
    show h⁻¹ (n (S.f j)) = _
    rw [hns j]
    exact rep_apply_sum_smul_eq_sum_mul_smul (rep_inv_of_mul_eq_one hhR hsbB) s j
  have hfli : LinearIndependent E S.f :=
    (_root_.GlobalTheory.FrameBasic.main L r k S).1.comp Sum.inl Sum.inl_injective
  obtain ⟨B', -, hB'u, hB'U, -, -⟩ := _root_.GlobalTheory.HL.BlockStab.inv_facts _ hu

  have key : ∀ g ∈ S.St ⊓ _root_.GlobalTheory.HL.stabL L
      (Submodule.span L.O (Set.range fun b => n (S.f b))),
      (h⁻¹ * g * h) • Submodule.span L.O (Set.range S.f) ≤
          Submodule.span L.O (Set.range S.f) ∧
        (h⁻¹ * g * h) • Submodule.span L.O (Set.range S.f') ≤
          Submodule.span L.O (Set.range S.f') := by
    intro g hg
    obtain ⟨hgSt, hgΛ⟩ := Subgroup.mem_inf.mp hg
    have hgΛ' : g • Submodule.span L.O (Set.range fun b => n (S.f b)) =
        Submodule.span L.O (Set.range fun b => n (S.f b)) := hgΛ
    have hg'St : h⁻¹ * g * h ∈ S.St :=
      mul_mem (mul_mem (inv_mem hhSt) hgSt) hhSt
    obtain ⟨t, htU, ht⟩ :=
      (_root_.GlobalTheory.HL.FrameOnto.unipotent_onto L r k S).1 _ (Subgroup.mem_inf.mp hg'St).1
    obtain ⟨t', ht'U, ht'⟩ :=
      (_root_.GlobalTheory.HL.FrameOnto.unipotent_onto L r k S).2.1 _ (Subgroup.mem_inf.mp hg'St).2
    have heq := ((_root_.GlobalTheory.HL.FrameStab.stab_eq L r k S).2 t t' htU
      ht'U).mpr ⟨_, hg'St, ht, ht'⟩
    obtain ⟨htblk, htint⟩ := (_root_.GlobalTheory.HL.BlockStab.stabiliser_blockDiag L r k S).1 t t' htU
      ht'U heq
    have htU' : _root_.GlobalTheory.HL.IsUni t := htU
    have htR : _root_.GlobalTheory.HL.StabConj.Rep S.f (h⁻¹ * g * h) t := ht
    have htoff : ∀ i j : Fin (r + 1), β i ≠ β j → t i j = 0 :=
      fun i j hij => (htblk i j (hfalse i j hij)).1

    have hcoef : ∀ j, ∃ c : Fin (r + 1) → L.O,
        ∑ i, c i • n (S.f i) = g (n (S.f j)) := by
      intro j
      have hmem : g • n (S.f j) ∈
          g • Submodule.span L.O (Set.range fun b => n (S.f b)) :=
        Submodule.smul_mem_pointwise_smul _ g _ (Submodule.subset_span ⟨j, rfl⟩)
      rw [hgΛ'] at hmem
      exact (Submodule.mem_span_range_iff_exists_fun L.O).mp hmem
    choose c hc using hcoef
    obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin (r + 1)) (Fin (r + 1)) E, C = fun i j => (c j i : E) :=
      ⟨_, rfl⟩
    have hhh : ∀ x, h (h⁻¹ x) = x := fun x => h.apply_symm_apply x
    have hlin : ∀ j, ∑ i, (t * (B * s)) i j • S.f i =
        ∑ i, ((B * s) * C) i j • S.f i := by
      intro j
      rw [← rep_apply_sum_smul_eq_sum_mul_smul htR, ← rep_apply_sum_smul_eq_sum_mul_smul hnu, ← hnu j]
      show h⁻¹ (g (h (h⁻¹ (n (S.f j))))) = h⁻¹ (n (∑ i, C i j • S.f i))
      rw [hhh, ← hc j]
      congr 1
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hC]
      rfl
    have htu := matrix_eq_of_linearIndependent_sum_smul_eq hfli hlin
    have hCeq : C = B' * (t * (B * s)) := by
      rw [htu, ← Matrix.mul_assoc, hB'u, Matrix.one_mul]
    have hCU : _root_.GlobalTheory.HL.IsUni C := by
      rw [hCeq]
      exact _root_.GlobalTheory.HL.FrameStabLat.uni_mul hB'U (_root_.GlobalTheory.HL.FrameStabLat.uni_mul htU' hu)
    have htO : _root_.GlobalTheory.HL.IsIntM L t := by
      unfold _root_.GlobalTheory.HL.IsIntM
      intro i j
      by_cases hij : β i = β j
      · have e1 : (t * (B * s)) i j = t i j := by
          rw [Matrix.mul_apply, Finset.sum_eq_single j]
          · rw [hublk j j rfl, Matrix.one_apply_eq, mul_one]
          · intro l _ hl
            by_cases hil : β i = β l
            · rw [hublk l j (hil.symm.trans hij), Matrix.one_apply_ne hl, mul_zero]
            · rw [htoff i l hil, zero_mul]
          · intro hj
            exact absurd (Finset.mem_univ j) hj
        have e2 : ((B * s) * C) i j = C i j := by
          rw [Matrix.mul_apply, Finset.sum_eq_single i]
          · rw [hublk i i rfl, Matrix.one_apply_eq, one_mul]
          · intro l _ hl
            rcases lt_trichotomy (β l) (β i) with h1 | h1 | h1
            · rw [hlower _ hu i l h1, zero_mul]
            · rw [hublk i l h1.symm, Matrix.one_apply_ne (Ne.symm hl), zero_mul]
            · rw [hlower _ hCU l j (hij ▸ h1), mul_zero]
          · intro hi
            exact absurd (Finset.mem_univ i) hi
        rw [← e1, htu, e2, hC]
        exact (c j i).2
      · rw [htoff i j hij]
        exact L.O.zero_mem
    exact ⟨smul_span_le_of_rep_entries_mem L htR htO, smul_span_le_of_rep_entries_mem L ht' (htint.mp htO)⟩
  have hconj : ∀ (g : S.GLV) (K : Subgroup S.GLV), g ∈ MulAut.conj h • K ↔ h⁻¹ * g * h ∈ K := by
    intro g K
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp
  have hstab : ∀ (x : S.GLV) (M : Submodule L.O S.V), x • M ≤ M → x⁻¹ • M ≤ M → x • M = M := by
    intro x M h1 h2
    refine le_antisymm h1 fun v hv => ?_
    have hv' : x⁻¹ • v ∈ M := h2 (Submodule.smul_mem_pointwise_smul v x⁻¹ M hv)
    simpa using Submodule.smul_mem_pointwise_smul _ x M hv'
  refine ⟨h, hhSt, fun g hg => ?_, B * s, hu, fun i j hij => ?_, hnu⟩
  · rw [hconj]
    have hg' : h⁻¹ * g * h ∈ S.St :=
      mul_mem (mul_mem (inv_mem hhSt) (Subgroup.mem_inf.mp hg).1) hhSt
    obtain ⟨h1, h2⟩ := key g hg
    obtain ⟨h3, h4⟩ := key g⁻¹ (inv_mem hg)
    have hinv : h⁻¹ * g⁻¹ * h = (h⁻¹ * g * h)⁻¹ := by group
    rw [hinv] at h3 h4
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hg', hstab _ _ h1 h3⟩, hstab _ _ h2 h4⟩
  · rw [hublk i j ((hsame i j).1 hij), Matrix.one_apply]
    split_ifs
    · exact L.O.one_mem
    · exact L.O.zero_mem
end _root_.GlobalTheory.HL.StabConj
end GlobalTheory.HL.StabConj
