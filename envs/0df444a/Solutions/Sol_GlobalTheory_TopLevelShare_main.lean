-- Prove2me | solution 1 for GlobalTheory.TopLevelShare.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:01:29.886683+00:00
-- url     : https://prove2.me/submissions/08516166-94db-4d00-9f80-1a76dd31d0a3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralEqOfFineSubgroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexIntegrableShareTopLevelVectors
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_FrameLevel_main
import Theorems.Thm_GlobalTheory_HL_Defect_exponents_and_defect
import Theorems.Thm_GlobalTheory_HL_FrameOnto_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_TermBasic_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_TermBasic_sub_mem
import Theorems.Thm_GlobalTheory_HL_TermBasic_term_basic
import Theorems.Thm_GlobalTheory_IdxInt_cint_eq_of_fine
import Theorems.Thm_GlobalTheory_LengthDualFunctional_main
import Theorems.Thm_GlobalTheory_LengthQuotientSpanValuation_main
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.TopLevelShare
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.TopLevelShare
namespace _root_.GlobalTheory.TopLevelShare
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → 1 ≤ βJ ∧ 1 ≤ β ∧ _root_.GlobalTheory.IdxInt.Nice (S.refB (j + 1) Λ) (_root_.GlobalTheory.IdxInt.ind fun b : S.V × S.V => b ∈ S.refB (j + 1) Λ ∧ S.lev (S.fr d Λ) (S.fr' d Λ) (b.1 + b.2) = j + 1) ∧ _root_.GlobalTheory.IdxInt.cint (S.refB (j + 1) Λ) (_root_.GlobalTheory.IdxInt.ind fun b : S.V × S.V => b ∈ S.refB (j + 1) Λ ∧ S.lev (S.fr d Λ) (S.fr' d Λ) (b.1 + b.2) = j + 1) = (βJ : ℂ) / (β : ℂ) := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF
  obtain ⟨-, hbe, hle, ⟨y₀, hy₀, hy₀l⟩, hJ⟩ := hF
  obtain ⟨-, -, hMsat, -⟩ := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, -, -, -, ⟨i, -, hq⟩, -, -, -, -, hlev⟩ := _root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT
  have hth : S.th ≠ 0 := (_root_.GlobalTheory.FrameBasic.main L r k S).2.2.2.2.2.1
  set A := S.refB (↑j + 1) Λ with hAdef
  have hA : ∀ b : S.V × S.V, b ∈ A ↔ b.1 ∈ S.spanTo S.f (↑j + 1) ∧ b.2 ∈ S.spanTo S.f' (↑j + 1) ∧ ∃ y ∈ Λ, S.th • y = b.1 + b.2 := by
    intro b
    simp [hAdef, _root_.GlobalTheory.HL.Frames.refB, AddSubgroup.mem_prod, and_assoc]
  have hlevC : ∀ y, S.levC d Λ y = S.lev (S.fr d Λ) (S.fr' d Λ) (S.th • y) := by
    intro y
    simp [_root_.GlobalTheory.HL.Frames.levC]
  have hsat : ∀ y, y ∈ S.sat Λ ↔ y ∈ Λ ∧ y ∈ S.spanTo S.f (r + 1) ⊔ S.spanTo S.f' (r + 1) := by
    intro y
    show y ∈ Λ ⊓ S.ME.restrictScalars L.O ↔ _
    rw [Submodule.mem_inf, Submodule.restrictScalars_mem]
    rfl
  have hbe' : S.be d Λ = (S.M d Λ).toAddSubgroup.relIndex (S.sat Λ).toAddSubgroup := rfl
  have hq0 : S.q ≠ 0 := by
    have hirr := S.ϖ_irr
    show _root_.GlobalTheory.HL.resQ S.ϖ ≠ 0
    unfold _root_.GlobalTheory.HL.resQ
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr]
    exact (Nat.card_pos (α := IsLocalRing.ResidueField (ValuativeRel.valuation F).integer)).ne'
  have hβ0 : β ≠ 0 := by rw [← hbe, hq]; exact pow_ne_zero _ hq0
  set π : S.V × S.V → S.V := fun b => S.th⁻¹ • (b.1 + b.2) with hπdef
  have hπsmul : ∀ b, S.th • π b = b.1 + b.2 := fun b => smul_inv_smul₀ hth _
  have hπadd : ∀ a b, π (a + b) = π a + π b := by
    intro a b
    simp only [hπdef, Prod.fst_add, Prod.snd_add, ← smul_add, add_add_add_comm]
  have hπsub : ∀ a b, π (a - b) = π a - π b := by
    intro a b
    simp only [hπdef, Prod.fst_sub, Prod.snd_sub, ← smul_sub, sub_add_sub_comm]
  have hπA : ∀ b ∈ A, π b ∈ S.sat Λ := by
    intro b hb
    obtain ⟨h1, h2, y, hy, hyb⟩ := (hA b).1 hb
    have hjr : (↑j + 1 : ℕ) ≤ r + 1 := by omega
    rw [hsat]
    refine ⟨?_, ?_⟩
    · rw [hπdef]; dsimp only; rw [← hyb, inv_smul_smul₀ hth]; exact hy
    · refine Submodule.smul_of_tower_mem _ _ (add_mem ?_ ?_)
      · exact Submodule.mem_sup_left (_root_.GlobalTheory.HL.FrameOnto.spanTo_mono S S.f hjr h1)
      · exact Submodule.mem_sup_right (_root_.GlobalTheory.HL.FrameOnto.spanTo_mono S S.f' hjr h2)
  have hlevπ : ∀ b : S.V × S.V, S.lev (S.fr d Λ) (S.fr' d Λ) (b.1 + b.2) = S.levC d Λ (π b) := by
    intro b; rw [hlevC, hπsmul]
  have hinv : ∀ y ∈ S.sat Λ, ∀ m ∈ S.M d Λ, S.levC d Λ (y + m) = S.levC d Λ y := by
    intro y hy m hm
    have key : ∀ n : ℕ, S.levC d Λ (y + m) ≤ n ↔ S.levC d Λ y ≤ n := by
      intro n
      rw [hlev _ (add_mem hy (hMsat hm)), hlev _ hy]
      constructor
      · rintro ⟨y₁, h₁, h₂⟩
        exact ⟨y₁, h₁, by simpa [add_sub_right_comm] using sub_mem h₂ hm⟩
      · rintro ⟨y₁, h₁, h₂⟩
        exact ⟨y₁, h₁, by simpa [add_sub_right_comm] using add_mem h₂ hm⟩
    exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)
  set B : AddSubgroup (S.V × S.V) := A ⊓ AddSubgroup.comap (AddMonoidHom.fst S.V S.V + AddMonoidHom.snd S.V S.V) ((S.M d Λ).toAddSubgroup.map (DistribMulAction.toAddMonoidHom S.V S.th)) with hBdef
  have hB : ∀ b, b ∈ B ↔ b ∈ A ∧ π b ∈ S.M d Λ := by
    intro b
    rw [hBdef, AddSubgroup.mem_inf]
    refine and_congr_right fun _ => ?_
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_map, AddMonoidHom.add_apply, AddMonoidHom.coe_fst, AddMonoidHom.coe_snd, DistribMulAction.toAddMonoidHom_apply, Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨m, hm, hmb⟩
      rw [hπdef]; dsimp only; rw [← hmb, inv_smul_smul₀ hth]; exact hm
    · intro h
      exact ⟨π b, h, hπsmul b⟩
  have hsatΛ : ∀ y ∈ S.sat Λ, y ∈ Λ := fun y hy => ((hsat y).1 hy).1
  have hlift : ∀ y ∈ S.sat Λ, ∃ b ∈ A, y - π b ∈ S.M d Λ := by
    intro y hy
    obtain ⟨y₁, hy₁U, hyM⟩ := (hlev y hy (↑j + 1)).1 (hle y hy)
    have hy₁Λ : y₁ ∈ Λ := by simpa using sub_mem (hsatΛ y hy) (hsatΛ _ (hMsat hyM))
    obtain ⟨u₁, hu₁, u₂, hu₂, hu⟩ := Submodule.mem_sup.1 (Submodule.smul_of_tower_mem _ S.th hy₁U)
    refine ⟨(u₁, u₂), (hA _).2 ⟨hu₁, hu₂, y₁, hy₁Λ, hu.symm⟩, ?_⟩
    have : π (u₁, u₂) = y₁ := by
      rw [hπdef]; dsimp only; rw [hu, inv_smul_smul₀ hth]
    rw [this]; exact hyM
  set K := (S.M d Λ).toAddSubgroup.addSubgroupOf (S.sat Λ).toAddSubgroup with hKdef
  let πA : A →+ (S.sat Λ).toAddSubgroup :=
    { toFun := fun b => ⟨π b, hπA b b.2⟩
      map_zero' := Subtype.ext (by simp [hπdef])
      map_add' := fun a b => Subtype.ext (hπadd a b) }
  let g : A →+ (S.sat Λ).toAddSubgroup ⧸ K := (QuotientAddGroup.mk' K).comp πA
  have hg : ∀ a : A, g a = QuotientAddGroup.mk (⟨π a, hπA a a.2⟩ : (S.sat Λ).toAddSubgroup) := fun a => rfl
  have hsurj : Function.Surjective g := by
    intro c
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨b, hb, hbM⟩ := hlift y hy
    refine ⟨⟨b, hb⟩, ?_⟩
    rw [hg, QuotientAddGroup.eq, hKdef, AddSubgroup.mem_addSubgroupOf]
    simpa [neg_add_eq_sub] using hbM
  have hker : g.ker = B.addSubgroupOf A := by
    ext a
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, hB, hg, QuotientAddGroup.eq_zero_iff, hKdef, AddSubgroup.mem_addSubgroupOf]
    simp
  have hidx : B.relIndex A = β := by
    rw [← hbe, hbe', AddSubgroup.relIndex, AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, AddSubgroup.card_top]
    rfl
  have hidx0 : B.relIndex A ≠ 0 := by rw [hidx]; exact hβ0
  haveI : Finite (A ⧸ B.addSubgroupOf A) := Nat.finite_of_card_ne_zero hidx0
  set φ := _root_.GlobalTheory.IdxInt.ind (fun b : S.V × S.V => b ∈ A ∧ S.lev (S.fr d Λ) (S.fr' d Λ) (b.1 + b.2) = ↑j + 1) with hφdef
  have hφval : ∀ w, φ w = if w ∈ A ∧ S.lev (S.fr d Λ) (S.fr' d Λ) (w.1 + w.2) = ↑j + 1 then 1 else 0 := by
    intro w
    rw [hφdef]
    unfold _root_.GlobalTheory.IdxInt.ind
    congr
  have hφinv : ∀ w b : S.V × S.V, b ∈ B → φ (w + b) = φ w := by
    intro w b hb
    obtain ⟨hbA, hbM⟩ := (hB b).1 hb
    have key : (w + b ∈ A ∧ S.lev (S.fr d Λ) (S.fr' d Λ) ((w + b).1 + (w + b).2) = ↑j + 1) ↔ (w ∈ A ∧ S.lev (S.fr d Λ) (S.fr' d Λ) (w.1 + w.2) = ↑j + 1) := by
      by_cases hw : w ∈ A
      · rw [hlevπ, hlevπ, hπadd, hinv _ (hπA w hw) _ hbM]
        simp [hw, add_mem hw hbA]
      · have hwb : w + b ∉ A := fun h => hw (by simpa using sub_mem h hbA)
        simp [hw, hwb]
    simp only [hφval, key]
  have hsupp : Function.support φ ⊆ A := by
    intro w hw
    by_contra h
    exact hw (by rw [hφval, if_neg (fun hc => h hc.1)])
  have hfin : ((fun w : S.V × S.V => (w : (S.V × S.V) ⧸ B)) '' Function.support φ).Finite := by
    let h : A ⧸ B.addSubgroupOf A →+ (S.V × S.V) ⧸ B := QuotientAddGroup.map (B.addSubgroupOf A) B A.subtype (fun x hx => hx)
    refine (Set.finite_range h).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨QuotientAddGroup.mk ⟨w, hsupp hw⟩, rfl⟩
  have hfine : _root_.GlobalTheory.IdxInt.Fine A φ B := ⟨inf_le_left, hidx0, hφinv, hfin⟩
  set T : Set ((S.V × S.V) ⧸ B) := {c | Quotient.out c ∈ A ∧ S.lev (S.fr d Λ) (S.fr' d Λ) ((Quotient.out c).1 + (Quotient.out c).2) = ↑j + 1} with hTdef
  have hTsub : T ⊆ (fun w : S.V × S.V => (w : (S.V × S.V) ⧸ B)) '' Function.support φ := by
    intro c hc
    refine ⟨Quotient.out c, ?_, QuotientAddGroup.out_eq' c⟩
    simp [Function.mem_support, hφval, hc.1, hc.2]
  have hTfin : T.Finite := hfin.subset hTsub
  have hsum : ∑ᶠ c : (S.V × S.V) ⧸ B, φ (Quotient.out c) = (T.ncard : ℂ) := by
    calc ∑ᶠ c : (S.V × S.V) ⧸ B, φ (Quotient.out c) = ∑ᶠ c ∈ T, (1 : ℂ) := by
          rw [finsum_mem_def]
          refine finsum_congr fun c => ?_
          simp only [hφval, Set.indicator, hTdef, Set.mem_setOf_eq]
      _ = T.ncard := by
          rw [finsum_mem_eq_finite_toFinset_sum _ hTfin, Finset.sum_const, nsmul_eq_mul, mul_one, Set.ncard_eq_toFinset_card T hTfin]
  have hout : ∀ b : S.V × S.V, Quotient.out (b : (S.V × S.V) ⧸ B) - b ∈ B := by
    intro b
    have h := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (b : (S.V × S.V) ⧸ B))
    rw [neg_add_eq_sub, ← neg_sub] at h
    simpa using B.neg_mem h
  set fC : (S.V × S.V) ⧸ B → Set S.V := fun c => {x | x - π (Quotient.out c) ∈ S.M d Λ} with hfCdef
  have himage : fC '' T = {C | ∃ y ∈ S.sat Λ, S.levC d Λ y = ↑j + 1 ∧ C = {x | x - y ∈ S.M d Λ}} := by
    ext C
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨π (Quotient.out c), hπA _ hc.1, (hlevπ _).symm.trans hc.2, rfl⟩
    · rintro ⟨y, hy, hyl, rfl⟩
      obtain ⟨b, hb, hbM⟩ := hlift y hy
      obtain ⟨h₁, h₂⟩ := (hB _).1 (hout b)
      have hoA : Quotient.out (b : (S.V × S.V) ⧸ B) ∈ A := by simpa using add_mem h₁ hb
      rw [hπsub] at h₂
      have hyo : y - π (Quotient.out (b : (S.V × S.V) ⧸ B)) ∈ S.M d Λ := by
        have := sub_mem hbM h₂
        rwa [sub_sub_sub_cancel_right] at this
      refine ⟨(b : (S.V × S.V) ⧸ B), ⟨hoA, ?_⟩, ?_⟩
      · have := hinv _ (hπA _ hoA) _ hyo
        rw [add_sub_cancel] at this
        rw [hlevπ, ← this, hyl]
      · ext x
        simp only [hfCdef, Set.mem_setOf_eq]
        constructor
        · intro hx
          have := sub_mem hx hyo
          rwa [sub_sub_sub_cancel_right] at this
        · intro hx
          have := add_mem hx hyo
          rwa [sub_add_sub_cancel] at this
  have hinj : Set.InjOn fC T := by
    intro c₁ hc₁ c₂ hc₂ heq
    have hmem : π (Quotient.out c₁) ∈ fC c₁ := by
      show π (Quotient.out c₁) - π (Quotient.out c₁) ∈ S.M d Λ
      rw [sub_self]; exact zero_mem _
    rw [heq] at hmem
    have hB₁₂ : Quotient.out c₁ - Quotient.out c₂ ∈ B :=
      (hB _).2 ⟨sub_mem hc₁.1 hc₂.1, by rw [hπsub]; exact hmem⟩
    rw [← QuotientAddGroup.out_eq' c₁, ← QuotientAddGroup.out_eq' c₂, QuotientAddGroup.eq, neg_add_eq_sub, ← neg_sub]
    exact B.neg_mem hB₁₂
  have hcount : T.ncard = βJ := by
    rw [← hJ]
    unfold _root_.GlobalTheory.HL.Frames.nLev
    rw [← himage, Set.ncard_image_of_injOn hinj]
  have hTne : T.Nonempty := by
    have : (fC '' T).Nonempty := by
      rw [himage]; exact ⟨_, y₀, hy₀, hy₀l, rfl⟩
    exact Set.image_nonempty.1 this
  refine ⟨?_, Nat.one_le_iff_ne_zero.2 hβ0, ⟨B, hfine⟩, ?_⟩
  · rw [← hcount]
    exact (Set.ncard_pos hTfin).2 hTne
  · rw [_root_.GlobalTheory.IdxInt.cint_eq_of_fine A B φ hfine, hsum, hcount, hidx]
end _root_.GlobalTheory.TopLevelShare
end GlobalTheory.TopLevelShare
