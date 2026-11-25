-- Prove2me | solution 1 for GlobalTheory.HL.CompLat.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:42:15.230571+00:00
-- url     : https://prove2.me/submissions/080e9cad-b7b7-4625-bfbc-686e57897ef8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsBasisFgMaximalOrderSpanningFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ComplementLatticeOfTermFreeRank
import Theorems.Thm_GlobalTheory_HL_CompLat_exists_mul_mem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_HL_StdLat_exists_mul_mem
import Theorems.Thm_GlobalTheory_HL_StdLat_stdLat_spec
import Theorems.Thm_GlobalTheory_HL_TermBasic_inner_smul
import Theorems.Thm_GlobalTheory_HL_TermBasic_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_TermBasic_term_basic
import Theorems.Thm_GlobalTheory_OrderBasis_order_basis
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
import Theorems.Thm_GlobalTheory_UnramOrder_exists_eq_add_mul
import Theorems.Thm_GlobalTheory_UnramOrder_exists_int_of_fixed
import Theorems.Thm_GlobalTheory_UnramOrder_exists_sub_cj_mul_eq_one
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
namespace GlobalTheory.HL.CompLat
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable [IsNonarchimedeanLocalField F] [CharZero F] in
private theorem exists_integral_smul_mem_of_span_eq_whole (Λ : Submodule L.O S.V)
    (hU : Submodule.span E (Λ : Set S.V) = ⊤) (w : S.V) :
    ∃ c : F, c ≠ 0 ∧ c ∈ (ValuativeRel.valuation F).integer ∧ algebraMap F E c • w ∈ Λ := by
  have hw : w ∈ Submodule.span E (Λ : Set S.V) := hU ▸ Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, Subring.one_mem _, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, Subring.one_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, hcO, hcx⟩ := hx
    obtain ⟨c', hc', hc'O, hcy⟩ := hy
    have h1 := (_root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L c).2 hcO
    have h2 := (_root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L c').2 hc'O
    refine ⟨c * c', mul_ne_zero hc hc', Subring.mul_mem _ hcO hc'O, ?_⟩
    have := Λ.add_mem (Λ.smul_mem (⟨_, h2⟩ : L.O) hcx) (Λ.smul_mem (⟨_, h1⟩ : L.O) hcy)
    convert this using 1
    change algebraMap F E (c * c') • (x + y) =
      algebraMap F E c' • algebraMap F E c • x + algebraMap F E c • algebraMap F E c' • y
    rw [map_mul]
    module
  | smul e x _ hx =>
    obtain ⟨c, hc, hcO, hcx⟩ := hx
    obtain ⟨c', hc', hc'O, he⟩ := _root_.GlobalTheory.HL.StdLat.exists_mul_mem L {e}
    have he' := he e (Finset.mem_singleton_self e)
    refine ⟨c' * c, mul_ne_zero hc' hc, Subring.mul_mem _ hc'O hcO, ?_⟩
    have := Λ.smul_mem (⟨_, he'⟩ : L.O) hcx
    convert this using 1
    change algebraMap F E (c' * c) • e • x = (algebraMap F E c' * e) • algebraMap F E c • x
    rw [map_mul]
    module
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable [IsNonarchimedeanLocalField F] [CharZero F] in
private theorem mem_complementLattice_and_tauRel_of_isTerm (d : S.Datum)
    (Λ : Submodule L.O S.V) (hT : S.IsTerm d Λ) (w : S.V)
    (hw : w ∈ S.W0) (hΛ : w ∈ Λ) :
    w ∈ S.complementLatticeOfDatum d ∧ S.TauRel d Λ w 0 := by
  obtain ⟨⟨n, n'⟩, hA, hA', hn, hn', hΛn, hΛn', -, hgr⟩ := hT
  have hME : ∀ x ∈ S.ME, S.h w x = 0 := hw
  have hXo : w ∈ _root_.GlobalTheory.HL.perp L S.Hm S.X := fun x hx =>
    hME x (le_sup_of_le_left (_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f (Nat.le_succ r)) hx)
  have hXo' : w ∈ _root_.GlobalTheory.HL.perp L S.Hm S.X' := fun x hx =>
    hME x (le_sup_of_le_right (_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f' (Nat.le_succ r)) hx)
  refine ⟨⟨hw, ?_, ?_, ?_⟩, ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, by simpa using hΛ,
    by simpa using hΛ, ⟨0, Λ.zero_mem, by simp⟩, by simpa using Submodule.zero_mem _⟩⟩
  · refine ((_root_.GlobalTheory.HL.StdLat.stdLat_spec L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩) _ hA).2.2 w).2 ?_
    refine (_root_.GlobalTheory.HL.TermBasic.inner_smul S hn w).2 ⟨w, ?_, hXo, by simpa using Submodule.zero_mem _⟩
    rw [← hΛn]; exact hΛ
  · refine ((_root_.GlobalTheory.HL.StdLat.stdLat_spec L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) _ hA').2.2 w).2 ?_
    refine (_root_.GlobalTheory.HL.TermBasic.inner_smul S hn' w).2 ⟨w, ?_, hXo', by simpa using Submodule.zero_mem _⟩
    rw [← hΛn']; exact hΛ
  · rw [hgr]
    exact ⟨w, hΛ, w, hΛ, hXo', hXo, by simpa using Submodule.zero_mem _,
      by simpa using Submodule.zero_mem _, 0, Λ.zero_mem, by simp⟩
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
variable [IsNonarchimedeanLocalField F] [CharZero F] in
private theorem isNoetherianRing_locE_O (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) : IsNoetherianRing L.O := by
  obtain ⟨ω, hω, e, he, hωe⟩ := _root_.GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  let φ : (ValuativeRel.valuation F).integer →+* L.O :=
    ((algebraMap F E).comp (ValuativeRel.valuation F).integer.subtype).codRestrict L.O
      (fun c => (_root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L c).2 c.2)
  letI : Algebra (ValuativeRel.valuation F).integer L.O := φ.toAlgebra
  let σ : L.O →+* L.O := ((L.cj : E →+* E).comp L.O.subtype).codRestrict L.O
    (fun x => _root_.GlobalTheory.UnramOrder.cj_mem L x.2)
  have key := _root_.GlobalTheory.UnramOrder.exists_eq_add_mul (R₀ := (ValuativeRel.valuation F).integer) σ
    (fun x => Subtype.ext (L.cj_cj x)) (fun c => Subtype.ext (L.cj.commutes _))
    (fun x hx => by
      obtain ⟨c, hc⟩ := _root_.GlobalTheory.UnramOrder.exists_int_of_fixed L x.2 (congrArg Subtype.val hx)
      exact ⟨c, Subtype.ext hc.symm⟩)
    (ω := ⟨ω, hω⟩) (isUnit_iff_exists_inv.2 ⟨⟨e, he⟩, Subtype.ext hωe⟩)
  haveI : Module.Finite (ValuativeRel.valuation F).integer L.O := by
    refine ⟨⟨{1, ⟨ω, hω⟩}, ?_⟩⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, b, rfl⟩ := key x
    refine Submodule.add_mem _ ?_ ?_
    · rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  exact IsNoetherianRing.of_finite (ValuativeRel.valuation F).integer L.O
end GlobalTheory.HL.CompLat
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CompLat
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k)
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.HL.CompLat
namespace _root_.GlobalTheory.HL.CompLat
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∃ b : Fin (k - 1) → S.V, LinearIndependent E b ∧ S.complementLatticeOfDatum d = (Submodule.span L.O (Set.range b) : Set S.V) := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT
  obtain ⟨-, -, -, -, -, -, -, b, hb, hW⟩ := _root_.GlobalTheory.FrameBasic.main L r k S
  have hsd := (_root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).1
  have hgr : d.2.2 = S.graphOf Λ := by
    obtain ⟨_, -, -, -, -, -, -, -, h⟩ := hT
    exact h
  let Q : Submodule L.O S.V := S.W0.restrictScalars L.O ⊓ d.1 ⊓
    d.2.1 ⊓ _root_.GlobalTheory.HL.CompLat.diagGraph S Λ
  have hQ : (Q : Set S.V) = S.complementLatticeOfDatum d := by
    ext w
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      refine ⟨h1, h2, h3, ?_⟩
      rw [hgr]
      exact h4
    · rintro ⟨h1, h2, h3, h4⟩
      rw [hgr] at h4
      exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  have hspan : Submodule.span E (Q : Set S.V) = Submodule.span E (Set.range b) := by
    rw [← hW]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro w ⟨⟨⟨h1, -⟩, -⟩, -⟩
      exact h1
    · intro w hw
      obtain ⟨c, hc, -, hcw⟩ := exists_integral_smul_mem_of_span_eq_whole S Λ hsd.1.2 w
      have hq : algebraMap F E c • w ∈ (Q : Set S.V) := by
        rw [hQ]
        exact (mem_complementLattice_and_tauRel_of_isTerm S d Λ hT _
          (S.W0.smul_mem _ hw) hcw).1
      have h1 : w = algebraMap F E c⁻¹ • algebraMap F E c • w := by
        rw [smul_smul, ← map_mul, inv_mul_cancel₀ hc, map_one, one_smul]
      rw [h1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hq)
  have hFG : Q.FG := by
    haveI := isNoetherianRing_locE_O L
    obtain ⟨-, hcompl, -⟩ := _root_.GlobalTheory.FrameBasic.main L r k S
    let π : S.V →ₗ[L.O] S.V :=
      (S.W0.subtype.comp
        (Submodule.linearProjOfIsCompl S.W0 S.ME hcompl.symm)).restrictScalars L.O
    refine Submodule.FG.of_le (hsd.1.1.map π) ?_
    rintro w ⟨⟨⟨h1, -⟩, -⟩, h4⟩
    obtain ⟨-, -, y, hy, -, -, -, hx, -⟩ := h4
    have hXME : y - w ∈ S.ME :=
      le_sup_of_le_left (_root_.GlobalTheory.HL.TermBasic.spanTo_mono S S.f (Nat.le_succ r)) hx
    refine ⟨y, hy, ?_⟩
    have hy' : y = w + (y - w) := by abel
    change ((Submodule.linearProjOfIsCompl S.W0 S.ME hcompl.symm y : S.V)) = w
    have e1 := Submodule.linearProjOfIsCompl_apply_left hcompl.symm ⟨w, h1⟩
    have e2 := Submodule.linearProjOfIsCompl_apply_right hcompl.symm ⟨y - w, hXME⟩
    rw [hy', map_add]
    erw [e1, e2]
    simp
  obtain ⟨b', hb', hQb⟩ := _root_.GlobalTheory.OrderBasis.order_basis L b hb Q hFG hspan
  exact ⟨b', hb', by rw [← hQ, hQb]⟩
end _root_.GlobalTheory.HL.CompLat
end GlobalTheory.HL.CompLat
