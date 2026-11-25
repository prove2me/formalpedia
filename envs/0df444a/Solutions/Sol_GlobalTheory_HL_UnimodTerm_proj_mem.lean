-- Prove2me | solution 1 for GlobalTheory.HL.UnimodTerm.proj_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:57:37.573973+00:00
-- url     : https://prove2.me/submissions/7bfc03b9-7481-46e4-acd4-40251f0275ea

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeGramDetAndMinorsOrbitInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegralOfMulVec
import Theorems.Thm_GlobalTheory_HL_UnimodTerm_hf_sum_left
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_FrameBasic_mem_perp_span
import Theorems.Thm_GlobalTheory_FrameGram_hf_sum_left
import Theorems.Thm_GlobalTheory_FrameGram_main
import Theorems.Thm_GlobalTheory_HL_FrameClass_smul_mem
import Theorems.Thm_GlobalTheory_HL_FrameTri_hf_sum_left
import Theorems.Thm_GlobalTheory_HL_StdLat_mem_perp_span
import Theorems.Thm_GlobalTheory_HL_TermBasic_term_basic
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_UnramVal_exists_eq_zpow_mul_unit
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
namespace GlobalTheory.HL.UnimodTerm
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
omit [IsNonarchimedeanLocalField F] [CharZero F] in
private lemma hf_Hm_sub_left (x m y : S.V) :
    _root_.GlobalTheory.HL.hf L S.Hm (x - m) y =
      _root_.GlobalTheory.HL.hf L S.Hm x y -
        _root_.GlobalTheory.HL.hf L S.Hm m y := by
  simp only [_root_.GlobalTheory.HL.hf, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
end GlobalTheory.HL.UnimodTerm
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.UnimodTerm
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k)
namespace GlobalTheory.HL.UnimodTerm
namespace _root_.GlobalTheory.HL.UnimodTerm
theorem _root_.solution {d : S.Datum}
    {Λ : Submodule L.O S.V} (hT : S.IsTerm d Λ) (ha : S.a = 0)
    {x m : S.V} (hx : x ∈ Λ) (hm : m ∈ S.ME)
    (hw : x - m ∈ S.W0) : m ∈ S.M d Λ := by
  obtain ⟨hsd, hW, -, hfr, -, -, -, -⟩ := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, hp, hq, -, -, hth, -⟩ := hW
  obtain ⟨-, -, -, -, -, hth0, -, -⟩ := _root_.GlobalTheory.FrameBasic.main L r k S
  obtain ⟨⟨c, hc0, hcv, hdet⟩, -, hspan⟩ :=
    _root_.GlobalTheory.FrameGram.main L r k S _ hp _ hq
  set p := (S.wit d Λ).1
  set q := (S.wit d Λ).2
  set e : Fin (r + 1) ⊕ Fin (r + 1) → S.V := Sum.elim (fun i => p (S.f i))
    (fun i => algebraMap F E S.th⁻¹ • (q (S.f' i) - p (S.f i))) with he_def

  obtain ⟨k', u, rfl⟩ := _root_.GlobalTheory.UnramVal.exists_eq_zpow_mul_unit S.ϖ_irr hc0
  rw [_root_.GlobalTheory.UnramVal.vE_zpow_mul_unit L S.ϖ_irr, ha] at hcv
  subst hcv
  simp only [zpow_zero, one_mul] at hdet
  have hu : algebraMap F E (u : F) ∈ L.O :=
    (_root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L _).mpr (u : (ValuativeRel.valuation F).integer).2
  have hu' : algebraMap F E ((u⁻¹ : (ValuativeRel.valuation F).integer ˣ) : F) ∈ L.O :=
    (_root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L _).mpr ((u⁻¹ : (ValuativeRel.valuation F).integer ˣ) : (ValuativeRel.valuation F).integer).2
  have huu : algebraMap F E ((u⁻¹ : (ValuativeRel.valuation F).integer ˣ) : F) * algebraMap F E (u : F) = 1 := by
    rw [← map_mul, ← Subring.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Subring.coe_one, map_one]

  have he : ∀ a, e a ∈ Λ := by
    rintro (i | i)
    · exact ((hfr (r + 1) le_rfl (p (S.f i))).mpr (Submodule.subset_span ⟨i, i.isLt, rfl⟩)).1
    · obtain ⟨y, hy, hxy⟩ := hth i
      simp only [he_def, Sum.elim_inr]
      rw [hxy, smul_smul, ← map_mul, inv_mul_cancel₀ hth0, map_one, one_smul]
      exact hy
  have hG : ∀ a b, _root_.GlobalTheory.HL.hf L S.Hm (e b) (e a) ∈ L.O :=
    fun a b => (hsd.2 (e a)).mpr (he a) (e b) (he b)

  rw [← hspan] at hm
  unfold _root_.GlobalTheory.HL.Frames.W0 at hw
  rw [← hspan] at hw
  obtain ⟨μ, hμ⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hm
  rw [_root_.GlobalTheory.HL.StdLat.mem_perp_span] at hw
  set G : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
    Matrix.of fun a b => _root_.GlobalTheory.HL.hf L S.Hm (e b) (e a) with hG_def
  set v : Fin (r + 1) ⊕ Fin (r + 1) → E := fun a => _root_.GlobalTheory.HL.hf L S.Hm x (e a)
  have hGμ : G.mulVec μ = v := by
    funext a
    have h1 := hw a
    rw [hf_Hm_sub_left, sub_eq_zero, ← hμ,
      _root_.GlobalTheory.HL.UnimodTerm.hf_sum_left] at h1
    simp only [Matrix.mulVec, dotProduct, hG_def, Matrix.of_apply, v, h1]
  have hdetG : G.det = algebraMap F E (u : F) := hdet
  have hadj : G.det • μ = G.adjugate.mulVec v := by
    rw [← hGμ, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  set GO : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) L.O := fun a b => ⟨G a b, hG a b⟩
  have hGO : L.O.subtype.mapMatrix GO = G := by
    ext a b
    rfl
  have hadjO : ∀ a b, G.adjugate a b ∈ L.O := by
    intro a b
    rw [← hGO, ← RingHom.map_adjugate]
    exact (GO.adjugate a b).2
  have hvO : ∀ a, v a ∈ L.O := fun a => (hsd.2 (e a)).mpr (he a) x hx
  have hμO : ∀ b, μ b ∈ L.O := by
    intro b
    have h2 := congrFun hadj b
    simp only [Pi.smul_apply, smul_eq_mul, hdetG] at h2
    have h3 : μ b = algebraMap F E ((u⁻¹ : (ValuativeRel.valuation F).integer ˣ) : F) * (G.adjugate.mulVec v) b := by
      rw [← h2, ← mul_assoc, huu, one_mul]
    rw [h3]
    refine L.O.mul_mem hu' ?_
    simp only [Matrix.mulVec, dotProduct]
    exact L.O.sum_mem fun a _ => L.O.mul_mem (hadjO b a) (hvO a)

  rw [← hμ]
  refine Submodule.sum_mem _ fun b _ => ?_
  have hmem : e b ∈ S.M d Λ := by
    apply Submodule.subset_span
    rcases b with i | i
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨i, rfl⟩
  exact Submodule.smul_mem _ (⟨μ b, hμO b⟩ : L.O) hmem
end _root_.GlobalTheory.HL.UnimodTerm
end GlobalTheory.HL.UnimodTerm
