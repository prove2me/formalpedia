-- Prove2me | solution 1 for GlobalTheory.HL.UniCount.encard_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:39:08.376583+00:00
-- url     : https://prove2.me/submissions/2c344c49-52b2-4a3e-8f19-cdf21bae3a38

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardQuotEqPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUniCosetsLe
import Theorems.Thm_GlobalTheory_HL_UniCount_exists_rep
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.UniCount
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {N : ℕ}
namespace GlobalTheory.HL.UniCount
theorem _root_.solution (L : LocE F E) (δ : L.O) (hδ : IsUnit (δ : E))
    [Finite (L.O ⧸ Ideal.span {δ})] (N : ℕ) :
    {C : Set (Matrix (Fin N) (Fin N) E) | ∃ u, IsUni u ∧ (∀ i j, (δ : E) * u i j ∈ L.O) ∧
      C = cos L u}.encard ≤
      ((Nat.card (L.O ⧸ Ideal.span {δ}) ^ (N * (N - 1) / 2) : ℕ) : ℕ∞) := by
  obtain ⟨d, hd⟩ := hδ
  let ρ : (L.O ⧸ Ideal.span {δ}) → E := fun q => (d⁻¹ : Eˣ) * (Quotient.out q : L.O)
  have hR : ∀ x : E, (δ : E) * x ∈ L.O → ∃ r ∈ Set.range ρ, r - x ∈ L.O := by
    intro x hx
    let y : L.O := ⟨_, hx⟩
    refine ⟨_, ⟨Ideal.Quotient.mk _ y, rfl⟩, ?_⟩
    have h1 : Quotient.out (Ideal.Quotient.mk (Ideal.span {δ}) y) - y ∈ Ideal.span {δ} :=
      Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out _)
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
    have h2 : ((Quotient.out (Ideal.Quotient.mk (Ideal.span {δ}) y) : L.O) : E)
        = (a : E) * d + d * x := by
      have := congrArg (Subtype.val) ha
      push_cast at this
      rw [hd, this]
      simp [y]
    have h3 : ρ (Ideal.Quotient.mk _ y) - x = a := by
      simp only [ρ]
      rw [h2]
      have := d.inv_mul
      linear_combination ((a : E) + x) * this
    rw [h3]
    exact a.2
  let P := {p : Fin N × Fin N // p.1 < p.2}
  let mk : (P → L.O ⧸ Ideal.span {δ}) → Matrix (Fin N) (Fin N) E := fun f =>
    Matrix.of fun i j => if h : i < j then ρ (f ⟨(i, j), h⟩) else if i = j then 1 else 0
  have hsub : {C : Set (Matrix (Fin N) (Fin N) E) | ∃ u, IsUni u ∧
      (∀ i j, (δ : E) * u i j ∈ L.O) ∧ C = cos L u} ⊆ (fun f => cos L (mk f)) '' Set.univ := by
    rintro C ⟨u, hu, huδ, rfl⟩
    obtain ⟨w, hw, -, hc, hg⟩ := exists_rep L δ _ hR u hu huδ N
    choose f hf using fun p : P => hg p.1.1 p.1.2 (by omega) p.2
    refine ⟨f, trivial, ?_⟩
    rw [← hc]
    show cos L (mk f) = _
    congr 1
    ext i j
    simp only [mk, Matrix.of_apply]
    split_ifs with h1 h2
    · exact hf ⟨(i, j), h1⟩
    · rw [h2, hw.2]
    · exact (hw.1 i j (lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2))).symm
  refine (Set.encard_le_encard hsub).trans ((Set.encard_image_le _ _).trans (le_of_eq ?_))
  have hP : Nat.card P = N * (N - 1) / 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_product_filter_lt,
      Fintype.card_fin, Nat.choose_two_right]
  rw [Set.encard_univ, ENat.card_eq_coe_natCard, Nat.card_fun, hP]
end GlobalTheory.HL.UniCount
