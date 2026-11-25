-- Prove2me | solution 1 for GlobalTheory.MoveFine.chi_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:39:25.539784+00:00
-- url     : https://prove2.me/submissions/95f2d55f-aabc-4e20-bcfd-65b08abac70b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerLatticeLocallyConstantDataStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsFineSubgroupMovesAtLattice
import Theorems.Thm_GlobalTheory_MoveFine_h_add_l
import Theorems.Thm_GlobalTheory_MoveFine_h_smul_l
import Theorems.Thm_GlobalTheory_MoveFine_h_add_r
import Theorems.Thm_GlobalTheory_MoveFine_h_smul_r
import Theorems.Thm_GlobalTheory_MoveFine_pair_int
import Theorems.Thm_GlobalTheory_MoveFine_algO
import Theorems.Thm_GlobalTheory_MoveFine_th_ne
import Theorems.Thm_GlobalTheory_MoveFine_p_eq_th
import Theorems.Thm_GlobalTheory_MoveFine_bound
import Theorems.Thm_GlobalTheory_MoveFine_mem_intP
import Theorems.Thm_GlobalTheory_MoveFine_p_unit
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_hermitian_double_coset_term_basic_facts
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
open GlobalTheory GlobalTheory.MoveFine
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.MoveFine
theorem _root_.solution (j : Fin r) {d : S.Datum} {Λ : Submodule L.O S.V} (hT : S.IsTerm d Λ) (A : ℕ)
    (hA : algebraMap F E ((S.ϖ : F) ^ S.a) = algebraMap F E S.ϖ ^ A) (n : ℕ) (w y : S.MW)
    (hw : S.Mv (j + 1) d Λ w) (hy : y ∈ intP S Λ) (hl : algebraMap F E S.ϖ ^ (n + A + 1) • y ∈ lin S (j + 1)) :
    S.chiM j d Λ (w + algebraMap F E S.ϖ ^ (n + A + 1) • y).1 (w + algebraMap F E S.ϖ ^ (n + A + 1) • y).2.1 =
      S.chiM j d Λ w.1 w.2.1 := by
  obtain ⟨hΛ, hW, -, hf, hf', -⟩ := GlobalTheory.T.hermitian_double_coset_term_basic_facts L r k S d Λ hT
  have hJ : (j : ℕ) + 1 ≤ r + 1 := by have := j.2; omega
  have hp := fun n => L.O.pow_mem (algO S S.ϖ) n
  have hi : ∀ x ∈ Λ, ∀ y ∈ Λ, S.h x y ∈ L.O := fun x hx y hy => (hΛ.2 y).2 hy x hx
  obtain ⟨hx, hx', hb, -, hu, -⟩ := hw
  obtain ⟨b1, b2⟩ := bound S d Λ hT _ hJ _ _ hx hx' hb
  rw [hA] at b1 b2
  obtain ⟨⟨h1, h2⟩, h3, -⟩ := (mem_intP S).1 hy
  have k1 := pair_int S S.f S.es S.dual _ hW.2.2.1 j _ ((hf _ hJ _).1 ⟨b1, Submodule.smul_mem _ _ hx⟩)
  have k2 := pair_int S S.f' S.es' S.dual' _ hW.2.2.2.1 j _ ((hf' _ hJ _).1 ⟨b2, Submodule.smul_mem _ _ hx'⟩)
  have k3 := pair_int S S.f S.es S.dual _ hW.2.2.1 j _ ((hf _ hJ _).1
      ⟨h1, (Submodule.smul_mem_iff_of_isUnit _ (p_unit S _)).1 hl.1.1⟩)
  have k4 := pair_int S S.f' S.es' S.dual' _ hW.2.2.2.1 j _ ((hf' _ hJ _).1
      ⟨h2, (Submodule.smul_mem_iff_of_isUnit _ (p_unit S _)).1 hl.1.2⟩)
  rw [h_smul_l] at k1 k2
  have g1 : S.fr d Λ j.succ ∈ Λ := ((hf (r + 1) le_rfl _).2 (Submodule.subset_span ⟨_, j.succ.2, rfl⟩)).1
  have g2 : S.fr' d Λ j.succ ∈ Λ := ((hf' (r + 1) le_rfl _).2 (Submodule.subset_span ⟨_, j.succ.2, rfl⟩)).1
  obtain ⟨e, he, h⟩ := p_eq_th S
  have ht : algebraMap F E S.th⁻¹ * algebraMap F E S.ϖ = e := by
    rw [h, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (th_ne S), map_one, one_mul]
  have hz := L.O.neg_mem (L.O.mul_mem (L.O.mul_mem he (hp n)) (L.O.add_mem
    (L.O.add_mem (L.O.mul_mem k1 (hi _ g1 _ h3)) (L.O.mul_mem k2 (hi _ g2 _ h3)))
    (L.O.mul_mem (hp A) (L.O.add_mem
      (L.O.mul_mem k3 (L.O.add_mem (hi _ g1 _ hu) (L.O.mul_mem (hp (n + A + 1)) (hi _ g1 _ h3))))
      (L.O.mul_mem k4 (L.O.add_mem (hi _ g2 _ hu) (L.O.mul_mem (hp (n + A + 1)) (hi _ g2 _ h3))))))))
  have h0 := (L.additive_character_dual_ring _).2 hz 1 L.O.one_mem
  unfold Frames.chiM
  rw [← mul_one (L.psi0 (-(_ * S.h _ w.2.1))), ← h0, ← AddChar.map_add_eq_mul]
  congr 1
  simp only [Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, h_add_l, h_add_r, h_smul_l,
    h_smul_r, map_pow, AlgEquiv.commutes, ← ht]
  ring
end GlobalTheory.MoveFine
