-- Prove2me | solution 1 for GlobalTheory.QNorm.first_inequality_sUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:58:26.249743+00:00
-- url     : https://prove2.me/submissions/0bd5c702-1e1a-4c06-8050-3e85aa4f6a24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexFormulaNormsInvolutionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoMulCardPlacesLeCardOverQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoMulCardInfinitePlaceLeQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsQuadraticSqrtExtensionOfNotSquareStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsPlacesOverAndQuadraticConjStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_Hilbert90SUnitsQuadraticExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HeightOneSpectrumPlacesOverFiniteSetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexSquaresSUnitsNumberFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FirstInequalitySUnits
import Theorems.Thm_GlobalTheory_QNorm_mem_normSub
import Theorems.Thm_GlobalTheory_QNorm_mem_sUnits
import Theorems.Thm_GlobalTheory_T_exists_isQuadraticSqrtExtension_of_not_square
import Theorems.Thm_GlobalTheory_T_heightOneSpectrum_places_over_finite_set
import Theorems.Thm_GlobalTheory_T_hilbert90_sUnits_quadratic_extension_of_adm
import Theorems.Thm_GlobalTheory_T_index_formula_norms_involution
import Theorems.Thm_GlobalTheory_T_isQuadraticSqrtExtension_basic_facts
import Theorems.Thm_GlobalTheory_T_relIndex_squares_sUnitsNumberField
import Theorems.Thm_GlobalTheory_T_sUnits_places_over_and_quadratic_conj
import Theorems.Thm_GlobalTheory_T_two_mul_card_infinitePlace_le_quadratic
import Theorems.Thm_GlobalTheory_T_two_mul_card_places_le_card_over_quadratic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
namespace GlobalTheory.QNorm
private theorem index_sqs_top_eq {G : Type} [CommGroup G] (U : Subgroup G) :
    (sqs (⊤ : Subgroup U)).index = (sqs U).relIndex U := by
  unfold Subgroup.relIndex
  congr 1
  ext x
  simp only [sqs, Subgroup.mem_map, Subgroup.mem_top, true_and, Subgroup.mem_subgroupOf,
    powMonoidHom_apply]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.2, by simp⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using h)⟩
private theorem relIndex_sqs_range_eq {U A : Type} [CommGroup U] [CommGroup A] (j : U →* A)
    (hj : Function.Injective j) :
    (sqs j.range).relIndex j.range = (sqs (⊤ : Subgroup U)).index := by
  rw [← Subgroup.index_comap]
  congr 1
  ext x
  simp only [sqs, Subgroup.mem_map, Subgroup.mem_top, true_and, Subgroup.mem_comap,
    powMonoidHom_apply, MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, h⟩
    exact ⟨y, hj (by simpa using h)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨j y, ⟨y, rfl⟩, by simp⟩
private theorem arith_first_ineq (m n e s t : ℕ) (hd : m ∣ n) (h : 2 * 2 ^ e * n = (2 ^ s) ^ 2)
    (hs : 2 * s ≤ e + t) : m ≠ 0 ∧ 2 * m ≤ 2 ^ t := by
  have hn : n ≠ 0 := by
    rintro rfl
    have : 0 < (2 ^ s) ^ 2 := by positivity
    omega
  refine ⟨fun h0 => hn (by subst h0; simpa using hd), ?_⟩
  have hmn : m ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
  have h1 : 2 ^ e * (2 * n) ≤ 2 ^ e * 2 ^ t := by
    calc 2 ^ e * (2 * n) = (2 ^ s) ^ 2 := by rw [← h]; ring
      _ = 2 ^ (2 * s) := by ring
      _ ≤ 2 ^ (e + t) := Nat.pow_le_pow_right (by norm_num) hs
      _ = 2 ^ e * 2 ^ t := pow_add _ _ _
  have h2 : 2 * n ≤ 2 ^ t := Nat.le_of_mul_le_mul_left h1 (by positivity)
  omega
end GlobalTheory.QNorm
end

set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution :
    ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))),
      admitted F S → δ ∈ sUnits F S → ¬ IsSquare (δ : F) →
      (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≠ 0 ∧
        2 * (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≤
          2 ^ (tFin F δ S + tReal F δ) := by
  intro F _ _ δ S hS hδ hns
  obtain ⟨E, _, _, _, θ, σ, hq⟩ := GlobalTheory.T.exists_isQuadraticSqrtExtension_of_not_square F δ hns
  obtain ⟨SE, hSE⟩ := (GlobalTheory.T.heightOneSpectrum_places_over_finite_set F E).1 S
  obtain ⟨hinv, hfix, -, hnorm, -, -, -⟩ := GlobalTheory.T.isQuadraticSqrtExtension_basic_facts F E δ θ σ hq
  obtain ⟨hup, hσ⟩ := GlobalTheory.T.sUnits_places_over_and_quadratic_conj F E δ θ σ hq S SE hSE
  have h90 := GlobalTheory.T.hilbert90_sUnits_quadratic_extension_of_adm F E δ θ σ hq S SE hSE hS ((mem_sUnits F S δ).1 hδ)
  have hcf := GlobalTheory.T.two_mul_card_places_le_card_over_quadratic F E δ θ σ hq S SE hSE
  have hci := GlobalTheory.T.two_mul_card_infinitePlace_le_quadratic F E δ θ σ hq
  let τ : sUnits E SE →* sUnits E SE :=
    ((Units.map (σ : E →* E)).comp (sUnits E SE).subtype).codRestrict _ (fun y => hσ y y.2)
  have hτ : ∀ y : sUnits E SE, (((τ y : sUnits E SE) : Eˣ) : E) = σ ((y : Eˣ) : E) :=
    fun _ => rfl
  let j : sUnits F S →* sUnits E SE :=
    ((Units.map (algebraMap F E : F →* E)).comp (sUnits F S).subtype).codRestrict _
      (fun y => (hup y).2 y.2)
  have hj : ∀ y : sUnits F S, (((j y : sUnits E SE) : Eˣ) : E) = algebraMap F E ((y : Fˣ) : F) :=
    fun _ => rfl
  have hext : ∀ a b : sUnits E SE, ((a : Eˣ) : E) = ((b : Eˣ) : E) → a = b :=
    fun a b h => Subtype.ext (Units.ext h)
  have hjinj : Function.Injective j := by
    intro a b h
    apply Subtype.ext
    apply Units.ext
    apply (algebraMap F E).injective
    rw [← hj, ← hj, h]
  have hm : (-1 : Eˣ) ∈ sUnits E SE := by
    rw [mem_sUnits]
    intro v _
    simp
  have hrange : τ.eqLocus (MonoidHom.id _) = j.range := by
    ext y
    rw [MonoidHom.mem_range]
    change τ y = y ↔ _
    constructor
    · intro h
      obtain ⟨a, ha⟩ := hfix ((y : Eˣ) : E) (by rw [← hτ, h])
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact (y : Eˣ).ne_zero (by simpa using ha)
      have hy : Units.map (algebraMap F E : F →* E) (Units.mk0 a ha0) = y :=
        Units.ext (by simpa using ha.symm)
      refine ⟨⟨Units.mk0 a ha0, (hup _).1 (hy ▸ y.2)⟩, hext _ _ ?_⟩
      rw [hj, ha]; rfl
    · rintro ⟨x, rfl⟩
      apply hext
      rw [hτ, hj, AlgEquiv.commutes]
  have key := GlobalTheory.T.index_formula_norms_involution (sUnits E SE) τ ⟨-1, hm⟩
    (fun a => hext _ _ (by rw [hτ, hτ, hinv]))
    (fun a ha => by
      have h1 : ((a : Eˣ) : E) * σ ((a : Eˣ) : E) = 1 := by
        rw [← hτ]
        have := congrArg (fun z : sUnits E SE => ((z : Eˣ) : E)) ha
        simpa using this
      obtain ⟨y, hy, h⟩ := h90 a a.2 h1
      refine ⟨⟨y, hy⟩, hext _ _ ?_⟩
      rw [h, Subgroup.coe_div, Units.val_div_eq_div_val, hτ])
    (fun h => by
      have := congrArg (fun z : sUnits E SE => ((z : Eˣ) : E)) h
      simp only [Units.val_neg, Units.val_one, OneMemClass.coe_one] at this
      norm_num at this)
    (hext _ _ (by simp))
    (hext _ _ (by rw [hτ]; simp))
    (fun a ha => by
      have h1 : ((a : Eˣ) : E) ^ 2 = 1 := by
        have := congrArg (fun z : sUnits E SE => ((z : Eˣ) : E)) ha
        simpa using this
      rcases sq_eq_one_iff.1 h1 with h | h
      · exact Or.inl (hext _ _ (by simpa using h))
      · exact Or.inr (hext _ _ (by simpa using h)))
  rw [hrange, relIndex_sqs_range_eq j hjinj, index_sqs_top_eq, index_sqs_top_eq,
    GlobalTheory.T.relIndex_squares_sUnitsNumberField E SE, GlobalTheory.T.relIndex_squares_sUnitsNumberField F S, ← Subgroup.index_comap] at key
  refine arith_first_ineq _ _ _ _ _ ?_ key (by omega)
  apply Subgroup.index_dvd_of_le
  rintro x ⟨y, hy⟩
  rw [Subgroup.mem_subgroupOf, mem_normSub]
  obtain ⟨a, b, hab⟩ := hnorm ((y : Eˣ) : E)
  refine ⟨a, b, ?_⟩
  apply (algebraMap F E).injective
  simp only [RingHom.id_apply]
  rw [← hab, ← hj, ← hy, ← hτ]
  simp
end GlobalTheory.QNorm
