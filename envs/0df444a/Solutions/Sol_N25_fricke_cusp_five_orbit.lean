-- Prove2me | solution 1 for N25.fricke_cusp_five_orbit
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:59.313293+00:00
-- url     : https://prove2.me/submissions/5a04ec3f-db4e-45a8-9f6e-cf2d13b7d701

import Mathlib
import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_N25_fricke_selected_cusp_galois_orbit
import Definitions.Def_N25_LocalKummerCharacter
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_diamondAutHBar_mul_and_diamondAutHBar_one
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Theorems.Thm_ModularCurve_diamondAutHBar_eq_refl_of_mem_or_neg_mem
import Theorems.Thm_N25_fricke_selected_cusp_width
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_N25_cusp_width_twentyFive_card_le_five
import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul
import Theorems.Thm_ModularCurve_coe_apply_eq_qExpand_jqModC_of_forall_coeffMap_mul_qExpansion_slash_fricke_eq

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open ModularCurve AlgebraicCurve

open scoped MatrixGroups ModularForm Pointwise

namespace N25

open Endgame

private theorem surjective_of_fin_five_card_bound {A : Type*} [Finite A]
    (f : Fin 5 → A) (hf : Function.Injective f) (hb : Nat.card A ≤ 5) :
    Function.Surjective f := by
  have hcard : Nat.card A = 5 := le_antisymm hb (by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf)
  let : Fintype A := Fintype.ofFinite A
  have hc : Fintype.card (Fin 5) = Fintype.card A := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using hcard.symm
  exact ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,hc⟩).2

private theorem exists_fricke_j_and_galois (ι : Qbar →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ),-1;(25 : ℝ),0]) :
    ∃ w : FG ≃ₐ[Qbar] FG,
      (w (emb25 j25) : LaurentSeries Qbar) = jqNModC Qbar 25 ∧
      ∀ (σ : Gal) (c : ℕ) (hc : c.Coprime 25),
        (∀ ζ : Qbar, ζ ^ 25 = 1 → σ ζ = ζ ^ c) →
        ∀ x : FG, w (arithmeticGalois FQ σ • x) =
          arithmeticGalois FQ σ • diamondAutHBar 25 H25 (ZMod.unitOfCoprime c hc) (w x) := by
  obtain ⟨w,hS,hgal⟩ := exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul 25 H25
    (heckeDiamondInputsHAll 25 H25).2 ι W hW
  have hw : (w (emb25 j25) : LaurentSeries Qbar) = jqNModC Qbar 25 :=
    coe_apply_eq_qExpand_jqModC_of_forall_coeffMap_mul_qExpansion_slash_fricke_eq
      Γ25 25 ι W hW w hS (emb25 j25) (by
        change coeffEmb Qbar (jqModC ℚ) = jqModC Qbar
        exact map_jqModC _)
  exact ⟨w,hw,hgal⟩

set_option diagnostics true in
/-- The five inverse-Fricke cusps form a nonrational transitive Galois orbit of width twenty-five. -/
theorem _root_.solution (ι : Qbar →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (25 : ℝ), 0]) :
    ∃ w : FG ≃ₐ[Qbar] FG,
      let family : Fin 5 → GPlace := fun i => SemilinearAut.ofAlgAut w.symm • pG25 i
      (∀ i : Fin 5, (family i).ord (emb25 j25) = -25) ∧
      Function.Injective family ∧
      (∃ σ : Gal, ∀ i : Fin 5, arithmeticGalois FQ σ • family i = family (i+1)) ∧
      (∀ i : Fin 5, ¬ IsRationalGeomPlace (family i)) ∧
      (∀ i j : Fin 5, ∃ σ : Gal, arithmeticGalois FQ σ • family i = family j) ∧
      ∀ P : GPlace, P.ord (emb25 j25) = -25 → ∃ i : Fin 5, P = family i := by
  obtain ⟨w,hw,hgal⟩ := exists_fricke_j_and_galois ι W hW
  obtain ⟨hinj,hcycle,hnon,htrans⟩ := fricke_selected_cusp_galois_orbit w hgal
  have hwidth := fricke_selected_cusp_width w hw
  refine ⟨w,hwidth,hinj,hcycle,hnon,htrans,?_⟩
  intro P hP
  let S := {Q : GPlace // Q.ord (emb25 j25) = -25}
  let selected : Fin 5 → S := fun i => ⟨SemilinearAut.ofAlgAut w.symm • pG25 i,hwidth i⟩
  have hs : Function.Injective selected := fun i j h => hinj (congrArg Subtype.val h)
  have hb := cusp_width_twentyFive_card_le_five
  let : Finite S := hb.1
  have hsurj : Function.Surjective selected := surjective_of_fin_five_card_bound selected hs hb.2
  obtain ⟨i,hi⟩ := hsurj ⟨P,hP⟩
  exact ⟨i,(congrArg Subtype.val hi).symm⟩

end N25
