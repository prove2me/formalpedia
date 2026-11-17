-- Prove2me | solution 1 for N25.cuspArithmeticCensus_of_degree_bounds
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:55.729463+00:00
-- url     : https://prove2.me/submissions/bb7eedc4-272c-456f-aa55-6cc369ac42fa

import Mathlib
import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_N25_Endgame_pQ25_j_order
import Theorems.Thm_N25_Endgame_pQ25_degree
import Theorems.Thm_N25_Endgame_pQ25_isCusp
import Theorems.Thm_N25_Endgame_cuspChoice25_spec
import Theorems.Thm_N25_Endgame_rational_place_geometric_lift25
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Definitions.Def_ModularCurve_GeometricBaseChange
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_Place_exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
import Theorems.Thm_N25_cuspArithmeticCensus_geometric
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin
import Theorems.Thm_N25_cusp_geometric_contraction
import Theorems.Thm_N25_Endgame_cusp_constant_fibre_degree25
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_Place_not_mem_iff_ord_neg
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_Function_bijective_of_fiber_card_bounds
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace N25

open Endgame

/-- The fourteen geometric cusps force the exact closed-cusp census once the
    middle and Fricke closed cusps have residue degrees at least four and five. -/
theorem _root_.solution
    (Q₄ Q₅ : QPlace) (hc₄ : IsCusp j25 Q₄) (hc₅ : IsCusp j25 Q₅)
    (ho₄ : Q₄.ord j25 = -5) (ho₅ : Q₅.ord j25 = -25)
    (hd₄ : 4 ≤ Q₄.deg) (hd₅ : 5 ≤ Q₅.deg) :
    Nat.card {P : GPlace // IsCusp (emb25 j25) P} = 14 ∧
      (∃ e : Fin 7 ≃ {Q : QPlace // IsCusp j25 Q},
        ∀ i, (e i).1.deg = (![1,1,1,1,1,4,5] i : ℕ)) ∧
      Q₄.deg = 4 ∧ Q₅.deg = 5 ∧
      ∀ Q : QPlace, IsCusp j25 Q ↔
        (∃ i : Fin 5, Q = pQ25 i) ∨ Q = Q₄ ∨ Q = Q₅ := by
  classical
  let A := {P : GPlace // IsCusp (emb25 j25) P}
  let B := {Q : QPlace // IsCusp j25 Q}
  let ι : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hgeo := cuspArithmeticCensus_geometric ι.toRingHom
  have hpred (P : GPlace) : IsCusp (emb25 j25) P ↔ P.ord (emb25 j25) < 0 :=
    P.not_mem_iff_ord_neg _
  let ge : A ≃ {P : GPlace // P.ord (emb25 j25) < 0} :=
    Equiv.subtypeEquivRight hpred
  let : Finite {P : GPlace // P.ord (emb25 j25) < 0} := hgeo.1
  let : Finite A := Finite.of_injective ge ge.injective
  have hcard : Nat.card A = 14 := (Nat.card_congr ge).trans hgeo.2
  let f : A → B := fun P =>
    ⟨(cusp_geometric_contraction P.1 P.2).choose,
      (cusp_geometric_contraction P.1 P.2).choose_spec.1.1⟩
  have hc (P : A) : (f P).1.toValuationSubring =
      P.1.toValuationSubring.comap emb25.toRingHom :=
    (cusp_geometric_contraction P.1 P.2).choose_spec.1.2
  have hfeq (P : A) (Q : B) : f P = Q ↔
      P.1.toValuationSubring.comap emb25.toRingHom = Q.1.toValuationSubring := by
    constructor
    · intro h
      rw [← hc P, h]
    · intro h
      apply Subtype.ext
      exact Place.ext ((hc P).trans h)
  have hf : Function.Surjective f := by
    intro Q
    obtain ⟨P, hP⟩ := rational_place_geometric_lift25 Q.1
    have hp : IsCusp (emb25 j25) P := by
      change emb25 j25 ∉ P.toValuationSubring
      intro hm
      apply Q.2
      rw [← hP]
      exact hm
    exact ⟨⟨P,hp⟩, (hfeq _ Q).mpr hP⟩
  have hcf (Q : B) : Nat.card {P : A // f P = Q} = Q.1.deg := by
    let e : {P : A // f P = Q} ≃ {P : GPlace |
        P.toValuationSubring.comap emb25.toRingHom = Q.1.toValuationSubring} :=
      { toFun := fun P => ⟨P.1.1, (hfeq P.1 Q).mp P.2⟩
        invFun := fun P =>
          let a : A := ⟨P.1, by
            change emb25 j25 ∉ P.1.toValuationSubring
            intro hm
            apply Q.2
            rw [← P.2]
            exact hm⟩
          ⟨a, (hfeq a Q).mpr P.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Nat.card_congr e).trans (cusp_constant_fibre_degree25 Q.1).2
  let p : Fin 7 → B :=
    ![⟨pQ25 0,pQ25_isCusp 0⟩, ⟨pQ25 1,pQ25_isCusp 1⟩,
      ⟨pQ25 2,pQ25_isCusp 2⟩, ⟨pQ25 3,pQ25_isCusp 3⟩,
      ⟨pQ25 4,pQ25_isCusp 4⟩, ⟨Q₄,hc₄⟩, ⟨Q₅,hc₅⟩]
  have hp : Function.Injective p := by
    intro i j hij
    have hval := congrArg (fun Q : B => Q.1) hij
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | solve
        | have ho := congrArg (fun Q : QPlace => Q.ord j25) hval
          norm_num [p, pQ25_j_order, ho₄, ho₅] at ho
        | have he := cuspChoice25_spec.2.1 (by simpa [p] using hval)
          have hv := congrArg Fin.val he
          norm_num at hv
  let w : Fin 7 → ℕ := ![1,1,1,1,1,4,5]
  have hw : ∑ i, w i = Nat.card A := by rw [hcard]; decide
  have hb (i : Fin 7) : w i ≤ Nat.card {P : A // f P = p i} := by
    rw [hcf]
    fin_cases i <;> simp [w, p, pQ25_degree, hd₄, hd₅]
  obtain ⟨hpbij, hexact⟩ := Function.bijective_of_fiber_card_bounds f hf p hp w hw hb
  refine ⟨hcard, ⟨Equiv.ofBijective p hpbij, ?_⟩, ?_, ?_, ?_⟩
  · intro i
    exact (hcf (p i)).symm.trans (hexact i)
  · simpa [p, w] using (hcf (p 5)).symm.trans (hexact 5)
  · simpa [p, w] using (hcf (p 6)).symm.trans (hexact 6)
  · intro Q
    constructor
    · intro hQ
      obtain ⟨i, hi⟩ := hpbij.2 ⟨Q,hQ⟩
      have hv := congrArg (fun x : B => x.1) hi
      fin_cases i
      · exact Or.inl ⟨0, by simpa [p] using hv.symm⟩
      · exact Or.inl ⟨1, by simpa [p] using hv.symm⟩
      · exact Or.inl ⟨2, by simpa [p] using hv.symm⟩
      · exact Or.inl ⟨3, by simpa [p] using hv.symm⟩
      · exact Or.inl ⟨4, by simpa [p] using hv.symm⟩
      · exact Or.inr (Or.inl (by simpa [p] using hv.symm))
      · exact Or.inr (Or.inr (by simpa [p] using hv.symm))
    · rintro (⟨i,rfl⟩ | rfl | rfl)
      · exact pQ25_isCusp i
      · exact hc₄
      · exact hc₅

end N25
