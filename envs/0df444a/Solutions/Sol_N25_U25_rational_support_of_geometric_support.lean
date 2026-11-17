-- Prove2me | solution 1 for N25.U25_rational_support_of_geometric_support
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:58:04.563607+00:00
-- url     : https://prove2.me/submissions/87292c9f-6f86-4ca2-9832-e40c796e5a94

import Mathlib
import Definitions.Def_N25_Units
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_N25_Endgame_cuspChoice25_spec
import Theorems.Thm_N25_Endgame_rational_place_geometric_lift25
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Definitions.Def_ModularCurve_GeometricBaseChange
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_Place_exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
import Theorems.Thm_N25_U25C_ne_zero

set_option autoImplicit false

open ModularCurve AlgebraicCurve N25.Endgame

namespace N25

private theorem selected_comap (j : Fin 5) :
    (pG25 j).toValuationSubring.comap emb25.toRingHom = (pQ25 j).toValuationSubring := by
  ext f
  change emb25 f ∈ (pG25 j).toValuationSubring ↔ f ∈ (pQ25 j).toValuationSubring
  by_cases hf : f = 0
  · simp [hf]
  have hgf : emb25 f ≠ 0 := by
    intro h
    exact hf (emb25.injective (h.trans (map_zero emb25).symm))
  have ho := cuspChoice25_spec.2.2.2.2.2 j f
  have hl : WithZero.log ((pG25 j).adicValuation (emb25 f)) =
      WithZero.log ((pQ25 j).adicValuation f) := by
    change -WithZero.log ((pG25 j).adicValuation (emb25 f)) =
      -WithZero.log ((pQ25 j).adicValuation f) at ho
    omega
  have hv : (pG25 j).adicValuation (emb25 f) = (pQ25 j).adicValuation f := by
    rw [← WithZero.exp_log ((pG25 j).adicValuation_ne_zero hgf),
      ← WithZero.exp_log ((pQ25 j).adicValuation_ne_zero hf), hl]
  rw [(pG25 j).mem_iff_adicValuation_le_one, (pQ25 j).mem_iff_adicValuation_le_one, hv]

theorem _root_.solution (i : Fin 5)
    (hG : ∀ W : GPlace, (∀ j : Fin 5, W ≠ pG25 j) →
      W.ord (emb25 (U25 i)) = 0) :
    ∀ P : QPlace, (∀ j : Fin 5, P ≠ pQ25 j) → P.ord (U25 i) = 0 := by
  intro P hP
  obtain ⟨W, hW⟩ := rational_place_geometric_lift25 P
  have hnot (j : Fin 5) : W ≠ pG25 j := by
    intro hj
    apply hP j
    apply Place.ext
    exact hW.symm.trans (hj ▸ selected_comap j)
  have ho := hG W hnot
  have hu : U25 i ≠ 0 := U25C_ne_zero ℚ i
  have hgu : emb25 (U25 i) ≠ 0 := by
    intro h
    exact hu (emb25.injective (h.trans (map_zero emb25).symm))
  have hv : W.adicValuation (emb25 (U25 i)) = 1 := by
    have hz : WithZero.log (W.adicValuation (emb25 (U25 i))) = 0 := by
      change -WithZero.log (W.adicValuation (emb25 (U25 i))) = 0 at ho
      omega
    rw [← WithZero.exp_log (W.adicValuation_ne_zero hgu), hz]
    rfl
  have hm : U25 i ∈ P.toValuationSubring := by
    rw [← hW]
    exact W.mem_iff_adicValuation_le_one.mpr hv.le
  have hi : (U25 i)⁻¹ ∈ P.toValuationSubring := by
    rw [← hW]
    apply W.mem_iff_adicValuation_le_one.mpr
    change W.adicValuation (emb25 ((U25 i)⁻¹)) ≤ 1
    rw [map_inv₀, map_inv₀, hv, inv_one]
  let u : P.toValuationSubringˣ :=
    { val := ⟨U25 i, hm⟩
      inv := ⟨(U25 i)⁻¹, hi⟩
      val_inv := Subtype.ext (mul_inv_cancel₀ hu)
      inv_val := Subtype.ext (inv_mul_cancel₀ hu) }
  exact P.ord_coe_unit u

end N25
