-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_nodeUnit_lam_mu_hasValue_of_ord_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/49fdc987-a780-5962-98a6-b58201b6377d

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces_univ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeUnit_lam_mu_hasValue_of_ord_eq_one
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace FltWs11
namespace VP

theorem exists_units_hasValue_of_ord_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    ∃ a : Kˣ, v.HasValue f (a : K) := by
  obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hf h
  obtain ⟨a, ha, hane⟩ := v.exists_hasValue_of_surjective hv hm
  exact ⟨Units.mk0 a (hane hu), ha⟩

theorem ord_div_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f = v.ord g) :
    v.ord (f / g) = 0 := by
  rw [div_eq_mul_inv, v.ord_mul hf (inv_ne_zero hg), v.ord_inv, h]
  ring

theorem ne_zero_of_ord_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (h : v.ord f ≠ 0) : f ≠ 0 := by
  rintro rfl
  exact h v.ord_zero

end FltWs11.VP

open FltWs11.VP in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    {W : Finset (Place k (modularFunctionFieldC k N))}
    (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hRL : R.RegularityLaw W)
    (K : Place k (modularFunctionFieldC k N) → IntermediateField ℚ (AlgebraicClosure ℚ))
    (coord : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), R.NodeCoordinates (K w) w)
    (u : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), ↥(R.nodeIntegersOver (K w) w))
    (hu : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), IsUnit (u w hw))
    (unifFst unifSnd : Place k (modularFunctionFieldC k N) → ↥(modularFunctionFieldC k N))
    (hunifFst : ∀ w ∈ W, w.ord (unifFst w) = 1)
    (hunifSnd : ∀ w ∈ W, (arithFrobC q k N • w).ord (unifSnd w) = 1) :
    ∃ (u0 lam mu : Place k (modularFunctionFieldC k N) → kˣ),
      (∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨(u w hw : ↥(modularFunctionFieldBar (N * q))), (u w hw).2.1⟩) ((u0 w : kˣ) : k)) ∧
      (∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨((coord w hw).y : ↥(modularFunctionFieldBar (N * q))), (coord w hw).y.2.1⟩
        / unifFst w) ((lam w : kˣ) : k)) ∧
      (∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      (arithFrobC q k N • w).HasValue
        (R.nodeResidue₂ w ⟨((coord w hw).x : ↥(modularFunctionFieldBar (N * q))), (coord w hw).x.2.1⟩
          / unifSnd w) ((mu w : kˣ) : k)) := by
  classical

  have hrat : ∀ w ∈ W, w.IsRational := fun w hw => (hW w hw).1
  have hratφ : ∀ w ∈ W, (arithFrobC q k N • w).IsRational := fun w hw =>
    (ModularCurve.arithFrobC_smul_mem_ssPlaces_univ q N k _ (hW w hw)).1

  have hA : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), ∃ a : kˣ,
      w.HasValue (R.nodeResidue₁ w ⟨(u w hw : ↥(modularFunctionFieldBar (N * q))), (u w hw).2.1⟩) (a : k) := by
    intro w hw

    have hval : ∀ f : ↥(R.nodeIntegers w), ∃ c : k, w.HasValue (R.nodeResidue₁ w f) c := by
      intro f
      obtain ⟨c, hc, -⟩ := hRL.2 (f : ↥(modularFunctionFieldBar (N * q))) f.2.1 f.2.2.1
        (smulNodePair (arithFrobC q k N) w) (smulNodePair_mem_nodePairsOfPlaces _ hw)
        (fun V hV => R.ord_nonneg_of_mem_nodeIntegers f.2 hV)
      exact ⟨c, hc⟩
    let f : ↥(R.nodeIntegers w) := ⟨(u w hw : ↥(modularFunctionFieldBar (N * q))), (u w hw).2.1⟩
    obtain ⟨g, hg⟩ := (hu w hw).exists_right_inv
    let f' : ↥(R.nodeIntegers w) := ⟨(g : ↥(modularFunctionFieldBar (N * q))), g.2.1⟩
    have hff' : f * f' = 1 := by
      apply Subtype.ext
      show ((u w hw * g : ↥(R.nodeIntegersOver (K w) w)) : ↥(modularFunctionFieldBar (N * q))) = 1
      rw [hg]
      rfl
    obtain ⟨c, hc⟩ := hval f
    obtain ⟨c', hc'⟩ := hval f'
    have h1 : w.HasValue (R.nodeResidue₁ w (f * f')) (c * c') := by
      rw [map_mul]
      exact hc.mul hc'
    rw [hff', map_one] at h1
    have hcc' : c * c' = 1 := h1.unique w.hasValue_one
    exact ⟨Units.mk0 c (left_ne_zero_of_mul_eq_one hcc'), hc⟩

  have hB : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), ∃ a : kˣ,
      w.HasValue (R.nodeResidue₁ w ⟨((coord w hw).y : ↥(modularFunctionFieldBar (N * q))), (coord w hw).y.2.1⟩
        / unifFst w) (a : k) := by
    intro w hw
    have hord1 : w.ord (R.nodeResidue₁ w ⟨((coord w hw).y : ↥(modularFunctionFieldBar (N * q))), (coord w hw).y.2.1⟩) = 1 :=
      (coord w hw).y_fst
    have hord2 : w.ord (unifFst w : modularFunctionFieldC k N) = 1 := hunifFst w hw
    refine exists_units_hasValue_of_ord_eq_zero w (hrat w hw) ?_ (ord_div_eq_zero w ?_ ?_ (hord1.trans hord2.symm))
    · exact div_ne_zero (ne_zero_of_ord_ne_zero w (by rw [hord1]; exact one_ne_zero))
        (ne_zero_of_ord_ne_zero w (by rw [hord2]; exact one_ne_zero))
    · exact ne_zero_of_ord_ne_zero w (by rw [hord1]; exact one_ne_zero)
    · exact ne_zero_of_ord_ne_zero w (by rw [hord2]; exact one_ne_zero)

  have hC : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), ∃ a : kˣ,
      (arithFrobC q k N • w).HasValue
        (R.nodeResidue₂ w ⟨((coord w hw).x : ↥(modularFunctionFieldBar (N * q))), (coord w hw).x.2.1⟩
          / unifSnd w) (a : k) := by
    intro w hw
    have hord1 : (arithFrobC q k N • w).ord
        (R.nodeResidue₂ w ⟨((coord w hw).x : ↥(modularFunctionFieldBar (N * q))), (coord w hw).x.2.1⟩) = 1 :=
      (coord w hw).x_snd
    have hord2 : (arithFrobC q k N • w).ord (unifSnd w : modularFunctionFieldC k N) = 1 := hunifSnd w hw
    refine exists_units_hasValue_of_ord_eq_zero _ (hratφ w hw) ?_
      (ord_div_eq_zero _ ?_ ?_ (hord1.trans hord2.symm))
    · exact div_ne_zero (ne_zero_of_ord_ne_zero _ (by rw [hord1]; exact one_ne_zero))
        (ne_zero_of_ord_ne_zero _ (by rw [hord2]; exact one_ne_zero))
    · exact ne_zero_of_ord_ne_zero _ (by rw [hord1]; exact one_ne_zero)
    · exact ne_zero_of_ord_ne_zero _ (by rw [hord2]; exact one_ne_zero)

  choose fA hfA using hA
  choose fB hfB using hB
  choose fC hfC using hC
  refine ⟨fun w => if h : w ∈ W then fA w h else 1, fun w => if h : w ∈ W then fB w h else 1,
    fun w => if h : w ∈ W then fC w h else 1, ?_, ?_, ?_⟩
  · intro w hw
    show w.HasValue _ (((if h : w ∈ W then fA w h else 1 : kˣ)) : k)
    rw [dif_pos hw]; exact hfA w hw
  · intro w hw
    show w.HasValue _ (((if h : w ∈ W then fB w h else 1 : kˣ)) : k)
    rw [dif_pos hw]; exact hfB w hw
  · intro w hw
    show (arithFrobC q k N • w).HasValue _ (((if h : w ∈ W then fC w h else 1 : kˣ)) : k)
    rw [dif_pos hw]; exact hfC w hw

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeUnit_lam_mu_hasValue_of_ord_eq_one
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeUnit_lam_mu_hasValue_of_ord_eq_one (solution)
