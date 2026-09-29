-- Prove2me | solution 1 for ModularCurve.NodeLocalized.exists_sub_algebraMap_mem_nonunits_of_mem_modularLocalizedAtPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/48ab6d97-7028-50f7-b7ce-d0afd1dd0ab8

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_exists_sub_algebraMap_mem_nonunits_of_mem_modularLocalizedAtPoint

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_NodeLocalized_exists_sub_algebraMap_mem_nonunits_of_mem_modularLocalizedAtPoint.ModularCurve ModularCurve.NodeLocalized IsLocalRing"

namespace Ws14Port
namespace Eval

theorem isUnit_of_sub_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] {u v : R}
    (hu : IsUnit u) (h : v - u ∈ IsLocalRing.maximalIdeal R) : IsUnit v := by
  by_contra hv
  have hv' : v ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal v).mpr hv
  have : u ∈ IsLocalRing.maximalIdeal R := by
    have := Ideal.sub_mem _ hv' h
    rwa [sub_sub_cancel] at this
  exact (IsLocalRing.mem_maximalIdeal u).mp this hu

theorem ringHom_eval₂Hom {σ R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
    (π : S →+* T) (c : R →+* S) (v : σ → S) (p : MvPolynomial σ R) :
    π (MvPolynomial.eval₂Hom c v p) = MvPolynomial.eval₂Hom (π.comp c) (fun i => π (v i)) p := by
  rw [← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom]

theorem exists_mem_maximalIdeal_of_ord_pos {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (h : 0 < v.ord f) :
    ∃ hf : f ∈ v.toValuationSubring, (⟨f, hf⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at h
  have hval : v.adicValuation f < 1 := by
    have hlog : WithZero.log (v.adicValuation f) < 0 := by
      change 0 < -(WithZero.log (v.adicValuation f)) at h; omega
    rwa [WithZero.log_lt_iff_lt_exp (v.adicValuation_ne_zero hf0), WithZero.exp_zero] at hlog
  refine ⟨(v.mem_iff_adicValuation_le_one).mpr hval.le, ?_⟩
  exact (v.mem_maximalIdeal_iff_adicValuation_lt_one _).mpr hval

end Ws14Port.Eval

open Ws14Port.Eval

section Coe

variable {q : ℕ} [Fact q.Prime]

namespace ModularCurve p2m_export "ModularCurve" "CharPReduction.constSeries coeffEmb jqModC jqNModC jqModC_rat qExpand jq PlaceSpecialization.jFun PlaceSpecialization.jqFun modularFunctionFieldBar PlaceSpecialization coeffMap_jqModC coeffMap_qExpand" namespace PlaceSpecialization p2m_export "ModularCurve.PlaceSpecialization" "jFun jqFun mk" end ModularCurve.PlaceSpecialization
p2m_open_scoped "ModularCurve ModularCurve.PlaceSpecialization" in

theorem ModularCurve.PlaceSpecialization.coe_jFun :
    ((PlaceSpecialization.jFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = jqModC (AlgebraicClosure ℚ) := by
  show coeffEmb (AlgebraicClosure ℚ) jq = _
  rw [coeffEmb, ← jqModC_rat, coeffMap_jqModC]

p2m_open_scoped "ModularCurve ModularCurve.PlaceSpecialization" in

theorem ModularCurve.PlaceSpecialization.coe_jqFun :
    ((PlaceSpecialization.jqFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = jqNModC (AlgebraicClosure ℚ) (1 * q) := by
  show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq) = _
  rw [coeffEmb, coeffMap_qExpand, ← jqModC_rat, coeffMap_jqModC]
  rfl

end Coe

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (hker : ∀ a : A, red a = 0 ↔ a ∈ IsLocalRing.maximalIdeal A)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (x y : A)
    (hx : 0 < W.ord (PlaceSpecialization.jFun (q := q)
      - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ)))
    (hy : 0 < W.ord (PlaceSpecialization.jqFun (q := q)
      - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))
    (g : ↥(modularFunctionFieldBar (1 * q)))
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈
      modularLocalizedAtPoint (1 * q) A.toSubring red (red x) (red y)) :
    ∃ a : A, g - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)
      ∈ W.toValuationSubring.nonunits := by
  classical

  let O := W.toValuationSubring
  let ι : A →+* O := (algebraMap (AlgebraicClosure ℚ) O).comp A.subtype
  have hιF : ∀ a : A, ((ι a : O) : ↥(modularFunctionFieldBar (1 * q))) = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ) :=
    fun a => rfl

  obtain ⟨hjm, hjmax⟩ := exists_mem_maximalIdeal_of_ord_pos W hx
  obtain ⟨hjqm, hjqmax⟩ := exists_mem_maximalIdeal_of_ord_pos W hy
  have hJmem : (PlaceSpecialization.jFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) ∈ O := by
    have := add_mem hjm (W.algebraMap_mem' (x : AlgebraicClosure ℚ))
    rwa [sub_add_cancel] at this
  have hJqmem : (PlaceSpecialization.jqFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) ∈ O := by
    have := add_mem hjqm (W.algebraMap_mem' (y : AlgebraicClosure ℚ))
    rwa [sub_add_cancel] at this
  set J : O := ⟨_, hJmem⟩ with hJ
  set Jq : O := ⟨_, hJqmem⟩ with hJq
  have hJx : J - ι x ∈ maximalIdeal O := by
    have e1 : J - ι x = ⟨_, hjm⟩ := Subtype.ext rfl
    rw [e1]; exact hjmax
  have hJqy : Jq - ι y ∈ maximalIdeal O := by
    have e1 : Jq - ι y = ⟨_, hjqm⟩ := Subtype.ext rfl
    rw [e1]; exact hjqmax

  let π := Ideal.Quotient.mk (maximalIdeal O)
  have hπv : ∀ i : Fin 2, π (![J, Jq] i) = π (ι (![x, y] i)) := by
    intro i
    fin_cases i
    · exact Ideal.Quotient.eq.mpr hJx
    · exact Ideal.Quotient.eq.mpr hJqy

  let ev : MvPolynomial (Fin 2) A →+* O := MvPolynomial.eval₂Hom ι ![J, Jq]
  have hev_coe : ∀ p : MvPolynomial (Fin 2) A,
      (((ev p : O) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = modularEval (1 * q) A.toSubring p := by
    intro p
    have hcomp : ((IntermediateField.val _).toRingHom.comp (O.subtype.comp ev))
        = modularEval (1 * q) A.toSubring := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
      · show (((ev (MvPolynomial.C a) : O) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
          = MvPolynomial.eval₂Hom (CharPReduction.constSeries A.toSubring)
              ![jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) (1 * q)] (MvPolynomial.C a)
        simp only [ev, MvPolynomial.eval₂Hom_C]
        rfl
      · show (((ev (MvPolynomial.X i) : O) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
          = MvPolynomial.eval₂Hom (CharPReduction.constSeries A.toSubring)
              ![jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) (1 * q)] (MvPolynomial.X i)
        simp only [ev, MvPolynomial.eval₂Hom_X']
        fin_cases i
        · exact ModularCurve.PlaceSpecialization.coe_jFun (q := q)
        · exact ModularCurve.PlaceSpecialization.coe_jqFun (q := q)
    exact RingHom.congr_fun hcomp p
  have hev_cong : ∀ p : MvPolynomial (Fin 2) A, π (ev p) = π (ι (MvPolynomial.eval ![x, y] p)) := by
    intro p
    show π (MvPolynomial.eval₂Hom ι ![J, Jq] p) = π (ι (MvPolynomial.eval₂Hom (RingHom.id A) ![x, y] p))
    rw [ringHom_eval₂Hom ι, RingHom.comp_id, ringHom_eval₂Hom π ι, ringHom_eval₂Hom π ι]
    have hfun : (fun i => π (![J, Jq] i)) = (fun i => π (ι (![x, y] i))) := funext hπv
    rw [hfun]
  have hred_eval : ∀ p : MvPolynomial (Fin 2) A,
      red (MvPolynomial.eval ![x, y] p) = pointEval A.toSubring red (red x) (red y) p := by
    intro p
    show red (MvPolynomial.eval₂Hom (RingHom.id A) ![x, y] p) = MvPolynomial.eval₂Hom red ![red x, red y] p
    rw [ringHom_eval₂Hom red, RingHom.comp_id]
    have hfun : (fun i => red (![x, y] i)) = ![red x, red y] := by
      funext i; fin_cases i <;> rfl
    rw [hfun]

  obtain ⟨r, s, hs, hgs⟩ := hg
  have hsunitA : IsUnit (MvPolynomial.eval ![x, y] s) := by
    by_contra h
    apply hs
    rw [← hred_eval, hker]
    exact (IsLocalRing.mem_maximalIdeal _).mpr h
  have hSunit : IsUnit (ev s) := by
    refine isUnit_of_sub_mem_maximalIdeal ((hsunitA.map ι)) ?_
    exact Ideal.Quotient.eq.mp (hev_cong s)

  have hgF : g * ((ev s : O) : ↥(modularFunctionFieldBar (1 * q))) = ((ev r : O) : ↥(modularFunctionFieldBar (1 * q))) := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, hev_coe, hev_coe]
    exact hgs
  set G : O := ev r * ↑(hSunit.unit⁻¹) with hG
  have hGg : (G : ↥(modularFunctionFieldBar (1 * q))) = g := by
    rw [hG, MulMemClass.coe_mul, ← hgF, mul_assoc]
    have : ((ev s : O) : ↥(modularFunctionFieldBar (1 * q))) * ((↑(hSunit.unit⁻¹) : O) : ↥(modularFunctionFieldBar (1 * q))) = 1 := by
      rw [← MulMemClass.coe_mul, IsUnit.mul_val_inv, OneMemClass.coe_one]
    rw [this, mul_one]

  refine ⟨MvPolynomial.eval ![x, y] r * ↑(hsunitA.unit⁻¹), ?_⟩
  have hGa : G - ι (MvPolynomial.eval ![x, y] r * ↑(hsunitA.unit⁻¹)) ∈ maximalIdeal O := by
    refine Ideal.Quotient.eq.mp ?_
    rw [hG, map_mul, map_mul, map_mul, hev_cong r]
    congr 1

    have h1 : π (↑(hSunit.unit⁻¹) : O) * π (ev s) = 1 := by
      have h := congrArg π hSunit.val_inv_mul
      simp only [map_mul, map_one] at h
      exact h
    have h2 : π (ι (↑(hsunitA.unit⁻¹) : A)) * π (ι (MvPolynomial.eval ![x, y] s)) = 1 := by
      have h := congrArg (fun t => π (ι t)) hsunitA.val_inv_mul
      simp only [map_mul, map_one] at h
      exact h
    rw [hev_cong s] at h1
    exact left_inv_eq_right_inv h1 ((mul_comm _ _).trans h2)
  have hmem := ValuationSubring.coe_mem_nonunits_iff.mpr hGa
  rwa [AddSubgroupClass.coe_sub, hGg, hιF] at hmem

end S_ModularCurve_NodeLocalized_exists_sub_algebraMap_mem_nonunits_of_mem_modularLocalizedAtPoint
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_exists_sub_algebraMap_mem_nonunits_of_mem_modularLocalizedAtPoint (solution)
