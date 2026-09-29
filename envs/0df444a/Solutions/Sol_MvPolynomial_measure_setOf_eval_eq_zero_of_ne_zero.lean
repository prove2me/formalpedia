-- Prove2me | solution 1 for MvPolynomial.measure_setOf_eval_eq_zero_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/db175f5d-a715-578d-8bc6-6afbf1d0914e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_measure_setOf_eval_eq_zero_of_ne_zero

set_option autoImplicit false

open MeasureTheory
open Filter Topology
open scoped ENNReal

namespace E8A
namespace NS

theorem nhdsNE_zero_neBot (F : Type) [AddGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    (hF : ¬ DiscreteTopology F) : (𝓝[≠] (0 : F)).NeBot := by
  rw [discreteTopology_iff_nhds_ne] at hF
  push_neg at hF
  obtain ⟨x, hx⟩ := hF
  have hx' : (𝓝[≠] x).NeBot := hx
  have h := (Homeomorph.addRight (-x)).isEmbedding.map_nhdsWithin_eq ({x}ᶜ) x
  rw [Set.image_compl_eq (Homeomorph.addRight (-x)).bijective, Set.image_singleton] at h
  simp only [Homeomorph.coe_addRight, add_neg_cancel] at h
  rw [← h]
  exact hx'.map _

theorem pi_fin (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace F]
    [T2Space F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] (hF : ¬ DiscreteTopology F)
    (μF : Measure F) [μF.IsAddHaarMeasure] :
    ∀ (n : ℕ) (p : MvPolynomial (Fin n) F), p ≠ 0 →
      (Measure.pi fun _ : Fin n => μF) {x | MvPolynomial.eval x p = 0} = 0 := by
  haveI : (𝓝[≠] (0 : F)).NeBot := nhdsNE_zero_neBot F hF
  intro n
  induction n with
  | zero =>
    intro p hp
    have h : {x : Fin 0 → F | MvPolynomial.eval x p = 0} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rw [MvPolynomial.eq_C_of_isEmpty p, MvPolynomial.eval_C]
      intro h0
      apply hp
      rw [MvPolynomial.eq_C_of_isEmpty p, h0, MvPolynomial.C_0]
    rw [h, measure_empty]
  | succ n ih =>
    intro p hp
    classical
    set P : Polynomial (MvPolynomial (Fin n) F) := MvPolynomial.finSuccEquiv F n p with hP
    have hP0 : P ≠ 0 := by
      intro h; apply hp
      apply (MvPolynomial.finSuccEquiv F n).injective
      rw [← hP, h, map_zero]
    have hlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => F) 0 with he
    have hmp : MeasurePreserving e (Measure.pi fun _ : Fin (n + 1) => μF)
        (μF.prod (Measure.pi fun _ : Fin n => μF)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μF) 0
    have hsymm : ∀ q : F × (Fin n → F), e.symm q = (Fin.cons q.1 q.2 : Fin (n + 1) → F) := by
      intro q
      rw [← Fin.insertNth_zero']
      rfl
    have hZm : MeasurableSet {x : Fin (n + 1) → F | MvPolynomial.eval x p = 0} :=
      (isClosed_singleton.preimage (MvPolynomial.continuous_eval p)).measurableSet
    set S : Set (F × (Fin n → F)) := e.symm ⁻¹' {x : Fin (n + 1) → F | MvPolynomial.eval x p = 0} with hSdef
    have hS : MeasurableSet S := hZm.preimage e.symm.measurable
    have hZ : {x : Fin (n + 1) → F | MvPolynomial.eval x p = 0} = e ⁻¹' S := by
      rw [hSdef, ← Set.preimage_comp, MeasurableEquiv.symm_comp_self, Set.preimage_id]
    rw [hZ, hmp.measure_preimage hS.nullMeasurableSet, Measure.prod_apply_symm hS]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    have hN : (Measure.pi fun _ : Fin n => μF) {y | MvPolynomial.eval y P.leadingCoeff = 0} = 0 :=
      ih _ hlc
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hN] with y hy
    change ¬ (MvPolynomial.eval y P.leadingCoeff = 0) at hy
    have hQ : P.map (MvPolynomial.eval y) ≠ 0 := by
      intro h
      apply hy
      have := congrArg (fun q => q.coeff P.natDegree) h
      simpa only [Polynomial.coeff_map, Polynomial.coeff_natDegree, Polynomial.coeff_zero] using this
    refine Set.Finite.measure_zero ?_ μF
    refine ((P.map (MvPolynomial.eval y)).roots.toFinset.finite_toSet).subset ?_
    intro x hx
    simp only [Set.mem_preimage, hSdef, Set.mem_setOf_eq, hsymm] at hx
    rw [MvPolynomial.eval_eq_eval_mv_eval', ← hP] at hx
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hQ, Polynomial.IsRoot]
    exact hx

theorem nullset (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace F]
    [T2Space F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] (hF : ¬ DiscreteTopology F)
    (ι : Type) [Fintype ι] (p : MvPolynomial ι F) (hp : p ≠ 0)
    (μ : Measure (ι → F)) [μ.IsAddHaarMeasure] : μ {x | MvPolynomial.eval x p = 0} = 0 := by
  classical
  set μF : Measure F := Measure.addHaar with hμF
  set π : Measure (ι → F) := Measure.pi fun _ : ι => μF with hπ
  have hac : μ ≪ π := Measure.absolutelyContinuous_isAddHaarMeasure μ π
  refine hac ?_
  set σ : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hmp : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : ι => F) σ.symm)
      (Measure.pi fun _ : Fin (Fintype.card ι) => μF) π :=
    measurePreserving_piCongrLeft (fun _ : ι => μF) σ.symm
  have hZm : MeasurableSet {x : ι → F | MvPolynomial.eval x p = 0} :=
    (isClosed_singleton.preimage (MvPolynomial.continuous_eval p)).measurableSet
  rw [← hmp.measure_preimage hZm.nullMeasurableSet]
  have hcoe : ∀ g : Fin (Fintype.card ι) → F,
      ((MeasurableEquiv.piCongrLeft (fun _ : ι => F) σ.symm) g : ι → F) = g ∘ σ := by
    intro g
    funext i
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft']
  have hpre : (MeasurableEquiv.piCongrLeft (fun _ : ι => F) σ.symm) ⁻¹' {x : ι → F | MvPolynomial.eval x p = 0} =
      {g : Fin (Fintype.card ι) → F | MvPolynomial.eval g (MvPolynomial.rename σ p) = 0} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_setOf_eq, MvPolynomial.eval_rename, hcoe]
  rw [hpre]
  exact pi_fin F hF μF _ _ (fun h => hp (MvPolynomial.rename_injective _ σ.injective (h.trans (map_zero _).symm)))

end E8A.NS

theorem solution
    (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace F] [T2Space F]
    [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] (hF : ¬ DiscreteTopology F)
    (ι : Type) [Fintype ι] (p : MvPolynomial ι F) (hp : p ≠ 0)
    (μ : Measure (ι → F)) [μ.IsAddHaarMeasure] :
    μ {x : ι → F | MvPolynomial.eval x p = 0} = 0 :=
  E8A.NS.nullset F hF ι p hp μ

end S_MvPolynomial_measure_setOf_eval_eq_zero_of_ne_zero
end P2MW
export P2MW.S_MvPolynomial_measure_setOf_eval_eq_zero_of_ne_zero (solution)
