-- Prove2me | solution 1 for MeasureTheory.Measure.exists_haar_eq_smul_map_mul_prod_of_homeomorph
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c92a0ced-125d-5e28-a390-637e3000bf93

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_Measure_exists_haar_eq_smul_map_mul_prod_of_homeomorph

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace P2mHaarProduct

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (T S : Subgroup G) [MeasurableSpace T] [BorelSpace T] [MeasurableSpace S] [BorelSpace S]
  (e : T × S ≃ₜ G)

theorem isClosed_left (he : ∀ p : T × S, e p = (p.1 : G) * (p.2 : G)) : IsClosed (T : Set G) := by
  have h : (T : Set G) = e '' ((Set.univ : Set T) ×ˢ ({1} : Set S)) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_image, Set.mem_prod, Set.mem_univ, true_and, Set.mem_singleton_iff,
      Prod.exists]
    constructor
    · intro hg; exact ⟨⟨g, hg⟩, 1, rfl, by rw [he]; simp⟩
    · rintro ⟨t, s, rfl, rfl⟩; rw [he]; simpa using t.2
  rw [h]
  exact (e.isClosedMap _ (isClosed_univ.prod isClosed_singleton))

theorem isClosed_right (he : ∀ p : T × S, e p = (p.1 : G) * (p.2 : G)) : IsClosed (S : Set G) := by
  have h : (S : Set G) = e '' (({1} : Set T) ×ˢ (Set.univ : Set S)) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_image, Set.mem_prod, Set.mem_univ, and_true, Set.mem_singleton_iff,
      Prod.exists]
    constructor
    · intro hg; exact ⟨1, ⟨g, hg⟩, rfl, by rw [he]; simp⟩
    · rintro ⟨t, s, rfl, rfl⟩; rw [he]; simpa using s.2
  rw [h]
  exact (e.isClosedMap _ (isClosed_singleton.prod isClosed_univ))

theorem exists_haar_eq_smul_map (he : ∀ p : T × S, e p = (p.1 : G) * (p.2 : G))
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (τ : Measure T) [τ.IsHaarMeasure]
    (ν : Measure S) [IsFiniteMeasureOnCompacts ν] [ν.IsMulRightInvariant] [ν.IsOpenPosMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • Measure.map e (τ.prod ν) := by

  haveI : LocallyCompactSpace T := (isClosed_left T S e he).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace S := (isClosed_right T S e he).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology T := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _

  set e' : T × S ≃ₜ G := ((Homeomorph.refl T).prodCongr (Homeomorph.inv S)).trans e with he'def
  haveI : BorelSpace (T × S) := Prod.borelSpace
  have he' : ∀ p : T × S, e' p = (p.1 : G) * ((p.2 : S) : G)⁻¹ := by
    rintro ⟨t, s⟩
    change e (t, s⁻¹) = _
    rw [he, Subgroup.coe_inv]
  set em : T × S ≃ᵐ G := e'.toMeasurableEquiv with hemdef
  have hem : (em : T × S → G) = e' := e'.toMeasurableEquiv_coe
  have hems : (em.symm : G → T × S) = e'.symm := e'.toMeasurableEquiv_symm_coe

  set ρ : Measure (T × S) := Measure.map em.symm μ with hρdef
  have hρapply : ∀ A : Set (T × S), ρ A = μ (e' '' A) := by
    intro A
    rw [hρdef, MeasurableEquiv.map_apply, hems, ← e'.image_eq_preimage_symm]

  haveI : ρ.IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    obtain ⟨t₀, s₀⟩ := g
    set L : G → G := fun x => (t₀ : G) * x * ((s₀ : S) : G)⁻¹ with hL
    have hLm : Measurable L := ((continuous_const.mul continuous_id).mul continuous_const).measurable
    have hcomp : (fun p : T × S => (t₀, s₀) * p) ∘ (em.symm : G → T × S) = (em.symm : G → T × S) ∘ L := by
      funext x
      obtain ⟨q, rfl⟩ := e'.surjective x
      simp only [Function.comp_apply, hems, e'.symm_apply_apply]
      apply e'.injective
      rw [e'.apply_symm_apply, Prod.mk_mul_mk, he', he']
      simp only [Subgroup.coe_mul, mul_inv_rev, hL]
      group
    have hLμ : Measure.map L μ = μ := by
      have : L = (fun x => x * ((s₀ : S) : G)⁻¹) ∘ (fun x => (t₀ : G) * x) := by funext x; rfl
      rw [this, ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _), map_mul_left_eq_self,
        map_mul_right_eq_self]
    rw [hρdef, Measure.map_map (measurable_const_mul _) em.symm.measurable, hcomp,
      ← Measure.map_map em.symm.measurable hLm, hLμ]

  haveI : IsFiniteMeasureOnCompacts ρ := ⟨fun K hK => by
    rw [hρapply]; exact (hK.image e'.continuous).measure_lt_top⟩
  haveI : ρ.IsOpenPosMeasure := ⟨fun U hU hne => by
    rw [hρapply]; exact ((e'.isOpenMap U hU).measure_pos μ (hne.image _)).ne'⟩
  haveI : ρ.IsHaarMeasure := {}

  haveI : ν.inv.IsHaarMeasure := {}
  haveI : (τ.prod ν.inv).IsHaarMeasure := Measure.prod.instIsHaarMeasure τ ν.inv

  set c : ℝ≥0 := ρ.haarScalarFactor (τ.prod ν.inv) with hcdef
  have hρc : ρ = c • (τ.prod ν.inv) := Measure.isMulLeftInvariant_eq_smul ρ (τ.prod ν.inv)
  have hcpos : 0 < c := Measure.haarScalarFactor_pos_of_isHaarMeasure ρ (τ.prod ν.inv)
  refine ⟨(c : ℝ≥0∞), by exact_mod_cast hcpos.ne', ENNReal.coe_ne_top, ?_⟩

  have hμ : μ = Measure.map em ρ := by rw [hρdef, MeasurableEquiv.map_map_symm]
  have hprod : Measure.map em (τ.prod ν.inv) = Measure.map e (τ.prod ν) := by
    have hfun : (em : T × S → G) = e ∘ Prod.map id Inv.inv := by
      rw [hem]; funext p; obtain ⟨t, s⟩ := p; rw [he', Function.comp_apply, Prod.map_apply, he]; simp
    rw [hfun, ← Measure.map_map e.continuous.measurable (measurable_id.prodMap measurable_inv),
      ← Measure.map_prod_map τ ν.inv measurable_id measurable_inv, Measure.map_id, ← Measure.inv_def,
      Measure.inv_inv]
  rw [hμ, hρc, Measure.map_smul, hprod, ENNReal.smul_def]

end P2mHaarProduct

open MeasureTheory in
open scoped ENNReal in
theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T S : Subgroup G) [MeasurableSpace T] [BorelSpace T] [MeasurableSpace S] [BorelSpace S]
    (e : T × S ≃ₜ G) (he : ∀ p : T × S, e p = (p.1 : G) * (p.2 : G))
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (τ : Measure T) [τ.IsHaarMeasure]
    (ν : Measure S) [IsFiniteMeasureOnCompacts ν] [ν.IsMulRightInvariant] [ν.IsOpenPosMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • Measure.map e (τ.prod ν) :=
  P2mHaarProduct.exists_haar_eq_smul_map T S e he μ τ ν

end
end S_MeasureTheory_Measure_exists_haar_eq_smul_map_mul_prod_of_homeomorph
end P2MW
export P2MW.S_MeasureTheory_Measure_exists_haar_eq_smul_map_mul_prod_of_homeomorph (solution)
