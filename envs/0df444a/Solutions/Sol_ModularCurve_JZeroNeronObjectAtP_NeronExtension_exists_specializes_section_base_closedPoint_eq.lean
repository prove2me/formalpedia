-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_specializes_section_base_closedPoint_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/023dbad8-bab3-5d9f-bbb4-f394b00c5ecd

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension

import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_henselianLocalRing_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_AlgebraicGeometry_exists_section_comp_eq_of_smooth_of_henselianLocalRing
import Theorems.Thm_ModularCurve_inertiaField_comap_incl_and_surjective_and_isAlgClosed_residueField
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_specializes_section_base_closedPoint_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 8000000 in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (F : O.NeronExtension) (n : ↥F.Nfull)
    (hn : F.gN.base n = IsLocalRing.closedPoint ↥(shRing A)) :
    ∃ (n₀ : ↥F.Nfull) (σ : SchemeHomOver (𝟙 (shBase A)) F.gN),
      n ⤳ n₀ ∧ σ.1.base (IsLocalRing.closedPoint ↥(shRing A)) = n₀ := by
  classical
  obtain ⟨hDVR, -, -, -⟩ := ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn A p hA
  haveI : IsDiscreteValuationRing ↥(shRing A) := hDVR
  haveI : HenselianLocalRing ↥(shRing A) :=
    ValuationSubring.henselianLocalRing_comap_fixedField_inertiaSubgroupIn (K := ℚ) (L := AlgebraicClosure ℚ) A
  haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def Fact.out hA
  haveI : IsAlgClosed (ResidueField ↥(shRing A)) :=
    (ModularCurve.inertiaField_comap_incl_and_surjective_and_isAlgClosed_residueField p A hA
      (IsLocalRing.residue ↥A) IsLocalRing.residue_surjective).choose_spec.2.2.2.2.2.2
  have hNb := F.hN
  haveI := hNb.smooth
  haveI := hNb.locallyOfFiniteType

  let r : Spec (CommRingCat.of (ResidueField ↥(shRing A))) ⟶ shBase A :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥(shRing A)))
  let ξ : ↥(Spec (CommRingCat.of (ResidueField ↥(shRing A)))) := IsLocalRing.closedPoint (ResidueField ↥(shRing A))
  have hrξ : r.base ξ = IsLocalRing.closedPoint ↥(shRing A) := IsLocalRing.comap_closedPoint (IsLocalRing.residue ↥(shRing A))

  have hmem : n ∈ Set.range (pullback.fst F.gN r).base := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨ξ, hrξ.trans hn.symm⟩
  obtain ⟨m, hm⟩ := hmem

  haveI : LocallyOfFiniteType (pullback.snd F.gN r) := MorphismProperty.pullback_snd _ _ inferInstance
  haveI : JacobsonSpace ↥(pullback F.gN r) := LocallyOfFiniteType.jacobsonSpace (pullback.snd F.gN r)
  obtain ⟨m₁, hm₁c, hm₁⟩ := nonempty_inter_closedPoints (X := ↥(pullback F.gN r))
    (Z := closure {m}) ⟨m, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  rw [mem_closedPoints_iff] at hm₁

  let pt := pointOfClosedPoint (pullback.snd F.gN r) m₁ hm₁
  have hx : (pt ≫ pullback.fst F.gN r) ≫ F.gN = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥(shRing A))) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

  obtain ⟨σ, hσ₁, hσ₂⟩ := exists_section_comp_eq_of_smooth_of_henselianLocalRing F.gN (pt ≫ pullback.fst F.gN r) hx
  refine ⟨(pullback.fst F.gN r).base m₁, ⟨σ, hσ₁⟩, ?_, ?_⟩
  ·
    rw [← hm]
    exact (specializes_iff_mem_closure.mpr hm₁c).map (pullback.fst F.gN r).base.hom.continuous
  ·
    show σ.base (IsLocalRing.closedPoint ↥(shRing A)) = (pullback.fst F.gN r).base m₁
    rw [← hrξ]
    show (r ≫ σ).base ξ = _
    rw [hσ₂]
    show (pullback.fst F.gN r).base (pt.base ξ) = _
    rw [pointOfClosedPoint_apply]

#print axioms solution

end S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_specializes_section_base_closedPoint_eq
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_specializes_section_base_closedPoint_eq (solution)
