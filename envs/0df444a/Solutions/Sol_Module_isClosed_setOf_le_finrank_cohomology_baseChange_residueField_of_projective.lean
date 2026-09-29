-- Prove2me | solution 1 for Module.isClosed_setOf_le_finrank_cohomology_baseChange_residueField_of_projective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/73edff57-9e36-5654-91a0-6e089114f3ad

import Mathlib
import Theorems.Thm_TwoChartCech_isClosed_setOf_le_finrank_ker_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_isClosed_setOf_le_finrank_cohomology_baseChange_residueField_of_projective
p2m_attr_erase "simp" "CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq"

set_option autoImplicit false

universe u

open TensorProduct
open CategoryTheory AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
    [∀ i, Module.Finite R (K i)] [∀ i, Module.Projective R (K i)]
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hδδ : ∀ i, δ (i + 1) ∘ₗ δ i = 0) (r : ℕ) :
    IsClosed {q : PrimeSpectrum R | r ≤ Module.finrank q.asIdeal.ResidueField
        ↥(LinearMap.ker ((δ 0).baseChange q.asIdeal.ResidueField))} ∧
      ∀ i : ℕ, IsClosed {q : PrimeSpectrum R |
        r + Module.finrank q.asIdeal.ResidueField
            ↥((LinearMap.range ((δ i).baseChange q.asIdeal.ResidueField)).comap
              (LinearMap.ker ((δ (i + 1)).baseChange q.asIdeal.ResidueField)).subtype) ≤
          Module.finrank q.asIdeal.ResidueField
            ↥(LinearMap.ker ((δ (i + 1)).baseChange q.asIdeal.ResidueField))} := by
  classical

  have hz : ∀ (j n : ℕ), IsClosed {q : PrimeSpectrum R | n ≤ Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ j).baseChange q.asIdeal.ResidueField))} := by
    intro j n
    exact TwoChartCech.isClosed_setOf_le_finrank_ker_baseChange (δ j) (𝟙 (Spec (.of R))) n
  refine ⟨hz 0 r, fun i => ?_⟩

  have hpt : ∀ q : PrimeSpectrum R, Module.finrank q.asIdeal.ResidueField ↥((LinearMap.range ((δ i).baseChange q.asIdeal.ResidueField)).comap (LinearMap.ker ((δ (i + 1)).baseChange q.asIdeal.ResidueField)).subtype) + Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ i).baseChange q.asIdeal.ResidueField)) = Module.rankAtStalk (K i) q := by
    intro q
    have hle : LinearMap.range ((δ i).baseChange q.asIdeal.ResidueField) ≤ LinearMap.ker ((δ (i + 1)).baseChange q.asIdeal.ResidueField) := by
      rintro _ ⟨x, rfl⟩
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hδδ i]
      simp
    rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq, Module.rankAtStalk_eq]
    exact LinearMap.finrank_range_add_finrank_ker _

  have hset : {q : PrimeSpectrum R | r + Module.finrank q.asIdeal.ResidueField ↥((LinearMap.range ((δ i).baseChange q.asIdeal.ResidueField)).comap (LinearMap.ker ((δ (i + 1)).baseChange q.asIdeal.ResidueField)).subtype) ≤ Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ (i + 1)).baseChange q.asIdeal.ResidueField))} =
      {q : PrimeSpectrum R | r + Module.rankAtStalk (K i) q ≤ Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ (i + 1)).baseChange q.asIdeal.ResidueField)) + Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ i).baseChange q.asIdeal.ResidueField))} := by
    ext q
    simp only [Set.mem_setOf_eq]
    have h := hpt q
    constructor
    · intro h'; omega
    · intro h'; omega
  rw [hset]

  have hsum : ∀ m : ℕ, IsClosed {q : PrimeSpectrum R | m ≤ Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ (i + 1)).baseChange q.asIdeal.ResidueField)) + Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ i).baseChange q.asIdeal.ResidueField))} := by
    intro m
    have heq : {q : PrimeSpectrum R | m ≤ Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ (i + 1)).baseChange q.asIdeal.ResidueField)) + Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ i).baseChange q.asIdeal.ResidueField))} =
        ⋃ a ∈ Finset.range (m + 1),
          ({q : PrimeSpectrum R | a ≤ Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ (i + 1)).baseChange q.asIdeal.ResidueField))} ∩ {q : PrimeSpectrum R | m - a ≤ Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ i).baseChange q.asIdeal.ResidueField))}) := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Finset.mem_range, exists_prop]
      constructor
      · intro h
        exact ⟨min m (Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ (i + 1)).baseChange q.asIdeal.ResidueField))), by omega, by omega, by omega⟩
      · rintro ⟨a, ha, h1, h2⟩
        omega
    rw [heq]
    exact isClosed_biUnion_finset fun a _ => (hz (i + 1) a).inter (hz i (m - a))

  haveI : Module.FinitePresentation R (K i) := Module.finitePresentation_of_projective R (K i)
  have hρ : IsLocallyConstant (Module.rankAtStalk (R := R) (K i)) := Module.isLocallyConstant_rankAtStalk
  rw [← isOpen_compl_iff]
  have hcompl : {q : PrimeSpectrum R | r + Module.rankAtStalk (K i) q ≤ Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ (i + 1)).baseChange q.asIdeal.ResidueField)) + Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ i).baseChange q.asIdeal.ResidueField))}ᶜ =
      ⋃ c : ℕ, ({q : PrimeSpectrum R | Module.rankAtStalk (K i) q = c} ∩
        {q : PrimeSpectrum R | r + c ≤ Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ (i + 1)).baseChange q.asIdeal.ResidueField)) + Module.finrank q.asIdeal.ResidueField ↥(LinearMap.ker ((δ i).baseChange q.asIdeal.ResidueField))}ᶜ) := by
    ext q
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨_, rfl, h⟩
    · rintro ⟨c, rfl, h⟩
      exact h
  rw [hcompl]
  exact isOpen_iUnion fun c => (hρ.isOpen_fiber c).inter (hsum (r + c)).isOpen_compl

end S_Module_isClosed_setOf_le_finrank_cohomology_baseChange_residueField_of_projective
end P2MW
export P2MW.S_Module_isClosed_setOf_le_finrank_cohomology_baseChange_residueField_of_projective (solution)
