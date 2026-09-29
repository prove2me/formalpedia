-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_levelAut_ord_residue_pos_and_not_of_levelOrbits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/7d6cab3c-2596-5303-b84f-86e688236f77

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_levelAut_ord_residue_pos_and_not_of_levelOrbits

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace P2mLevelOrbitsFree

open scoped Pointwise

variable {k Fbar : Type*} [Field k] [Field Fbar] [Algebra k Fbar]

theorem exists_mem_and_not_mem_of_isMaximal_ne {B : Type*} [CommRing B] {I J : Ideal B}
    (hI : I.IsMaximal) (hJ : J.IsMaximal) (hne : I ≠ J) : ∃ g ∈ I, g ∉ J := by
  by_contra h
  push Not at h
  exact hne (hI.eq_of_le hJ.ne_top fun g hg => h g hg)

end P2mLevelOrbitsFree

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (FSS : Type) [Field FSS] [Algebra (ResidueField A) FSS]
    (R : RegularProlongation A ↥(fieldBar q M') FSS)
    (hint : ∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      R.integers.comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom = R.integers)
    (N : Finset (Place (ResidueField A) FSS))

    (heqvN : ∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
        ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
      ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField ↥A) FSS),
        (R.resAut τ hτ • Q ∈ N ↔ Q ∈ N))

    (hfree : ∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N →
      ∃ (ζ : Idx q) (γ : SL(2, ℤ)) (_ : γ ∈ Gamma0 M')
        (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ f ∈ R.integers ↔ f ∈ R.integers),
        R.resAut (levelAutBar q M' ζ γ) hτ • Q ≠ Q)

    (C : ComponentChart A ↥(fieldBar q M') FSS)
    (hCR : C.integers = R.integers)
    (hCres : ∀ (f : ↥(fieldBar q M')) (hC : f ∈ C.integers) (hR : f ∈ R.integers), C.residue ⟨f, hC⟩ = R.residue ⟨f, hR⟩)

    (hdict : (∀ 𝔪 : Ideal ↥(⨅ (Q : Place (ResidueField A) FSS) (_ : Q ∉ N), Q.toValuationSubring.toSubring), 𝔪.IsMaximal →
          ∃! Q : Place (ResidueField A) FSS, Q ∉ N ∧
            ∀ g : ↥(⨅ (Q : Place (ResidueField A) FSS) (_ : Q ∉ N), Q.toValuationSubring.toSubring), g ∈ 𝔪 ↔ (g : FSS) = 0 ∨ 0 < Q.ord (g : FSS)) ∧
        ∀ Q : Place (ResidueField A) FSS, Q ∉ N →
          ∃ 𝔪 : Ideal ↥(⨅ (Q : Place (ResidueField A) FSS) (_ : Q ∉ N), Q.toValuationSubring.toSubring), 𝔪.IsMaximal ∧
            ∀ g : ↥(⨅ (Q : Place (ResidueField A) FSS) (_ : Q ∉ N), Q.toValuationSubring.toSubring), g ∈ 𝔪 ↔ (g : FSS) = 0 ∨ 0 < Q.ord (g : FSS))

    (hlift : ∀ g : FSS, (∀ Q : Place (ResidueField A) FSS, Q ∉ N → g ∈ Q.toValuationSubring) →
      ∃ (f : ↥(fieldBar q M')) (hf : f ∈ C.integers),
        (∀ P ∈ C.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) ∧ C.residue ⟨f, hf⟩ = g) :

    (∀ Q : Place (ResidueField A) FSS, Q ∉ N →
      ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧
        ∃ (f : ↥(fieldBar q M')) (hf : f ∈ C.integers) (hf' : levelAutBar q M' ζ γ f ∈ C.integers),
          (∀ P ∈ C.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) ∧
          0 < Q.ord (C.residue ⟨f, hf⟩) ∧ ¬ 0 < Q.ord (C.residue ⟨levelAutBar q M' ζ γ f, hf'⟩)) := by
  intro Q hQ

  obtain ⟨ζ, γ, hγ, hτ, hmove⟩ := hfree Q hQ
  set τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') := levelAutBar q M' ζ γ with hτdef
  set σ : FSS ≃ₐ[ResidueField A] FSS := R.resAut τ hτ with hσdef

  set Q' : Place (ResidueField A) FSS := σ⁻¹ • Q with hQ'def
  have hσQ' : σ • Q' = Q := by rw [hQ'def, smul_inv_smul]
  have hQ'ne : Q' ≠ Q := by
    intro h
    apply hmove
    have : σ • Q' = σ • Q := by rw [h]
    rw [hσQ'] at this
    exact this.symm

  have hτmem : τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
      ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ} :=
    Subgroup.subset_closure ⟨ζ, γ, hγ, rfl⟩
  have hQ'N : Q' ∉ N := by
    intro h
    have := (heqvN τ hτmem hτ Q').mpr h
    rw [hσQ'] at this
    exact hQ this

  obtain ⟨huniq, hexist⟩ := hdict
  obtain ⟨𝔪, h𝔪max, h𝔪⟩ := hexist Q hQ
  obtain ⟨𝔪', h𝔪'max, h𝔪'⟩ := hexist Q' hQ'N
  have hne : 𝔪 ≠ 𝔪' := by
    intro heq
    obtain ⟨Q₀, _, hQ₀uniq⟩ := huniq 𝔪 h𝔪max
    have h1 : Q = Q₀ := hQ₀uniq Q ⟨hQ, h𝔪⟩
    have h2 : Q' = Q₀ := hQ₀uniq Q' ⟨hQ'N, by rw [heq]; exact h𝔪'⟩
    exact hQ'ne (h2.trans h1.symm)
  obtain ⟨g, hg𝔪, hg𝔪'⟩ := P2mLevelOrbitsFree.exists_mem_and_not_mem_of_isMaximal_ne h𝔪max h𝔪'max hne
  have hgQ' : ¬ ((g : FSS) = 0 ∨ 0 < Q'.ord (g : FSS)) := fun h => hg𝔪' ((h𝔪' g).mpr h)
  have hg0 : (g : FSS) ≠ 0 := fun h => hgQ' (Or.inl h)
  have hgQ : 0 < Q.ord (g : FSS) := ((h𝔪 g).mp hg𝔪).resolve_left hg0
  have hgQ'ord : ¬ 0 < Q'.ord (g : FSS) := fun h => hgQ' (Or.inr h)

  have hgreg : ∀ Q'' : Place (ResidueField A) FSS, Q'' ∉ N → (g : FSS) ∈ Q''.toValuationSubring := by
    intro Q'' hQ''
    have hmem := g.2
    rw [Subring.mem_iInf] at hmem
    have hmem' := hmem Q''
    rw [Subring.mem_iInf] at hmem'
    exact hmem' hQ''

  obtain ⟨f, hfC, hftube, hfres⟩ := hlift (g : FSS) hgreg
  have hfR : f ∈ R.integers := hCR ▸ hfC
  have hτfR : τ f ∈ R.integers := (hτ f).mpr hfR
  have hτfC : τ f ∈ C.integers := hCR ▸ hτfR
  refine ⟨ζ, γ, hγ, f, hfC, hτfC, hftube, ?_, ?_⟩
  · rw [hfres]; exact hgQ
  ·
    have hres : C.residue ⟨τ f, hτfC⟩ = σ (g : FSS) := by
      rw [hCres (τ f) hτfC hτfR, ← hfres, hCres f hfC hfR, hσdef,
        RegularProlongation.resAut_residue]
    rw [hres, ← hσQ', Place.ord_smul σ Q' (g : FSS)]
    exact hgQ'ord

end S_ModularCurve_FullLevel_exists_levelAut_ord_residue_pos_and_not_of_levelOrbits
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_levelAut_ord_residue_pos_and_not_of_levelOrbits (solution)
