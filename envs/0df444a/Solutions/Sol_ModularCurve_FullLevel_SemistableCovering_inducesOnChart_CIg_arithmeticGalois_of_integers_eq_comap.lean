-- Prove2me | solution 1 for ModularCurve.FullLevel.SemistableCovering.inducesOnChart_CIg_arithmeticGalois_of_integers_eq_comap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/94e15ee6-0ba0-5af0-b131-25764b00b709

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Theorems.Thm_AlgebraicCurve_ComponentChart_inducesOnChart_arithmeticGalois_of_gaussPresentation_of_mem_inertiaSubgroupIn
import Theorems.Thm_ModularCurve_FullLevel_arithmeticGalois_mul_ofAlgAut_levelAutBar_of_tameCharacter_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_SemistableCovering_inducesOnChart_CIg_arithmeticGalois_of_integers_eq_comap
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel AlgebraicCurve IsLocalRing
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace IgTransport

private theorem transport
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField A) Fbar]
    {Fbar' : Type} [Field Fbar'] [Algebra (ResidueField A) Fbar']
    (C : ComponentChart A (fieldBar q M') Fbar) (C' : ComponentChart A (fieldBar q M') Fbar')
    (σ : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M')
    (hC' : C'.integers = C.integers.comap σ.toAlgHom.toRingHom)
    (g : SemilinearAut (AlgebraicClosure ℚ) (fieldBar q M'))
    (hcomm : g * SemilinearAut.ofAlgAut σ = SemilinearAut.ofAlgAut σ * g)
    (h : SemistableCovering.InducesOnChart C g (RingEquiv.refl _)) :
    SemistableCovering.InducesOnChart C' g (RingEquiv.refl _) := by
  obtain ⟨hst, hres⟩ := h
  have hc : ∀ f : fieldBar q M', g • σ f = σ (g • f) := fun f => by
    have h1 := congrArg (fun s : SemilinearAut (AlgebraicClosure ℚ) (fieldBar q M') => s • f) hcomm
    simpa only [mul_smul, SemilinearAut.ofAlgAut_smul] using h1
  have hmem : ∀ f : fieldBar q M', f ∈ C'.integers ↔ σ f ∈ C.integers := by
    intro f; rw [hC', ValuationSubring.mem_comap]; rfl
  have hst' : ∀ f : fieldBar q M', f ∈ C'.integers ↔ g • f ∈ C'.integers := by
    intro f; rw [hmem, hmem, hst (σ f), hc]
  refine ⟨hst', fun f hf => ?_⟩
  have hfσ : σ f ∈ C.integers := (hmem f).mp hf
  have hgσ : g • σ f ∈ C.integers := (hst (σ f)).mp hfσ
  have hgf : g • f ∈ C'.integers := (hst' f).mp hf

  have hy : (⟨g • σ f, hgσ⟩ - ⟨σ f, hfσ⟩ : C.integers) ∈ maximalIdeal C.integers := by
    rw [← C.ker_residue, RingHom.mem_ker, map_sub, sub_eq_zero]
    exact hres (σ f) hfσ

  have hx : (⟨g • f, hgf⟩ - ⟨f, hf⟩ : C'.integers) ∈ maximalIdeal C'.integers := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    obtain ⟨v, hv⟩ := hunit.exists_right_inv
    have hvσ : σ (v : fieldBar q M') ∈ C.integers := (hmem _).mp v.2
    have hvF : (g • f - f) * (v : fieldBar q M') = 1 := congrArg Subtype.val hv
    have hvF' : (g • σ f - σ f) * σ (v : fieldBar q M') = 1 := by
      rw [hc, ← map_sub, ← map_mul, hvF, map_one]
    have hunit' : IsUnit (⟨g • σ f, hgσ⟩ - ⟨σ f, hfσ⟩ : C.integers) :=
      IsUnit.of_mul_eq_one ⟨σ (v : fieldBar q M'), hvσ⟩ (Subtype.ext hvF')
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp hy) hunit'
  rw [← C'.ker_residue, RingHom.mem_ker, map_sub, sub_eq_zero] at hx
  exact hx

end IgTransport

theorem solution
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
    (hA : A.LiesOverPrime q) (hqM' : ¬ q ∣ M')
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (𝒞 : SemistableCovering q M' A W) (ζ : Idx q)
    (hO : ∀ f : fieldBar q M', f ∈ (𝒞.CIg (lineInfty q)).integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (ℓ : CuspidalType.ProjLine q) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (hℓ : (𝒞.CIg ℓ).integers = ((𝒞.CIg (lineInfty q)).integers).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ A.inertiaSubgroupIn ℚ) (hτπ : A.tameCharacter π τ = 1) :
    SemistableCovering.InducesOnChart (𝒞.CIg ℓ)
      (ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ) (RingEquiv.refl _) :=
  IgTransport.transport (𝒞.CIg (lineInfty q)) (𝒞.CIg ℓ) (levelAutBar q M' ζ γ) hℓ _
    (ModularCurve.FullLevel.arithmeticGalois_mul_ofAlgAut_levelAutBar_of_tameCharacter_eq_one q M' hqM' A hA π hπ hτ hτπ ζ γ hγ)
    (AlgebraicCurve.ComponentChart.inducesOnChart_arithmeticGalois_of_gaussPresentation_of_mem_inertiaSubgroupIn
      (𝒞.CIg (lineInfty q)) hO hτ)

end S_ModularCurve_FullLevel_SemistableCovering_inducesOnChart_CIg_arithmeticGalois_of_integers_eq_comap
end P2MW
export P2MW.S_ModularCurve_FullLevel_SemistableCovering_inducesOnChart_CIg_arithmeticGalois_of_integers_eq_comap (solution)
