-- Prove2me | solution 1 for ModularCurve.FullLevel.SemistableCovering.inertiaClause_of_gaussPresentation_of_integers_eq_comap_of_discs
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/bcc02cac-b6d6-5d36-9b18-41b407b2601c

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Theorems.Thm_ModularCurve_FullLevel_SemistableCovering_inducesOnChart_CIg_arithmeticGalois_of_integers_eq_comap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_SemistableCovering_inertiaClause_of_gaussPresentation_of_integers_eq_comap_of_discs
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel ModularCurve.FullLevel.SemistableCovering AlgebraicCurve IsLocalRing CongruenceSubgroup

open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

private theorem placeMap_comp_eq_and_mem_dom_iff_of_discs {X Y : Type*} (dom : Set X) (placeMap : X → Y) (φ : X → X)
    (N : Finset Y) (disc : Y → Set X)
    (h1 : ∀ P, P ∈ dom ↔ ∃ Q, Q ∉ N ∧ P ∈ disc Q)
    (h2 : ∀ P Q, Q ∉ N → P ∈ disc Q → placeMap P = Q)
    (h3 : ∀ P P', P ∉ dom → P' ∉ dom → placeMap P = placeMap P')
    (h4 : ∀ Q, Q ∉ N → ∀ P, P ∈ disc Q ↔ φ P ∈ disc Q) :
    (∀ P, placeMap (φ P) = placeMap P) ∧ (∀ P, P ∈ dom ↔ φ P ∈ dom) := by
  have hdom : ∀ P, P ∈ dom ↔ φ P ∈ dom := fun P => by
    rw [h1, h1]
    exact exists_congr (fun Q => and_congr_right (fun hQ => h4 Q hQ P))
  refine ⟨fun P => ?_, hdom⟩
  by_cases hP : P ∈ dom
  · obtain ⟨Q, hQ, hPQ⟩ := (h1 P).mp hP
    rw [h2 P Q hQ hPQ, h2 (φ P) Q hQ ((h4 Q hQ P).mp hPQ)]
  · exact h3 _ _ (fun h => hP ((hdom P).mpr h)) hP

theorem solution
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
    (hA : A.LiesOverPrime q) (hqM' : ¬ q ∣ M')
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (𝒞 : SemistableCovering q M' A W) (ζ : Idx q)

    (hO : ∀ f : fieldBar q M', f ∈ (𝒞.CIg (lineInfty q)).integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hℓ : ∀ ℓ : CuspidalType.ProjLine q, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧
      (𝒞.CIg ℓ).integers = ((𝒞.CIg (lineInfty q)).integers).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)

    (hIg_discs : ∀ ℓ : CuspidalType.ProjLine q,
      ∃ (N : Finset (Place (ResidueField A) (𝒞.FIg ℓ)))
        (disc : Place (ResidueField A) (𝒞.FIg ℓ) → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
        (∀ P, P ∈ (𝒞.CIg ℓ).dom ↔ ∃ Q, Q ∉ N ∧ P ∈ disc Q) ∧
        (∀ P Q, Q ∉ N → P ∈ disc Q → (𝒞.CIg ℓ).placeMap P = Q) ∧
        (∀ P P', P ∉ (𝒞.CIg ℓ).dom → P' ∉ (𝒞.CIg ℓ).dom → (𝒞.CIg ℓ).placeMap P = (𝒞.CIg ℓ).placeMap P') ∧
        (∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
          ∀ Q, Q ∉ N → ∀ P, P ∈ disc Q ↔ ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • P ∈ disc Q))

    (hSS_ind : ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
      ∀ s : ↥W, InducesOnChart (𝒞.CSS s) (ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ) (RingEquiv.refl _))
    (hSS_discs : ∀ s : ↥W,
      ∃ (N : Finset (Place (ResidueField A) (𝒞.FSS s)))
        (disc : Place (ResidueField A) (𝒞.FSS s) → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
        (∀ P, P ∈ (𝒞.CSS s).dom ↔ ∃ Q, Q ∉ N ∧ P ∈ disc Q) ∧
        (∀ P Q, Q ∉ N → P ∈ disc Q → (𝒞.CSS s).placeMap P = Q) ∧
        (∀ P P', P ∉ (𝒞.CSS s).dom → P' ∉ (𝒞.CSS s).dom → (𝒞.CSS s).placeMap P = (𝒞.CSS s).placeMap P') ∧
        (∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
          ∀ Q, Q ∉ N → ∀ P, P ∈ disc Q ↔ ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • P ∈ disc Q))

    (hAn_dom : ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
      ∀ (ℓ : CuspidalType.ProjLine q) (s : ↥W) (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')),
        P ∈ (𝒞.An ℓ s).dom ↔ ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • P ∈ (𝒞.An ℓ s).dom)
    (hAn_param : ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
      ∀ (ℓ : CuspidalType.ProjLine q) (s : ↥W), ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (𝒞.An ℓ s).param = (𝒞.An ℓ s).param)
    (hAn'_param : ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
      ∀ (ℓ : CuspidalType.ProjLine q) (s : ↥W), ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (𝒞.An' ℓ s).param = (𝒞.An' ℓ s).param) :
    𝒞.InertiaClause π := by
  intro τ hτ hτπ g
  refine ⟨fun ℓ => ?_, fun s => ?_, fun ℓ s => ?_⟩
  · obtain ⟨γ, hγ, hℓγ⟩ := hℓ ℓ
    obtain ⟨N, disc, h1, h2, h3, h4⟩ := hIg_discs ℓ
    have key := placeMap_comp_eq_and_mem_dom_iff_of_discs (𝒞.CIg ℓ).dom (𝒞.CIg ℓ).placeMap (fun P => g • P) N disc
      h1 h2 h3 (h4 τ hτ hτπ)
    exact ⟨SemistableCovering.inducesOnChart_CIg_arithmeticGalois_of_integers_eq_comap hA hqM' π hπ 𝒞 ζ hO ℓ γ hγ hℓγ hτ hτπ,
      key.1, key.2⟩
  · obtain ⟨N, disc, h1, h2, h3, h4⟩ := hSS_discs s
    have key := placeMap_comp_eq_and_mem_dom_iff_of_discs (𝒞.CSS s).dom (𝒞.CSS s).placeMap (fun P => g • P) N disc
      h1 h2 h3 (h4 τ hτ hτπ)
    exact ⟨hSS_ind τ hτ hτπ s, key.1, key.2⟩
  · exact ⟨hAn_dom τ hτ hτπ ℓ s, hAn_param τ hτ hτπ ℓ s, hAn'_param τ hτ hτπ ℓ s⟩

end S_ModularCurve_FullLevel_SemistableCovering_inertiaClause_of_gaussPresentation_of_integers_eq_comap_of_discs
end P2MW
export P2MW.S_ModularCurve_FullLevel_SemistableCovering_inertiaClause_of_gaussPresentation_of_integers_eq_comap_of_discs (solution)
