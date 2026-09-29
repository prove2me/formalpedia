-- Prove2me | solution 1 for ModularCurve.FullLevel.SemistableCovering.inducesOnChart_refl_of_drinfeldClause_of_tameCharacter_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/9766b378-50ff-53c3-a7a6-ab1a65d747cf

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_SemistableCovering_inducesOnChart_refl_of_drinfeldClause_of_tameCharacter_eq_one

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup DrinfeldCurve
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem solution
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
    (𝒞 : SemistableCovering q M' A W)
    [Algebra (GaloisField q 2) (ResidueField A)] [IsDomain (CoordRing q (ResidueField A))]
    (π : AlgebraicClosure ℚ) (ι : GaloisField q 2 →+* ResidueField A) (η : ℕ) (ζ : Idx q) (s : ↥W)
    (hD : 𝒞.DrinfeldClause π ι η ζ s) :
    ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
      SemistableCovering.InducesOnChart (𝒞.CSS s)
        (ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ) (RingEquiv.refl _) := by
  intro τ hτ h1
  obtain ⟨C, e, -, hE2⟩ := hD
  have hι : ι ((1 : (GaloisField q 2)ˣ) : GaloisField q 2) = A.tameCharacter π τ := by
    simp [h1]
  obtain ⟨⟨φ, hφ⟩, hlaw⟩ := hE2 τ hτ 1 hι
  have hd : algebraMap (ZMod q) (GaloisField q 2) ((1 : (ZMod q)ˣ) : ZMod q) =
      ((1 : (GaloisField q 2)ˣ) : GaloisField q 2) ^ (q + 1) := by simp
  have hdiag : diagOneElem q (1 : (ZMod q)ˣ) = 1 := by
    apply Units.ext
    rw [coe_diagOneElem]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hpair : ((diagOneElem q ((1 : (ZMod q)ˣ) ^ η)⁻¹, (1 : (GaloisField q 2)ˣ) ^ η) :
      Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ) = 1 := by
    simp only [one_pow, inv_one, hdiag]; rfl
  have hmem : (diagOneElem q ((1 : (ZMod q)ˣ) ^ η)⁻¹, (1 : (GaloisField q 2)ˣ) ^ η) ∈ hSubgroup q := by
    rw [hpair]; exact one_mem _
  have h1' : (⟨_, hmem⟩ : ↥(hSubgroup q)) = 1 := Subtype.ext hpair
  have key : ∀ x : 𝒞.FSS s, φ x = x := by
    intro x
    have hx := hlaw φ hφ 1 hd hmem x
    rw [h1', map_one] at hx

    have hx' : (e (φ x) : ↥(DrinfeldCurve.quotField q (ResidueField A) C)) = e x := by
      apply Subtype.ext
      simpa using hx
    exact e.injective hx'
  obtain ⟨hst, hres⟩ := hφ
  exact ⟨hst, fun f hf => by rw [hres f hf, key]; rfl⟩

end S_ModularCurve_FullLevel_SemistableCovering_inducesOnChart_refl_of_drinfeldClause_of_tameCharacter_eq_one
end P2MW
export P2MW.S_ModularCurve_FullLevel_SemistableCovering_inducesOnChart_refl_of_drinfeldClause_of_tameCharacter_eq_one (solution)
