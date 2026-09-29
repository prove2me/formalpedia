-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_mem_eq_cx_mul_unit_isUnit_of_commonChart_of_igusaSep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/93a54d6f-237a-5af9-bfee-983308c1fc74

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Theorems.Thm_ModularCurve_FullLevel_exists_pow_eq_mul_nonunit_of_mem_maximalIdeal_igusaBranch_of_node_crossingPresentation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_mem_eq_cx_mul_unit_isUnit_of_commonChart_of_igusaSep
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal"

set_option autoImplicit false

namespace Sep2Half

open IsLocalRing

theorem isUnit_add_of_isUnit_of_not_isUnit {R : Type*} [CommRing R] [IsLocalRing R] (a b : R)
    (ha : IsUnit a) (hb : ¬ IsUnit b) : IsUnit (a + b) := by
  by_contra hab
  have hb' : b ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hb
  have hab' : a + b ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hab
  have ha' : a ∈ maximalIdeal R := by simpa using sub_mem hab' hb'
  exact (mem_maximalIdeal _).mp ha' ha

end Sep2Half

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')) (W₀ : ValuationSubring ↥F₀),
      ((∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ W₀) ∧
      IsDiscreteValuationRing ↥W₀ ∧
      (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ W₀, maximalIdeal ↥W₀ = Ideal.span {(⟨_, hπW⟩ : ↥W₀)})) →
    ∀ (O : Subring ↥F₀) [IsLocalRing ↥O] [IsNoetherianRing ↥O],
      (∀ f : ↥F₀, f ∈ O → f ∈ W₀) →
      (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ O) →
      (∀ (f : ↥F₀) (hf : f ∈ O), ∃ (x : ↥k₀) (hx : algebraMap ↥k₀ ↥F₀ x ∈ O), (x : (AlgebraicClosure ℚ)) ∈ A ∧
              ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, hx⟩)) →
      (∀ f : ↥F₀, ∃ g h : ↥F₀, g ∈ O ∧ h ∈ O ∧ h ≠ 0 ∧ f * h = g) →
    ∀ (E₀ : ℕ) (_ : 1 ≤ E₀) (hπO : algebraMap ↥k₀ ↥F₀ π₀ ∈ O) (cx cy : ↥O) (u : (↥O)ˣ)
      (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))
      (γU γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))ˣ),
      cx * cy = (⟨_, hπO⟩ : ↥O) ^ E₀ * (u : ↥O) →
      (∀ (x : ↥k₀) (hx : (x : (AlgebraicClosure ℚ)) ∈ A) (hxO : algebraMap ↥k₀ ↥F₀ x ∈ O),
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hxO⟩) =
                  UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨x, hx⟩)) →
      ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = (γU : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) →
      ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = (γV : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) →
    ∀ (Wx : ValuationSubring ↥F₀),
      (∀ f : ↥F₀, f ∈ O → f ∈ Wx) →
      IsDiscreteValuationRing ↥Wx →
      (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ Wx, maximalIdeal ↥Wx = Ideal.span {(⟨_, hπW⟩ : ↥Wx)}) →
      (∀ hcx : (cx : ↥F₀) ∈ Wx, (⟨(cx : ↥F₀), hcx⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
      (∀ hcy : (cy : ↥F₀) ∈ Wx, (⟨(cy : ↥F₀), hcy⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) →
    ∀ (O' : Subring ↥F₀) [IsLocalRing ↥O'] (Bc : Subring ↥F₀),
      (∀ f : ↥F₀, f ∈ Bc → f ∈ O) → (∀ f : ↥F₀, f ∈ Bc → f ∈ O') →
      (∀ f : ↥F₀, f ∈ O ↔ ∃ g h : ↥F₀, g ∈ Bc ∧ h ∈ Bc ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g) →
      (∀ f : ↥F₀, f ∈ O' ↔ ∃ g h : ↥F₀, g ∈ Bc ∧ h ∈ Bc ∧ (∀ hh : h ∈ O', IsUnit (⟨h, hh⟩ : ↥O')) ∧ f * h = g) →

      (∃ f : ↥F₀, f ∈ O' ∧ f ∉ Wx) →
      ∃ (g : ↥F₀) (hg : g ∈ O) (hg' : g ∈ O'),
        (∃ (v : ↥O), IsUnit v ∧ (⟨g, hg⟩ : ↥O) = cx * v) ∧ IsUnit (⟨g, hg'⟩ : ↥O') := by
  intro F₀ W₀ hW₀ O _ _ hOW₀ hAO hresO hfrac E₀ hE₀ hπO cx cy u ι γU γV hcxcy hconst hcx hcy Wx hOWx hWxdvr
    hπW hcxW hcyW O' _ Bc hBcO hBcO' hOloc hO'loc hsep

  have hpow := ModularCurve.FullLevel.exists_pow_eq_mul_nonunit_of_mem_maximalIdeal_igusaBranch_of_node_crossingPresentation
    q hq M' hqM' A hA k₀ π₀ hπ hdvr hunif hhens hres hκ F₀ W₀ hW₀ O hOW₀ hAO hresO hfrac E₀ hE₀ hπO cx cy u ι γU γV
    hcxcy hconst hcx hcy Wx hOWx hWxdvr hπW hcxW hcyW

  obtain ⟨t, s, htB, hsB, hsU, hcxs⟩ := (hOloc (cx : ↥F₀)).mp cx.2
  have hsO : s ∈ O := hBcO _ hsB
  have htO : t ∈ O := hBcO _ htB
  have htO' : t ∈ O' := hBcO' _ htB
  have hsunit : IsUnit (⟨s, hsO⟩ : ↥O) := hsU hsO
  have ht_eq : (⟨t, htO⟩ : ↥O) = cx * ⟨s, hsO⟩ := Subtype.ext hcxs.symm

  obtain ⟨f, hfO', hfW⟩ := hsep
  obtain ⟨g₀, h, hg₀B, hhB, hhU, hfh⟩ := (hO'loc f).mp hfO'
  have hhO : h ∈ O := hBcO _ hhB
  have hhO' : h ∈ O' := hBcO' _ hhB
  have hhunit' : IsUnit (⟨h, hhO'⟩ : ↥O') := hhU hhO'

  have hhW : ∀ hb : (((⟨h, hhO⟩ : ↥O) : ↥F₀)) ∈ Wx, (⟨((⟨h, hhO⟩ : ↥O) : ↥F₀), hb⟩ : ↥Wx) ∈ maximalIdeal ↥Wx := by
    intro hb
    by_contra hnot
    apply hfW
    have hu : IsUnit (⟨h, hb⟩ : ↥Wx) := IsLocalRing.notMem_maximalIdeal.mp hnot
    have h1 : Wx.valuation h = 1 := (Wx.valuation_eq_one_iff ⟨h, hb⟩).mp hu
    have hg₀le : Wx.valuation g₀ ≤ 1 := (Wx.valuation_le_one_iff _).mpr (hOWx _ (hBcO _ hg₀B))
    rw [← hfh, map_mul, h1, mul_one] at hg₀le
    exact (Wx.valuation_le_one_iff _).mp hg₀le
  obtain ⟨m, hm, hpow'⟩ := hpow ⟨h, hhO⟩ hhW
  by_cases htU' : IsUnit (⟨t, htO'⟩ : ↥O')
  · exact ⟨t, htO, htO', ⟨⟨s, hsO⟩, hsunit, ht_eq⟩, htU'⟩
  · refine ⟨t + h ^ (E₀ + 1), add_mem htO (pow_mem hhO _), add_mem htO' (pow_mem hhO' _), ?_, ?_⟩
    · refine ⟨⟨s, hsO⟩ + m, Sep2Half.isUnit_add_of_isUnit_of_not_isUnit _ _ hsunit hm, ?_⟩
      have e1 : (⟨t + h ^ (E₀ + 1), add_mem htO (pow_mem hhO _)⟩ : ↥O) = ⟨t, htO⟩ + ⟨h, hhO⟩ ^ (E₀ + 1) :=
        Subtype.ext (by simp)
      rw [e1, ht_eq, hpow', mul_add]
    · have e2 : (⟨t + h ^ (E₀ + 1), add_mem htO' (pow_mem hhO' _)⟩ : ↥O') = ⟨h, hhO'⟩ ^ (E₀ + 1) + ⟨t, htO'⟩ :=
        Subtype.ext (by simp [add_comm])
      rw [e2]
      exact Sep2Half.isUnit_add_of_isUnit_of_not_isUnit _ _ (hhunit'.pow _) htU'

end S_ModularCurve_FullLevel_exists_mem_eq_cx_mul_unit_isUnit_of_commonChart_of_igusaSep
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_mem_eq_cx_mul_unit_isUnit_of_commonChart_of_igusaSep (solution)
