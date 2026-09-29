-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.ProlongationDatum.nodeValueLaw_of_regularityLaw_of_typeDichotomy
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/43f778d0-4353-5ac3-a5d5-3a85c513adf5

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_nodeValueLaw_of_regularityLaw_of_typeDichotomy
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (hcomm : ∀ v, δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v) =
      qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (δ v))
    (hss : ∀ y ∈ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p, JHPlaceSpecialization.Fixed p M H hpM A δ y)
    (hreg : Rpd.RegularityLaw α β hα hβ δ SS) :
    Rpd.NodeValueLaw α β hα hβ δ SS := by
  intro f h₁ h₂ hne₁ hne₂ s hs havoid
  have hRL := hreg.2
  have hφinj : Function.Injective (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) :=
    (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (JHNeronObjectAtP.ΓN p M H hpM)).1

  obtain ⟨hyss, hs1⟩ := (mem_ssNodePairsQExp_iff s).mp ((hSS s).mp hs)
  have hfix : qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p s.2)) = s.2 := hss s.2 hyss

  have hsnd : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Psp.reduceFst α hα V = s.1 → Psp.reduceSnd β hβ δ V = s.2 := by
    intro V hV
    rcases hTD V with h | h
    · rw [hV, hs1] at h
      exact (hφinj h).symm
    · rw [hV, hs1, hcomm] at h
      rw [← h, hfix]

  have hord : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = s.1 → V.ord f = 0 := by
    intro V hV
    by_contra hne
    exact havoid V hne ⟨hV, hsnd V hV⟩

  have hf0 : f ≠ 0 := by
    rintro rfl; apply hne₁
    have : (⟨0, h₁⟩ : ↥Rpd.R₁.integers) = 0 := rfl
    rw [this, map_zero]
  have hinv : ∀ (O : ValuationSubring ↥(xHFunctionFieldBar M H)) (h : f ∈ O), IsUnit (⟨f, h⟩ : ↥O) → f⁻¹ ∈ O := by
    intro O h hu
    obtain ⟨u, hu⟩ := hu
    have hmul : f * (((u⁻¹ : (↥O)ˣ) : ↥O) : ↥(xHFunctionFieldBar M H)) = 1 := by
      have := congrArg (fun x : ↥O => (x : ↥(xHFunctionFieldBar M H))) (u.mul_inv)
      simpa [hu] using this
    have : (((u⁻¹ : (↥O)ˣ) : ↥O) : ↥(xHFunctionFieldBar M H)) = f⁻¹ := eq_inv_of_mul_eq_one_right hmul
    rw [← this]
    exact SetLike.coe_mem _
  have h₁' : f⁻¹ ∈ Rpd.R₁.integers := hinv _ h₁ (Rpd.R₁.isUnit_of_residue_ne_zero hne₁)
  have h₂' : f⁻¹ ∈ Rpd.R₂.integers := hinv _ h₂ (Rpd.R₂.isUnit_of_residue_ne_zero hne₂)

  obtain ⟨c, hc₁, hc₂⟩ := hRL f h₁ h₂ s hs (fun V hV => (hord V hV).symm.le)
  obtain ⟨c', hc₁', -⟩ := hRL f⁻¹ h₁' h₂' s hs (fun V hV => by rw [Place.ord_inv, hord V hV, neg_zero])

  have hprod : (Rpd.R₁.residue ⟨f⁻¹, h₁'⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) * Rpd.R₁.residue ⟨f, h₁⟩ = 1 := by
    rw [← map_mul, ← map_one Rpd.R₁.residue]
    congr 1
    exact Subtype.ext (inv_mul_cancel₀ hf0)
  refine ⟨c, ?_, hc₁, hc₂⟩
  rintro rfl
  have h1 := hc₁'.mul hc₁
  rw [hprod, mul_zero] at h1
  exact one_ne_zero ((Place.hasValue_one _).unique h1)

#print axioms solution

end S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_nodeValueLaw_of_regularityLaw_of_typeDichotomy
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_nodeValueLaw_of_regularityLaw_of_typeDichotomy (solution)
