-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Giv.ResProj.sameOrbit_of_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:18:37.554098+00:00
-- url     : https://prove2.me/submissions/d2ab8e77-31ee-4c26-ac76-a88d2420603d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MultihomogeneousNonvanishingOnJoin
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_evC_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_proportional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Giv
open GlobalTheory.CompanionTheory.Ar.Giv.ResProj
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
variable {M : ℕ}
local notation "𝔅" => (fun _ : Unit => Fin M)
namespace GlobalTheory.CompanionTheory.Ar.Giv.ResProj
theorem _root_.solution {G : Fin M → MRing ι} {g : K → ℕ} (hG : ∀ i, IsMultiHomog (G i) g)
    {z u : (Σ k, joinIdx ι 𝔅 k) → ℂ}
    (hzb : ∃ i : Fin M, z ⟨Sum.inr (), i⟩ ≠ 0) (hub : ∃ i : Fin M, u ⟨Sum.inr (), i⟩ ≠ 0)
    (hzc : ∀ i j : Fin M, z ⟨Sum.inr (), i⟩ * evC (z ∘ joinInl ι 𝔅) (G j) =
      z ⟨Sum.inr (), j⟩ * evC (z ∘ joinInl ι 𝔅) (G i))
    (huc : ∀ i j : Fin M, u ⟨Sum.inr (), i⟩ * evC (u ∘ joinInl ι 𝔅) (G j) =
      u ⟨Sum.inr (), j⟩ * evC (u ∘ joinInl ι 𝔅) (G i))
    (ho : SameOrbit (z ∘ joinInl ι 𝔅) (u ∘ joinInl ι 𝔅))
    {l : Fin M} (hl : evC (z ∘ joinInl ι 𝔅) (G l) ≠ 0) : SameOrbit z u := by
  obtain ⟨c, hc, hcz⟩ := ho
  have e : ∀ i, evC (z ∘ joinInl ι 𝔅) (G i) = (∏ k, c k ^ g k) * evC (u ∘ joinInl ι 𝔅) (G i) := by
    intro i
    rw [hcz]
    exact evC_smul (hG i) c _
  have hC0 : (∏ k, c k ^ g k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hl' : evC (u ∘ joinInl ι 𝔅) (G l) ≠ 0 := by
    intro h0
    apply hl
    rw [e, h0, mul_zero]
  obtain ⟨μ, hμ, hz⟩ := proportional hzb hzc hl
  obtain ⟨ν, hν, hu⟩ := proportional hub huc hl'
  refine ⟨Sum.elim c fun _ => μ * (∏ k, c k ^ g k) / ν, ?_, ?_⟩
  · rintro (k | ⟨⟩)
    · exact hc k
    · exact div_ne_zero (mul_ne_zero hμ hC0) hν
  · funext q
    obtain ⟨k | ⟨⟩, i⟩ := q
    · exact congrFun hcz ⟨k, i⟩
    · have h1 := hz i
      have h2 := hu i
      show z ⟨Sum.inr (), i⟩ = μ * (∏ k, c k ^ g k) / ν * u ⟨Sum.inr (), i⟩
      rw [h1, h2, e i]
      field_simp
end GlobalTheory.CompanionTheory.Ar.Giv.ResProj
