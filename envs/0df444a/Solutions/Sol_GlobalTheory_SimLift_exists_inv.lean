-- Prove2me | solution 1 for GlobalTheory.SimLift.exists_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:13:10.504008+00:00
-- url     : https://prove2.me/submissions/a5af249c-8973-470f-a52b-514f83f084ce

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ModNOfDvdModulus
import Theorems.Thm_GlobalTheory_SimLift_exists_rep
import Theorems.Thm_GlobalTheory_SimLift_modN_of_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.SimLift
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
namespace GlobalTheory.SimLift
theorem _root_.solution {n : ℕ} (hn : 0 < n) {f : D.La →ₗ[𝓞 E] D.La} {ν : ℤ} (hf : IsSimMod D n f ν) :
    ∃ g : D.La →ₗ[𝓞 E] D.La, ∀ a, D.ModN n (g (f a) - a) ∧ D.ModN n (f (g a) - a) := by
  obtain ⟨⟨κ, t, hκ⟩, hB⟩ := hf
  obtain ⟨u, hu⟩ := exists_rep D (fun a b => D.EF a (f b)) (fun a a' b => by simp)
    (fun a b b' => by simp) (fun c a b => by rw [f.map_smul, D.adj])
  set g : D.La →ₗ[𝓞 E] D.La := κ • u with hg
  have h1 : ∀ a, D.ModN n (g (f a) - a) := fun a => modN_of_dvd D hn fun b => by
    obtain ⟨B, hB⟩ := hB a b
    simp only [hg, LinearMap.smul_apply, map_sub, map_zsmul, LinearMap.sub_apply, smul_eq_mul, hu]
    exact ⟨κ * B - t * D.EF a b, by linear_combination κ * hB + D.EF a b * hκ⟩
  let S : Submodule (𝓞 E) D.La := LinearMap.range (n • (LinearMap.id : D.La →ₗ[𝓞 E] D.La))
  have hS : ∀ x, x ∈ S ↔ D.ModN n x := fun x =>
    ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  have hgS : S ≤ S.comap g := by
    rintro x hx
    obtain ⟨b, rfl⟩ := (hS x).mp hx
    exact (hS _).mpr ⟨g b, map_nsmul g n b⟩
  have := D.fin
  have hsurj : Function.Surjective (S.mapQ S g hgS) := by
    intro q
    obtain ⟨a, rfl⟩ := S.mkQ_surjective q
    exact ⟨S.mkQ (f a), (Submodule.Quotient.eq S).mpr ((hS _).mpr (h1 a))⟩
  have hinj := OrzechProperty.injective_of_surjective_endomorphism _ hsurj
  refine ⟨g, fun a => ⟨h1 a, (hS _).mp ((Submodule.Quotient.eq S).mp (hinj ?_))⟩⟩
  exact (Submodule.Quotient.eq S).mpr ((hS _).mpr (h1 (g a)))
end GlobalTheory.SimLift
