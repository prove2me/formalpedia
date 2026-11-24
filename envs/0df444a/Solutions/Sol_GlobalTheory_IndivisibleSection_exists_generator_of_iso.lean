-- Prove2me | solution 1 for GlobalTheory.IndivisibleSection.exists_generator_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:41:46.561942+00:00
-- url     : https://prove2.me/submissions/fd72359e-1183-4ef6-b89e-ade3471d4732

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsGeneratorOfBasis
import Theorems.Thm_GlobalTheory_IndivisibleSection_sval_of_secIsMul
import Theorems.Thm_GlobalTheory_IndivisibleSection_secIsMul_of_sval
import Theorems.Thm_GlobalTheory_IndivisibleSection_exists_pull_val
import Theorems.Thm_GlobalTheory_IndivisibleSection_prod_fam_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndivisibleSection
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
namespace GlobalTheory.IndivisibleSection
theorem _root_.solution {Y : Scheme.{0}} (π : Y ⟶ D.P.A.left) (σ : D.P.A.left ⟶ Y)
    (h₁ : σ ≫ π = 𝟙 _) (h₂ : π ≫ σ = 𝟙 _) (f : Y ⟶ Sp R) (hf : π ≫ D.P.A.hom = f)
    (β : LB.Sec (LB.LinComb D.P.L (K := Fin 1) (fun _ => π) (fun _ => ((1 : ℕ) : ℤ))))
    (H : ∀ s : LB.Sec (LB.LinComb D.P.L (K := Fin 1) (fun _ => π) (fun _ => ((1 : ℕ) : ℤ))),
      ∃! a : R, SecIsMul f a s β) :
    ∃ b : D.SecB 1 0, ∀ s : D.SecB 1 0, ∃! a : R, SecIsMul D.P.A.hom a s b := by
  have hL : D.P.L.IsLB := D.P.isLB
  subst hf
  have hform1 : FormEq (fun _ : Fin 1 => σ ≫ π) (fun _ => ((1 : ℕ) : ℤ)) (D.famφB 0) (DegPre.famε 1) := by
    unfold FormEq
    intro U _ h
    rw [prod_fam_zero D h, h₁]
    simp
  obtain ⟨b, hbv⟩ := exists_pull_val hL β σ hform1
  refine ⟨b, fun s => ?_⟩
  have hform2 : FormEq (fun k => π ≫ D.famφB 0 k) (DegPre.famε 1) (fun _ : Fin 1 => π) (fun _ => ((1 : ℕ) : ℤ)) := by
    unfold FormEq
    intro U _ h
    have e0 := prod_fam_zero D (fun g => h (π ≫ g))
    simp only [Category.comp_id] at e0
    rw [e0]
    simp
  obtain ⟨sY, hsY⟩ := exists_pull_val hL s π hform2
  obtain ⟨a, ha, hau⟩ := H sY
  refine ⟨a, ?_, fun a' ha' => hau a' ?_⟩
  · apply secIsMul_of_sval hL
    intro y J hJ
    have e1 := hsY _ σ y J hJ
    rw [h₁] at e1
    have e2 := hbv _ (𝟙 _) y J hJ
    rw [Category.id_comp] at e2
    rw [← e1, e2, sval_of_secIsMul ha σ y hJ, ← Category.assoc, h₁, Category.id_comp]
  · apply secIsMul_of_sval hL
    intro y J hJ
    have e1 := hsY _ (𝟙 _) y J hJ
    rw [Category.id_comp] at e1
    rw [e1, sval_of_secIsMul ha' π y hJ, hbv _ π y J hJ, h₂]
end GlobalTheory.IndivisibleSection
