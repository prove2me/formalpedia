-- Prove2me | solution 1 for GlobalTheory.LieEtale.mult_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:58:22.787774+00:00
-- url     : https://prove2.me/submissions/4adeca27-c807-4253-b894-d252059abd71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueTangentLift
import Theorems.Thm_GlobalTheory_LieEtale_comp_listProd
import Theorems.Thm_GlobalTheory_LieEtale_ofFn_prod_comp

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
open GlobalTheory GlobalTheory.LieEtale
variable {S : Scheme.{0}} {O k : Type} {P E : Over S}
namespace GlobalTheory.LieEtale
theorem _root_.solution {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ]
    (z : P ⟶ E) (sc : k → (E ⟶ E)) (hz : ∀ c, z ≫ sc c = z)
    (a : O → (A ⟶ A)) (b : O → (B ⟶ B)) (ha : ∀ c, IsMonHom (a c))
    (hab : ∀ c, a c ≫ ψ = ψ ≫ b c) (τ : O → k)
    (H : ∀ w : E ⟶ B, z ≫ w = 1 → ∃! v : E ⟶ A, z ≫ v = 1 ∧ v ≫ ψ = w) (n : ℕ) :
    (∃ v : Fin n → (E ⟶ A), (∀ i, Eig z sc a τ (v i)) ∧ ∀ w, Eig z sc a τ w →
      ∃! c : Fin n → k, w = (List.ofFn fun i => sc (c i) ≫ v i).prod) ↔
    (∃ v : Fin n → (E ⟶ B), (∀ i, Eig z sc b τ (v i)) ∧ ∀ w, Eig z sc b τ w →
      ∃! c : Fin n → k, w = (List.ofFn fun i => sc (c i) ≫ v i).prod) := by
  have htan : ∀ v : E ⟶ A, z ≫ v = 1 → z ≫ v ≫ ψ = 1 := fun v hv => by
    rw [← Category.assoc, hv, MonObj.one_comp]
  have hinj : ∀ v v' : E ⟶ A, z ≫ v = 1 → z ≫ v' = 1 → v ≫ ψ = v' ≫ ψ → v = v' :=
    fun v v' hv hv' e => (H _ (htan v' hv')).unique ⟨hv, e⟩ ⟨hv', rfl⟩
  have hsc : ∀ (c : k) (v : E ⟶ A), z ≫ v = 1 → z ≫ sc c ≫ v = 1 := fun c v hv => by
    rw [← Category.assoc, hz, hv]
  have heig : ∀ v : E ⟶ A, z ≫ v = 1 → (Eig z sc a τ v ↔ Eig z sc b τ (v ≫ ψ)) := fun v hv => by
    refine ⟨fun h => ⟨htan v hv, fun c => ?_⟩, fun h => ⟨hv, fun c => hinj _ _ ?_ (hsc _ _ hv) ?_⟩⟩
    · rw [Category.assoc, ← hab, ← Category.assoc, h.2, Category.assoc]
    · have := ha c
      rw [← Category.assoc, hv, MonObj.one_comp]
    · rw [Category.assoc, hab, ← Category.assoc, h.2, Category.assoc]
  have hcomb : ∀ (v : Fin n → (E ⟶ A)) (w : E ⟶ A), (∀ i, z ≫ v i = 1) → z ≫ w = 1 →
      ∀ c : Fin n → k, (w = (List.ofFn fun i => sc (c i) ≫ v i).prod ↔
        w ≫ ψ = (List.ofFn fun i => sc (c i) ≫ v i ≫ ψ).prod) := fun v w hv hw c => by
    have e : (List.ofFn fun i => sc (c i) ≫ v i).prod ≫ ψ =
        (List.ofFn fun i => sc (c i) ≫ v i ≫ ψ).prod := by
      simp only [ofFn_prod_comp, Category.assoc]
    rw [← e]
    refine ⟨fun h => by rw [← h], hinj _ _ hw (comp_listProd z _ fun u hu => ?_)⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
    exact hsc _ _ (hv i)
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨fun i => v i ≫ ψ, fun i => (heig _ (hv i).1).mp (hv i), fun w hw => ?_⟩
    obtain ⟨w', ⟨hw', rfl⟩, -⟩ := H w hw.1
    exact (existsUnique_congr (hcomb v w' (fun i => (hv i).1) hw')).mp (h w' ((heig _ hw').mpr hw))
  · rintro ⟨v, hv, h⟩
    choose v' hv' using fun i => (H (v i) (hv i).1).exists
    obtain rfl : v = fun i => v' i ≫ ψ := funext fun i => (hv' i).2.symm
    refine ⟨v', fun i => (heig _ (hv' i).1).mpr (hv i), fun w hw => ?_⟩
    exact (existsUnique_congr (hcomb v' w (fun i => (hv' i).1) hw.1)).mpr
      (h _ ((heig _ hw.1).mp hw))
end GlobalTheory.LieEtale
