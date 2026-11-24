-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.exists_limit_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:06:52.013984+00:00
-- url     : https://prove2.me/submissions/ec26ad4c-6dcc-44a2-9c94-46c443ab4c57

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOut
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_ofFamily_apply


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ultra
namespace GlobalTheory.CompanionTheory.Ultra
theorem _root_.solution {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) {S₀ : Set R₀}
    (hS₀ : Algebra.adjoin ℤ S₀ = ⊤) {V : Finset R → Type} [∀ F, CommRing (V F)]
    (β : ∀ F, lvl φ S₀ F →+* V F) (U : Ultrafilter (Finset R))
    (hU : (U : Filter (Finset R)) ≤ atTop) :
    ∃ ρ : R →+* Ult U V, ∀ r, ρ (φ r) = mk U (fun F => β F (lvlHom φ hS₀ F r)) := by
  classical
  have hmem : ∀ r : R, ∀ᶠ F in (U : Filter (Finset R)), r ∈ lvl φ S₀ F := by
    intro r
    filter_upwards [hU (eventually_ge_atTop ({r} : Finset R))] with F hF
    exact Algebra.subset_adjoin (Or.inr (by simpa using hF))
  let h : ∀ F, R → V F := fun F r => if hr : r ∈ lvl φ S₀ F then β F ⟨r, hr⟩ else 0
  have hv : ∀ (F : Finset R) (r : R) (hr : r ∈ lvl φ S₀ F), h F r = β F ⟨r, hr⟩ :=
    fun F r hr => dif_pos hr
  refine ⟨ofFamily U h ?_ ?_ ?_, fun r => ?_⟩
  · filter_upwards [hmem 1] with F h1
    rw [hv F 1 h1]
    exact map_one (β F)
  · intro a b
    filter_upwards [hmem a, hmem b, hmem (a + b)] with F ha hb hab
    rw [hv F _ hab, hv F _ ha, hv F _ hb, ← map_add]
    rfl
  · intro a b
    filter_upwards [hmem a, hmem b, hmem (a * b)] with F ha hb hab
    rw [hv F _ hab, hv F _ ha, hv F _ hb, ← map_mul]
    rfl
  · refine (ofFamily_apply U h _ _ _ (φ r)).trans ((mk_eq_mk_iff U).2 ?_)
    refine Filter.Eventually.of_forall fun F => ?_
    rw [hv F _ (map_mem_lvl φ hS₀ F r)]
    rfl
end GlobalTheory.CompanionTheory.Ultra
