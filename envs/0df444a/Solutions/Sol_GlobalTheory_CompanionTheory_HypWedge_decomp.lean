-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HypWedge.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:16:50.565111+00:00
-- url     : https://prove2.me/submissions/2e9878c4-2641-4010-ba2f-502b8366ab65

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FormComponentOfWedgeClassZero
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_wB_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_wB_swap
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_exterior_square_map_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_mix_tmul
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HypWedge
variable {R M N V W : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
namespace GlobalTheory.CompanionTheory.HypWedge
theorem _root_.solution (σ : V →ₗ[R] M) (k : W →ₗ[R] M) (hs : ∀ a, ∃ v w, a = σ v + k w) (x : ⋀[R]^2 M) :
    ∃ y u z, x = exteriorPower.map 2 σ y + mix σ k u + exteriorPower.map 2 k z := by
  let S : Submodule R (⋀[R]^2 M) :=
    LinearMap.range (exteriorPower.map 2 σ) ⊔ LinearMap.range (mix σ k) ⊔
      LinearMap.range (exteriorPower.map 2 k)
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← exteriorPower.ιMulti_span R 2 M, Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    have hm : m = ![m 0, m 1] := by
      ext i; fin_cases i <;> rfl
    obtain ⟨v, w, h0⟩ := hs (m 0)
    obtain ⟨v', w', h1⟩ := hs (m 1)
    rw [hm, ← wB_apply, h0, h1]
    have e : wB R M (σ v + k w) (σ v' + k w') =
        exteriorPower.map 2 σ (exteriorPower.ιMulti R 2 ![v, v']) +
          mix σ k (v ⊗ₜ w' - v' ⊗ₜ w) + exteriorPower.map 2 k (exteriorPower.ιMulti R 2 ![w, w']) := by
      rw [exterior_square_map_apply, exterior_square_map_apply, map_sub, mix_tmul, mix_tmul, wB_swap (σ v') (k w)]
      simp only [map_add, LinearMap.add_apply]
      abel
    rw [e]
    exact S.add_mem (S.add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left ⟨_, rfl⟩))
      (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨_, rfl⟩)))
      (Submodule.mem_sup_right ⟨_, rfl⟩)
  have hx : x ∈ S := hS ▸ Submodule.mem_top
  obtain ⟨x', hx', z', ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨_, ⟨y, rfl⟩, _, ⟨u, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx'
  exact ⟨y, u, z, rfl⟩
end GlobalTheory.CompanionTheory.HypWedge
