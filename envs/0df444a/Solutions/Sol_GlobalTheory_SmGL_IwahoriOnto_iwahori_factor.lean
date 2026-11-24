-- Prove2me | solution 1 for GlobalTheory.SmGL.IwahoriOnto.iwahori_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:02:48.360031+00:00
-- url     : https://prove2.me/submissions/c07b2e41-80c1-4d97-9837-1b2ff5a868f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_exists_mul_mem_borel
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_exists_levi_mul_unip
import Theorems.Thm_GlobalTheory_SmGL_mem_unipB
import Theorems.Thm_GlobalTheory_SmGL_val_diagT


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel Matrix Topology Filter
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IwahoriOnto
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
namespace GlobalTheory.SmGL.IwahoriOnto
theorem _root_.solution : ∀ g ∈ iwahori k n, ∃ d ∈ torusO k n, ∃ x ∈ unipB k n, ∃ c ∈ lowerInt k n,
    g = diagT k n d * x * c := by
  rintro _ ⟨h, hh, rfl⟩
  obtain ⟨L, hL0, hL1, hb⟩ := exists_mul_mem_borel h hh
  obtain ⟨u, hu, e⟩ := exists_levi_mul_unip 𝒪[k] (points n) ⟨_, hb⟩
  obtain ⟨d, hd⟩ := (leviTorus 𝒪[k] n).surjective (leviProj 𝒪[k] (points n) ⟨_, hb⟩)
  rw [← hd] at e
  have e' : h * L = diagT 𝒪[k] n d * u := e
  have hLl : L ∈ unipBLower 𝒪[k] n :=
    (mem_unipB (n := nᵒᵈ) 𝒪[k]).2 ⟨fun i j hij => hL0 i j hij, hL1⟩
  have hLi := (mem_unipB (n := nᵒᵈ) 𝒪[k]).1 (inv_mem hLl)
  have hu' := (mem_unipB 𝒪[k]).1 hu
  let f := GeneralLinearGroup.map (n := n) (algebraMap 𝒪[k] k)
  have hf : ∀ (g : GL n 𝒪[k]) i j, (f g : Matrix n n k) i j = algebraMap 𝒪[k] k ((g : Matrix n n 𝒪[k]) i j) :=
    fun _ _ _ => rfl
  refine ⟨fun i => Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) (d i), fun i =>
    (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _), f u,
    (mem_unipB k).2 ⟨fun i j hij => by rw [hf, hu'.1 i j hij, map_zero], fun i => by rw [hf, hu'.2 i, map_one]⟩,
    f L⁻¹, ⟨fun i j => ((L⁻¹ : GL n 𝒪[k]).val i j).2, fun i j hij => ?_, fun i => ?_⟩, ?_⟩
  · rw [hf]; exact (congrArg _ (hLi.1 i j hij)).trans (map_zero _)
  · rw [hf]; exact (congrArg _ (hLi.2 i)).trans (map_one _)
  · have : diagT k n (fun i => Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) (d i)) = f (diagT 𝒪[k] n d) := by
      ext i j
      rw [hf, val_diagT, val_diagT, diagonal_apply, diagonal_apply]
      split_ifs
      · rfl
      · simp
    rw [this, ← map_mul, ← map_mul, ← e', mul_inv_cancel_right]
end GlobalTheory.SmGL.IwahoriOnto
