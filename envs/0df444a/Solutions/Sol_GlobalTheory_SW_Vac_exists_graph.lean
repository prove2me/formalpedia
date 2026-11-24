-- Prove2me | solution 1 for GlobalTheory.SW.Vac.exists_graph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:58:43.067012+00:00
-- url     : https://prove2.me/submissions/00422fdb-9426-4a96-9e96-354f03744a9a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
import Theorems.Thm_GlobalTheory_SW_Vac_exists_pr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Vac
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.Vac
theorem _root_.solution (Γ : AddSubgroup (Matrix κ ι ℚ × ℚ)) (M : AddSubgroup (Matrix κ ι ℚ))
    (hM : M.FG) (hΓ : ∀ p ∈ Γ, p.1 ∈ M) : ∃ x, ∀ p ∈ Γ, (p.1, pr x p.1) ∈ Γ := by
  let G : Submodule ℤ (Matrix κ ι ℚ × ℚ) := Γ.toIntSubmodule
  let q : G →ₗ[ℤ] Matrix κ ι ℚ := (LinearMap.fst ℤ _ _).comp G.subtype
  have hM' : (M.toIntSubmodule).FG := (Submodule.fg_iff_addSubgroup_fg _).2 (by simpa using hM)
  have hfg : (LinearMap.range q).FG := by
    refine hM'.of_le ?_
    rintro _ ⟨p, rfl⟩
    exact hΓ p.1 p.2
  haveI : Module.Finite ℤ (LinearMap.range q) := Module.Finite.iff_fg.2 hfg
  haveI : Module.IsTorsionFree ℤ (Matrix κ ι ℚ) :=
    inferInstanceAs (Module.IsTorsionFree ℤ (κ → ι → ℚ))
  haveI : Module.Free ℤ (LinearMap.range q) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q.rangeRestrict LinearMap.id
    q.surjective_rangeRestrict
  have hB : Module.Baer ℤ ℚ := Module.Baer.of_divisible ℚ
  obtain ⟨f, hf⟩ := hB.extension_property (LinearMap.range q).subtype
    (Submodule.injective_subtype _) (((LinearMap.snd ℤ _ _).comp G.subtype).comp s)
  obtain ⟨x, hx⟩ := exists_pr f
  refine ⟨x, fun p hp => ?_⟩
  let u : LinearMap.range q := ⟨p.1, ⟨p, hp⟩, rfl⟩
  have h1 : (s u).1.1 = p.1 := congrArg Subtype.val (LinearMap.congr_fun hs u)
  have h2 : (s u).1.2 = pr x p.1 := by
    rw [← hx]; exact (LinearMap.congr_fun hf u).symm
  have : (p.1, pr x p.1) = (s u).1 := Prod.ext h1.symm h2.symm
  rw [this]; exact (s u).2
end GlobalTheory.SW.Vac
