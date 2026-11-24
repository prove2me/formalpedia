-- Prove2me | solution 1 for GlobalTheory.SeriesNakayama.surjective_of_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:13:17.967448+00:00
-- url     : https://prove2.me/submissions/1ea0dd8b-6420-49ff-bbc4-9c4089c732bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SpanModEquationsLift
import Theorems.Thm_GlobalTheory_SeriesNakayama_mem_pow_smul_top_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.SeriesNakayama
namespace GlobalTheory.SeriesNakayama
theorem _root_.solution {O ι κ : Type*} [CommRing O] (π : O)
    [IsAdicComplete (Ideal.span {π}) O] (Φ : (ι → O) →ₗ[O] (κ → O))
    (h : ∀ G : κ → O, ∃ x, ∀ j, G j - Φ x j ∈ Ideal.span {π}) : Function.Surjective Φ := by
  have : IsPrecomplete (Ideal.span {π}) (ι → O) := by
    refine ⟨fun u hu => ?_⟩
    have h1 : ∀ i, ∃ L : O, ∀ k, u k i ≡ L [SMOD (Ideal.span {π} ^ k • ⊤ : Submodule O O)] :=
      fun i => IsPrecomplete.prec' (fun k => u k i) fun {a b} hab =>
        SModEq.sub_mem.2 ((mem_pow_smul_top_pi π a _).1 (SModEq.sub_mem.1 (hu hab)) i)
    choose L hL using h1
    exact ⟨L, fun k => SModEq.sub_mem.2
      ((mem_pow_smul_top_pi π k _).2 fun i => SModEq.sub_mem.1 (hL i k))⟩
  have : IsHausdorff (Ideal.span {π}) (κ → O) := by
    refine ⟨fun x hx => funext fun j => IsHausdorff.haus' (I := Ideal.span {π}) (x j) fun n => ?_⟩
    exact SModEq.sub_mem.2 ((mem_pow_smul_top_pi π n _).1 (SModEq.sub_mem.1 (hx n)) j)
  refine surjective_of_mkQ_comp_surjective (I := Ideal.span {π}) fun G => ?_
  obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective _ G
  obtain ⟨x, hx⟩ := h G
  refine ⟨x, ((Submodule.Quotient.eq _).2 ?_).symm⟩
  have := (mem_pow_smul_top_pi π 1 (G - Φ x)).2 fun j => by simpa using hx j
  rwa [pow_one] at this
end GlobalTheory.SeriesNakayama
