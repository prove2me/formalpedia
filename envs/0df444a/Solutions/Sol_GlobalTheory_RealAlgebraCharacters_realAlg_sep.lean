-- Prove2me | solution 1 for GlobalTheory.RealAlgebraCharacters.realAlg_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:14:03.067851+00:00
-- url     : https://prove2.me/submissions/b5208b64-487b-4d09-87aa-bef6c3abded1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RealAlgSep
import Theorems.Thm_GlobalTheory_RealAlgebraCharacters_chi_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RealAlgebraCharacters
open Filter Topology
variable {X : Type} {B : Type} [AddCommGroup B] (χ : B → X → ℂ)
namespace GlobalTheory.RealAlgebraCharacters
theorem _root_.solution [TopologicalSpace X] (hc : ∀ b, Continuous (χ b))
    (hadd : ∀ (a b : B) (x : X), χ (a + b) x = χ a x * χ b x)
    (h0 : ∀ x, χ 0 x = 1) (hn : ∀ (a : B) (x : X), ‖χ a x‖ = 1)
    (hs : ∀ x y : X, x ≠ y → ∃ b, χ b x ≠ χ b y) : (realAlg χ hadd h0).SeparatesPoints := by
  intro x y hxy
  obtain ⟨b, hb⟩ := hs x y hxy
  have hneg : ∀ u, χ (-b) u = (starRingEnd ℂ) (χ b u) := fun u => chi_neg χ hadd h0 hn b u
  let fre : C(X, ℝ) := ⟨fun u => (χ b u).re, Complex.continuous_re.comp (hc b)⟩
  let fim : C(X, ℝ) := ⟨fun u => (χ b u).im, Complex.continuous_im.comp (hc b)⟩
  have hre : fre ∈ realAlg χ hadd h0 := by
    show (fun u => (((χ b u).re : ℝ) : ℂ)) ∈ Submodule.span ℂ (Set.range χ)
    have he : (fun u => (((χ b u).re : ℝ) : ℂ)) = (1 / 2 : ℂ) • (χ b + χ (-b)) := by
      funext u
      simp only [Pi.smul_apply, Pi.add_apply, hneg, smul_eq_mul]
      rw [Complex.re_eq_add_conj]
      ring
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span ⟨b, rfl⟩)
      (Submodule.subset_span ⟨-b, rfl⟩))
  have him : fim ∈ realAlg χ hadd h0 := by
    show (fun u => (((χ b u).im : ℝ) : ℂ)) ∈ Submodule.span ℂ (Set.range χ)
    have he : (fun u => (((χ b u).im : ℝ) : ℂ)) = (1 / (2 * Complex.I)) • (χ b - χ (-b)) := by
      funext u
      simp only [Pi.smul_apply, Pi.sub_apply, hneg, smul_eq_mul]
      rw [Complex.im_eq_sub_conj]
      ring
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨b, rfl⟩)
      (Submodule.subset_span ⟨-b, rfl⟩))
  by_cases hr : (χ b x).re = (χ b y).re
  · refine ⟨fim, ⟨fim, him, rfl⟩, fun heq => hb (Complex.ext hr heq)⟩
  · exact ⟨fre, ⟨fre, hre, rfl⟩, hr⟩
end GlobalTheory.RealAlgebraCharacters
