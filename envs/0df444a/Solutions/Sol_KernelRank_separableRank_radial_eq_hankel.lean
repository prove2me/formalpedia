-- Prove2me | solution 1 for KernelRank.separableRank_radial_eq_hankel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:27:21.101221+00:00
-- url     : https://prove2.me/submissions/4dac5eb6-8474-44c7-80ca-1a9a68c05952

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Translations
import Theorems.Thm_KernelRank_separableRank_comp_surjective


set_option autoImplicit true
open NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {𝕜 : Type*} [CommSemiring 𝕜] (d : ℕ) (φ : ℝ → 𝕜) :
    separableRank (fun x : Fin d → ℝ => φ (∑ i, x i ^ 2)) =
      separableRank (fun s : Fin d → ℝ≥0 => φ (∑ i, (s i : ℝ))) := by
  let sqNN (x : ℝ) : ℝ≥0 := ⟨x ^ 2, sq_nonneg x⟩
  have hsurj : Function.Surjective sqNN := fun s =>
    ⟨Real.sqrt s, Subtype.ext (Real.sq_sqrt s.2)⟩
  exact separableRank_comp_surjective (X := fun _ : Fin d => ℝ≥0) (Y := fun _ : Fin d => ℝ)
    (fun s => φ (∑ i, (s i : ℝ))) (g := fun _ => sqNN) (fun _ => hsurj)
end KernelRank
