-- Prove2me | solution 1 for LatticePrepro.ObliviousPCP.pcp_reduction
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-16T22:16:01.362338+00:00
-- url     : https://prove2.me/submissions/9f7b48bf-6bb1-45f0-b66e-0aa8cf5ba547

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_PCP_Verifier
import Definitions.Def_LatticePrepro_PCP_Code
import Theorems.Thm_LatticePrepro_ObliviousPCP_card_coord
import Theorems.Thm_LatticePrepro_ObliviousPCP_codeDist_le_of_mem
import Theorems.Thm_LatticePrepro_ObliviousPCP_lt_codeDist_of_not_mem

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.ObliviousPCP end LatticePrepro.ObliviousPCP

namespace LatticePrepro

namespace ObliviousPCP

variable {X : Type} (P : ObliviousPCP X) {F : Type} [Field F] [DecidableEq F] {B : ℕ}

/-- **Theorem 6.4** (the PCP reduction). Let `P` be a query-oblivious PCP with perfect
completeness and soundness error `ε > 0` for `Lang`, let `E : F^m → F^B` be an injective linear
map whose image has relative distance at least `δ`, and let `g < δ · ε^{-1/q}`. Then the
accepting-view code `𝒞` and the targets `y_x` of Construction 6.2 satisfy, with
`Y = B · 2^ρ · q`:

* `dist(y_x, 𝒞) ≤ Y` for every `x ∈ Lang`;
* `dist(y_x, 𝒞) > g · Y` for every `x ∉ Lang`;
* the block length is `(|Σ| + g) · Y + 1`.

The code does not depend on `x`. -/
private theorem pcp_reduction {Lang : Set X} {ε δ : ℝ} (hc : P.PerfectlyComplete Lang)
    (hs : P.SoundnessError Lang ε) (hε : 0 < ε) {E : (P.Views → F) →ₗ[F] (Fin B → F)}
    (hE : Function.Injective E)
    (hδ : ∀ c ∈ LinearMap.range E, c ≠ 0 → δ * B ≤ hammingNorm c) {g : ℕ}
    (hg : (g : ℝ) < δ * ε ^ (-(1 : ℝ) / P.q)) :
    (∀ x ∈ Lang, CodeFamily.codeDist (P.target E g x) (P.code E g) ≤ P.radius B) ∧
    (∀ x, x ∉ Lang → g * P.radius B < CodeFamily.codeDist (P.target E g x) (P.code E g)) ∧
    Fintype.card (P.Coord B ⊕ Fin (g * P.radius B + 1)) =
      (Fintype.card P.Alphabet + g) * P.radius B + 1 :=
  ⟨fun _ hx => P.codeDist_le_of_mem hc E g hx,
    fun _ hx => P.lt_codeDist_of_not_mem hs hε hE hδ hg hx, P.card_coord B g⟩

end ObliviousPCP

end LatticePrepro

open LatticePrepro
open LatticePrepro.ObliviousPCP
variable {X : Type} (P : ObliviousPCP X) {F : Type} [Field F] [DecidableEq F] {B : ℕ}
theorem solution {Lang : Set X} {ε δ : ℝ} (hc : P.PerfectlyComplete Lang)
    (hs : P.SoundnessError Lang ε) (hε : 0 < ε) {E : (P.Views → F) →ₗ[F] (Fin B → F)}
    (hE : Function.Injective E)
    (hδ : ∀ c ∈ LinearMap.range E, c ≠ 0 → δ * B ≤ hammingNorm c) {g : ℕ}
    (hg : (g : ℝ) < δ * ε ^ (-(1 : ℝ) / P.q)) :
    (∀ x ∈ Lang, CodeFamily.codeDist (P.target E g x) (P.code E g) ≤ P.radius B) ∧
    (∀ x, x ∉ Lang → g * P.radius B < CodeFamily.codeDist (P.target E g x) (P.code E g)) ∧
    Fintype.card (P.Coord B ⊕ Fin (g * P.radius B + 1)) =
      (Fintype.card P.Alphabet + g) * P.radius B + 1 :=
  @LatticePrepro.ObliviousPCP.pcp_reduction X P F _ _ B Lang ε δ hc hs hε E hE hδ g hg
