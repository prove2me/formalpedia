-- Prove2me | solution 1 for GlobalTheory.BetaOfSum.detSpan_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:52:59.206914+00:00
-- url     : https://prove2.me/submissions/7741e528-0cba-47ed-aab6-a3e77e709a6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BlockHarmLevOfBlockHarm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsBetaUnitBlock
import Theorems.Thm_GlobalTheory_BetaOfSum_mem_block
import Theorems.Thm_GlobalTheory_BetaOfSum_det_block
import Theorems.Thm_GlobalTheory_BetaOfSum_det_pure_mem
import Theorems.Thm_GlobalTheory_BetaEx_det_mem
import Theorems.Thm_GlobalTheory_BetaEx_mem_detSet


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
open GlobalTheory GlobalTheory.BetaOfSum
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BetaEx GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility GlobalTheory.ShortLawsCompare
variable {E : Type} [Field E] [NumberField E] {n₁ n₂ : ℕ}
namespace GlobalTheory.BetaOfSum
theorem _root_.solution (M₁ : Submodule (𝓞 E) (Fin n₁ → E)) (M₂ : Submodule (𝓞 E) (Fin n₂ → E)) :
    detSpan (blockLat ⟨M₁⟩ ⟨M₂⟩).La = detSpan M₁ * detSpan M₂ := by
  classical
  have z₁ : (fun _ => 0) ∈ M₁ := M₁.zero_mem
  have z₂ : (fun _ => 0) ∈ M₂ := M₂.zero_mem
  apply le_antisymm
  · refine Submodule.span_le.2 fun d hd => ?_
    obtain ⟨v, hv, rfl⟩ := (mem_detSet _ d).1 hd
    let a : Fin (n₁ + n₂) → Fin (n₁ + n₂) → E := fun i => Fin.append (fun j => v i (Fin.castAdd n₂ j)) 0
    let b : Fin (n₁ + n₂) → Fin (n₁ + n₂) → E := fun i => Fin.append 0 (fun j => v i (Fin.natAdd n₁ j))
    have e : (v : Fin (n₁ + n₂) → Fin (n₁ + n₂) → E) = a + b := by
      funext i j
      induction j using Fin.addCases <;> simp [a, b]
    have e2 : v.det = ∑ s : Finset (Fin (n₁ + n₂)), (Matrix.of (s.piecewise a b)).det := by
      have := (Matrix.detRowAlternating (n := Fin (n₁ + n₂)) (R := E)).toMultilinearMap.map_add_univ a b
      rw [← e] at this
      exact this
    rw [SetLike.mem_coe, e2]
    refine Submodule.sum_mem _ fun s _ => det_pure_mem M₁ M₂ _ (fun i => ?_) (fun i => ?_) (fun i => ?_)
    · by_cases hi : i ∈ s
      · simpa [hi, a] using ((mem_block _ _ _).1 (hv i)).1
      · simpa [hi, b] using z₁
    · by_cases hi : i ∈ s
      · simpa [hi, a] using z₂
      · simpa [hi, b] using ((mem_block _ _ _).1 (hv i)).2
    · by_cases hi : i ∈ s
      · exact Or.inr fun j => by simp [hi, a]
      · exact Or.inl fun j => by simp [hi, b]
  · rw [detSpan, detSpan, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨v, hv, rfl⟩ := (mem_detSet _ _).1 hx
    obtain ⟨w, hw, rfl⟩ := (mem_detSet _ _).1 hy
    let u : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) E :=
      Matrix.of (Fin.append (fun i => Fin.append (v i) 0) (fun i => Fin.append 0 (w i)))
    have e : u.det = v.det * w.det := by
      rw [det_block u (fun i j => by simp [u])]
      congr 2 <;> ext i j <;> simp [u]
    change v.det * w.det ∈ detSpan _
    rw [← e]
    refine det_mem _ fun i => (mem_block _ _ _).2 ?_
    induction i using Fin.addCases with
    | left i => exact ⟨by simpa [u] using hv i, by simpa [u] using z₂⟩
    | right i => exact ⟨by simpa [u] using z₁, by simpa [u] using hw i⟩
end GlobalTheory.BetaOfSum
