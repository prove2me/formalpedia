-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.nbOf_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:58:46.944834+00:00
-- url     : https://prove2.me/submissions/e35c7289-1617-4817-9a18-a73f78878c71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Theorems.Thm_GlobalTheory_SW_Nbr_co_co
import Theorems.Thm_GlobalTheory_SW_Nbr_mem_conjI
import Theorems.Thm_GlobalTheory_SW_Nbr_ne_bot_of_norm
import Theorems.Thm_GlobalTheory_SW_Nbr_max_of_norm
import Theorems.Thm_P2M_GlobalTheory_SW_Nbr_Int__symm_b5c59deb8a7e
import Theorems.Thm_GlobalTheory_SW_Nbr_int_move
import Theorems.Thm_GlobalTheory_SW_Nbr_smul_le_iff
import Theorems.Thm_GlobalTheory_SW_Nbr_exists_sep
import Theorems.Thm_GlobalTheory_SW_Nbr_index_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Nbr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.SW.Nbr
theorem _root_.solution {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ Λ₀ : Lt E n}
    (h : Λ ∈ Vset E n M) (h1 : P • Λ ≤ Λ₀) (h2 : Λ₀ ≤ Λ)
    (h3 : Λ₀.toAddSubgroup.relIndex Λ.toAddSubgroup = q) :
    SD (nbOf P Λ₀) ∧ Λ ⊓ nbOf P Λ₀ = Λ₀ := by
  have hS : SD Λ := h.2.1
  have := max_of_norm hP.1 hP.2.2.1
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 hP.2.2.2.1
  have hdec : ∀ x : Fin n → E, x = a • x + b • x := fun x => by rw [← add_smul, hab, one_smul]
  obtain ⟨f, -, hf⟩ := (index_iff hP.1 hP.2.2.1 (Λ₀.comap Λ.subtype)).1
    ⟨fun c hc x => smul_le_iff.1 h1 c hc x x.2, h3⟩
  obtain ⟨w, hw⟩ := exists_sep h P (ne_bot_of_norm hP.1 hP.2.2.1) f
  have hw' : ∀ y ∈ Λ, Int' y w ↔ y ∈ Λ₀ := fun y hy => by
    rw [hw ⟨y, hy⟩, ← LinearMap.mem_ker, hf]; rfl
  have hle : Λ₀ ≤ nbOf P Λ₀ := fun x hx =>
    ⟨fun y hy => (hS x).1 (h2 hx) y (h2 hy), fun c _ => Λ₀.smul_mem c hx⟩
  have hQ : ∀ x, (∀ y ∈ Λ₀, Int' x y) → ∀ c ∈ conjI P, c • x ∈ Λ := fun x hx c hc =>
    (hS _).2 fun y hy => (int_move c x y).2 (hx _ (smul_le_iff.1 h1 _ (mem_conjI.1 hc) y hy))
  refine ⟨fun x => ⟨fun hx y hy => ?_, fun hx => ?_⟩, le_antisymm (fun x hx => ?_) (le_inf h2 hle)⟩
  · rw [hdec x]
    exact ((int_move a x y).2 (hx.1 _ (hy.2 _ (mem_conjI.2 (by rwa [co_co]))))).add
      (hy.1 _ (hx.2 b hb)).symm
  · have hx0 : ∀ y ∈ Λ₀, Int' x y := fun y hy => hx y (hle hy)
    refine ⟨hx0, fun c hc => (hw' _ (hQ x hx0 c hc)).1 ((int_move c x w).2 (hx _ ?_))⟩
    have hw0 : ∀ y ∈ Λ₀, Int' w y := fun y hy => ((hw' y (h2 hy)).2 hy).symm
    refine ⟨fun y hy => (hw0 y hy).smul _, fun d hd => ?_⟩
    rw [smul_comm]
    exact smul_le_iff.1 h1 _ (mem_conjI.1 hc) _ (hQ w hw0 d hd)
  · rw [hdec x]
    exact Λ₀.add_mem (smul_le_iff.1 h1 a ha x hx.1) (hx.2.2 b hb)
end GlobalTheory.SW.Nbr
