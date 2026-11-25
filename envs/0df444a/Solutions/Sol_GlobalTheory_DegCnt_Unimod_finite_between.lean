-- Prove2me | solution 1 for GlobalTheory.DegCnt.Unimod.finite_between
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:26:19.211302+00:00
-- url     : https://prove2.me/submissions/2210e700-c87f-4109-9103-29680335a2b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntSmulLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBisTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Unimod
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.Unimod
theorem _root_.solution {Λ : Submodule (𝓞 K) V} (hΛ : Λ.FG) {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    {M : Submodule (𝓞 K) V | (∀ x ∈ Λ, a • x ∈ M) ∧ ∀ x ∈ M, b • x ∈ Λ}.Finite := by
  haveI : Module.Finite (𝓞 K) Λ := Module.Finite.iff_fg.2 hΛ
  haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 K) Λ
  let P : Submodule ℤ Λ := LinearMap.range (LinearMap.lsmul ℤ Λ (b * a))
  haveI : Finite (Λ ⧸ P) := by
    refine Module.finite_of_fg_torsion _ ?_
    intro q
    obtain ⟨x, rfl⟩ := P.mkQ_surjective q
    refine ⟨⟨b * a, mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hb ha)⟩, ?_⟩
    change (b * a) • P.mkQ x = 0
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
  let f : Submodule (𝓞 K) V → Set (Λ ⧸ P) := fun M =>
    {q | ∃ x ∈ M, ∃ h : b • x ∈ Λ, P.mkQ ⟨b • x, h⟩ = q}
  have key : ∀ M M' : Submodule (𝓞 K) V, (∀ x ∈ M, b • x ∈ Λ) → (∀ x ∈ Λ, a • x ∈ M') →
      f M = f M' → M ≤ M' := by
    intro M M' hM hM' e x hx
    have : P.mkQ ⟨b • x, hM x hx⟩ ∈ f M' := e ▸ ⟨x, hx, hM x hx, rfl⟩
    obtain ⟨y, hy, hy', h⟩ := this
    obtain ⟨z, hz⟩ := (Submodule.Quotient.eq _).1 h
    have hz' : (b * a) • (z : V) = b • y - b • x := congrArg Subtype.val hz
    have h2 : (b : K) • (a • (z : V)) = (b : K) • (y - x) := by
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, ← mul_smul, hz', smul_sub]
    have h3 := smul_right_injective V (by exact_mod_cast hb : (b : K) ≠ 0) h2
    have h4 : x = y - a • (z : V) := by
      have h3' : a • (z : V) = y - x := h3
      rw [h3']; abel
    rw [h4]
    exact M'.sub_mem hy (hM' _ z.2)
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro M hM M' hM' e
  exact le_antisymm (key M M' hM.2 hM'.1 e) (key M' M hM'.2 hM.1 e.symm)
end GlobalTheory.DegCnt.Unimod
