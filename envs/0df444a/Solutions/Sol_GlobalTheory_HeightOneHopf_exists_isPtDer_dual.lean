-- Prove2me | solution 1 for GlobalTheory.HeightOneHopf.exists_isPtDer_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:26:44.460828+00:00
-- url     : https://prove2.me/submissions/b4f5b24a-0aae-4e21-9598-505220bc95ee

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_SmallLevelClassSet
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AevalSurjectiveOfIsNilpotentKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AevalSurjectiveOfSpanCotangent
import Theorems.Thm_ReciprocityTheory_PGsh_isPtDer_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.HeightOneHopf
namespace GlobalTheory.HeightOneHopf
theorem _root_.solution {k H : Type*} [Field k] [CommRing H] [Bialgebra k H] {d : ℕ}
    (x : Fin d → H) (hx : ∀ i, x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H))
    (hind : ∀ l : Fin d → k,
      ∑ i, l i • x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H) ^ 2 → l = 0) :
    ∃ δ : Fin d → H →ₗ[k] k, (∀ i, IsPtDer (δ i)) ∧
      ∀ i j, δ i (x j) = if i = j then 1 else 0 := by
  classical
  set I : Ideal H := RingHom.ker (Bialgebra.counitAlgHom k H) with hI
  set J : Submodule k H := (I ^ 2).restrictScalars k with hJ
  let φ : (Fin d → k) →ₗ[k] H ⧸ J := J.mkQ ∘ₗ Fintype.linearCombination k x
  have hφ : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro l hl
    apply hind l
    have h1 : Fintype.linearCombination k x l ∈ J := (Submodule.Quotient.mk_eq_zero J).1 hl
    rw [Fintype.linearCombination_apply] at h1
    exact h1
  obtain ⟨g, hg⟩ := φ.exists_leftInverse_of_injective hφ
  let π : H →ₗ[k] H := LinearMap.id - Algebra.linearMap k H ∘ₗ Coalgebra.counit
  have hπ : ∀ y ∈ I, π y = y := by
    intro y hy
    rw [hI, RingHom.mem_ker, Bialgebra.counitAlgHom_apply] at hy
    simp [π, hy]
  refine ⟨fun i => LinearMap.proj i ∘ₗ g ∘ₗ J.mkQ ∘ₗ π, fun i => ?_, fun i j => ?_⟩
  · apply isPtDer_of
    · simp [π]
    · intro f hf
      have hfI : f ∈ I := Ideal.pow_le_self two_ne_zero hf
      have h0 : J.mkQ f = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hf
      simp only [LinearMap.comp_apply, hπ f hfI, h0, map_zero]
  · have e : J.mkQ (x j) = φ (Pi.single j 1) := by
      simp [φ]
    have e2 : g (φ (Pi.single j 1)) = Pi.single j 1 := LinearMap.congr_fun hg _
    simp only [LinearMap.comp_apply, hπ _ (hx j), e, e2, LinearMap.proj_apply, Pi.single_apply]
end GlobalTheory.HeightOneHopf
